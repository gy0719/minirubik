#!/usr/bin/env python3
"""Run under WSL; requires Python's standard library, host cc, RV32 GCC,
and the pinned Windows Ripes. Ripes --regs checks the target replay result.

  python3 test_d11.py --smoke
  python3 test_d11.py --jobs 4 --output d11_ripes_results.csv

Repeat the same command to resume. Completed rows, including failures, stay
recorded; use a new output name to retest failures after fixing their cause.
A JSON sidecar records source/tool fingerprints and the final summary.
No repository build artifacts are modified. Exit 0 means the entire selected
set passed, 1 means failures/incomplete results, and 130 means interrupted.
"""

import argparse
import concurrent.futures
import csv
import fcntl
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import signal
import statistics
import struct
import subprocess
import tempfile
import threading
import time

ROOT = Path(__file__).resolve().parent
RIPES_DEFAULT = '/mnt/c/Users/young/Downloads/Ripes-v2.2.6-106-g5b8a616-win-x86_64/Ripes.exe'
RIPES_SHA256 = 'bd2ddea8cd6fcf6902cda7366fe99ab6dd0c7fdbbc7efcfdb89ede20acc67f0f'
RIPES_VERSION = 'v2.2.6-106-g5b8a616'
SOURCES = ('solver.S', 'solver_tables.S', 'my_solver.c', 'my_solver_test.c')
FLAGS = ('-march=rv32i', '-mabi=ilp32')
FIELDS = ('cube', 'iret', 'under_50m', 'replay_ok', 'replayed_moves',
          'length_ok', 'coordinates_ok', 'final_p', 'final_o',
          'reference_path', 'error', 'attempts')
NAMES = ('R', 'R2', "R'", 'B', 'B2', "B'", 'D', 'D2', "D'")
ALLOWED = set('lui auipc jal jalr beq bne blt bge bltu bgeu lb lh lw lbu lhu '
              'sb sh sw addi slti sltiu xori ori andi slli srli srai add sub '
              'sll slt sltu xor srl sra or and fence ecall ebreak'.split())

# Only a temporary host copy's CLI entry point is renamed. Its BFS, solving,
# and independent concrete replay are reused unchanged; nothing links to RV32.
ENUMERATOR = r'''
#include "my_solver_test.c"
int main(void) {
    if (!initialize_tables() || !check_initialization_reference(1)) return 1;
    uint8_t *exact = build_oracle();
    if (!exact) return 1;
    unsigned count = 0;
    for (uint32_t r = 0; r < STATES; ++r) count += exact[r] == 11;
    if (count != 2644) { fprintf(stderr, "d11 count=%u\n", count); return 1; }
    puts("cube,p,o,path");
    for (uint32_t r = 0; r < STATES; ++r) {
        if (exact[r] != 11) continue;
        char input[15]; solution_t solution;
        ranked_state_t state = {r / ORIENTATIONS, r % ORIENTATIONS};
        if (!solve(state, &solution) || solution.length != 11 ||
            !verify_solution(r, &solution)) return 1;
        format_input(r, input);
        printf("%s,%u,%u,", input, state.p, state.o);
        for (unsigned i = 0; i < solution.length; ++i)
            printf("%s%u", i ? " " : "", solution.moves[i]);
        putchar('\n');
    }
    free(exact);
    return output_failed();
}
'''


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def command(argv, cwd, timeout=60):
    result = subprocess.run([str(a) for a in argv], cwd=cwd, capture_output=True,
                            text=True, timeout=timeout)
    require(result.returncode == 0,
            f'{argv[0]} exited {result.returncode}: {(result.stderr + result.stdout)[-3000:]}')
    return result.stdout


def executable(name):
    found = shutil.which(str(name))
    require(found, f'Executable unavailable: {name}')
    return str(Path(found).resolve())


def sections(binary):
    require(binary[:6] == b'\x7fELF\x01\x01', 'Expected little-endian ELF32')
    require(struct.unpack_from('<HH', binary, 16) == (2, 243), 'Expected RISC-V executable')
    require(struct.unpack_from('<I', binary, 36)[0] == 0, 'Unexpected ELF ISA/ABI flags')
    offset = struct.unpack_from('<I', binary, 32)[0]
    size, count, names_index = struct.unpack_from('<HHH', binary, 46)
    entries = [struct.unpack_from('<10I', binary, offset + i * size) for i in range(count)]
    names_entry = entries[names_index]
    names = binary[names_entry[4]:names_entry[4] + names_entry[5]]
    result = {}
    for s in entries:
        if s[2] & 2:  # SHF_ALLOC; NOBITS contributes size but no file bytes.
            name = names[s[0]:].split(b'\0')[0].decode()
            result[name] = (s[3], s[5], s[2], b'' if s[1] == 8 else binary[s[4]:s[4] + s[5]])
    return result


def enumerate_states(work, cc):
    test = (work / 'my_solver_test.c').read_text()
    entry = 'int main(int argc, char **argv)'
    require(test.count(entry) == 1, 'Cannot locate host test CLI entry point')
    (work / 'my_solver_test.c').write_text(test.replace(entry, 'int d11_unused_main(int argc, char **argv)'))
    (work / 'enumerate.c').write_text(ENUMERATOR)
    command([cc, '-O3', '-std=c99', '-Wall', '-Wextra', 'enumerate.c', '-o', 'enumerate'], work)
    output = command([work / 'enumerate'], work, timeout=300)
    header = 'cube,p,o,path\n'
    require(header in output, 'BFS enumerator emitted no CSV header')
    states = list(csv.DictReader(io.StringIO(output[output.index(header):])))
    require(len(states) == len({s['cube'] for s in states}) == 2644,
            'BFS must produce exactly 2,644 distinct distance-11 states')
    for s in states:
        require(re.fullmatch(r'[1-7]{7}[1-3]{7}', s['cube']) and
                len(set(s['cube'][:7])) == 7 and
                sum(int(c) - 1 for c in s['cube'][7:]) % 3 == 0 and
                0 <= int(s['p']) < 5040 and 0 <= int(s['o']) < 729 and
                len(s['path'].split()) == 11, f'Invalid oracle row: {s}')
    return states


def build(work, folder, cube, gcc, tables):
    obj, elf = folder / 'solver.o', folder / 'solver.elf'
    command([gcc, *FLAGS, f'-DSOLVER_CUBE_INPUT="{cube}"', '-c',
             work / 'solver.S', '-o', obj], work)
    command([gcc, *FLAGS, '-nostdlib', '-nostartfiles', '-Wl,--no-relax',
             obj, tables, '-o', elf], work)
    return elf


def audit(elf, work, prefix):
    symbols = {}
    listing = command([prefix + 'nm', '-S', elf], work)
    for line in listing.splitlines():
        f = line.split()
        if len(f) == 4:
            symbols[f[3]] = int(f[0], 16), int(f[1], 16)
    expected = {'perm_move_table': 30240, 'ori_move_table': 4374,
                'hp_table': 2520, 'ho_table': 365, 'search_frames': 384,
                'solution_path': 12, 'solution_length': 4, 'validation_result': 4}
    for name, size in expected.items():
        require(name in symbols and symbols[name][1] == size, f'Unexpected symbol size: {name}')
    require(not command([prefix + 'nm', '-u', elf], work).strip(), 'Undefined symbols')
    require(not re.search(r'__(?:mul|div|mod|udiv|umod|ash|lshr|float|fix)\w*', listing),
            'Compiler arithmetic helper detected')
    asm = command([prefix + 'objdump', '-d', '-M', 'no-aliases', elf], work)
    instructions = 0
    for line in asm.splitlines():
        match = re.match(r'\s*[0-9a-f]+:\s+([0-9a-f]+)\s+(\S+)', line)
        if match:
            require(len(match[1]) == 8 and match[2] in ALLOWED, f'Non-RV32I instruction: {line}')
            instructions += 1
    require(instructions > 0, 'Empty disassembly')
    baseline = sections(elf.read_bytes())
    require(sum(s[1] for s in baseline.values() if not s[2] & 4) < 128 * 1024,
            'Static data is not under 128 KiB')
    address, size = symbols['cube_input']
    require(size == 15 and 'perm_rank' in symbols and 'ori_rank' in symbols,
            'Missing input/root coordinate storage')
    input_offset = address - baseline['.rodata'][0]
    start, length = symbols['_start']
    exit_offset = start + length - 4 - baseline['.text'][0]
    require(baseline['.text'][3][exit_offset:exit_offset + 4] == b'\x73\0\0\0',
            'Expected final exit ecall in _start')
    require(baseline['.text'][3][exit_offset - 4:exit_offset] == struct.pack('<I', 0x00a00893),
            'Expected li a7,10 immediately before exit')
    replay_start, replay_size = symbols['replay_solution']
    replay_end = replay_start + replay_size - baseline['.text'][0]
    require(baseline['.text'][3][replay_end - 8:replay_end] == struct.pack('<II', 0x00a2a023, 0x000f8067),
            'Replay register contract changed: expected sw a0,0(t0); jalr zero,0(t6)')
    return baseline, symbols, input_offset


def check_binary(elf, cube, baseline, input_offset):
    actual = sections(elf.read_bytes())
    require(actual.keys() == baseline.keys(), 'Allocated section layout changed')
    for name, expected in baseline.items():
        candidate = actual[name]
        require(candidate[:3] == expected[:3], f'{name} address/size/flags changed')
        data = candidate[3]
        if name == '.rodata':
            require(data[input_offset:input_offset + 14] == cube.encode(), 'Incorrect inline input')
            data = data[:input_offset] + b'54721631111111' + data[input_offset + 14:]
        require(data == expected[3], f'{name} bytes changed beyond cube_input')


def ripes_result(output, state, symbols):
    """Interpret the frozen solver's post-replay register convention.

    a0 is the value stored to validation_result; t0 identifies that store.
    s0/s1 are final coordinates, s2 advances once per replayed move, and
    s3 is the remaining move count. a4/a5 preserve the original root ranks.
    The actual solution_path byte array is not exposed by this CLI.
    """
    require('Program exited with code: 0' in output, f'Ripes did not exit successfully: {output[-2000:]}')
    counts = re.findall(r'instructions retired\s+(\d+)', output)
    require(len(counts) == 1, f'Invalid Ripes instruction count: {output[-2000:]}')
    processors = re.findall(r'(?m)^processor:[ \t]*([^\r\n]*)', output)
    extensions = re.findall(r'(?m)^ISA extensions:[ \t]*([^\r\n]*)', output)
    require(processors == ['RV32_ISS'] and len(extensions) == 1 and not extensions[0].strip(),
            'Unexpected Ripes processor/extensions')
    registers = {}
    for index, decimal, hex_value in re.findall(r'(?m)^x(\d+):\s*(-?\d+)\s+\(0x([0-9a-fA-F]{8})\)', output):
        index, value = int(index), int(hex_value, 16)
        require(index not in registers and int(decimal) % (1 << 32) == value, 'Invalid register report')
        registers[index] = value
    require(set(registers) == set(range(32)), 'Ripes must report all 32 registers')
    r = registers
    require(r[0] == 0 and r[17] == 10, 'Unexpected exit register state')
    count = int(counts[0])
    # s2 reaches solution_path + solution_length only after complete replay.
    moves = r[18] - symbols['solution_path'][0]
    root_ok = r[14] == int(state['p']) and r[15] == int(state['o'])
    replay_ok = (r[10] == 1 and r[5] == symbols['validation_result'][0] and
                 r[8] == 0 and r[9] == 0 and r[19] == 0)
    row = dict(iret=count, under_50m=int(0 < count < 50000000),
               replay_ok=int(replay_ok), replayed_moves=moves, length_ok=int(moves == 11),
               coordinates_ok=int(root_ok), final_p=r[8], final_o=r[9],
               reference_path=' '.join(NAMES[int(m)] for m in state['path'].split()), error='')
    if not replay_ok or not root_ok or moves != 11:
        row['error'] = 'Ripes register validation failure'
    elif not row['under_50m']:
        row['error'] = 'instruction limit failure'
    return row


def evaluate(state, work, config, baseline, symbols, input_offset, tables, stop):
    row = dict.fromkeys(FIELDS, '')
    row['cube'] = cube = state['cube']
    with tempfile.TemporaryDirectory(prefix='d11-case-', dir=work) as name:
        folder = Path(name)
        for attempt in range(1, config.retries + 2):
            if stop.is_set():
                return None
            row = dict.fromkeys(FIELDS, '')
            row.update(cube=cube, attempts=attempt)
            try:
                elf = build(work, folder, cube, config.gcc, tables)
                check_binary(elf, cube, baseline, input_offset)
                src = command(['wslpath', '-w', elf], work).strip()
                output = command([config.ripes, '--mode', 'cli', '--src', src,
                                  '-t', 'elf', '--proc', 'RV32_ISS', '--iret', '--regs', '--runinfo',
                                  '--timeout', str(int(config.timeout * 1000))],
                                 work, timeout=config.timeout + 10)
                if stop.is_set():
                    return None
                row.update(ripes_result(output, state, symbols))
                return row  # Deterministic failures are recorded without retries.
            except Exception as error:
                row['error'] = f'{type(error).__name__}: {error}'.replace('\n', r'\n')
                if attempt <= config.retries and not stop.is_set():
                    stop.wait(.25 * attempt)
        return None if stop.is_set() else row


def metadata_write(path, data):
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, delete=False) as f:
        temporary = Path(f.name)
        json.dump(data, f, indent=2)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    try:
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def csv_record(stream, row):
    text = io.StringIO(newline='')
    writer = csv.writer(text, lineterminator='\n')
    writer.writerow(FIELDS if row is None else [row[k] for k in FIELDS])
    stream.seek(0, os.SEEK_END)
    stream.write(text.getvalue().encode())
    stream.flush()
    os.fsync(stream.fileno())


def resume_rows(stream, selected):
    stream.seek(0)
    raw = stream.read()
    if raw and not raw.endswith(b'\n'):
        # Each record is one line; an interrupted final append can be retried.
        end = raw.rfind(b'\n') + 1
        stream.seek(end)
        stream.truncate()
        stream.flush()
        os.fsync(stream.fileno())
        raw = raw[:end]
        print('Recovered an incomplete final CSV line', flush=True)
    if not raw:
        csv_record(stream, None)
        return {}
    reader = csv.DictReader(io.StringIO(raw.decode()), strict=True)
    require(tuple(reader.fieldnames or ()) == FIELDS, 'Incompatible CSV columns')
    rows = {}
    for row in reader:
        require(set(row) == set(FIELDS) and all(v is not None for v in row.values()), 'Malformed CSV row')
        cube = row['cube']
        require(cube in selected and cube not in rows, f'Unknown/duplicate cube: {cube}')
        require(row['attempts'].isdigit() and int(row['attempts']) > 0, 'Invalid attempts field')
        require(not row['iret'] or row['iret'].isdigit(), 'Invalid instruction count')
        if not row['error']:
            require(row['replayed_moves'] == '11' and row['final_p'] == row['final_o'] == '0' and all(row[k] == '1' for k in
                    ('under_50m', 'replay_ok', 'length_ok', 'coordinates_ok')) and
                    row['iret'] and 0 < int(row['iret']) < 50000000,
                    f'Invalid successful checkpoint: {cube}')
            expected_path = ' '.join(NAMES[int(m)] for m in selected[cube]['path'].split())
            require(row['reference_path'] == expected_path, f'Checkpoint reference path mismatch: {cube}')
        rows[cube] = row
    return rows


def summary(rows, expected):
    measured = [r for r in rows.values() if str(r['iret']).isdigit()]
    ranked = sorted(measured, key=lambda r: (-int(r['iret']), r['cube']))
    counts = [int(r['iret']) for r in measured]
    return dict(states_expected=expected, states_tested=len(rows), complete=len(rows) == expected,
                measurements=len(measured), failures=sum(bool(r['error']) for r in rows.values()),
                replay_failures=sum(str(r['replay_ok']) == '0' for r in rows.values()),
                replay_unverified=sum(str(r['replay_ok']) not in ('0', '1') for r in rows.values()),
                length_failures=sum(str(r['length_ok']) == '0' for r in rows.values()),
                at_or_above_50m=sum(n >= 50000000 for n in counts),
                max_iret=max(counts, default=None), max_state=ranked[0]['cube'] if ranked else None,
                min_iret=min(counts, default=None), average_iret=statistics.mean(counts) if counts else None,
                top_10=[dict(cube=r['cube'], iret=int(r['iret'])) for r in ranked[:10]],
                required_213=rows.get('21345671111111'))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--smoke', action='store_true', help='five d11 states, including both representative cases')
    parser.add_argument('--jobs', type=int, default=4, help='isolated concurrent ELF runs (default: 4)')
    parser.add_argument('--output', type=Path, help='CSV checkpoint; repeats resume without overwriting existing rows')
    parser.add_argument('--ripes', default=os.environ.get('RIPES', RIPES_DEFAULT), help='path to the pinned Ripes.exe')
    parser.add_argument('--prefix', default='riscv64-unknown-elf-', help='GNU RV32 tool prefix')
    parser.add_argument('--cc', default='cc', help='host C compiler')
    parser.add_argument('--timeout', type=float, default=60, help='seconds per runtime attempt')
    parser.add_argument('--retries', type=int, default=2, help='additional attempts after build/runtime errors')
    config = parser.parse_args()
    def interrupted_signal(signum, frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted_signal)
    require(1 <= config.jobs <= 16 and config.timeout >= 1 and 0 <= config.retries <= 10,
            'Expected jobs=1..16, timeout>=1, retries=0..10')
    config.gcc = executable(config.prefix + 'gcc')
    config.cc, config.ripes = map(executable, (config.cc, config.ripes))
    for name in ('nm', 'objdump'):
        executable(config.prefix + name)
    executable('wslpath')
    require(digest(config.ripes) == RIPES_SHA256, f'Ripes binary must match pinned {RIPES_VERSION}')
    config.output = (config.output or Path('d11_ripes_smoke_results.csv' if config.smoke else 'd11_ripes_results.csv')).resolve()
    require(config.output.parent.is_dir(), 'Output parent directory does not exist')
    meta_path = config.output.with_suffix(config.output.suffix + '.meta.json')
    source_bytes = {name: (ROOT / name).read_bytes() for name in SOURCES}
    require(re.search(rb'(?m)^\.equ\s+RENDER,\s*0\s*$', source_bytes['solver.S']), 'Renderer must be disabled')
    identity = dict(script_sha256=digest(__file__), sources={name: hashlib.sha256(data).hexdigest()
                   for name, data in source_bytes.items()}, ripes_sha256=RIPES_SHA256,
                   gcc_version=command([config.gcc, '--version'], ROOT),
                   cc_version=command([config.cc, '--version'], ROOT), mode='smoke' if config.smoke else 'all_d11',
                   processor='RV32_ISS', extensions=[], renderer=False, measurement='--iret',
                   validation='Ripes --regs: a0/t0, s0/s1, s2/s3, a4/a5')
    stop = threading.Event()
    with config.output.open('a+b') as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise RuntimeError('Another test process already owns this CSV') from None
        if meta_path.exists():
            metadata = json.loads(meta_path.read_text())
            require(metadata.get('identity') == identity, 'Checkpoint source/tool/mode mismatch; use a new --output')
        else:
            require(os.fstat(stream.fileno()).st_size == 0, 'Existing CSV has no fingerprint; use a new --output')
            metadata = dict(identity=identity, ripes_version=RIPES_VERSION,
                            correctness='Ripes final registers: target replay, replayed length, root/final coordinates; actual path bytes not inspected')
            metadata_write(meta_path, metadata)
        with tempfile.TemporaryDirectory(prefix='minirubik-d11-') as temporary:
            work = Path(temporary)
            for name, data in source_bytes.items():
                (work / name).write_bytes(data)
            print('Generating the complete BFS oracle and verifying 2,644 C solutions...', flush=True)
            states = enumerate_states(work, config.cc)
            if config.smoke:
                by_cube = {s['cube']: s for s in states}
                states = [by_cube[c] for c in ('21345671111111', '54721631111111',
                          states[0]['cube'], states[len(states) // 2]['cube'], states[-1]['cube'])]
            selected = {s['cube']: s for s in states}
            rows = resume_rows(stream, selected)
            tables = work / 'tables.o'
            command([config.gcc, *FLAGS, '-c', work / 'solver_tables.S', '-o', tables], work)
            baseline_elf = build(work, work, '54721631111111', config.gcc, tables)
            baseline, symbols, input_offset = audit(baseline_elf, work, config.prefix)
            metadata['sizes'] = {name: baseline.get(name, (0, 0))[1] for name in ('.text', '.rodata', '.bss', '.data')}
            metadata['static_data'] = sum(s[1] for s in baseline.values() if not s[2] & 4)
            metadata_write(meta_path, metadata)
            pending = iter(s for s in states if s['cube'] not in rows)
            started, last_progress = time.monotonic(), time.monotonic()
            print(f'BFS: 2,644 distinct d11 states; selected={len(states)}; resumed={len(rows)}; '
                  f'Ripes {RIPES_VERSION} RV32_ISS --iret; RV32I audit passed', flush=True)
            pool = concurrent.futures.ThreadPoolExecutor(max_workers=config.jobs)
            futures = set()
            interrupted = False
            def submit():
                state = next(pending, None)
                if state:
                    futures.add(pool.submit(evaluate, state, work, config, baseline, symbols, input_offset, tables, stop))
            try:
                for _ in range(config.jobs):
                    submit()
                while futures:
                    done, _ = concurrent.futures.wait(futures, timeout=1,
                                                     return_when=concurrent.futures.FIRST_COMPLETED)
                    for future in done:
                        futures.remove(future)
                        row = future.result()
                        if row is not None:
                            csv_record(stream, row)
                            rows[row['cube']] = row
                            if row['error']:
                                print(f"FAIL {row['cube']}: {row['error']}", flush=True)
                        submit()
                    if (done and (config.smoke or len(rows) % 10 == 0)) or time.monotonic() - last_progress >= 30:
                        print(f'Progress {len(rows)}/{len(states)}; elapsed={time.monotonic() - started:.1f}s; '
                              f'failures={sum(bool(r["error"]) for r in rows.values())}', flush=True)
                        last_progress = time.monotonic()
            except KeyboardInterrupt:
                interrupted = True
                stop.set()
                print('Interrupted: durable CSV rows saved; repeat the same command to resume.', flush=True)
            finally:
                stop.set()
                pool.shutdown(wait=True, cancel_futures=True)
            result = summary(rows, len(states))
            metadata['summary'] = result
            metadata_write(meta_path, metadata)
            print(json.dumps(result, indent=2), flush=True)
            return 130 if interrupted else int(not result['complete'] or result['failures'] != 0)


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
    except Exception as error:
        print(f'ERROR: {error}', flush=True)
        raise SystemExit(1)
