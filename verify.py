"""Rebuild all pinned BCMP proof modules in a previously nonexistent directory (Python 3.11+)."""
import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
import tomllib
from graphlib import TopologicalSorter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REVISION = "770dbf88b28b8b8b7326d7aec4db6a8f57ab19689de4819b9a2cb2dc8680858c"
CONSUMER = "2c298ee8060de04ccde83c810ad05846ecd09d539debc616d722805e729b7d85"
VERSION = "4.36.0"
TOOLCHAIN = f"leanprover/lean4:v{VERSION}"
LEAN_REV = "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9"
MATHLIB_REV = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"
THEOREM = "BCMP430.Final430.bcmp_conjecture_4_30"
AXIOMS = f"'{THEOREM}' depends on axioms: [propext, Classical.choice, Quot.sound]"


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True, type=Path, help='real Lean binary, e.g. the path from elan which lean')
    parser.add_argument('--out', type=Path, help='new output directory (never reused)')
    parser.add_argument('--preflight-only', action='store_true', help='check dependencies and compile an import smoke, NOT the theorem')
    args = parser.parse_args()
    lean = args.lean.resolve(strict=True)
    lake = lean.with_name('lake' + lean.suffix)
    require(lake.is_file(), 'Missing Lake beside the selected Lean')
    if args.out:
        out = args.out.resolve()
        require(not out.exists(), f'Output already exists: {out}')
        out.mkdir(parents=True, exist_ok=False)
    else:
        base = ROOT / '.verification'
        base.mkdir(exist_ok=True)
        out = Path(tempfile.mkdtemp(dir=base))
    print(f'Fresh output: {out}', flush=True)
    env = {k: v for k, v in os.environ.items() if not k.upper().startswith(('LEAN', 'LAKE', 'ELAN', 'GIT_'))}
    env.update(LEAN_ABORT_ON_PANIC='1', PATH=str(lean.parent) + os.pathsep + env.get('PATH', ''))
    log_path = out / 'build.log'

    def run(cmd, cwd=ROOT, paths=None):
        e = dict(env)
        if paths is not None:
            e['LEAN_PATH'] = os.pathsep.join(map(str, paths))
        r = subprocess.run(cmd, cwd=cwd, env=e, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        text = r.stdout.decode('utf-8', errors='replace').replace('\r\n', '\n')
        with log_path.open('a', encoding='utf-8') as f:
            print(f'cwd={cwd}\ncmd={list(map(str, cmd))!r}\nexit={r.returncode}\n{text}', file=f)
        require(r.returncode == 0, f'Command failed (exit {r.returncode}): {cmd}\n{text}')
        return text.strip()

    lv = run([lean, '--version'])
    kv = run([lake, '--version'])
    require(f'version {VERSION},' in lv and f'commit {LEAN_REV},' in lv, f'Wrong Lean: {lv}')
    require(f'(Lean version {VERSION})' in kv and LEAN_REV[:7] in kv, f'Wrong Lake: {kv}')
    require((ROOT / 'lean-toolchain').read_text().strip() == TOOLCHAIN, 'Project toolchain pin mismatch')
    manifest = (ROOT / 'formal/sources.sha256').read_bytes()
    require(digest(manifest) == REVISION, 'Proof manifest checksum mismatch')
    sources = {}
    for line in manifest.decode('ascii').splitlines():
        h, filename = line.split('  ')
        require(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*\.lean', filename), 'Bad module name')
        data = (ROOT / 'formal' / filename).read_bytes()
        require(digest(data) == h, f'Proof source checksum mismatch: {filename}')
        sources[Path(filename).stem] = data
    require(set(sources) == {p.stem for p in (ROOT / 'formal').glob('*.lean')}, 'Proof inventory mismatch')
    consumer = (ROOT / 'checks/VerifyStatement.lean').read_bytes()
    require(digest(consumer) == CONSUMER, 'Expanded consumer checksum mismatch')
    cfg = tomllib.loads((ROOT / 'lakefile.toml').read_text(encoding='utf-8'))
    lib, = cfg['lean_lib']
    require(lib['srcDir'] == 'formal' and set(lib['roots']) == set(sources) and cfg['defaultTargets'] == [lib['name']], 'Lake proof roots mismatch')
    imports = {n: [i for line in b.decode('utf-8-sig').splitlines() if line.startswith('import ') for i in line.split()[1:]] for n,b in sources.items()}
    order = tuple(TopologicalSorter({n:[i for i in im if i in sources] for n,im in imports.items()}).static_order())
    lock = json.loads((ROOT / 'lake-manifest.json').read_bytes())
    require(lock.get('fixedToolchain') is True and lock['packagesDir'] == '.lake/packages' and lock['name'] == cfg['name'], 'Bad project lock configuration')
    entries = {e['name']: e for e in lock['packages']}
    require(len(entries) == len(lock['packages']), 'Duplicate locked dependency')
    direct, = cfg['require']
    m = entries.get('mathlib', {})
    require(direct['name'] == 'mathlib' and direct['rev'] == f'v{VERSION}' and m.get('rev') == MATHLIB_REV and m.get('inputRev') == direct['rev'] and m.get('url') == direct['git'], 'Mathlib pin mismatch')
    pkg = ROOT / lock['packagesDir']
    paths = []
    for name, entry in entries.items():
        require(re.fullmatch(r'[\w-]+', name) and entry.get('type') == 'git' and entry.get('subDir') is None and re.fullmatch('[a-f0-9]{40}', entry['rev']), 'Invalid git lock entry')
        d = pkg / name
        require(d.is_dir(), f'Missing dependency: {name}')
        require(Path(run(['git', '-C', d, 'rev-parse', '--show-toplevel'])).resolve() == d.resolve(), f'Not a package checkout: {name}')
        require(run(['git', '-C', d, 'rev-parse', 'HEAD']) == entry['rev'], f'Wrong locked revision: {name}')
        require(not run(['git', '-C', d, 'status', '--porcelain=v1', '--untracked-files=all']), f'Dirty dependency: {name}')
        paths.append(d / '.lake/build/lib/lean')
    upstream = json.loads(run(['git', '-C', pkg/'mathlib', 'show', 'HEAD:lake-manifest.json']))['packages']
    require(set(entries) == {'mathlib'} | {e['name'] for e in upstream}, 'Incomplete transitive lock')
    for e in upstream:
        require(all(entries[e['name']].get(k) == e.get(k) for k in ('rev','url','type','subDir','configFile','manifestFile','scope','inputRev')), f'Transitive lock mismatch: {e["name"]}')
    externals = sorted({i for im in imports.values() for i in im} - set(sources))
    syslib = Path(run([lean,'--print-libdir']))
    for mod in set(sources) | set(externals):
        obj = Path(*mod.split('.')).with_suffix('.olean')
        hits = [d for d in [*paths,syslib] if (d / obj).is_file()]
        require(len(hits) == (0 if mod in sources else 1), f'Missing or shadowed module: {mod}')
    for cmd in (['build', 'checkLakePins'], ['exe', 'checkLakePins']):
        pins = run([lake, '--no-cache', '--wfail', *cmd])
    require(f'PASS: {len(entries)} mathlib packages match lake-manifest.json' in pins.splitlines(), 'Lake pin check missing')
    (out / 'sources.sha256').write_bytes(manifest)
    smoke = out / 'ImportProbe.lean'
    smoke.write_text(''.join(f'import {i}\n' for i in externals) + 'example (x : ℝ) : x*x = x^2 := by ring\n', encoding='utf-8')
    run([lean, '-j1', '-DwarningAsError=true', smoke.name], out, paths)
    print(f'{lv}\n{kv}\n{pins}\nDependency import smoke passed.', flush=True)
    if args.preflight_only:
        print('PREFLIGHT ONLY: no BCMP modules checked.')
        return
    def check_axioms(text):
        lines = [line for line in text.splitlines() if line.startswith(f"'{THEOREM}' depends on axioms:")]
        require(lines == [AXIOMS], f'Unexpected final axiom output: {lines}')
    for index, name in enumerate(order, 1):
        print(f'{index}/{len(order)} {name}', flush=True)
        (out / f'{name}.lean').write_bytes(sources[name])
        text = run([lean, '-j1', '-DwarningAsError=true', '-o', f'{name}.olean', f'{name}.lean'], out, [out,*paths])
        require((out/f'{name}.olean').is_file() and 'sorryAx' not in text, f'Missing object or placeholder: {name}')
        if name == 'Final430':
            check_axioms(text)
    (out/'VerifyStatement.lean').write_bytes(consumer)
    text = run([lean, '-j1', '-DwarningAsError=true', 'VerifyStatement.lean'], out, [out,*paths])
    check_axioms(text)
    (out/'statement-and-axioms.txt').write_text(text+'\n',encoding='utf-8')
    print(f'{AXIOMS}\nPASS: {len(order)} modules and expanded consumer; source manifest {REVISION}', flush=True)


if __name__ == '__main__':
    main()
