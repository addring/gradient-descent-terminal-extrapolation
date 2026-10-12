"""Run the three exact Python checks with the standard library."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'build' / 'verification'

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    exact = OUT / 'exact'
    exact.mkdir(exist_ok=True)
    for source in (ROOT / 'verification/exact').glob('*.py'):
        shutil.copy2(source, exact / source.name)
    entries = [exact / 'run_exact_checks.py',
               ROOT / 'verification/independent/verify_round31_corrections.py',
               ROOT / 'verification/independent/audit_asymptotic_proof_standalone.py']
    rows = []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONIOENCODING='utf-8')
    for script in entries:
        result = subprocess.run([sys.executable, '-B', str(script)], cwd=ROOT,
                                env=env, capture_output=True, text=True, encoding='utf-8')
        (OUT / (script.stem + '.log')).write_text(result.stdout + '\n' + result.stderr, encoding='utf-8')
        rows.append({'script': script.name, 'exit_code': result.returncode})
        print(f'{script.name}: {"PASS" if result.returncode == 0 else "FAIL"}', flush=True)
        if result.returncode:
            print(result.stderr)
            raise SystemExit(result.returncode)
    (OUT / 'summary.json').write_text(json.dumps({'passed': True, 'checks': rows}, indent=2), encoding='utf-8')

if __name__ == '__main__':
    main()
