"""Export the GitHub-ready files to a zip, excluding local archives and caches."""
from pathlib import Path
import hashlib
import json
import os
import zipfile

ROOT = Path(__file__).resolve().parents[1]
ROOT_FILES = ['README.md', '.gitignore', 'main.pdf']
DIRECTORIES = ['lean_formalization', 'verification', 'scripts']
EXCLUDED = {'.lake', '__pycache__', 'results'}
EXCLUDED_FILES = {'scripts/build_report.py', 'verification/exact/proof.md'}
SUFFIXES = {'.pyc', '.log', '.aux', '.out', '.toc', '.xdv', '.synctex.gz'}

def source_files():
    files = [ROOT / name for name in ROOT_FILES]
    for directory in DIRECTORIES:
        for folder, subdirs, names in os.walk(ROOT / directory):
            subdirs[:] = sorted(name for name in subdirs if name not in EXCLUDED)
            for name in names:
                path = Path(folder) / name
                if path.relative_to(ROOT).as_posix() not in EXCLUDED_FILES and not any(name.endswith(suffix) for suffix in SUFFIXES):
                    files.append(path)
    return sorted(files)

def main():
    out = ROOT / 'dist'
    out.mkdir(exist_ok=True)
    target = out / 'critical-extrapolation.zip'
    entries=[]
    with zipfile.ZipFile(target, 'w', zipfile.ZIP_DEFLATED) as archive:
        for path in source_files():
            name=path.relative_to(ROOT).as_posix()
            archive.write(path, 'critical-extrapolation/' + name)
            entries.append({'path':name,'bytes':path.stat().st_size,
                            'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
    with zipfile.ZipFile(target) as archive:
        assert archive.testzip() is None
    (out/'manifest.json').write_text(json.dumps(entries,ensure_ascii=False,indent=2),encoding='utf-8')
    print(f'Exported {len(entries)} files, {target.stat().st_size / 1024 / 1024:.2f} MiB: dist/critical-extrapolation.zip')

if __name__ == '__main__':
    main()
