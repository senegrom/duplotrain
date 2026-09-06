"""Prepare verified Git objects; the connected maintainer performs the ref update."""
import hashlib
import json
import os
import runpy
import subprocess
from pathlib import Path

manifest = runpy.run_path('.github/editor-speedups/apply.py')['EXPECTED']
repo = os.environ['GITHUB_REPOSITORY']
tested = os.environ['GITHUB_SHA']


def api(path, data=None):
    command = ['gh', 'api', f'repos/{repo}/{path}']
    if data is not None:
        command += ['--method', 'POST', '--input', '-']
    output = subprocess.check_output(command, input=json.dumps(data) if data is not None else None, text=True)
    return json.loads(output)


def entries(commit):
    return {entry['path']: entry for entry in api(f"git/trees/{commit['tree']['sha']}")['tree']}

parent = api('git/ref/heads/main')['object']['sha']
comparison = api(f'compare/{tested}...{parent}')
assert comparison['status'] in ('identical', 'ahead'), 'main no longer descends from the tested commit'
base = api(f'git/commits/{parent}')
old = entries(api(f'git/commits/{tested}'))
current = entries(base)
for name in ('src', 'webapp', 'tests', 'docs', '.github', 'pyproject.toml'):
    assert current[name]['sha'] == old[name]['sha'], f'Concurrent application change: {name}'
changes = []
for name, before, after in manifest['files']:
    data = Path(name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == after
    blob = api('git/blobs', {'content': data.decode('utf-8'), 'encoding': 'utf-8'})
    local_sha = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    assert blob['sha'] == local_sha, f'Uploaded blob mismatch: {name}'
    changes.append({'path': name, 'mode': '100644', 'type': 'blob', 'sha': blob['sha']})
# The prepared commit removes its verification scaffolding; no permanent job or branch.
temporary = sorted(Path('.github/editor-speedups').glob('*'))
temporary.append(Path('.github/workflows/verify-editor-speedups.yml'))
for path in temporary:
    changes.append({'path': path.as_posix(), 'mode': '100644', 'type': 'blob', 'sha': None})
tree = api('git/trees', {'base_tree': base['tree']['sha'], 'tree': changes})
assert entries({'tree': tree})['theory']['sha'] == current['theory']['sha'], 'Proof changed'
message = '''Speed up exact editor geometry and trim the browser worker

Use exact rational arithmetic fast paths and enforce Alg immutability.
Bound geometry/traversal caches, retain caller-owned list containers, reuse
ring/bridge transforms and eliminate duplicate candidate-size calculations.
Retain catalogue controls and candidate cards across unchanged redraws.
Omit duplicate editor HTML and desktop-only modules from the worker ZIP only.

Verified Python 3.12/3.13 lint and tests plus Chromium/WebKit browser tests
before preparing this commit. Preserve concurrent proof work unchanged and
remove all temporary verification files. No search rules or safety checks removed.'''
commit = api('git/commits', {'message': message, 'tree': tree['sha'], 'parents': [parent]})
result = {'commit': commit['sha'], 'parent': parent, 'tree': tree['sha'],
          'tested_commit': tested, 'run_id': os.environ['GITHUB_RUN_ID'],
          'files': manifest['files'], 'theory_tree': current['theory']['sha']}
Path(os.environ['RUNNER_TEMP'], 'verified-commit.json').write_text(json.dumps(result, indent=2))
print('VERIFIED_COMMIT=' + commit['sha'])
print('PARENT=' + parent)
print('TREE=' + tree['sha'])
print('No branch reference has been changed.')
