"""Fail closed before expensive Palomar replay; use the pinned upstream contract."""
import argparse
import hashlib
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys

PIPELINE = '3561d237dcc4b28482558ad28a64d767d7cc8615'
RELATIONSHIP = 'I have approval from a responsible author or maintainer'


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()


def require_snapshot(root, commit):
    if git(root, 'rev-parse', 'HEAD') != commit:
        raise ValueError('Checkout does not match the requested commit')
    if git(root, 'status', '--porcelain', '--untracked-files=all'):
        raise ValueError('Checkout is dirty; validate an immutable clean snapshot')


def validate_inputs(contract, inputs):
    values, request_id = contract.submission_request({'inputs': inputs})
    if not contract.SHA_RE.fullmatch(values['commit_sha']):
        raise ValueError('Invalid source commit')
    if values.get('authorization_relationship') not in contract.AUTHORIZATION_RELATIONSHIPS:
        raise ValueError('Missing or invalid authorization relationship')
    return request_id


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--pipeline', type=Path, required=True)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--repository', required=True)
    parser.add_argument('--run-id', required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args()
    source, pipeline = args.source.resolve(), args.pipeline.resolve()
    require_snapshot(source, args.commit)
    require_snapshot(pipeline, PIPELINE)
    sys.path.insert(0, str(pipeline))
    contract = importlib.import_module('scripts.submission_contract')
    request_id = hashlib.sha256((args.repository + args.commit + args.run_id).encode()).hexdigest()[:12]
    options = json.dumps({'comparator_config_path': 'comparator.json',
                          'authorization_relationship': RELATIONSHIP})
    inputs = dict(repository=args.repository, commit=args.commit,
                  pipeline_commit=PIPELINE, request_id=request_id,
                  mode='full', options=options)
    validate_inputs(contract, inputs)
    contract.load_formalization_metadata(source / 'formalization.yaml')
    manifest = json.loads((source / 'EXTRACTION_MANIFEST.json').read_text())
    for entry in manifest['files']:
        if hashlib.sha256((source / entry['path']).read_bytes()).hexdigest() != entry['sha256']:
            raise ValueError('Manifest mismatch: ' + entry['path'])
    config = json.loads((source / 'comparator.json').read_text())
    metadata = contract.load_formalization_metadata(source / 'formalization.yaml')
    if config['theorem_names'] != [r['declaration'] for r in metadata['status']['main_results']]:
        raise ValueError('Metadata and Comparator theorem selections differ')
    # Ensure a future workflow edit cannot silently validate one pin and execute another.
    import yaml
    workflow = yaml.safe_load((source / '.github/workflows/palomar-full-preflight.yml').read_text())
    job = workflow['jobs']['verify']
    if job.get('needs') != 'guard' or not job['uses'].endswith('@' + PIPELINE):
        raise ValueError('Full replay must depend on guard and use the validated pipeline')
    expected = {'repository': '${{ github.repository }}', 'commit': '${{ needs.guard.outputs.commit }}',
                'pipeline_commit': '${{ needs.guard.outputs.pipeline }}',
                'request_id': '${{ needs.guard.outputs.request_id }}',
                'options': '${{ needs.guard.outputs.options }}', 'mode': 'full'}
    if job['with'] != expected:
        raise ValueError('Replay inputs must come from the successful guard')
    receipt = {'status': 'pass', 'scope': 'input and metadata guard; not mechanical proof verification',
               'inputs': inputs, 'metadata_sha256': hashlib.sha256((source / 'formalization.yaml').read_bytes()).hexdigest()}
    args.receipt.write_text(json.dumps(receipt, indent=2) + '\n')
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
            for key, value in [('commit', args.commit), ('pipeline', PIPELINE), ('request_id', request_id), ('options', options)]:
                out.write(f'{key}={value}\n')
    print('PASS: pinned request/metadata validators, clean snapshots, manifest and replay binding')


if __name__ == '__main__':
    main()
