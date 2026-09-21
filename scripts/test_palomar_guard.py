"""Regression cases for actual preflight failures; no Lean build required."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import yaml
import palomar_guard as guard

parser = argparse.ArgumentParser()
parser.add_argument('--pipeline', type=Path, required=True)
args = parser.parse_args()
sys.path.insert(0, str(args.pipeline.resolve()))
from scripts import submission_contract as contract


class GuardRegression(unittest.TestCase):
    def inputs(self):
        return dict(repository='example/project', commit='a' * 40, request_id='abcdef123456',
                    options=json.dumps({'comparator_config_path': 'comparator.json',
                                        'authorization_relationship': guard.RELATIONSHIP}))

    def test_valid_request(self):
        self.assertEqual(guard.validate_inputs(contract, self.inputs()), 'abcdef123456')

    def test_bad_request_id(self):
        inputs = self.inputs()
        inputs['request_id'] = 'collatz-positive-density-9f15b52'
        with self.assertRaisesRegex(Exception, 'twelve'):
            guard.validate_inputs(contract, inputs)

    def test_missing_authorization(self):
        inputs = self.inputs()
        inputs['options'] = '{"comparator_config_path":"comparator.json"}'
        with self.assertRaisesRegex(ValueError, 'authorization'):
            guard.validate_inputs(contract, inputs)

    def test_orcid_names(self):
        source = Path(__file__).resolve().parents[1] / 'formalization.yaml'
        valid = contract.load_formalization_metadata(source)
        for key in ('authors', 'responsible_maintainers'):
            bad = copy.deepcopy(valid)
            bad['project'][key] = ['Idris Ali Shaik (ORCID: 0009-0009-9699-9712)']
            with tempfile.TemporaryDirectory() as tmp:
                path = Path(tmp) / 'formalization.yaml'
                path.write_text(yaml.safe_dump(bad))
                with self.assertRaisesRegex(Exception, 'ORCID'):
                    contract.load_formalization_metadata(path)

    def test_snapshot_checks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            def run(*args):
                return subprocess.check_output(['git', '-C', tmp, *args], text=True, stderr=subprocess.DEVNULL).strip()
            run('init')
            (root / 'tracked').write_text('original')
            run('add', 'tracked')
            run('-c', 'user.name=Guard Test', '-c', 'user.email=guard@example.invalid', '-c', 'core.hooksPath=/dev/null', 'commit', '-m', 'fixture')
            commit = run('rev-parse', 'HEAD')
            guard.require_snapshot(root, commit)
            with self.assertRaisesRegex(ValueError, 'match'):
                guard.require_snapshot(root, '0' * 40)
            (root / 'tracked').write_text('changed')
            with self.assertRaisesRegex(ValueError, 'dirty'):
                guard.require_snapshot(root, commit)


unittest.main(argv=[sys.argv[0]])
