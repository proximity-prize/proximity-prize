import copy
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from generate import apply_edits, declaration, discovery_roots, reachable, statement_name, submission_modules, suggest_nodes
from validate import compare_types, source_binding, source_fields, validate_bundle
from batch import CONFIG, extract, inventory, run
from test_publish import fixture


class GenerationTests(unittest.TestCase):
    def test_utf8_byte_offsets_and_nested_type_assignments(self):
        source = '/-- unicode α --/\ntheorem value : (let x := 1; x) = 1 := by rfl\n'
        data = source.encode()
        position = lambda text: data.index(text.encode())
        fact = {"kind": "decl", "declStart": {"line": 1, "offset": 0}, "declEnd": {"line": 2, "offset": len(data)-1}, "valStart": {"line": 2, "offset": position(':= by')}, "docstring": {"start": {"offset": 0}, "end": {"offset": position('\ntheorem')}}, "privateTok": None}
        ref = {"kind": "ref", "const": "value", "start": {"offset": position('value')}, "end": {"offset": position('value')+5}}
        row = {"startLine": 2, "userName": "value"}
        stub = declaration(source, row, [fact, ref], name='BC_value', stub=True)
        self.assertEqual(stub, 'theorem BC_value : (let x := 1; x) = 1 := by sorry')
        self.assertEqual(declaration(source, row, [fact, ref], name='solution'), 'theorem solution : (let x := 1; x) = 1 := by rfl')

    def test_ambiguous_and_overlapping_edits_fail_closed(self):
        with self.assertRaises(ValueError): apply_edits('abcdef', [(0, 3, ''), (2, 4, '')])
        with self.assertRaises(ValueError): apply_edits('abc', [(0, 8, '')])

    def test_reachability_keeps_instances_constructors_and_companion_dependencies(self):
        def row(name, kind='def', **extra):
            return {"name": name, "kind": kind, "startLine": 1, "isInstance": False, "typeDeps": [], "valueDeps": [], **extra}
        rows = [row('root', 'theorem', valueDeps=['aux']), row('aux', startLine=0, valueDeps=['shape']), row('shape','inductive'), row('ctor','ctor',typeDeps=['shape','fieldType']), row('fieldType'), row('instance',isInstance=True), row('dead')]
        self.assertEqual({row['name'] for row in reachable(rows,['root'])}, {'root','shape','ctor','fieldType','instance'})

    def test_independent_short_results_are_candidates_without_becoming_final_roots(self):
        module = 'ProximityPrize.SubmissionUpper.Helper'
        def row(name, **extra):
            return {"name": name, "module": module, "kind": "theorem", "startLine": 1,
                    "isPrivate": False, "isInstance": False, "typeDeps": [], "valueDeps": [], **extra}
        rows = [row('candidate'), row('short_unused'), row('useful_definition', kind='def'),
                row('private_helper', isPrivate=True), row('compiler_helper', startLine=0),
                row('other_track', module='ProximityPrize.SubmissionLower.Helper'),
                row('library', module='ArkLib.Helper')]
        candidates = discovery_roots(rows, {module})
        self.assertEqual(candidates, ['candidate', 'short_unused', 'useful_definition'])
        self.assertEqual({entry['name'] for entry in reachable(rows, ['candidate'])}, {'candidate'})
        self.assertEqual(suggest_nodes(rows, {}, ['candidate'], candidates), candidates)

    def test_discovery_module_scope_is_flat_tracked_submission_source(self):
        directory = 'ProximityPrize/SubmissionUpper'
        self.assertEqual(submission_modules([directory + '/Helper.lean', directory + '/Solution.lean',
                         directory + '/score.txt', 'ProximityPrize/SubmissionLower/Helper.lean'], directory),
                         ['ProximityPrize.SubmissionUpper.Helper', 'ProximityPrize.SubmissionUpper.Solution'])
        with self.assertRaises(ValueError): submission_modules([directory + '/nested/Helper.lean'], directory)

    def test_failed_nonwinning_root_does_not_hide_an_independent_compiled_helper(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary); source = directory / 'source'; upstream = directory / 'upstream'
            (source / 'ProximityPrize/SubmissionUpper').mkdir(parents=True)
            (source / '.lake/packages').mkdir(parents=True)
            (upstream / 'scripts').mkdir(parents=True)
            (upstream / 'scripts/extract_decl_graph.lean').write_text('import SumSquares\n')
            helper = 'ProximityPrize.SubmissionUpper.Helper'; root_module = 'ProximityPrize.SubmissionUpper.Solution'
            (source / 'ProximityPrize/SubmissionUpper/Helper.lean').write_text('theorem independent : True := by trivial\n')
            row = {'name': 'independent', 'module': helper, 'kind': 'theorem', 'startLine': 1,
                   'isPrivate': False, 'isInstance': False, 'typeDeps': [], 'valueDeps': []}
            def execute(args, cwd, timeout=600, output=None):
                if args[:3] == ['git', 'rev-parse', 'HEAD']: return CONFIG['workspaceRevision']
                if args[:2] == ['git', 'ls-tree']:
                    return 'ProximityPrize/SubmissionUpper/Helper.lean\nProximityPrize/SubmissionUpper/Solution.lean'
                if args == ['lake', 'build', root_module]: raise subprocess.CalledProcessError(1, args)
                if args[-1] == 'ExtractGraph.lean': (source / 'decl_graph.jsonl').write_text(json.dumps(row) + '\n')
                if output: Path(output).write_text('')
                return ''
            work = {'module': root_module, 'root': 'candidate', 'directory': 'ProximityPrize/SubmissionUpper', 'nativeCommit': 'a'*40, 'winner': False}
            with patch('batch.run', execute):
                extract(source, upstream, directory, work)
                discovered = json.loads((directory / 'facts/suggested.json').read_text())
                self.assertEqual(discovered, {'roots': [], 'candidates': ['independent'], 'nodes': ['independent'], 'failedModules': [root_module]})
                self.assertEqual((source / 'ExtractGraph.lean').read_text(), f'import {helper}\n')
                with self.assertRaisesRegex(ValueError, 'winning claim'):
                    extract(source, upstream, directory, work | {'winner': True})

    def test_unchanged_statements_reuse_names_but_context_changes_do_not(self):
        args = ('Bound','import Mathlib','theorem _ : P', ['definition-a'], 'a'*40)
        self.assertEqual(statement_name(*args),statement_name(*args))
        self.assertNotEqual(statement_name(*args),statement_name('Bound','import Mathlib','theorem _ : Q',['definition-a'],'a'*40))
        self.assertNotEqual(statement_name(*args),statement_name('Bound','import Mathlib','theorem _ : P',['definition-b'],'a'*40))

    def test_a_weaker_statement_changed_definition_and_hidden_sorry_fail(self):
        native = {"levels": 0, "type": ["claim", 6804], "body": None, "shape": None, "axioms": ['propext']}
        for change in [{"type": ['claim',6800]}, {"body": ['new-definition']}, {"axioms": ['sorryAx']}, {"shape": ['different-constructor']}]:
            with self.assertRaises(ValueError): compare_types(native, native | change)
        compare_types(native,native)
        # A matching Mathlib theorem cannot be attributed to an unrelated
        # submission file by changing the agent's extracted metadata.
        with self.assertRaisesRegex(ValueError, 'different module'):
            compare_types(native | {'module':'Mathlib.Other'}, native, native_module='ProximityPrize.SubmissionUpper.Helper')

    def test_inventory_starts_with_both_winners_then_nonwinning_work(self):
        track_ids = [track['benchmarkId'] for track in CONFIG['tracks']]
        def fetch(url):
            index = 0 if track_ids[0] in url else 1
            rows = [{'id': f'{index}-winner', 'submissionCommitSha': str(index+1)*40, 'status': 'accepted','promotionStatus':'promoted','officialScore':100, 'createdAt':'2026-09-01'},
                    {'id': f'{index}-other', 'submissionCommitSha': str(index+3)*40, 'status': 'rejected','promotionStatus':None, 'officialScore':None, 'createdAt':'2026-08-01'}]
            return {'submissions':rows}
        state={'completed':{},'deferred':{}}
        first=inventory(state,fetch,limit=4)
        self.assertTrue(all(item['winner'] for item in first[:2]))
        self.assertTrue(all(not item['winner'] for item in first[2:]))
        state['completed'][first[0]['id']]={}
        self.assertNotIn(first[0]['id'],[item['id'] for item in inventory(state,fetch,limit=4)])
        state['completed'].clear()
        state['attempted']={first[0]['id']: 1}
        self.assertEqual(inventory(state,fetch)[0]['id'],first[1]['id'])
        state['attempted']={item['id']: index+1 for index,item in enumerate(first)}
        self.assertEqual(inventory(state,fetch)[0]['id'],first[0]['id'])
        # A confirmed queued upload gets its cached publication resumed before
        # another source's extraction, rather than waiting for the whole backlog.
        state['items']={'pending': {'phase':'posting','kind':'problem','proofs':{},'sources':[{'submissionId':first[-1]['submissionId']}]}}
        self.assertEqual(inventory(state,fetch)[0]['id'],first[-1]['id'])
        state['items']['pending']['phase']='FAILED'
        self.assertEqual(inventory(state,fetch)[0]['id'],first[0]['id'])

    def test_compile_boundary_refuses_publication_credentials(self):
        with patch.dict(os.environ, {'PROVE2ME_API_KEY':'test-only-secret'}):
            with self.assertRaisesRegex(ValueError, 'credentials'): run(['false'], Path('.'))

    def test_source_links_bind_the_original_commit_and_actual_native_module(self):
        mapping = fixture()['items'][0]['sources'][0]
        work = {key: mapping[key] for key in ('submissionId', 'benchmarkId', 'repository', 'commit')}
        item = {'nativeModule': 'Main'}
        source_binding(item, mapping, work)
        for change in [{'commit':'c'*40}, {'path':'Other.lean'}, {'submissionId':'another-submission'}]:
            with self.assertRaises(ValueError): source_binding(item, mapping | change, work)

    def test_public_bundle_rejects_private_fields_bad_order_and_other_collections(self):
        bundle=fixture()
        bundle.update(version=1, workspaceRevision=CONFIG['workspaceRevision'],mathlibRev=CONFIG['mathlibRev'])
        bundle['collections']=[{'benchmarkId':track['benchmarkId'],'tag':CONFIG['tag'],'mathlibRev':CONFIG['mathlibRev']} for track in CONFIG['tracks']]
        bundle['items'][0]['sources'][0]['benchmarkId']=CONFIG['tracks'][0]['benchmarkId']
        validate_bundle(bundle)
        changed=copy.deepcopy(bundle); changed['items'][0]['sources'][0]['email']='private@example.invalid'
        with self.assertRaises(ValueError):validate_bundle(changed)
        changed=copy.deepcopy(bundle); changed['items'][0]['requires']=['unknown']
        with self.assertRaises(ValueError):validate_bundle(changed)
        changed=copy.deepcopy(bundle); changed['collections'][0]['tag']='another-project'
        with self.assertRaises(ValueError):validate_bundle(changed)


if __name__ == '__main__': unittest.main()
