import copy
import json
import os
import unittest
from pathlib import Path
from unittest.mock import patch
from generate import apply_edits, declaration, reachable, statement_name
from validate import compare_types, source_fields, validate_bundle
from batch import CONFIG, inventory, run
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

    def test_compile_boundary_refuses_publication_credentials(self):
        with patch.dict(os.environ, {'PROVE2ME_API_KEY':'test-only-secret'}):
            with self.assertRaisesRegex(ValueError, 'credentials'): run(['false'], Path('.'))

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
