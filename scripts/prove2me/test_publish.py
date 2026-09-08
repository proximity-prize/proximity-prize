import copy
import tempfile
import time
import unittest
import uuid
from publish import Publisher, publication_digest
from storage import Storage, empty_state

ENV = "a" * 40
BENCHMARK = "11111111-1111-4111-8111-111111111111"


def fixture():
    return {"mathlibRev": ENV, "collections": [{"benchmarkId": BENCHMARK, "tag": "better-codes-proximity-prize", "mathlibRev": ENV}],
            "work": [{"id": "work-a", "items": ["lemma"]}], "items": [{"key": "lemma", "kind": "problem", "name": "shared_lemma", "body": "theorem shared_lemma : True := by sorry", "preamble": "import Mathlib", "solution": "import Mathlib\ntheorem solution : True := by trivial", "requires": [], "isRoot": True, "title": "Useful lemma", "description": "A useful intermediate result.", "explanation": "Direct proof.", "tags": ["better-codes-proximity-prize"], "sources": [{"benchmarkId": BENCHMARK, "submissionId": BENCHMARK, "repository": "https://github.com/example/proofs", "commit": "a" * 40, "path": "Main.lean", "line": 1, "sha256": "b" * 64, "toolchain": "leanprover/lean4:v4.33.1", "manifestSha256": "c" * 64}]}]}


class ProviderFixture:
    def __init__(self):
        self.jobs, self.proofs, self.theorems = {}, {}, {}
        self.post_count = self.proof_count = 0
        self.drop_post = self.drop_verify = False
        self.job_status, self.verdict = "PUBLISHED", "ACCEPTED"

    def post(self, path, payload):
        self.post_count += 1
        identifier, theorem_id = str(uuid.uuid4()), str(uuid.uuid4())
        if path == "/submit-problem":
            data = payload["problems"][0]
            name, body, preamble, kind = data["theorem_name"], data["formal_statement"], data["preamble"], "problem"
        else:
            data = payload
            name, body, preamble, kind = data["definition_name"], "", data["definition"], "definition"
        job = {"id": identifier, "theorem_id": theorem_id, "theorem_name": name, "formal_statement": body, "definitions": preamble, "kind": kind, "status": self.job_status, "visibility": "public"}
        self.jobs[identifier] = job
        self.theorems[theorem_id] = {"theorem_id": theorem_id, "theorem_name": name, "preamble": preamble, "formal_statement": body, "mathlib_rev": payload["env"], "visibility": "public", "deprecated_at": None}
        if self.drop_post:
            self.drop_post = False
            raise ConnectionError("response lost after queueing")
        return {"jobs": [{"name": name, "job_id": identifier}], "errors": []} if kind == "problem" else {"job_id": identifier}

    def verify(self, theorem_id, source, explanation):
        self.proof_count += 1
        identifier = str(uuid.uuid4())
        self.proofs[identifier] = {"id": identifier, "theorem_id": theorem_id, "status": self.verdict, "content": source, "deprecated_at": None}
        if self.drop_verify:
            self.drop_verify = False
            raise ConnectionError("response lost after queueing")
        return {"submission_id": identifier}

    def get(self, path, **query):
        if path.startswith("/publish-jobs/"): return copy.deepcopy(self.jobs[path.split("/")[-1]])
        if path.startswith("/theorems/"): return copy.deepcopy(self.theorems[path.split("/")[-1]])
        if path.startswith("/submissions/"): return {"content": self.proofs[path.split("/")[2]]["content"], "file_path": "opaque/provider/path"}
        if path == "/verify": return copy.deepcopy(self.proofs[query["submission_id"]])
        raise AssertionError(path)

    def pages(self, path, field, **query):
        return list(copy.deepcopy(self.jobs if field == "jobs" else self.proofs).values())


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.storage = Storage(self.directory.name)
        self.storage.write("state.json", empty_state())
        self.provider, self.bundle = ProviderFixture(), fixture()

    def run_batch(self):
        return Publisher(self.provider, self.storage, time.time() + 60).run(self.bundle)

    def test_queued_is_not_published(self):
        self.provider.job_status = "PENDING"
        self.assertEqual(self.run_batch(), set())
        self.assertEqual(self.storage.read("catalog.json")["collections"][0]["entries"], [])
        self.assertEqual(self.storage.read("state.json")["completed"], {})
        next(iter(self.provider.jobs.values()))["status"] = "PUBLISHED"
        self.assertEqual(self.run_batch(), {"lemma"})
        self.assertEqual(self.provider.post_count, 1)

    def test_interrupted_publication_resumes_without_duplicate(self):
        self.provider.drop_post = True
        with self.assertRaises(ConnectionError): self.run_batch()
        self.assertEqual(self.run_batch(), {"lemma"})
        self.assertEqual(self.provider.post_count, 1)

    def test_uncertain_post_waits_for_evidence(self):
        self.provider.drop_post = True
        with self.assertRaises(ConnectionError): self.run_batch()
        self.provider.jobs.clear()
        with self.assertRaisesRegex(RuntimeError, "Uncertain publication"): self.run_batch()
        self.assertEqual(self.provider.post_count, 1)

    def test_interrupted_proof_resumes_by_exact_source(self):
        self.provider.drop_verify = True
        with self.assertRaises(ConnectionError): self.run_batch()
        self.assertEqual(self.run_batch(), {"lemma"})
        self.assertEqual(self.provider.proof_count, 1)

    def test_repeated_source_and_new_attribution_reuse_provider_ids(self):
        self.run_batch()
        self.bundle["items"][0]["sources"][0]["submissionId"] = str(uuid.uuid4())
        self.run_batch()
        self.assertEqual((self.provider.post_count, self.provider.proof_count), (1, 1))
        entries = self.storage.read("catalog.json")["collections"][0]["entries"]
        self.assertEqual(len(entries), 1)
        self.assertEqual(len(entries[0]["sources"]), 2)

    def test_a_different_statement_cannot_overwrite_the_old_one(self):
        self.run_batch()
        self.bundle["items"][0].update(name="stronger_claim", body="theorem stronger_claim : 2 = 2 := by sorry")
        self.run_batch()
        self.assertEqual(self.provider.post_count, 2)
        self.assertEqual(len(self.storage.read("catalog.json")["collections"][0]["entries"]), 2)

    def test_reduction_acceptance_remains_separate_from_proof_acceptance(self):
        self.provider.verdict = "SKETCH_ACCEPTED"
        self.run_batch()
        receipt = next(iter(self.storage.read("state.json")["items"].values()))
        self.assertEqual(next(iter(receipt["proofs"].values()))["phase"], "SKETCH_ACCEPTED")
        self.assertNotIn("status", self.storage.read("catalog.json")["collections"][0]["entries"][0])

    def test_wrong_environment_and_private_records_never_enter_catalog(self):
        self.provider.job_status = "PENDING"
        self.run_batch()
        next(iter(self.provider.jobs.values()))["status"] = "PUBLISHED"
        theorem = next(iter(self.provider.theorems.values()))
        theorem["mathlib_rev"] = "b" * 40
        with self.assertRaises(ValueError): self.run_batch()
        theorem.update(mathlib_rev=ENV, visibility="private")
        with self.assertRaises(ValueError): self.run_batch()
        self.assertEqual(self.storage.read("catalog.json")["collections"][0]["entries"], [])

    def test_dependency_and_deadline_gates(self):
        self.bundle["items"][0]["requires"] = ["not-ready"]
        self.run_batch()
        self.assertEqual(self.provider.post_count, 0)
        self.bundle["items"][0]["requires"] = []
        Publisher(self.provider, self.storage, 0).run(self.bundle)
        self.assertEqual(self.provider.post_count, 0)

    def test_failed_compiles_are_retained_for_repair(self):
        self.provider.job_status = "FAILED"
        self.run_batch(); self.run_batch()
        self.assertEqual(self.provider.post_count, 1)
        self.assertEqual(self.storage.read("state.json")["completed"], {})

    def test_definitions_publish_without_fake_proof_attempts(self):
        self.bundle["items"][0].update(kind="definition", body="def increment (n : Nat) := n + 1", preamble="")
        self.run_batch()
        self.assertEqual(self.provider.proof_count, 0)
        self.assertEqual(len(self.storage.read("catalog.json")["collections"][0]["entries"]), 1)


if __name__ == "__main__": unittest.main()
