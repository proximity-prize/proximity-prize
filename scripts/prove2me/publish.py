"""Resume checked publications. A lost POST response is reconciled, never blindly repeated."""
import hashlib
import json
import time
import uuid

TERMINAL_PROOFS = {"ACCEPTED", "SKETCH_ACCEPTED"}


def digest(value):
    return hashlib.sha256(value.encode() if isinstance(value, str) else json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def identifier(value):
    return str(uuid.UUID(value))


def publication_digest(item, env):
    return digest({"env": env, "kind": item["kind"], "name": item["name"], "body": item["body"], "preamble": item.get("preamble", "")})


def matches_job(job, item):
    return (job.get("theorem_name") == item["name"] and job.get("kind") == item["kind"]
            and job.get("visibility") == "public" and job.get("definitions") == (item["body"] if item["kind"] == "definition" else item.get("preamble", ""))
            and (item["kind"] == "definition" or job.get("formal_statement") == item["body"]))


def make_catalog(state, collections):
    result = {"version": 1, "collections": []}
    for collection in collections:
        entries = []
        for receipt in state["items"].values():
            sources = [source for source in receipt.get("sources", []) if source["benchmarkId"] == collection["benchmarkId"]]
            if receipt.get("theoremId") and receipt["mathlibRev"] == collection["mathlibRev"] and sources:
                entries.append({"theoremId": receipt["theoremId"], "publicationJobId": receipt["jobId"], "visibility": "public",
                                "isRoot": collection["benchmarkId"] in receipt.get("roots", []),
                                "sources": [{key: value for key, value in source.items() if key != "benchmarkId"} for source in sources]})
        result["collections"].append({**collection, "entries": entries})
    return result


class Publisher:
    def __init__(self, provider, storage, deadline, now=time.time):
        self.provider, self.storage, self.deadline, self.now = provider, storage, deadline, now
        self.state = storage.read("state.json", None)
        if self.state is None or self.state.get("version") != 1:
            raise ValueError("Initialize an explicit checkpoint before publishing")

    def save(self):
        self.storage.write("state.json", self.state)

    def poll_publication(self, item, receipt, env):
        job = self.provider.get("/publish-jobs/" + identifier(receipt["jobId"]))
        if job.get("id") != receipt["jobId"] or not matches_job(job, item):
            raise ValueError("Publication receipt does not match the checked payload")
        if job["status"] in {"FAILED", "ERROR"}:
            receipt["phase"] = job["status"]
            self.save()
            return False
        if job["status"] != "PUBLISHED":
            if job["status"] not in {"PENDING", "COMPILING"}:
                raise ValueError("Unknown publication status")
            return False
        theorem_id = identifier(job["theorem_id"])
        theorem = self.provider.get("/theorems/" + theorem_id)
        if (theorem.get("theorem_id") != theorem_id or theorem.get("mathlib_rev") != env
                or theorem.get("theorem_name") != item["name"] or theorem.get("visibility") == "private"
                or theorem.get("deprecated_at") is not None):
            raise ValueError("Published theorem differs from its source receipt or environment")
        if item["kind"] == "problem" and (theorem.get("preamble") != item.get("preamble", "") or theorem.get("formal_statement") != item["body"]):
            raise ValueError("Published statement context differs from the checked payload")
        receipt.update(theoremId=theorem_id, phase="published")
        self.save()
        return True

    def publish_item(self, item, env):
        key = publication_digest(item, env)
        receipt = self.state["items"].get(key)
        if receipt is None:
            receipt = {"name": item["name"], "kind": item["kind"], "mathlibRev": env, "phase": "ready", "sources": [], "roots": [], "proofs": {}}
            self.state["items"][key] = receipt
        for source in item["sources"]:
            if source not in receipt["sources"]:
                receipt["sources"].append(source)
            if item["isRoot"] and source["benchmarkId"] not in receipt["roots"]:
                receipt["roots"].append(source["benchmarkId"])
        self.save()
        if receipt.get("phase") in {"FAILED", "ERROR"}:
            return False  # A human or a future repair batch must explicitly replace this work.
        if not receipt.get("jobId"):
            if receipt["phase"] == "posting":
                matches = [job for job in self.provider.pages("/publish-jobs", "jobs", kind=item["kind"]) if matches_job(job, item)]
                if len(matches) != 1:
                    raise RuntimeError("Uncertain publication POST: no unique matching receipt yet; retain checkpoint and retry reconciliation later")
                receipt["jobId"] = identifier(matches[0]["id"])
                self.save()
            else:
                # Persist intent BEFORE a request that could queue a job.
                receipt["phase"] = "posting"
                self.save()
                source = item["sources"][0]
                common = {"env": env, "private": False, "tags": item["tags"], "source": f'{source["repository"]}/blob/{source["commit"]}/{source["path"]}#L{source["line"]}', "natural_language_statement": item["description"]}
                if item["kind"] == "definition":
                    result = self.provider.post("/submit-definition", {**common, "definition_name": item["name"], "definition_title": item["title"], "definition": item["body"]})
                    receipt["jobId"] = identifier(result["job_id"])
                else:
                    result = self.provider.post("/submit-problem", {"env": env, "private": False, "problems": [{key: value for key, value in common.items() if key not in {"env", "private"}} | {"theorem_name": item["name"], "theorem_title": item["title"], "formal_statement": item["body"], "preamble": item.get("preamble", "")}]})
                    if result.get("errors") or len(result.get("jobs", [])) != 1 or result["jobs"][0].get("name") != item["name"]:
                        raise ValueError("Publication was not confirmed as one queued job")
                    receipt["jobId"] = identifier(result["jobs"][0]["job_id"])
                self.save()
        if not self.poll_publication(item, receipt, env):
            return False
        if item["kind"] == "definition":
            return True
        proof_key = digest(item["solution"])
        proof = receipt["proofs"].setdefault(proof_key, {"phase": "ready"})
        if not proof.get("id"):
            if proof["phase"] == "posting":
                matches = []
                for candidate in self.provider.pages(f'/theorems/{receipt["theoremId"]}/submissions', "submissions"):
                    if candidate.get("deprecated_at") is not None:
                        continue
                    result = self.provider.get(f'/submissions/{identifier(candidate["id"])}/solution')
                    if candidate.get("theorem_id") == receipt["theoremId"] and digest(result["content"]) == proof_key:
                        matches.append(candidate)
                if len(matches) != 1:
                    raise RuntimeError("Uncertain proof POST: no unique matching source yet; keep checkpoint for reconciliation")
                proof["id"] = identifier(matches[0]["id"])
                self.save()
            else:
                proof["phase"] = "posting"
                self.save()
                proof["id"] = identifier(self.provider.verify(receipt["theoremId"], item["solution"], item["explanation"])["submission_id"])
                self.save()
        verdict = self.provider.get("/verify", submission_id=proof["id"])
        if verdict.get("id") != proof["id"] or verdict.get("theorem_id") != receipt["theoremId"]:
            raise ValueError("Proof verdict is for a different submission or statement")
        if verdict["status"] not in {"PENDING", "ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}:
            raise ValueError("Unknown proof verdict")
        proof["phase"] = verdict["status"]
        self.save()
        return proof["phase"] in TERMINAL_PROOFS

    def run(self, bundle):
        ready = set()
        for item in bundle["items"]:
            if self.now() >= self.deadline:
                break
            if any(dependency not in ready for dependency in item["requires"]):
                continue
            if self.publish_item(item, bundle["mathlibRev"]):
                ready.add(item["key"])
            # Even Open statements have confirmed public identities and belong in the map.
            self.storage.write("catalog.json", make_catalog(self.state, bundle["collections"]))
        for work in bundle["work"]:
            if all(key in ready for key in work["items"]):
                self.state["completed"][work["id"]] = {"items": [publication_digest(item, bundle["mathlibRev"]) for item in bundle["items"] if item["key"] in work["items"]]}
        self.save()
        return ready
