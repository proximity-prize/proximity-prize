#!/usr/bin/env python3
"""Regression checks for profile isolation and exact score/claim binding."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from benchmark_contract import comppoly_source, parse_unsafe_index
from benchmark_profiles import PROFILES
import challenges

ROOT = Path(__file__).resolve().parents[1]
COMMIT = "a" * 40


def run(script, *args, cwd=ROOT, env=None):
    return subprocess.run([sys.executable, str(ROOT / "scripts" / script), *map(str, args)],
                          cwd=cwd, env=env, capture_output=True, text=True)


class ProfileTests(unittest.TestCase):
    def test_challenge_versions_are_independent_per_slug(self):
        with tempfile.TemporaryDirectory() as directory:
            entries = challenges.load()
            lower = next(e for e in entries if e["slug"] == PROFILES["lower"].challenge)
            upper = next(e for e in entries if e["slug"] == PROFILES["upper"].challenge)
            lower_version = lower["version"]
            upper_number = int(lower_version.rsplit("-v", 1)[1]) + 1
            upper["version"] = f"{challenges.series(lower_version)}-v{upper_number}"
            config = Path(directory) / "challenges.json"
            config.write_text(json.dumps({"challenges": entries}))
            with patch.object(challenges, "CONFIG", config):
                self.assertEqual(challenges.get(lower["slug"])["version"], lower_version)
                self.assertEqual(challenges.get(upper["slug"])["version"], upper["version"])

    def test_unsafe_index_requires_profile_ceiling(self):
        with self.assertRaises(TypeError):
            parse_unsafe_index("1")
        for p in [p for p in PROFILES.values() if p.side == "upper"]:
            self.assertEqual(
                parse_unsafe_index(str(p.max_unsafe_index), maximum=p.max_unsafe_index),
                p.max_unsafe_index,
            )
            with self.assertRaises(ValueError):
                parse_unsafe_index(str(p.max_unsafe_index + 1), maximum=p.max_unsafe_index)

    def test_exact_render_and_comparator_names(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "Challenge.lean"
            for p in PROFILES.values():
                claim = "1/4" if p.side == "lower" else str(p.max_unsafe_index)
                result = run("render-benchmark-challenge.py", p.selector, "5300", claim, output)
                self.assertEqual(result.returncode, 0, result.stderr)
                source = output.read_text()
                self.assertIn("import " + p.target + "\n", source)
                self.assertIn("namespace " + p.namespace + "\n", source)
                cfg = json.loads((ROOT / p.comparator).read_text())
                self.assertEqual(cfg["theorem_names"], [p.namespace + ".candidate"])
                self.assertEqual(cfg["solution_module"], p.submission.replace("/", ".") + ".Solution")
                self.assertEqual(cfg["challenge_module"], p.challenge_module)
                self.assertEqual(challenges.get(p.challenge)["submission_root"], p.submission)

    def test_upper_grid_boundaries(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "Challenge.lean"
            for p in [p for p in PROFILES.values() if p.side == "upper"]:
                for value in ["0", str(p.max_unsafe_index + 1), "01", "1.0", "-1"]:
                    self.assertNotEqual(run("render-benchmark-challenge.py", p.selector, "12800", value, output).returncode, 0)
            self.assertNotEqual(run("render-benchmark-challenge.py", "upper", "12800", "1048576", output).returncode, 0)
            self.assertEqual(run("render-benchmark-challenge.py", "binary-upper", "12800", "1048576", output).returncode, 0)
            self.assertNotEqual(run("render-benchmark-challenge.py", "bogus", "12800", "1", output).returncode, 0)

    def test_cross_profile_imports_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for p in PROFILES.values():
                (root / "score.txt").write_text("5300\n")
                for claim in ["radius.txt", "unsafe-index.txt"]:
                    (root / claim).unlink(missing_ok=True)
                (root / p.claim_file).write_text("1/4\n" if p.side == "lower" else "1\n")
                for target in [q.target for q in PROFILES.values()]:
                    (root / "Solution.lean").write_text("import " + target + "\n")
                    result = subprocess.run(["bash", str(ROOT / "scripts/check-submission-imports.sh"), p.selector, str(root)], capture_output=True, text=True)
                    self.assertEqual(result.returncode == 0, target == p.target, result.stderr)

    def test_verified_result_must_match_profile_and_claim(self):
        with tempfile.TemporaryDirectory() as directory:
            tmp = Path(directory)
            (tmp / "lake-manifest.json").write_text((ROOT / "lake-manifest.json").read_text())
            (tmp / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
            for p in PROFILES.values():
                root = tmp / p.submission
                root.mkdir(parents=True, exist_ok=True)
                (root / "score.txt").write_text("5300\n")
                (root / p.claim_file).write_text("1/4\n" if p.side == "lower" else str(p.max_unsafe_index) + "\n")
                version = challenges.get(p.challenge)["version"]
                env = os.environ | {"CHALLENGE_VERSION": version, "GITHUB_SHA": COMMIT}
                metrics = {"radius_numerator": 1, "radius_denominator": 4} if p.side == "lower" else {"unsafe_index": p.max_unsafe_index}
                fixture = {"status": "verified", "id": "fixture", "resolved_commit": COMMIT,
                    "challenge": {"challenge": p.challenge, "version": version},
                    "result": {"score": {"metric": "fixture", "direction": "maximize" if p.side == "lower" else "minimize", "unit": "bits", "value": "5300", "scale": 100}, "metrics": metrics}}
                path = tmp / "result.json"
                path.write_text(json.dumps(fixture))
                result = run("write-verifier-score.py", p.selector, path, cwd=tmp, env=env)
                self.assertEqual(result.returncode, 0, result.stderr)
                output = json.loads((tmp / f".yukon/{p.track}-score.json").read_text())
                self.assertEqual(output["metrics"]["domainSize"], p.domain_size)
                # This is the authoritative artifact -- launchEligible, and the
                # only one an accepted result comes from. It must name its whole
                # trusted base, which the diagnostic writer did while this one
                # was silently missing arklibRev, the field fixing the other 19
                # packages in the manifest.
                for field in ("arklibRev", "compPolyRev", "compPolyUrl", "leanToolchain"):
                    self.assertIn(field, output["metrics"], f"{field} missing from the authoritative artifact")
                self.assertTrue(output["metrics"]["launchEligible"])
                if p.side == "upper":
                    self.assertEqual(output["metrics"]["unsafeRadiusExact"], f"{p.max_unsafe_index}/{p.domain_size}")
                for mutate in [lambda f: f["challenge"].update(challenge="wrong-profile"),
                               lambda f: f["challenge"].update(version="wrong-version"),
                               lambda f: f.update(resolved_commit="b" * 40),
                               lambda f: f["result"]["score"].update(value="5301"),
                               lambda f: f["result"]["score"].update(scale=True)]:
                    bad = json.loads(json.dumps(fixture))
                    mutate(bad)
                    path.write_text(json.dumps(bad))
                    self.assertNotEqual(run("write-verifier-score.py", p.selector, path, cwd=tmp, env=env).returncode, 0)
                bad = json.loads(json.dumps(fixture))
                key = "radius_numerator" if p.side == "lower" else "unsafe_index"
                bad["result"]["metrics"][key] = True
                path.write_text(json.dumps(bad))
                self.assertNotEqual(run("write-verifier-score.py", p.selector, path, cwd=tmp, env=env).returncode, 0)

    def test_protected_contracts_agree_modulo_profile(self):
        """The four protected contracts stay deliberately duplicated, one per
        immutable challenge version, so a shared definition cannot silently
        change four registered claims at once. Guard against the other failure
        mode instead: an *unintended* divergence between a track and its twin.

        Normalising only the profile identifiers must leave the files equal. A
        genuine, intended divergence fails here and has to be stated.
        """
        renames = [
            ("Benchmark.BinaryIRSProfile", "Benchmark.IRSProfile"),
            ("Benchmark.BinaryTarget", "Benchmark.Target"),
            ("BinaryIRSProfile", "IRSProfile"),
            ("ProximityPrize.Benchmark.Binary", "ProximityPrize.Benchmark"),
        ]

        def normalise(path):
            text = path.read_text()
            for old, new in renames:
                text = text.replace(old, new)
            return text

        benchmark = ROOT / "ProximityPrize" / "Benchmark"
        for side in ["Lower", "Upper"]:
            koala = benchmark / f"Target{side}.lean"
            binary = benchmark / f"BinaryTarget{side}.lean"
            self.assertEqual(
                normalise(koala),
                normalise(binary),
                f"Target{side}.lean and BinaryTarget{side}.lean have diverged "
                "beyond their profile identifiers",
            )

    def test_summary_profile_line_is_human_readable(self):
        with tempfile.TemporaryDirectory() as directory:
            tmp = Path(directory)
            (tmp / "lake-manifest.json").write_text((ROOT / "lake-manifest.json").read_text())
            (tmp / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
            env = os.environ | {"GITHUB_SHA": COMMIT}
            for p in PROFILES.values():
                claim = "1/4" if p.side == "lower" else str(p.max_unsafe_index)
                result = run("write-benchmark-score.py", p.selector, "5300", claim, cwd=tmp, env=env)
                self.assertEqual(result.returncode, 0, result.stderr)
                summary = (tmp / f"benchmark-results/{p.track}-summary.md").read_text()
                self.assertIn("- Profile: " + p.summary_line, summary)
                # A Python dict repr must never reach the released markdown.
                self.assertNotIn("{'", summary)
                self.assertIn(f"`n={'2^21' if p.binary else '2^18'}`", summary)

    def test_local_binary_metadata_is_diagnostic(self):
        with tempfile.TemporaryDirectory() as directory:
            tmp = Path(directory)
            (tmp / "lake-manifest.json").write_text((ROOT / "lake-manifest.json").read_text())
            (tmp / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
            env = os.environ | {"GITHUB_SHA": COMMIT}
            for p in [p for p in PROFILES.values() if p.binary]:
                claim = "1/4" if p.side == "lower" else "1048576"
                result = run("write-benchmark-score.py", p.selector, "5300", claim, cwd=tmp, env=env)
                self.assertEqual(result.returncode, 0, result.stderr)
                metrics = json.loads((tmp / f".yukon/{p.track}-score.json").read_text())["metrics"]
                self.assertEqual(metrics["field"], "BF64.Ext3")
                self.assertEqual(metrics["totalDimension"], 2**26)
                self.assertEqual(metrics["interleaving"], 64)
                self.assertFalse(metrics["verified"])
                self.assertFalse(metrics["launchEligible"])

    def test_comppoly_repository_travels_with_its_revision(self):
        """A CompPoly hash is meaningless without the repository holding it.

        ArkLib's revision fixes every other package in the manifest, but not
        this one: a manifest can name a different CompPoly than the lakefile it
        was resolved from, and production's does -- ArkLib e6519789 declares
        Verified-zkEVM/CompPoly while the manifest beside it records a
        zksecurity fork on a branch. Recording the revision alone would
        describe those accepted results as verified against a library they
        never saw, so the URL is recorded with it and checked here.
        """
        with tempfile.TemporaryDirectory() as directory:
            tmp = Path(directory)
            manifest = json.loads((ROOT / "lake-manifest.json").read_text())
            fork = "https://github.com/zksecurity/CompPoly"
            for package in manifest["packages"]:
                if package.get("name") == "CompPoly":
                    package["url"] = fork
            (tmp / "lake-manifest.json").write_text(json.dumps(manifest))
            (tmp / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
            env = os.environ | {"GITHUB_SHA": COMMIT}
            p = PROFILES["lower"]
            result = run("write-benchmark-score.py", p.selector, "5300", "1/4", cwd=tmp, env=env)
            self.assertEqual(result.returncode, 0, result.stderr)
            metrics = json.loads((tmp / f".yukon/{p.track}-score.json").read_text())["metrics"]
            # The forked URL reaches the artifact rather than the repository's own.
            self.assertEqual(metrics["compPolyUrl"], fork)
            self.assertEqual(metrics["compPolyRev"], comppoly_source()[1])
            summary = (tmp / f"benchmark-results/{p.track}-summary.md").read_text()
            self.assertIn("- CompPoly: `zksecurity/CompPoly@", summary)

    def test_comppoly_entry_without_a_url_is_rejected(self):
        """A revision with no repository is not a record of anything."""
        with tempfile.TemporaryDirectory() as directory:
            tmp = Path(directory)
            manifest = json.loads((ROOT / "lake-manifest.json").read_text())
            for package in manifest["packages"]:
                if package.get("name") == "CompPoly":
                    package.pop("url", None)
            path = tmp / "lake-manifest.json"
            path.write_text(json.dumps(manifest))
            with self.assertRaises(ValueError):
                comppoly_source(path)


if __name__ == "__main__":
    unittest.main()
