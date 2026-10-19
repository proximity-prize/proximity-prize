#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${root}"

lake build ProximityPrize \
  ProximityPrize.SubmissionLower.Solution \
  ProximityPrize.SubmissionUpper.Solution \
  ProximityPrize.SubmissionBinaryLower.Solution \
  ProximityPrize.SubmissionBinaryUpper.Solution \
  VCVio.OracleComp.RunIO
lake env lean scripts/check-axioms.lean
lake env lean scripts/check-baseline-axioms.lean
lake env lean --run scripts/BinaryToyRuntime.lean
# The geometry every score artifact advertises must be the geometry Lean has.
lake env lean --run scripts/emit-profile-geometry.lean \
  | python3 scripts/check-profile-geometry.py
for profile in lower upper binary-lower binary-upper; do
  # `mapfile` needs bash >= 4; macOS ships 3.2.
  policy=()
  while IFS= read -r line; do policy+=("${line}"); done \
    < <(python3 scripts/benchmark_profiles.py shell "${profile}")
  bash scripts/check-submission-imports.sh "${profile}" "${policy[1]}"
done
# The claim files must agree with what the proofs actually prove.
lake env lean scripts/emit-candidate-claims.lean \
  | python3 scripts/check-candidate-claims.py
# No challenge may import another.
python3 scripts/check-track-isolation.py
python3 scripts/check-versions.py
python3 scripts/test-benchmark-profiles.py
git diff --check
