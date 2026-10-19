#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${root}"

export PATH="${HOME}/.elan/bin:${PATH}"

[[ "$#" -eq 1 ]] || { echo "usage: ./benchmark.sh lower|upper|binary-lower|binary-upper" >&2; exit 2; }

profile="$1"
# Read line-by-line rather than with `mapfile`, which needs bash >= 4. macOS
# ships bash 3.2, and these scripts are run by hand outside CI too.
policy=()
while IFS= read -r line; do policy+=("${line}"); done \
  < <(python3 scripts/benchmark_profiles.py shell "${profile}")
[[ "${#policy[@]}" -eq 5 ]] || { echo "invalid benchmark profile: ${profile}" >&2; exit 2; }
track="${policy[0]}"
submission_dir="${root}/${policy[1]}"
challenge_path="${root}/${policy[2]}"
claim_path="${submission_dir}/${policy[3]}"
comparator_config="${policy[4]}"

rm -f "${root}/.yukon/${track}-score.json" \
  "${root}/benchmark-results/${track}-summary.md"

score_path="${submission_dir}/score.txt"
comparator_dir="${root}/.benchmark-tools/comparator"
comparator_bin="${comparator_dir}/.lake/build/bin/comparator"
lean4export_bin="${comparator_dir}/.lake/packages/lean4export/.lake/build/bin/lean4export"

bash scripts/check-submission-imports.sh "${profile}" "${submission_dir}"

centibits="$(python3 scripts/benchmark_contract.py read-scalar "${score_path}")"
claim="$(python3 scripts/benchmark_contract.py read-scalar "${claim_path}")"
python3 scripts/render-benchmark-challenge.py \
  "${profile}" "${centibits}" "${claim}" "${challenge_path}"
trap 'rm -f "${challenge_path}"' EXIT

[[ -x "${comparator_bin}" && -x "${lean4export_bin}" ]] || {
  echo "benchmark tools are missing; run ./setup.sh first" >&2
  exit 1
}

export COMPARATOR_LEAN4EXPORT="${lean4export_bin}"

if [[ "$(uname -s)" == Linux && "${BENCHMARK_INSECURE_LOCAL:-0}" != 1 ]]; then
  landrun_bin="${root}/.benchmark-tools/landrun/landrun"
  [[ -x "${landrun_bin}" ]] || { echo "landrun is missing; run ./setup.sh first" >&2; exit 1; }
  command -v systemd-run >/dev/null 2>&1 || { echo "systemd-run is required for a trusted local run" >&2; exit 1; }
  export COMPARATOR_LANDRUN="${landrun_bin}"
  systemd-run --user --wait --pipe \
    --property=RestrictAddressFamilies=~AF_UNIX \
    --setenv=PATH="${PATH}" \
    --setenv=HOME="${HOME}" \
    --setenv=COMPARATOR_LANDRUN="${COMPARATOR_LANDRUN}" \
    --setenv=COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT}" \
    --working-directory="${root}" \
    -- lake env "${comparator_bin}" "${comparator_config}"
else
  [[ "${BENCHMARK_INSECURE_LOCAL:-0}" == 1 ]] || {
    echo "set BENCHMARK_INSECURE_LOCAL=1 for a non-ranked local run on $(uname -s)" >&2
    exit 1
  }
  echo "WARNING: using Comparator's fake sandbox; this local run is not trusted" >&2
  export COMPARATOR_LANDRUN="${comparator_dir}/scripts/fake-landrun.sh"
  lake env "${comparator_bin}" "${comparator_config}"
fi

python3 scripts/write-benchmark-score.py "${profile}" "${centibits}" "${claim}"
cat "benchmark-results/${track}-summary.md"
