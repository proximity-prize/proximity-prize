#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${root}"

export PATH="${HOME}/.elan/bin:${PATH}"

readonly comparator_rev="777e7f56119efc0fac34003db4efe831e0b53723"
readonly landrun_rev="811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"
readonly tools_dir="${root}/.benchmark-tools"
readonly comparator_dir="${tools_dir}/comparator"
readonly landrun_dir="${tools_dir}/landrun"

if ! command -v elan >/dev/null 2>&1; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi

clone_at() {
  local url="$1"
  local revision="$2"
  local destination="$3"
  if [[ ! -d "${destination}/.git" ]]; then
    git clone --filter=blob:none --no-checkout "${url}" "${destination}"
  fi
  git -C "${destination}" fetch --depth=1 origin "${revision}"
  # Tool checkouts are generated cache contents. Reset tracked source changes
  # before verifying and applying any repository-owned compatibility patches.
  git -C "${destination}" checkout --detach --force "${revision}"
  [[ "$(git -C "${destination}" rev-parse HEAD)" == "${revision}" ]]
  [[ -z "$(git -C "${destination}" status --porcelain --untracked-files=no)" ]] || {
    echo "generated tool checkout is dirty: ${destination}" >&2
    exit 1
  }
}

mkdir -p "${tools_dir}"
clone_at https://github.com/leanprover/comparator.git "${comparator_rev}" "${comparator_dir}"

# Comparator's fresh-environment replay ignores declaration-local recursion
# limits and cannot replay CompPoly's checked KoalaBear.Ext6 irreducibility
# certificate.  Keep Comparator's structural/axiom export checks, but recheck
# every untrusted submission module with Lean's kernel against the already
# audited imports in a read-only Landrun sandbox.  Build both tools with this
# repository's exact Lean release so their olean format and kernel agree.
cp lean-toolchain "${comparator_dir}/lean-toolchain"
git -C "${comparator_dir}" apply --check "${root}/benchmark/comparator-leanchecker.patch"
git -C "${comparator_dir}" apply "${root}/benchmark/comparator-leanchecker.patch"
lake -d "${comparator_dir}" build lean4export comparator

if [[ "$(uname -s)" == Linux && "${BENCHMARK_INSECURE_LOCAL:-0}" != 1 ]]; then
  command -v go >/dev/null 2>&1 || {
    echo "Go 1.24 or newer is required to build landrun" >&2
    exit 1
  }
  clone_at https://github.com/Zouuup/landrun.git "${landrun_rev}" "${landrun_dir}"
  (
    cd "${landrun_dir}"
    go build -trimpath -o landrun ./cmd/landrun
  )
elif [[ "$(uname -s)" == Linux ]]; then
  echo "skipping landrun build for explicitly non-ranked local setup"
fi

# Download trusted dependency sources and available precompiled Lean artifacts.
# The submitted solution is intentionally not built here; Comparator must be
# the first process to compile it.
lake exe cache get || true

# Precompile the public library root and its locked dependency closure. The
# public root imports all four protected benchmark targets.
lake build ProximityPrize

# Audit all protected contracts independently of submitted theorems.
lake env lean scripts/check-axioms.lean

# The published geometry must be the geometry Lean has. Here for the same reason
# the axiom audit is: this is the only place a built environment exists, and it
# reads only `ProximityPrize`, already built above. A property of the repository
# rather than of a submission, so it gives the same answer on every run -- about
# 8s against a build that takes minutes.
#
# The claim/proof check is deliberately NOT here, for two reasons. Its emitter
# imports all four `Submission*/Solution` modules, so running it would compile
# the submitted solution and break the invariant above -- Comparator must be the
# first process to compile it. And it would be redundant: `benchmark.sh` renders
# the trusted statement from `score.txt` and the claim file, and Comparator
# checks the submission against that, so the binding already holds here.
lake env lean --run scripts/emit-profile-geometry.lean \
  | python3 scripts/check-profile-geometry.py

echo "benchmark setup complete"
