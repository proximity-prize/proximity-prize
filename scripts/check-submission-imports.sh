#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -ne 2 ]]; then
  echo "usage: check-submission-imports.sh PROFILE SUBMISSION_DIR" >&2
  exit 2
fi

profile="$1"
submission_dir="$2"
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# `mapfile` needs bash >= 4; macOS ships 3.2.
policy=()
while IFS= read -r line; do policy+=("${line}"); done \
  < <(python3 "${script_dir}/benchmark_profiles.py" imports "${profile}")
[[ "${#policy[@]}" -eq 3 ]] || { echo "invalid submission profile: ${profile}" >&2; exit 2; }
submission_module="${policy[0]}"
target_module="${policy[1]}"
claim_file="${policy[2]}"

[[ -d "${submission_dir}" && ! -L "${submission_dir}" ]] || {
  echo "missing submission directory: ${submission_dir}" >&2
  exit 1
}

# Blank every comment and string-literal interior to whitespace (preserving line
# structure) so the textual audits below inspect real code, not prose or string
# data. This is what keeps the audits both correct and strict:
#   - without it, a sentence in a /- -/ comment that wraps onto "module ..." or
#     mentions "#eval" is wrongly rejected (a false positive), and
#   - a string such as "--" or "/-" could otherwise start a fake comment that
#     hides the following real code from the scan (a bypass).
# It mirrors the service's semantic checks in spirit: audit the code, not text.
strip_comments() {
  python3 - "$1" <<'PY'
import sys

data = open(sys.argv[1], "r", encoding="utf-8", errors="surrogateescape").read()
out = []
i, n = 0, len(data)
NORMAL, LINE, BLOCK, STRING = range(4)
state, depth = NORMAL, 0
while i < n:
    c = data[i]
    two = data[i : i + 2]
    if state == NORMAL:
        if two == "--":
            state = LINE; out.append("  "); i += 2; continue
        if two == "/-":
            state = BLOCK; depth = 1; out.append("  "); i += 2; continue
        if c == '"':
            state = STRING; out.append('"'); i += 1; continue
        out.append(c); i += 1; continue
    if state == LINE:
        if c == "\n":
            state = NORMAL; out.append("\n")
        else:
            out.append(" ")
        i += 1; continue
    if state == BLOCK:
        if two == "/-":
            depth += 1; out.append("  "); i += 2; continue
        if two == "-/":
            depth -= 1; out.append("  "); i += 2
            if depth == 0:
                state = NORMAL
            continue
        out.append("\n" if c == "\n" else " "); i += 1; continue
    # STRING: keep the delimiters, blank the interior (so string data never
    # reads as a comment marker, a module header, or a forbidden construct).
    if c == "\\" and i + 1 < n:
        out.append("  "); i += 2; continue
    if c == '"':
        out.append('"'); state = NORMAL; i += 1; continue
    out.append("\n" if c == "\n" else " "); i += 1; continue
sys.stdout.write("".join(out))
PY
}

if find "${submission_dir}" -type l -print -quit | grep -q .; then
  echo "submission tree may not contain symbolic links" >&2
  exit 1
fi

if find "${submission_dir}" -mindepth 1 -type d -print -quit | grep -q .; then
  echo "submission tree must be flat: subdirectories are not allowed" >&2
  exit 1
fi

# Use NUL delimiters throughout so unusual Git filenames cannot split into
# separate apparent artifacts and bypass the allowlist.
while IFS= read -r -d '' artifact; do
  relative="${artifact#"${submission_dir}"/}"
  case "${relative}" in
    */*)
      # The service source policy is layout: flat -- a nested file is rejected
      # as source_rejected before verification. Fail here, with a clear message,
      # instead of letting a local run pass and the submission fail remotely.
      # (Checked first: a nested *.lean matches both this and the suffix arm.)
      echo "submission tree must be flat: ${relative} is inside a subdirectory" >&2
      echo "move every .lean helper directly under ${submission_dir} (no subdirectories)" >&2
      exit 1
      ;;
    *.lean|score.txt|"${claim_file}") ;;
    *)
      echo "unsupported artifact in submission tree: ${artifact}" >&2
      exit 1
      ;;
  esac
done < <(find "${submission_dir}" -type f -print0)

for required in Solution.lean score.txt "${claim_file}"; do
  [[ -f "${submission_dir}/${required}" && ! -L "${submission_dir}/${required}" ]] || {
    echo "missing submission artifact: ${submission_dir}/${required}" >&2
    exit 1
  }
done

while IFS= read -r -d '' source; do
  # Audit the comment/string-stripped code, never the raw text.
  code="$(strip_comments "${source}")"

  # The Lean module system (`module` header with `public`/`private`/`meta
  # import`) changes import syntax in ways a token scanner cannot audit
  # reliably, and submissions have no need for it. Reject it outright.
  if printf '%s\n' "${code}" | grep -qE \
      '^[[:space:]]*(module([[:space:]]|$)|(public|private|meta)[[:space:]]+import([[:space:]]|$))'; then
    echo "${source} uses the Lean module system, which submissions may not use" >&2
    exit 1
  fi
  # Reject build-time code execution and kernel-bypass constructs. Custom
  # elaborators, macros, and run_tac can execute after the audited import block
  # and dynamically load another challenge, so they are forbidden too.
  if printf '%s\n' "${code}" | grep -qE '(^|[^[:alnum:]_])(run_cmd|run_elab|initialize|implemented_by|extern)([^[:alnum:]_]|$)|#eval|#exit|debug\.skipKernelTC'; then
    echo "${source} uses build-time execution or kernel-bypass constructs, which submissions may not use" >&2
    exit 1
  fi
  if printf '%s\n' "${code}" | grep -qE '(^|[^[:alnum:]_])(run_tac|builtin_initialize|elab|elab_rules|macro|macro_rules|syntax|syntax_cat|command_elab|term_elab|tactic_elab|builtin_command_elab|builtin_term_elab|builtin_tactic|importModules|importModulesCore|withImportModules|setEnv|modifyEnv|addDecl)([^[:alnum:]_]|$)'; then
    echo "${source} uses metaprogramming that can bypass the import boundary" >&2
    exit 1
  fi
  # Keep the accepted import grammar intentionally small: one module per line,
  # in a leading import block. Lean otherwise accepts continuations such as
  # `import\n  Mathlib`, which a line-oriented allowlist can miss.
  modules="$(printf '%s\n' "${code}" | awk '
    BEGIN { imports = 1 }
    /^[[:space:]]*$/ { next }
    imports && $1 == "import" {
      if (NF != 2 || $2 !~ /^[A-Za-z_][A-Za-z0-9_.]*$/) exit 2
      print $2
      next
    }
    imports && $0 ~ /^[[:space:]]*[A-Za-z_][A-Za-z0-9_.]*[[:space:]]*$/ {
      exit 2
    }
    { imports = 0 }
    $1 == "import" { exit 2 }
  ')" || {
    echo "${source} must use one module per import line in its initial import block" >&2
    exit 1
  }

  while IFS= read -r module; do
    [[ -n "${module}" ]] || continue
    if [[ "${module}" == "${target_module}" ]]; then
      continue
    fi
    # The trusted libraries the challenge itself is built from, which ship
    # precompiled in the verifier image.
    case "${module}" in
      Mathlib|Mathlib.*|ArkLib|ArkLib.*|CompPoly|CompPoly.*)
        continue
        ;;
    esac
    if [[ "${module}" != "${submission_module}"* ]]; then
      echo "${source} imports untrusted module ${module}" >&2
      echo "only ${target_module} and modules inside ${submission_dir} are allowed" >&2
      exit 1
    fi
    relative="${module#"${submission_module}"}"
    relative="${relative//.//}.lean"
    [[ -f "${submission_dir}/${relative}" ]] || {
      echo "${source} imports ${module}, which is outside ${submission_dir}" >&2
      exit 1
    }
  done <<< "${modules}"
done < <(find "${submission_dir}" -type f -name '*.lean' -print0)
