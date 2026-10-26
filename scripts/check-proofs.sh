#!/usr/bin/env bash
# Checks that WritProofs uses no escape hatch (sorry, admit, native_decide, unsafe, axiom), that
# every axiom list pinned in WritProofs/Axioms.lean names only propext, Classical.choice and
# Quot.sound, and that every Lean name the README's Proof status section cites as proved has its
# axioms pinned by a `#print axioms Writ.Proofs.<name>` line there, and that every pinned name
# appears backticked in docs/theorems.md. A trailing `*` in a README name matches any suffix; the
# literal `accepted_iff_*` in docs/theorems.md stands for every `accepted_iff_` name. Exit 0 when all
# four hold, 1 otherwise.
set -euo pipefail
cd "$(dirname "$0")/.."

status=0

escapes=$(grep -rnwE 'sorry|admit|native_decide|unsafe' WritProofs || true)
axioms=$(grep -rnE "^[[:space:]]*((private|protected)[[:space:]]+)*axiom([^A-Za-z0-9_']|$)" WritProofs || true)
if [ -n "$escapes$axioms" ]; then
  echo "escape hatches in WritProofs:"
  printf '%s\n' "$escapes" "$axioms" | sed '/^$/d; s/^/  /'
  status=1
fi

# A pinned list is an `info:` message in a `/-- ... -/` block, which Lean wraps over several
# lines when it is long.
bad_axioms=$(awk -v q="'" '
  /^(\/-- )?info:/ { buf = ""; inside = 1 }
  inside { buf = buf " " $0 }
  inside && /-\// {
    inside = 0
    split(buf, part, q)
    name = part[2]
    if (buf ~ /does not depend on any axioms/) next
    if (!match(buf, /depends on axioms: \[[^]]*\]/)) { print name ": unreadable axiom list"; next }
    list = substr(buf, RSTART + 20, RLENGTH - 21)
    n = split(list, ax, ",")
    for (i = 1; i <= n; i++) {
      a = ax[i]
      gsub(/[[:space:]]/, "", a)
      if (a != "propext" && a != "Classical.choice" && a != "Quot.sound") print name ": " a
    }
  }
' WritProofs/Axioms.lean)
if [ -n "$bad_axioms" ]; then
  echo "pinned axioms other than propext, Classical.choice, Quot.sound in WritProofs/Axioms.lean:"
  printf '%s\n' "$bad_axioms" | sed 's/^/  /'
  status=1
fi

# Only table rows whose Status cell claims a proof and the section's list items are read: prose
# and "not yet proved" rows may name things that are not theorems (a mode, a layer-2 function).
names=$(awk '
  /^## Proof status/ { inside = 1; next }
  inside && /^## / { inside = 0 }
  !inside { next }
  /^\|/ {
    split($0, cell, "|")
    status = cell[4]
    sub(/^[[:space:]]+/, "", status)
    if (status ~ /^not yet proved/) next
  }
  /^\|/ || /^- / {
    n = split($0, part, "`")
    for (i = 2; i < n; i += 2) print part[i]
  }
' README.md | { grep -E "^[A-Za-z_][A-Za-z0-9_.']*[*]?$" || true; } | { grep -vE '\.lean$' || true; } | sort -u)

if [ -z "$names" ]; then
  echo "no theorem names found in the README Proof status section"
  exit 1
fi

pinned=$(sed -n 's/^#guard_msgs in #print axioms Writ\.Proofs\.\([^[:space:]]*\).*$/\1/p' WritProofs/Axioms.lean)

missing=""
count=0
while IFS= read -r name; do
  count=$((count + 1))
  case "$name" in
    *'*')
      prefix=${name%'*'}
      found=$(printf '%s\n' "$pinned" | awk -v p="$prefix" 'index($0, p) == 1 { print; exit }')
      ;;
    *)
      found=$(printf '%s\n' "$pinned" | grep -xF -- "$name" || true)
      ;;
  esac
  [ -n "$found" ] || missing="$missing  $name"$'\n'
done <<< "$names"

if [ -n "$missing" ]; then
  echo "README names without a #print axioms line in WritProofs/Axioms.lean:"
  printf '%s' "$missing"
  status=1
fi

undocumented=""
pins=0
while IFS= read -r name; do
  [ -n "$name" ] || continue
  pins=$((pins + 1))
  grep -qF -- "\`$name\`" docs/theorems.md && continue
  case "$name" in
    accepted_iff_*) grep -qF -- '`accepted_iff_*`' docs/theorems.md && continue ;;
  esac
  undocumented="$undocumented  $name"$'\n'
done <<< "$pinned"

if [ -n "$undocumented" ]; then
  echo "names pinned in WritProofs/Axioms.lean but not backticked in docs/theorems.md:"
  printf '%s' "$undocumented"
  status=1
fi

if [ "$status" -eq 0 ]; then
  echo "proofs ok: $count README names pinned in WritProofs/Axioms.lean, all $pins pinned names in docs/theorems.md, only standard axioms, no escape hatches"
fi
exit "$status"
