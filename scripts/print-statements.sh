#!/bin/sh
# Prints the statement of every theorem pinned in WritProofs/Axioms.lean, in pin order, without
# its proof: a line "== Writ.Proofs.<name>" and then what `#check @Writ.Proofs.<name>` prints.
# With --defs it then prints `#print` of every def, structure and inductive declared in
# WritProofs that a pinned statement mentions, and of every such declaration those mention in
# turn, with the equations of the recursive ones, and last a line per function outside
# WritProofs (kernel or Core) that those statements and definitions use, with its module. Run
# `lake build` first. Exit 0 on success, 1 if Lean reports an error, 2 on an unknown argument.
set -u
cd "$(dirname "$0")/.." || exit 1

usage() {
  echo "usage: scripts/print-statements.sh [--defs]" >&2
  exit 2
}
defs=0
case "${1:-}" in
  "") ;;
  --defs) defs=1 ;;
  *) usage ;;
esac
[ "$#" -le 1 ] || usage

names=$(sed -n 's/^#guard_msgs in #print axioms Writ\.Proofs\.\([^[:space:]]*\).*$/\1/p' WritProofs/Axioms.lean)
if [ -z "$names" ]; then
  echo "no #print axioms pins found in WritProofs/Axioms.lean" >&2
  exit 1
fi

dir=$(mktemp -d) || exit 1
trap 'rm -rf "$dir"' EXIT
# dash runs the EXIT trap on a signal only if the signal's trap exits.
trap 'exit 1' HUP INT TERM
file="$dir/Statements.lean"

{
  echo 'import Lean'
  echo 'import WritProofs'
  echo 'set_option pp.proofs false'
  echo 'set_option pp.fieldNotation true'
  for name in $names; do
    echo "#eval IO.println \"== Writ.Proofs.$name\""
    echo "#check @Writ.Proofs.$name"
  done
  if [ "$defs" -eq 1 ]; then
    echo '#eval IO.println "== definitions"'
    echo 'open Lean Elab Command in'
    echo 'run_cmd do'
    echo '  let env ← getEnv'
    printf '  let roots : List Name := ['
    sep=''
    for name in $names; do
      printf '%s`Writ.Proofs.%s' "$sep" "$name"
      sep=', '
    done
    echo ']'
    cat <<'EOF'
  let moduleOf := fun (n : Name) =>
    match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => Name.anonymous
  let fromProofs := fun (n : Name) => (`WritProofs).isPrefixOf (moduleOf n)
  -- Constructors and projections stand for their type; matchers, recursors and other compiler
  -- auxiliaries are walked through but not printed.
  let owner := fun (n : Name) =>
    match env.find? n with
    | some (.ctorInfo c) => c.induct
    | _ => match env.getProjectionFnInfo? n with
      | some p => match env.find? p.ctorName with
        | some (.ctorInfo c) => c.induct
        | _ => n
      | none => n
  let uses := fun (c : ConstantInfo) =>
    match c with
    | .inductInfo i => i.ctors.foldl (fun acc k =>
        match env.find? k with
        | some kc => acc ++ kc.type.getUsedConstants.toList
        | none => acc) c.type.getUsedConstants.toList
    | .defnInfo d => d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList
    | _ => []
  let mut seen : NameSet := {}
  let mut shown : Array Name := #[]
  let mut outside : NameSet := {}
  let mut queue : List Name := []
  for r in roots do
    if let some c := env.find? r then
      queue := queue ++ c.type.getUsedConstants.toList
  while true do
    match queue with
    | [] => break
    | n :: rest =>
      queue := rest
      let n := owner n
      if (`Writ).isPrefixOf (moduleOf n) && !fromProofs n then
        let generated := isAuxRecursor env n || Meta.isInstanceCore env n ||
          n matches .str _ "ctorIdx"
        if let some (.defnInfo _) := env.find? n then
          if !generated then outside := outside.insert n
        continue
      if seen.contains n || !fromProofs n then continue
      seen := seen.insert n
      let some c := env.find? n | continue
      match c with
      | .defnInfo _ | .inductInfo _ =>
        queue := queue ++ uses c
        let aux := n.isInternal || isAuxRecursor env n || isNoConfusion env n ||
          (Meta.Match.Extension.getMatcherInfo? env n).isSome
        if !aux then shown := shown.push n
      | _ => pure ()
  -- `#print` shows a recursive definition in its compiled form, so its equations follow it.
  let recursor := fun (c : Name) =>
    match c with
    | .str _ "brecOn" => true
    | _ => c == ``WellFounded.fix
  let recursive := fun (n : Name) =>
    match env.find? n with
    | some (.defnInfo d) => d.value.getUsedConstants.any recursor
    | _ => false
  for n in shown do
    elabCommand (← `(#print $(mkIdent n)))
    if recursive n then
      elabCommand (← `(#print eqns $(mkIdent n)))
  IO.println "== outside WritProofs"
  for n in outside.toList.toArray.qsort (·.toString < ·.toString) do
    IO.println s!"{n}  {moduleOf n}"
EOF
  fi
} > "$file"

lake env lean "$file" || exit 1
