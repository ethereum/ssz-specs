import Lean

/-!
Reject nonstandard axioms anywhere in the native implementation or its proofs.

EthLib's `check-decls` checks the specification; this checks what is built here on top of it.
-/

open Lean Elab Command in
elab "audit_native" : command => do
  -- Audit imported declarations as well as local ones, so new proofs need no registry entry.
  let environment ← getEnv
  for (name, _) in environment.constants.toList do
    -- Private helper declarations are checked under their original namespace as well.
    let publicName := (privateToUserName? name).getD name
    if (`EthLib.Consensus.Ssz.Native).isPrefixOf publicName then
      -- Every transitive axiom dependency must be one of Lean's three standard logical axioms.
      for assumption in ← Lean.collectAxioms name do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains assumption do
          throwError "{name} depends on forbidden axiom {assumption}"
