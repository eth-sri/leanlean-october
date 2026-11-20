module

public import Glennie.Automorphism
public import Glennie.Native.AlgebraLaws
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Glennie.Compact.Affine20

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Triples and the 54-entry ledger -/

/-- Three ordered frames of three atoms each. -/
abbrev Triple := Fin 3 → Fin 3 → Albert

/-- The complete raw ledger: the 27 triple traces C, then the pair blocks P, Q, R
(R indexed (k, i)). -/
abbrev Ledger54 :=
  (Fin 3 → Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) ×
    (Fin 3 → Fin 3 → ℝ)

end
end Glennie.Compact.Affine20
