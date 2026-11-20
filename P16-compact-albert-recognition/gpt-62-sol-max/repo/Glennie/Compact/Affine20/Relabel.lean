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

set_option quotPrecheck false in
/-- All three components of a labelled triple are frames. This notation keeps the
expanded frame condition in the public statements. -/
notation "IsFrameTriple " T:arg => (∀ a : Fin 3, Frame (T a))

/-- The complete raw ledger: the 27 triple traces C, then the pair blocks P, Q, R
(R indexed (k, i)). -/
abbrev Ledger54 :=
  (Fin 3 → Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) ×
    (Fin 3 → Fin 3 → ℝ)

end
end Glennie.Compact.Affine20

namespace Glennie.SubmissionR03
noncomputable section
open Glennie.Compact.Affine20

/-- Named Fin indices avoid compiler-generated numeral witnesses in the statement. -/
def f0 : Fin 3 := ⟨0, Nat.zero_lt_succ 2⟩
def f1 : Fin 3 := ⟨1, Nat.lt_succ_of_le (Nat.le_succ 1)⟩
def f2 : Fin 3 := ⟨2, Nat.lt_succ_self 2⟩
def b0 : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩
def b1 : Fin 2 := ⟨1, Nat.lt_succ_self 1⟩

@[simp] theorem f0_eq : f0 = (0 : Fin 3) := rfl
@[simp] theorem f1_eq : f1 = (1 : Fin 3) := rfl
@[simp] theorem f2_eq : f2 = (2 : Fin 3) := rfl

/-- The complete triple-trace block and three pair-trace blocks. -/
def fullLedger (T : Triple) : Ledger54 :=
  (ledger (T f0) (T f1) (T f2),
   fun i j => inner (T f0 i) (T f1 j),
   fun j k => inner (T f1 j) (T f2 k),
   fun k i => inner (T f2 k) (T f0 i))

/-- A single automorphism acts on every label of all three frames. -/
def mapAtoms (g : CompactAutomorphism) (T : Triple) : Triple :=
  fun a i => g.equiv (T a i)

end
end Glennie.SubmissionR03

namespace Glennie.Compact.Affine20
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

export Glennie.SubmissionR03 (mapAtoms)

abbrev ledger54 := Glennie.SubmissionR03.fullLedger

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

theorem mapAtoms_slot (g : CompactAutomorphism) (T : Triple) (a : Fin 3) :
    mapAtoms g T a = fun i => g.equiv (T a i) := rfl

/-! Projections of the 54-entry ledger, on variables. Proofs rewrite with these before any
comparison, so no unification has to unfold Albert products. -/

theorem ledger54_C (T : Triple) (i j k : Fin 3) :
    (ledger54 T).1 i j k = ledger (T 0) (T 1) (T 2) i j k := rfl

theorem ledger54_Q (T : Triple) (j k : Fin 3) :
    (ledger54 T).2.2.1 j k = inner (T 1 j) (T 2 k) := rfl

theorem ledger54_R (T : Triple) (k i : Fin 3) :
    (ledger54 T).2.2.2 k i = inner (T 2 k) (T 0 i) := rfl

theorem ledger54_map (g : CompactAutomorphism) (T : Triple) :
    ledger54 (mapAtoms g T) = ledger54 T := by
  simp [ledger54, Glennie.SubmissionR03.fullLedger, mapAtoms_slot, g.inner_map]
  funext i j k
  exact g.ledger_map _ _ _ i j k

end
end Glennie.Compact.Affine20
