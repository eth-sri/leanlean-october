/- The 1296-element relabelling group and the raw
54-entry ledger.
  * `Relabel`: a frame order σ ∈ S3 and one outcome permutation ℓ_a ∈ S3 per frame slot,
    with the wreath (semidirect) multiplication; `card_relabel : Fintype.card Relabel = 1296`.
  * `relabelTriple γ T a i = T (σ a) (ℓ_a i)` (the action of the RobustBranches
    `relabel`). It is a right action: `relabelTriple (γ * δ) = relabelTriple δ ∘ relabelTriple γ`.
  * `ledger54`: the complete raw ledger (C, P, Q, R; R indexed (k, i)).
  * `ledgerAct γ`: the induced permutation of the 54 coordinates;
    `ledger54_relabel : ledger54 (relabelTriple γ T) = ledgerAct γ (ledger54 T)` for every
    triple (no frame hypothesis), from the symmetry of the trace form.
  * `ledger54_map`: invariance under every `CompactAutomorphism`.
Finite facts about Fin 3 are kernel-checked Boolean checks (`decide +kernel` on lists of
Fin 3, no reals). No chart, rank or analytic statement is made here.
Proof method: projections of the ledger are related to their
values only through rfl lemmas on variables (`ledger54_C/P/Q/R`, `ledgerAct_C/P/Q/R`,
`pairExt_xy`) used by rw/simp only; no rfl, exact or show compares two different
Albert-valued structures. -/
module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Aesop

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

/-! ## Triples and the 54-entry ledger -/

/-- Three ordered frames of three atoms each. -/
abbrev Triple := Fin 3 → Fin 3 → Albert

/-- The complete raw ledger: the 27 triple traces C, then the pair blocks P, Q, R
(R indexed (k, i)). -/
abbrev Ledger54 :=
  (Fin 3 → Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) ×
    (Fin 3 → Fin 3 → ℝ)

/-- The 54-entry raw ledger of a triple: C = T((p_i o q_j) o r_k), P = T(p_i o q_j),
Q = T(q_j o r_k), R = T(r_k o p_i). -/
def ledger54 (T : Triple) : Ledger54 :=
  (ledger (T 0) (T 1) (T 2), fun i j => inner (T 0 i) (T 1 j),
    fun j k => inner (T 1 j) (T 2 k), fun k i => inner (T 2 k) (T 0 i))

/-- Fin 3 has exactly the elements 0, 1, 2 (kernel-checked Boolean list check). -/
theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  omega

/-- Pointwise transport by a compact automorphism. -/
def mapAtoms (g : CompactAutomorphism) (T : Triple) : Triple :=
  fun a i => g.equiv (T a i)

theorem mapAtoms_apply (g : CompactAutomorphism) (T : Triple) (a i : Fin 3) :
    mapAtoms g T a i = g.equiv (T a i) := rfl

theorem mapAtoms_slot (g : CompactAutomorphism) (T : Triple) (a : Fin 3) :
    mapAtoms g T a = fun i => g.equiv (T a i) := rfl

/-! Projections of the 54-entry ledger, on variables. Proofs rewrite with these before any
comparison, so no unification has to unfold Albert products. -/

theorem ledger54_C (T : Triple) (i j k : Fin 3) :
    (ledger54 T).1 i j k = ledger (T 0) (T 1) (T 2) i j k := rfl

theorem ledger54_P (T : Triple) (i j : Fin 3) :
    (ledger54 T).2.1 i j = inner (T 0 i) (T 1 j) := rfl

theorem ledger54_Q (T : Triple) (j k : Fin 3) :
    (ledger54 T).2.2.1 j k = inner (T 1 j) (T 2 k) := rfl

theorem ledger54_R (T : Triple) (k i : Fin 3) :
    (ledger54 T).2.2.2 k i = inner (T 2 k) (T 0 i) := rfl

theorem ledger54_map (g : CompactAutomorphism) (T : Triple) :
    ledger54 (mapAtoms g T) = ledger54 T := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext i j k
    rw [ledger54_C, ledger54_C, mapAtoms_slot, mapAtoms_slot, mapAtoms_slot]
    exact g.ledger_map (T 0) (T 1) (T 2) i j k
  · funext i j
    rw [ledger54_P, ledger54_P, mapAtoms_apply, mapAtoms_apply]
    exact g.inner_map (T 0 i) (T 1 j)
  · funext j k
    rw [ledger54_Q, ledger54_Q, mapAtoms_apply, mapAtoms_apply]
    exact g.inner_map (T 1 j) (T 2 k)
  · funext k i
    rw [ledger54_R, ledger54_R, mapAtoms_apply, mapAtoms_apply]
    exact g.inner_map (T 2 k) (T 0 i)

/-! ## Finite facts about Fin 3 (kernel-checked Boolean lists) -/

/-! ## Symmetry of the triple trace -/

/-! ## The induced action on the 54 coordinates -/

end
end Glennie.Compact.Affine20
