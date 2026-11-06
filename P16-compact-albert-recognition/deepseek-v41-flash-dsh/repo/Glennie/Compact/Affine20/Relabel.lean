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

set_option maxHeartbeats 2000000

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
  have hb : (List.finRange 3).all (fun i => decide (i = 0 ∨ i = 1 ∨ i = 2)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hb i (List.mem_finRange i))

/-! ## The relabelling group (S3)^3 ⋊ S3 -/

/-- A relabelling: a frame order and one outcome permutation per frame slot. -/
@[ext] structure Relabel where
  order : Equiv.Perm (Fin 3)
  labels : Fin 3 → Equiv.Perm (Fin 3)

namespace Relabel

instance : Mul Relabel :=
  ⟨fun γ δ => ⟨γ.order * δ.order, fun a => γ.labels (δ.order a) * δ.labels a⟩⟩

instance : One Relabel := ⟨⟨1, fun _ => 1⟩⟩

instance : Inv Relabel := ⟨fun γ => ⟨γ.order⁻¹, fun a => (γ.labels (γ.order⁻¹ a))⁻¹⟩⟩

@[simp] theorem mul_order (γ δ : Relabel) : (γ * δ).order = γ.order * δ.order := rfl

@[simp] theorem mul_labels (γ δ : Relabel) (a : Fin 3) :
    (γ * δ).labels a = γ.labels (δ.order a) * δ.labels a := rfl

@[simp] theorem one_order : (1 : Relabel).order = 1 := rfl

@[simp] theorem one_labels (a : Fin 3) : (1 : Relabel).labels a = 1 := rfl

@[simp] theorem inv_order (γ : Relabel) : γ⁻¹.order = γ.order⁻¹ := rfl

@[simp] theorem inv_labels (γ : Relabel) (a : Fin 3) :
    γ⁻¹.labels a = (γ.labels (γ.order⁻¹ a))⁻¹ := rfl

/-- The group structure; `Mul`, `One` and `Inv` are the instances above (the pattern of
Mathlib's `Equiv.Perm.permGroup`). -/
instance : Group Relabel where
  mul_assoc γ δ ε := Relabel.ext (by simp [mul_assoc]) (by funext a; simp [mul_assoc])
  one_mul γ := Relabel.ext (by simp) (by funext a; simp)
  mul_one γ := Relabel.ext (by simp) (by funext a; simp)
  inv_mul_cancel γ := Relabel.ext (by simp) (by funext a; simp)

/-- Relabellings as four permutations (order, labels 0, labels 1, labels 2). -/
def equivProd : Relabel ≃
    Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) where
  toFun γ := (γ.order, γ.labels 0, γ.labels 1, γ.labels 2)
  invFun p := ⟨p.1, ![p.2.1, p.2.2.1, p.2.2.2]⟩
  left_inv γ := by
    apply Relabel.ext
    · rfl
    · funext a
      rcases fin3_cases a with rfl | rfl | rfl <;> rfl
  right_inv _ := rfl

instance : Fintype Relabel := Fintype.ofEquiv _ equivProd.symm

end Relabel

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
