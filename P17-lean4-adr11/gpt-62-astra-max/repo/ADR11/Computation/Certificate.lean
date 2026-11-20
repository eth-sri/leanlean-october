module
public import ADR11.Computation.Sparse
public import ADR11.Trees.Metric

/-! Certify equalities by collecting coefficients of equal monomials.
A point query extracts the probability of an unrooted topology. -/
@[expose] public section
namespace ADR11.Computation.Sparse
open Finset Real
variable {n : ℕ}

private theorem agrees_sound (z : ℕ → ℝ) {P Q : Poly} (h : agrees P Q = true) : eval z P = eval z Q := by
  let S := ((P+Q).map Prod.snd).toFinset
  have byKey (D : Poly) (sub : ∀ t ∈ D, t.2 ∈ S) : eval z D = ∑ k ∈ S, coeff D k * mon z k := by
    induction D using Multiset.induction_on with
    | empty => simp [coeff]
    | cons t D ih =>
      have step (k) : coeff (t ::ₘ D) k = (if t.2=k then t.1 else 0) + coeff D k := by
        by_cases e : t.2=k <;> simp [coeff,e]
      rw [eval_cons,ih (fun t ht => sub t (Multiset.mem_cons_of_mem ht))]
      simp [step,apply_ite,ite_mul,add_mul,sum_add_distrib,sub t (by simp)]
  have apart (D E : Poly) (eqn : P+Q = D+E) : ∀ t ∈ D, t.2 ∈ S := by
    intro t ht; simp [S,eqn]; grind
  rw [byKey P (apart P Q rfl),byKey Q (apart Q P (add_comm ..))]
  exact sum_congr rfl fun k hk => by rw [(of_decide_eq_true h : ∀ k ∈ S, coeff P k = coeff Q k) k hk]

noncomputable def branch (σ : SpeciesTree (Fin n)) (c : ℕ) := exp (-σ.edge (decC n c))
@[simp] theorem branch_pos (σ : SpeciesTree (Fin n)) (c : ℕ) : 0 < branch σ c := exp_pos _
theorem branch_le (σ : SpeciesTree (Fin n)) (c : ℕ) : branch σ c ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (σ.edge_nonneg _))

private theorem eval_trim (σ : SpeciesTree (Fin n)) (P : Poly) : eval (coords σ.length) (trim σ.clusters P) = eval (branch σ) P := by
  have pad (k : Key) : mon (coords σ.length) (k.filter fun c => decC n c ∈ σ.clusters.erase univ) = mon (branch σ) k := by
    induction k using Multiset.induction_on with
    | empty => rfl
    | cons c k ih => by_cases h : decC n c ∈ σ.clusters.erase univ <;> simp_all [mon,branch,coords,SpeciesTree.edge]
  simp [eval,trim,Multiset.map_map,-mem_erase,pad]

theorem likelihood (σ : SpeciesTree (Fin n)) {T : Family n} {P : Poly}
    (hc : verifies σ.clusters T P = true) : σ.unrootedDist id T = eval (branch σ) P := by
  rw [← eval_observed,← eval_trim]; exact agrees_sound _ hc

end ADR11.Computation.Sparse
