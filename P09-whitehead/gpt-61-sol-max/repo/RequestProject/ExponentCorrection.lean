import Mathlib.Tactic

import RequestProject.Commutators

/-!
# Rule 2 of Section 3.4: cancelling the exponent sums by core relators

The replacement operation `T` of Section 3.4 proceeds in three rules.  Rule 1 (the
substitution `z ↦ [a_z, b_z]`) has its group-theoretic input in
`RequestProject/HNNEmbedding.lean`, and rule 3 (factorization into `q ≥ 2` commutators) is
`RequestProject/Commutators.lean`.  This file contains rule 2:

> For a substituted extra relator `r*`, let `e ∈ ℤ^{(I)}` be its exponent vector on the
> `x_i`.  Compute `c = -M⁻¹ e` and replace this entry by `r⁰ = r* ∏_j r_j^{c_j}` in a fixed
> order.  This word has zero exponent sums in every generator.

The paper's reason for the existence of `c` is that the exponent-sum map `M` of the acyclic
core `D` is an isomorphism.  Accordingly the hypothesis used here is that `M` — the linear
map sending a coefficient vector to the corresponding combination of the exponent vectors
of the core relators — is surjective; this is all the correction needs.

The final statement, `exists_correction_commutator_factorization`, is exactly the input of
rule 3: the corrected word is a product of `q ≥ 2` commutators, so a block `B_q` can be
substituted for it.
-/




namespace FiniteChains



variable {α J : Type*} [DecidableEq α]

/-- The exponent vector of a word: its exponent sum in every generator. -/
noncomputable def expVec (w : FreeGroup α)  :=
  Multiplicative.toAdd (expSumTotal w)

@[simp] theorem expVec_apply (w : FreeGroup α) (i : α) :
    expVec w i = Multiplicative.toAdd (expSum i w) := by
  rw [expVec, expSumTotal_apply]

section
omit [DecidableEq α]
theorem expVec_mul (w w' : FreeGroup α) : expVec (w * w') = expVec w + expVec w' := by
  simp [expVec]

theorem expVec_zpow (w : FreeGroup α) (n : ℤ) : expVec (w ^ n) = n • expVec w := by
  simp [expVec]
end

variable (r : J → FreeGroup α)
/-- **The exponent-sum map `M` of the core presentation** (formula (3.1) of the paper):
a coefficient vector `c` is sent to `∑_j c_j · (exponent vector of r_j)`. -/
noncomputable def expMatrix   :=
  Finsupp.linearCombination ℤ fun j => expVec (r j)

omit [DecidableEq α] in
theorem expMatrix_apply  (c : J →₀ ℤ) :
    expMatrix r c = c.sum fun j n => n • expVec (r j) :=
  Finsupp.linearCombination_apply _ _

/-- The correcting word `∏_j r_j^{c_j}`, taken in a fixed order. -/
noncomputable def correctionWord  (c : J →₀ ℤ)  :=
  (c.support.toList.map fun j => r j ^ c j).prod

section
omit [DecidableEq α]
theorem expVec_list_prod (L : List (FreeGroup α)) :
    expVec L.prod = (L.map expVec).sum := by
  induction L <;> simp_all [expVec]

theorem expVec_correctionWord (r : J → FreeGroup α) (c : J →₀ ℤ) :
    expVec (correctionWord r c) = expMatrix r c := by simp_all [correctionWord, expVec_list_prod, expMatrix_apply, Finsupp.sum, expVec_zpow]

/-- **Rule 2.**  If the exponent-sum map of the core relators is surjective — which is the
case for an acyclic core, where it is even bijective — then every word can be corrected by
a product of core relators so that all its exponent sums vanish. -/
theorem exists_correction (r : J → FreeGroup α) (w : FreeGroup α)
    (hM : Function.Surjective (expMatrix r)) :
    ∃ c : J →₀ ℤ, expVec (w * correctionWord r c) = 0 := by
  obtain ⟨c, hc⟩ := hM (-expVec w)
  exact ⟨c, by simp_all [expVec_mul, expVec_correctionWord]⟩
end

end FiniteChains
