/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Determinant.FilteredDeterminant
import CCDN.Determinant.HypersurfaceHilbert

/-! A coefficient-independent local determinant exponent for hypersurfaces.
The exponent is an explicit finite sum depending only on dimension,
multiplicity and the number of rows, and admits sharp binomial cutoff bounds. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

section

variable (n s K k : ℕ) {μ : ℕ} (hμ : 0 < μ)

/-- Deficit exponent from the cumulative bound μ binomial(n+k,n), where n
is the hypersurface dimension. -/
def hypersurfaceMultiplicityExponent (μ s : ℕ) : ℕ :=
  Finset.univ.sum fun k : Fin s => s - μ * (n + k.val).choose n

private lemma hypersurfaceMultiplicityExponent_le_origin {K : Type*} [Field K] {n μ s : ℕ}
    (f : MvPolynomial (Fin (n + 2)) K)
    (hf : f ∈ idealOfVars (Fin (n + 2)) K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0) :
    hypersurfaceMultiplicityExponent (n + 1) μ s ≤
      filtrationExponent (fun k => Module.finrank K (originLayer f k)) s := by
  apply Finset.sum_le_sum
  intro k _
  have h := originLayer_cumulative_le f hf hμ k.val
  rw [show n + k.val + 1 = n + 1 + k.val by omega] at h
  exact Nat.sub_le_sub_left h s

include hμ in
private lemma hypersurface_cumulative_capacity_ge :
    k + 1 ≤ μ * (n + 1 + k).choose (n + 1) := by
  have h := Nat.choose_le_choose k (show 1 + k ≤ n + 1 + k by omega)
  rw [Nat.choose_symm_add (a := n + 1)]
  rw [Nat.add_comm 1 k, Nat.choose_succ_self_right] at h
  nlinarith

/-- Hockey-stick identity: `∑_{k < K} (n + k).choose n = (n + K).choose (n + 1)`. -/
lemma sum_cumulative_binomial :
    (∑ k ∈ Finset.range K, (n + k).choose n) = (n + K).choose (n + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    grind [Finset.sum_range_succ, Nat.choose_succ_succ']

include hμ in
/-- Cutoffs beyond s add no positive deficits. Hence the finite
exponent controls every numerical cutoff. -/
private lemma sum_hypersurface_deficits_le :
    (∑ k ∈ Finset.range K, (s - μ * (n + 1 + k).choose (n + 1))) ≤
      hypersurfaceMultiplicityExponent (n + 1) μ s := by
  unfold hypersurfaceMultiplicityExponent
  rw [Fin.sum_univ_eq_sum_range (fun k => s - μ * (n + 1 + k).choose _)]
  by_cases hK : K ≤ s
  gcongr
  · apply le_of_eq ((Finset.sum_subset (Finset.range_mono (by omega)) (f := fun k => s - μ * (n + 1 + k).choose _)) ?_).symm
    intro k _ hk
    have hs := by simpa using hk
    have hc := hypersurface_cumulative_capacity_ge n k hμ
    omega

include hμ in
/-- Exact integer cutoff inequality. Optimizing K gives the leading
(n!/μ)^(1/n) * n/(n+1) * s^(1+1/n) term of CCDN's local determinant bound. -/
theorem hypersurfaceMultiplicityExponent_cutoff :
    s * K ≤ hypersurfaceMultiplicityExponent (n + 1) μ s +
      μ * (n + 1 + K).choose (n + 2) := by
  have hsum := Finset.sum_le_sum (s := Finset.range K)
    (f := fun _ => s)
    (g := fun k => (s - μ * (n + 1 + k).choose (n + 1)) +
      μ * (n + 1 + k).choose (n + 1)) (by omega)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_cumulative_binomial] at hsum
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  nlinarith [sum_hypersurface_deficits_le n s K hμ]

end

/-- Every evaluation determinant in one hypersurface residue class has the
explicit dimension/multiplicity divisor, even for zeros only modulo that power. -/
theorem hypersurface_pow_dvd_det_mod {p n μ s : ℕ} [Fact p.Prime]
    (f : IntegerPolynomial (n + 2))
    (hf : residueEquation p f ∈ idealOfVars (Fin (n + 2)) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (residueEquation p f) ≠ 0)
    (x : Fin s → Fin (n + 2) → ℤ) (hx : ∀ i j, (p : ℤ) ∣ x i j)
    (hfx : ∀ i, (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣ eval (x i) f)
    (F : Fin s → IntegerPolynomial (n + 2)) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
      (valueMatrix x F).det :=
  origin_filtration_pow_dvd_det_mod f x hx
    (hypersurfaceMultiplicityExponent_le_origin _ hf hμ) hfx F

end
end CCDN
