module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization

public section

namespace NumberField

open Finset Function Height Real

variable {K : Type*} [Field K] [NumberField K] {ι ι' : Type*} [Fintype ι] [Fintype ι']

@[expose] noncomputable def arakelovMulHeight (x : ι → K) : ℝ :=
  have : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then 1 else
    (∏ v : InfinitePlace K, (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ)) *
      ∏ᶠ v : FinitePlace K, ⨆ i, v (x i)

lemma arakelovMulHeight_eq {x : ι → K} (hx : x ≠ 0) :
    arakelovMulHeight x =
      (∏ v : InfinitePlace K, (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ)) *
        ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
  simp [arakelovMulHeight, hx]

@[simp]
lemma arakelovMulHeight_zero : arakelovMulHeight (0 : ι → K) = 1 := by
  simp [arakelovMulHeight]

private lemma sq_rpow_div_two {a : ℝ} (ha : 0 ≤ a) (n : ℕ) : (a ^ 2) ^ ((n : ℝ) / 2) = a ^ n := by
  rw [← Real.rpow_natCast a n, ← Real.rpow_natCast a 2, ← Real.rpow_mul ha]
  congr 1
  push_cast
  ring

section Smul

variable {κ : Type*}

omit [NumberField K] in
private lemma iSup_smul_eq {F : Type*} [FunLike F K ℝ] [MonoidWithZeroHomClass F K ℝ]
    [NonnegHomClass F K ℝ] (v : F) (c : K) (x : κ → K) :
    ⨆ i, v ((c • x) i) = v c * ⨆ i, v (x i) := by
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Real.mul_iSup_of_nonneg (apply_nonneg v c)]

private lemma prod_infinitePlace_mul_finprod_iSup_smul [Finite κ] {x : κ → K} (hx : x ≠ 0)
    {c : K} (hc : c ≠ 0) :
    (∏ v : InfinitePlace K, v c ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ i, v ((c • x) i) =
      ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
  have hcx : c • x ≠ 0 := by simp [hc, hx]
  have hA : (0 : ℝ) < ∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
    exact prod_pos fun v _ ↦ pow_pos
      ((v.pos_iff.mpr hi).trans_le (Finite.le_ciSup_of_le i le_rfl)) _
  have h := Height.mulHeight_smul_eq_mulHeight x hc
  rw [NumberField.mulHeight_eq hcx, NumberField.mulHeight_eq hx] at h
  simp only [iSup_smul_eq, mul_pow, prod_mul_distrib] at h ⊢
  exact mul_left_cancel₀ hA.ne' (by linear_combination h)

lemma arakelovMulHeight_smul_eq (x : ι → K) {c : K} (hc : c ≠ 0) :
    arakelovMulHeight (c • x) = arakelovMulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have hcx : c • x ≠ 0 := by simp [hc, hx]
  have harch (v : InfinitePlace K) :
      (∑ i, v ((c • x) i) ^ 2) ^ (v.mult / 2 : ℝ)
        = v c ^ v.mult * (∑ i, v (x i) ^ 2) ^ (v.mult / 2 : ℝ) := by
    have hsum : ∑ i, v ((c • x) i) ^ 2 = v c ^ 2 * ∑ i, v (x i) ^ 2 := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by simp [mul_pow]
    rw [hsum, Real.mul_rpow (by positivity) (by positivity),
      sq_rpow_div_two (apply_nonneg v c) v.mult]
  rw [arakelovMulHeight_eq hcx, arakelovMulHeight_eq hx]
  simp only [harch, prod_mul_distrib]
  rw [mul_right_comm, prod_infinitePlace_mul_finprod_iSup_smul hx hc, mul_comm]

end Smul

lemma arakelovMulHeight_comp_equiv (e : ι ≃ ι') (x : ι' → K) :
    arakelovMulHeight (x ∘ e) = arakelovMulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : x ∘ e ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
    exact ne_iff.mpr ⟨e.symm i, by simpa using hi⟩
  have hsum (v : InfinitePlace K) : ∑ i, v (x (e i)) ^ 2 = ∑ i, v (x i) ^ 2 :=
    e.sum_comp fun i ↦ v (x i) ^ 2
  have hsup (v : FinitePlace K) : ⨆ i, v (x (e i)) = ⨆ i, v (x i) :=
    e.iSup_congr (congrFun rfl)
  rw [arakelovMulHeight_eq hx, arakelovMulHeight_eq hx']
  simp only [comp_apply, hsum, hsup]

end NumberField

namespace Projectivization

open NumberField Real

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

private lemma arakelovMulHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K)
    (h : a.val = t • b.val) :
    NumberField.arakelovMulHeight a.val = NumberField.arakelovMulHeight b.val :=
  have ht : t ≠ 0 := by
    contrapose! h
    simpa [h] using a.prop
  h ▸ arakelovMulHeight_smul_eq _ ht

noncomputable def arakelovMulHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun r ↦ NumberField.arakelovMulHeight r.val) arakelovMulHeight_aux

lemma arakelovMulHeight_mk {x : ι → K} (hx : x ≠ 0) :
    arakelovMulHeight (mk K x hx) = NumberField.arakelovMulHeight x := by
  rfl

end Projectivization
end
