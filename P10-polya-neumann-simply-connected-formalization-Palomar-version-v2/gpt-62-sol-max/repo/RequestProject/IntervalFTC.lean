module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public section

open MeasureTheory Set Filter AbsolutelyContinuousOnInterval
open scoped Topology

namespace PolyaNeumann

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The increments of a Banach-valued primitive are dominated by those of
its scalar norm primitive. -/
theorem absolutelyContinuousOnInterval_intervalIntegral_banach
    {f : ℝ → V} {a b c : ℝ} (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, f t) a b := by
  have hg := hf.norm.absolutelyContinuousOnInterval_intervalIntegral hc
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hg ε hε
  refine ⟨δ, hδ, fun E hE hlen => (Finset.sum_le_sum fun i hi => ?_).trans_lt
    (h E hE hlen)⟩
  obtain ⟨hx, hy⟩ := hE.1 i hi
  have hx' := hf.mono_set (uIcc_subset_uIcc hc hx)
  have hy' := hf.mono_set (uIcc_subset_uIcc hc hy)
  simp  [dist_eq_norm, Real.norm_eq_abs, intervalIntegral.integral_interval_sub_left hx' hy',
    intervalIntegral.integral_interval_sub_left hx'.norm hy'.norm,
    intervalIntegral.abs_integral_eq_abs_integral_uIoc]
  exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans (le_abs_self _)

theorem ae_hasDerivAt_intervalIntegral_banach {f : ℝ → V} {L : ℝ} (hL : 0 ≤ L)
    (hf : IntervalIntegrable f volume 0 L) :
    ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, f t) (f x) x := by
  have h := hf.ae_hasDerivAt_integral
  rw [uIcc_of_le hL] at h
  filter_upwards [h] with x hx hm
  exact hx (Ioo_subset_Icc_self hm) 0 ⟨le_rfl, hL⟩

/-- Banach-valued FTC for an absolutely continuous function with a genuine a.e. derivative. -/
theorem eq_add_intervalIntegral_of_ac_ae_deriv {f g : ℝ → V} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : IntervalIntegrable g volume a b)
    (hd : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    ∀ θ ∈ uIcc a b, f θ = f a + ∫ s in a..θ, g s := by
  let P (x : ℝ) := ∫ s in a..x, g s
  have hP := absolutelyContinuousOnInterval_intervalIntegral_banach hg (by simp : a ∈ uIcc a b)
  have hz : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt (f - P) 0 x := by
    filter_upwards [hd, hg.ae_hasDerivAt_integral]
      with x hx hxP hm
    simpa using HasDerivAt.sub (hx hm) (hxP hm a (of_eq_true left_mem_uIcc._simp_1))
  obtain ⟨c, hc⟩ := (hf.sub hP).const_of_ae_hasDerivAt_zero hz
  intro θ hθ
  have h := (hc θ hθ).trans (hc a (by simp)).symm
  simp_all [sub_eq_iff_eq_add, add_comm]

theorem eq_add_intervalIntegral_of_ac_ae_hasDerivAt {f g : ℝ → V} {L : ℝ} (hL : 0 ≤ L)
    (hf : AbsolutelyContinuousOnInterval f 0 L) (hg : IntegrableOn g (Icc 0 L))
    (hd : ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt f (g x) x) :
    ∀ θ ∈ Icc 0 L, f θ = f 0 + ∫ s in (0 : ℝ)..θ, g s := by
  rw [← uIcc_of_le hL] at hg ⊢
  apply eq_add_intervalIntegral_of_ac_ae_deriv hf hg.intervalIntegrable
  have h₀ : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff]
  have h₁ : ∀ᵐ x : ℝ, x ≠ L := by simp [ae_iff]
  rw [uIcc_of_le hL]
  filter_upwards [hd, h₀, h₁] with x; grind

theorem eq_add_integral_of_ae_hasDerivAt {f g : ℝ → V} {L : ℝ} {K : NNReal}
    (hf : LipschitzOnWith K f (Icc 0 L)) (hg : IntegrableOn g (Icc 0 L))
    (hd : ∀ᵐ x, x ∈ Ioo 0 L → HasDerivAt f (g x) x) :
    ∀ θ ∈ Icc 0 L, f θ = f 0 + ∫ s in (0 : ℝ)..θ, g s := fun θ hθ =>
  eq_add_intervalIntegral_of_ac_ae_hasDerivAt (hθ.1.trans hθ.2)
    ((uIcc_of_le (hθ.1.trans hθ.2) ▸ hf).absolutelyContinuousOnInterval) hg hd θ hθ

/-- Actual operator evaluation preserves absolute continuity. Its increment
estimate uses the genuine operator norm inequality, not a scalar norm equality. -/
theorem absolutelyContinuousOnInterval_clm_apply
    {V Z : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {A : ℝ → V →L[ℂ] Z} {f : ℝ → V} {a b : ℝ}
    (hA : AbsolutelyContinuousOnInterval A a b) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => A x (f x)) a b := by
  obtain ⟨C, hC⟩ := hA.exists_bound
  obtain ⟨D, hD⟩ := hf.exists_bound
  unfold AbsolutelyContinuousOnInterval at hA hf ⊢
  have hlim : Tendsto
      (fun E : ℕ × (ℕ → ℝ × ℝ) => ∑ i ∈ Finset.range E.1,
        (C * dist (f (E.2 i).1) (f (E.2 i).2) +
          D * dist (A (E.2 i).1) (A (E.2 i).2)))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) := by
    simpa only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_zero, add_zero] using
      (hf.const_mul C).add (hA.const_mul D)
  apply squeeze_zero' ?_ ?_ hlim
  exact Eventually.of_forall fun E => Finset.sum_nonneg fun x x_1 => dist_nonneg
  rw [eventually_inf_principal]
  filter_upwards with E hE
  simp only [disjWithin] at hE
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hxi := (hE.1 i hi).1
  have hyi := (hE.1 i hi).2
  let x := (E.2 i).1
  let y := (E.2 i).2
  have he : A x (f x) - A y (f y) = A x (f x - f y) + (A x - A y) (f y) := by
    simp
  calc
    _ = ‖A x (f x - f y) + (A x - A y) (f y)‖ := by rw [dist_eq_norm, he]
    _ ≤ ‖A x‖ * ‖f x - f y‖ + ‖A x - A y‖ * ‖f y‖ :=
      (norm_add_le _ _).trans (add_le_add ((A x).le_opNorm _) ((A x - A y).le_opNorm _))
    _ ≤ C * dist (f x) (f y) + D * dist (A x) (A y) := by
      rw [dist_eq_norm, dist_eq_norm]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (hC x hxi) (norm_nonneg _))
        (by rw [mul_comm D]; exact mul_le_mul_of_nonneg_left (hD y hyi) (norm_nonneg _))

end PolyaNeumann
