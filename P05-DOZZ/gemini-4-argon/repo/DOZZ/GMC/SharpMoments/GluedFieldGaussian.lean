/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.GluedField
public import DOZZ.GMC.FiniteChaosMean

/-! # The glued comparison field

The comparison field of the two-branch small-deviation step is built from two independent copies of
a centered Gaussian field `Φ`, one used on a measurable set `A` and one on its complement, together
with an independent centered Gaussian scalar of variance `C`. It is again a centered Gaussian field,
its covariance is the original covariance inside each piece plus `C` and exactly `C` across the two
pieces, and its Wick mass is the scalar exponential times the sum of the two independent piece
masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Two independent copies of `Φ`, one on `A` and one off `A`, plus an independent common scalar. -/
noncomputable def gluedField {Ω S : Type*} (Φ : Ω → S → ℝ) (A : Set S)
    (q : Ω × Ω × ℝ) (x : S) : ℝ :=
  A.indicator (Φ q.1) x + Aᶜ.indicator (Φ q.2.1) x + q.2.2

/-- A centered Gaussian scalar of arbitrary variance times fixed coefficients is a centered jointly
Gaussian family. -/
theorem gluedField_scalar_mul {ι : Type*} [Fintype ι] (C : ℝ≥0) (c : ι → ℝ) :
    IsCenteredJointlyGaussian (gaussianReal 0 C) (fun z i => c i * z) := by
  refine ⟨inferInstance, fun i => (measurable_id.const_mul (c i)).aemeasurable, fun a => ?_⟩
  have heq : (fun z : ℝ => ∑ i, a i * (c i * z)) = fun z => (∑ i, a i * c i) * z := by
    funext z
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [heq]
  refine ⟨(memLp_id_gaussianReal 2).const_mul _,
    ⟨.mk ((∑ i, a i * c i) ^ 2) (sq_nonneg _) * C, ?_⟩⟩
  have h := gaussianReal_map_const_mul (μ := 0) (v := C) (∑ i, a i * c i)
  rw [mul_zero] at h
  exact h




/-- A coordinate of the field restricted to the set `B` is square-integrable. -/
theorem gluedField_memLp_indicator {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} {Φ} (hΦ : IsCenteredGaussianField P Φ) (B : Set S) x :
    MemLp (fun ω => B.indicator (Φ ω) x) 2 P := by
  by_cases hx : x ∈ B
  · simpa only [Set.indicator_of_mem hx] using (by simpa using (((hΦ.2 1 (fun _ => x)).2.2 (fun _ => 1)).1))
  · simpa only [Set.indicator_of_notMem hx] using (MemLp.zero' : MemLp (fun _ : Ω => (0 : ℝ)) 2 P)

/-- A coordinate of the field restricted to the set `B` has mean zero. -/
theorem gluedField_integral_indicator {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} {Φ} (hΦ : IsCenteredGaussianField P Φ) (B : Set S) x :
    ∫ ω, B.indicator (Φ ω) x ∂P = 0 := by
  by_cases hx : x ∈ B
  · simpa only [Set.indicator_of_mem hx] using (by obtain ⟨_, _, hmean, _⟩ := coordinate_mean_variance P (fun ω (_ : Fin 1) => Φ ω x) (hΦ.2 1 (fun _ => x)) 0; exact hmean)
  · simp only [Set.indicator_of_notMem hx, integral_zero]

/-- A set indicator is multiplication by the indicator of the constant `1`. -/
theorem gluedField_indicator_eq_mul {S : Type*} (B : Set S) (f : S → ℝ) x :
    B.indicator f x = B.indicator (fun _ => (1 : ℝ)) x * f x := by
  by_cases hx : x ∈ B <;> simp [hx]

/-- Reassociation of the three summands of the glued field. -/
theorem gluedField_eq_add {Ω S : Type*} (Φ : Ω → S → ℝ) (A : Set S) (q : Ω × Ω × ℝ) x :
    gluedField Φ A q x = A.indicator (Φ q.1) x + (Aᶜ.indicator (Φ q.2.1) x + q.2.2) :=
  add_assoc _ _ _

/-- The mixed second moment of the glued field splits into the two piece moments and the scalar
variance. -/
theorem gluedField_covariance_eq {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) Φ (hΦ : IsCenteredGaussianField P Φ)
    (A : Set S) (C : ℝ≥0) x y :
    ∫ q, gluedField Φ A q x * gluedField Φ A q y ∂(P.prod (P.prod (gaussianReal 0 C))) =
      (∫ ω, A.indicator (Φ ω) x * A.indicator (Φ ω) y ∂P) +
        ((∫ ω, Aᶜ.indicator (Φ ω) x * Aᶜ.indicator (Φ ω) y ∂P) + C) := by
  have gluedField_gaussianReal_second_moment : ∫ z, z * z ∂(gaussianReal 0 C) = C := by
    have h := variance_of_integral_eq_zero (X := fun z => z) (μ := gaussianReal 0 C)
      measurable_id.aemeasurable (by simp)
    rw [variance_fun_id_gaussianReal] at h
    rw [h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  have : IsProbabilityMeasure P := (hΦ.2 0 (fun i => Fin.elim0 i)).1
  have hmemR : ∀ t : S, MemLp (fun r : Ω × ℝ => Aᶜ.indicator (Φ r.1) t + r.2) 2
      (P.prod (gaussianReal 0 C)) := fun t =>
    ((gluedField_memLp_indicator hΦ Aᶜ t).comp_fst _).add ((memLp_id_gaussianReal 2).comp_snd P)
  simp only [gluedField_eq_add]
  refine (gaussianCovariance_prod_add P (P.prod (gaussianReal 0 C)) (fun ω => A.indicator (Φ ω) x) (fun ω => A.indicator (Φ ω) y) (fun r => Aᶜ.indicator (Φ r.1) x + r.2) (fun r => Aᶜ.indicator (Φ r.1) y + r.2) (gluedField_memLp_indicator hΦ A x) (gluedField_memLp_indicator hΦ A y) (hmemR x) (hmemR y) (gluedField_integral_indicator hΦ A x) (gluedField_integral_indicator hΦ A y)).trans ?_
  rw [(gaussianCovariance_prod_add P (gaussianReal 0 C) (fun ω => Aᶜ.indicator (Φ ω) x) (fun ω => Aᶜ.indicator (Φ ω) y) (fun z => z) (fun z => z) (gluedField_memLp_indicator hΦ Aᶜ x) (gluedField_memLp_indicator hΦ Aᶜ y) (memLp_id_gaussianReal 2) (memLp_id_gaussianReal 2) (gluedField_integral_indicator hΦ Aᶜ x) (gluedField_integral_indicator hΦ Aᶜ y))]
  unfold gaussianCovariance
  rw [(gluedField_gaussianReal_second_moment)]

/-- Inside `A`, the glued covariance is the original covariance plus the scalar variance. -/
theorem gluedField_covariance_of_mem_of_mem {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    A (C : ℝ≥0) {x y} (hx : x ∈ A) (hy : y ∈ A) :
    ∫ q, gluedField Φ A q x * gluedField Φ A q y ∂(P.prod (P.prod (gaussianReal 0 C))) =
      (∫ ω, Φ ω x * Φ ω y ∂P) + C := by
  have hx' : x ∉ Aᶜ := fun h => h hx
  rw [gluedField_covariance_eq P Φ hΦ A C x y]
  simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_notMem hx',
    zero_mul, integral_zero, zero_add]

/-- Outside `A`, the glued covariance is the original covariance plus the scalar variance. -/
theorem gluedField_covariance_of_notMem_of_notMem {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    A (C : ℝ≥0) {x y} (hx : x ∉ A) (hy : y ∉ A) :
    ∫ q, gluedField Φ A q x * gluedField Φ A q y ∂(P.prod (P.prod (gaussianReal 0 C))) =
      (∫ ω, Φ ω x * Φ ω y ∂P) + C := by
  have hx' : x ∈ Aᶜ := hx
  have hy' : y ∈ Aᶜ := hy
  rw [gluedField_covariance_eq P Φ hΦ A C x y]
  simp only [Set.indicator_of_mem hx', Set.indicator_of_mem hy', Set.indicator_of_notMem hx,
    zero_mul, integral_zero, zero_add]

/-- Across the two pieces, the glued covariance is exactly the scalar variance. -/
theorem gluedField_covariance_of_mem_of_notMem {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    A (C : ℝ≥0) {x y} (hx : x ∈ A) (hy : y ∉ A) :
    ∫ q, gluedField Φ A q x * gluedField Φ A q y ∂(P.prod (P.prod (gaussianReal 0 C))) = C := by
  have hx' : x ∉ Aᶜ := fun h => h hx
  rw [gluedField_covariance_eq P Φ hΦ A C x y]
  simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx', mul_zero, zero_mul,
    integral_zero, zero_add]


/-- The glued field is jointly measurable in the sample point and the spatial variable. -/
theorem gluedField_measurable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} {Φ} (hΦ : IsCenteredGaussianField P Φ)
    {A} (hA : MeasurableSet A) :
    Measurable (fun p : (Ω × Ω × ℝ) × S => gluedField Φ A p.1 p.2) := by
  exact (((hΦ.1.comp (by fun_prop : Measurable fun p : (Ω × Ω × ℝ) × S => (p.1.1, p.2))).indicator (measurable_snd hA)).add ((hΦ.1.comp (by fun_prop : Measurable fun p : (Ω × Ω × ℝ) × S => (p.1.2.1, p.2))).indicator (measurable_snd hA.compl))).add (by fun_prop)

/-- The glued field is a centered Gaussian field on the product of two independent copies of the
sample space and an independent Gaussian scalar. -/
theorem gluedField_isCenteredGaussianField {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : IsCenteredGaussianField P Φ)
    A (hA : MeasurableSet A) (C : ℝ≥0) :
    IsCenteredGaussianField (P.prod (P.prod (gaussianReal 0 C))) (gluedField Φ A) := by
  refine ⟨gluedField_measurable hΦ hA, fun n x => ?_⟩
  rw [(show (fun (q : Ω × Ω × ℝ) (i : Fin n) => gluedField Φ A q (x i)) = fun q i => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ q.1 (x i) + (Aᶜ.indicator (fun _ => (1 : ℝ)) (x i) * Φ q.2.1 (x i) + 1 * q.2.2) by funext q i; rw [gluedField_eq_add, gluedField_indicator_eq_mul A, gluedField_indicator_eq_mul Aᶜ, one_mul])]
  exact (isCenteredJointlyGaussian_prod_add P (P.prod (gaussianReal 0 C)) _ _ (isCenteredJointlyGaussian_coord_mul P _ (hΦ.2 n x) (fun i => A.indicator (fun _ => (1 : ℝ)) (x i))) (isCenteredJointlyGaussian_prod_add P (gaussianReal 0 C) _ _ (isCenteredJointlyGaussian_coord_mul P _ (hΦ.2 n x) (fun i => Aᶜ.indicator (fun _ => (1 : ℝ)) (x i))) (gluedField_scalar_mul (ι := Fin n) C (fun _ => 1))))



/-- The Wick mass of the glued field is the scalar exponential times the sum of the two
independent piece masses. -/
theorem gluedField_fieldChaosMass {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) Φ (hΦ : IsCenteredGaussianField P Φ)
    A (hA : MeasurableSet A) (C : ℝ≥0) (ν : Measure S) (h : S → ℝ≥0) γ
    (q : Ω × Ω × ℝ) :
    fieldChaosMass (P.prod (P.prod (gaussianReal 0 C))) (gluedField Φ A) ν h γ q =
      ENNReal.ofReal (Real.exp (γ * q.2.2 - γ ^ 2 / 2 * C)) *
        (fieldChaosMass P Φ (ν.restrict A) h γ q.1 +
          fieldChaosMass P Φ (ν.restrict Aᶜ) h γ q.2.1) := by
  have gluedField_wick_integrand (ω : Ω) (x : S) (hg : gluedField Φ A q x = Φ ω x + q.2.2) : (h x : ℝ≥0∞) * ENNReal.ofReal (Real.exp (γ * gluedField Φ A q x - γ ^ 2 / 2 * ∫ q', gluedField Φ A q' x ^ 2 ∂(P.prod (P.prod (gaussianReal 0 C))))) = ENNReal.ofReal (Real.exp (γ * q.2.2 - γ ^ 2 / 2 * C)) * ((h x : ℝ≥0∞) * ENNReal.ofReal (Real.exp (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P))) := by
    have gluedField_wick_factor (t : ℝ≥0∞) a b : t * ENNReal.ofReal (Real.exp (b + a)) = ENNReal.ofReal (Real.exp a) * (t * ENNReal.ofReal (Real.exp b)) := by
      rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ring
    have gluedField_variance : ∫ q, gluedField Φ A q x ^ 2 ∂(P.prod (P.prod (gaussianReal 0 C))) = (∫ ω, Φ ω x ^ 2 ∂P) + C := by
      by_cases hx : x ∈ A
      · simpa only [pow_two] using gluedField_covariance_of_mem_of_mem P Φ hΦ A C hx hx
      · simpa only [pow_two] using gluedField_covariance_of_notMem_of_notMem P Φ hΦ A C hx hx
    rw [hg, gluedField_variance, (show γ * (Φ ω x + q.2.2) - γ ^ 2 / 2 * ((∫ ω', Φ ω' x ^ 2 ∂P) + C) = (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P) + (γ * q.2.2 - γ ^ 2 / 2 * C) by ring), gluedField_wick_factor]
  have hc : ENNReal.ofReal (Real.exp (γ * q.2.2 - γ ^ 2 / 2 * C)) ≠ ∞ := ENNReal.ofReal_ne_top
  unfold fieldChaosMass
  refine (lintegral_add_compl _ hA).symm.trans ?_
  rw [mul_add, ← lintegral_const_mul' _ _ hc, ← lintegral_const_mul' _ _ hc]
  congr 1
  · refine setLIntegral_congr_fun hA fun x hx => ?_
    refine gluedField_wick_integrand q.1 x ?_
    rw [gluedField, Set.indicator_of_mem hx,
      Set.indicator_of_notMem (show x ∉ Aᶜ from fun hxc => hxc hx), add_zero]
  · refine setLIntegral_congr_fun hA.compl fun x hx => ?_
    refine gluedField_wick_integrand q.2.1 x ?_
    rw [gluedField, Set.indicator_of_notMem (show x ∉ A from hx), Set.indicator_of_mem hx,
      zero_add]

end DOZZ.Proofs
