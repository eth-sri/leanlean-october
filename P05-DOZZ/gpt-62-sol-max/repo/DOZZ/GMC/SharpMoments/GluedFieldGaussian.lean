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
open scoped ENNReal NNReal Classical

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

/-- The second moment of a centered real Gaussian is its variance parameter. -/
theorem gluedField_gaussianReal_second_moment (C : ℝ≥0) :
    ∫ z, z * z ∂(gaussianReal 0 C) = C := by
  have h := variance_of_integral_eq_zero (X := fun z : ℝ => z) (μ := gaussianReal 0 C)
    measurable_id.aemeasurable (by simp)
  rw [variance_fun_id_gaussianReal] at h
  rw [h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)

section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] {P : Measure Ω} {Φ : Ω → S → ℝ}
  (hΦ : IsCenteredGaussianField P Φ)
include Ω hΦ

/-- Every coordinate of a centered Gaussian field is square-integrable. -/
theorem gluedField_memLp (x : S) :
    MemLp (fun ω => Φ ω x) 2 P := by
  have h := ((hΦ.2 1 (fun _ => x)).2.2 (fun _ => 1)).1
  simpa using h

/-- Every coordinate of a centered Gaussian field has mean zero. -/
theorem gluedField_integral_eq_zero (x : S) :
    ∫ ω, Φ ω x ∂P = 0 := by
  obtain ⟨_, _, hmean, _⟩ :=
    coordinate_mean_variance P (fun ω (_ : Fin 1) => Φ ω x) (hΦ.2 1 (fun _ => x)) 0
  exact hmean

/-- A coordinate of the field restricted to the set `B` is square-integrable. -/
theorem gluedField_memLp_indicator (B : Set S) (x : S) :
    MemLp (fun ω => B.indicator (Φ ω) x) 2 P := by
  by_cases hx : x ∈ B
  · simpa only [Set.indicator_of_mem hx] using gluedField_memLp hΦ x
  simp_all

/-- A coordinate of the field restricted to the set `B` has mean zero. -/
theorem gluedField_integral_indicator (B : Set S) (x : S) :
    ∫ ω, B.indicator (Φ ω) x ∂P = 0 := by
  by_cases hx : x ∈ B
  · simpa only [Set.indicator_of_mem hx] using gluedField_integral_eq_zero hΦ x
  · simp only [Set.indicator_of_notMem hx, integral_zero]

end

/-- A set indicator is multiplication by the indicator of the constant `1`. -/
theorem gluedField_indicator_eq_mul {S : Type*} (B : Set S) (f : S → ℝ) (x : S) :
    B.indicator f x = B.indicator (fun _ => (1 : ℝ)) x * f x := by
  by_cases hx : x ∈ B <;> simp [hx]

/-- Use the first field copy on `A` and the second independent copy on its complement. -/
noncomputable def independent_piece_field {Ω S : Type*} (Φ : Ω → S → ℝ) (A : Set S)
    (ω : Ω × Ω) (x : S) : ℝ := A.indicator (Φ ω.1) x + Aᶜ.indicator (Φ ω.2) x

section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ)
  (hΦ : IsCenteredGaussianField P Φ) (A : Set S)
include Ω S hΦ

/-- The independent-copy field is a jointly measurable centered Gaussian field. -/
theorem independent_piece_field_gaussian (hA : MeasurableSet A) :
    IsCenteredGaussianField (P.prod P) (independent_piece_field Φ A) := by
  constructor
  exact Measurable.add
    (Measurable.indicator
      (Measurable.comp hΦ.left (Measurable.prodMk (Measurable.comp measurable_fst measurable_fst) measurable_snd))
      (measurable_snd hA))
    (Measurable.indicator
      (Measurable.comp hΦ.left (Measurable.prodMk (Measurable.comp measurable_snd measurable_fst) measurable_snd))
      (measurable_snd (MeasurableSet.compl hA)))
  · intro n x
    have h1 := isCenteredJointlyGaussian_coord_mul P _ (hΦ.2 n x)
      (fun i => A.indicator (fun _ => (1 : ℝ)) (x i))
    have h2 := isCenteredJointlyGaussian_coord_mul P _ (hΦ.2 n x)
      (fun i => Aᶜ.indicator (fun _ => (1 : ℝ)) (x i))
    have h := isCenteredJointlyGaussian_prod_add P P _ _ h1 h2
    have he : (fun ω i => independent_piece_field Φ A ω (x i)) =
        fun ω i => A.indicator (fun _ => (1 : ℝ)) (x i) * Φ ω.1 (x i) +
          Aᶜ.indicator (fun _ => (1 : ℝ)) (x i) * Φ ω.2 (x i) := by
      funext ω i
      unfold independent_piece_field
      rw [gluedField_indicator_eq_mul A, gluedField_indicator_eq_mul Aᶜ]
    rw [he]
    exact h

/-- Within either region the covariance is unchanged; across the regions it is zero. -/
theorem independent_piece_field_covariance (x y : S) :
    gaussianCovariance (P.prod P) (fun ω => independent_piece_field Φ A ω x)
      (fun ω => independent_piece_field Φ A ω y) =
      if (x ∈ A ↔ y ∈ A) then gaussianCovariance P (fun ω => Φ ω x) (fun ω => Φ ω y)
        else 0 := by
  classical
  let _ : IsProbabilityMeasure P := (hΦ.2 0 (fun i => Fin.elim0 i)).1
  have h := gaussianCovariance_prod_add P P
    (fun ω => A.indicator (Φ ω) x) (fun ω => A.indicator (Φ ω) y)
    (fun ω => Aᶜ.indicator (Φ ω) x) (fun ω => Aᶜ.indicator (Φ ω) y)
    (gluedField_memLp_indicator hΦ A x) (gluedField_memLp_indicator hΦ A y)
    (gluedField_memLp_indicator hΦ Aᶜ x) (gluedField_memLp_indicator hΦ Aᶜ y)
    (gluedField_integral_indicator hΦ A x) (gluedField_integral_indicator hΦ A y)
  change gaussianCovariance (P.prod P)
    (fun ω => A.indicator (Φ ω.1) x + Aᶜ.indicator (Φ ω.2) x)
    (fun ω => A.indicator (Φ ω.1) y + Aᶜ.indicator (Φ ω.2) y) = _
  rw [h]
  unfold gaussianCovariance
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;>
    simp [*]

/-- Splitting copies across a partition leaves every diagonal second moment unchanged. -/
theorem independent_piece_field_variance (x : S) :
    (∫ w, independent_piece_field Φ A w x ^ 2 ∂P.prod P) = ∫ ω, Φ ω x ^ 2 ∂P := by
  simpa only [iff_self, ite_true, gaussianCovariance, pow_two] using
    independent_piece_field_covariance P Φ hΦ A x x

end

section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ)
  (hΦ : IsCenteredGaussianField P Φ) (A : Set S) (hA : MeasurableSet A) (C : ℝ≥0)
include Ω hΦ hA

/-- Adding the common scalar adds `C` to the covariance of the partitioned field. -/
theorem gluedField_covariance (x y : S) :
    (∫ q, gluedField Φ A q x * gluedField Φ A q y ∂P.prod (P.prod (gaussianReal 0 C))) =
      (if (x ∈ A ↔ y ∈ A) then (∫ ω, Φ ω x * Φ ω y ∂P) else 0) + C := by
  let _ := (hΦ.2 0 Fin.elim0).1
  let Ψ := independent_piece_field Φ A
  have hΨ := independent_piece_field_gaussian P Φ hΦ A hA
  rw [← (measurePreserving_prodAssoc P P (gaussianReal 0 C)).integral_comp'
    (fun q => gluedField Φ A q x * gluedField Φ A q y)]
  have h := gaussianCovariance_prod_add (P.prod P) (gaussianReal 0 C)
    (fun w => Ψ w x) (fun w => Ψ w y) id id
    (gluedField_memLp hΨ x) (gluedField_memLp hΨ y)
    (memLp_id_gaussianReal 2) (memLp_id_gaussianReal 2)
    (gluedField_integral_eq_zero hΨ x) (gluedField_integral_eq_zero hΨ y)
  rw [independent_piece_field_covariance P Φ hΦ A, gaussianCovariance] at h
  have he (w : (Ω × Ω) × ℝ) (z : S) :
      gluedField Φ A (MeasurableEquiv.prodAssoc w) z = Ψ w.1 z + w.2 := rfl
  simpa only [he, gaussianCovariance, id_eq, gluedField_gaussianReal_second_moment] using h

/-- The pointwise variance of the glued field is the original variance plus the scalar variance. -/
theorem gluedField_variance (x : S) :
    (∫ q, gluedField Φ A q x ^ 2 ∂P.prod (P.prod (gaussianReal 0 C))) =
      (∫ ω, Φ ω x ^ 2 ∂P) + C := by
  simpa only [pow_two, iff_self, ite_true] using gluedField_covariance P Φ hΦ A hA C x x

/-- The glued field is the partitioned field plus one independent centered Gaussian. -/
theorem gluedField_isCenteredGaussianField :
    IsCenteredGaussianField (P.prod (P.prod (gaussianReal 0 C))) (gluedField Φ A) := by
  let _ := (hΦ.2 0 Fin.elim0).1
  let Ψ := independent_piece_field Φ A
  have hΨ := independent_piece_field_gaussian P Φ hΦ A hA
  refine ⟨(hΨ.1.comp (f := fun q : (Ω × Ω × ℝ) × S => ((q.1.1, q.1.2.1), q.2))
    (by fun_prop)).add (by fun_prop), fun n x => ?_⟩
  have hs : IsCenteredJointlyGaussian (gaussianReal 0 C) (fun z (_ : Fin n) => z) := by
    simpa using gluedField_scalar_mul (ι := Fin n) C (fun _ => 1)
  exact isCenteredJointlyGaussian_comp_measurePreserving
    ((measurePreserving_prodAssoc P P (gaussianReal 0 C)).symm MeasurableEquiv.prodAssoc)
    (isCenteredJointlyGaussian_prod_add (P.prod P) (gaussianReal 0 C) _ _ (hΨ.2 n x) hs)

end

/-- The exponential of a sum splits off one factor from a weighted Wick density. -/
theorem gluedField_wick_factor (t : ℝ≥0∞) (a b : ℝ) :
    t * ENNReal.ofReal (Real.exp (b + a)) =
      ENNReal.ofReal (Real.exp a) * (t * ENNReal.ofReal (Real.exp b)) := by
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  ring

section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ)
  (hΦ : IsCenteredGaussianField P Φ) (A : Set S)
include hΦ

/-- Where the glued field equals a copy of `Φ` plus the scalar, its Wick density is the scalar
exponential times the Wick density of that copy. -/
theorem gluedField_wick_integrand (hA : MeasurableSet A) (C : ℝ≥0) (h : S → ℝ≥0) (γ : ℝ) (q : Ω × Ω × ℝ) (ω : Ω) (x : S)
    (hg : gluedField Φ A q x = Φ ω x + q.2.2) :
    (h x : ℝ≥0∞) * ENNReal.ofReal (Real.exp (γ * gluedField Φ A q x - γ ^ 2 / 2 *
        ∫ q', gluedField Φ A q' x ^ 2 ∂(P.prod (P.prod (gaussianReal 0 C))))) =
      ENNReal.ofReal (Real.exp (γ * q.2.2 - γ ^ 2 / 2 * C)) *
        ((h x : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P))) := by
  have hexp : γ * (Φ ω x + q.2.2) - γ ^ 2 / 2 * ((∫ ω', Φ ω' x ^ 2 ∂P) + C) =
      (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P) + (γ * q.2.2 - γ ^ 2 / 2 * C) := by
    ring
  rw [hg, gluedField_variance P Φ hΦ A hA C x, hexp, gluedField_wick_factor]

/-- The Wick mass of the glued field is the scalar exponential times the sum of the two
independent piece masses. -/
theorem gluedField_fieldChaosMass (hA : MeasurableSet A) (C : ℝ≥0) (ν : Measure S) (h : S → ℝ≥0) (γ : ℝ)
    (q : Ω × Ω × ℝ) :
    fieldChaosMass (P.prod (P.prod (gaussianReal 0 C))) (gluedField Φ A) ν h γ q =
      ENNReal.ofReal (Real.exp (γ * q.2.2 - γ ^ 2 / 2 * C)) *
        (fieldChaosMass P Φ (ν.restrict A) h γ q.1 +
          fieldChaosMass P Φ (ν.restrict Aᶜ) h γ q.2.1) := by
  have hc : ENNReal.ofReal (Real.exp (γ * q.2.2 - γ ^ 2 / 2 * C)) ≠ ∞ := ENNReal.ofReal_ne_top
  unfold fieldChaosMass
  refine (lintegral_add_compl _ hA).symm.trans ?_
  rw [mul_add, ← lintegral_const_mul' _ _ hc, ← lintegral_const_mul' _ _ hc]
  congr 1
  · refine setLIntegral_congr_fun hA fun x hx => ?_
    refine gluedField_wick_integrand P Φ hΦ A hA C h γ q q.1 x ?_
    rw [gluedField, Set.indicator_of_mem hx,
      Set.indicator_of_notMem (show x ∉ Aᶜ from fun hxc => hxc hx), add_zero]
  · refine setLIntegral_congr_fun hA.compl fun x hx => ?_
    refine gluedField_wick_integrand P Φ hΦ A hA C h γ q q.2.1 x ?_
    rw [gluedField, Set.indicator_of_notMem (show x ∉ A from hx), Set.indicator_of_mem hx,
      zero_add]

end

end DOZZ.Proofs
