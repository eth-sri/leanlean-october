module

public import RoughRegime.Lower
public import RoughRegime.GeneralTesting
public import RoughRegime.Model

@[expose] public section

/-! General probability-density ingredients for the one-dimensional lower bound. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace RoughRegime.LowerMeasure

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_sqrt_product {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf₀ : 0 ≤ᵐ[μ] f) (hg₀ : 0 ≤ᵐ[μ] g) :
    Integrable (fun x => Real.sqrt (f x) * Real.sqrt (g x)) μ := by
  apply ((hf.add hg).div_const 2).mono'
  · exact (hf.aemeasurable.sqrt.mul hg.aemeasurable.sqrt).aestronglyMeasurable
  · filter_upwards [hf₀, hg₀] with x hfx hgx
    change 0 ≤ f x at hfx
    change 0 ≤ g x at hgx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    change Real.sqrt (f x) * Real.sqrt (g x) ≤ (f x + g x) / 2
    nlinarith [Real.sq_sqrt hfx, Real.sq_sqrt hgx,
      sq_nonneg (Real.sqrt (f x) - Real.sqrt (g x))]

def densityAffinity (L R : GeneralTesting.DensityLaw μ) : ℝ :=
  ∫ x, Real.sqrt (L.density x) * Real.sqrt (R.density x) ∂μ

theorem densityAffinity_integrable (L R : GeneralTesting.DensityLaw μ) :
    Integrable (fun x => Real.sqrt (L.density x) * Real.sqrt (R.density x)) μ :=
  integrable_sqrt_product L.integrable R.integrable L.nonneg R.nonneg

theorem hellinger_integral_eq (L R : GeneralTesting.DensityLaw μ) :
    GeneralTesting.hellingerSquared L R = 2 - 2 * densityAffinity L R := by
  have hi := densityAffinity_integrable L R
  have he : (fun x => (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2) =ᵐ[μ]
      fun x => L.density x + R.density x -
        2 * (Real.sqrt (L.density x) * Real.sqrt (R.density x)) := by
    filter_upwards [L.nonneg, R.nonneg] with x hx hy
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]
  unfold GeneralTesting.hellingerSquared
  rw [integral_congr_ae he]
  change (∫ x, (L.density + R.density) x -
    (fun x => 2 * (Real.sqrt (L.density x) * Real.sqrt (R.density x))) x ∂μ) = _
  rw [integral_sub (L.integrable.add R.integrable) (hi.const_mul 2)]
  change (∫ x, L.density x + R.density x ∂μ) -
    (∫ x, 2 * (Real.sqrt (L.density x) * Real.sqrt (R.density x)) ∂μ) = _
  rw [integral_add L.integrable R.integrable, integral_const_mul, L.integral_one, R.integral_one]
  unfold densityAffinity
  ring

theorem hellinger_integrable (L R : GeneralTesting.DensityLaw μ) :
    Integrable (fun x => (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2) μ := by
  apply ((L.integrable.add R.integrable).sub ((densityAffinity_integrable L R).const_mul 2)).congr
  filter_upwards [L.nonneg, R.nonneg] with x hx hy
  change 0 ≤ L.density x at hx
  change 0 ≤ R.density x at hy
  change L.density x + R.density x - 2 * (Real.sqrt (L.density x) * Real.sqrt (R.density x)) = _
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

theorem densityAffinity_nonneg (L R : GeneralTesting.DensityLaw μ) :
    0 ≤ densityAffinity L R := integral_nonneg fun _ =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

def iidDensityLaw [SigmaFinite μ] (L : GeneralTesting.DensityLaw μ) (n : ℕ) :
    GeneralTesting.DensityLaw (Measure.pi (fun _ : Fin n => μ)) where
  density xs := ∏ i, L.density (xs i)
  measurable := by
    apply Finset.measurable_prod
    intro i _
    exact L.measurable.comp (measurable_pi_apply i)
  integrable := Integrable.fintype_prod fun _ => L.integrable
  nonneg := by
    have h : ∀ᵐ xs : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
        ∀ i, 0 ≤ L.density (xs i) := by
      filter_upwards [ae_le_pi (fun _ : Fin n => L.nonneg)] with xs hx
      exact hx
    filter_upwards [h] with xs hx
    exact Finset.prod_nonneg fun i _ => hx i
  integral_one := by
    rw [integral_fin_nat_prod_eq_prod]
    simp [L.integral_one]

/-- The density-product construction is exactly the iid product of the actual
probability laws, not merely an integral representation. -/
theorem iidDensityLaw_measure [SigmaFinite μ] (L : GeneralTesting.DensityLaw μ) (n : ℕ) :
    (iidDensityLaw L n).measure = Measure.pi (fun _ : Fin n => L.measure) := by
  apply (Measure.pi_eq (μ := fun _ : Fin n => L.measure) ?_).symm
  intro s hs
  have hS : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hrhs : (∏ i : Fin n, L.measure (s i)) ≠ ∞ := by
    rw [← Measure.pi_pi (fun _ : Fin n => L.measure)]
    exact measure_ne_top _ _
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hrhs).mp
  rw [ENNReal.toReal_prod]
  change (iidDensityLaw L n).measure.real (Set.univ.pi s) = ∏ i, L.measure.real (s i)
  rw [(iidDensityLaw L n).measureReal_eq_setIntegral _ hS]
  simp_rw [L.measureReal_eq_setIntegral _ (hs _)]
  rw [Measure.restrict_pi_pi]
  change (∫ xs : Fin n → Ω, ∏ i, L.density (xs i) ∂Measure.pi (fun i => μ.restrict (s i))) = _
  rw [integral_fin_nat_prod_eq_prod (fun _ : Fin n => L.density)]

theorem densityAffinity_iid [SigmaFinite μ] (L R : GeneralTesting.DensityLaw μ) (n : ℕ) :
    densityAffinity (iidDensityLaw L n) (iidDensityLaw R n) = densityAffinity L R ^ n := by
  have hp : ∀ᵐ xs : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i, 0 ≤ L.density (xs i) := by
    filter_upwards [ae_le_pi (fun _ : Fin n => L.nonneg)] with xs hx
    exact hx
  have hq : ∀ᵐ xs : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i, 0 ≤ R.density (xs i) := by
    filter_upwards [ae_le_pi (fun _ : Fin n => R.nonneg)] with xs hx
    exact hx
  have he : (fun xs : Fin n → Ω =>
      Real.sqrt ((iidDensityLaw L n).density xs) * Real.sqrt ((iidDensityLaw R n).density xs)) =ᵐ[
        Measure.pi (fun _ : Fin n => μ)]
      fun xs => ∏ i, Real.sqrt (L.density (xs i)) * Real.sqrt (R.density (xs i)) := by
    filter_upwards [hp, hq] with xs hpx hqx
    change Real.sqrt (∏ i, L.density (xs i)) * Real.sqrt (∏ i, R.density (xs i)) = _
    rw [Lower.sqrt_finite_product _ hpx, Lower.sqrt_finite_product _ hqx,
      Finset.prod_mul_distrib]
  unfold densityAffinity
  rw [integral_congr_ae he]
  rw [integral_fin_nat_prod_eq_prod (fun _ : Fin n =>
    fun x : Ω => Real.sqrt (L.density x) * Real.sqrt (R.density x))]
  simp

theorem hellinger_iid_le [SigmaFinite μ] (L R : GeneralTesting.DensityLaw μ) (n : ℕ) :
    GeneralTesting.hellingerSquared (iidDensityLaw L n) (iidDensityLaw R n) ≤
      n * GeneralTesting.hellingerSquared L R := by
  rw [hellinger_integral_eq, densityAffinity_iid, hellinger_integral_eq]
  have h := one_add_mul_sub_le_pow (by linarith [densityAffinity_nonneg L R] :
    -1 ≤ densityAffinity L R) n
  nlinarith

/-- Quadratic Hellinger bound for an affine density path on an arbitrary
measurable observation space, with all density inequalities almost everywhere. -/
theorem affine_hellinger_bound [IsProbabilityMeasure μ]
    (L R : GeneralTesting.DensityLaw μ) (f₀ f₁ : Ω → ℝ)
    (t s cf Cf : ℝ) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (hL : L.density =ᵐ[μ] fun x => f₀ x + t * f₁ x)
    (hR : R.density =ᵐ[μ] fun x => f₀ x + s * f₁ x)
    (ht : ∀ᵐ x ∂μ, cf ≤ f₀ x + t * f₁ x)
    (hs : ∀ᵐ x ∂μ, cf ≤ f₀ x + s * f₁ x)
    (hf₁ : ∀ᵐ x ∂μ, |f₁ x| ≤ Cf) :
    GeneralTesting.hellingerSquared L R ≤ Cf ^ 2 * (t - s) ^ 2 / (4 * cf) := by
  have hx : ∀ᵐ x ∂μ, (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2 ≤
      Cf ^ 2 * (t - s) ^ 2 / (4 * cf) := by
    filter_upwards [hL, hR, ht, hs, hf₁] with x hxL hxR hxt hxs hxf
    rw [hxL, hxR]
    have h := Lower.square_root_difference_bound hcf hxt hxs
    have hsq : f₁ x ^ 2 ≤ Cf ^ 2 := by
      nlinarith [sq_abs (f₁ x), abs_nonneg (f₁ x), hxf]
    have hid : (f₀ x + t * f₁ x - (f₀ x + s * f₁ x)) ^ 2 =
        f₁ x ^ 2 * (t - s) ^ 2 := by ring
    rw [hid] at h
    exact le_trans h (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)) (by positivity))
  have hi := integral_mono_ae (hellinger_integrable L R)
    (integrable_const (Cf ^ 2 * (t - s) ^ 2 / (4 * cf))) hx
  simpa [GeneralTesting.hellingerSquared] using hi

def densityLawWithSeed {S : Type*} [MeasurableSpace S] (ν : Measure S)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (L : GeneralTesting.DensityLaw μ) :
    GeneralTesting.DensityLaw (μ.prod ν) where
  density x := L.density x.1
  measurable := L.measurable.comp measurable_fst
  integrable := by
    simpa using L.integrable.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : S => (1 : ℝ)) ν)
  nonneg := by
    filter_upwards [quasiMeasurePreserving_fst.tendsto_ae.eventually L.nonneg] with x hx
    exact hx
  integral_one := by
    rw [integral_fun_fst]
    simp [L.integral_one]

theorem densityLawWithSeed_measure {S : Type*} [MeasurableSpace S] (ν : Measure S)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (L : GeneralTesting.DensityLaw μ) :
    (densityLawWithSeed ν L).measure = L.measure.prod ν := by
  unfold densityLawWithSeed GeneralTesting.DensityLaw.measure
  exact (prod_withDensity_left (ENNReal.measurable_ofReal.comp L.measurable)).symm

theorem hellinger_with_seed {S : Type*} [MeasurableSpace S] (ν : Measure S)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (L R : GeneralTesting.DensityLaw μ) :
    GeneralTesting.hellingerSquared (densityLawWithSeed ν L) (densityLawWithSeed ν R) =
      GeneralTesting.hellingerSquared L R := by
  change (∫ x : Ω × S, (Real.sqrt (L.density x.1) - Real.sqrt (R.density x.1)) ^ 2 ∂μ.prod ν) =
    ∫ x, (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2 ∂μ
  rw [integral_fun_fst (fun x => (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2)]
  simp

end RoughRegime.LowerMeasure
