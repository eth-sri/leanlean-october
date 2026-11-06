module
public import Mathlib
public import RoughRegime.Model
public import NearlyMinimax.Clipping
public import NearlyMinimax.ParametricConstants
@[expose] public section
noncomputable section
section
section
namespace RoughRegime.Applications
open Filter MeasureTheory
open scoped BigOperators ENNReal Topology
lemma eLpNorm_two_eq_squaredIntegral  [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) :
    eLpNorm f 2 μ = (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  congr 2
  funext x
  rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
lemma square_tail_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (t : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal (t ^ 2) * μ {x | t ≤ |f x|} ≤
      ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
  rw [← lintegral_indicator_const (measurableSet_le measurable_const hf.abs)]
  apply lintegral_mono
  intro x
  by_cases hx : t ≤ |f x|
  · rw [Set.indicator_of_mem (show x ∈ {x | t ≤ |f x|} from hx)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_abs (f x), sq_nonneg (|f x| - t)]
  · rw [Set.indicator_of_notMem (show x ∉ {x | t ≤ |f x|} from hx)]
    exact bot_le
end RoughRegime.Applications
namespace RoughRegime.GeneralTesting
open MeasureTheory Set Filter
open scoped ENNReal
structure DensityLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) where
  density : Ω → ℝ
  measurable : Measurable density
  integrable : Integrable density μ
  nonneg : 0 ≤ᵐ[μ] density
  integral_one : (∫ x, density x ∂μ) = 1
namespace DensityLaw
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
def measure (L : DensityLaw μ) : Measure Ω :=
  μ.withDensity (fun x => ENNReal.ofReal (L.density x))
instance isProbabilityMeasure (L : DensityLaw μ) : IsProbabilityMeasure L.measure where
  measure_univ := by
    rw [measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal L.integrable L.nonneg, L.integral_one]
    exact ENNReal.ofReal_one
theorem measureReal_eq_setIntegral (L : DensityLaw μ) (A ) (hA : MeasurableSet A) :
    L.measure.real A = ∫ x in A, L.density x ∂μ := by
  rw [measureReal_def, measure, withDensity_apply _ hA]
  exact (integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae L.nonneg)
    L.integrable.integrableOn.aestronglyMeasurable).symm
theorem measureReal_eq_integral_indicator (L : DensityLaw μ) (A : Set Ω)
    (hA : MeasurableSet A) :
    L.measure.real A = ∫ x, A.indicator L.density x ∂μ := by
  rw [integral_indicator hA]
  exact measureReal_eq_setIntegral L A hA
end DensityLaw
def hellingerSquared {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (L R : DensityLaw μ) : ℝ :=
  ∫ x, (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2 ∂μ
theorem sqrt_difference_sq_le_add  (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a + b := by
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
theorem square_root_testing_lower  (ha : 0 ≤ a) (hb : 0 ≤ b) :
    3 * (a + b) / 8 - (Real.sqrt a - Real.sqrt b) ^ 2 ≤ min a b := by
  apply le_min
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      sq_nonneg (8 * Real.sqrt a - 5 * Real.sqrt b), sq_nonneg (Real.sqrt a)]
  · nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      sq_nonneg (5 * Real.sqrt a - 8 * Real.sqrt b), sq_nonneg (Real.sqrt b)]
theorem two_point_rmse_lower  [MeasurableSpace Ω] {μ : Measure Ω}
    (L R : DensityLaw μ) (g : Ω → ℝ) (hg : Measurable g) (a b : ℝ)
    (hH : hellingerSquared L R ≤ 1 / 4) :
    ENNReal.ofReal (|b - a| / 4) ≤ eLpNorm (fun x => g x - a) 2 L.measure ∨
      ENNReal.ofReal (|b - a| / 4) ≤ eLpNorm (fun x => g x - b) 2 R.measure := by
  have h_two_point_absolute_large_error : (1 / 4 : ℝ) ≤ L.measure.real {x | |b - a| / 2 ≤ |g x - a|} ∨
      (1 / 4 : ℝ) ≤ R.measure.real {x | |b - a| / 2 ≤ |g x - b|} := by
    let A : Set Ω := {x | |g x - a| < |b - a| / 2}
    have he : Aᶜ = {x | |b - a| / 2 ≤ |g x - a|} := by
      ext x
      simp only [A, mem_compl_iff, mem_ofPred_eq, not_lt]
    have hsubset : A ⊆ {x | |b - a| / 2 ≤ |g x - b|} := by
      intro x hx
      have : |g x - a| < |b - a| / 2 := hx
      have : |b - a| ≤ |g x - a| + |g x - b| := by
        simpa [abs_sub_comm, add_comm] using abs_sub_le b (g x) a
      change |b - a| / 2 ≤ |g x - b|
      linarith
    have h_test_loss_ge_half : 1 / 2 ≤ L.measure.real Aᶜ + R.measure.real A := by
      have h_test_loss_lower (hA : MeasurableSet A) : 3 / 4 - hellingerSquared L R ≤ L.measure.real Aᶜ + R.measure.real A := by
        have h_hellinger_integrable : Integrable (fun x => (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2) μ := by
          refine (L.integrable.add R.integrable).mono'
            ((L.measurable.sqrt.sub R.measurable.sqrt).pow_const 2).aestronglyMeasurable ?_
          filter_upwards [L.nonneg, R.nonneg] with x hx hy
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact sqrt_difference_sq_le_add hx hy
        have hH := h_hellinger_integrable
        have hL := L.integrable.indicator hA.compl
        have hR := R.integrable.indicator hA
        have hp : (fun x => (3 / 8 : ℝ) * (L.density x + R.density x) -
            (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2) ≤ᵐ[μ]
            (fun x => Aᶜ.indicator L.density x + A.indicator R.density x) := by
          filter_upwards [L.nonneg, R.nonneg] with x hx hy
          have hl := square_root_testing_lower hx hy
          by_cases h : x ∈ A
          · rw [indicator_of_notMem (show x ∉ Aᶜ from fun hxA => hxA h),
              indicator_of_mem h, zero_add]
            convert hl.trans (min_le_right _ _) using 1; ring
          · rw [indicator_of_mem (show x ∈ Aᶜ from h), indicator_of_notMem h, add_zero]
            convert hl.trans (min_le_left _ _) using 1; ring
        have hi := integral_mono_ae
          (((L.integrable.add R.integrable).const_mul (3 / 8 : ℝ)).sub hH)
          (hL.add hR) hp
        change (∫ x, (3 / 8 : ℝ) * (L.density x + R.density x) -
          (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2 ∂μ) ≤
          ∫ x, Aᶜ.indicator L.density x + A.indicator R.density x ∂μ at hi
        have hI : Integrable (fun x => (3 / 8 : ℝ) * (L.density x + R.density x)) μ :=
          (L.integrable.add R.integrable).const_mul _
        rw [integral_sub hI hH,
          integral_const_mul, integral_add L.integrable R.integrable,
          L.integral_one, R.integral_one, integral_add hL hR,
          ← L.measureReal_eq_integral_indicator Aᶜ hA.compl,
          ← R.measureReal_eq_integral_indicator A hA] at hi
        norm_num at hi
        unfold hellingerSquared
        linarith
      have := (h_test_loss_lower (measurableSet_lt (hg.sub measurable_const).abs measurable_const))
      linarith
    have htest := h_test_loss_ge_half
    rw [he] at htest
    have := measureReal_mono (μ := R.measure) hsubset
    by_contra hn
    push Not at hn
    linarith
  have h_tailReal_to_eLpNorm (ν : Measure Ω) (g) (hg : Measurable g) (target) (δ) (hδ : 0 ≤ δ) (htail : (1 / 4 : ℝ) ≤ ν.real {x | δ / 2 ≤ |g x - target|}) : ENNReal.ofReal (δ / 4) ≤ eLpNorm (fun x => g x - target) 2 ν := by
    have h_tail_to_eLpNorm (htail : (1 / 4 : ℝ≥0∞) ≤ ν {x | δ / 2 ≤ |g x - target|}) : ENNReal.ofReal (δ / 4) ≤ eLpNorm (fun x => g x - target) 2 ν := by
      have hs := Applications.square_tail_lower ν (fun x => g x - target)
        (hg.sub measurable_const) (δ / 2) (by positivity)
      have hm : ENNReal.ofReal ((δ / 4) ^ 2) ≤
          ∫⁻ x, ENNReal.ofReal ((g x - target) ^ 2) ∂ν := by
        calc
          _ = ENNReal.ofReal ((δ / 2) ^ 2) * (1 / 4 : ℝ≥0∞) := by
            calc
              _ = ENNReal.ofReal ((δ / 2) ^ 2 * (1 / 4 )) := by congr 1; ring
              _ = ENNReal.ofReal ((δ / 2) ^ 2) * ENNReal.ofReal (1 / 4 ) :=
                ENNReal.ofReal_mul (sq_nonneg _)
              _ = _ := by
                rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
                norm_num
          _ ≤ ENNReal.ofReal ((δ / 2) ^ 2) * ν {x | δ / 2 ≤ |g x - target|} :=
            by gcongr
          _ ≤ _ := hs
      have hmeas : Measurable (fun x => g x - target) := hg.sub measurable_const
      rw [Applications.eLpNorm_two_eq_squaredIntegral ν (fun x => g x - target) hmeas]
      have hh := (ENNReal.le_rpow_inv_iff
        (x := ENNReal.ofReal (δ / 4))
        (y := ∫⁻ x, ENNReal.ofReal ((g x - target) ^ 2) ∂ν)
        (by norm_num : (0 : ℝ) < 2)).2
      simpa only [one_div] using hh (by rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity) 2]; exact hm)
    apply h_tail_to_eLpNorm
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using (ENNReal.ofReal_le_of_le_toReal htail)
  rcases h_two_point_absolute_large_error with h | h
  · exact Or.inl (h_tailReal_to_eLpNorm L.measure g hg a |b - a| (abs_nonneg _) h)
  · exact Or.inr (h_tailReal_to_eLpNorm R.measure g hg b |b - a| (abs_nonneg _) h)
end RoughRegime.GeneralTesting
end
section
namespace RoughRegime.Lower
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
end
theorem square_root_difference_bound {f g c : ℝ} (hc : 0 < c)
    (hf : c ≤ f) (hg : c ≤ g) :
    (Real.sqrt f - Real.sqrt g) ^ 2 ≤ (f - g) ^ 2 / (4 * c) := by
  have := Real.sqrt_nonneg g
  have := Real.sq_sqrt (le_of_lt hc)
  have := Real.sq_sqrt (le_trans (le_of_lt hc) hf)
  have := Real.sq_sqrt (le_trans (le_of_lt hc) hg)
  have : c ≤ Real.sqrt f * Real.sqrt g := by
    nlinarith [mul_le_mul (Real.sqrt_le_sqrt hf) (Real.sqrt_le_sqrt hg) (Real.sqrt_nonneg c) (Real.sqrt_nonneg f)]
  have hid : (f - g) ^ 2 =
      (Real.sqrt f - Real.sqrt g) ^ 2 * (Real.sqrt f + Real.sqrt g) ^ 2 := by
    have hi : f - g = (Real.sqrt f - Real.sqrt g) * (Real.sqrt f + Real.sqrt g) := by
      nlinarith
    rw [hi, mul_pow]
  apply (le_div_iff₀ (by positivity)).mpr
  rw [hid]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
theorem sqrt_finite_product {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    Real.sqrt (∏ i, f i) = ∏ i, Real.sqrt (f i) := by
  apply (Real.sqrt_eq_iff_eq_sq (Finset.prod_nonneg fun i _ => hf i)
    (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg (f i))).mpr
  rw [← Finset.prod_pow]
  simp_rw [Real.sq_sqrt (hf _)]
end RoughRegime.Lower
end
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace RoughRegime.LowerMeasure
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
theorem integrable_sqrt_product 
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf₀ : 0 ≤ᵐ[μ] f) (hg₀ : 0 ≤ᵐ[μ] g) :
    Integrable (fun x => Real.sqrt (f x) * Real.sqrt (g x)) μ := by
  apply ((hf.add hg).div_const 2).mono'
  · exact (hf.aemeasurable.sqrt.mul hg.aemeasurable.sqrt).aestronglyMeasurable
  · filter_upwards [hf₀, hg₀] with x hfx hgx
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
  have he : (fun x => (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2) =ᵐ[μ]
      fun x => L.density x + R.density x -
        2 * (Real.sqrt (L.density x) * Real.sqrt (R.density x)) := by
    filter_upwards [L.nonneg, R.nonneg] with x hx hy
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]
  unfold GeneralTesting.hellingerSquared
  rw [integral_congr_ae he]
  change (∫ x, (L.density + R.density) x -
    (fun x => 2 * (Real.sqrt (L.density x) * Real.sqrt (R.density x))) x ∂μ) = _
  rw [integral_sub (L.integrable.add R.integrable) ((densityAffinity_integrable L R).const_mul 2)]
  change (∫ x, L.density x + R.density x ∂μ) -
    (∫ x, 2 * (Real.sqrt (L.density x) * Real.sqrt (R.density x)) ∂μ) = _
  rw [integral_add L.integrable R.integrable, integral_const_mul, L.integral_one, R.integral_one]
  unfold densityAffinity
  ring
def iidDensityLaw [SigmaFinite μ] (L : GeneralTesting.DensityLaw μ) (n ) :
    GeneralTesting.DensityLaw (Measure.pi (fun _ : Fin n => μ)) where
  density xs := ∏ i, L.density (xs i)
  measurable := by
    apply Finset.measurable_prod
    intro i _
    exact L.measurable.comp (measurable_pi_apply i)
  integrable := Integrable.fintype_prod fun _ => L.integrable
  nonneg := by
    filter_upwards [(by filter_upwards [ae_le_pi (fun _ => L.nonneg)] with xs hx; exact hx)] with xs hx
    exact Finset.prod_nonneg fun i _ => hx i
  integral_one := by
    rw [integral_fin_nat_prod_eq_prod]
    simp [L.integral_one]
theorem iidDensityLaw_measure [SigmaFinite μ] (L : GeneralTesting.DensityLaw μ) (n ) :
    (iidDensityLaw L n).measure = Measure.pi (fun _ : Fin n => L.measure) := by
  apply (Measure.pi_eq (μ := fun _ => L.measure) ?_).symm
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by rw [← Measure.pi_pi (fun _ : Fin n => L.measure)]; exact measure_ne_top _ _)).mp
  rw [ENNReal.toReal_prod]
  change (iidDensityLaw L n).measure.real (Set.univ.pi s) = ∏ i, L.measure.real (s i)
  rw [(iidDensityLaw L n).measureReal_eq_setIntegral _ (MeasurableSet.univ_pi hs)]
  simp_rw [L.measureReal_eq_setIntegral _ (hs _)]
  rw [Measure.restrict_pi_pi]
  change (∫ xs : Fin n → Ω, ∏ i, L.density (xs i) ∂Measure.pi (fun i => μ.restrict (s i))) = _
  rw [integral_fin_nat_prod_eq_prod (fun _ => L.density)]
theorem hellinger_iid_le [SigmaFinite μ] (L R : GeneralTesting.DensityLaw μ) (n : ℕ) :
    GeneralTesting.hellingerSquared (iidDensityLaw L n) (iidDensityLaw R n) ≤
      n * GeneralTesting.hellingerSquared L R := by
  have h_densityAffinity_iid : densityAffinity (iidDensityLaw L n) (iidDensityLaw R n) = densityAffinity L R ^ n := by
    have he : (fun xs : Fin n → Ω =>
        Real.sqrt ((iidDensityLaw L n).density xs) * Real.sqrt ((iidDensityLaw R n).density xs)) =ᵐ[
          Measure.pi (fun _ : Fin n => μ)]
        fun xs => ∏ i, Real.sqrt (L.density (xs i)) * Real.sqrt (R.density (xs i)) := by
      filter_upwards [(by filter_upwards [ae_le_pi (fun _ : Fin n => L.nonneg)] with xs hx; exact hx), (by filter_upwards [ae_le_pi (fun _ : Fin n => R.nonneg)] with xs hx; exact hx)] with xs hpx hqx
      change Real.sqrt (∏ i, L.density (xs i)) * Real.sqrt (∏ i, R.density (xs i)) = _
      rw [Lower.sqrt_finite_product _ hpx, Lower.sqrt_finite_product _ hqx,
        Finset.prod_mul_distrib]
    unfold densityAffinity
    rw [integral_congr_ae he, integral_fin_nat_prod_eq_prod (fun _ : Fin n =>
      fun x : Ω => Real.sqrt (L.density x) * Real.sqrt (R.density x))]
    simp
  rw [hellinger_integral_eq, h_densityAffinity_iid, hellinger_integral_eq]
  have h_densityAffinity_nonneg : 0 ≤ densityAffinity L R := integral_nonneg fun _ =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have := one_add_mul_sub_le_pow (by linarith [h_densityAffinity_nonneg] :
    -1 ≤ densityAffinity L R) n
  nlinarith
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
    have hid : (f₀ x + t * f₁ x - (f₀ x + s * f₁ x)) ^ 2 =
        f₁ x ^ 2 * (t - s) ^ 2 := by ring
    rw [hid] at h
    exact le_trans h (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by nlinarith [sq_abs (f₁ x), abs_nonneg (f₁ x), hxf]) (sq_nonneg _)) (by positivity))
  have h_hellinger_integrable : Integrable (fun x => (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2) μ := by
    apply ((L.integrable.add R.integrable).sub ((densityAffinity_integrable L R).const_mul 2)).congr
    filter_upwards [L.nonneg, R.nonneg] with x hx hy
    change 0 ≤ L.density x at hx
    change 0 ≤ R.density x at hy
    change L.density x + R.density x - 2 * (Real.sqrt (L.density x) * Real.sqrt (R.density x)) = _
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]
  have hi := integral_mono_ae h_hellinger_integrable
    (integrable_const (Cf ^ 2 * (t - s) ^ 2 / (4 * cf))) hx
  simpa [GeneralTesting.hellingerSquared] using hi
def densityLawWithSeed  [MeasurableSpace S] (ν : Measure S)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (L : GeneralTesting.DensityLaw μ) :
    GeneralTesting.DensityLaw (μ.prod ν) where
  density x := L.density x.1
  measurable := L.measurable.comp measurable_fst
  integrable := by
    simpa using L.integrable.mul_prod (integrable_const ↑1 : Integrable (fun _ => ↑1) ν)
  nonneg := by
    filter_upwards [quasiMeasurePreserving_fst.tendsto_ae.eventually L.nonneg] with x hx
    exact hx
  integral_one := by
    rw [integral_fun_fst]
    simp [L.integral_one]
theorem densityLawWithSeed_measure  [MeasurableSpace S] (ν : Measure S)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (L : GeneralTesting.DensityLaw μ) :
    (densityLawWithSeed ν L).measure = L.measure.prod ν := (prod_withDensity_left (ENNReal.measurable_ofReal.comp L.measurable)).symm
theorem hellinger_with_seed  [MeasurableSpace S] (ν : Measure S)
    [SigmaFinite μ] [IsProbabilityMeasure ν] (L R : GeneralTesting.DensityLaw μ) :
    GeneralTesting.hellingerSquared (densityLawWithSeed ν L) (densityLawWithSeed ν R) =
      GeneralTesting.hellingerSquared L R := by
  change (∫ x : Ω × S, (Real.sqrt (L.density x.1) - Real.sqrt (R.density x.1)) ^ 2 ∂μ.prod ν) =
    ∫ x, (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2 ∂μ
  rw [integral_fun_fst (fun x => (Real.sqrt (L.density x) - Real.sqrt (R.density x)) ^ 2)]
  simp
end RoughRegime.LowerMeasure
end
open MeasureTheory ProbabilityTheory Set RoughRegime.GeneralTesting RoughRegime.LowerMeasure
open scoped ENNReal BigOperators
namespace NearlyMinimax
def labelBase : Measure (Fin 3) := ENNReal.ofReal (1 / 3 ) • Measure.count
instance labelBase_isProbability : IsProbabilityMeasure labelBase := by
  constructor
  simp [labelBase, Measure.smul_apply, Measure.count_univ]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
def ternaryDensityLaw (a V ) (ha : a ≠ 0)
    (hp : ∀ y, 0 ≤ ternaryMass a 0 V y) : DensityLaw labelBase where
  density y := 3 * ternaryMass a 0 V y
  measurable := measurable_of_countable _
  integrable := Integrable.of_finite
  nonneg := Filter.Eventually.of_forall (fun y => mul_nonneg (by norm_num) (hp y))
  integral_one := by
    rw [labelBase, integral_smul_measure, integral_count]
    norm_num only [ENNReal.toReal_ofReal, smul_eq_mul]
    rw [← Finset.mul_sum, ternary_normalized a 0 V ha]
    norm_num
theorem ternary_submodel_admissible  (C : ModelConstants d)
    (a V ) (ha : 0 < a) (hV : C.varianceLower ≤ V)
    (hVupper : V ≤ C.varianceUpper) (_hVa : V < a ^ 2)
    (hfourth : a ^ 2 * V ≤ C.fourthBound)
    (hp ) :
    Admissible C (uniformZeroParameter d a V ha.ne' hp) := by
  let θ := uniformZeroParameter d a V ha.ne' hp
  refine ⟨measurable_const, measurable_const, ?_, ?_, ?_, hV, hVupper, ?_⟩
  · exact Filter.Eventually.of_forall (fun x =>
      ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩)
  · simp only [uniformZeroParameter, ENNReal.ofReal_one, lintegral_const, one_mul]
    exact cubeVolume_univ d
  · refine ⟨fun _ => 0, fun _ _ => rfl, contDiffOn_const, ?_⟩
    rw [holderNorm_zero]
    exact zero_le
  · apply Filter.Eventually.of_forall
    intro x
    simp only [uniformZeroParameter, Kernel.const_apply]
    refine ⟨ternaryMeasure_integrable a 0 V _, ternaryMeasure_integrable a 0 V _,
      ternaryMeasure_integrable a 0 V _, ternaryMeasure_mean a 0 V ha.ne' hp, ?_, ?_⟩
    · simpa using ternaryMeasure_variance a 0 V ha.ne' hp
    · have he := ternaryMeasure_fourthMoment a 0 V ha.ne' hp
      simp only [sub_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0),
        mul_zero, add_zero] at he
      exact he.trans_le hfourth
def encodeResponse {d n : ℕ} (a : ℝ) :
    (Fin n → Fin 3) × (Fin n → Covariate d) → (Fin n → Observation d) :=
  fun z i => (z.2 i, ternaryValue a (z.1 i))
theorem encodeResponse_measurable  (a ) :
    Measurable (encodeResponse (d := d) (n := n) a) := by
  apply Measurable.of_eval
  intro i
  exact ((measurable_pi_apply i).comp measurable_snd).prodMk
    ((measurable_of_countable (ternaryValue a)).comp
      ((measurable_pi_apply i).comp measurable_fst))
theorem encodeResponse_measurePreserving  (a V ha hp) :
    MeasurePreserving (encodeResponse (d := d) (n := n) a)
      ((Measure.pi (fun _ => (ternaryDensityLaw a V ha hp).measure)).prod
        (Measure.pi (fun _ => cubeVolume d)))
      (sampleLaw (uniformZeroParameter d a V ha hp) n) := by
  let _ := cubeVolume_isProbability d
  let _ := ternaryMeasure_isProbability a 0 V ha hp
  let _ : IsProbabilityMeasure (observationLaw (uniformZeroParameter d a V ha hp)) := by
    rw [uniformZeroParameter_observationLaw]
    infer_instance
  have h_ternary_label_design_map : (((ternaryDensityLaw a V ha hp).measure).prod (cubeVolume d)).map
      (fun z => (z.2, ternaryValue a z.1)) =
        observationLaw (uniformZeroParameter d a V ha hp) := by
    let _ := cubeVolume_isProbability d
    let _ := ternaryMeasure_isProbability a 0 V ha hp
    rw [uniformZeroParameter_observationLaw]
    have h := Measure.map_prod_map (ternaryDensityLaw a V ha hp).measure (cubeVolume d)
      (measurable_of_countable (ternaryValue a)) measurable_id
    have h_ternaryDensityLaw_map : (ternaryDensityLaw a V ha hp).measure.map (ternaryValue a) = ternaryMeasure a 0 V := by
      have h_ternaryDensityLaw_measure : (ternaryDensityLaw a V ha hp).measure =
          Measure.count.withDensity (fun y => ENNReal.ofReal (ternaryMass a 0 V y)) := by
        unfold DensityLaw.measure ternaryDensityLaw labelBase
        rw [withDensity_smul_measure, ← withDensity_smul]
        · congr 1
          funext y
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)]
          congr 1
          ring
        · exact ENNReal.measurable_ofReal.comp (measurable_of_countable _)
      rw [h_ternaryDensityLaw_measure, count_withDensity,
        Measure.map_sum (measurable_of_countable _).aemeasurable, Measure.sum_fintype]
      apply Finset.sum_congr rfl
      intro y _
      rw [Measure.map_smul _ (measurable_of_countable _).aemeasurable, Measure.map_dirac]
    rw [h_ternaryDensityLaw_map, Measure.map_id] at h
    calc
      _ = ((((ternaryDensityLaw a V ha hp).measure).prod (cubeVolume d)).map
          (Prod.map (ternaryValue a) id)).map Prod.swap := by
        rw [Measure.map_map measurable_swap
          ((measurable_of_countable (ternaryValue a)).prodMap measurable_id)]
        rfl
      _ = ((ternaryMeasure a 0 V).prod (cubeVolume d)).map Prod.swap := by rw [← h]
      _ = _ := Measure.prod_swap
  have hsingle : MeasurePreserving (fun z =>
      (z.2, ternaryValue a z.1))
      (((ternaryDensityLaw a V ha hp).measure).prod (cubeVolume d))
      (observationLaw (uniformZeroParameter d a V ha hp)) :=
    ⟨measurable_snd.prodMk ((measurable_of_countable _).comp measurable_fst),
      h_ternary_label_design_map⟩
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin 3) (Covariate d) (Fin n)
  have he := (measurePreserving_arrowProdEquivProdArrow (Fin 3) (Covariate d) (Fin n)
    (fun _ => (ternaryDensityLaw a V ha hp).measure) (fun _ => cubeVolume d)).symm e
  have hm := (measurePreserving_pi _ _ (fun _ => hsingle)).comp he
  exact hm
def ternaryDensitySlope (a : ℝ) : Fin 3 → ℝ :=
  ![3 / (2 * a ^ 2), -3 / a ^ 2, 3 / (2 * a ^ 2)]
theorem ternary_density_affine (a V y) :
    3 * ternaryMass a 0 V y = ![0, 3, 0] y + V * ternaryDensitySlope a y := by
  fin_cases y <;> simp [ternaryMass, ternaryDensitySlope, div_eq_mul_inv] <;> ring
theorem ternary_two_point_minimax_lower  (C : ModelConstants d) (n : ℕ)
    (a V₀ V₁ cf Cf : ℝ) (ha : 0 < a) (hcf : 0 < cf) (hCf : 0 ≤ Cf)
    (hV₀ : C.varianceLower ≤ V₀) (hV₀upper : V₀ ≤ C.varianceUpper)
    (hV₁ : C.varianceLower ≤ V₁) (hV₁upper : V₁ ≤ C.varianceUpper)
    (hVa₀ : V₀ < a ^ 2) (hVa₁ : V₁ < a ^ 2)
    (hfourth₀ : a ^ 2 * V₀ ≤ C.fourthBound)
    (hfourth₁ : a ^ 2 * V₁ ≤ C.fourthBound)
    (hmass₀ : ∀ y, cf ≤ 3 * ternaryMass a 0 V₀ y)
    (hmass₁ : ∀ y, cf ≤ 3 * ternaryMass a 0 V₁ y)
    (hslope : ∀ y, |ternaryDensitySlope a y| ≤ Cf)
    (hsmall : (n : ℝ) * Cf ^ 2 * (V₀ - V₁) ^ 2 / (4 * cf) ≤ 1 / 4) :
    ENNReal.ofReal (|V₁ - V₀| / 4) ≤ minimaxRMS C n := by
  have hp₀ : ∀ y, 0 ≤ ternaryMass a 0 V₀ y := by
    intro y
    linarith [hmass₀ y]
  have hp₁ : ∀ y, 0 ≤ ternaryMass a 0 V₁ y := by
    intro y
    linarith [hmass₁ y]
  let θ₀ := uniformZeroParameter d a V₀ ha.ne' hp₀
  let θ₁ := uniformZeroParameter d a V₁ ha.ne' hp₁
  have hθ₀ : Admissible C θ₀ :=
    ternary_submodel_admissible C a V₀ ha hV₀ hV₀upper hVa₀ hfourth₀ hp₀
  have hθ₁ : Admissible C θ₁ :=
    ternary_submodel_admissible C a V₁ ha hV₁ hV₁upper hVa₁ hfourth₁ hp₁
  let P₀ := ternaryDensityLaw a V₀ ha.ne' hp₀
  let P₁ := ternaryDensityLaw a V₁ ha.ne' hp₁
  let ν := Measure.pi (fun _ : Fin n => cubeVolume d)
  let _ := cubeVolume_isProbability d
  let _ : IsProbabilityMeasure ν := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => cubeVolume d)))
  let L := densityLawWithSeed ν (iidDensityLaw P₀ n)
  let R := densityLawWithSeed ν (iidDensityLaw P₁ n)
  have hH : hellingerSquared L R ≤ 1 / 4 := by
    have hone := affine_hellinger_bound P₀ P₁ ![0, 3, 0] (ternaryDensitySlope a)
      V₀ V₁ cf Cf hcf hCf
      (Filter.Eventually.of_forall (ternary_density_affine a V₀))
      (Filter.Eventually.of_forall (ternary_density_affine a V₁))
      (Filter.Eventually.of_forall (fun y => by rw [← ternary_density_affine]; exact hmass₀ y))
      (Filter.Eventually.of_forall (fun y => by rw [← ternary_density_affine]; exact hmass₁ y))
      (Filter.Eventually.of_forall hslope)
    change hellingerSquared (densityLawWithSeed ν (iidDensityLaw P₀ n))
      (densityLawWithSeed ν (iidDensityLaw P₁ n)) ≤ _
    rw [hellinger_with_seed]
    exact (hellinger_iid_le P₀ P₁ n).trans
      ((mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg n)).trans (by
        convert hsmall using 1; ring))
  have hL : L.measure = (Measure.pi (fun _ : Fin n => P₀.measure)).prod ν := by
    dsimp [L]
    rw [densityLawWithSeed_measure, iidDensityLaw_measure]
  have hR : R.measure = (Measure.pi (fun _ : Fin n => P₁.measure)).prod ν := by
    dsimp [R]
    rw [densityLawWithSeed_measure, iidDensityLaw_measure]
  have h_minimaxRMS_eq_inf_sup_eLpNorm : minimaxRMS C n = ⨅ T : Estimator d n,
      ⨆ θ : {θ : RegressionParameter d // Admissible C θ},
        eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n) := by
    have h_meanSquaredRisk_rpow_eq_eLpNorm (T : Estimator d n) (θ : RegressionParameter d) : meanSquaredRisk T θ ^ (1 / 2 : ℝ) =
        eLpNorm (fun z => T.val z - θ.variance) 2 (sampleLaw θ n) := by
      symm
      exact RoughRegime.Applications.eLpNorm_two_eq_squaredIntegral (sampleLaw θ n)
        (fun z => T.val z - θ.variance) (T.property.sub measurable_const)
    have h_minimaxRMS_eq_inf_sup_rms : minimaxRMS C n = ⨅ T : Estimator d n,
        ⨆ θ : {θ : RegressionParameter d // Admissible C θ},
          meanSquaredRisk T θ.val ^ (1 / 2 : ℝ) := by
      let φ := ENNReal.orderIsoRpow (1 / 2 : ℝ) (by norm_num)
      change φ (⨅ T : Estimator d n, ⨆ θ : {θ // Admissible C θ}, meanSquaredRisk T θ.val) = _
      rw [φ.map_iInf]
      simp_rw [φ.map_iSup]
      rfl
    rw [h_minimaxRMS_eq_inf_sup_rms]
    simp_rw [h_meanSquaredRisk_rpow_eq_eLpNorm]
  rw [h_minimaxRMS_eq_inf_sup_eLpNorm]
  apply le_iInf
  intro T
  have ht := two_point_rmse_lower L R (T.val ∘ encodeResponse (d := d) (n := n) a)
    (T.property.comp (encodeResponse_measurable a)) V₀ V₁ hH
  rw [hL, hR] at ht
  have he₀ : eLpNorm (fun z => T.val (encodeResponse a z) - V₀) 2
      ((Measure.pi (fun _ : Fin n => P₀.measure)).prod ν) =
      eLpNorm (fun z => T.val z - θ₀.variance) 2 (sampleLaw θ₀ n) := by
    exact eLpNorm_comp_measurePreserving (T.property.sub measurable_const).aestronglyMeasurable
      (encodeResponse_measurePreserving a V₀ ha.ne' hp₀)
  have he₁ : eLpNorm (fun z => T.val (encodeResponse a z) - V₁) 2
      ((Measure.pi (fun _ : Fin n => P₁.measure)).prod ν) =
      eLpNorm (fun z => T.val z - θ₁.variance) 2 (sampleLaw θ₁ n) := by
    exact eLpNorm_comp_measurePreserving (T.property.sub measurable_const).aestronglyMeasurable
      (encodeResponse_measurePreserving a V₁ ha.ne' hp₁)
  change _ ≤ eLpNorm (fun z => T.val (encodeResponse a z) - V₀) 2 _ ∨
    _ ≤ eLpNorm (fun z => T.val (encodeResponse a z) - V₁) 2 _ at ht
  rw [he₀, he₁] at ht
  rcases ht with ht | ht
  · exact ht.trans (le_iSup (fun θ : {θ // Admissible C θ} =>
      eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n)) ⟨θ₀, hθ₀⟩)
  · exact ht.trans (le_iSup (fun θ : {θ // Admissible C θ} =>
      eLpNorm (fun z => T.val z - θ.val.variance) 2 (sampleLaw θ.val n)) ⟨θ₁, hθ₁⟩)
theorem ternaryDensitySlope_eq (a y) :
    ternaryDensitySlope a y = 3 * ternaryVarianceDerivative a y := by
  fin_cases y <;> simp [ternaryDensitySlope, ternaryVarianceDerivative] <;> ring
theorem parametric_minimax_lower {d : ℕ} (C : ModelConstants d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (c * ↑n ^ (-(1 / 2 : ℝ))) ≤ minimaxRMS C n := by
  obtain ⟨P⟩ := parametricTernaryConstants_exists C
  refine ⟨P.delta / 2, div_pos P.delta_pos (by norm_num), ?_⟩
  intro n hn
  have hm := P.varianceMinus_mem n hn
  have hp := P.variancePlus_mem n hn
  have hb₀ := P.model_variance_bounds _ hm
  have hb₁ := P.model_variance_bounds _ hp
  have htest := ternary_two_point_minimax_lower C n P.a (P.varianceMinus n)
    (P.variancePlus n) P.cf P.Cf P.a_pos P.cf_pos P.Cf_pos.le
    hb₀.1 hb₀.2 hb₁.1 hb₁.2
    (P.variance_lt_square_of_mem _ hm) (P.variance_lt_square_of_mem _ hp)
    (P.fourth_le_of_mem _ hm) (P.fourth_le_of_mem _ hp)
    (P.density_lower _ hm) (P.density_lower _ hp)
    (fun y => by rw [ternaryDensitySlope_eq]; exact P.derivative_bound y)
    (P.score_budget_reverse n hn)
  have hinv : ↑n ^ (-(1 / 2 : ℝ)) = (Real.sqrt ↑n)⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
  have hscale : |P.variancePlus n - P.varianceMinus n| / 4 =
      (P.delta / 2) * ↑n ^ (-(1 / 2 : ℝ)) := by
    rw [abs_of_pos (P.separation_pos n hn), P.separation n, hinv]
    ring
  rw [hscale] at htest
  exact htest
end NearlyMinimax
