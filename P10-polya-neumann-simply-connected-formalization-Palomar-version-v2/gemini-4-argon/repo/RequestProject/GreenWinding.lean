module

public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import RequestProject.ArcLength

/-!
# Green's formula through winding numbers

For a Lipschitz curve `γ : ℝ → ℂ` define the winding number
`wind(γ, z) = (2πi)⁻¹ ∫₀^{2π} γ'(θ) / (γ(θ) - z) dθ`.

* `PolyaNeumann.integral_ball_inv_sub`: the Cauchy transform of a disc,
  `∫_{|z| < R} (w - z)⁻¹ dz = π w̄` for `|w| < R`;
* `PolyaNeumann.integral_ball_windingNumber`: if `γ([0, 2π]) ⊂ {|z| < R}`, then
  `∫_{|z| < R} wind(γ, z) dz = (2i)⁻¹ ∫₀^{2π} conj(γ) γ'`;
* `PolyaNeumann.volume_image_Icc_eq_zero`: a Lipschitz curve has planar measure zero.

Together these give Green's formula `∫₀^{2π} Im(conj γ · γ') = ±2|Ω|` for a Jordan
parametrization of `∂Ω` whose winding number is `±1` on `Ω` and `0` off `Ω̄`.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

variable {γ : ℝ → ℂ}

/-- The winding number `(2πi)⁻¹ ∫₀^{2π} γ'(θ) / (γ(θ) - z) dθ` of a Lipschitz curve. -/
def windingNumber (γ : ℝ → ℂ) (z : ℂ) : ℂ :=
  (2 * π * Complex.I)⁻¹ * ∫ θ in 0..(2 * π), deriv γ θ / (γ θ - z)

/-- The angular integral of `(w - r e^{iφ})⁻¹`. -/
local notation "Φ0" => ball 0

lemma integral_inv_sub_circleMap w  (hr : 0 < r) (hrw : r ≠ ‖w‖) :
    ∫ φ in 0..(2 * π), (w - circleMap 0 r φ)⁻¹ =
      if r < ‖w‖ then 2 * π * w⁻¹ else 0 := by
  split_ifs with h
  · have hw0 : w ≠ 0 := by rintro rfl; simp at h; linarith
    have hd : DiffContOnCl ℂ (fun z => (w - z)⁻¹) (Φ0 |r|) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (by rw [abs_of_pos hr]; exact hr.ne')]
      intro z hz
      have : w - z ≠ 0 := by
        intro h0; rw [sub_eq_zero] at h0; subst h0
        simp [abs_of_pos hr] at hz; linarith
      exact ((differentiableAt_const _).sub differentiableAt_id).inv this |>.differentiableWithinAt
    have := hd.circleAverage
    rw [Real.circleAverage_def] at this
    simp only [sub_zero] at this
    have h2 : 2 * π ≠ 0 := by positivity
    rw [← this, Complex.real_smul, ← mul_assoc]
    push_cast
    field_simp
  · have hlt := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hrw)
    have key : ∫ φ in 0..(2 * π), (w - circleMap 0 r φ)⁻¹ =
        ∮ z in C(0, r), (z * Complex.I)⁻¹ * (w - z)⁻¹ := by
      rw [circleIntegral]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [deriv_circleMap, smul_eq_mul]
      have := (fun θ => circleMap_ne_center hr.ne' : ∀ θ, circleMap 0 r θ ≠ 0) θ
      field_simp
    rw [key]
    by_cases hw0 : w = 0
    · subst hw0
      have : ∮ z in C(0, r), (z * Complex.I)⁻¹ * (0 - z)⁻¹ =
          ∮ z in C(0, r), (-Complex.I⁻¹) • (z - 0) ^ (-2 : ℤ) := by
        refine circleIntegral.integral_congr hr.le fun z hz => ?_
        simp only [sub_zero, zero_sub, smul_eq_mul, zpow_neg]
        rw [zpow_two, mul_inv, mul_inv, inv_neg]; ring
      rw [this, circleIntegral.integral_smul, circleIntegral.integral_sub_zpow_of_ne (by norm_num),
        smul_zero]
    · have : ∮ z in C(0, r), (z * Complex.I)⁻¹ * (w - z)⁻¹ =
          ∮ z in C(0, r), (Complex.I * w)⁻¹ • ((z - 0)⁻¹ - (z - w)⁻¹) := by
        refine circleIntegral.integral_congr hr.le fun z hz => ?_
        have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
        have hzw : z - w ≠ 0 := by
          intro h0; rw [sub_eq_zero] at h0; subst h0; simp at hz; linarith
        have hwz : w - z ≠ 0 := fun h0 => hzw (by rw [← neg_sub, h0, neg_zero])
        simp only [sub_zero, smul_eq_mul]
        field_simp
        ring
      rw [this, circleIntegral.integral_smul, circleIntegral.integral_sub,
        circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hr),
        circleIntegral.integral_sub_inv_of_mem_ball (by simpa using hlt), sub_self, smul_zero]
      · exact circleIntegrable_sub_inv_iff.mpr (Or.inr (by simp [abs_of_pos hr]; exact hr.ne))
      · exact circleIntegrable_sub_inv_iff.mpr (Or.inr (by simp [abs_of_pos hr]; linarith))

/-- `∫_{|u| < ρ} |u|⁻¹ du ≤ 2πρ` (polar coordinates). -/
lemma lintegral_ball_inv_norm_le  (hρ : 0 ≤ ρ) :
    ∫⁻ u in ball (0 : ℂ) ρ, ‖u‖ₑ⁻¹ ≤ ENNReal.ofReal (2 * π * ρ) := by
  rw [← lintegral_indicator measurableSet_ball, ← Complex.lintegral_comp_polarCoord_symm]
  calc _
      ≤ _ :=
        setLIntegral_mono' Complex.polarCoord.open_target.measurableSet (by
          intro p hp
          rw [Complex.polarCoord_target] at hp
          obtain ⟨hp1, hp2⟩ := hp
          have hp1' : 0 < p.1 := hp1
          have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
            rw [Complex.norm_polarCoord_symm, abs_of_pos hp1']
          by_cases hb : p.1 < ρ
          · have hmem : Complex.polarCoord.symm p ∈ Φ0 ρ := by
              rw [mem_ball_zero_iff, hn]; exact hb
            rw [indicator_of_mem hmem, indicator_of_mem (by exact ⟨⟨hp1', hb⟩, hp2⟩), smul_eq_mul, ← ofReal_norm, hn, Pi.one_apply]
            rw [ENNReal.mul_inv_cancel (by simpa using hp1') ENNReal.ofReal_ne_top]
          · have hmem : Complex.polarCoord.symm p ∉ Φ0 ρ := by
              rw [mem_ball_zero_iff, hn]; exact hb
            rw [indicator_of_notMem hmem]; simp)
    _ ≤ _ := setLIntegral_le_lintegral _ _
    _ = _ :=
        lintegral_indicator_one (measurableSet_Ioo.prod measurableSet_Ioo)
    _ = _ := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
          ← ENNReal.ofReal_mul (by linarith)]
        congr 1; ring

/-- `∫_{|z| < R} |w - z|⁻¹ dz ≤ 4πR` for `|w| ≤ R`. -/
lemma lintegral_ball_inv_norm_sub_le  (hR : 0 ≤ R) {w : ℂ} (hw : ‖w‖ ≤ R) :
    ∫⁻ z in Φ0 R, ‖w - z‖ₑ⁻¹ ≤ ENNReal.ofReal (4 * π * R) := by
  calc ∫⁻ z in Φ0 R, ‖w - z‖ₑ⁻¹ ≤ ∫⁻ z in ball w (2 * R), ‖w - z‖ₑ⁻¹ :=
        lintegral_mono_set (by
          intro z hz
          rw [mem_ball_zero_iff] at hz
          rw [mem_ball, dist_eq_norm]
          calc ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le _ _
            _ < R + R := by linarith
            _ = 2 * R := by ring)
    _ = ∫⁻ z, (Φ0 (2 * R)).indicator (fun u => ‖u‖ₑ⁻¹) (z - w) := by
        rw [← lintegral_indicator measurableSet_ball]
        congr 1; funext z
        by_cases hz : z ∈ ball w (2 * R)
        · have hz' : z - w ∈ Φ0 (2 * R) := by
            rwa [mem_ball_zero_iff, ← dist_eq_norm]
          rw [indicator_of_mem hz, indicator_of_mem hz', ← enorm_neg, neg_sub]
        · have hz' : z - w ∉ Φ0 (2 * R) := by
            rwa [mem_ball_zero_iff, ← dist_eq_norm]
          rw [indicator_of_notMem hz, indicator_of_notMem hz']
    _ = _ := by
        rw [lintegral_sub_right_eq_self (fun u => (ball (0 : ℂ) (2 * R)).indicator
          (fun u => ‖u‖ₑ⁻¹) u) w, lintegral_indicator measurableSet_ball]
    _ ≤ _ := lintegral_ball_inv_norm_le (by linarith)
    _ = ENNReal.ofReal (4 * π * R) := by ring_nf

lemma enorm_inv_le_inv_enorm (x : ℂ) : ‖x⁻¹‖ₑ ≤ ‖x‖ₑ⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [enorm_inv hx]

lemma measurable_complexPolarCoord_symm : Measurable (Complex.polarCoord.symm) := by
  rw [funext fun p => (Complex.measurableEquivRealProd_symm_polarCoord_symm_apply p).symm]
  exact Complex.measurableEquivRealProd.symm.measurable.comp continuous_polarCoord_symm.measurable

/-- The Cauchy transform of a disc: `∫_{|z| < R} (w - z)⁻¹ dz = π w̄` for `|w| < R`. -/
theorem integral_ball_inv_sub {R : ℝ}  (hw : ‖w‖ < R) :
    ∫ z in ball (0 : ℂ) R, (w - z)⁻¹ = π * conj w := by
  set f := (Φ0 R).indicator (fun z => (w - z)⁻¹) with hf
  have hgi : IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (Ioi 0 ×ˢ Ioo (-π) π) := by
    refine ⟨(measurable_fst.smul
      (((measurable_const.sub measurable_id).inv.indicator measurableSet_ball).comp measurable_complexPolarCoord_symm)).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    rw [show ∫⁻ p in Ioi 0 ×ˢ Ioo (-π) π, ‖p.1 • f (Complex.polarCoord.symm p)‖ₑ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • ‖f (Complex.polarCoord.symm p)‖ₑ by
      refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
      rw [enorm_smul, smul_eq_mul, Real.enorm_eq_ofReal (le_of_lt hp.1)], Complex.lintegral_comp_polarCoord_symm (fun z => ‖f z‖ₑ)]
    calc _ = _ := by
          rw [← lintegral_indicator measurableSet_ball]
          congr 1; funext z; simp [hf, enorm_indicator_eq_indicator_enorm]
      _ ≤ _ :=
          lintegral_mono fun z => enorm_inv_le_inv_enorm _
      _ ≤ _ := lintegral_ball_inv_norm_sub_le (lt_of_le_of_lt (norm_nonneg _) hw).le hw.le
      _ < ⊤ := ENNReal.ofReal_lt_top
  rw [← integral_indicator measurableSet_ball, ← Complex.integral_comp_polarCoord_symm]
  change ∫ p in Ioi 0 ×ˢ Ioo (-π) π, p.1 • f (Complex.polarCoord.symm p) = _
  rw [Measure.volume_eq_prod] at hgi ⊢
  rw [setIntegral_prod _ hgi]
  simp_rw [show ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = circleMap 0 p.1 p.2 by
    intro p
    rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]]
  rw [setIntegral_congr_ae measurableSet_Ioi (by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton ‖w‖)] with x hx hx0
    exact (show ∀ x : ℝ, 0 < x → x ≠ ‖w‖ → ∫ y in Ioo (-π) π, x • f (circleMap 0 x y) = (Iio ‖w‖).indicator (fun x => x * (2 * π * w⁻¹)) x by
      intro x hx hxw
      have hn : ∀ y, ‖circleMap 0 x y‖ = x := fun y => by simp [abs_of_pos hx]
      by_cases hxR : x < R
      · have : ∀ y, f (circleMap 0 x y) = (w - circleMap 0 x y)⁻¹ := fun y => by
          rw [hf, indicator_of_mem (by rw [mem_ball_zero_iff, hn]; exact hxR)]
        simp_rw [this]
        rw [integral_smul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
          (by linarith [Real.pi_pos])]
        have hper : Function.Periodic (fun y => (w - circleMap 0 x y)⁻¹) (2 * π) := fun y => by
          simp [periodic_circleMap 0 x y]
        have := hper.intervalIntegral_add_eq (-π) 0
        rw [show -π + 2 * π = π by ring, zero_add] at this
        rw [this, integral_inv_sub_circleMap w hx hxw]
        split_ifs with h
        · rw [indicator_of_mem (show x ∈ Iio ‖w‖ from h), Complex.real_smul]
        · rw [indicator_of_notMem (show x ∉ Iio ‖w‖ from h), smul_zero]
      · have : ∀ y, f (circleMap 0 x y) = 0 :=
          fun y => indicator_of_notMem (by rw [mem_ball_zero_iff, hn]; exact hxR) _
        simp_rw [this, smul_zero, integral_zero]
        rw [indicator_of_notMem (show x ∉ Iio ‖w‖ by simp; linarith)]) x hx0 hx)]
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    show Iio ‖w‖ ∩ Ioi 0 = Ioo 0 ‖w‖ by ext; simp [and_comm],
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (norm_nonneg _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, integral_id]
  by_cases hw0 : w = 0
  · simp [hw0]
  · push_cast
    rw [← Complex.mul_conj']
    field_simp
    ring

/-- Green's formula through winding numbers: for a Lipschitz curve with
`γ([0, 2π]) ⊂ {|z| < R}`, `∫_{|z| < R} wind(γ, z) dz = (2i)⁻¹ ∫₀^{2π} conj(γ) γ'`. -/
theorem integral_ball_windingNumber   (hK : LipschitzWith K γ) 
    (hγR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ‖ < R) :
    ∫ z in Φ0 R, windingNumber γ z =
      (2 * Complex.I)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), conj (γ θ) * deriv γ θ := by
  have hpi : 0 ≤ 2 * π := by positivity
  set F : ℂ → ℝ → ℂ := fun z θ => deriv γ θ * (γ θ - z)⁻¹ with hF
  have hFm : Measurable (Function.uncurry F) :=
    ((measurable_deriv γ).comp measurable_snd).mul
      ((hK.continuous.measurable.comp measurable_snd).sub measurable_fst).inv
  simp_rw [show ∀ z, windingNumber γ z = (2 * π * Complex.I)⁻¹ * ∫ θ in Ioc 0 (2 * π), F z θ by
    intro z
    rw [windingNumber, intervalIntegral.integral_of_le hpi]
    rfl]
  rw [integral_const_mul, integral_integral_swap (by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod_symm _ hFm.enorm.aemeasurable]
    calc _
        ≤ _ :=
          setLIntegral_mono' measurableSet_Ioc (by
            intro θ hθ
            calc ∫⁻ z in Φ0 R, ‖Function.uncurry F (z, θ)‖ₑ
                ≤ ∫⁻ z in Φ0 R, K * ‖γ θ - z‖ₑ⁻¹ := by
                  refine lintegral_mono fun z => ?_
                  simp [hF]
                  gcongr
                  · rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
                    exact ENNReal.ofReal_le_ofReal (norm_deriv_le_of_lipschitzWith hK θ)
                  · exact enorm_inv_le_inv_enorm _
              _ = _ :=
                  lintegral_const_mul' _ _ ENNReal.coe_ne_top
              _ ≤ K * ENNReal.ofReal (4 * π * R) := by
                  gcongr
                  exact lintegral_ball_inv_norm_sub_le (le_trans (norm_nonneg _) (hγR 0 ⟨le_rfl, hpi⟩).le) (hγR θ ⟨hθ.1.le, hθ.2⟩).le)
      _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Ioc]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)
            ENNReal.ofReal_lt_top), intervalIntegral.integral_of_le hpi]
  rw [setIntegral_congr_fun measurableSet_Ioc (show ∀ θ ∈ Ioc 0 (2 * π), ∫ z in Φ0 R, F z θ = π * (conj (γ θ) * deriv γ θ) by
    intro θ hθ
    simp [hF]
    rw [integral_const_mul, integral_ball_inv_sub (hγR θ ⟨hθ.1.le, hθ.2⟩)]
    ring), integral_const_mul]
  rw [← mul_assoc]
  congr 1
  field_simp

/-- A Lipschitz curve has planar measure zero. -/
theorem volume_image_Icc_eq_zero   (hK : LipschitzWith K γ) a b :
    volume (γ '' Icc a b) = 0 := by
  set g := Complex.equivRealProdCLM ∘ γ
  have h0 : (volume : Measure (ℝ × ℝ)) (g '' Icc a b) = 0 := by rw [← (show μH[((2 : NNReal) : ℝ)] = volume by
    rw [NNReal.coe_ofNat]; exact MeasureTheory.hausdorffMeasure_prod_real)]; exact (hausdorffMeasure_of_dimH_lt (by
    calc _ ≤ _ := ((Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).lipschitz.comp hK).dimH_image_le _
      _ ≤ _ := dimH_mono (subset_univ _)
      _ = 1 := by rw [Real.dimH_univ_eq_finrank]; simp
      _ < _ := by norm_num))
  rw [show γ '' Icc a b = Complex.measurableEquivRealProd ⁻¹' (g '' Icc a b) by
    ext z
    simp only [mem_image, mem_preimage, g, Function.comp_apply]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, h⟩
      exact ⟨t, ht, Complex.equivRealProd.injective h⟩, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]
  exact h0

/-- Green's formula for a Lipschitz parametrization of the boundary of a bounded open set `Ω`
whose winding number is `σ` on `Ω` and `0` off `Ω̄`:
`∫₀^{2π} Im(conj γ · γ') = 2σ|Ω|`. -/
theorem integral_signedAreaDensity_of_winding {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω)   (hK : LipschitzWith K γ)
    (himage : γ '' Icc 0 (2 * π) = frontier Ω) (σ : ℝ)
    (hin : ∀ z ∈ Ω, windingNumber γ z = σ) (hout : ∀ z, z ∉ closure Ω → windingNumber γ z = 0) :
    ∫ θ in 0..(2 * π), signedAreaDensity γ θ = 2 * σ * (volume Ω).toReal := by
  obtain ⟨R, hR⟩ := hb.closure.subset_ball 0
  have hgreen := integral_ball_windingNumber hK (by
    intro θ hθ
    exact mem_ball_zero_iff.mp (hR (frontier_subset_closure (himage ▸ mem_image_of_mem γ hθ))))
  have hae : ∀ᵐ z ∂(volume.restrict (Φ0 R)),
      windingNumber γ z = Ω.indicator (fun _ => (σ : ℂ)) z := by
    refine ae_restrict_of_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (himage ▸ volume_image_Icc_eq_zero hK 0 (2 * π))] with z hz
    by_cases hzΩ : z ∈ Ω
    · rw [indicator_of_mem hzΩ, hin z hzΩ]
    · rw [indicator_of_notMem hzΩ]
      refine hout z fun hc => hz ?_
      rw [frontier, hΩ.interior_eq]
      exact ⟨hc, hzΩ⟩
  rw [integral_congr_ae hae, integral_indicator hΩ.measurableSet,
    Measure.restrict_restrict hΩ.measurableSet, inter_eq_self_of_subset_left (subset_closure.trans hR),
    setIntegral_const] at hgreen
  rw [show ∫ θ in 0..(2 * π), signedAreaDensity γ θ = (∫ θ in 0..(2 * π), conj (γ θ) * deriv γ θ).im by
    rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm (by
      obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
        (f := γ) hK.continuous.continuousOn
      refine (intervalIntegrable_const (c := M * K)).mono_fun' (((Complex.continuous_conj.comp hK.continuous).measurable.mul (measurable_deriv γ)).aestronglyMeasurable).restrict ?_
      rw [uIoc_of_le (by positivity)]
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun θ hθ => ?_)
      show ‖conj (γ θ) * deriv γ θ‖ ≤ M * K
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hM θ ⟨hθ.1.le, hθ.2⟩) (norm_deriv_le_of_lipschitzWith hK θ)
        (norm_nonneg _) ((norm_nonneg _).trans (hM θ ⟨hθ.1.le, hθ.2⟩)))]
    rfl, show ∫ θ in 0..(2 * π), conj (γ θ) * deriv γ θ = 2 * Complex.I * ((volume Ω).toReal * σ : ℝ) by
    rw [measureReal_def, Complex.real_smul] at hgreen
    have h2 : 2 * Complex.I ≠ 0 := by simp
    rw [Complex.ofReal_mul, hgreen]
    field_simp]
  simp
  ring

end PolyaNeumann

end
