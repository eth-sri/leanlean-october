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

/-- The winding number `(2πi)⁻¹ ∫₀^{2π} γ'(θ) / (γ(θ) - z) dθ` of a Lipschitz curve. -/
def windingNumber (γ : ℝ → ℂ) (z : ℂ) : ℂ :=
  (2 * π * Complex.I)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), deriv γ θ / (γ θ - z)

variable {R : ℝ} {γ : ℝ → ℂ} {K : NNReal}

/-- The angular integral of `(w - r e^{iφ})⁻¹`. -/
lemma integral_inv_sub_circleMap (w : ℂ) {r : ℝ} (hr : 0 < r) (hrw : r ≠ ‖w‖) :
    ∫ φ in 0..(2 * π), (w - circleMap 0 r φ)⁻¹ =
      if r < ‖w‖ then 2 * π * w⁻¹ else 0 := by
  split_ifs with h
  · have hd : DiffContOnCl ℂ (fun z  => (w - z)⁻¹) (ball 0 |r|) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (by positivity)]
      intro z hz
      have : w - z ≠ 0 := by
        intro h0; rw [sub_eq_zero] at h0; subst h0
        simp [abs_of_pos hr] at hz; linarith
      fun_prop
    have := hd.circleAverage
    rw [Real.circleAverage_def] at this
    simp only [sub_zero] at this
    rw [← this]
    rw [Complex.real_smul]
    push_cast
    field_simp
  · have hlt  := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hrw)
    have hcm : ∀ θ, circleMap 0 r θ ≠ 0 := fun θ => circleMap_ne_center hr.ne'
    have key : ∫ φ in 0..(2 * π), (w - circleMap 0 r φ)⁻¹ =
        ∮ z in C(0, r), (z * Complex.I)⁻¹ * (w - z)⁻¹ := by
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [deriv_circleMap, smul_eq_mul]
      have := hcm θ
      field_simp
    rw [key]
    by_cases hw0 : w = 0
    · subst hw0
      have : ∮ z in C(0, r), (z * Complex.I)⁻¹ * (0 - z)⁻¹ =
          ∮ z in C(0, r), (-Complex.I⁻¹) • (z - 0) ^ (-2 : ℤ) := by
        refine circleIntegral.integral_congr hr.le fun z hz => ?_
        simp 
        field_simp
      rw [this, circleIntegral.integral_smul, circleIntegral.integral_sub_zpow_of_ne (by norm_num),
        smul_zero]
    · have : ∮ z in C(0, r), (z * Complex.I)⁻¹ * (w - z)⁻¹ =
          ∮ z in C(0, r), ((Complex.I * w)⁻¹ • ((z - 0)⁻¹ - (z - w)⁻¹)) := by
        refine circleIntegral.integral_congr hr.le fun z hz => ?_
        have hz0 : z ≠ 0 := by rintro rfl; simp_all
        have hzw : z - w ≠ 0 := by
          intro h0; simp_all [sub_eq_zero]
        have hwz : w - z ≠ 0 := fun h0 => hzw (by grind)
        simp 
        field_simp
        ring
      rw [this, circleIntegral.integral_smul, circleIntegral.integral_sub,
        circleIntegral.integral_sub_inv_of_mem_ball (by simp_all),
        circleIntegral.integral_sub_inv_of_mem_ball (by simp_all), sub_self, smul_zero]
      · exact (circleIntegrable_sub_inv_iff).mpr (Or.inr (by simp ; positivity))
      · exact (circleIntegrable_sub_inv_iff).mpr (Or.inr (by simp [abs_of_pos hr]; linarith))

/-- `∫_{|u| < ρ} |u|⁻¹ du ≤ 2πρ` (polar coordinates). -/
lemma lintegral_ball_inv_norm_le {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫⁻ u in ball (0 : ℂ) ρ, ‖u‖ₑ⁻¹ ≤ ENNReal.ofReal (2 * π * ρ) := by
  rw [← lintegral_indicator measurableSet_ball, ← Complex.lintegral_comp_polarCoord_symm]
  calc ∫⁻ p in Complex.polarCoord.target, ENNReal.ofReal p.1 •
          (ball 0 ρ).indicator (fun u => ‖u‖ₑ⁻¹) (Complex.polarCoord.symm p)
      ≤ ∫⁻ p in Complex.polarCoord.target, (Ioo 0 ρ ×ˢ Ioo (-π) π).indicator 1 p :=
        setLIntegral_mono' (Complex.polarCoord.open_target.measurableSet) (by
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases hb : p.1 < ρ
    · rw [indicator_of_mem (by
        rw [mem_ball_zero_iff, hn]; assumption), indicator_of_mem (by trivial)]
      rw [← ofReal_norm, hn]
      norm_num
    · have hmem : Complex.polarCoord.symm p ∉ ball 0 ρ := by
        rw [mem_ball_zero_iff, hn]; assumption
      simp_all)
    _ ≤ ∫⁻ p, (Ioo 0 ρ ×ˢ Ioo (-π) π).indicator 1 p := setLIntegral_le_lintegral _ _
    _ = volume (Ioo 0 ρ ×ˢ Ioo (-π) π) :=
        lintegral_indicator_one (measurableSet_Ioo.prod measurableSet_Ioo)
    _ = ENNReal.ofReal (2 * π * ρ) := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
          ← ENNReal.ofReal_mul (by linarith)]
        ring

/-- `∫_{|z| < R} |w - z|⁻¹ dz ≤ 4πR` for `|w| ≤ R`. -/
lemma lintegral_ball_inv_norm_sub_le (hR : 0 ≤ R) {w : ℂ} (hw : ‖w‖ ≤ R) :
    ∫⁻ z in ball 0 R, ‖w - z‖ₑ⁻¹ ≤ ENNReal.ofReal (4 * π * R) := by
  calc ∫⁻ z in ball 0 R, ‖w - z‖ₑ⁻¹ ≤ ∫⁻ z in ball w (2 * R), ‖w - z‖ₑ⁻¹ :=
        lintegral_mono_set (by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    rw [mem_ball, dist_eq_norm]
    calc ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le _ _
      _ < R + R := by linarith
      _ = 2 * R := by ring)
    _ = ∫⁻ z, (ball 0 (2 * R)).indicator (fun u => ‖u‖ₑ⁻¹) (z - w) := by
        rw [← lintegral_indicator measurableSet_ball]
        congr 1; funext z
        by_cases hz : z ∈ ball w (2 * R)
        · rw [indicator_of_mem hz, indicator_of_mem (by
            rwa [mem_ball_zero_iff, ← dist_eq_norm]), ← enorm_neg, neg_sub]
        simp_all [← dist_eq_norm]
    _ = ∫⁻ u in ball (0 : ℂ) (2 * R), ‖u‖ₑ⁻¹ := by
        simp [lintegral_sub_right_eq_self (fun u => (ball 0 (2 * R)).indicator           (fun u => ‖u‖ₑ⁻¹) u) w, lintegral_indicator measurableSet_ball]
    _ ≤ ENNReal.ofReal (2 * π * (2 * R)) := lintegral_ball_inv_norm_le (by linarith)
    _ = ENNReal.ofReal (4 * π * R) := by ring_nf

lemma enorm_inv_le_inv_enorm (x : ℂ) : ‖x⁻¹‖ₑ ≤ ‖x‖ₑ⁻¹ := by
  by_cases hx : x = 0
  all_goals simp_all

lemma measurable_complexPolarCoord_symm : Measurable (Complex.polarCoord.symm) := Complex.measurableEquivRealProd.symm.measurable.comp continuous_polarCoord_symm.measurable

/-- The Cauchy transform of a disc: `∫_{|z| < R} (w - z)⁻¹ dz = π w̄` for `|w| < R`. -/
theorem integral_ball_inv_sub {w : ℂ} (hw : ‖w‖ < R) :
    ∫ z in ball 0 R, (w - z)⁻¹ = π * conj w := by
  set f : ℂ → ℂ := (ball 0 R).indicator (fun z => (w - z)⁻¹) with hf
  have hpol : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    simp [circleMap, Complex.exp_mul_I]
  have hgi : IntegrableOn (fun p  => p.1 • f (Complex.polarCoord.symm p))
      (Ioi 0 ×ˢ Ioo (-π) π) := by
    refine ⟨(measurable_fst.smul
      (((measurable_const.sub measurable_id).inv.indicator measurableSet_ball).comp measurable_complexPolarCoord_symm)).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have h1 : ∫⁻ p in Ioi 0 ×ˢ Ioo (-π) π, ‖p.1 • f (Complex.polarCoord.symm p)‖ₑ =
        ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • ‖f (Complex.polarCoord.symm p)‖ₑ := by
      refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
      rw [enorm_smul, smul_eq_mul, Real.enorm_eq_ofReal (le_of_lt hp.1)]
    rw [h1, Complex.lintegral_comp_polarCoord_symm (fun z => ‖f z‖ₑ)]
    calc ∫⁻ z, ‖f z‖ₑ = ∫⁻ z in ball 0 R, ‖(w - z)⁻¹‖ₑ := by
          simp [← lintegral_indicator measurableSet_ball, hf, enorm_indicator_eq_indicator_enorm]
      _ ≤ ∫⁻ z in ball 0 R, ‖w - z‖ₑ⁻¹ :=
          lintegral_mono fun z => enorm_inv_le_inv_enorm _
      _ ≤ ENNReal.ofReal (4 * π * R) := lintegral_ball_inv_norm_sub_le (lt_of_le_of_lt (norm_nonneg _) hw).le hw.le
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hinner : ∀ x : ℝ, 0 < x → x ≠ ‖w‖ →
      ∫ y in Ioo (-π) π, x • f (circleMap 0 x y) =
        (Iio ‖w‖).indicator (fun x  => x * (2 * π * w⁻¹)) x := by
    intro x hx hxw
    have hn : ∀ y, ‖circleMap 0 x y‖ = x := fun y => by simp [abs_of_pos hx]
    by_cases hxR : x < R
    · have : ∀ y, f (circleMap 0 x y) = (w - circleMap 0 x y)⁻¹ := fun y => by
        rw [hf, indicator_of_mem (by rw [mem_ball_zero_iff, hn]; assumption)]
      simp_rw [this]
      rw [integral_smul, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
        (by linarith [Real.pi_pos])]
      have hper : Function.Periodic (fun y => (w - circleMap 0 x y)⁻¹) (2 * π) := fun y => by
        simp [periodic_circleMap 0 x y]
      have := hper.intervalIntegral_add_eq (-π) 0
      rw [show -π + 2 * π = π by ring, zero_add] at this
      rw [this, integral_inv_sub_circleMap w hx hxw]
      split_ifs with h
      all_goals simp_all
    · have : ∀ y, f (circleMap 0 x y) = 0 :=
        fun y => indicator_of_notMem (by rw [mem_ball_zero_iff, hn]; assumption) _
      simp_rw [this, smul_zero, integral_zero]
      rw [indicator_of_notMem (by simp; linarith)]
  rw [← integral_indicator measurableSet_ball, ← Complex.integral_comp_polarCoord_symm]
  change ∫ p in Ioi 0 ×ˢ Ioo (-π) π, p.1 • f (Complex.polarCoord.symm p) = _
  rw [Measure.volume_eq_prod] at hgi ⊢
  rw [setIntegral_prod _ hgi]
  simp_rw [hpol]
  have hae : ∀ᵐ x ∂volume, x ∈ Ioi 0 →
      ∫ y in Ioo (-π) π, x • f (circleMap 0 x y) =
        (Iio ‖w‖).indicator (fun x  => x * (2 * π * w⁻¹)) x := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton ‖w‖)] with x hx hx0
    simp_all
  rw [setIntegral_congr_ae measurableSet_Ioi hae]
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    show Iio ‖w‖ ∩ Ioi 0 = Ioo 0 ‖w‖ by grind,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (norm_nonneg _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, integral_id]
  by_cases hw0 : w = 0
  · simp_all
  · push_cast
    rw [← Complex.mul_conj']
    field_simp
    ring

/-- Green's formula through winding numbers: for a Lipschitz curve with
`γ([0, 2π]) ⊂ {|z| < R}`, `∫_{|z| < R} wind(γ, z) dz = (2i)⁻¹ ∫₀^{2π} conj(γ) γ'`. -/
theorem integral_ball_windingNumber {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {R : ℝ}
    (hγR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ‖ < R) :
    ∫ z in ball 0 R, windingNumber γ z =
      (2 * Complex.I)⁻¹ * ∫ θ in 0..(2 * π), conj (γ θ) * deriv γ θ := by
  have hpi : 0 ≤ 2 * π := by positivity
  set F : ℂ → ℝ → ℂ := fun z θ => deriv γ θ * (γ θ - z)⁻¹ with hF
  have hFm : Measurable (Function.uncurry F) :=
    ((measurable_deriv γ).comp measurable_snd).mul
      ((hK.continuous.measurable.comp measurable_snd).sub measurable_fst).inv
  have hwind : ∀ z, windingNumber γ z =
      (2 * π * Complex.I)⁻¹ * ∫ θ in Ioc 0 (2 * π), F z θ := by
    intro z
    rw [windingNumber, intervalIntegral.integral_of_le hpi]
    rfl
  simp_rw [hwind]
  rw [integral_const_mul, integral_integral_swap (by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod_symm _ hFm.enorm.aemeasurable]
    calc ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ z in ball 0 R, ‖Function.uncurry F (z, θ)‖ₑ
        ≤ ∫⁻ θ in Ioc 0 (2 * π), K * ENNReal.ofReal (4 * π * R) :=
          setLIntegral_mono' measurableSet_Ioc (by
      intro θ hθ
      calc ∫⁻ z in ball 0 R, ‖Function.uncurry F (z, θ)‖ₑ
          ≤ ∫⁻ z in ball 0 R, K * ‖γ θ - z‖ₑ⁻¹ := by
            simp only [Function.uncurry_apply_pair, hF, enorm_mul]
            gcongr
            · rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
              exact ENNReal.ofReal_le_ofReal (norm_deriv_le_of_lipschitzWith hK θ)
            · exact enorm_inv_le_inv_enorm _
        _ = K * ∫⁻ z in ball 0 R, ‖γ θ - z‖ₑ⁻¹ :=
            lintegral_const_mul' _ _ ENNReal.coe_ne_top
        _ ≤ K * ENNReal.ofReal (4 * π * R) := by
            gcongr
            exact lintegral_ball_inv_norm_sub_le (le_trans (norm_nonneg _) (hγR 0 ⟨le_rfl, hpi⟩).le) (hγR θ ⟨hθ.1.le, hθ.2⟩).le)
      _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Ioc]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)
            ENNReal.ofReal_lt_top), intervalIntegral.integral_of_le hpi]
  have hin : ∀ θ ∈ Ioc 0 (2 * π), ∫ z in ball 0 R, F z θ =
      π * (conj (γ θ) * deriv γ θ) := by
    intro θ hθ
    rw [integral_const_mul, integral_ball_inv_sub (hγR θ ⟨hθ.1.le, hθ.2⟩)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hin, integral_const_mul]
  field_simp

/-- A Lipschitz curve has planar measure zero. -/
theorem volume_image_Icc_eq_zero (hK : LipschitzWith K γ) (a b : ℝ) :
    volume (γ '' Icc a b) = 0 := by
  set g : ℝ → ℝ × ℝ := Complex.equivRealProdCLM ∘ γ
  have h1 : μH[(2 : NNReal)] (g '' Icc a b) = 0 :=
    hausdorffMeasure_of_dimH_lt (by
    calc dimH (g '' Icc a b) ≤ dimH (Icc a b) := ((Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).lipschitz.comp hK).dimH_image_le _
      _ ≤ dimH univ := dimH_mono (subset_univ _)
      _ = 1 := by simp [Real.dimH_univ_eq_finrank]
      _ < _ := by norm_num)
  have himg : γ '' Icc a b = Complex.measurableEquivRealProd ⁻¹' (g '' Icc a b) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, h⟩
      exact ⟨t, ht, Complex.equivRealProd.injective h⟩
  simp_all [Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]

/-- Green's formula for a Lipschitz parametrization of the boundary of a bounded open set `Ω`
whose winding number is `σ` on `Ω` and `0` off `Ω̄`:
`∫₀^{2π} Im(conj γ · γ') = 2σ|Ω|`. -/
theorem integral_signedAreaDensity_of_winding {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (himage : γ '' Icc 0 (2 * π) = frontier Ω) (σ : ℝ)
    (hin : ∀ z ∈ Ω, windingNumber γ z = σ) (hout : ∀ z, z ∉ closure Ω → windingNumber γ z = 0) :
    ∫ θ in 0..(2 * π), signedAreaDensity γ θ = 2 * σ * (volume Ω).toReal := by
  obtain ⟨R, hR⟩ := hb.closure.subset_ball 0
  have hgreen := integral_ball_windingNumber hK (by
    intro θ hθ
    have  := himage ▸ mem_image_of_mem γ hθ
    exact mem_ball_zero_iff.mp (hR (frontier_subset_closure this)))
  have hae : ∀ᵐ z ∂(volume.restrict (ball 0 R)),
      windingNumber γ z = Ω.indicator (fun _ => (σ : ℂ)) z := by
    refine ae_restrict_of_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (himage ▸ volume_image_Icc_eq_zero hK 0 (2 * π))] with z hz
    by_cases hzΩ : z ∈ Ω
    · simp_all
    simp_all [frontier, hΩ.interior_eq]
  rw [integral_congr_ae hae, integral_indicator hΩ.measurableSet,
    Measure.restrict_restrict hΩ.measurableSet, inter_eq_self_of_subset_left (subset_closure.trans hR),
    setIntegral_const] at hgreen
  have hI : ∫ θ in 0..(2 * π), conj (γ θ) * deriv γ θ =
      2 * Complex.I * ((volume Ω).toReal * σ : ℝ) := by
    rw [measureReal_def] at hgreen
    rw [Complex.real_smul] at hgreen
    rw [Complex.ofReal_mul, hgreen]
    field_simp
  have hre : ∫ θ in 0..(2 * π), signedAreaDensity γ θ =
      (∫ θ in 0..(2 * π), conj (γ θ) * deriv γ θ).im := by
    rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm (by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn 
       hK.continuous.continuousOn
    refine (intervalIntegrable_const (c := M * K)).mono_fun' ((Complex.continuous_conj.comp hK.continuous).measurable.mul
        (measurable_deriv γ)).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun θ hθ => ?_)
    show ‖conj (γ θ) * deriv γ θ‖ ≤ M * K
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hM θ ⟨hθ.1.le, hθ.2⟩) (norm_deriv_le_of_lipschitzWith hK θ)
      (norm_nonneg _) ((norm_nonneg _).trans (hM θ ⟨hθ.1.le, hθ.2⟩)))]
    rfl
  rw [hre, hI]
  norm_num
  ring

end PolyaNeumann

end
