/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.BarrierCauchy

/-! Omitted coarse barriers of two separated roots for one admissible regularization: self-compatibility, a charge-uniform double-root barrier tail, and truncation of the growing barrier at a fixed level. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ) (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
include hY

/-- Every admissible regularization is compatible with itself. -/
theorem isCompatibleAdmissibleRegularizations_self
 :
    IsCompatibleAdmissibleRegularizations P U ε₀ ε₀ Y Y :=
  ⟨fun n q hq => by
      simpa only [ite_self] using hY.gaussian n (fun i => (q i).2)
        fun i => ⟨(hq i).1, (hq i).2.trans (min_le_left _ _)⟩,
   fun K hK hKU => by
      obtain ⟨C, hC, hcov⟩ := hY.covarianceBound K hK hKU
      exact ⟨C, hC, fun ε δ hε hεc hδ hδc x hx y hy => hcov ε δ hε hεc hδ hδc x hx y hy⟩,
   fun K hK hKU => by
      obtain ⟨C, hC, hmix⟩ := hY.coarseMixedBound K hK hKU
      exact ⟨C, hC, fun k hk ε hε hεk x hx => hmix k hk ε hε (hεk.trans (min_le_right _ _)) x hx⟩,
   fun _ _ _ _ _ _ hη => ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ _ _ => by simp [hη]⟩,
   fun _ _ _ _ _ _ hη => ⟨1, one_pos, fun _ _ _ _ _ _ _ => by simp [hη]⟩⟩

/-- The coarse field at a fixed point is measurable in the sample. -/
theorem admissible_field_measurable_sample (ε : ℝ) (x : ℂ) :
    Measurable (fun ω => Y ω ε x) :=
  (hY.measurableAtScale ε).comp (measurable_id.prodMk measurable_const)

/-- The Wick weight is measurable in the sample at each fixed point. -/
theorem admissibleLogWickWeight_measurable_sample (g ε : ℝ) (x : ℂ) :
    Measurable (fun ω => admissibleLogWickWeight P Y g ε x ω) := by
  have := admissible_field_measurable_sample P U dens ε₀ Y hY ε x
  unfold admissibleLogWickWeight; fun_prop


end

/-- Truncating the growing barrier of a separated root pair at level `m` costs at most the
summed omitted-barrier tails. The constant depends only on the regularization and chart. -/
theorem finiteBarrierPairKernel_le_growing_add_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k₀ m : ℕ, C < (m : ℝ) → Real.exp (-(m : ℝ)) ≤ ε₀ →
      ∀ r s : ℝ, (m : ℝ) ≤ r → (m : ℝ) ≤ s →
      ∀ x ∈ K, ∀ y ∈ K, ∀ L : ℝ, 0 < ‖x - y‖ → Real.log (1 / ‖x - y‖) ≤ L →
      ∀ g a : ℝ, 0 < g → g < a → g * (|L| + 2 * C) ≤ (a - g) * (m : ℝ) / 2 →
      compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m
          (Real.exp (-r)) (Real.exp (-s)) x y true true ≤
        compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel P Y Y g a k₀ r s x y
            true true +
          2 * (ENNReal.ofReal (Real.exp (g ^ 2 * (L + C))) *
            ∑' j : ℕ, ENNReal.ofReal
              (Real.exp (-((a - g) ^ 2 * ((j + (m + 1) : ℕ) : ℝ) / 16)))) := by
  have double_root_tail_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, C < (k : ℝ) → Real.exp (-(k : ℝ)) ≤ ε₀ →
        ∀ x ∈ K, ∀ y ∈ K, ∀ L : ℝ, 0 < ‖x - y‖ → Real.log (1 / ‖x - y‖) ≤ L →
        ∀ ε δ : ℝ, 0 < ε → ε ≤ Real.exp (-(k : ℝ)) → 0 < δ → δ ≤ ε₀ →
        ∀ g a : ℝ, 0 < g → g < a → g * (|L| + 2 * C) ≤ (a - g) * (k : ℝ) / 2 →
        ∫⁻ ω, admissibleLogWickWeight P Y g ε x ω * admissibleLogWickWeight P Y g δ y ω *
            Set.indicator {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x} (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
          ENNReal.ofReal (Real.exp (g ^ 2 * (L + C))) *
            ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16))) := by
    obtain ⟨Cv, hCv, hvar⟩ := hY.coarseVarianceBound K hK hKU
    obtain ⟨Cm, _, hmix⟩ := hY.coarseMixedBound K hK hKU
    obtain ⟨Cc, _, hcov⟩ := hY.covarianceBound K hK hKU
    let C := max Cv (max Cm Cc)
    have hCv' : Cv ≤ C := le_max_left _ _
    have hCm' : Cm ≤ C := (le_max_left _ _).trans (le_max_right _ _)
    have hCc' : Cc ≤ C := (le_max_right _ _).trans (le_max_right _ _)
    refine ⟨C, hCv.trans hCv', fun k hkC hkcut x hx y hy L hxy hL ε δ hε hεk hδ hδcut g a hg hga hgap => ?_⟩
    have hεcut := hεk.trans hkcut
    have hkpos := lt_of_le_of_lt (hCv.trans hCv') hkC
    let q : Fin 3 → ℝ × ℂ := fun i => if i = 0 then (Real.exp (-(k : ℝ)), x) else if i = 1 then (ε, x) else (δ, y)
    let V : Ω → Fin 3 → ℝ := fun ω i => Y ω (q i).1 (q i).2
    have hV : IsCenteredJointlyGaussian P V := hY.gaussian 3 q fun i => by
      fin_cases i <;> [exact ⟨Real.exp_pos _, hkcut⟩; exact ⟨hε, hεcut⟩; exact ⟨hδ, hδcut⟩]
    have hV0 : (fun ω => V ω 0) = fun ω => Y ω (Real.exp (-(k : ℝ))) x := rfl
    have hV1 : (fun ω => V ω 1) = fun ω => Y ω ε x := rfl
    have hV2 : (fun ω => V ω 2) = fun ω => Y ω δ y := rfl
    have hvarV : |gaussianVariance P (fun ω => V ω 0) - (k : ℝ)| ≤ C := by
      rw [hV0]; exact (hvar k hkcut x hx).trans hCv'
    have hcov01 : gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω 1) ≤ (k : ℝ) + C := by
      rw [hV0, hV1]; linarith [(abs_le.mp ((hmix k hkcut ε hε hεk x hx).trans hCm')).2]
    have hlogmax (u v : ℝ) : Real.log (1 / max ‖x - y‖ (max u v)) ≤ L :=
      (Real.log_le_log (one_div_pos.2 (lt_of_lt_of_le hxy (le_max_left _ _)))
        (one_div_le_one_div_of_le hxy (le_max_left _ _))).trans hL
    have hcov02 : gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω 2) ≤ L + C := by
      rw [hV0, hV2]
      linarith [(abs_le.mp ((hcov _ δ (Real.exp_pos _) hkcut hδ hδcut x hx y hy).trans hCc')).2,
        hlogmax (Real.exp (-(k : ℝ))) δ]
    have hcov12 : gaussianCovariance P (fun ω => V ω 1) (fun ω => V ω 2) ≤ L + C := by
      rw [hV1, hV2]
      linarith [(abs_le.mp ((hcov ε δ hε hεcut hδ hδcut x hx y hy).trans hCc')).2, hlogmax ε δ]
    let B (ω : Ω) := Set.indicator {ω | a * (k : ℝ) < V ω 0} (fun _ => (1 : ℝ≥0∞)) ω
    let tilt : Fin 3 → ℝ := twoRootTilt 1 2 g
    have hmUpper : (∑ j : Fin 3, gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω j) * tilt j) ≤
        g * (k : ℝ) + g * (|L| + 2 * C) := by
      have hm : (∑ j : Fin 3, gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω j) * tilt j) =
          g * gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω 1) +
            g * gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω 2) := by
        simp [Fin.sum_univ_three, tilt, twoRootTilt]; ring
      rw [hm]
      linarith [mul_le_mul_of_nonneg_left hcov01 hg.le, mul_le_mul_of_nonneg_left hcov02 hg.le,
        mul_le_mul_of_nonneg_left (le_abs_self L) hg.le]
    have hgapStrict : (∑ j : Fin 3, gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω j) * tilt j) < a * (k : ℝ) := by
      have : 0 < (a - g) * (k : ℝ) / 2 := by have := sub_pos.2 hga; positivity
      linarith
    have hvpos : 0 < gaussianVariance P (fun ω => V ω 0) := by linarith [(abs_le.mp hvarV).1]
    have hvle : gaussianVariance P (fun ω => V ω 0) ≤ 2 * (k : ℝ) := by linarith [(abs_le.mp hvarV).2]
    have hident := finite_gaussian_two_root_wick_tilt_integral_identity P V 1 2 (by decide) g B
    have hrate := gaussian_barrier_tail_rate a g (g * (|L| + 2 * C))
      (∑ j : Fin 3, gaussianCovariance P (fun ω => V ω 0) (fun ω => V ω j) * tilt j)
      (gaussianVariance P (fun ω => V ω 0)) (k : ℝ) hga hkpos hgap hmUpper hvpos hvle
    change ∫⁻ ω, ENNReal.ofReal (Real.exp (g * V ω 1 - g ^ 2 / 2 * gaussianVariance P (fun ω => V ω 1))) *
        ENNReal.ofReal (Real.exp (g * V ω 2 - g ^ 2 / 2 * gaussianVariance P (fun ω => V ω 2))) * B ω ∂P ≤ _
    rw [hident]
    exact mul_le_mul'
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hcov12 (sq_nonneg g))))
      ((finite_gaussian_tilt_barrier_tail_bound P V hV tilt 0 (a * (k : ℝ)) hgapStrict hvpos).trans
        (ENNReal.ofReal_le_ofReal (by simpa using hrate)))
  classical
  obtain ⟨C, hC, htail⟩ := double_root_tail_uniform
  refine ⟨C, hC, fun k₀ m hmC hmcut r s hmr hms x hx y hy L hxy hL g a hg hga hgap => ?_⟩
  let omitted (t : ℝ) (z : ℂ) : Set Ω :=
    {ω | ∃ k : ℕ, m < k ∧ (k : ℝ) ≤ t ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z}
  have hbad_meas (t : ℝ) (z : ℂ) (k : ℕ) :
      MeasurableSet {ω | m < k ∧ (k : ℝ) ≤ t ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z} := by
    by_cases hk : m < k ∧ (k : ℝ) ≤ t
    · rw [show {ω | m < k ∧ (k : ℝ) ≤ t ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z} =
          {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z} by ext; simp [hk]]
      exact measurableSet_lt measurable_const (admissible_field_measurable_sample P U dens ε₀ Y hY _ z)
    · rw [show {ω | m < k ∧ (k : ℝ) ≤ t ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z} = ∅ from
          Set.eq_empty_of_forall_notMem fun _ h => hk ⟨h.1, h.2.1⟩]
      exact MeasurableSet.empty
  have ho_meas (t : ℝ) (z : ℂ) : MeasurableSet (omitted t z) := by
    rw [show omitted t z = ⋃ k : ℕ, {ω | m < k ∧ (k : ℝ) ≤ t ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z} by ext; simp [omitted]]
    exact MeasurableSet.iUnion (hbad_meas t z)
  let c := ENNReal.ofReal (Real.exp (g ^ 2 * (L + C)))
  let f (k : ℕ) := ENNReal.ofReal (Real.exp (-((a - g) ^ 2 * (k : ℝ) / 16)))
  have homit_bd {u v : ℝ} {z w : ℂ} (hmu : (m : ℝ) ≤ u) (hmv : (m : ℝ) ≤ v)
      (hz : z ∈ K) (hw : w ∈ K) (hzw : 0 < ‖z - w‖) (hLzw : Real.log (1 / ‖z - w‖) ≤ L) :
      ∫⁻ ω, admissibleLogWickWeight P Y g (Real.exp (-u)) z ω *
          admissibleLogWickWeight P Y g (Real.exp (-v)) w ω *
          Set.indicator (omitted u z) (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
        c * ∑' j : ℕ, f (j + (m + 1)) := by
    let W (ω : Ω) := admissibleLogWickWeight P Y g (Real.exp (-u)) z ω *
      admissibleLogWickWeight P Y g (Real.exp (-v)) w ω
    have hWm : Measurable W := (admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY g _ z).mul
      (admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY g _ w)
    have h1 := lintegral_mul_indicator_exists_le_tsum P W
      (fun k ω => m < k ∧ (k : ℝ) ≤ u ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z)
      fun k => (hWm.mul (measurable_const.indicator (hbad_meas u z k))).aemeasurable
    have h2 : (∑' k : ℕ, ∫⁻ ω, W ω * Set.indicator
        {ω | m < k ∧ (k : ℝ) ≤ u ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z} (fun _ => (1 : ℝ≥0∞)) ω ∂P) ≤
        ∑' k : ℕ, Set.indicator {k : ℕ | m < k} (fun k => c * f k) k :=
      ENNReal.tsum_le_tsum fun k => by
        by_cases hk : m < k ∧ (k : ℝ) ≤ u
        · rw [show {ω | m < k ∧ (k : ℝ) ≤ u ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z} =
              {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z} by ext; simp [hk],
            Set.indicator_of_mem (show k ∈ {k : ℕ | m < k} from hk.1)]
          have hkm : (m : ℝ) ≤ k := mod_cast hk.1.le
          exact htail k (lt_of_lt_of_le hmC hkm) ((Real.exp_le_exp.2 (by linarith)).trans hmcut)
            z hz w hw L hzw hLzw (Real.exp (-u)) (Real.exp (-v))
            (Real.exp_pos _) (Real.exp_le_exp.2 (by linarith [hk.2]))
            (Real.exp_pos _) ((Real.exp_le_exp.2 (by linarith)).trans hmcut) g a hg hga
            (by linarith [mul_le_mul_of_nonneg_left hkm (sub_pos.2 hga).le])
        · rw [show {ω | m < k ∧ (k : ℝ) ≤ u ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) z} = ∅ from
              Set.eq_empty_of_forall_notMem fun _ h => hk ⟨h.1, h.2.1⟩]; simp
    have hinj : Function.Injective (fun j : ℕ => j + (m + 1)) := fun _ _ h => by simpa using h
    have hsupp : Function.support (Set.indicator {k : ℕ | m < k} fun k => c * f k) ⊆
        Set.range (fun j : ℕ => j + (m + 1)) := fun k hk => by
      have hmk : m < k := by by_contra h; exact hk (Set.indicator_of_notMem h _)
      exact ⟨k - (m + 1), by dsimp; omega⟩
    refine (h1.trans h2).trans_eq ?_
    rw [← hinj.tsum_eq hsupp, ← ENNReal.tsum_mul_left]
    exact tsum_congr fun j => Set.indicator_of_mem (show m < j + (m + 1) by omega) _
  let Wx (ω : Ω) := admissibleLogWickWeight P Y g (Real.exp (-r)) x ω
  let Wy (ω : Ω) := admissibleLogWickWeight P Y g (Real.exp (-s)) y ω
  have hWx := admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY g (Real.exp (-r)) x
  have hWy := admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY g (Real.exp (-s)) y
  have hbx := homit_bd hmr hms hx hy hxy hL
  have hby : ∫⁻ ω, Wx ω * Wy ω * Set.indicator (omitted s y) (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤
      c * ∑' j : ℕ, f (j + (m + 1)) := by
    refine (le_of_eq (lintegral_congr fun ω => by dsimp [Wx, Wy]; ring)).trans
      (homit_bd hms hmr hy hx (by rwa [norm_sub_rev]) (by rwa [norm_sub_rev]))
  have hpt (ω : Ω) :
      admissibleLogWickWeight P (if true = true then Y else Y) g (Real.exp (-r)) x ω *
          admissibleLogWickWeight P (if true = true then Y else Y) g (Real.exp (-s)) y ω *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ)) (fun _ => (1 : ℝ≥0∞)) (ω, x) *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ)) (fun _ => (1 : ℝ≥0∞)) (ω, y) ≤
        (admissibleLogWickWeight P (if true = true then Y else Y) g (Real.exp (-r)) x ω *
            admissibleLogWickWeight P (if true = true then Y else Y) g (Real.exp (-s)) y ω *
            Set.indicator (admissibleGrowingBarrierSet Y a k₀ r) (fun _ => (1 : ℝ≥0∞)) (ω, x) *
            Set.indicator (admissibleGrowingBarrierSet Y a k₀ s) (fun _ => (1 : ℝ≥0∞)) (ω, y) +
          Wx ω * Wy ω * Set.indicator (omitted r x) (fun _ => (1 : ℝ≥0∞)) ω) +
          Wx ω * Wy ω * Set.indicator (omitted s y) (fun _ => (1 : ℝ≥0∞)) ω := by
    have hI : Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ)) (fun _ => (1 : ℝ≥0∞)) (ω, x) *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ (m : ℝ)) (fun _ => (1 : ℝ≥0∞)) (ω, y) ≤
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ r) (fun _ => (1 : ℝ≥0∞)) (ω, x) *
            Set.indicator (admissibleGrowingBarrierSet Y a k₀ s) (fun _ => (1 : ℝ≥0∞)) (ω, y) +
          Set.indicator (omitted r x) (fun _ => (1 : ℝ≥0∞)) ω +
          Set.indicator (omitted s y) (fun _ => (1 : ℝ≥0∞)) ω := by
      by_cases hmx : (ω, x) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ)
      · by_cases hmy : (ω, y) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ)
        · rw [Set.indicator_of_mem hmx, Set.indicator_of_mem hmy, one_mul]
          by_cases hox : ω ∈ omitted r x
          · rw [Set.indicator_of_mem hox]; exact le_add_self.trans le_self_add
          · by_cases hoy : ω ∈ omitted s y
            · rw [Set.indicator_of_mem hoy]; exact le_add_self
            · have hmem {t : ℝ} {z : ℂ} (hmz : (ω, z) ∈ admissibleGrowingBarrierSet Y a k₀ (m : ℝ))
                  (hoz : ω ∉ omitted t z) : (ω, z) ∈ admissibleGrowingBarrierSet Y a k₀ t := fun k hk0 hkt => by
                by_cases hkm : k ≤ m
                · exact hmz k hk0 (mod_cast hkm)
                · by_contra hb; exact hoz ⟨k, Nat.lt_of_not_le hkm, hkt, lt_of_not_ge hb⟩
              rw [Set.indicator_of_mem (hmem hmx hox), Set.indicator_of_mem (hmem hmy hoy), one_mul]
              exact le_self_add.trans le_self_add
        · simp [Set.indicator_of_notMem hmy]
      · simp [Set.indicator_of_notMem hmx]
    simp only [ite_self, Wx, Wy]
    calc Wx ω * Wy ω * _ * _ = Wx ω * Wy ω * (_ * _) := by ring
      _ ≤ Wx ω * Wy ω * (_ + _ + _) := mul_le_mul_right hI _
      _ = _ := by ring
  have hm1 : Measurable fun ω => Wx ω * Wy ω * Set.indicator (omitted s y) (fun _ => (1 : ℝ≥0∞)) ω :=
    (hWx.mul hWy).mul (measurable_const.indicator (ho_meas s y))
  have hm2 : Measurable fun ω => Wx ω * Wy ω * Set.indicator (omitted r x) (fun _ => (1 : ℝ≥0∞)) ω :=
    (hWx.mul hWy).mul (measurable_const.indicator (ho_meas r x))
  calc compatibleAdmissibleSelectedFiniteBarrierPairKernel P Y Y g a k₀ m (Real.exp (-r)) (Real.exp (-s)) x y true true
    _ ≤ _ := lintegral_mono hpt
    _ = compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel P Y Y g a k₀ r s x y true true +
          (∫⁻ ω, Wx ω * Wy ω * Set.indicator (omitted r x) (fun _ => (1 : ℝ≥0∞)) ω ∂P) +
          ∫⁻ ω, Wx ω * Wy ω * Set.indicator (omitted s y) (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
        rw [lintegral_add_right _ hm1, lintegral_add_right _ hm2]; rfl
    _ ≤ compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel P Y Y g a k₀ r s x y true true +
          c * ∑' j : ℕ, f (j + (m + 1)) + c * ∑' j : ℕ, f (j + (m + 1)) := add_le_add (add_le_add le_rfl hbx) hby
    _ = _ := by ring

end DOZZ.Assembly
