/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Assembly.KernelCauchy

/-! Good and bad cutoff masses of bounded nonnegative Borel tests and the cutoff `L¹` Cauchy estimate on a charge interval. -/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- Cutoff Wick mass of a nonnegative test restricted to an event in sample and point. -/
def wickEventMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : Measure ℂ) (Y : Ω → ℝ → ℂ → ℝ) (g r : ℝ) (E : Set (Ω × ℂ))
    (f : ℂ → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (f x) * admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
    Set.indicator E (fun _ => (1 : ℝ≥0∞)) (ω, x) ∂μ

theorem ennDist_measurable {α : Type*} [MeasurableSpace α] {F G : α → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) : Measurable (fun x => ennDist (F x) (G x)) :=
  (hF.sub hG).add (hG.sub hF)

/-- The full cutoff mass of a test on the compact chart `K`. -/
abbrev chartMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (K : Set ℂ) (Y : Ω → ℝ → ℂ → ℝ)
    (g r : ℝ) (f : ℂ → ℝ) (ω : Ω) : ℝ≥0∞ :=
  wickEventMass P ((logRegularizationReference U dens).restrict K) Y g r Set.univ f ω

section
variable {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
  (Y : Ω → ℝ → ℂ → ℝ)
  (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
include hY

/-- The Wick weight is jointly measurable in the sample and the point. -/
theorem admissibleLogWickWeight_measurable_joint (g ε : ℝ) :
    Measurable (fun q : Ω × ℂ => admissibleLogWickWeight P Y g ε q.2 q.1) := by
  have : Measurable (fun q : Ω × ℂ => gaussianVariance P (fun ω => Y ω ε q.2)) :=
    (admissibleLogRegularization_variance_measurable P U dens ε₀ Y hY ε).comp measurable_snd
  have := hY.measurableAtScale ε
  unfold admissibleLogWickWeight
  fun_prop

theorem wickEventMass_integrand_measurable (g r : ℝ) (E : Set (Ω × ℂ))
    (hE : MeasurableSet E) (f : ℂ → ℝ) (hf : Measurable f) :
    Measurable (fun q : Ω × ℂ => ENNReal.ofReal (f q.2) *
      admissibleLogWickWeight P Y g (Real.exp (-r)) q.2 q.1 *
      Set.indicator E (fun _ => (1 : ℝ≥0∞)) q) :=
  ((ENNReal.measurable_ofReal.comp (hf.comp measurable_snd)).mul
    (admissibleLogWickWeight_measurable_joint P U dens ε₀ Y hY g _)).mul
    (measurable_const.indicator hE)

theorem wickEventMass_measurable (μ : Measure ℂ) [SFinite μ]
    (g r : ℝ) (E : Set (Ω × ℂ)) (hE : MeasurableSet E) (f : ℂ → ℝ) (hf : Measurable f) :
    Measurable (wickEventMass P μ Y g r E f) :=
  (wickEventMass_integrand_measurable P U dens ε₀ Y hY g r E hE f hf).lintegral_prod_right'

/-- Full cutoff masses of tests with values in `[0, L]` are Cauchy in `L¹(P)` as both cutoffs
vanish, uniformly over such tests and charges in a compact interval admitting barrier
parameters. -/
theorem chartMass_L1_uniform_cauchy_interval
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (gLo gHi a η κ : ℝ) (hgLo : 0 < gLo) (hgLoHi : gLo ≤ gHi) (hga : gHi < a)
    (ha2 : a < 2 * gLo) (hη : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hκ2 : κ < 2)
    (hκexp : ∀ g ∈ Icc gLo gHi, g ^ 2 - ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤ κ)
    (L : ℝ) (hL : 0 ≤ L) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ r s : ℝ, R ≤ r → R ≤ s → ∀ g ∈ Icc gLo gHi, ∀ f : ℂ → ℝ, Measurable f →
      (∀ x, 0 ≤ f x) → (∀ x, f x ≤ L) →
      ∫⁻ ω, ennDist (chartMass P U dens K Y g r f ω) (chartMass P U dens K Y g s f ω) ∂P <
        ENNReal.ofReal ε := by
  let μK := (logRegularizationReference U dens).restrict K
  let τ : ℕ → ℝ≥0∞ := fun N =>
    ∑' j : ℕ, ENNReal.ofReal (Real.exp (-((a - gHi) ^ 2 * ((j + N : ℕ) : ℝ) / 16)))
  obtain ⟨Cb, hCb, htail⟩ := admissible_coarse_barrier_tail_rate P U dens ε₀ Y hY K hK hKU
  obtain ⟨Cv, hCv, hvarB⟩ := hY.coarseVarianceBound K hK hKU
  have hcoef : ENNReal.ofReal L * logRegularizationReference U dens K ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY K hK hKU)
  have hbadlim : Tendsto (fun N => ENNReal.ofReal L * logRegularizationReference U dens K * τ N)
      atTop (𝓝 0) := by
    simpa [τ] using ENNReal.Tendsto.const_mul
      (tendsto_compatible_mixed_double_root_barrier_tail_sum gHi a hga) (Or.inr hcoef)
  obtain ⟨N₁, hN₁⟩ := exists_natural_scale_after_covariance_errors (max Cb Cv + 1) 1 1 1 ε₀
    (by positivity) one_pos one_pos one_pos hY.cutoffPositive
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 * (gHi * Cb) / (a - gHi))
  obtain ⟨k₀, ⟨⟨hk₀N₁, hk₀N₂⟩, hk₀bad⟩⟩ := ((eventually_ge_atTop N₁).and (eventually_ge_atTop N₂)
    |>.and (hbadlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (by linarith : 0 < ε / 3))))).exists
  have hk₀N₁' : (N₁ : ℝ) ≤ k₀ := by exact_mod_cast hk₀N₁
  have hk₀N₂' : (N₂ : ℝ) ≤ k₀ := by exact_mod_cast hk₀N₂
  have hk₀cut : Real.exp (-(k₀ : ℝ)) ≤ ε₀ :=
    (Real.exp_le_exp.mpr (by linarith)).trans hN₁.1
  have hk₀C : Cb < (k₀ : ℝ) := by linarith [hN₁.2.1, le_max_left Cb Cv]
  have hk₀gap : gHi * Cb ≤ (a - gHi) * (k₀ : ℝ) / 2 := by
    linarith [(div_lt_iff₀ (sub_pos.mpr hga)).mp (hN₂.trans_le hk₀N₂')]
  have hvar (k : ℕ) (hk : k₀ ≤ k) (x : ℂ) (hx : x ∈ K) :
      1 ≤ gaussianVariance P (fun ω => Y ω (Real.exp (-(k : ℝ))) x) := by
    have hkc : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
    have := (abs_le.mp (hvarB k ((Real.exp_le_exp.mpr (by linarith)).trans hk₀cut) x hx)).1
    linarith [hN₁.2.1, le_max_right Cb Cv]
  -- Bad-mass upper bound at fixed `k₀`
  have hbad_le {g : ℝ} (r : ℝ) (hg : g ∈ Icc gLo gHi) {f : ℂ → ℝ} (hf : Measurable f)
      (hfL : ∀ x, f x ≤ L) :
      ∫⁻ ω, wickEventMass P μK Y g r (admissibleGrowingBarrierSet Y a k₀ r)ᶜ f ω ∂P ≤
        ENNReal.ofReal L * logRegularizationReference U dens K * τ k₀ := by
    have hAc := (admissibleGrowingBarrierSet_measurable P U dens ε₀ Y hY a k₀ r).compl
    unfold wickEventMass
    rw [lintegral_lintegral_swap
      (wickEventMass_integrand_measurable P U dens ε₀ Y hY g r _ hAc f hf).aemeasurable]
    refine (lintegral_mono_ae (g := fun _ => ENNReal.ofReal L * τ k₀)
      (ae_restrict_mem hK.measurableSet |>.mono fun x hx => ?_)).trans_eq ?_
    · have hw := admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY g (Real.exp (-r)) x
      have hωm : Measurable fun ω => admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)ᶜ (fun _ => (1 : ℝ≥0∞)) (ω, x) :=
        hw.mul ((measurable_const.indicator hAc).comp (measurable_id.prodMk (measurable_const (a := x))))
      rw [show (∫⁻ ω, ENNReal.ofReal (f x) * admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)ᶜ (fun _ => (1 : ℝ≥0∞)) (ω, x) ∂P) =
        ENNReal.ofReal (f x) * ∫⁻ ω, admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)ᶜ (fun _ => (1 : ℝ≥0∞)) (ω, x) ∂P by
        rw [← lintegral_const_mul _ hωm]; exact lintegral_congr fun _ => by ring]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (hfL x)) ?_
      let bad : ℕ → Ω → Prop := fun k ω =>
        k₀ ≤ k ∧ (k : ℝ) ≤ r ∧ a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x
      have hset (k : ℕ) : MeasurableSet {ω | bad k ω} := by
        by_cases hk : k₀ ≤ k ∧ (k : ℝ) ≤ r
        · rw [show {ω | bad k ω} = {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x} by ext ω; simp [bad, hk]]
          exact measurableSet_lt measurable_const (admissible_field_measurable_sample P U dens ε₀ Y hY _ x)
        · rw [Set.eq_empty_of_forall_notMem (s := {ω | bad k ω}) fun ω h => hk ⟨h.1, h.2.1⟩]
          exact MeasurableSet.empty
      have hev (ω : Ω) : Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)ᶜ
          (fun _ => (1 : ℝ≥0∞)) (ω, x) = Set.indicator {ω | ∃ k, bad k ω} (fun _ => 1) ω := by
        have hiff : (ω, x) ∈ (admissibleGrowingBarrierSet Y a k₀ r)ᶜ ↔ ω ∈ {ω | ∃ k, bad k ω} := by
          simp [admissibleGrowingBarrierSet, bad, and_assoc]
        by_cases h : (ω, x) ∈ (admissibleGrowingBarrierSet Y a k₀ r)ᶜ
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun h' => h (hiff.mpr h')]
      simp_rw [hev]
      refine (lintegral_mul_indicator_exists_le_tsum P _ bad
        fun k => (hw.mul (measurable_const.indicator (hset k))).aemeasurable).trans ?_
      let fn : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (Real.exp (-((a - gHi) ^ 2 * (k : ℝ) / 16)))
      have hterm (k : ℕ) : ∫⁻ ω, admissibleLogWickWeight P Y g (Real.exp (-r)) x ω *
          Set.indicator {ω | bad k ω} (fun _ => 1) ω ∂P ≤ Set.indicator {k | k₀ ≤ k} fn k := by
        by_cases hk : k₀ ≤ k ∧ (k : ℝ) ≤ r
        · rw [Set.indicator_of_mem (show k ∈ {k | k₀ ≤ k} from hk.1)]
          have hEq : {ω | bad k ω} = {ω | a * (k : ℝ) < Y ω (Real.exp (-(k : ℝ))) x} := by
            ext ω; simp [bad, hk]
          rw [hEq]
          have hk₀k : (k₀ : ℝ) ≤ k := by exact_mod_cast hk.1
          have hga' : g < a := hg.2.trans_lt hga
          refine (htail k ((Real.exp_le_exp.mpr (by linarith)).trans hk₀cut) (hk₀C.trans_le hk₀k)
            x hx _ (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith [hk.2])) g a
            (hgLo.trans_le hg.1) hga' ?_).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
          · have h1 := mul_le_mul_of_nonneg_right hg.2 hCb
            have h2 := mul_le_mul (by linarith [hg.2] : a - gHi ≤ a - g) hk₀k
              (Nat.cast_nonneg _) (by linarith)
            linarith
          · have hsq : (a - gHi) ^ 2 ≤ (a - g) ^ 2 :=
              pow_le_pow_left₀ (sub_pos.mpr hga).le (by linarith [hg.2]) 2
            linarith [mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        · have hEq : {ω | bad k ω} = ∅ := Set.eq_empty_of_forall_notMem fun ω h => hk ⟨h.1, h.2.1⟩
          simp [hEq]
      refine (ENNReal.tsum_le_tsum hterm).trans_eq ?_
      have hinj : Function.Injective fun j : ℕ => j + k₀ := fun i j h => by simpa using h
      rw [← hinj.tsum_eq fun k hk => ⟨k - k₀,
        Nat.sub_add_cancel (by by_contra h; exact hk (Set.indicator_of_notMem h fn))⟩]
      exact tsum_congr fun j => Set.indicator_of_mem (show k₀ ≤ j + k₀ by omega) fn
    · rw [lintegral_const, Measure.restrict_apply_univ]; ring
  -- Good-mass L¹ Cauchy estimate at fixed `k₀`
  set εg := ε / 3
  have hεg : 0 < εg := by positivity
  set ε' : ℝ := εg ^ 2 / (2 * (L ^ 2 + 1))
  obtain ⟨R₁, hR₁⟩ := growingPairKernel_L1_uniform_cauchy P U dens ε₀ Y hY K hK hKU gLo gHi a
    η κ hgLo hgLoHi hga ha2 hη hη1 hκ hκ2 hκexp k₀ hk₀cut hvar ε' (by positivity)
  obtain ⟨R₀, Maj, hMajm, hMajInt, hle⟩ := growingPairKernel_ae_le_integrable_majorant P U dens
    ε₀ Y hY K hK hKU gLo gHi a η κ hgLo hgLoHi hga ha2 hη hη1 hκ hκ2 hκexp k₀
  refine ⟨max R₀ R₁, fun r s hr hs g hg f hf hf0 hfL => ?_⟩
  set μ := chartPairMeasure U dens K
  let good (t : ℝ) := wickEventMass P μK Y g t (admissibleGrowingBarrierSet Y a k₀ t) f
  let bad (t : ℝ) := wickEventMass P μK Y g t (admissibleGrowingBarrierSet Y a k₀ t)ᶜ f
  have hbarr (t : ℝ) := admissibleGrowingBarrierSet_measurable P U dens ε₀ Y hY a k₀ t
  have hJm (t : ℝ) : Measurable (good t) := wickEventMass_measurable P U dens ε₀ Y hY _ g t _ (hbarr t) f hf
  have hBm (t : ℝ) : Measurable (bad t) := wickEventMass_measurable P U dens ε₀ Y hY _ g t _ (hbarr t).compl f hf
  have hKer (t t' : ℝ) := growingPairKernel_measurable P U dens ε₀ Y hY g a k₀ t t'
  have hff := (ENNReal.measurable_ofReal.comp (hf.comp measurable_fst)).mul
    (ENNReal.measurable_ofReal.comp (hf.comp measurable_snd))
  have hffL (p : ℂ × ℂ) : ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) ≤ ENNReal.ofReal L ^ 2 := by
    rw [pow_two]; exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hfL _)) (ENNReal.ofReal_le_ofReal (hfL _))
  have hmom (t t' : ℝ) : ∫⁻ ω, good t ω * good t' ω ∂P =
      ∫⁻ p, ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) *
        growingPairKernel P Y g a k₀ t t' p ∂μ := by
    let F₁ : Ω → ℂ → ℝ≥0∞ := fun ω x => ENNReal.ofReal (f x) *
      admissibleLogWickWeight P Y g (Real.exp (-t)) x ω *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ t) (fun _ => 1) (ω, x)
    let F₂ : Ω → ℂ → ℝ≥0∞ := fun ω x => ENNReal.ofReal (f x) *
      admissibleLogWickWeight P Y g (Real.exp (-t')) x ω *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ t') (fun _ => 1) (ω, x)
    have hFt := wickEventMass_integrand_measurable P U dens ε₀ Y hY g t _ (hbarr t) f hf
    have hFt' := wickEventMass_integrand_measurable P U dens ε₀ Y hY g t' _ (hbarr t') f hf
    have hH : Measurable fun q : Ω × (ℂ × ℂ) => F₁ q.1 q.2.1 * F₂ q.1 q.2.2 :=
      (hFt.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
        (hFt'.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
    refine (lintegral_congr (g := fun ω => ∫⁻ p, F₁ ω p.1 * F₂ ω p.2 ∂μ) fun ω => ?_).trans
      ((lintegral_lintegral_swap hH.aemeasurable).trans (lintegral_congr fun p => ?_))
    · exact (lintegral_prod_mul
        (hFt.comp (measurable_const.prodMk measurable_id)).aemeasurable
        (hFt'.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
    · have hmeasW : Measurable fun ω =>
          admissibleLogWickWeight P Y g (Real.exp (-t)) p.1 ω *
          admissibleLogWickWeight P Y g (Real.exp (-t')) p.2 ω *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ t) (fun _ => (1 : ℝ≥0∞)) (ω, p.1) *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ t') (fun _ => (1 : ℝ≥0∞)) (ω, p.2) :=
        ((((admissibleLogWickWeight_measurable_joint P U dens ε₀ Y hY g _).comp
            (measurable_id.prodMk measurable_const)).mul
          ((admissibleLogWickWeight_measurable_joint P U dens ε₀ Y hY g _).comp
            (measurable_id.prodMk measurable_const))).mul
          ((measurable_const.indicator (hbarr t)).comp (measurable_id.prodMk measurable_const))).mul
          ((measurable_const.indicator (hbarr t')).comp (measurable_id.prodMk measurable_const))
      show ∫⁻ ω, F₁ ω p.1 * F₂ ω p.2 ∂P = ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) *
        ∫⁻ ω, admissibleLogWickWeight P Y g (Real.exp (-t)) p.1 ω *
          admissibleLogWickWeight P Y g (Real.exp (-t')) p.2 ω *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ t) (fun _ => (1 : ℝ≥0∞)) (ω, p.1) *
          Set.indicator (admissibleGrowingBarrierSet Y a k₀ t') (fun _ => (1 : ℝ≥0∞)) (ω, p.2) ∂P
      rw [← lintegral_const_mul _ hmeasW]
      exact lintegral_congr fun _ => by dsimp [F₁, F₂]; ring
  have hcompare (t₁ t₂ : ℝ) : ∫⁻ ω, good t₁ ω * good t₂ ω ∂P ≤ ∫⁻ ω, good r ω * good s ω ∂P +
      ENNReal.ofReal L ^ 2 * ∫⁻ p, ennDist (growingPairKernel P Y g a k₀ t₁ t₂ p)
        (growingPairKernel P Y g a k₀ r s p) ∂μ := by
    have hrs : Measurable fun p : ℂ × ℂ => ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) *
        growingPairKernel P Y g a k₀ r s p := hff.mul (hKer r s)
    rw [hmom t₁ t₂, hmom r s, ← lintegral_const_mul _ (ennDist_measurable (hKer t₁ t₂) (hKer r s)),
      ← lintegral_add_left hrs]
    refine lintegral_mono fun p => ?_
    have hleD : growingPairKernel P Y g a k₀ t₁ t₂ p ≤ growingPairKernel P Y g a k₀ r s p +
        ennDist (growingPairKernel P Y g a k₀ t₁ t₂ p) (growingPairKernel P Y g a k₀ r s p) :=
      le_add_tsub.trans (add_le_add le_rfl le_self_add)
    exact (mul_le_mul_right hleD _).trans
      ((mul_add _ _ _).le.trans (add_le_add le_rfl (mul_le_mul_left (hffL p) _)))
  have hABfin : ∫⁻ ω, good r ω * good s ω ∂P ≠ ⊤ := by
    rw [hmom r s]
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal L ^ 2 * ∫⁻ p, Maj p ∂μ)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hMajInt) ?_
    rw [← lintegral_const_mul _ hMajm]
    exact lintegral_mono_ae ((hle r s ((le_max_left _ _).trans hr) ((le_max_left _ _).trans hs) g hg).mono
      fun p hp => mul_le_mul' (hffL p) hp)
  have hsq_le : ∫⁻ ω, ennDist (good r ω) (good s ω) ^ 2 ∂P ≤
      ENNReal.ofReal L ^ 2 * ∫⁻ p, ennDist (growingPairKernel P Y g a k₀ r r p)
        (growingPairKernel P Y g a k₀ r s p) ∂μ +
      ENNReal.ofReal L ^ 2 * ∫⁻ p, ennDist (growingPairKernel P Y g a k₀ s s p)
        (growingPairKernel P Y g a k₀ r s p) ∂μ := by
    have hpt (ω : Ω) : ennDist (good r ω) (good s ω) ^ 2 + 2 * (good r ω * good s ω) ≤
        good r ω * good r ω + good s ω * good s ω := by
      generalize good r ω = x, good s ω = y
      by_cases hx : x = ⊤; · subst hx; simp [pow_two]
      by_cases hy : y = ⊤; · subst hy; simp [pow_two]
      rcases le_total x y with h | h
      · obtain ⟨d, rfl⟩ : ∃ d, y = x + d := ⟨y - x, (add_tsub_cancel_of_le h).symm⟩
        have : ennDist x (x + d) = d := by
          unfold ennDist; rw [tsub_eq_zero_of_le le_self_add, zero_add, ENNReal.add_sub_cancel_left hx]
        rw [this]; exact le_of_eq (by ring)
      · obtain ⟨d, rfl⟩ : ∃ d, x = y + d := ⟨x - y, (add_tsub_cancel_of_le h).symm⟩
        have : ennDist (y + d) y = d := by
          unfold ennDist; rw [tsub_eq_zero_of_le le_self_add, add_zero, ENNReal.add_sub_cancel_left hy]
        rw [this]; exact le_of_eq (by ring)
    have hint := lintegral_mono (μ := P) hpt
    have hABm : Measurable fun ω => good r ω * good s ω := (hJm r).mul (hJm s)
    have hAAm : Measurable fun ω => good r ω * good r ω := (hJm r).mul (hJm r)
    rw [lintegral_add_right _ (hABm.const_mul 2), lintegral_add_left hAAm,
      lintegral_const_mul 2 hABm] at hint
    exact (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (by norm_num) hABfin)).mp
      (hint.trans ((add_le_add (hcompare r r) (hcompare s s)).trans_eq (by ring)))
  have hR₁r := (le_max_right R₀ R₁).trans hr
  have hR₁s := (le_max_right R₀ R₁).trans hs
  have hgood_lt : ∫⁻ ω, ennDist (good r ω) (good s ω) ∂P < ENNReal.ofReal εg := by
    have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
      (ennDist_measurable (hJm r) (hJm s)).aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
      ENNReal.rpow_two] at hcs
    have hcs' : ∫⁻ ω, ennDist (good r ω) (good s ω) ∂P ≤
        (∫⁻ ω, ennDist (good r ω) (good s ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) := by simpa using hcs
    refine hcs'.trans_lt ((ENNReal.rpow_lt_rpow (y := ENNReal.ofReal (εg ^ 2))
      (hsq_le.trans_lt ?_) (by norm_num)).trans_eq ?_)
    · refine (add_le_add (mul_le_mul_right (hR₁ r r r s hR₁r hR₁r hR₁r hR₁s g hg).le _)
        (mul_le_mul_right (hR₁ s s r s hR₁s hR₁s hR₁r hR₁s g hg).le _)).trans_lt ?_
      rw [← ENNReal.ofReal_pow hL, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      have hfrac : L ^ 2 * (2 * ε') < εg ^ 2 := by
        dsimp only [ε']
        rw [show L ^ 2 * (2 * (εg ^ 2 / (2 * (L ^ 2 + 1)))) = εg ^ 2 * (L ^ 2 / (L ^ 2 + 1)) by field_simp]
        exact (mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).mpr (by linarith))
          (by positivity)).trans_eq (mul_one _)
      linarith
    · rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
        Real.sqrt_sq hεg.le]
  -- Combine good and bad parts
  have hsplit (t : ℝ) (ω : Ω) : chartMass P U dens K Y g t f ω = good t ω + bad t ω := by
    have hm : Measurable fun x : ℂ => ENNReal.ofReal (f x) *
        admissibleLogWickWeight P Y g (Real.exp (-t)) x ω *
        Set.indicator (admissibleGrowingBarrierSet Y a k₀ t) (fun _ => 1) (ω, x) :=
      (wickEventMass_integrand_measurable P U dens ε₀ Y hY g t _ (hbarr t) f hf).comp
        (measurable_const.prodMk measurable_id)
    unfold chartMass wickEventMass
    dsimp only [good, bad, wickEventMass]
    rw [← lintegral_add_left hm]
    refine lintegral_congr fun x => ?_
    by_cases hx : (ω, x) ∈ admissibleGrowingBarrierSet Y a k₀ t
    · rw [Set.indicator_of_mem (Set.mem_univ _), Set.indicator_of_mem hx,
        Set.indicator_of_notMem (show (ω, x) ∉ (admissibleGrowingBarrierSet Y a k₀ t)ᶜ from fun h => h hx)]; ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (Set.mem_univ _),
        Set.indicator_of_mem (show (ω, x) ∈ (admissibleGrowingBarrierSet Y a k₀ t)ᶜ from hx)]; ring
  have hpt (ω : Ω) : ennDist (chartMass P U dens K Y g r f ω) (chartMass P U dens K Y g s f ω) ≤
      ennDist (good r ω) (good s ω) + (bad r ω + bad s ω) := by
    rw [hsplit r ω, hsplit s ω]
    unfold ennDist
    refine (add_le_add add_tsub_add_le_tsub_add_tsub add_tsub_add_le_tsub_add_tsub).trans ?_
    exact (by ring_nf : _ = (good r ω - good s ω + (good s ω - good r ω)) +
      (bad r ω - bad s ω + (bad s ω - bad r ω))).le.trans
      (add_le_add le_rfl (add_le_add tsub_le_self tsub_le_self))
  refine (lintegral_mono hpt).trans_lt ?_
  rw [lintegral_add_left (ennDist_measurable (hJm r) (hJm s)), lintegral_add_left (hBm r)]
  have hbad2 := add_le_add ((hbad_le r hg hf hfL).trans hk₀bad.le) ((hbad_le s hg hf hfL).trans hk₀bad.le)
  refine (ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hbad2) hgood_lt hbad2).trans_eq ?_
  rw [← ENNReal.ofReal_add hεg.le hεg.le, ← ENNReal.ofReal_add hεg.le (by positivity)]
  congr 1; dsimp [εg]; ring

end

end DOZZ.Assembly
