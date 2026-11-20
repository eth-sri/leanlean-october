/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CutoffUIBadLimit
public import DOZZ.GMC.SharpMoments.CoulombCutoffLimit
public import DOZZ.GMC.SharpMoments.GoodPart
public import DOZZ.GMC.SharpMoments.CutoffUIConvergenceAux
public import DOZZ.GMC.SharpMoments.CutoffUIMoment

/-! # Convergence in probability of regularized Coulomb masses, uniformly on compact sets

Split the plane into a bad region, small disks about the roots and the exterior of a large disk,
and its complement. The bad parts of the regularized and of the limiting Coulomb masses have
small moments uniformly in the parameters and in the cutoff. On the complement the regularized
weight converges uniformly to the Coulomb weight, and the bounded Coulomb weight integrated
against the cutoff chaos converges in `L¹`, uniformly in the parameters, by the uniform `L¹`
convergence of cutoff chaos over compact couplings. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Admissible compact parameter sets carry a uniform small admissible order: a positive order
admissible at every root charge, at its positive part, and at the positive part of the charge at
infinity, together with a uniform root separation. -/
theorem cutoffUI_uniform_order
    {N : ℕ} (S : Set (CoulombParameters N)) (hS : IsCompact S)
    (hadm : ∀ c ∈ S, CoulombCutoffConfiguration c) :
    ∃ tst : ℝ, 0 < tst ∧
      (∀ c ∈ S, ∀ k, 0 < weightedCutoffSlack (c.1, c.2.2.1 k, tst)) ∧
      (∀ c ∈ S, ∀ k, 0 < weightedCutoffSlack (c.1, max (c.2.2.1 k) 0, tst)) ∧
      (∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, tst)) ∧
      ∃ ρs : ℝ, 0 < ρs ∧ ρs ≤ 1 ∧ ∀ c ∈ S, ∀ j k, j ≠ k → 2 * ρs ≤ ‖c.2.1 j - c.2.1 k‖ := by
  obtain ⟨ε, hε, hε1, h, hsep⟩ := exists_cutoffUI_slack (s := fun _ => 0) hS continuousOn_const hadm
    (fun c hc => by have := (hadm c hc).1; positivity)
    (fun c hc k => mul_pos (div_pos two_pos (hadm c hc).1) (sub_pos.mpr ((hadm c hc).2.2.2.1 k)))
    (fun c hc => mul_pos (div_pos two_pos (hadm c hc).1) (sub_pos.mpr (hadm c hc).2.2.2.2))
  simp only [max_self, zero_add] at h
  have hh c hc := h c hc (ε / 2) (half_pos hε) (by linarith)
  exact ⟨ε / 2, half_pos hε, fun c hc => (hh c hc).1, fun c hc => (hh c hc).2.1,
    fun c hc => (hh c hc).2.2, ε, hε, hε1, hsep⟩

/-- Regularized Coulomb masses converge in probability to the Coulomb masses of the limiting
chaos, uniformly over compact admissible parameter sets: the convergence half of the
extended-Seiberg cutoff uniform integrability. -/
theorem regularizedCoulombMass_tendstoInProbability_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (partition : GMCChartPartition)
    (Mfam : ℝ → Ω → Measure ℂ)
    (hMfam : ∀ γ ∈ Set.Ioo (0 : ℝ) 2, IsGMCOf P X γ (Mfam γ)) {N : ℕ}
    (S : Set (CoulombParameters N)) (hS : IsCompact S)
    (hadm : ∀ c ∈ S, CoulombCutoffConfiguration c) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun r : ℝ => ⨆ c ∈ S, P {ω | ε ≤ edist
        (regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω).toReal
        (coulombMass c.1 (Mfam c.1 ω) c.2.2.1 c.2.1 c.2.2.2).toReal})
      atTop (𝓝 0) := by
  classical
  let := hX.1
  intro ε hε
  obtain ⟨tst, htst, hroot, hrootp, hinf, ρs, hρs, hρs1, hsep⟩ := cutoffUI_uniform_order S hS hadm
  obtain ⟨ρ1, hρ1, A1, hA1, κ1, hκ1, hbad1⟩ := cutoffUI_bad_cutoff_moment_le P X hX Xc hXc
    partition N S hS htst hroot hinf hρs hρs1 hsep
  obtain ⟨ρ2, hρ2, A2, hA2, κ2, hκ2, hbad2⟩ := cutoffUI_bad_limit_moment_le P X hX Xc hXc Mfam
    hMfam N S hS htst hrootp hinf hρs hρs1 hsep
  obtain ⟨Zs, E, hZs, hE, hZc, -, hEα, hEinf⟩ := compact_coulomb_bounds hS
  let Γ := Prod.fst '' S
  have hΓ : IsCompact Γ := hS.image continuous_fst
  have hΓ2 : Γ ⊆ Set.Ioo 0 2 := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨(hadm c hc).1, (hadm c hc).2.1⟩
  let e := (min ε 1).toReal
  have hmin : min ε 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have he : 0 < e := ENNReal.toReal_pos (lt_min hε one_pos).ne' hmin
  have hεe : ENNReal.ofReal e ≤ ε := by rw [ENNReal.ofReal_toReal hmin]; exact min_le_left _ _
  let a := ENNReal.ofReal (e / 3)
  have ha : 0 < a := ENNReal.ofReal_pos.mpr (by positivity)
  refine ENNReal.tendsto_atTop_zero.mpr fun θ hθ => ?_
  have hsmall (A : ℝ≥0∞) (hA : A ≠ ⊤) {κ : ℝ} (hκ : 0 < κ) :
      ∀ᶠ ρ : ℝ in 𝓝[>] 0, A * ENNReal.ofReal (ρ ^ κ) < θ / 3 * a ^ tst := by
    have h := (Real.continuousAt_rpow_const 0 κ (Or.inr hκ.le)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rw [Real.zero_rpow hκ.ne'] at h
    have h' := ENNReal.Tendsto.const_mul (a := A) (ENNReal.tendsto_ofReal h) (Or.inr hA)
    simp only [ENNReal.ofReal_zero, mul_zero] at h'
    exact h'.eventually (Iio_mem_nhds (ENNReal.mul_pos (ENNReal.div_pos hθ.ne' (by norm_num)).ne'
      (ENNReal.rpow_pos ha ENNReal.ofReal_ne_top).ne'))
  obtain ⟨ρ, hb₁, hb₂, hρ, hρ'⟩ := ((hsmall A1 hA1.ne hκ1).and ((hsmall A2 hA2.ne hκ2).and
    (Ioo_mem_nhdsGT (lt_min hρ1 (lt_min hρ2 one_pos))))).exists
  obtain ⟨hρ₁, hρ₂, hρ₃⟩ := lt_min_iff.mp hρ' |>.imp_right lt_min_iff.mp
  obtain ⟨L, hL₀, hL⟩ := coulombCutoffWeight_sub_coulombWeight_le partition N hZs hE hρ hρ₃.le
  let U : ℝ → ℝ≥0∞ := fun r => ⨆ γ ∈ Γ, ⨆ (f : ℂ → ℝ) (_ : Measurable f)
      (_ : ∀ x, |f x| ≤ L) (_ : ∀ x ∉ closedBall (0 : ℂ) (1 / ρ), f x = 0),
      ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂regularizedGMC P Xc γ r ω - ∫ x, f x ∂Mfam γ ω| ∂P
  have hU : Tendsto U atTop (𝓝 0) := equatorGFF_GMC_uniform_L1 P X hX Xc hXc Mfam hMfam Γ hΓ hΓ2
    _ (isCompact_closedBall _ _) L
  have hL1 := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul L)
  rw [mul_zero] at hL1
  have hT := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hL1) (Or.inr gmcReferenceMeasure_univ_ne_top)
  simp only [ENNReal.ofReal_zero, zero_mul] at hT
  have ht : Tendsto (fun r => ENNReal.ofReal (L * Real.exp (-r)) * gmcReferenceMeasure Set.univ + U r)
      atTop (𝓝 0) := by simpa using hT.add hU
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds
    (ENNReal.mul_pos (ENNReal.div_pos hθ.ne' (by norm_num)).ne' ha.ne' : 0 < θ / 3 * a)))
  refine ⟨max r₀ (Real.log (1 / ρ)), fun r hr => iSup₂_le fun c hc => ?_⟩
  have hrlog := (le_max_right r₀ (Real.log (1 / ρ))).trans hr
  have hrnon : 0 ≤ r := (Real.log_nonneg (by rw [le_div_iff₀ hρ]; simpa using hρ₃.le)).trans hrlog
  obtain ⟨hγ0, hγ2, -, -, -⟩ := hadm c hc
  let M := Mfam c.1
  let Mr := regularizedGMC P Xc c.1 r
  have hmM : IsGMCOf P X c.1 M := hMfam c.1 ⟨hγ0, hγ2⟩
  have hmMr : Measurable Mr := regularizedGMC_measurable P X hX Xc hXc c.1 r
  let Bad := coulombBadRegion c.2.1 ρ
  let Good := Badᶜ \ {0}
  have hBad : MeasurableSet Bad := measurableSet_coulombBadRegion _ _
  have hGood : MeasurableSet Good := hBad.compl.diff (measurableSet_singleton _)
  let G := coulombCutoffWeight partition c.1 c.2.2.1 c.2.1 c.2.2.2 r
  let F := coulombWeight c.1 c.2.2.1 c.2.1 c.2.2.2
  have hG : Measurable G := measurable_coulombCutoffWeight _ _ _ _ _ _
  have hF : Measurable F := measurable_coulombWeight _ _ _ _
  let Br := fun ω => ∫⁻ x in Bad, G x ∂Mr ω
  let B := fun ω => ∫⁻ x in Bad, F x ∂M ω
  let Gr := fun ω => ∫⁻ x in Good, G x ∂Mr ω
  let Gl := fun ω => ∫⁻ x in Good, F x ∂M ω
  have hm₁ : ∫⁻ ω, Br ω ^ tst ∂P ≤ A1 * ENNReal.ofReal (ρ ^ κ1) :=
    hbad1 c hc ρ hρ hρ₁.le r hrlog
  have hm₂ : ∫⁻ ω, B ω ^ tst ∂P ≤ A2 * ENNReal.ofReal (ρ ^ κ2) :=
    hbad2 c hc ρ hρ hρ₂.le
  have hMrmeas (s : Set ℂ) (hs : MeasurableSet s) :
      AEMeasurable (fun ω => ∫⁻ x in s, G x ∂Mr ω) P := by
    simpa only [Function.comp_def, lintegral_indicator hs] using
      ((Measure.measurable_lintegral (hG.indicator hs)).comp hmMr).aemeasurable
  have hMmeas s hs := gmc_setLIntegral_aemeasurable P X hX c.1 hγ0 hγ2 M hmM F hF s hs
  have hgeom x (hx : x ∈ Good) := (mem_coulombBadRegion_compl c.2.1 ρ x).mp hx.1
  have hbulk x (hx : x ∈ Good) := hL c.1 c.2.2.1 c.2.1 c.2.2.2 r x hrnon
    (hZc c hc) (hEα c hc) (hEinf c hc) (hgeom x hx).1 (hgeom x hx).2 hx.2
  have hfin := regularizedGMC_finite_ae P X hX Xc hXc c.1 r
  have hgr : ∀ᵐ ω ∂P, Gr ω ≠ ⊤ := hfin.mono fun ω _ =>
    setLIntegral_ne_top_of_bound hGood fun x hx => (hbulk x hx).1
  have hgl : ∀ᵐ ω ∂P, Gl ω ≠ ⊤ := Eventually.of_forall fun ω => by
    have := hmM.1 ω
    exact setLIntegral_ne_top_of_bound hGood fun x hx => (hbulk x hx).2.1
  have hsplit {m : Measure ℂ} (h0 : m {0} = 0) (f : ℂ → ℝ≥0∞) :
      (∫⁻ x, f x ∂m) = (∫⁻ x in Bad, f x ∂m) + ∫⁻ x in Good, f x ∂m := by
    have h : m.restrict Good = m.restrict Badᶜ := by
      apply Measure.restrict_congr_set
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with x hx
      simp [Good, hx]
    rw [h, lintegral_add_compl _ hBad]
  have hZr : ∀ᵐ ω ∂P, regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω = Br ω + Gr ω :=
    Eventually.of_forall fun ω => by
      rw [regularizedCoulombMass_eq_lintegral P X hX Xc hXc]
      exact hsplit (regularizedGMC_singleton_eq_zero P Xc c.1 r ω 0) G
  have hZ : ∀ᵐ ω ∂P, coulombMass c.1 (M ω) c.2.2.1 c.2.1 c.2.2.2 = B ω + Gl ω := by
    filter_upwards [gmc_singleton_mass_eq_zero_ae P X hX c.1 hγ0 hγ2 M hmM 0] with ω hω
    rw [coulombMass_eq_lintegral_coulombWeight]
    exact hsplit hω F
  let d := fun ω => ENNReal.ofReal |(Gr ω).toReal - (Gl ω).toReal|
  have hd : AEMeasurable d P := by
    have hr' : AEMeasurable Gr P := hMrmeas _ hGood
    have hl' : AEMeasurable Gl P := hMmeas _ hGood
    fun_prop
  refine (prob_edist_le_of_split P _ _ Br B Gr Gl hZr hZ hgr hgl
    (hMrmeas _ hBad) (hMmeas _ hBad) hd he hεe htst
      (hm₁.trans_lt (ENNReal.mul_lt_top hA1 ENNReal.ofReal_lt_top))
      (hm₂.trans_lt (ENNReal.mul_lt_top hA2 ENNReal.ofReal_lt_top))).trans ?_
  let f : ℂ → ℝ := Good.indicator fun x => (F x).toReal
  have hfm : Measurable f := (ENNReal.measurable_toReal.comp hF).indicator hGood
  have hfb x : |f x| ≤ L := by
    by_cases hx : x ∈ Good
    · simpa [f, hx, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.toReal_ofReal hL₀] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbulk x hx).2.1
    · simp [f, hx, hL₀]
  have hfK x (hx : x ∉ closedBall (0 : ℂ) (1 / ρ)) : f x = 0 := by
    apply Set.indicator_of_notMem
    exact fun h => hx (by simpa using (hgeom x h).1)
  have hgood : ∫⁻ ω, d ω ∂P ≤ ENNReal.ofReal (L * Real.exp (-r)) * gmcReferenceMeasure Set.univ + U r := by
    let l := ENNReal.ofReal (L * Real.exp (-r))
    let b := fun ω => ENNReal.ofReal |∫ x, f x ∂Mr ω - ∫ x, f x ∂M ω|
    have hpoint : ∀ᵐ ω ∂P, d ω ≤ l * Mr ω Good + b ω := by
      filter_upwards [hfin] with ω hω
      have := hmM.1 ω
      exact goodPart_ofReal_abs_le _ _ Good hGood G F hG hF L _ (by positivity) hbulk
    have hmass : Measurable (fun ω => Mr ω Good) := (Measure.measurable_coe hGood).comp hmMr
    have hlm : Measurable (fun ω => l * Mr ω Good) := measurable_const.mul hmass
    have href : ∫⁻ ω, Mr ω Good ∂P = gmcReferenceMeasure Good :=
      regularizedGMC_lintegral_eq_reference P X hX Xc hXc _ _ _ hGood
    refine (lintegral_mono_ae hpoint).trans ?_
    rw [lintegral_add_left hlm, lintegral_const_mul _ hmass, href]
    exact add_le_add (by gcongr; exact Set.subset_univ _)
      (le_iSup₂_of_le c.1 ⟨c, hc, rfl⟩ (le_iSup_of_le f (le_iSup_of_le hfm
        (le_iSup_of_le hfb (le_iSup_of_le hfK le_rfl)))))
  have h₁ := ENNReal.div_le_of_le_mul ((hm₁.trans_lt hb₁).le)
  have h₂ := ENNReal.div_le_of_le_mul ((hm₂.trans_lt hb₂).le)
  have h₃ := ENNReal.div_le_of_le_mul (hgood.trans (hr₀ r ((le_max_left _ _).trans hr)).le)
  exact (add_le_add (add_le_add h₁ h₂) h₃).trans_eq (ENNReal.add_thirds θ)

end DOZZ.Proofs
