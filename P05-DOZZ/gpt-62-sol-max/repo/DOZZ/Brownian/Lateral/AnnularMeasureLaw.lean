/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Lateral.DilationLaw
public import DOZZ.GMC.Moments.InversionMeasureLaw
public import DOZZ.Brownian.LateralLocalFiniteness
import DOZZ.GMC.MeasurableIntegrals
@[expose] public section
open Filter MeasureTheory Set ProbabilityTheory
open scoped Topology Distributions ENNReal
namespace DOZZ.Proofs

/-- A bounded open annulus used to exhaust the punctured plane. -/
def lateralLawAnnulus (n : ℕ) : Set ℂ :=
  {x | 1 / ((n : ℝ) + 2) < ‖x‖ ∧ ‖x‖ < (n : ℝ) + 2}

/-- The annular exhaustion consists of open sets. -/
theorem isOpen_lateralLawAnnulus (n : ℕ) : IsOpen (lateralLawAnnulus n) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

/-- Its closure is compact and stays away from the origin. -/
theorem lateralLawAnnulus_closure (n : ℕ) :
    IsCompact (closure (lateralLawAnnulus n)) ∧ (0 : ℂ) ∉ closure (lateralLawAnnulus n) := by
  have hs : closure (lateralLawAnnulus n) ⊆
      {x : ℂ | 1 / ((n : ℝ) + 2) ≤ ‖x‖ ∧ ‖x‖ ≤ (n : ℝ) + 2} := by
    apply closure_minimal
    · exact fun _ hx => ⟨hx.1.le, hx.2.le⟩
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
  constructor
  · apply (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 2)).of_isClosed_subset isClosed_closure
    intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hs hx).2
  · intro h
    have hn : 0 < 1 / ((n : ℝ) + 2) := by positivity
    exact (not_le_of_gt hn) (by simpa only [norm_zero] using (hs h).1)

/-- The annuli increase. -/
theorem lateralLawAnnulus_monotone : Monotone lateralLawAnnulus := by
  intro n k hnk x hx
  have hnk' : (n : ℝ) + 2 ≤ (k : ℝ) + 2 := by simpa
  exact ⟨lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) hnk') hx.1,
    hx.2.trans_le hnk'⟩

/-- Every nonzero point is in some annulus. -/
theorem lateralLawAnnulus_exhaustion :
    (⋃ n, lateralLawAnnulus n) = ({0} : Set ℂ)ᶜ := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hpos  := lt_trans (by positivity) hn.1
    simpa only [mem_compl_iff, mem_singleton_iff] using norm_pos_iff.mp hpos
  · intro hx
    have hxpos  := norm_pos_iff.mpr hx
    obtain ⟨n, hn⟩ := exists_nat_gt (max ‖x‖ (1 / ‖x‖))
    apply mem_iUnion.mpr
    refine ⟨n, ?_, ?_⟩
    · have ht : 1 / ‖x‖ < (n : ℝ) + 2 := (le_max_right _ _).trans_lt hn |>.trans (by linarith)
      exact (div_lt_iff₀ (by positivity)).mpr
        (by simpa only [one_mul, mul_comm] using (div_lt_iff₀ hxpos).mp ht)
    · exact (le_max_left _ _).trans_lt hn |>.trans (by linarith)

private abbrev LateralAnnularOpen :=
  {U : Set ℂ // IsOpen U ∧ IsCompact (closure U) ∧ (0 : ℂ) ∉ closure U}
private abbrev LateralLocallyFiniteMeasure :=
  {μ : Measure ℂ // μ {0} = 0 ∧ ∀ K : Set ℂ,
    IsCompact K → (0 : ℂ) ∉ K → μ K < ⊤}
private noncomputable abbrev lateralAnnularMeasureCode : LateralLocallyFiniteMeasure → LateralAnnularOpen → ℝ≥0∞ :=
  measureMassCode

/-- The law of a locally finite punctured-plane random measure is determined by finite
vectors of relatively compact open masses. Measurability up to a null event suffices. -/
theorem lateral_random_measure_law_of_annular_open_fdd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (M N : Ω → Measure ℂ) (hM : AEMeasurable M P) (hN : AEMeasurable N P)
    (hMf : ∀ ω, M ω {0} = 0 ∧ ∀ K : Set ℂ,
      IsCompact K → (0 : ℂ) ∉ K → M ω K < ⊤)
    (hNf : ∀ ω, N ω {0} = 0 ∧ ∀ K : Set ℂ,
      IsCompact K → (0 : ℂ) ∉ K → N ω K < ⊤)
    (hfdd : ∀ (ι : Type) [Fintype ι] (U : ι → Set ℂ),
      (∀ j, IsOpen (U j) ∧ IsCompact (closure (U j)) ∧ (0 : ℂ) ∉ closure (U j)) →
      P.map (fun ω j => M ω (U j)) = P.map (fun ω j => N ω (U j))) :
    P.map M = P.map N := by
  have hc : MeasurableSpace.pi.comap lateralAnnularMeasureCode = Subtype.instMeasurableSpace := by
    apply measureMassCode_comap_eq (fun U => U.2.1.measurableSet)
    let _ : MeasurableSpace LateralLocallyFiniteMeasure := MeasurableSpace.pi.comap lateralAnnularMeasureCode
    have hcode : Measurable lateralAnnularMeasureCode := .of_comap_le le_rfl
    have hrestrict (n : ℕ) : Measurable
        (fun q : LateralLocallyFiniteMeasure => q.1.restrict (lateralLawAnnulus n)) := by
      let : ∀ q : LateralLocallyFiniteMeasure,
          IsFiniteMeasure (q.1.restrict (lateralLawAnnulus n)) := fun q => ⟨by
        rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_lt (measure_mono subset_closure)
          (q.2.2 _ (lateralLawAnnulus_closure n).1 (lateralLawAnnulus_closure n).2)⟩
      apply Measurable.measure_of_isPiSystem BorelSpace.measurable_eq isPiSystem_isOpen
      · intro S hS
        change IsOpen S at hS
        have hcs : closure (S ∩ lateralLawAnnulus n) ⊆ closure (lateralLawAnnulus n) :=
          closure_mono inter_subset_right
        have hu : IsOpen (S ∩ lateralLawAnnulus n) ∧
            IsCompact (closure (S ∩ lateralLawAnnulus n)) ∧
            (0 : ℂ) ∉ closure (S ∩ lateralLawAnnulus n) :=
          ⟨hS.inter (isOpen_lateralLawAnnulus n),
            (lateralLawAnnulus_closure n).1.of_isClosed_subset isClosed_closure hcs,
            fun h => (lateralLawAnnulus_closure n).2 (hcs h)⟩
        simpa only [lateralAnnularMeasureCode, Measure.restrict_apply hS.measurableSet] using
          (measurable_pi_iff.mp hcode) ⟨S ∩ lateralLawAnnulus n, hu⟩
      · simpa using (measurable_pi_iff.mp hcode) ⟨lateralLawAnnulus n,
                    isOpen_lateralLawAnnulus n, lateralLawAnnulus_closure n⟩
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have heq : (fun q : LateralLocallyFiniteMeasure => q.1 S) =
        fun q => ⨆ n, q.1.restrict (lateralLawAnnulus n) S := by
      funext q
      have hsupport : q.1.restrict (⋃ n, lateralLawAnnulus n) = q.1 := by
        rw [lateralLawAnnulus_exhaustion]
        exact Measure.restrict_eq_self_of_ae_mem (by
          rw [ae_iff]; simpa only [not_not, mem_compl_iff, ofPred_mem_eq] using q.2.1)
      calc q.1 S = q.1.restrict (⋃ n, lateralLawAnnulus n) S :=
        congrArg (fun μ : Measure ℂ => μ S) hsupport.symm
      _ = _ := Measure.restrict_iUnion_apply_eq_iSup lateralLawAnnulus_monotone.directed_le hS
    rw [heq]
    exact Measurable.iSup fun n => (Measure.measurable_coe hS).comp (hrestrict n)
  exact (identDistrib_measure_of_mass_fdd hc hM hN hMf hNf
    fun s => hfdd s (fun j => j.1.1) (fun j => j.1.2)).map_eq

/-- Removing the radial factor preserves finiteness on every compact subset of the
punctured plane. Its logarithmic radii lie in a compact interval. -/
theorem originRadialRemovedGMC_compact_lt_top
    (γ : ℝ) (A : TwoSidedPath) (M : Measure ℂ) [IsFiniteMeasure M]
    (K : Set ℂ) (hK : IsCompact K) (hzero : (0 : ℂ) ∉ K) :
    M.withDensity (lateralRadialWeight γ A) K < ⊤ := by
  let r : ℂ → ℝ := fun x => -Real.log ‖x‖
  have hr  :=
    (continuous_norm.continuousOn.log (fun x hx =>
      norm_ne_zero_iff.mpr (fun h => hzero (h ▸ hx)))).neg
  obtain ⟨a, ha⟩ := (hK.image_of_continuousOn hr).bddBelow
  exact Exists.casesOn (IsCompact.bddAbove (IsCompact.image_of_continuousOn hK hr)) fun b hb =>
    have hsub := fun x hx => ⟨ha (Exists.intro x ⟨hx, rfl⟩), hb (Exists.intro x ⟨hx, rfl⟩)⟩;
    have hrm := Measurable.comp measurable_neg (Measurable.comp Real.measurable_log measurable_norm);
    Trans.trans (Trans.trans (measure_mono hsub) (Eq.symm (Measure.map_apply hrm measurableSet_Icc)))
      (lateralProjectedGMC_Icc_ne_top γ A M a b)

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (M N : Ω → Measure ℂ)
  (hM : AEMeasurable M P) (hN : AEMeasurable N P)
include Ω hM hN

/-- Equality of finite vectors of compact test integrals determines finite vectors of
relatively compact open-set masses, even for measures with infinite total mass. -/
theorem lateral_open_mass_fdd_of_compact_test_fdd
    (hMf : ∀ ω K, IsCompact K → (0 : ℂ) ∉ K → M ω K < ⊤)
    (hNf : ∀ ω K, IsCompact K → (0 : ℂ) ∉ K → N ω K < ⊤)
    (htest : ∀ {m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ),
      (∀ j, HasCompactSupport (f j : ℂ → ℝ)) →
      (∀ j, (0 : ℂ) ∉ tsupport (f j : ℂ → ℝ)) →
      P.map (fun ω j => ∫ x, f j x ∂M ω) = P.map (fun ω j => ∫ x, f j x ∂N ω))
    (ι : Type) [Fintype ι] (U : ι → Set ℂ)
    (hU : ∀ j, IsOpen (U j) ∧ IsCompact (closure (U j)) ∧ (0 : ℂ) ∉ closure (U j)) :
    P.map (fun ω j => M ω (U j)) = P.map (fun ω j => N ω (U j)) := by
  apply (identDistrib_open_mass U (fun j => (hU j).1) M N
    (fun ω j => hMf ω _ (hU j).2.1 (hU j).2.2)
    (fun ω j => hNf ω _ (hU j).2.1 (hU j).2.2) ?_).map_eq
  intro n
  classical
  let e := (Fintype.equivFin ι).symm
  let q := fun j => gmcOpenApprox (U (e j)) (hU (e j)).1 n
  apply identDistrib_pi_of_reindex e
  exact ⟨AEMeasurable.of_eval (fun j => ((measurable_integral_of_measurable_measure measurable_id
        (q j).continuous.stronglyMeasurable).comp_aemeasurable hM)),
    AEMeasurable.of_eval (fun j => ((measurable_integral_of_measurable_measure measurable_id
        (q j).continuous.stronglyMeasurable).comp_aemeasurable hN)),
    htest q (fun j => (hU (e j)).2.1.of_isClosed_subset (isClosed_tsupport _)
      (gmcOpenApprox_tsupport_subset _ _ n))
      (fun j hx => (hU (e j)).2.2 (gmcOpenApprox_tsupport_subset _ _ n hx))⟩

/-- Compact test-vector laws determine entire punctured locally finite measure laws. -/
theorem lateral_random_measure_law_of_compact_test_fdd
    (hMf : ∀ ω, M ω {0} = 0 ∧ ∀ K : Set ℂ,
      IsCompact K → (0 : ℂ) ∉ K → M ω K < ⊤)
    (hNf : ∀ ω, N ω {0} = 0 ∧ ∀ K : Set ℂ,
      IsCompact K → (0 : ℂ) ∉ K → N ω K < ⊤)
    (htest : ∀ {m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ),
      (∀ j, HasCompactSupport (f j : ℂ → ℝ)) →
      (∀ j, (0 : ℂ) ∉ tsupport (f j : ℂ → ℝ)) →
      P.map (fun ω j => ∫ x, f j x ∂M ω) = P.map (fun ω j => ∫ x, f j x ∂N ω)) :
    P.map M = P.map N :=
  lateral_random_measure_law_of_annular_open_fdd P M N hM hN hMf hNf
    (lateral_open_mass_fdd_of_compact_test_fdd P M N hM hN
      (fun ω => (hMf ω).2) (fun ω => (hNf ω).2) htest)

end

/-- Every compact subset of the punctured plane fits in a positive lateral chart. -/
theorem exists_originLateralChart_of_compact
    (K : Set ℂ) (hK : IsCompact K) (hzero : (0 : ℂ) ∉ K) :
    ∃ ρ : ℝ, 0 < ρ ∧ K ⊆ originLateralChart ρ := by
  by_cases hn : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hn continuous_norm.continuousOn
    have hxpos  := norm_pos_iff.mpr (fun h => hzero (h ▸ hx))
    refine ⟨‖x‖ / 4, by positivity, ?_⟩
    intro y hy
    have hxy  := (isMinOn_iff.mp hmin) y hy
    change 2 * (‖x‖ / 4) < ‖y‖
    linarith
  · exact ⟨1, zero_lt_one, (not_nonempty_iff_eq_empty.mp hn) ▸ empty_subset _⟩

/-- Nonzero dilation preserves zero origin mass and local finiteness on punctured compacts. -/
theorem lateral_locally_finite_map_dilation
    (μ : Measure ℂ) (hzero : μ {0} = 0)
    (hfin : ∀ K, IsCompact K → (0 : ℂ) ∉ K → μ K < ⊤)
    (c : ℝ) (hc : 0 < c) :
    (μ.map (fun x : ℂ => (c : ℂ) * x)) {0} = 0 ∧
      ∀ K, IsCompact K → (0 : ℂ) ∉ K →
        (μ.map (fun x : ℂ => (c : ℂ) * x)) K < ⊤ := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hm : Measurable (fun x : ℂ => (c : ℂ) * x) := by fun_prop
  constructor
  · rw [Measure.map_apply hm (measurableSet_singleton 0)]
    simpa only [preimage, mem_singleton_iff, mul_eq_zero, hc0, false_or,
      ofPred_eq_eq_singleton] using hzero
  · intro K hK hz
    rw [Measure.map_apply hm hK.measurableSet]
    exact hfin _ ((Homeomorph.mulLeft₀ (c : ℂ) hc0).isCompact_preimage.mpr hK)
      (by simpa)

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
  (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
  (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
  (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
include hX hc hm hcont

section
variable (c γ : ℝ) (hcpos : 0 < c) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
  (hM : IsGMCOf P X γ M)
include hcpos hγ hγ2 hM

/-- Dilation invariance of compact-test vectors with only their intrinsic support
conditions; the common chart and pullback support are constructed here. -/
theorem originRadialRemovedGMC_dilation_annular_test_vector_law
    {m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (hfc : ∀ j, HasCompactSupport (f j : ℂ → ℝ))
    (hfzero : ∀ j, (0 : ℂ) ∉ tsupport (f j : ℂ → ℝ)) :
    P.map (fun ω j => ∫ x, f j x
      ∂(M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) =
    P.map (fun ω j => ∫ x, f j (c * x)
      ∂(M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  let e := Homeomorph.mulLeft₀ (c : ℂ) hc0
  let T := ⋃ j, tsupport (f j : ℂ → ℝ)
  have hT  := isCompact_iUnion hfc
  have hTzero : (0 : ℂ) ∉ T := by
    intro h; obtain ⟨j, hj⟩ := mem_iUnion.mp h; exact hfzero j hj
  let K := e ⁻¹' T
  have hK  := e.isCompact_preimage.mpr hT
  have hKzero : (0 : ℂ) ∉ K := by simpa only [K, mem_preimage, e,
    Homeomorph.coe_mulLeft₀, mul_zero] using hTzero
  obtain ⟨ρ, hρ, hKU⟩ := exists_originLateralChart_of_compact K hK hKzero
  have hgK j  :=
    (tsupport_comp_subset_preimage (f j : ℂ → ℝ) e.continuous).trans
      (preimage_mono (subset_iUnion (fun j => tsupport (f j : ℂ → ℝ)) j))
  have hgc j  :=
    (hfc j).comp_homeomorph e
  have hgU j  :=
    (hgK j).trans hKU
  have hfV j : tsupport (f j : ℂ → ℝ) ⊆ originLateralChart (c * ρ) := by
    intro x hx
    have hpre : e.symm x ∈ K := by
      change e (e.symm x) ∈ T
      rw [e.apply_symm_apply]
      exact mem_iUnion.mpr ⟨j, hx⟩
    have h := (originLateralChart_dilation_mem ρ c hcpos (e.symm x)).mpr (hKU hpre)
    change e (e.symm x) ∈ originLateralChart (c * ρ) at h
    simpa only [e.apply_symm_apply] using h
  exact originRadialRemovedGMC_dilation_test_vector_law P X Xc hX hc hm hcont
    ρ c γ hρ hcpos hγ hγ2 M hM K hK hKU f hfc hfV
    (fun j x hx => image_eq_zero_of_notMem_tsupport (fun h =>
      hx (show e x ∈ T from mem_iUnion.mpr ⟨j, h⟩))) hgc hgU

/-- Positive dilation preserves the law of the entire actual radial-removed
measure. The measure need only be locally finite on the punctured plane. -/
theorem originRadialRemovedGMC_dilation_law :
    P.map (fun ω => ((M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))).map
      (fun x : ℂ => (c : ℂ) * x)) =
    P.map (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) := by
  let  := hX.1
  let F := fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hMm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hF := originRadialRemovedGMC_aemeasurable P γ _ hA M hMm hM.1
  have hs : Measurable (fun x : ℂ => (c : ℂ) * x) := by fun_prop
  have hN  :=
    (Measure.measurable_map _ hs).comp_aemeasurable hF
  have hfin ω K hK hz := @originRadialRemovedGMC_compact_lt_top γ
    (originRadialPath Xc ω) (M ω) (hM.1 ω) K hK hz
  have hf ω := lateral_locally_finite_map_dilation (F ω)
    (originRadialRemovedGMC_origin γ _ _) (hfin ω) c hcpos
  apply lateral_random_measure_law_of_compact_test_fdd P _ F hN hF hf
    (fun ω => ⟨originRadialRemovedGMC_origin γ _ _, hfin ω⟩)
  intro m f hfc hz
  have he ω j : (∫ x, f j x ∂(F ω).map (fun x : ℂ => (c : ℂ) * x)) =
      ∫ x, f j (c * x) ∂F ω :=
    integral_map hs.aemeasurable (f j).continuous.aestronglyMeasurable
  change P.map (fun ω j => ∫ x, f j x ∂(F ω).map (fun x : ℂ => (c : ℂ) * x)) =
    P.map (fun ω j => ∫ x, f j x ∂F ω)
  simp_rw [he]
  exact (originRadialRemovedGMC_dilation_annular_test_vector_law P X Xc hX hc hm hcont
    c γ hcpos hγ hγ2 M hM f hfc hz).symm

end

/-- Translation preserves the law of the entire polar lateral projection
`DOZZ.lateralProjectedGMC`. -/
theorem lateralProjectedGMC_translation_law
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (t : ℝ) :
    P.map (fun ω => (lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)).map
      (fun s : ℝ => s + t)) =
    P.map (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) := by
  let F := fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))
  let c := Real.exp (-t)
  have hcpos : 0 < c := Real.exp_pos _
  have hs : Measurable (fun x : ℂ => (c : ℂ) * x) := by fun_prop
  have hr : Measurable (fun x : ℂ => -Real.log ‖x‖) := by fun_prop
  have hmap := originRadialRemovedGMC_dilation_law P X Xc hX hc hm hcont
    c γ hcpos hγ hγ2 M hM
  have hF := originRadialRemovedGMC_aemeasurable P γ _
    (originRadialPath_aemeasurable P X Xc hc hcont) M
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM) hM.1
  have hN : AEMeasurable (fun ω => (F ω).map (fun x : ℂ => (c : ℂ) * x)) P :=
    (Measure.measurable_map _ hs).comp_aemeasurable hF
  have hproj := Measure.measurable_map _ hr
  have h := congrArg (fun μ : Measure (Measure ℂ) => μ.map (fun ν => ν.map
    (fun x : ℂ => -Real.log ‖x‖))) hmap
  rw [AEMeasurable.map_map_of_aemeasurable hproj.aemeasurable hN,
    AEMeasurable.map_map_of_aemeasurable hproj.aemeasurable hF] at h
  have he ω : ((F ω).map (fun x : ℂ => (c : ℂ) * x)).map
      (fun x : ℂ => -Real.log ‖x‖) =
      (lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)).map (fun s : ℝ => s + t) := by
    rw [logRadiusProjection_dilation (F ω) (originRadialRemovedGMC_origin γ _ _) c hcpos]
    change (lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)).map _ = _
    congr 1
    funext s
    simp only [c, Real.log_exp, sub_neg_eq_add]
  change P.map (fun ω => ((F ω).map (fun x : ℂ => (c : ℂ) * x)).map
    (fun x : ℂ => -Real.log ‖x‖)) =
    P.map (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) at h
  simpa only [he] using h

end

end DOZZ.Proofs
