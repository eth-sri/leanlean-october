/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Lateral.DilationLaw
public import DOZZ.GMC.Moments.InversionMeasureLaw
public import DOZZ.Brownian.LateralLocalFiniteness
@[expose] public section
open Filter MeasureTheory Set
open scoped Topology Distributions ENNReal
namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

private def latAnnulus (n : ℕ) : Set ℂ :=
  {x | 1 / ((n : ℝ) + 2) < ‖x‖ ∧ ‖x‖ < (n : ℝ) + 2}


private abbrev LatAnnOpen :=
  {U : Set ℂ // IsOpen U ∧ IsCompact (closure U) ∧ (0 : ℂ) ∉ closure U}
private abbrev LatLocFin :=
  {μ : Measure ℂ // μ {0} = 0 ∧ ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → μ K < ⊤}
private def latCode (μ : LatLocFin) : LatAnnOpen → ℝ≥0∞ := fun U => μ.1 U.1


/-- Bounded continuous integrals of finite random measures are measurable up to null sets. -/
theorem finiteMeasure_bcf_integral_aemeasurable (P : Measure Ω)
    (M : Ω → Measure ℂ) (hM : AEMeasurable M P)
    (hfin : ∀ ω, IsFiniteMeasure (M ω)) (f : BoundedContinuousFunction ℂ ℝ) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P := by
  let : ∀ ω, IsFiniteMeasure (M ω) := hfin
  have hp := (Measure.measurable_lintegral
    (BoundedContinuousFunction.measurable_coe_ennreal_comp f.nnrealPart)).comp_aemeasurable hM
  have hn := (Measure.measurable_lintegral
    (BoundedContinuousFunction.measurable_coe_ennreal_comp (-f).nnrealPart)).comp_aemeasurable hM
  have h : AEMeasurable (fun ω =>
      (∫⁻ x, (f.nnrealPart x : ℝ≥0∞) ∂M ω).toReal -
      (∫⁻ x, ((-f).nnrealPart x : ℝ≥0∞) ∂M ω).toReal) P :=
    hp.ennreal_toReal.sub hn.ennreal_toReal
  simpa only [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub,
    BoundedContinuousFunction.toReal_lintegral_coe_eq_integral, Function.comp_def, Pi.sub_apply] using h



/-- Translation preserves the law of the entire polar lateral projection
`DOZZ.lateralProjectedGMC`. -/
theorem lateralProjectedGMC_translation_law (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (t : ℝ) :
    P.map (fun ω => (lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)).map (fun s : ℝ => s + t)) =
      P.map (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) := by
  have openApprox_tsupport_sub (U : Set ℂ) (hU : IsOpen U) (n : ℕ) : tsupport (gmcOpenApprox U hU n : ℂ → ℝ) ⊆ closure U := 
    closure_mono fun x hx => by
      by_contra h; classical
      exact hx (by simp [gmcOpenApprox, show U ≠ univ from fun hu => h (hu ▸ mem_univ x),
        Metric.infDist_zero_of_mem (show x ∈ Uᶜ from h)])
  have lat_law_of_annular_open_fdd [IsFiniteMeasure P] (M N : Ω → Measure ℂ) (hM : AEMeasurable M P) (hN : AEMeasurable N P) (hMf : ∀ ω, M ω {0} = 0 ∧ ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → M ω K < ⊤) (hNf : ∀ ω, N ω {0} = 0 ∧ ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → N ω K < ⊤) (hfdd : ∀ (ι : Type) [Fintype ι] (U : ι → Set ℂ), (∀ j, IsOpen (U j) ∧ IsCompact (closure (U j)) ∧ (0 : ℂ) ∉ closure (U j)) → P.map (fun ω j => M ω (U j)) = P.map (fun ω j => N ω (U j))) : P.map M = P.map N := by
    have latAnnulus_props (n : ℕ) : IsOpen (latAnnulus n) ∧ IsCompact (closure (latAnnulus n)) ∧ (0 : ℂ) ∉ closure (latAnnulus n) := by
      have hs : closure (latAnnulus n) ⊆ {x : ℂ | 1 / ((n : ℝ) + 2) ≤ ‖x‖ ∧ ‖x‖ ≤ (n : ℝ) + 2} :=
        closure_minimal (fun _ hx => ⟨hx.1.le, hx.2.le⟩)
          ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
      refine ⟨(isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const),
        (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 2)).of_isClosed_subset isClosed_closure
          fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using (hs hx).2,
        fun h => (not_le_of_gt (by positivity : 0 < 1 / ((n : ℝ) + 2))) (by simpa using (hs h).1)⟩
    classical
    let C := measurableCylinders (fun _ : LatAnnOpen => ℝ≥0∞)
    let mOut := MeasurableSpace.pi.comap latCode
    let : MeasurableSpace LatLocFin := mOut
    let outM (ω : Ω) : LatLocFin := ⟨M ω, hMf ω⟩
    let outN (ω : Ω) : LatLocFin := ⟨N ω, hNf ω⟩
    let Cout := Set.preimage latCode '' C
    have hgen : mOut = MeasurableSpace.generateFrom Cout := by
      dsimp [mOut, Cout, C]; rw [← generateFrom_measurableCylinders, MeasurableSpace.comap_generateFrom]
    have hpi : IsPiSystem Cout := by
      rintro _ ⟨A', hA', rfl⟩ _ ⟨B', hB', rfl⟩ ⟨q, hq⟩
      exact ⟨A' ∩ B', isPiSystem_measurableCylinders A' hA' B' hB' ⟨latCode q, hq⟩, rfl⟩
    have hcode : Measurable latCode := Measurable.of_comap_le le_rfl
    have hto : @Measurable LatLocFin LatLocFin Subtype.instMeasurableSpace mOut id := by
      rw [measurable_iff_comap_le, MeasurableSpace.comap_id]
      let : MeasurableSpace LatLocFin := Subtype.instMeasurableSpace
      exact (measurable_pi_iff.mpr fun U =>
        (Measure.measurable_coe U.2.1.measurableSet).comp measurable_subtype_coe).comap_le
    have hom : AEMeasurable outM P :=
      @Measurable.comp_aemeasurable Ω LatLocFin LatLocFin _ mOut P Subtype.instMeasurableSpace
        outM id hto (@AEMeasurable.subtype_mk Ω (Measure ℂ) _ _ M P hM _ hMf)
    have hon : AEMeasurable outN P :=
      @Measurable.comp_aemeasurable Ω LatLocFin LatLocFin _ mOut P Subtype.instMeasurableSpace
        outN id hto (@AEMeasurable.subtype_mk Ω (Measure ℂ) _ _ N P hN _ hNf)
    have hrest (n : ℕ) : Measurable (fun q : LatLocFin => q.1.restrict (latAnnulus n)) := by
      obtain ⟨ho, hc, hz⟩ := latAnnulus_props n
      let : ∀ q : LatLocFin, IsFiniteMeasure (q.1.restrict (latAnnulus n)) := fun q =>
        ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono subset_closure).trans_lt (q.2.2 _ hc hz)⟩
      refine Measurable.measure_of_isPiSystem rfl isPiSystem_isOpen (fun S (hS : IsOpen S) => ?_) ?_
      · have hcs : closure (S ∩ latAnnulus n) ⊆ closure (latAnnulus n) := closure_mono inter_subset_right
        simpa only [latCode, Measure.restrict_apply hS.measurableSet] using
          (measurable_pi_iff.mp hcode) ⟨S ∩ latAnnulus n, hS.inter ho,
            hc.of_isClosed_subset isClosed_closure hcs, fun h => hz (hcs h)⟩
      · simpa only [latCode, Measure.restrict_apply_univ] using (measurable_pi_iff.mp hcode) ⟨latAnnulus n, ho, hc, hz⟩
    have hexh : (⋃ n, latAnnulus n) = ({0} : Set ℂ)ᶜ := by
      ext x; constructor
      · rintro ⟨_, ⟨n, rfl⟩, hx⟩
        exact norm_pos_iff.mp (lt_trans (by positivity) hx.1)
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_gt (max ‖x‖ (1 / ‖x‖))
        refine mem_iUnion.2 ⟨n, ?_, (le_max_left _ _).trans_lt (hn.trans (by linarith))⟩
        have ht : 1 / ‖x‖ < (n : ℝ) + 2 := (le_max_right _ _).trans_lt (hn.trans (by linarith))
        exact (div_lt_iff₀ (by positivity)).2
          (by simpa [mul_comm] using (div_lt_iff₀ (norm_pos_iff.2 hx)).1 ht)
    have hmono : Monotone latAnnulus := fun n k hnk _ hx => by
      have hle : (n : ℝ) + 2 ≤ (k : ℝ) + 2 := mod_cast Nat.add_le_add_right hnk 2
      exact ⟨lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) hle) hx.1, hx.2.trans_le hle⟩
    have hforget : Measurable (fun q : LatLocFin => q.1) :=
      Measure.measurable_of_measurable_coe _ fun S hS => by
        have heq : (fun q : LatLocFin => q.1 S) = fun q => ⨆ n, q.1.restrict (latAnnulus n) S :=
          funext fun q => by
            have hsup : q.1.restrict (⋃ n, latAnnulus n) = q.1 := by
              rw [hexh]; exact Measure.restrict_eq_self_of_ae_mem
                (by rw [ae_iff]; simpa only [not_not, mem_compl_iff, ofPred_mem_eq] using q.2.1)
            exact (congrArg (· S) hsup.symm).trans (Measure.restrict_iUnion_apply_eq_iSup hmono.directed_le hS)
        rw [heq]; exact Measurable.iSup fun n => (Measure.measurable_coe hS).comp (hrest n)
    have hLaw : P.map outM = P.map outN := by
      refine MeasureTheory.ext_of_generate_finite Cout hgen hpi ?_ ?_
      · rintro _ ⟨A, hA, rfl⟩
        rcases (mem_measurableCylinders A).1 hA with ⟨s, As, hAs, rfl⟩
        have hm : AEMeasurable (fun ω (j : s) => M ω j.1.1) P :=
          AEMeasurable.of_eval fun j => (Measure.measurable_coe j.1.2.1.measurableSet).comp_aemeasurable hM
        have hn : AEMeasurable (fun ω (j : s) => N ω j.1.1) P :=
          AEMeasurable.of_eval fun j => (Measure.measurable_coe j.1.2.1.measurableSet).comp_aemeasurable hN
        have hs : MeasurableSet (latCode ⁻¹' cylinder s As) := by
          apply hcode
          rw [← generateFrom_measurableCylinders]
          exact MeasurableSpace.measurableSet_generateFrom
            (cylinder_mem_measurableCylinders (α := fun _ : LatAnnOpen => ℝ≥0∞) s As hAs)
        rw [Measure.map_apply_of_aemeasurable hom hs, Measure.map_apply_of_aemeasurable hon hs]
        have h := congrArg (· As) (hfdd s (fun j => j.1.1) (fun j => j.1.2))
        rwa [Measure.map_apply_of_aemeasurable hm hAs, Measure.map_apply_of_aemeasurable hn hAs] at h
      · simp [Measure.map_apply_of_aemeasurable hom MeasurableSet.univ,
          Measure.map_apply_of_aemeasurable hon MeasurableSet.univ]
    simpa only [AEMeasurable.map_map_of_aemeasurable hforget.aemeasurable hom,
      AEMeasurable.map_map_of_aemeasurable hforget.aemeasurable hon, Function.comp_def] using
      congrArg (fun μ => μ.map (fun q : LatLocFin => q.1)) hLaw
  have integral_restrict_of_zero_outside (μ : Measure ℂ) (K : Set ℂ) (hK : MeasurableSet K) (f : ℂ → ℝ) (hf : ∀ x, x ∉ K → f x = 0) : ∫ x, f x ∂μ.restrict K = ∫ x, f x ∂μ := by
    rw [← integral_indicator hK]
    exact integral_congr_ae (ae_of_all _ fun x => by by_cases hx : x ∈ K <;> simp [hx, hf x])
  let _ := hX.1
  let F (ω : Ω) := (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))
  let c := Real.exp (-t)
  have hcpos : 0 < c := Real.exp_pos _
  have hc0 : (c : ℂ) ≠ 0 := mod_cast hcpos.ne'
  have hs : Measurable (fun x : ℂ => (c : ℂ) * x) := by fun_prop
  have hr : Measurable (fun x : ℂ => -Real.log ‖x‖) := by fun_prop
  have hF := originRadialRemovedGMC_aemeasurable P γ _ (originRadialPath_aemeasurable P X Xc hc hcont) M
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM) hM.1
  have hN : AEMeasurable (fun ω => (F ω).map (fun x : ℂ => (c : ℂ) * x)) P :=
    (Measure.measurable_map _ hs).comp_aemeasurable hF
  have hfin (ω : Ω) (K : Set ℂ) (hK : IsCompact K) (hz : (0 : ℂ) ∉ K) : F ω K < ⊤ := by
    let _ := hM.1 ω
    let rfn (x : ℂ) := -Real.log ‖x‖
    have hrc := (continuous_norm.continuousOn.log fun x hx =>
      norm_ne_zero_iff.2 fun h => hz (h ▸ hx)).neg
    obtain ⟨a, ha⟩ := (hK.image_of_continuousOn hrc).bddBelow
    obtain ⟨b, hb⟩ := (hK.image_of_continuousOn hrc).bddAbove
    have hrm : Measurable rfn := measurable_neg.comp (Real.measurable_log.comp measurable_norm)
    exact ((measure_mono (fun x hx => ⟨ha ⟨x, hx, rfl⟩, hb ⟨x, hx, rfl⟩⟩ : K ⊆ rfn ⁻¹' Icc a b)).trans_eq
      (Measure.map_apply hrm measurableSet_Icc).symm).trans_lt
      (lateralProjectedGMC_Icc_ne_top γ (originRadialPath Xc ω) (M ω) a b)
  have hNf (ω : Ω) : ((F ω).map (fun x : ℂ => (c : ℂ) * x)) {0} = 0 ∧
      ∀ K, IsCompact K → (0 : ℂ) ∉ K → ((F ω).map (fun x : ℂ => (c : ℂ) * x)) K < ⊤ :=
    ⟨by rw [Measure.map_apply hs (measurableSet_singleton 0)]
        simpa only [preimage, mem_singleton_iff, mul_eq_zero, hc0, false_or,
          ofPred_eq_eq_singleton] using originRadialRemovedGMC_origin γ (originRadialPath Xc ω) (M ω),
     fun K hK hz => by
        rw [Measure.map_apply hs hK.measurableSet]
        exact hfin ω _ ((Homeomorph.mulLeft₀ (c : ℂ) hc0).isCompact_preimage.2 hK) (by simpa using hz)⟩
  have hFf (ω : Ω) := (⟨originRadialRemovedGMC_origin γ _ _, hfin ω⟩ :
    F ω {0} = 0 ∧ ∀ K, IsCompact K → (0 : ℂ) ∉ K → F ω K < ⊤)
  -- Dilation law on compact test vectors -> open mass FDD -> measure law
  have htest {m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ)
      (hfc : ∀ j, HasCompactSupport (f j : ℂ → ℝ)) (hfz : ∀ j, (0 : ℂ) ∉ tsupport (f j : ℂ → ℝ)) :
      P.map (fun ω j => ∫ x, f j x ∂(F ω).map (fun x : ℂ => (c : ℂ) * x)) =
        P.map (fun ω j => ∫ x, f j x ∂F ω) := by
    let e := Homeomorph.mulLeft₀ (c : ℂ) hc0
    let T := ⋃ j, tsupport (f j : ℂ → ℝ)
    let K := e ⁻¹' T
    have hK := e.isCompact_preimage.2 (isCompact_iUnion hfc)
    have hKz : (0 : ℂ) ∉ K := fun h => by
      have h0T : (0 : ℂ) ∈ T := by simpa [K, e] using h
      obtain ⟨j, hj⟩ := mem_iUnion.1 h0T; exact hfz j hj
    obtain ⟨ρ, hρ, hKU⟩ : ∃ ρ : ℝ, 0 < ρ ∧ K ⊆ originLateralChart ρ := by
      by_cases hn : K.Nonempty
      · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hn continuous_norm.continuousOn
        have hx0 := norm_pos_iff.2 fun h => hKz (h ▸ hx)
        exact ⟨‖x‖ / 4, by positivity, fun y hy => by
          change 2 * (‖x‖ / 4) < ‖y‖; linarith [isMinOn_iff.1 hmin y hy]⟩
      · exact ⟨1, zero_lt_one, (not_nonempty_iff_eq_empty.1 hn) ▸ empty_subset _⟩
    have hgK (j : Fin m) := (tsupport_comp_subset_preimage (f j : ℂ → ℝ) e.continuous).trans
      (preimage_mono (subset_iUnion (fun j => tsupport (f j : ℂ → ℝ)) j))
    have hfV (j : Fin m) : tsupport (f j : ℂ → ℝ) ⊆ originLateralChart (c * ρ) := fun x hx => by
      have hpre : e.symm x ∈ K := by
        change e (e.symm x) ∈ T; rw [e.apply_symm_apply]; exact mem_iUnion.2 ⟨j, hx⟩
      have h := (originLateralChart_dilation_mem ρ c hcpos (e.symm x)).2 (hKU hpre)
      change e (e.symm x) ∈ originLateralChart (c * ρ) at h
      simpa only [e.apply_symm_apply] using h
    have heq (ω : Ω) (j : Fin m) : (∫ x, f j x ∂(F ω).map (fun x : ℂ => (c : ℂ) * x)) =
        ∫ x, f j (c * x) ∂F ω :=
      integral_map hs.aemeasurable (f j).continuous.aestronglyMeasurable
    simp_rw [heq]
    exact (originRadialRemovedGMC_dilation_test_vector_law P X Xc hX hc hm hcont
      ρ c γ hρ hcpos hγ hγ2 M hM K hK hKU f hfc hfV
      (fun j x hx => image_eq_zero_of_notMem_tsupport fun h => hx (mem_iUnion.2 ⟨j, h⟩))
      (fun j => (hfc j).comp_homeomorph e) (fun j => (hgK j).trans hKU)).symm
  have hmap : P.map (fun ω => (F ω).map (fun x : ℂ => (c : ℂ) * x)) = P.map F := by
    refine lat_law_of_annular_open_fdd _ F hN hF hNf hFf fun ι _ U hU => ?_
    classical
    let e := (Fintype.equivFin ι).symm
    let q (n : ℕ) (j : Fin (Fintype.card ι)) := gmcOpenApprox (U (e j)) (hU (e j)).1 n
    have hqc (n : ℕ) (j : Fin (Fintype.card ι)) : HasCompactSupport (q n j : ℂ → ℝ) :=
      (hU (e j)).2.1.of_isClosed_subset (isClosed_tsupport _) (openApprox_tsupport_sub _ _ n)
    have hqz (n : ℕ) (j : Fin (Fintype.card ι)) : (0 : ℂ) ∉ tsupport (q n j : ℂ → ℝ) :=
      fun h => (hU (e j)).2.2 (openApprox_tsupport_sub _ _ n h)
    have hct_ae {G : Ω → Measure ℂ} (hG : AEMeasurable G P)
        (hGf : ∀ ω K, IsCompact K → (0 : ℂ) ∉ K → G ω K < ⊤) (n : ℕ) (j : Fin (Fintype.card ι)) :
        AEMeasurable (fun ω => ∫ x, q n j x ∂G ω) P := by
      let K := tsupport (q n j : ℂ → ℝ)
      have hK : MeasurableSet K := (isClosed_tsupport _).measurableSet
      have he (ω : Ω) : (∫ x, q n j x ∂(G ω).restrict K) = ∫ x, q n j x ∂G ω :=
        integral_restrict_of_zero_outside _ K hK _ fun _ hx => image_eq_zero_of_notMem_tsupport hx
      simpa only [he] using finiteMeasure_bcf_integral_aemeasurable P (fun ω => (G ω).restrict K)
        ((measurable_measure_restrict K hK).comp_aemeasurable hG)
        (fun ω => ⟨by rw [Measure.restrict_apply_univ]; exact hGf ω K (hqc n j) (hqz n j)⟩) (q n j)
    have hlim_pt (μ : Measure ℂ) (j : Fin (Fintype.card ι))
        (hμ : μ (closure (U (e j))) < ⊤) :
        Tendsto (fun n => ∫ x, q n j x ∂μ) atTop (𝓝 ((μ (U (e j))).toReal)) := by
      let : IsFiniteMeasure (μ.restrict (closure (U (e j)))) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hμ⟩
      have he (n : ℕ) := integral_restrict_of_zero_outside μ (closure (U (e j)))
        isClosed_closure.measurableSet (q n j) fun _ hx => image_eq_zero_of_notMem_tsupport
          fun h => hx (openApprox_tsupport_sub (U (e j)) (hU (e j)).1 n h)
      have hm : μ.restrict (closure (U (e j))) (U (e j)) = μ (U (e j)) := by
        rw [Measure.restrict_apply (hU (e j)).1.measurableSet, inter_eq_left.2 subset_closure]
      simpa only [q, he, hm] using gmcOpenApprox_integral_tendsto (μ.restrict (closure (U (e j)))) _ (hU (e j)).1
    let A (ω : Ω) (j : Fin (Fintype.card ι)) := (((F ω).map (fun x : ℂ => (c : ℂ) * x)) (U (e j))).toReal
    let B (ω : Ω) (j : Fin (Fintype.card ι)) := (F ω (U (e j))).toReal
    have hA : AEMeasurable A P := AEMeasurable.of_eval fun j =>
      ((Measure.measurable_coe (hU (e j)).1.measurableSet).comp_aemeasurable hN).ennreal_toReal
    have hB : AEMeasurable B P := AEMeasurable.of_eval fun j =>
      ((Measure.measurable_coe (hU (e j)).1.measurableSet).comp_aemeasurable hF).ennreal_toReal
    have hlaw : P.map A = P.map B := gmc_limit_test_vector_law
      (fun n ω j => ∫ x, q n j x ∂(F ω).map (fun x : ℂ => (c : ℂ) * x))
      (fun n ω j => ∫ x, q n j x ∂F ω) A B
      (fun n => AEMeasurable.of_eval fun j => hct_ae hN (fun ω => (hNf ω).2) n j)
      (fun n => AEMeasurable.of_eval fun j => hct_ae hF (fun ω => (hFf ω).2) n j)
      hA hB (fun n => htest (q n) (hqc n) (hqz n))
      (fun j => tendstoInMeasure_of_tendsto_ae (fun n => (hct_ae hN (fun ω => (hNf ω).2) n j).aestronglyMeasurable)
        (ae_of_all _ fun ω => hlim_pt _ j ((hNf ω).2 _ (hU (e j)).2.1 (hU (e j)).2.2)))
      (fun j => tendstoInMeasure_of_tendsto_ae (fun n => (hct_ae hF (fun ω => (hFf ω).2) n j).aestronglyMeasurable)
        (ae_of_all _ fun ω => hlim_pt _ j ((hFf ω).2 _ (hU (e j)).2.1 (hU (e j)).2.2)))
    let post (v : Fin (Fintype.card ι) → ℝ) (j : ι) := ENNReal.ofReal (v (e.symm j))
    have hp : Measurable post := by fun_prop
    have heA : post ∘ A = fun ω j => ((F ω).map (fun x : ℂ => (c : ℂ) * x)) (U j) := by
      funext ω j
      simp only [post, A, Function.comp_apply, Equiv.apply_symm_apply]
      exact ENNReal.ofReal_toReal ((measure_mono subset_closure).trans_lt ((hNf ω).2 _ (hU j).2.1 (hU j).2.2)).ne
    have heB : post ∘ B = fun ω j => F ω (U j) := by
      funext ω j
      simp only [post, B, Function.comp_apply, Equiv.apply_symm_apply]
      exact ENNReal.ofReal_toReal ((measure_mono subset_closure).trans_lt ((hFf ω).2 _ (hU j).2.1 (hU j).2.2)).ne
    rw [← heA, ← AEMeasurable.map_map_of_aemeasurable hp.aemeasurable hA, hlaw,
      AEMeasurable.map_map_of_aemeasurable hp.aemeasurable hB, heB]
  have hproj := Measure.measurable_map _ hr
  have h := congrArg (fun μ : Measure (Measure ℂ) => μ.map (fun ν => ν.map (fun x : ℂ => -Real.log ‖x‖))) hmap
  rw [AEMeasurable.map_map_of_aemeasurable hproj.aemeasurable hN,
    AEMeasurable.map_map_of_aemeasurable hproj.aemeasurable hF] at h
  have he (ω : Ω) : ((F ω).map (fun x : ℂ => (c : ℂ) * x)).map (fun x : ℂ => -Real.log ‖x‖) =
      (lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)).map (fun s : ℝ => s + t) := by
    rw [logRadiusProjection_dilation (F ω) (originRadialRemovedGMC_origin γ _ _) c hcpos]
    change (lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)).map _ = _
    congr 1; funext s; simp [c]
  change P.map (fun ω => ((F ω).map (fun x : ℂ => (c : ℂ) * x)).map (fun x : ℂ => -Real.log ‖x‖)) =
    P.map (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) at h
  simpa only [he] using h

end DOZZ.Proofs
