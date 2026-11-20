module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.WeakSections.SupportAndMultiplication
public import DedekindZetaZeroFree.Analysis.EllipticEquations.Regularity.IntegerOrderEstimateTransfer

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorFormWeakLocalization
open KPContSectorLineL2Isometry KPContActualSectorSmoothTestModules
open KPContActualSectorTestDifferentialDescent
open KPContSectorScalarLineAlgebra KPContSectorCoveredQuotientVocabulary
open KPContActualSectorTestEmbeddings
open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentOverlapRationalBranches
open KPContActualCotangentMeasurableFamilies KPContActualCotangentPieceHilbertSum
open KPContActualSectorChartEquivariantInputs KPContLocalNorm
open KPContActualCotangentChartRestriction

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

 section

variable (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ) (hη : Measurable η) (B : ℝ) (hB : ∀ x, |η x| ≤ B)
    (s : BorelL2Sections F ζ hζ U R P H)

def actualBorelProduct : BorelL2Sections F ζ hζ U R P H := by
  let v := scalarRepresentative F ζ hζ U R P H s.val
  let f : GenuineCoveredScalars F ζ hζ U :=
    ⟨fun x => (η (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x) : ℂ) * v.val x, by
      intro ε x
      simp only [q_z, v.property ε x]
      ring⟩
  have hf :=
    ((Complex.measurable_ofReal.comp hη).comp ((KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U).measurable)).mul
      ((borel_iff F ζ hζ U R P H s.val).mp s.property.1)
  have hlp : MemLp f.val 2 (KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U) := by
    refine (representative_memLp F ζ hζ U R P H s).of_le_mul hf.aestronglyMeasurable
      (c := B) (Filter.Eventually.of_forall (fun x => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  exact borelS F ζ hζ U R P H ⟨f, hf, hlp⟩

private theorem actualBorelProduct_coefficient (a : ActualChart (U := U) (H := H))
    (y : a.domain) :
    (a.coefficient (actualBorelProduct η hη B hB s).val y : ℂ) =
      (η (a.toBase y) : ℂ) * (a.coefficient s.val y : ℂ) := by
  change (S F ζ hζ U R P H ⟨_,_⟩ a.component).val y.val = _
  rw [S_apply]
  change (η (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U (Quotient.mk _
      (y.val, (H.atlas U).representative a.component))) : ℂ) *
    (scalarRepresentative F ζ hζ U R P H s.val).val
      (Quotient.mk _ (y.val, (H.atlas U).representative a.component)) = _
  rw [q_mk]
  have he := congrArg (fun t : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H =>
      (t a.component).val y.val)
    ((S F ζ hζ U R P H).apply_symm_apply s.val)
  rw [S_apply] at he
  change (scalarRepresentative F ζ hζ U R P H s.val).val
    (Quotient.mk _ (y.val, (H.atlas U).representative a.component)) = _ at he
  rw [he]
  congr 2

end

private alias continuous_labeledA_self := DedekindZetaZeroFree.KPContActualGlobalGreen.continuous_labeledA_actual
private theorem isOpen_omega (a : ActualChart (U := U) (H := H)) : IsOpen (omega a) :=
  a.domain_open.preimage continuous_labeledA_self

private lemma q_coordinates (a : ActualChart (U := U) (H := H)) (y : a.domain) :
    q a (coordinates a y).val = a.toBase y := by apply @DedekindZetaZeroFree.KPContActualGlobalGreen.q_coordinates <;> assumption
private alias continuous_iff_isQuotientMap := DedekindZetaZeroFree.KPContActualSectorMultiplier.CompactCutoffDifferentialBounds.continuous_iff_isQuotientMap
private alias continuous_of_all_lifts := DedekindZetaZeroFree.KPContActualSectorMultiplier.CompactCutoffDifferentialBounds.continuous_of_all_lifts
private alias cutoff_continuous := DedekindZetaZeroFree.KPContActualSectorMultiplier.CompactCutoffDifferentialBounds.cutoff_continuous
private theorem smooth_liftExtension {a : ActualChart (U := U) (H := H)} {f : omega a → ℂ}
    (hf : SmoothOnLift a f) : ContDiffOn ℝ (⊤ : ℕ∞) (liftExtension a f) (omega a) := by apply @DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization.WeakGradientLocalization.smooth_liftExtension <;> assumption

private theorem smooth_differential {a : ActualChart (U := U) (H := H)} {f : omega a → ℂ}
    (hf : SmoothOnLift a f) : SmoothOnLift a (fun x => CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (liftExtension a f) x.val)) := by
  refine ⟨fun x => CotangentLogCoframe.j (d F)
    (HyperbolicChart.differential (d F) (liftExtension a f) x), ?_, fun _ => rfl⟩
  rw [contDiffOn_piLp]
  rintro ⟨i, k⟩
  have hcd (k : Fin 3) : ContDiffOn ℝ (⊤ : ℕ∞)
      (HyperbolicChart.coordinateDerivative (d F) i k (liftExtension a f)) (omega a) :=
    ((smooth_liftExtension hf).fderiv_of_isOpen (isOpen_omega a) (by simp)).clm_apply contDiffOn_const
  have hexp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : M F => (Real.exp (x (i, 2)) : ℂ)) (omega a) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.exp.contDiffOn)
  fin_cases k
  · simpa [CotangentLogCoframe.j, HyperbolicChart.differential] using hcd 2
  · simpa [CotangentLogCoframe.j, HyperbolicChart.differential] using hexp.mul (hcd 0)
  · simpa [CotangentLogCoframe.j, HyperbolicChart.differential] using hexp.mul (hcd 1)

private alias measurable_smooth := DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus.ScalarDifferentialDescent.measurable_smooth

private alias differential_frame := DedekindZetaZeroFree.KPContActualSectorMultiplier.CompactCutoffDifferentialBounds.differential_frame

private alias differential_frame_sum := DedekindZetaZeroFree.KPContActualSectorMultiplier.CompactCutoffDifferentialBounds.differential_frame_sum

private alias differential_arrow_const := DedekindZetaZeroFree.KPContActualSectorMultiplier.CompactCutoffDifferentialBounds.differential_arrow_const

private alias smooth_ofReal := DedekindZetaZeroFree.KPContActualSectorMultiplier.CompactCutoffDifferentialBounds.smooth_ofReal

private theorem differentiable_liftExtension {a : ActualChart (U := U) (H := H)}
    {f : omega a → ℂ} (hf : SmoothOnLift a f) (x : omega a) :
    DifferentiableAt ℝ (liftExtension a f) x.val :=
  ((smooth_liftExtension hf).differentiableOn (by simp) x.val x.property).differentiableAt
    ((isOpen_omega a).mem_nhds x.property)

private alias sectionFields_apply := DedekindZetaZeroFree.KPContActualSectorCoordinateNullEquivalence.CoordinateNullEquivalence.sectionFields_apply_actual

private theorem section_compatible (s : KPContSectorSmoothFramesSupport.Sections F ζ hζ U R P H) :
    ScalarCompatible (sectionFields s) := by
  constructor
  · intro a γ x hx
    exact (unitary_phase (isotropyArrow a γ)).2.2.2 s x (omega_subset_larger a hx)
  · intro a b e x hx
    obtain ⟨hab, arr, hsource, htarget, hlarger⟩ := e
    cases a with
    | mk i ca oa da dao dac das dai =>
      cases b with
      | mk j cb ob db dbo dbc dbs dbi =>
        dsimp at hab
        subst j
        exact (unitary_phase arr).2.2.2 s x hx

private theorem measurable_sectionFields
    (s : BorelL2Sections F ζ hζ U R P H) (a : ActualChart (U := U) (H := H)) :
    Measurable (sectionFields s.val a) := by
  rw [(funext (sectionFields_apply s.val a))]
  exact (s.property.1 a.component).comp
    (continuous_labeledA_self.measurable.comp measurable_subtype_coe)

private alias q_isotropy := DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus.ScalarDifferentialDescent.q_isotropy

private theorem q_branch {a b : ActualChart (U := U) (H := H)} (e : ActualBranch a b)
    (x : M F) : q b (e.arrow.psi x) = q a x := by apply @DedekindZetaZeroFree.KPContActualFinitePartitionError.q_actualBranch <;> assumption

 section

variable (η : RealSmoothCutoff F ζ hζ U R P H)

theorem cutoff_gradient
    (s : BorelL2Sections F ζ hζ U R P H) :
    IsMeasurableCotangentFamily (fun a x => sectionFields s.val a x • CotangentLogCoframe.j (d F)
      (HyperbolicChart.differential (d F) (liftExtension a (fun y => (η.val (q a y.val) : ℂ))) x.val)) := by
  let u : ScalarFields F ζ hζ U R P H := fun a y => (η.val (q a y.val) : ℂ)
  have hu a : SmoothOnLift a (u a) := smooth_ofReal (η.smooth a)
  refine ⟨fun a => (measurable_sectionFields s a).smul
    (measurable_smooth (smooth_differential (hu a))), ?_, ?_⟩
  · intro a γ x hx
    have hd := differential_arrow_const (isotropyArrow a γ) 1 (liftExtension a (u a)) (liftExtension a (u a))
      x (omega_subset_larger a hx) (differentiable_liftExtension (hu a) ⟨x, hx⟩)
      (differentiable_liftExtension (hu a) ⟨_, isotropy_mem a γ x hx⟩) (by
        filter_upwards [(isOpen_omega a).mem_nhds hx] with y hy
        simp [liftExtension, u, hy, isotropy_mem a γ y hy, q_isotropy])
    change sectionFields s.val a ⟨_, _⟩ • _ = _
    rw [hd, one_smul, (section_compatible s.val).1 a γ x hx]
    change _ = (isotropyArrow a γ).phase x •
      KPContCotangentRealOrthogonalComplexification.operatorComplexification _
        (Q (isotropyArrow a γ) x) (sectionFields s.val a ⟨x, hx⟩ • _)
    rw [map_smul, smul_smul]
  · intro a b e x hx
    have hd := differential_arrow_const e.arrow 1 (liftExtension a (u a)) (liftExtension b (u b)) x hx
      (differentiable_liftExtension (hu a) ⟨x, e.source_shrinking hx⟩)
      (differentiable_liftExtension (hu b) ⟨_, e.target_shrinking hx⟩) (by
        filter_upwards [e.arrow.isOpen_domain.mem_nhds hx] with y hy
        simp [liftExtension, u, e.source_shrinking hy, e.target_shrinking hy, q_branch])
    change sectionFields s.val b ⟨_, _⟩ • _ = _
    rw [hd, one_smul, (section_compatible s.val).2 a b e x hx]
    change _ = e.arrow.phase x •
      KPContCotangentRealOrthogonalComplexification.operatorComplexification _
        (Q e.arrow x) (sectionFields s.val a ⟨x, e.source_shrinking hx⟩ • _)
    rw [map_smul, smul_smul]

 theorem cutoff_family
    (W : Family (U := U) (H := H)) :
    IsMeasurableCotangentFamily (fun a x => cutoffLift η a x • coefficient W a x) := by
  refine ⟨fun a => (measurable_smooth (smooth_ofReal (η.smooth a))).smul
    (W.property.1 a), ?_, ?_⟩
  · intro a γ x hx
    simp only [cutoffLift, coefficient]
    rw [q_isotropy, W.property.2.1 a γ x hx, map_smul]
  · intro a b e x hx
    simp only [cutoffLift, coefficient]
    rw [q_branch, W.property.2.2 a b e x hx, map_smul]

 def productFamily
    (s : BorelL2Sections F ζ hζ U R P H) (W : Family (U := U) (H := H)) :
    Family (U := U) (H := H) :=
  (⟨fun a x => cutoffLift η a x • coefficient W a x, cutoff_family η W⟩ : Family) +
    ⟨fun a x => sectionFields s.val a x • cutoffDifferential η a x, cutoff_gradient η s⟩

end

private alias base_direction := DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization.WeakGradientLocalization.base_direction
private alias decoder_differential := DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization.WeakGradientLocalization.decoder_differential

private alias flattened_differential := DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization.WeakGradientLocalization.flattened_differential

private alias coordinateDomain_isOpen := DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization.WeakGradientLocalization.coordinateDomain_isOpen

private alias smooth_liftExtension_flat := DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization.WeakGradientLocalization.smooth_liftExtension

private alias smooth_flattened := DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization.WeakGradientLocalization.smooth_flattened

 section

variable {n : ℕ} (B : LocalBall n) (b : Space n → ℂ) (hb : MemLp b ⊤ (volume.restrict B.carrier))

def mulBall : BallL2 B →L[ℂ] BallL2 B :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (volume.restrict B.carrier) ⊤ 2 2 (hb.toLp b)
 theorem mulBall_ae (u : BallL2 B) :
    (fun x => mulBall B b hb u x) =ᵐ[volume.restrict B.carrier] (fun x => b x * u x) := by apply @DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization.WeakGradientLocalization.mulBall_ae <;> assumption

end
 alias memLp_top_on_ball := DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization.WeakGradientLocalization.memLp_top_on_ball

private theorem smooth_cutoff_flat (η : CompactMultiplier (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (multiplierCoordinate η a) (coordinateDomain a) := by apply @DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization.WeakGradientLocalization.smooth_cutoff_flat <;> assumption

 section

variable (x : Space (3*d F)) (j : Fin (3*d F))

def decode (v : KPContCotangentActualGenuineTwistIsotropy.E F) : ℂ :=
  let p := (baseReindex (F := F)).symm x
  let ik := (coefficientIndex (F := F)).symm j
  ![(Real.exp (-p (ik.1,2)) : ℂ) * v (ik.1,1),
    (Real.exp (-p (ik.1,2)) : ℂ) * v (ik.1,2), v (ik.1,0)] ik.2

private theorem decode_add_smul
    (b c : ℂ) (v w : KPContCotangentActualGenuineTwistIsotropy.E F) :
    decode x j (b • v + c • w) = b * decode x j v + c * decode x j w := by apply @DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization.WeakGradientLocalization.decode_add_smul <;> assumption

end

 def cutoffPartial (η : CompactMultiplier (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (j : Fin (3*d F)) (x : Space (3*d F)) : ℂ :=
  fderiv ℝ (multiplierCoordinate η a) x (EuclideanSpace.single j 1)

private theorem cutoffPartial_decode (η : CompactMultiplier (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (j : Fin (3*d F))
    (x : Space (3*d F)) (hx : x ∈ coordinateDomain a) :
    cutoffPartial η a j x = decode x j
      (cutoffDifferential η.val a ⟨(baseReindex (F := F)).symm x, hx⟩) := by apply @DedekindZetaZeroFree.KPContActualSectorFormWeakLocalization.WeakGradientLocalization.cutoffPartial_decode <;> assumption

 theorem index_cases {n : ℕ} (α : MultiIndex n 1) :
    α = zeroIndex n ∨ ∃ i : Fin n, α = KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex i := by
  by_cases hz : ∀ i, (α.val i).val = 0
  · left
    apply Subtype.ext
    funext i
    exact Fin.ext (hz i)
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    right
    refine ⟨i, ?_⟩
    have hone : (α.val i).val = 1 := by omega
    apply Subtype.ext
    funext j
    apply Fin.ext
    by_cases hji : j = i
    · subst j; simpa [KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex] using hone
    · have hj : (α.val j).val = 0 := by
        have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => (α.val i).val)
          (show ({i,j} : Finset (Fin n)) ⊆ Finset.univ from Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
        simp [Finset.sum_pair (Ne.symm hji), hone] at hsum
        omega
      simpa [KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, hji] using hj
open WeakJets.Raw
 alias counts_first := DedekindZetaZeroFree.WeakJets.Raw.MultiIndexLeibnizRule.counts_first

 section

variable {n : ℕ} (B : LocalBall n) (Ω : Set (Space n)) (hΩ : IsOpen Ω)
    (hB : IsCompact (closure B.carrier) ∧ closure B.carrier ⊆ Ω) (b : Space n → ℂ)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b Ω) (u : IntegerSobolev B 1)

def multipliedSobolev : IntegerSobolev B 1 := by
  let db := fun j x => fderiv ℝ b x (EuclideanSpace.single j 1)
  have hpartial j : ContinuousOn (db j) Ω :=
    ((hb.fderiv_of_isOpen hΩ (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffOn_const).continuousOn
  let M := mulBall B b (memLp_top_on_ball B Ω hΩ hB b hb.continuousOn)
  let N := fun j => mulBall B (db j) (memLp_top_on_ball B Ω hΩ hB _ (hpartial j))
  let pick := fun α : MultiIndex n 1 => α.directions.headD ⟨0, B.dimension_pos⟩
  let v := fun α : MultiIndex n 1 => if α = zeroIndex n then M (u.derivatives α)
    else M (u.derivatives α) + N (pick α) (u.derivatives (zeroIndex n))
  have hzero : v (zeroIndex n) = M (u.derivatives (zeroIndex n)) := by simp [v]
  have hfirst j : v (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j) =
      M (u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j)) +
        N j (u.derivatives (zeroIndex n)) := by
    have hn : KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j ≠ zeroIndex n := by
      intro h
      have he := congrArg (fun α : MultiIndex n 1 => (α.val j).val) h
      simp [KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, zeroIndex] at he
    simp [v, hn, pick, KPContLocalEnergy.SobolevEnergyEstimates.firstIndex_directions]
  refine ⟨v, ?_⟩
  intro α
  change IsWeakDerivative B α (v (zeroIndex n)) (v α)
  rcases index_cases α with rfl | ⟨j, rfl⟩
  · intro φ
    have hd : (zeroIndex n).directions = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro i hi
      simp [zeroIndex]
    simp only [coordinateDerivative, hd, coordinateDerivativeList]
    have hdeg : (zeroIndex n).degree = 0 := by simp [MultiIndex.degree, zeroIndex]
    rw [hdeg]
    simp
  · intro φ
    change (∫ x in B.carrier, v (zeroIndex n) x *
      coordinateDerivative (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j) (fun y => φ y) x) = _
    rw [hzero, hfirst]
    have hjet : jet u (unitCount j) = u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j) := by
      rw [← counts_first, jet_index]
    have hw := weak_product_rule_first u 0 j (by
      simp [unitCount]) (hb.mono (subset_closure.trans hB.2)) φ
    simp only [zero_add, jet_zero, hjet] at hw
    simp only [IsWeakDerivative, coordinateDerivative,
      KPContLocalEnergy.SobolevEnergyEstimates.firstIndex_directions]
    have hdegree : (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j).degree = 1 := by
      simp only [MultiIndex.degree, KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex,
        apply_ite Fin.val, Fin.val_one, Fin.val_zero]
      simp
    rw [hdegree, pow_one, neg_one_mul]
    calc
      _ = ∫ x in B.carrier, b x * u.derivatives (zeroIndex n) x *
          coordinateDerivativeList [j] (fun y => φ y) x := by
        apply integral_congr_ae
        filter_upwards [mulBall_ae B b _ (u.derivatives (zeroIndex n))] with x hx
        rw [hx]
      _ = -(∫ x in B.carrier, (db j x * u.derivatives (zeroIndex n) x +
          b x * u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j) x) * φ x) := hw
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (M (u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j)))
          (N j (u.derivatives (zeroIndex n))),
          mulBall_ae B b _ (u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j)),
          mulBall_ae B (db j) _ (u.derivatives (zeroIndex n))] with x h1 h2 h3
        rw [h1]
        change (_ + _) * φ x = (M _ x + N j _ x) * φ x
        change M _ x = _ at h2
        change N j _ x = _ at h3
        rw [h2, h3, add_comm]

private theorem multipliedSobolev_zero :
    (fun x => (multipliedSobolev B Ω hΩ hB b hb u).derivatives (zeroIndex n) x)
      =ᵐ[volume.restrict B.carrier] fun x => b x * u.derivatives (zeroIndex n) x := by
  simp only [multipliedSobolev, ↓reduceIte]
  exact mulBall_ae B b _ _

private theorem multipliedSobolev_first (j : Fin n) :
    (fun x => (multipliedSobolev B Ω hΩ hB b hb u).derivatives
      (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j) x) =ᵐ[volume.restrict B.carrier]
      fun x => b x * u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j) x +
        fderiv ℝ b x (EuclideanSpace.single j 1) * u.derivatives (zeroIndex n) x := by
  have hn : KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j ≠ zeroIndex n := by
    intro h
    have he := congrArg (fun α : MultiIndex n 1 => (α.val j).val) h
    simp [KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, zeroIndex] at he
  simp only [multipliedSobolev, hn, ↓reduceIte, KPContLocalEnergy.SobolevEnergyEstimates.firstIndex_directions,
    List.headD_cons]
  let N := mulBall B (fun x => fderiv ℝ b x (EuclideanSpace.single j 1))
    (memLp_top_on_ball B Ω hΩ hB _
      ((hb.fderiv_of_isOpen hΩ (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffOn_const).continuousOn)
  filter_upwards [Lp.coeFn_add ((mulBall B b (memLp_top_on_ball B Ω hΩ hB b hb.continuousOn)) (u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j)))
      (N (u.derivatives (zeroIndex n))), mulBall_ae B b _
      (u.derivatives (KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j)),
    mulBall_ae B (fun x => fderiv ℝ b x (EuclideanSpace.single j 1)) _
      (u.derivatives (zeroIndex n))] with x h1 h2 h3
  rw [h1]
  simp only [Pi.add_apply]
  rw [h2, h3]

end

private theorem actualBorelProduct_fields
    (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : Measurable η) (B : ℝ) (hB : ∀ x, |η x| ≤ B)
    (s : BorelL2Sections F ζ hζ U R P H) (a : ActualChart (U := U) (H := H))
    (x : omega a) :
    sectionFields (actualBorelProduct η hη B hB s).val a x =
      (η (q a x.val) : ℂ) * sectionFields s.val a x := by
  rw [sectionFields_apply, sectionFields_apply]
  exact actualBorelProduct_coefficient η hη B hB s a ⟨_, x.property⟩

private theorem scalarCoordinate_product
    (η : CompactMultiplier (U := U) (H := H))
    (hη : Measurable η.val.val) (C : ℝ) (hC : ∀ x, |η.val.val x| ≤ C)
    (s : BorelL2Sections F ζ hζ U R P H) (a : ActualChart (U := U) (H := H))
    (x : Space (3*d F)) (hx : x ∈ coordinateDomain a) :
    scalarCoordinate (actualBorelProduct η.val.val hη C hC s) a x =
      multiplierCoordinate η a x * scalarCoordinate s a x := by
  simp only [scalarCoordinate, multiplierCoordinate, liftExtension, dite_eq_left (show (baseReindex).symm x ∈ omega a from hx)]
  exact actualBorelProduct_fields η.val.val hη C hC s a ⟨_, hx⟩

private theorem covariantCoordinate_product
    (η : CompactMultiplier (U := U) (H := H))
    (s : BorelL2Sections F ζ hζ U R P H) (W : Family (U := U) (H := H))
    (a : ActualChart (U := U) (H := H)) (x : Space (3*d F))
    (hx : x ∈ coordinateDomain a) (j : Fin (3*d F)) :
    covariantCoordinate (productFamily η.val s W) a x j =
      multiplierCoordinate η a x * covariantCoordinate W a x j +
        cutoffPartial η a j x * scalarCoordinate s a x := by
  have hdecode (Z : Family) : covariantCoordinate Z a x j =
      decode x j (coefficient Z a ⟨(baseReindex).symm x, hx⟩) := by
    simp only [covariantCoordinate, decode, liftExtension, dite_eq_left (show (baseReindex).symm x ∈ omega a from hx)]
  rw [hdecode, hdecode]
  have hc : coefficient (productFamily η.val s W) a ⟨(baseReindex).symm x, hx⟩ =
      cutoffLift η.val a ⟨_, hx⟩ • coefficient W a ⟨_, hx⟩ +
        sectionFields s.val a ⟨_, hx⟩ • cutoffDifferential η.val a ⟨_, hx⟩ := rfl
  rw [hc, decode_add_smul, ← (cutoffPartial_decode η a j x hx)]
  simp only [multiplierCoordinate, scalarCoordinate, liftExtension, dite_eq_left (show (baseReindex).symm x ∈ omega a from hx)]
  ring

private theorem product_weakChartData
    (η : CompactMultiplier (U := U) (H := H))
    (hη : Measurable η.val.val) (C : ℝ) (hC : ∀ x, |η.val.val x| ≤ C)
    (s : BorelL2Sections F ζ hζ U R P H) (W : Family (U := U) (H := H))
    (hw : WeakChartData s W) :
    WeakChartData (actualBorelProduct η.val.val hη C hC s) (productFamily η.val s W) := by
  intro a B hB ε
  obtain ⟨h, hzero, hfirst⟩ := hw a B hB ε
  refine ⟨(multipliedSobolev B (coordinateDomain a) (coordinateDomain_isOpen a) hB
    (multiplierCoordinate η a) (smooth_cutoff_flat η a) h), ?_, ?_⟩
  · filter_upwards [multipliedSobolev_zero B (coordinateDomain a) (coordinateDomain_isOpen a) hB
      (multiplierCoordinate η a) (smooth_cutoff_flat η a) h,
      hzero, ae_restrict_mem B.toOpens.isOpen.measurableSet] with x hv hx hmem
    rw [hv, hx, scalarCoordinate_product η hη C hC s a x (hB.2 (subset_closure hmem))]
    ring
  · intro α j hj
    have hα : α = KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j := by
      rcases index_cases α with hα | ⟨k, hα⟩
      · simp [hα, zeroIndex] at hj
      · have hkj : j = k := by
          by_contra hn
          simp [hα, KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex, hn] at hj
        simpa [hkj] using hα
    subst α
    have hj' : ((KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex j).val j).val = 1 := by
      simp [KPContLocalEnergy.SobolevEnergyEstimates.Raw.firstIndex]
    filter_upwards [multipliedSobolev_first B (coordinateDomain a) (coordinateDomain_isOpen a) hB
        (multiplierCoordinate η a) (smooth_cutoff_flat η a) h j,
      hzero, hfirst _ j hj', ae_restrict_mem B.toOpens.isOpen.measurableSet] with x hv h0 h1 hx
    rw [hv, h0, h1, covariantCoordinate_product η s W a x (hB.2 (subset_closure hx)) j]
    dsimp [cutoffPartial]
    ring

private theorem actualBorelProduct_supported
    (η : CompactMultiplier (U := U) (H := H))
    (hη : Measurable η.val.val) (C : ℝ) (hC : ∀ x, |η.val.val x| ≤ C)
    (s : BorelL2Sections F ζ hζ U R P H) (x : KPFiniteCuspAtlas.rawXU F ζ hζ U)
    (hx : x ∉ tsupport η.val.val) :
    squaredNorm F ζ hζ U R P H (actualBorelProduct η.val.val hη C hC s).val x = 0 := by
  obtain ⟨y, rfl⟩ := KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U x
  unfold squaredNorm
  change ENNReal.ofReal
    (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ U R P H
      (S F ζ hζ U R P H ⟨_, _⟩) (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U y) ^ 2) = 0
  rw [KPContSectorSmoothFramesSupport.sectionNorm_pullback]
  simp [(image_eq_zero_of_notMem_tsupport hx)]

theorem compactMultiplier_product_weakH1
    (η : CompactMultiplier (U := U) (H := H))
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (hweak : ActualWeakH1Loc (H := H) u) :
    ∃ v : KPContSectorClosedLpSubspace.H F ζ hζ R U,
      IsActualProduct η u v ∧ ActualWeakH1Loc (H := H) v ∧
      ∃ L : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), IsCompact L ∧ SupportedAE (H := H) v L := by
  obtain ⟨s, W, hs, hw⟩ := hweak
  obtain ⟨C, D, hC0, hD0, hC, hD⟩ := (KPContActualSectorMultiplier.compactCutoff_bounds
    F ζ hζ U R P H η.val η.property)
  have hη := (cutoff_continuous η.val).measurable
  let t := actualBorelProduct η.val.val hη C hC s
  let v := (sectorLineIsometry F ζ hζ U R P H).symm (mk F ζ hζ U R P H t)
  have hv : sectorLineIsometry F ζ hζ U R P H v = mk F ζ hζ U R P H t :=
    (sectorLineIsometry F ζ hζ U R P H).apply_symm_apply _
  refine ⟨v, ⟨s, t, hs, hv, ?_⟩, ⟨t, productFamily η.val s W, hv, ?_⟩,
    tsupport η.val.val, η.property, t, hv, ?_⟩
  · intro a
    exact Filter.Eventually.of_forall fun y =>
      actualBorelProduct_fields η.val.val hη C hC s a (coordinates a y)
  · exact product_weakChartData η hη C hC s W hw
  · exact Filter.Eventually.of_forall fun x hx => actualBorelProduct_supported η hη C hC s x hx

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

end
