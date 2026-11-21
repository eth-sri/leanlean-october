module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicQuotients.CuspEndCoordinates
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.LaplacianJets
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.ChartCoefficientAveraging
public import DedekindZetaZeroFree.Eisenstein.Continuation.IncomingCuspModes.JetSpatialSmoothness
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.MeanZeroEnergyTails

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section
open scoped Classical NumberField BigOperators ContDiff ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContThreeL2CompactBoundHelpers
private theorem clm_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (O : Set ℂ) (hO : IsOpen O) (j : ℂ → E) (hj : DifferentiableOn ℂ j O)
    (k : ℕ) (s : ℂ) (hs : s ∈ O) (L : E →L[ℂ] ℂ) :
    iteratedDerivWithin k (fun z => L (j z)) O s = L (iteratedDerivWithin k j O s) := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin]
  change ((iteratedFDerivWithin ℂ k (L ∘ j) O s) fun _ => 1) = _
  rw [L.iteratedFDerivWithin_comp_left ((hj.contDiffOn hO (n := (⊤ : ℕ∞ω))).contDiffWithinAt hs) hO.uniqueDiffOn hs (by simp)]
  rfl
open KPContLocalNorm

private theorem tuple_parameter_jet_joint {n m : ℕ} (A : LocalBall n)
    (O : Set ℂ) (hO : IsOpen O) (v : ℂ → Space n → ℂ)
    (hv : KPCutoffSource.ChartSmoothHolomorphicOn A v O)
    (K : Set (Space n)) (hK : IsCompact K) (hKA : K ⊆ A.carrier)
    (k : ℕ) (α : MultiIndex n m) :
    ContinuousOn (fun p : ℂ × Space n => iteratedDerivWithin k
      (fun z => coordinateDerivative α (v z) p.2) O p.1) (O ×ˢ K) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨j,hj,he⟩ := hv.2 K hK hKA m
  have hc := (hj.contDiffOn hO (n := (⊤ : ℕ∞ω))).continuousOn_iteratedDerivWithin
    (m := k) (by simp) hO.uniqueDiffOn
  have hp : ContinuousOn (fun z => (iteratedDerivWithin k j O z) α) O :=
    (continuous_apply α).comp_continuousOn hc
  have hcont : ContinuousOn (fun p : ℂ × K =>
      (iteratedDerivWithin k j O p.1) α p.2) (O ×ˢ Set.univ) :=
    continuous_eval.comp_continuousOn ((hp.comp continuous_fst.continuousOn
      (fun _ h => h.1)).prodMk continuous_snd.continuousOn)
  apply continuousOn_iff_continuous_restrict.mpr
  let a : (O ×ˢ K) → ℂ × K := fun p => (p.val.1, ⟨p.val.2,p.property.2⟩)
  have ha : Continuous a := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => p.property.2))
  apply (hcont.comp_continuous ha (fun p => ⟨p.property.1, Set.mem_univ _⟩)).congr
  intro p
  let ev : CompactJets K m →L[ℂ] ℂ :=
    (ContinuousMap.evalCLM ℂ (⟨p.val.2,p.property.2⟩ : K)).comp (ContinuousLinearMap.proj α)
  have heq : Set.EqOn (fun z => coordinateDerivative α (v z) p.val.2)
      (fun z => ev (j z)) O := fun z hz => (he z hz α ⟨p.val.2,p.property.2⟩).symm
  change _ = iteratedDerivWithin k (fun z => coordinateDerivative α (v z) p.val.2) O p.val.1
  rw [iteratedDerivWithin_congr heq p.property.1, clm_jet O hO j hj k p.val.1 p.property.1 ev]
  rfl

end DedekindZetaZeroFree.KPContThreeL2CompactBoundHelpers

namespace DedekindZetaZeroFree.KPContActualChamberThreeL2Tails

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev V : Set ℂ := KPContActualChamberCasimirJets.V
abbrev level := KPContActualAllCuspSource.level F ζ hζ C R P H U
abbrev Base := KPContActualAllCuspSource.Base F ζ hζ C R P H U
abbrev Covered := KPContActualAllCuspSource.Covered F ζ hζ C R P H U
abbrev Sector := KPContActualAllCuspSource.Sector F ζ hζ C R P H U
abbrev Sections := KPContSectorSmoothFramesSupport.Sections F ζ hζ
  (level F ζ hζ C R P H U) R P H
abbrev SmoothSections := KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
abbrev BorelL2Sections := KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ
  (level F ζ hζ C R P H U) R P H
abbrev measure := KPContActualAllCuspSource.measure F ζ hζ C R P H U
abbrev baseMeasure := KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P
  (level F ζ hζ C R P H U)
abbrev Frame (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount) :=
  KPContActualChamberCasimirJets.Frame F ζ hζ C R P H U i


def tail (A : ℝ) : Set (Base F ζ hζ C R P H U) :=
  KPCuspCutoffGraph.highEnds F ζ hζ H.totallyComplex (level F ζ hζ C R P H U)
    (H.atlas (level F ζ hζ C R P H U)) A

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S)
variable {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)
variable (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U →
  KPCutoffSource.SmoothCuspCutoff T)
variable (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer
  KPContinuation.spectralDomain f χ)

def g (k : ℕ) (s : ℂ) (x : Covered F ζ hζ C R P H U) : ℂ :=
  iteratedDerivWithin k (fun z =>
    KPContActualChamberNormalSeries.E F ζ hζ U ι f z
      (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x) -
    KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff z) x) V s

def h (k : ℕ) (s : ℂ) (x : Covered F ζ hζ C R P H U) : ℂ :=
  iteratedDerivWithin k (fun z =>
    KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
      (source.descent.commutator z) x) V s

theorem genuine (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain) (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    g F ζ hζ C R P H U ι f buffer χ source k s ∈
      KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ (level F ζ hζ C R P H U) ∧
    h F ζ hζ C R P H U ι f buffer χ source k s ∈
      KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ (level F ζ hζ C R P H U) := by
  obtain ⟨eE, heE, -, -⟩ :=
    KPContActualChamberNormalSeries.descent_series F ζ hζ C R P H U ι f hι hf
  have hvalE : ∀ w ∈ V, ∀ x, (eE w).val x =
      KPContActualChamberNormalSeries.E F ζ hζ U ι f w
        (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x) := by
    intro w hw x
    rw [← heE w hw (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U x),
      KPContActualChamberNormalSeries.coveredRepresentative_projection]
  let eC : ℂ → KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ
      (level F ζ hζ C R P H U) := fun w =>
    ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ (level F ζ hζ C R P H U) R P H).symm
      (source.descent.cutoff w)).val
  have hvalC : ∀ w x, (eC w).val x = KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
      (source.descent.cutoff w) x := fun w x => rfl
  let eK : ℂ → KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ
      (level F ζ hζ C R P H U) := fun w =>
    ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ (level F ζ hζ C R P H U) R P H).symm
      (source.descent.commutator w)).val
  have hvalK : ∀ w x, (eK w).val x = KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
      (source.descent.commutator w) x := fun w x => rfl
  have hg : g F ζ hζ C R P H U ι f buffer χ source k s =
      fun v => iteratedDerivWithin k (fun z =>
        KPContActualChamberNormalSeries.E F ζ hζ U ι f z
          (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U v) -
        KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff z) v) V s := by
    funext v; rfl
  have hh : h F ζ hζ C R P H U ι f buffer χ source k s =
      fun v => iteratedDerivWithin k (fun z =>
        KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
          (source.descent.commutator z) v) V s := by
    funext v; rfl
  constructor
  · rw [hg]
    intro ε v
    simp only []
    have hsum : iteratedDerivWithin k (fun z =>
          KPContActualChamberNormalSeries.E F ζ hζ U ι f z
            (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
              (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) -
          KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff z)
            (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) V s =
        iteratedDerivWithin k (fun z =>
          (eE z).val (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v) -
          (eC z).val (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) V s :=
      iteratedDerivWithin_congr (fun z hz => by
        rw [← hvalE z hz (KPContSectorCoveredQuotientVocabulary.z F ζ hζ
              (level F ζ hζ C R P H U) ε v),
          ← hvalC z (KPContSectorCoveredQuotientVocabulary.z F ζ hζ
              (level F ζ hζ C R P H U) ε v)]) hs
    have hA : iteratedDerivWithin k (fun z =>
          (eE z).val (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v) -
          (eC z).val (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) V s =
        iteratedDerivWithin k (fun z =>
          (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
            ((eE z).val v - (eC z).val v)) V s :=
      iteratedDerivWithin_congr (fun z _ => by
        rw [(eE z).property ε v, (eC z).property ε v]; ring) hs
    have hcm : iteratedDerivWithin k (fun z =>
          (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
            ((eE z).val v - (eC z).val v)) V s =
        (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
          iteratedDerivWithin k (fun z => (eE z).val v - (eC z).val v) V s :=
      iteratedDerivWithin_const_mul_field _ _
    have hZ : iteratedDerivWithin k (fun z => (eE z).val v - (eC z).val v) V s =
        iteratedDerivWithin k (fun z =>
          KPContActualChamberNormalSeries.E F ζ hζ U ι f z
            (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U v) -
          KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.cutoff z) v) V s :=
      iteratedDerivWithin_congr (fun z hz => by rw [hvalE z hz v, hvalC z v]) hs
    rw [hsum, hA, hcm, hZ]
  · rw [hh]
    intro ε v
    simp only []
    have hsum : iteratedDerivWithin k (fun z =>
          KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (source.descent.commutator z)
            (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) V s =
        iteratedDerivWithin k (fun z =>
          (eK z).val (KPContSectorCoveredQuotientVocabulary.z F ζ hζ
            (level F ζ hζ C R P H U) ε v)) V s :=
      iteratedDerivWithin_congr (fun z _ => hvalK z
        (KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε v)) hs
    have hA : iteratedDerivWithin k (fun z =>
          (eK z).val (KPContSectorCoveredQuotientVocabulary.z F ζ hζ
            (level F ζ hζ C R P H U) ε v)) V s =
        iteratedDerivWithin k (fun z =>
          (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * (eK z).val v) V s :=
      iteratedDerivWithin_congr (fun z _ => (eK z).property ε v) hs
    have hcm : iteratedDerivWithin k (fun z =>
          (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) * (eK z).val v) V s =
        (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ ε : ℂ) *
          iteratedDerivWithin k (fun z => (eK z).val v) V s :=
      iteratedDerivWithin_const_mul_field _ _
    have hZ : iteratedDerivWithin k (fun z => (eK z).val v) V s =
        iteratedDerivWithin k (fun z =>
          KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
            (source.descent.commutator z) v) V s :=
      (iteratedDerivWithin_congr (fun z _ => hvalK z v) hs).symm
    rw [hsum, hA, hcm, hZ]

variable (hι : Function.Injective ι)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)

def coveredG (k : ℕ) (s : ℂ) :
    KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ (level F ζ hζ C R P H U) :=
  if hs : s ∈ V then ⟨_, (genuine F ζ hζ C R P H U ι f buffer χ source hι hf k s hs).1⟩ else 0

def coveredH (k : ℕ) (s : ℂ) :
    KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ (level F ζ hζ C R P H U) :=
  if hs : s ∈ V then ⟨_, (genuine F ζ hζ C R P H U ι f buffer χ source hι hf k s hs).2⟩ else 0

def lineG (k : ℕ) (s : ℂ) : Sections F ζ hζ C R P H U :=
  KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H
    (coveredG F ζ hζ C R P H U ι f buffer χ source hι hf k s)

def lineH (k : ℕ) (s : ℂ) : Sections F ζ hζ C R P H U :=
  KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H
    (coveredH F ζ hζ C R P H U ι f buffer χ source hι hf k s)

open KPContLocalNorm

private theorem point_holomorphic {n : ℕ} (A : LocalBall n) (Ω : Set ℂ)
    (g : ℂ → Space n → ℂ) (hg : KPCutoffSource.ChartSmoothHolomorphicOn A g Ω)
    (x : Space n) (hx : x ∈ A.carrier) : DifferentiableOn ℂ (fun s => g s x) Ω := by
  let K : Set (Space n) := {x}
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_singleton : IsCompact K)
  obtain ⟨j,hj,he⟩ := hg.2 K isCompact_singleton (Set.singleton_subset_iff.mpr hx) 0
  let α : MultiIndex n 0 := ⟨fun _ => 0,by simp⟩
  let L : CompactJets K 0 →L[ℂ] ℂ :=
    (ContinuousMap.evalCLM ℂ (⟨x,rfl⟩ : K)).comp (ContinuousLinearMap.proj α)
  apply (L.differentiable.comp_differentiableOn hj).congr
  intro s hs
  have h := he s hs α ⟨x,rfl⟩
  have hd : α.directions = [] := by
    simp only [MultiIndex.directions,α,List.replicate_zero]
    induction List.finRange n with
    | nil => rfl
    | cons i l ih => simpa using ih
  simpa [L,coordinateDerivative,hd,coordinateDerivativeList] using h.symm

private theorem realCoordinates_inverse_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (KPContActualChartRestrictionDensity.coordinates F).symm := by
  rw [contDiff_piLp]
  intro k
  dsimp [KPContActualChartRestrictionDensity.coordinates, KPArchRealCoordinates.coordinates]
  split_ifs
  · exact Complex.reCLM.contDiff.comp ((contDiff_apply ℝ (ℂ × ℝ) _).fst)
  · exact Complex.imCLM.contDiff.comp ((contDiff_apply ℝ (ℂ × ℝ) _).fst)
  · exact (contDiff_apply ℝ (ℂ × ℝ) _).snd

private theorem E_holo (hι : Function.Injective ι)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (x : KPContActualChamberNormalSeries.G F ζ hζ) :
    DifferentiableOn ℂ (fun s => KPContActualChamberNormalSeries.E F ζ hζ U ι f s x) V := by
  let A : Set (KPContActualChamberNormalSeries.G F ζ hζ) := {x}
  letI : CompactSpace A := isCompact_iff_compactSpace.mp isCompact_singleton
  have hh := KPContActualChamberNormalSeries.compactMixedJet_holomorphic F ζ hζ U ι f hι hf 0 [] A isCompact_singleton
  have hd := (ContinuousMap.evalCLM ℂ (⟨x, Set.mem_singleton x⟩ : A)).differentiable.comp_differentiableOn hh
  apply hd.congr
  intro s hs
  simp [KPContActualChamberNormalSeries.compactMixedJet, hs,
    KPContActualChamberNormalSeries.mixedJet, KPContActualChamberNormalSeries.rightWord]

private theorem source_chart_neighborhood (b : Bool)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (y : KPFiniteCuspAtlas.SymmetricSpace F) :
    ∃ B : LocalBall (KPCuspLogShape.dimension F * 3),
      (KPContActualChartRestrictionDensity.coordinates F).symm y ∈ B.carrier ∧
      KPCutoffSource.ChartSmoothHolomorphicOn B
        (fun s => KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U
          (if b then source.descent.commutator s else source.descent.cutoff s) i
          (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ (level F ζ hζ C R P H U) 1))
        KPContinuation.spectralDomain := by
  let O := (KPContSectorPhaseComponentCharts.orbifoldChart_exists F ζ hζ
    (level F ζ hζ C R P H U) R P H i y).some
  let x := (KPContActualChartRestrictionDensity.coordinates F).symm y
  have hx : x ∈ KPContActualChartRestrictionDensity.chartDomain F ζ hζ
      (level F ζ hζ C R P H U) R P H i y O := by
    change KPContActualChartRestrictionDensity.coordinates F x ∈ O.neighborhood
    rw [Homeomorph.apply_symm_apply]
    exact O.center_mem
  have hopen := O.isOpen.preimage (KPContActualChartRestrictionDensity.coordinates F).continuous
  obtain ⟨r, hr, hrD⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hx)
  have hn : 0 < KPCuspLogShape.dimension F * 3 := by
    have he := (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1
    have hd := (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.2
    dsimp [KPCuspLogShape.dimension]
    positivity
  let B : LocalBall (KPCuspLogShape.dimension F * 3) := ⟨hn, x, r/2, by positivity⟩
  have hBD : KPContLocalCubeEmbedding.closedCarrier B ⊆
      KPContActualChartRestrictionDensity.chartDomain F ζ hζ
        (level F ζ hζ C R P H U) R P H i y O :=
    (Metric.closedBall_subset_ball (by change r/2 < r; linarith)).trans hrD
  refine ⟨B, Metric.mem_ball_self B.radius_pos, ?_⟩
  have hh := source.local_holomorphy i y O
    (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ (level F ζ hζ C R P H U) 1) B hBD
  cases b
  · exact hh.1
  · exact hh.2

private theorem source_coefficient_formula (b : Bool) (s : ℂ)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (x : Space (KPCuspLogShape.dimension F * 3)) :
    KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U
      (if b then source.descent.commutator s else source.descent.cutoff s) i
      (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ (level F ζ hζ C R P H U) 1) x =
    KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
      (if b then source.descent.commutator s else source.descent.cutoff s)
      (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
        (level F ζ hζ C R P H U))
        (KPContActualChartRestrictionDensity.coordinates F x,
          (H.atlas (level F ζ hζ C R P H U)).representative i)) := by
  unfold KPContActualAllCuspSource.chartCoefficient
  rw [KPContActualChartRestrictionDensity.frameCoefficient_class,
    KPContSectorScalarLineAlgebra.S_apply]
  simp [KPContActualCutoffSmoothDescent.scalar]

private theorem source_component_holo (b : Bool)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (y : KPFiniteCuspAtlas.SymmetricSpace F) :
    DifferentiableOn ℂ (fun s => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
      (if b then source.descent.commutator s else source.descent.cutoff s)
      (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
        (level F ζ hζ C R P H U)) (y, (H.atlas (level F ζ hζ C R P H U)).representative i)))
      KPContinuation.spectralDomain := by
  obtain ⟨B, hx, hh⟩ := source_chart_neighborhood F ζ hζ C R P H U ι f buffer χ source b i y
  apply (point_holomorphic B _ _ hh _ hx).congr
  intro s hs
  rw [source_coefficient_formula, Homeomorph.apply_symm_apply]

private theorem source_component_jet_joint (b : Bool) (k : ℕ)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount) :
    ContinuousOn (fun p : ℂ × KPFiniteCuspAtlas.SymmetricSpace F =>
      iteratedDerivWithin k (fun z => KPContActualCutoffSmoothDescent.scalar
        F ζ hζ C R P H U
        (if b then source.descent.commutator z else source.descent.cutoff z)
        (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
          (level F ζ hζ C R P H U))
          (p.2, (H.atlas (level F ζ hζ C R P H U)).representative i))) V p.1)
      (V ×ˢ Set.univ) := by
  apply (KPChamberL2Defect.chamber_isOpen.prod isOpen_univ).continuousOn_iff.mpr
  intro p hp
  obtain ⟨B,hx,hh⟩ := source_chart_neighborhood F ζ hζ C R P H U ι f buffer χ source b i p.2
  obtain ⟨K,hK,hxK,hKB⟩ := exists_compact_subset Metric.isOpen_ball hx
  let α : MultiIndex (KPCuspLogShape.dimension F * 3) 0 := ⟨fun _ => 0,by simp⟩
  have hα : ∀ u x, coordinateDerivative α u x = u x := by
    intro u x
    have hd : α.directions = [] := by
      simp only [MultiIndex.directions,α,List.replicate_zero]
      induction List.finRange (KPCuspLogShape.dimension F * 3) with
      | nil => rfl
      | cons i l ih => simpa using ih
    simp [coordinateDerivative,hd,coordinateDerivativeList]
  have hj := KPContThreeL2CompactBoundHelpers.tuple_parameter_jet_joint B
    KPContinuation.spectralDomain KPContinuation.spectralDomain_isOpen _ hh K hK hKB k α
  have hpΩ : p.1 ∈ KPContinuation.spectralDomain := by
    change -(1 : ℝ)/6 < p.1.re
    have hr : (1 : ℝ)/3 < p.1.re := hp.1
    linarith
  have hnh : KPContinuation.spectralDomain ×ˢ K ∈
      𝓝 (p.1, (KPContActualChartRestrictionDensity.coordinates F).symm p.2) := by
    apply mem_nhds_prod_iff.mpr
    exact ⟨_, KPContinuation.spectralDomain_isOpen.mem_nhds hpΩ,
      _, Filter.mem_of_superset (isOpen_interior.mem_nhds hxK) interior_subset, Set.Subset.refl _⟩
  have ht := hj.continuousAt (x := (p.1, (KPContActualChartRestrictionDensity.coordinates F).symm p.2)) hnh
  let map : ℂ × KPFiniteCuspAtlas.SymmetricSpace F → ℂ × Space (KPCuspLogShape.dimension F * 3) :=
    fun q => (q.1, (KPContActualChartRestrictionDensity.coordinates F).symm q.2)
  have hm : ContinuousAt map p := continuousAt_fst.prodMk
    ((KPContActualChartRestrictionDensity.coordinates F).symm.continuous.continuousAt.comp continuousAt_snd)
  have hc := ht.comp_of_eq hm rfl
  apply hc.congr_of_eventuallyEq
  filter_upwards [((KPChamberL2Defect.chamber_isOpen.prod isOpen_univ).mem_nhds hp)] with q hq
  simp only [Function.comp_def, hα]
  rw [iteratedDerivWithin_of_isOpen KPContinuation.spectralDomain_isOpen (by
      change -(1 : ℝ)/6 < q.1.re
      have hr : (1 : ℝ)/3 < q.1.re := hq.1
      linarith),
    iteratedDerivWithin_of_isOpen KPChamberL2Defect.chamber_isOpen hq.1]
  congr 1
  funext z
  rw [source_coefficient_formula, Homeomorph.apply_symm_apply]

private theorem source_component_jet_smooth (b : Bool) (k : ℕ) (s : ℂ)
    (hs : s ∈ V) (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => iteratedDerivWithin k
      (fun z => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
        (if b then source.descent.commutator z else source.descent.cutoff z)
        (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
          (level F ζ hζ C R P H U)) (y, (H.atlas (level F ζ hζ C R P H U)).representative i))) V s) := by
  have hsΩ : s ∈ KPContinuation.spectralDomain := by
    change -(1 : ℝ)/6 < s.re
    change (1 : ℝ)/3 < s.re at hs
    linarith
  rw [contDiff_iff_contDiffAt]
  intro y
  obtain ⟨B, hx, hh⟩ := source_chart_neighborhood F ζ hζ C R P H U ι f buffer χ source b i y
  have hj := KPContActualCutoffSmoothDescent.smooth_parameter_jet_on_ball B _
    KPContinuation.spectralDomain_isOpen _ hh k s hsΩ
  have hd := (hj.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).comp y
    (realCoordinates_inverse_smooth F).contDiffAt
  apply hd.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro z
  dsimp only [Function.comp_def]
  rw [iteratedDerivWithin_of_isOpen (show IsOpen V from KPChamberL2Defect.chamber_isOpen) hs,
    iteratedDerivWithin_of_isOpen KPContinuation.spectralDomain_isOpen hsΩ]
  congr 1
  funext w
  rw [source_coefficient_formula, Homeomorph.apply_symm_apply]

theorem smooth (k : ℕ) (s : ℂ) :
    KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ (level F ζ hζ C R P H U) R P H
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) ∧
    KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ (level F ζ hζ C R P H U) R P H
      (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) := by
  by_cases hs : s ∈ V
  · have hE := KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf k s hs
    have hC := source_component_jet_smooth F ζ hζ C R P H U ι f buffer χ source false k s hs
    have hK := source_component_jet_smooth F ζ hζ C R P H U ι f buffer χ source true k s hs
    constructor
    · intro i
      have he : (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s i).val =
          fun y => (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s i).val y -
            iteratedDerivWithin k (fun z => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
              (source.descent.cutoff z)
              (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
                (level F ζ hζ C R P H U)) (y, (H.atlas (level F ζ hζ C R P H U)).representative i))) V s := by
        funext y
        unfold lineG KPContActualChamberCasimirJets.lineJet
        rw [KPContSectorScalarLineAlgebra.S_apply, KPContSectorScalarLineAlgebra.S_apply]
        simp only [coveredG, KPContActualChamberCasimirJets.coveredJet, dif_pos hs]
        unfold g KPContActualChamberCasimirJets.jet
        have hh := (source_component_holo F ζ hζ C R P H U ι f buffer χ source false i y)
        have hVΩ : V ⊆ KPContinuation.spectralDomain := by
          intro z hz
          change -(1 : ℝ)/6 < z.re
          change (1 : ℝ)/3 < z.re at hz
          linarith
        exact iteratedDerivWithin_sub hs KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
          ((E_holo F ζ hζ U ι f hι hf _).contDiffOn KPChamberL2Defect.chamber_isOpen s hs)
          ((hh.mono hVΩ).contDiffOn KPChamberL2Defect.chamber_isOpen s hs)
      rw [he]
      exact (hE i).sub (hC i)
    · intro i
      have he : (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s i).val =
          fun y => iteratedDerivWithin k (fun z => KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
            (source.descent.commutator z)
            (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
              (level F ζ hζ C R P H U)) (y, (H.atlas (level F ζ hζ C R P H U)).representative i))) V s := by
        funext y
        unfold lineH
        rw [KPContSectorScalarLineAlgebra.S_apply]
        simp only [coveredH, dif_pos hs, h]
      rw [he]
      exact hK i
  · simp only [lineG, lineH, coveredG, coveredH, dif_neg hs, map_zero]
    exact ⟨(KPContSectorSmoothFramesSupport.smoothSections F ζ hζ (level F ζ hζ C R P H U) R P H).zero_mem,
      (KPContSectorSmoothFramesSupport.smoothSections F ζ hζ (level F ζ hζ C R P H U) R P H).zero_mem⟩

private theorem source_scalar_component (w : SmoothSections F ζ hζ C R P H U)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (y : KPFiniteCuspAtlas.SymmetricSpace F) :
    KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U w
      (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
        (level F ζ hζ C R P H U)) (y, (H.atlas (level F ζ hζ C R P H U)).representative i)) =
      (w.val i).val y := by
  have he := congrArg (fun v => (v i).val y)
    (congrArg Subtype.val ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
      (level F ζ hζ C R P H U) R P H).apply_symm_apply w))
  rw [KPContSectorSmoothFramesSupport.smoothS_apply,
    KPContSectorScalarLineAlgebra.S_apply] at he
  exact he

theorem lineG_eq_series_sub_source (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s -
      KPContActualCompactSectionL2Jets.pointwiseJets
        (fun z => (source.descent.cutoff z).val) V k s := by
  funext i
  apply Subtype.ext
  funext y
  simp only [Pi.sub_apply, Submodule.coe_sub, Pi.sub_apply]
  unfold lineG KPContActualChamberCasimirJets.lineJet
  rw [KPContSectorScalarLineAlgebra.S_apply, KPContSectorScalarLineAlgebra.S_apply]
  simp only [coveredG, KPContActualChamberCasimirJets.coveredJet, dif_pos hs,
    KPContActualCompactSectionL2Jets.pointwiseJets_apply]
  unfold g KPContActualChamberCasimirJets.jet
  have hVΩ : V ⊆ KPContinuation.spectralDomain := by
    intro z hz
    change -(1 : ℝ)/6 < z.re
    change (1 : ℝ)/3 < z.re at hz
    linarith
  have hC := ((source_component_holo F ζ hζ C R P H U ι f buffer χ source false i y).mono hVΩ).contDiffOn (n := k)
      KPChamberL2Defect.chamber_isOpen s hs
  simp only [Bool.false_eq_true, ↓reduceIte] at hC
  refine (iteratedDerivWithin_sub hs KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
    ((E_holo F ζ hζ U ι f hι hf
      (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
        (Quotient.mk (KPContSectorCoveredQuotientVocabulary.coveredRelation F ζ hζ
          (level F ζ hζ C R P H U)) (y, (H.atlas (level F ζ hζ C R P H U)).representative i)))).contDiffOn
        KPChamberL2Defect.chamber_isOpen s hs) hC).trans ?_
  congr 1
  congr 1
  funext z
  exact source_scalar_component F ζ hζ C R P H U (source.descent.cutoff z) i y

theorem lineH_eq_source_jet (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualCompactSectionL2Jets.pointwiseJets
        (fun z => (source.descent.commutator z).val) V k s := by
  funext i
  apply Subtype.ext
  funext y
  unfold lineH
  rw [KPContSectorScalarLineAlgebra.S_apply]
  simp only [coveredH, dif_pos hs, h, KPContActualCompactSectionL2Jets.pointwiseJets_apply]
  congr 1
  funext z
  exact source_scalar_component F ζ hζ C R P H U (source.descent.commutator z) i y

def smoothG (k : ℕ) (s : ℂ) : SmoothSections F ζ hζ C R P H U :=
  ⟨_, (smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1⟩

private theorem smooth_coefficient_at
    (w : Sections F ζ hζ C R P H U)
    (hw : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ (level F ζ hζ C R P H U) R P H w)
    {i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount}
    (a : Frame F ζ hζ C R P H U i) (x : KPContActualChamberCasimirJets.M F) (hx : x ∈ a.omega) :
    ContDiffAt ℝ (⊤ : ℕ∞) (a.coefficient w) x := by
  let v : KPArch.Space (KPCuspLogShape.dimension F) → ℂ := fun y => (w i).val (a.kind.representative • y)
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := (hw i).comp
    (CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff F a.kind.representative)
  have ha : ContDiff ℝ (⊤ : ℕ∞) (KPContCotangentActualOverlap.labeledA a.places) := by
    exact contDiff_pi.2 (fun j => contDiff_pi.1
      (CotangentLogCoframe.A (KPContActualChamberCasimirJets.d F)).contDiff (a.places.symm j))
  let c : ℂ := KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x)
  have hp : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝 x] (fun _ => c) := by
    have he := (a.splitting_locallyConstant.comp (fun ε => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ))).eventually_eq (⟨x,hx⟩ : a.omega)
    have hh : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝[a.omega] x] (fun _ => c) := by
      rw [nhdsWithin_eq_map_subtype_coe hx]; exact he
    rwa [a.isOpen_omega.nhdsWithin_eq hx] at hh
  apply (((contDiff_const (c := c)).mul (hv.comp ha)).contDiffAt).congr_of_eventuallyEq
  filter_upwards [hp] with y hy
  simp only [KPContCotangentActualOverlap.LiftedChart.coefficient, hy]
  rfl

private theorem metric_laplacian_sub {n : ℕ} {u v : HyperbolicChart.Space n → ℂ}
    {x : HyperbolicChart.Space n}
    (hu : ContDiffAt ℝ (⊤ : ℕ∞) u x) (hv : ContDiffAt ℝ (⊤ : ℕ∞) v x) :
    HyperbolicChart.laplacian n (u - v) x =
      HyperbolicChart.laplacian n u x - HyperbolicChart.laplacian n v x := by
  have hfirst (j : Fin n) (l : Fin 3) :
      HyperbolicChart.coordinateDerivative n j l (u - v) =ᶠ[𝓝 x]
        HyperbolicChart.coordinateDerivative n j l u - HyperbolicChart.coordinateDerivative n j l v := by
    filter_upwards [(hu.of_le (m := 1) (by simp)).eventually (by simp), (hv.of_le (m := 1) (by simp)).eventually (by simp)] with y hy hz
    simp only [HyperbolicChart.coordinateDerivative]
    rw [fderiv_sub (hy.differentiableAt (by simp)) (hz.differentiableAt (by simp))]
    rfl
  have hdiff (f : HyperbolicChart.Space n → ℂ) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x)
      (j : Fin n) (l : Fin 3) : DifferentiableAt ℝ (HyperbolicChart.coordinateDerivative n j l f) x := by
    unfold HyperbolicChart.coordinateDerivative
    exact (hf.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const |>.differentiableAt (by simp)
  have hsecond (j : Fin n) (l : Fin 3) :
      HyperbolicChart.coordinateDerivative n j l (HyperbolicChart.coordinateDerivative n j l (u - v)) x =
        HyperbolicChart.coordinateDerivative n j l (HyperbolicChart.coordinateDerivative n j l u) x -
        HyperbolicChart.coordinateDerivative n j l (HyperbolicChart.coordinateDerivative n j l v) x := by
    change fderiv ℝ (HyperbolicChart.coordinateDerivative n j l (u - v)) x
      (HyperbolicChart.coordinateVector n j l) = _
    rw [(hfirst j l).fderiv_eq, fderiv_sub (hdiff u hu j l) (hdiff v hv j l)]
    rfl
  unfold HyperbolicChart.laplacian
  simp only [hsecond, (hfirst _ _).eq_of_nhds, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem defect_frame_equation (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (a : Frame F ζ hζ C R P H U i) (x : KPContActualChamberCasimirJets.M F) (hx : x ∈ a.omega) :
    HyperbolicChart.laplacian (KPContActualChamberCasimirJets.d F)
      (a.coefficient (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)) x =
    KPContActualChamberCasimirJets.lambda F s *
      a.coefficient (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x -
      a.coefficient (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s) x +
      ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) *
        KPContActualChamberCasimirJets.lambdaJet F j s *
        a.coefficient (lineG F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s) x := by
  let cjet := KPContActualCompactSectionL2Jets.pointwiseJets
    (fun z => (source.descent.cutoff z).val) V
  have hc : KPContSectorSmoothFramesSupport.IsSmoothSections F ζ hζ
      (level F ζ hζ C R P H U) R P H (cjet k s) := by
    intro j
    have he := congrArg (fun v => (v j).val)
      (lineG_eq_series_sub_source F ζ hζ C R P H U ι f buffer χ source hι hf k s hs)
    have hcj := (KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf k s hs j).sub
      ((smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1 j)
    convert hcj using 1
    funext y
    have hh := congrFun he y
    simp only [Pi.sub_apply, Submodule.coe_sub, Pi.sub_apply] at hh ⊢
    change (cjet k s j).val y =
      (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s j).val y -
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s j).val y
    linear_combination hh
  have hVΩ : V ⊆ KPContinuation.spectralDomain := by
    intro z hz
    change -(1 : ℝ)/6 < z.re
    change (1 : ℝ)/3 < z.re at hz
    linarith
  have hsource := (KPContActualAllCuspSourceLaplacianJets.actual_source_laplacian_jets
    F ζ hζ C R P H U ι f buffer χ source V KPChamberL2Defect.chamber_isOpen hVΩ).2 k s hs i a x hx
  have hE := KPContActualChamberCasimirJets.casimir_jets F ζ hζ C R P H U ι f hι hf k s hs a x hx
  simp only [lineG_eq_series_sub_source F ζ hζ C R P H U ι f buffer χ source hι hf _ s hs,
    lineH_eq_source_jet F ζ hζ C R P H U ι f buffer χ source hι hf _ s hs]
  have hcoef : ∀ u v : Sections F ζ hζ C R P H U, a.coefficient (u - v) =
      a.coefficient u - a.coefficient v := by
    intro u v
    funext y
    simp [KPContCotangentActualOverlap.LiftedChart.coefficient, mul_sub]
  rw [hcoef, metric_laplacian_sub
    (smooth_coefficient_at F ζ hζ C R P H U _
      (KPContActualChamberCasimirJets.lineJet_smooth F ζ hζ C R P H U ι f hι hf k s hs) a x hx)
    (smooth_coefficient_at F ζ hζ C R P H U _ hc a x hx)]
  have hE' : HyperbolicChart.laplacian (KPContActualChamberCasimirJets.d F)
      (a.coefficient (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s)) x =
      KPContActualChamberCasimirJets.lambda F s *
        a.coefficient (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf k s) x +
      ∑ j ∈ Finset.Icc 1 (min k 2), (Nat.choose k j : ℂ) *
        KPContActualChamberCasimirJets.lambdaJet F j s *
        a.coefficient (KPContActualChamberCasimirJets.lineJet F ζ hζ C R P H U ι f hι hf (k-j) s) x := hE
  rw [hE', hsource]
  simp only [hcoef, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  simp only [KPContActualChamberCasimirJets.lambdaJet, KPContActualChamberCasimirJets.V, V]
  simp only [KPContActualChamberCasimirJets.lambda, KPContActualChamberCasimirJets.d]
  ring_nf
  rfl

def lineDelta (k : ℕ) (s : ℂ) : Sections F ζ hζ C R P H U :=
  KPCuspCutoffGraph.localLaplacianSection F ζ hζ H.totallyComplex
    (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U))
    (smoothG F ζ hζ C R P H U ι f buffer χ source hι hf k s)

private theorem threeL2_rational_laplacian (γ : KPCuspArithmetic.PGL2 F)
    (u : KPArch.Space (KPCuspLogShape.dimension F) → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
      (fun y => u (γ • y)) z =
      KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F) u (γ • z) := by
  obtain ⟨B,hB⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  have he : (fun y : KPArch.Space (KPCuspLogShape.dimension F) => γ • y) =
      KPArch.productAction (KPCuspLogShape.dimension F)
        (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding B) := by
    funext y
    rw [← hB]
    exact KPCuspSiegel.action_mk F B y
  simp_rw [show ∀ y, γ • y = KPArch.productAction (KPCuspLogShape.dimension F)
    (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding B) y from
      fun y => congrFun he y]
  exact KPContArchLaplacianNaturality.pullback _ _ _ hu z

theorem lineDelta_frame (k : ℕ) (s : ℂ)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (a : Frame F ζ hζ C R P H U i) (x : KPContActualChamberCasimirJets.M F) (hx : x ∈ a.omega) :
    a.coefficient (lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s) x =
      HyperbolicChart.laplacian (KPContActualChamberCasimirJets.d F)
        (a.coefficient (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)) x := by
  let w := lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s
  have hw := (smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1 i
  let v : KPArch.Space (KPCuspLogShape.dimension F) → ℂ := fun y => (w i).val (a.kind.representative • y)
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := hw.comp
    (CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff F a.kind.representative)
  let c : ℂ := KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting x)
  have hp : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝 x] (fun _ => c) := by
    have he := (a.splitting_locallyConstant.comp (fun ε => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ))).eventually_eq (⟨x,hx⟩ : a.omega)
    have hh : (fun y => (KPCuspGenuineMonodromy.chi F ζ hζ (a.splitting y) : ℂ)) =ᶠ[𝓝[a.omega] x] (fun _ => c) := by
      rw [nhdsWithin_eq_map_subtype_coe hx]; exact he
    rwa [a.isOpen_omega.nhdsWithin_eq hx] at hh
  have hg : a.coefficient w =ᶠ[𝓝 x]
      (fun y => c * v (KPContCotangentActualOverlap.labeledA a.places y)) := by
    filter_upwards [hp] with y hy
    simp only [KPContCotangentActualOverlap.LiftedChart.coefficient, hy]
    rfl
  rw [KPCuspCutoffGraphApproximation.laplacian_congr_nhds _ hg]
  have hb := KPContArchLaplacianCoordinateBridge.bridge_equiv
    (KPContActualChamberCasimirJets.d F) (KPCuspLogShape.dimension F) a.places
    (fun y => c * v y) (contDiff_const.mul hv) x
  change KPContActualSphericalFlatStage.localLaplacian _ (fun y => c * v y)
    (KPContCotangentActualOverlap.labeledA a.places x) =
      HyperbolicChart.laplacian _ (fun y => c * v (KPContCotangentActualOverlap.labeledA a.places y)) x at hb
  rw [← hb, KPContArchLaplacianNaturality.localLaplacian_const_mul _ _ hv,
    threeL2_rational_laplacian F a.kind.representative (w i).val hw]
  change c * KPCuspCutoffGraph.localLaplacianComplex F ζ hζ H.totallyComplex
    (level F ζ hζ C R P H U) (H.atlas (level F ζ hζ C R P H U)) w i
    (a.kind.representative • KPContCotangentActualOverlap.labeledA a.places x) = _
  congr 1
  exact (KPContArchLaplacianCoordinateBridge.bridge F (w i).val hw
    (a.kind.representative • KPContCotangentActualOverlap.labeledA a.places x)).symm

theorem lineH_support (k : ℕ) (s : ℂ) :
    tsupport (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
      (level F ζ hζ C R P H U) R P H
      (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)) ⊆
    KPContActualAllCuspSource.K F ζ hζ C R P H U buffer := by
  by_cases hs : s ∈ V
  · have hsΩ : s ∈ KPContinuation.spectralDomain := by
      change -(1 : ℝ)/6 < s.re
      change (1 : ℝ)/3 < s.re at hs
      linarith
    have he : lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s =
        KPContActualCompactSectionL2Jets.pointwiseJets
          (fun z => (source.descent.commutator z).val) KPContinuation.spectralDomain k s := by
      funext i
      apply Subtype.ext
      funext y
      unfold lineH
      rw [KPContSectorScalarLineAlgebra.S_apply]
      simp only [coveredH, dif_pos hs, h, KPContActualCompactSectionL2Jets.pointwiseJets_apply]
      rw [iteratedDerivWithin_of_isOpen (show IsOpen V from KPChamberL2Defect.chamber_isOpen) hs,
        iteratedDerivWithin_of_isOpen KPContinuation.spectralDomain_isOpen hsΩ]
      congr 1
      funext z
      unfold KPContActualCutoffSmoothDescent.scalar
      rw [← KPContSectorScalarLineAlgebra.S_apply]
      have hS : KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H
          ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ (level F ζ hζ C R P H U) R P H).symm
            (source.descent.commutator z)).val = (source.descent.commutator z).val := by
        rw [← KPContSectorSmoothFramesSupport.smoothS_apply, LinearEquiv.apply_symm_apply]
      rw [hS]
    rw [he]
    exact KPContActualCompactSectionL2Jets.pointwiseJets_support _ _ _
      source.compact_collars.isClosed source.support k s hsΩ
  · simp only [lineH, coveredH, dif_neg hs, map_zero]
    have hz : KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
        (level F ζ hζ C R P H U) R P H (0 : Sections F ζ hζ C R P H U) = 0 := by
      funext x
      obtain ⟨v, rfl⟩ := KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ
        (level F ζ hζ C R P H U) x
      rw [← map_zero (KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H),
        KPContSectorSmoothFramesSupport.sectionNorm_pullback]
      simp
    rw [hz]
    simp

theorem lineH_borelL2 (k : ℕ) (s : ℂ) :
    lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈
      BorelL2Sections F ζ hζ C R P H U := by
  have hsm := (smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).2
  have hm : ∀ i, Measurable
      (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s i).val :=
    fun i => (hsm i).continuous.measurable
  refine ⟨hm, ?_⟩
  apply (KPContSectorLineL2Isometry.finite_integral_iff F ζ hζ
    (level F ζ hζ C R P H U) R P H _ hm).mpr
  letI := KPContSectorFixedMeasureLocalFiniteness.coveredMeasure_finiteOnCompacts
    F ζ hζ R (level F ζ hζ C R P H U)
  have hc := (KPContSectorLineL2Isometry.continuous_iff F ζ hζ
    (level F ζ hζ C R P H U) R P H _).mp (fun i => (hsm i).continuous)
  apply hc.memLp_of_hasCompactSupport
  apply (KPContSectorSmoothFramesSupport.hasCompactSupport_iff F ζ hζ
    (level F ζ hζ C R P H U) R P H _).mpr
  rw [show KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H
      (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ (level F ζ hζ C R P H U) R P H
        (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)) =
      lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s from
    (KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H).apply_symm_apply _]
  exact source.compact_collars.of_isClosed_subset isClosed_closure
    (lineH_support F ζ hζ C R P H U ι f buffer χ source hι hf k s)

private theorem scalar_cusp_frame_identity
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (e : KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ (level F ζ hζ C R P H U))
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    (KPContSectorScalarLineAlgebra.J F ζ hζ (level F ζ hζ C R P H U) e).val
      (z, KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a 1) =
      (KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H e a.1).val
        (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a • z) := by
  let j := KPContSectorScalarLineAlgebra.J F ζ hζ (level F ζ hζ C R P H U) e
  have hr := j.property.1 z
    (KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a 1)
    (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a)
  have hc : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
      (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a) *
      KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a 1 =
      (H.atlas (level F ζ hζ C R P H U)).representative a.1 := by
    simp [KPContFlatCuspIncomingEvaluation.finiteRepresentative,
      KPContFlatCuspIncomingEvaluation.atlas, map_inv]
  rw [hc] at hr
  rw [KPContSectorScalarLineAlgebra.S_apply]
  exact hr.symm

include hι hf in
private theorem E_cusp_scalar (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) :
    KPContActualChamberNormalSeries.E F ζ hζ U ι f s
      (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
        (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a 1 p)) =
    KPContActualChamberNormalSeries.E F ζ hζ U ι f s
      (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a p.2 p.1.1 p.1.2 1) := by
  obtain ⟨e, he, -, -⟩ := KPContActualChamberNormalSeries.descent_series F ζ hζ C R P H U ι f hι hf
  have hleft := he s hs (KPContActualChamberNormalSeries.coveredRepresentative F ζ hζ C R P H U
    (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a 1 p))
  rw [KPContActualChamberNormalSeries.coveredRepresentative_projection] at hleft
  rw [← hleft]
  have hv : (e s).val (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a 1 p) =
      (KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H (e s) a.1).val
        (KPContFlatCuspIncomingEvaluation.sigma F ζ hζ C R P H U a • KPCuspCharts.toArch F p) := by
    rw [KPContSectorScalarLineAlgebra.S_apply]
    simp [KPContActualCutoffSmoothDescent.coveredPoint, KPContSectorSmoothFramesSupport.cuspPoint,
      KPContFlatCuspIncomingEvaluation.sigma, KPContFlatCuspIncomingEvaluation.atlas]
  rw [hv, KPContFlatCuspIncomingEvaluation.cuspGroup,
    (KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).1,
    ← he s hs, KPContFlatCuspIncomingEvaluation.localGroup,
    KPContSectorScalarLineAlgebra.group_lift_formula,
    KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection,
    scalar_cusp_frame_identity F ζ hζ C R P H U a (e s)]

include hι hf in

theorem g_cusp_scalar (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) :
    g F ζ hζ C R P H U ι f buffer χ source k s
      (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a 1 p) =
    iteratedDerivWithin k (fun w => KPContActualChamberOutgoingAdapter.correctionSheet
      F ζ hζ C R P H U a ι buffer f χ source w p.2 p.1.1 p.1.2 1) V s := by
  unfold g KPContActualChamberOutgoingAdapter.correctionSheet
  exact iteratedDerivWithin_congr (fun w hw => by rw [E_cusp_scalar F ζ hζ C R P H U ι f hι hf w hw]) hs

theorem sectionNorm_cusp_scalar (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) :
    KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ (level F ζ hζ C R P H U) R P H
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)
      (KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U) R P H a p) =
    ‖iteratedDerivWithin k (fun w => KPContActualChamberOutgoingAdapter.correctionSheet
      F ζ hζ C R P H U a ι buffer f χ source w p.2 p.1.1 p.1.2 1) V s‖ := by
  rw [← KPContActualCutoffSmoothDescent.coveredPoint_base F ζ hζ C R P H U a 1 p]
  unfold lineG
  rw [KPContSectorSmoothFramesSupport.sectionNorm_pullback]
  simp only [coveredG, dif_pos hs]
  rw [g_cusp_scalar F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p]

include hι hf in
private theorem scalar_correction_holomorphic
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) :
    DifferentiableOn ℂ (fun w => KPContActualChamberOutgoingAdapter.correctionSheet
      F ζ hζ C R P H U a ι buffer f χ source w p.2 p.1.1 p.1.2 1) V := by
  apply (E_holo F ζ hζ U ι f hι hf
    (KPContFlatCuspIncomingEvaluation.cuspGroup F ζ hζ C R P H U a p.2 p.1.1 p.1.2 1)).sub
  have hh := (source_component_holo F ζ hζ C R P H U ι f buffer χ source false a.1
    (KPContSectorSmoothFramesSupport.cuspPoint F ζ hζ (level F ζ hζ C R P H U) R P H
      a.1 a.2 p)).mono (show V ⊆ KPContinuation.spectralDomain from by
        intro s hs; change -(1 : ℝ)/6 < s.re; change (1 : ℝ)/3 < s.re at hs; linarith)
  simpa [KPContActualCutoffSmoothDescent.coveredPoint] using hh

include hι hf in
private theorem scalar_zero_holomorphic
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) (ht : T + 1 ≤ p.2) (hb : buffer.τ < p.2) :
    DifferentiableOn ℂ (fun w => KPContActualChamberOutgoingAdapter.zeroScalar
      F ζ hζ C R P H U a ι buffer f χ source w p) V := by
  have hexp : DifferentiableOn ℂ (fun w => KPChamberOutgoingL2.outgoingFactor
      (KPContActualChamberOutgoingAdapter.d F) w p.2) V := by
    unfold KPChamberOutgoingL2.outgoingFactor
    fun_prop
  apply (hexp.mul (KPContActualChamberOutgoingAdapter.coefficient_holomorphic
    F ζ hζ C R P H U a ι f hι hf p.1.2)).congr
  intro w hw
  unfold KPContActualChamberOutgoingAdapter.zeroScalar
  rw [KPContActualChamberOutgoingAdapter.outgoing_formula
    F ζ hζ C R P H U a ι buffer f χ source hι hf w hw p.2 p.1.2 ht hb]
  rfl

include hι hf in

theorem g_cusp_split (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) (ht : T + 1 ≤ p.2) (hb : buffer.τ < p.2) :
    g F ζ hζ C R P H U ι f buffer χ source k s
      (KPContActualCutoffSmoothDescent.coveredPoint F ζ hζ C R P H U a 1 p) =
    KPContActualChamberOutgoingAdapter.parameterScalar F ζ hζ C R P H U
      a ι buffer f χ source k s (KPCuspCharts.toArch F p) +
    KPContActualChamberMeanZeroAdapter.jetScalar F ζ hζ C R P H U
      a ι f k s p := by
  have he : (KPCuspCharts.toArchHomeomorph F
      (KPContActualChamberMeanZeroAdapter.geometry F ζ hζ C R P H U a).positive_dimension).symm
      (KPCuspCharts.toArch F p) = p := Homeomorph.symm_apply_apply _ p
  have he' : (KPCuspCharts.toArchHomeomorph F
      (KPContActualChamberOutgoingAdapter.geometry F ζ hζ C R P H U a).positive_dimension).symm
      (KPCuspCharts.toArch F p) = p := Homeomorph.symm_apply_apply _ p
  have hm : KPContActualChamberMeanZeroAdapter.jetScalar F ζ hζ C R P H U a ι f k s p =
      iteratedDerivWithin k ((fun w => KPContActualChamberOutgoingAdapter.correctionSheet
        F ζ hζ C R P H U a ι buffer f χ source w p.2 p.1.1 p.1.2 1) -
        (fun w => KPContActualChamberOutgoingAdapter.zeroScalar
          F ζ hζ C R P H U a ι buffer f χ source w p)) V s := by
    unfold KPContActualChamberMeanZeroAdapter.jetScalar
      KPContActualChamberMeanZeroAdapter.parameterScalar KPContActualChamberMeanZeroAdapter.meanZero
    rw [he]
    apply iteratedDerivWithin_congr _ hs
    intro w hw
    dsimp only [Pi.sub_apply]
    rw [← KPContActualChamberMeanZeroAdapter.correction_complement_eq F ζ hζ C R P H U a ι f buffer χ source hι hf w hw
      p.2 p.1.1 p.1.2 1 hb]
    unfold KPContActualChamberMeanZeroAdapter.correctionMeanZeroSheet
      KPContActualChamberOutgoingAdapter.zeroScalar
    rw [(KPContActualChamberOutgoingAdapter.zeroMode F ζ hζ C R P H U a ι buffer f χ source
      w p.2 p.1.2).property.2 (QuotientAddGroup.mk p.1.1)]
    simp
  rw [hm, iteratedDerivWithin_sub hs KPChamberL2Defect.chamber_isOpen.uniqueDiffOn
    (((scalar_correction_holomorphic F ζ hζ C R P H U ι f buffer χ source hι hf a p).contDiffOn
      KPChamberL2Defect.chamber_isOpen).contDiffWithinAt hs)
    (((scalar_zero_holomorphic F ζ hζ C R P H U ι f buffer χ source hι hf a p ht hb).contDiffOn
      KPChamberL2Defect.chamber_isOpen).contDiffWithinAt hs)]
  unfold KPContActualChamberOutgoingAdapter.parameterScalar
  rw [he', g_cusp_scalar F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p]
  ring

theorem sectionNorm_cusp_split_sq (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (p : KPCuspCharts.Coordinates F) (ht : T + 1 ≤ p.2) (hb : buffer.τ < p.2) :
    (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ (level F ζ hζ C R P H U) R P H
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)
      (KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U) R P H a p)) ^ 2 ≤
    2 * (KPContActualChamberOutgoingAdapter.jetNorm F ζ hζ C R P H U
      a ι buffer f χ source k 0 s p) ^ 2 +
    2 * ‖KPContActualChamberMeanZeroAdapter.jetScalar F ζ hζ C R P H U a ι f k s p‖ ^ 2 := by
  rw [sectionNorm_cusp_scalar F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p,
    ← g_cusp_scalar F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p,
    g_cusp_split F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p ht hb]
  simp only [KPContActualChamberOutgoingAdapter.jetNorm,
    KPContActualChamberOutgoingAdapter.covariantNorm, ite_true]
  have hn := norm_add_le
    (KPContActualChamberOutgoingAdapter.parameterScalar F ζ hζ C R P H U
      a ι buffer f χ source k s (KPCuspCharts.toArch F p))
    (KPContActualChamberMeanZeroAdapter.jetScalar F ζ hζ C R P H U a ι f k s p)
  have hsq := sq_nonneg
    (‖KPContActualChamberOutgoingAdapter.parameterScalar F ζ hζ C R P H U
      a ι buffer f χ source k s (KPCuspCharts.toArch F p)‖ -
      ‖KPContActualChamberMeanZeroAdapter.jetScalar F ζ hζ C R P H U a ι f k s p‖)
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith

theorem lineG_norm_continuous (k : ℕ) (s : ℂ) :
    Continuous (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ
      (level F ζ hζ C R P H U) R P H
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)) := by
  have hq := (KPContSectorQuotientRelationsComparison.q_isOpenMap F ζ hζ
    (level F ζ hζ C R P H U)).isQuotientMap
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ (level F ζ hζ C R P H U))
    (KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ (level F ζ hζ C R P H U))
  apply hq.continuous_iff.mpr
  have hc := (KPContSectorLineL2Isometry.continuous_iff F ζ hζ
    (level F ζ hζ C R P H U) R P H _).mp
    (fun i => ((smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1 i).continuous)
  convert hc.norm using 1
  funext v
  rw [Function.comp_apply, KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
  unfold lineG
  rw [LinearEquiv.symm_apply_apply, KPContSectorSmoothFramesSupport.sectionNorm_pullback]

theorem lineG_compact_square_finite (k : ℕ) (s : ℂ)
    (K : Set (Base F ζ hζ C R P H U)) (hK : IsCompact K) :
    (∫⁻ x in K, KPContSectorLineL2Isometry.squaredNorm F ζ hζ
      (level F ζ hζ C R P H U) R P H
      (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) < ⊤ := by
  letI := KPContSectorFixedMeasureLocalFiniteness.sphericalMeasure_finiteOnCompacts
    F ζ hζ R P (level F ζ hζ C R P H U)
  have hc := (lineG_norm_continuous F ζ hζ C R P H U ι f buffer χ source hι hf k s).pow 2
  have hi := hc.continuousOn.integrableOn_compact (μ := baseMeasure F ζ hζ C R P H U) hK
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))).mp hi.hasFiniteIntegral

theorem lineG_end_square_transport (k : ℕ) (s : ℂ) (hs : s ∈ V)
    (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
    (A : ℝ) (hA : (H.atlas (level F ζ hζ C R P H U)).threshold < A) :
    (∫⁻ x in KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a,
      KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H
        (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) =
    ∫⁻ p in {p : KPCuspCharts.Coordinates F | A < p.2}, ENNReal.ofReal
      (‖iteratedDerivWithin k (fun w => KPContActualChamberOutgoingAdapter.correctionSheet
        F ζ hζ C R P H U a ι buffer f χ source w p.2 p.1.1 p.1.2 1) V s‖ ^ 2)
      ∂KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a := by
  rw [← KPContActualEndHaarTransport.actual_end_coordinates_pushforward
    F ζ hζ C R P H U a A hA]
  rw [lintegral_map (KPContSectorLineL2Isometry.squaredNorm_measurable
    F ζ hζ (level F ζ hζ C R P H U) R P H _
      (fun i => ((smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1 i).continuous.measurable))
    (show Measurable (KPContActualCollarBuffer.chartLift F ζ hζ
      (level F ζ hζ C R P H U) R P H a) from by
        unfold KPContActualCollarBuffer.chartLift
        exact (continuous_quotient_mk'.comp
          (((KPCuspCharts.projectiveHomeomorph F
            (((H.atlas (level F ζ hζ C R P H U)).cuspAtlas a.1).representative a.2)).continuous.comp
            (KPCuspCharts.toArch_contDiff F).continuous).prodMk continuous_const)).measurable)]
  apply lintegral_congr
  intro p
  unfold KPContSectorLineL2Isometry.squaredNorm
  rw [sectionNorm_cusp_scalar F ζ hζ C R P H U ι f buffer χ source hι hf k s hs a p]

theorem lineG_high_end_square_bound (L : Set ℂ) (hL : IsCompact L) (hLV : L ⊆ V)
    (k : ℕ) : ∃ A B : ℝ,
    (H.atlas (level F ζ hζ C R P H U)).threshold < A ∧ 0 ≤ B ∧
    ∀ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U, ∀ s ∈ L,
    (∫⁻ x in KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a,
      KPContSectorLineL2Isometry.squaredNorm F ζ hζ (level F ζ hζ C R P H U) R P H
        (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s) x
      ∂baseMeasure F ζ hζ C R P H U) ≤ ENNReal.ofReal B := by
  obtain ⟨t₀,c,h0,hT,hb,hc,hbound⟩ := KPContActualChamberOutgoingAdapter.jets_memLp_square_bound
    F ζ hζ C R P H U ι buffer f χ source hι hf L hL hLV k 0
  obtain ⟨t₁,b,h1atlas,hb0,hmbound⟩ := KPContActualChamberMeanZeroAdapter.actual_unweighted_tails
    F ζ hζ C R P H U ι f hι hf L hL hLV k
  let A := max t₀ t₁
  have h0A : t₀ ≤ A := le_max_left _ _
  have h1A : t₁ ≤ A := le_max_right _ _
  have hA : (H.atlas (level F ζ hζ C R P H U)).threshold < A := h1atlas.trans_le h1A
  refine ⟨A,2*c+2*b,hA,by positivity,?_⟩
  intro a s hs
  rw [lineG_end_square_transport F ζ hζ C R P H U ι f buffer χ source hι hf k s (hLV hs) a A hA]
  have hout : KPContActualChamberOutgoingAdapter.squareTail F ζ hζ C R P H U
      a ι buffer f χ source k 0 s A ≤ ENNReal.ofReal c :=
    (lintegral_mono_set (fun p hp => lt_of_le_of_lt h0A hp)).trans (hbound a s hs).2
  have hmean : KPContActualChamberMeanZeroAdapter.energy F ζ hζ C R P H U
      a ι f k s 0 A ≤ ENNReal.ofReal b :=
    (lintegral_mono_set (fun p hp => lt_of_le_of_lt h1A hp)).trans (hmbound a s hs)
  have hsplit : ∀ p : KPCuspCharts.Coordinates F, A < p.2 →
      ENNReal.ofReal (‖iteratedDerivWithin k
        (fun w => KPContActualChamberOutgoingAdapter.correctionSheet
          F ζ hζ C R P H U a ι buffer f χ source w p.2 p.1.1 p.1.2 1) V s‖ ^ 2) ≤
      (2 : ℝ≥0∞) * ENNReal.ofReal ((KPContActualChamberOutgoingAdapter.jetNorm
        F ζ hζ C R P H U a ι buffer f χ source k 0 s p) ^ 2) +
      (2 : ℝ≥0∞) * ENNReal.ofReal
        (KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p) := by
    intro p hp
    have hh := sectionNorm_cusp_split_sq F ζ hζ C R P H U ι f buffer χ source hι hf
      k s (hLV hs) a p (hT.le.trans (h0A.trans hp.le)) (hb.trans_le h0A |>.trans hp)
    rw [sectionNorm_cusp_scalar F ζ hζ C R P H U ι f buffer χ source hι hf k s (hLV hs) a p] at hh
    have he : ‖KPContActualChamberMeanZeroAdapter.jetScalar F ζ hζ C R P H U a ι f k s p‖ ^ 2 ≤
        KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p := by
      unfold KPContActualChamberMeanZeroAdapter.energyDensity KPContActualChamberMeanZeroAdapter.gradientSq
      simp only [mul_zero, zero_mul, Real.exp_zero, one_mul]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => sq_nonneg _)
    have henergy : 0 ≤ KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p :=
      (sq_nonneg _).trans he
    calc
      _ ≤ ENNReal.ofReal (2 * (KPContActualChamberOutgoingAdapter.jetNorm
          F ζ hζ C R P H U a ι buffer f χ source k 0 s p) ^ 2 +
          2 * KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p) :=
        ENNReal.ofReal_le_ofReal (hh.trans (by linarith))
      _ = _ := by rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]; norm_num
  calc
    _ ≤ ∫⁻ p in {p : KPCuspCharts.Coordinates F | A < p.2},
        (2 : ℝ≥0∞) * ENNReal.ofReal ((KPContActualChamberOutgoingAdapter.jetNorm
          F ζ hζ C R P H U a ι buffer f χ source k 0 s p) ^ 2) +
        (2 : ℝ≥0∞) * ENNReal.ofReal
          (KPContActualChamberMeanZeroAdapter.energyDensity F ζ hζ C R P H U a ι f k s 0 p)
        ∂KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a :=
      setLIntegral_mono' (measurableSet_lt measurable_const (by fun_prop)) (by intro p hp; exact hsplit p hp)
    _ ≤ (2 : ℝ≥0∞) * KPContActualChamberOutgoingAdapter.squareTail F ζ hζ C R P H U
        a ι buffer f χ source k 0 s A +
        (2 : ℝ≥0∞) * KPContActualChamberMeanZeroAdapter.energy F ζ hζ C R P H U a ι f k s 0 A := by
      have hmnorm : AEMeasurable (fun p => ENNReal.ofReal
          ((KPContActualChamberOutgoingAdapter.jetNorm F ζ hζ C R P H U a ι buffer f χ source k 0 s p) ^ 2))
          ((KPContActualChamberOutgoingAdapter.endMeasure F ζ hζ C R P H U a).restrict {p | A < p.2}) := by
        have hh := ((hbound a s hs).1.aestronglyMeasurable.mono_measure
          (Measure.restrict_mono (fun p hp => lt_of_le_of_lt h0A hp) le_rfl)).aemeasurable
        exact (hh.pow_const 2).ennreal_ofReal
      rw [lintegral_add_left' (hmnorm.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
        lintegral_const_mul' _ _ (by norm_num)]
      exact le_rfl
    _ ≤ 2 * ENNReal.ofReal c + 2 * ENNReal.ofReal b := add_le_add (mul_le_mul_right hout _) (mul_le_mul_right hmean _)
    _ = ENNReal.ofReal (2*c+2*b) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem lineG_borelL2 (k : ℕ) (s : ℂ) :
    lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈
      BorelL2Sections F ζ hζ C R P H U := by
  by_cases hs : s ∈ V
  · obtain ⟨A,B,hA,hB,hbound⟩ := lineG_high_end_square_bound
      F ζ hζ C R P H U ι f buffer χ source hι hf {s} isCompact_singleton
      (Set.singleton_subset_iff.mpr hs) k
    let E : Set (Base F ζ hζ C R P H U) := ⋃ a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U,
      KPContActualCollarBuffer.endSet F ζ hζ (level F ζ hζ C R P H U) R P H A a
    have hE : MeasurableSet E := (isOpen_iUnion (fun a => KPContActualCollarBuffer.all_ends_open
      F ζ hζ (level F ζ hζ C R P H U) R P H A a)).measurableSet
    have hEc : IsCompact Eᶜ := KPContActualCollarBuffer.compact_truncated_core
      F ζ hζ (level F ζ hζ C R P H U) R P H A
    refine ⟨fun i => ((smooth F ζ hζ C R P H U ι f buffer χ source hι hf k s).1 i).continuous.measurable, ?_⟩
    unfold KPContSectorLineL2Isometry.normIntegral
    rw [← lintegral_add_compl _ hE]
    apply ENNReal.add_lt_top.mpr
    refine ⟨?_, lineG_compact_square_finite F ζ hζ C R P H U ι f buffer χ source hι hf k s Eᶜ hEc⟩
    apply lt_of_le_of_lt (lintegral_iUnion_le _ _)
    rw [tsum_fintype]
    apply ENNReal.sum_lt_top.mpr
    intro a ha
    exact (hbound a s (Set.mem_singleton s)).trans_lt ENNReal.ofReal_lt_top
  · have he : lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s = 0 := by
      simp [lineG, coveredG, hs]
    rw [he]
    exact (BorelL2Sections F ζ hζ C R P H U).zero_mem

include hι hf in

theorem g_memLp (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    MemLp (g F ζ hζ C R P H U ι f buffer χ source k s) 2 (measure F ζ hζ C R P H U) := by
  have hm := lineG_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf k s
  have he : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ (level F ζ hζ C R P H U)
      R P H (lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s)).val =
      g F ζ hζ C R P H U ι f buffer χ source k s := by
    rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
    unfold lineG
    rw [LinearEquiv.symm_apply_apply]
    simp [coveredG, hs]
  rw [← he]
  exact (KPContSectorLineL2Isometry.finite_integral_iff F ζ hζ
    (level F ζ hζ C R P H U) R P H _ hm.1).mp hm.2

include hι hf in

theorem h_memLp (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    MemLp (h F ζ hζ C R P H U ι f buffer χ source k s) 2 (measure F ζ hζ C R P H U) := by
  have hm := lineH_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf k s
  have he : (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ (level F ζ hζ C R P H U)
      R P H (lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s)).val =
      h F ζ hζ C R P H U ι f buffer χ source k s := by
    rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
    unfold lineH
    rw [LinearEquiv.symm_apply_apply]
    simp [coveredH, hs]
  rw [← he]
  exact (KPContSectorLineL2Isometry.finite_integral_iff F ζ hζ
    (level F ζ hζ C R P H U) R P H _ hm.1).mp hm.2

theorem lineDelta_zero (k : ℕ) (s : ℂ) (hs : s ∉ V) :
    lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s = 0 := by
  have he : lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s = 0 := by
    simp [lineG, coveredG, hs]
  funext i
  apply Subtype.ext
  funext y
  change HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
    ((lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s i).val ∘
      KPCuspCutoffGraph.toArch F) (KPCuspCutoffGraph.fromArch F y) = 0
  rw [he]
  have hd : ∀ j l, HyperbolicChart.coordinateDerivative
      (KPCuspLogShape.dimension F) j l (fun _ => (0 : ℂ)) = 0 := by
    intro j l
    funext x
    simp [HyperbolicChart.coordinateDerivative]
  simp [HyperbolicChart.laplacian, Function.comp_def, hd,
    HyperbolicChart.coordinateDerivative]

theorem lineDelta_borelL2_outside (k : ℕ) (s : ℂ) (hs : s ∉ V) :
    lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈
      BorelL2Sections F ζ hζ C R P H U := by
  rw [lineDelta_zero F ζ hζ C R P H U ι f buffer χ source hι hf k s hs]
  exact (BorelL2Sections F ζ hζ C R P H U).zero_mem

theorem lineDelta_eq_rhs (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualChamberCasimirJets.lambda F s • lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s -
      lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s +
      ∑ j ∈ Finset.Icc 1 (min k 2),
        ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
          lineG F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s := by
  funext i
  apply Subtype.ext
  funext y
  let O := (KPContSectorPhaseComponentCharts.orbifoldChart_exists F ζ hζ
    (level F ζ hζ C R P H U) R P H i y).some
  let a : Frame F ζ hζ C R P H U i := {
    kind := .orbifold y O
    places := KPContCotangentActualOverlap.placeEquiv F ζ hζ
    splitting := fun _ => 1
    splitting_locallyConstant := IsLocallyConstant.const 1 }
  let x := KPContCotangentActualOverlap.labeledAInv a.places y
  have hxy : KPContCotangentActualOverlap.labeledA a.places x = y := by
    funext j
    simp [x, KPContCotangentActualOverlap.labeledAInv,
      KPContCotangentActualOverlap.labeledA]
  have hx : x ∈ a.omega := by
    change KPContCotangentActualOverlap.labeledA a.places x ∈ O.neighborhood
    rw [hxy]
    exact O.center_mem
  have hc (w : Sections F ζ hζ C R P H U) : a.coefficient w x = (w i).val y := by
    simp [KPContCotangentActualOverlap.LiftedChart.coefficient, a,
      KPContCotangentActualOverlap.ChartKind.representative, hxy]
  have he := defect_frame_equation F ζ hζ C R P H U ι f buffer χ source hι hf k s hs i a x hx
  rw [← lineDelta_frame F ζ hζ C R P H U ι f buffer χ source hι hf k s i a x hx] at he
  simp only [hc] at he
  simpa only [Pi.add_apply, Pi.sub_apply, Submodule.coe_add,
    Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_sum,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc] using he

private theorem laplacian_l2_from_rhs (k : ℕ) (s : ℂ)
    (he : lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualChamberCasimirJets.lambda F s • lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s -
      lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s +
      ∑ j ∈ Finset.Icc 1 (min k 2),
        ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
          lineG F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s) :
    lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈ BorelL2Sections F ζ hζ C R P H U := by
  rw [he]
  apply Submodule.add_mem
  · exact Submodule.sub_mem _ (Submodule.smul_mem _ _
      (lineG_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf k s))
      (lineH_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf k s)
  · exact Submodule.sum_mem _ (fun j hj => Submodule.smul_mem _ _
      (lineG_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s))

theorem integrability (k : ℕ) (s : ℂ) :
    lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈ BorelL2Sections F ζ hζ C R P H U ∧
    lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈ BorelL2Sections F ζ hζ C R P H U ∧
    lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s ∈ BorelL2Sections F ζ hζ C R P H U := by
  refine ⟨lineG_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf k s,
    lineH_borelL2 F ζ hζ C R P H U ι f buffer χ source hι hf k s, ?_⟩
  by_cases hs : s ∈ V
  · exact laplacian_l2_from_rhs F ζ hζ C R P H U ι f buffer χ source hι hf k s
      (lineDelta_eq_rhs F ζ hζ C R P H U ι f buffer χ source hι hf k s hs)
  · exact lineDelta_borelL2_outside F ζ hζ C R P H U ι f buffer χ source hι hf k s hs

def borelG (k : ℕ) (s : ℂ) : BorelL2Sections F ζ hζ C R P H U :=
  ⟨_, (integrability F ζ hζ C R P H U ι f buffer χ source hι hf k s).1⟩

def borelH (k : ℕ) (s : ℂ) : BorelL2Sections F ζ hζ C R P H U :=
  ⟨_, (integrability F ζ hζ C R P H U ι f buffer χ source hι hf k s).2.1⟩

def borelDelta (k : ℕ) (s : ℂ) : BorelL2Sections F ζ hζ C R P H U :=
  ⟨_, (integrability F ζ hζ C R P H U ι f buffer χ source hι hf k s).2.2⟩

def UJet (k : ℕ) (s : ℂ) : Sector F ζ hζ C R P H U :=
  KPContSectorLineL2Isometry.toSector F ζ hζ (level F ζ hζ C R P H U) R P H
    (borelG F ζ hζ C R P H U ι f buffer χ source hι hf k s)

def HJet (k : ℕ) (s : ℂ) : Sector F ζ hζ C R P H U :=
  KPContSectorLineL2Isometry.toSector F ζ hζ (level F ζ hζ C R P H U) R P H
    (borelH F ζ hζ C R P H U ι f buffer χ source hι hf k s)

def DeltaJet (k : ℕ) (s : ℂ) : Sector F ζ hζ C R P H U :=
  KPContSectorLineL2Isometry.toSector F ζ hζ (level F ζ hζ C R P H U) R P H
    (borelDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s)

private theorem differential_class_from_rhs (k : ℕ) (s : ℂ)
    (he : lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualChamberCasimirJets.lambda F s • lineG F ζ hζ C R P H U ι f buffer χ source hι hf k s -
      lineH F ζ hζ C R P H U ι f buffer χ source hι hf k s +
      ∑ j ∈ Finset.Icc 1 (min k 2),
        ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
          lineG F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s) :
    DeltaJet F ζ hζ C R P H U ι f buffer χ source hι hf k s =
      KPContActualChamberCasimirJets.lambda F s • UJet F ζ hζ C R P H U ι f buffer χ source hι hf k s -
      HJet F ζ hζ C R P H U ι f buffer χ source hι hf k s +
      ∑ j ∈ Finset.Icc 1 (min k 2),
        ((Nat.choose k j : ℂ) * KPContActualChamberCasimirJets.lambdaJet F j s) •
          UJet F ζ hζ C R P H U ι f buffer χ source hι hf (k-j) s := by
  unfold DeltaJet UJet HJet
  simp_rw [← map_smul]
  rw [← map_sub, ← map_sum, ← map_add]
  congr 1
  apply Subtype.ext
  simpa only [borelDelta, borelG, borelH, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_smul, Submodule.coe_sum] using he


theorem jets_actual_ae (k : ℕ) (s : ℂ) (hs : s ∈ V) :
    ((UJet F ζ hζ C R P H U ι f buffer χ source hι hf k s).val : Covered F ζ hζ C R P H U → ℂ)
      =ᵐ[measure F ζ hζ C R P H U] g F ζ hζ C R P H U ι f buffer χ source k s ∧
    ((HJet F ζ hζ C R P H U ι f buffer χ source hι hf k s).val : Covered F ζ hζ C R P H U → ℂ)
      =ᵐ[measure F ζ hζ C R P H U] h F ζ hζ C R P H U ι f buffer χ source k s ∧
    ((DeltaJet F ζ hζ C R P H U ι f buffer χ source hι hf k s).val : Covered F ζ hζ C R P H U → ℂ)
      =ᵐ[measure F ζ hζ C R P H U]
        (KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ
          (level F ζ hζ C R P H U) R P H
          (lineDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s)).val := by
  have hg := MemLp.coeFn_toLp (KPContSectorLineL2Isometry.representative_memLp F ζ hζ
    (level F ζ hζ C R P H U) R P H (borelG F ζ hζ C R P H U ι f buffer χ source hι hf k s))
  have hh := MemLp.coeFn_toLp (KPContSectorLineL2Isometry.representative_memLp F ζ hζ
    (level F ζ hζ C R P H U) R P H (borelH F ζ hζ C R P H U ι f buffer χ source hι hf k s))
  have hd := MemLp.coeFn_toLp (KPContSectorLineL2Isometry.representative_memLp F ζ hζ
    (level F ζ hζ C R P H U) R P H (borelDelta F ζ hζ C R P H U ι f buffer χ source hι hf k s))
  refine ⟨?_,?_,hd⟩
  · exact hg.trans (Filter.Eventually.of_forall (fun x => by
      simp [borelG, lineG, coveredG, hs,
        KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]))
  · exact hh.trans (Filter.Eventually.of_forall (fun x => by
      simp [borelH, lineH, coveredH, hs,
        KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]))

/-- The undifferentiated defect satisfies the inhomogeneous eigenvalue equation
in the Hilbert space of genuine sections. -/
theorem deltaJet_zero (s : ℂ) (hs : s ∈ V) :
    DeltaJet F ζ hζ C R P H U ι f buffer χ source hι hf 0 s =
      KPContActualChamberCasimirJets.lambda F s • UJet F ζ hζ C R P H U ι f buffer χ source hι hf 0 s -
      HJet F ζ hζ C R P H U ι f buffer χ source hι hf 0 s := by
  simpa using differential_class_from_rhs F ζ hζ C R P H U ι f buffer χ source hι hf 0 s
    (lineDelta_eq_rhs F ζ hζ C R P H U ι f buffer χ source hι hf 0 s hs)

end DedekindZetaZeroFree.KPContActualChamberThreeL2Tails

end
