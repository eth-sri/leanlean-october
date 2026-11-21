module

public import DedekindZetaZeroFree.Adeles.Quotients.LineSections.ChartRestrictionDensity
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.CommutatorHilbertHolomorphy
public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.LocalCommutatorEquation

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section
open scoped Classical NumberField ContDiff ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualAllCuspSource

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev level := KPContActualCutoffSmoothDescent.level F ζ hζ C R P H U
abbrev Base := KPContActualCutoffSmoothDescent.Base F ζ hζ C R P H U
abbrev Covered := KPContActualCutoffSmoothDescent.Covered F ζ hζ C R P H U
abbrev Cusps := KPContActualCutoffSmoothDescent.Cusps F ζ hζ C R P H U
abbrev SmoothSections := KPContActualCutoffSmoothDescent.SmoothSections F ζ hζ C R P H U

abbrev Sector := KPContSectorClosedLpSubspace.H F ζ hζ R (level F ζ hζ C R P H U)

abbrev measure := KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R
  (level F ζ hζ C R P H U)

def chartCoefficient (w : SmoothSections F ζ hζ C R P H U)
    (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
    (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ (level F ζ hζ C R P H U)) :
    KPContLocalNorm.Space (KPCuspLogShape.dimension F * 3) → ℂ :=
  KPContActualChartRestrictionDensity.frameCoefficient F ζ hζ
    (level F ζ hζ C R P H U) R P H
    ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ (level F ζ hζ C R P H U)
      R P H).symm w).val i m

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)

abbrev K := KPContActualCollarBuffer.collars F ζ hζ
  (level F ζ hζ C R P H U) R P H B.τ T

structure Source (Ω : Set ℂ) (f : ℂ → S)
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T) where
  descent : KPContActualCutoffSmoothDescent.Descent F ζ hζ C R P H U ι B Ω f χ
  compact_collars : IsCompact (K F ζ hζ C R P H U B)

  support : ∀ s ∈ Ω, tsupport
    (KPContSectorSmoothFramesSupport.sectionNorm F ζ hζ (level F ζ hζ C R P H U)
      R P H (descent.commutator s).val) ⊆ K F ζ hζ C R P H U B

  local_equation : ∀ s ∈ Ω,
    ∀ (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
      (z : KPFiniteCuspAtlas.SymmetricSpace F),
    KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
      ((descent.cutoff s).val i).val z -
        KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s *
          ((descent.cutoff s).val i).val z = ((descent.commutator s).val i).val z

  h : ℂ → Sector F ζ hζ C R P H U
  hilbert_holomorphic : DifferentiableOn ℂ h Ω
  source_ae : ∀ s ∈ Ω,
    ((h s : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R (level F ζ hζ C R P H U)) :
      Covered F ζ hζ C R P H U → ℂ) =ᵐ[measure F ζ hζ C R P H U]
        KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U (descent.commutator s)

  line_representative : ∀ s ∈ Ω,
    ∃ g : KPContSectorLineL2Isometry.BorelL2Scalars F ζ hζ
        (level F ζ hζ C R P H U) R,
      g.val.val = KPContActualCutoffSmoothDescent.scalar F ζ hζ C R P H U
        (descent.commutator s) ∧
      KPContSectorLineL2Isometry.scalarEmbedding F ζ hζ (level F ζ hζ C R P H U)
        R P H g = h s ∧
      KPContSectorScalarLineAlgebra.S F ζ hζ (level F ζ hζ C R P H U) R P H g.val =
        (descent.commutator s).val
  local_holomorphy :
    ∀ (i : Fin (H.atlas (level F ζ hζ C R P H U)).componentCount)
      (x : KPFiniteCuspAtlas.SymmetricSpace F)
      (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ
        (level F ζ hζ C R P H U) R P H i x)
      (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ (level F ζ hζ C R P H U))
      (A : KPContLocalNorm.LocalBall (KPCuspLogShape.dimension F * 3)),
    KPContLocalCubeEmbedding.closedCarrier A ⊆
      KPContActualChartRestrictionDensity.chartDomain F ζ hζ
        (level F ζ hζ C R P H U) R P H i x O →
    KPCutoffSource.ChartSmoothHolomorphicOn A
      (fun s => chartCoefficient F ζ hζ C R P H U (descent.cutoff s) i m) Ω ∧
    KPCutoffSource.ChartSmoothHolomorphicOn A
      (fun s => chartCoefficient F ζ hζ C R P H U (descent.commutator s) i m) Ω

end DedekindZetaZeroFree.KPContActualAllCuspSource

namespace DedekindZetaZeroFree

private theorem allCusp_coordinate_reindex {n m : ℕ} (h : n = m)
    (p : KPContLocalNorm.Space (m * 3)) :
    (fun i : Fin m => CotangentLogCoframe.A n
      (WithLp.toLp 2 (fun ik : Fin n × Fin 3 =>
        (cast (congrArg (fun k => KPContLocalNorm.Space (k * 3)) h.symm) p)
          (finProdFinEquiv ik))) ((finCongr h).symm i)) =
      (fun i : Fin m => ((⟨p (finProdFinEquiv (i, 0)), p (finProdFinEquiv (i, 1))⟩ : ℂ),
        p (finProdFinEquiv (i, 2)))) := by
  subst m
  funext i
  apply Prod.ext
  · apply Complex.ext <;> simp [CotangentLogCoframe.A, finCongr]
  · simp [CotangentLogCoframe.A, finCongr]

private theorem allCusp_chart_transport {n m : ℕ} (h : n = m)
    (A : KPContLocalNorm.LocalBall m) (g v : ℂ → KPContLocalNorm.Space m → ℂ)
    (g' v' : ℂ → KPContLocalNorm.Space n → ℂ) (Ω : Set ℂ)
    (hg : ∀ s x, g' s (cast (congrArg KPContLocalNorm.Space h.symm) x) = g s x)
    (hv : ∀ s x, v' s (cast (congrArg KPContLocalNorm.Space h.symm) x) = v s x)
    (H : KPCutoffSource.ChartSmoothHolomorphicOn
        (cast (congrArg KPContLocalNorm.LocalBall h.symm) A) g' Ω ∧
      KPCutoffSource.ChartSmoothHolomorphicOn
        (cast (congrArg KPContLocalNorm.LocalBall h.symm) A) v' Ω) :
    KPCutoffSource.ChartSmoothHolomorphicOn A g Ω ∧
      KPCutoffSource.ChartSmoothHolomorphicOn A v Ω := by
  subst m
  have hgg : g' = g := funext (fun s => funext (hg s))
  have hvv : v' = v := funext (fun s => funext (hv s))
  simpa [hgg, hvv] using H

private theorem allCusp_closedBall_transport {n m : ℕ} (h : n = m)
    (A : KPContLocalNorm.LocalBall m) (V : Set (KPContLocalNorm.Space m))
    (V' : Set (KPContLocalNorm.Space n))
    (hV : ∀ x, cast (congrArg KPContLocalNorm.Space h.symm) x ∈ V' ↔ x ∈ V)
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ V) :
    Metric.closedBall
      (cast (congrArg KPContLocalNorm.LocalBall h.symm) A).center
      (cast (congrArg KPContLocalNorm.LocalBall h.symm) A).radius ⊆ V' := by
  subst m
  intro x hx
  exact (hV x).mpr (hA hx)

theorem kp_cont_actual_all_cusp_source
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (_hR : KPContActualFixedSectorRealization.LevelRealization F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    (hι : Function.Injective ι)
    (Ω : Set ℂ) (hΩopen : IsOpen Ω) (hΩ : Ω ⊆ KPContinuation.spectralDomain)
    (f : ℂ → S) (hf : DifferentiableOn ℂ f Ω)
    (T : ℝ) (hT : (H.atlas (KPContActualAllCuspSource.level F ζ hζ C R P H U)).threshold < T)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T) :
    ∃ B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T,
      Nonempty (KPContActualAllCuspSource.Source F ζ hζ C R P H U ι B Ω f χ) := by
  obtain ⟨B⟩ := kp_cont_actual_collar_buffer F ζ hζ
    (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H _hR T hT
  obtain ⟨D⟩ := kp_cont_actual_cutoff_smooth_descent F ζ hζ C R P H U B ι Ω hΩ f χ
  obtain ⟨HH⟩ := kp_cont_actual_commutator_hilbert_holomorphy F ζ hζ C R P H U _hR B ι hι
    Ω hΩopen hΩ f hf χ D
  refine ⟨B, ⟨{ descent := D,
                 compact_collars := B.compact_collars,
                 support := D.support,
                 local_equation := ?_,
                 h := HH.h,
                 hilbert_holomorphic := HH.holomorphic,
                 source_ae := HH.inclusion,
                 line_representative := HH.representative,
                 local_holomorphy := ?_ }⟩⟩
  · intro s hs i z
    have hh := congrArg (fun w : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U =>
      (w.val i).val z) 
        (KPContActualCutoffLocalCommutator.section_equation F ζ hζ C R P H U
          ι B Ω hΩ f χ D s hs)
    change KPContActualSphericalFlatStage.localLaplacian (KPCuspLogShape.dimension F)
        ((D.cutoff s).val i).val z -
      KPContinuation.spectralCoordinate ((Module.finrank ℚ F / 2 : ℕ) : ℤ) s *
        ((D.cutoff s).val i).val z = ((D.commutator s).val i).val z at hh
    exact hh
  · intro i x O m A hA
    obtain ⟨ε, rfl⟩ := Quotient.mk_surjective m
    let q : KPContActualCutoffChartJetHolomorphy.Chart F ζ hζ C R P H U i :=
      { kind := .orbifold x O
        places := KPContCotangentActualOverlap.placeEquiv F ζ hζ
        splitting := fun _ => ε
        splitting_locallyConstant := IsLocallyConstant.const ε }
    let hd : KPContCotangentActualOverlap.d F = KPCuspLogShape.dimension F :=
      (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1.symm
    let hn : KPContActualCutoffChartJetHolomorphy.dimension F = KPCuspLogShape.dimension F * 3 :=
      congrArg (fun n => n * 3) hd
    let A' : KPContLocalNorm.LocalBall (KPContActualCutoffChartJetHolomorphy.dimension F) :=
      cast (congrArg KPContLocalNorm.LocalBall hn.symm) A
    have hcoord (p : KPContLocalNorm.Space (KPCuspLogShape.dimension F * 3)) :
        KPContCotangentActualOverlap.labeledA q.places
          (KPContActualCutoffChartJetHolomorphy.coordinates F
            (cast (congrArg KPContLocalNorm.Space hn.symm) p)) =
          KPContActualChartRestrictionDensity.coordinates F p := by
      exact allCusp_coordinate_reindex hd p
    have hdom (p : KPContLocalNorm.Space (KPCuspLogShape.dimension F * 3)) :
        cast (congrArg KPContLocalNorm.Space hn.symm) p ∈
          KPContActualCutoffChartJetHolomorphy.chartDomain F ζ hζ C R P H U q ↔
        p ∈ KPContActualChartRestrictionDensity.chartDomain F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H i x O := by
      change KPContCotangentActualOverlap.labeledA q.places
        (KPContActualCutoffChartJetHolomorphy.coordinates F _) ∈ O.neighborhood ↔ _
      rw [hcoord]
      rfl
    have hA' : Metric.closedBall A'.center A'.radius ⊆
        KPContActualCutoffChartJetHolomorphy.chartDomain F ζ hζ C R P H U q :=
      allCusp_closedBall_transport hn A _ _ hdom hA
    have hj := kp_cont_actual_cutoff_chart_jet_holomorphy F ζ hζ C R P H U _hR B ι hι
      Ω hΩ hΩopen f hf χ D i q A' hA'
    have hframe (w : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U)
        (p : KPContLocalNorm.Space (KPCuspLogShape.dimension F * 3)) :
        KPContActualCutoffChartJetHolomorphy.framePullback F ζ hζ C R P H U q w
          (cast (congrArg KPContLocalNorm.Space hn.symm) p) =
          KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U w i
            (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ
              (KPContActualAllCuspSource.level F ζ hζ C R P H U) ε) p := by
      unfold KPContActualAllCuspSource.chartCoefficient
      rw [KPContActualChartRestrictionDensity.frameCoefficient_class]
      have hS : KPContSectorScalarLineAlgebra.S F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
          ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ
            (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H).symm w).val = w.val := by
        rw [← KPContSectorSmoothFramesSupport.smoothS_apply]
        simp
      rw [hS]
      simp only [KPContActualCutoffChartJetHolomorphy.framePullback,
        KPContCotangentActualOverlap.LiftedChart.coefficient, q,
        KPContCotangentActualOverlap.ChartKind.representative, one_smul]
      rw [hcoord]
      rfl
    apply allCusp_chart_transport hn A _ _
      (KPContActualCutoffChartJetHolomorphy.pullback F ζ hζ C R P H U ι B Ω f χ D q false)
      (KPContActualCutoffChartJetHolomorphy.pullback F ζ hζ C R P H U ι B Ω f χ D q true) Ω
    · intro s p
      exact hframe (D.cutoff s) p
    · intro s p
      exact hframe (D.commutator s) p
    · exact ⟨hj.on_ball false, hj.on_ball true⟩
end DedekindZetaZeroFree

end
