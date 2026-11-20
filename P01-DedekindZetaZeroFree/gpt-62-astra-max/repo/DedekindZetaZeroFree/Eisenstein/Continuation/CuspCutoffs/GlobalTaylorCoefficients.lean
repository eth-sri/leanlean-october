module

public import DedekindZetaZeroFree.Eisenstein.Continuation.SmoothHolomorphy.TaylorData

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCutoffPlusClearedGerm

section CauchyHelpers
set_option maxHeartbeats 600000
open KPContLocalNorm KPContLocalHolomorphyUpgrade.CauchyAssembly

private alias chartJetContinuous := DedekindZetaZeroFree.KPContActualCutoffChartJetHolomorphy.ChartJetHolomorphy.ballJet_continuous

private alias scalarJetHolomorphic := DedekindZetaZeroFree.KPContActualCutoffChartJetHolomorphy.ChartJetHolomorphy.ballScalarJet_holomorphic

 def scalarCauchy (f : ℂ → ℂ) (c : ℂ) (ρ : ℝ) (j : ℕ) : ℂ :=
  (cauchyPowerSeries f c ρ j) (fun _ => 1)

private theorem scalarCauchySeries {n : ℕ} (A : LocalBall n) (Ω : Set ℂ)
    (f : ℂ → Space n → ℂ) (hf : KPCutoffSource.ChartSmoothHolomorphicOn A f Ω)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hclosed : Metric.closedBall c ρ ⊆ Ω) :
    SmoothPowerSeriesOn A c ρ (fun j x => scalarCauchy (fun s => f s x) c ρ j) f := by
  let b := fun j x => scalarCauchy (fun s => f s x) c ρ j
  have hj := chartJetContinuous A Ω f hf
  have hb := fun j => ContourLift.coefficient_smooth_and_derivatives A Ω f hf.1 hj c ρ hρ hclosed j
  refine ⟨fun j => (hb j).1, fun s hs => hf.1 s (hclosed (Metric.ball_subset_closedBall hs)), ?_⟩
  intro K hK hKA m r hr hrρ ε hε
  have hhol : ∀ m (α : MultiIndex n m) x, x ∈ A.carrier →
      DifferentiableOn ℂ (fun s => coordinateDerivative α (f s) x) (Metric.ball c ρ) := fun m α x hx => (scalarJetHolomorphic A Ω f hf m α x hx).mono (Metric.ball_subset_closedBall.trans hclosed)
  obtain ⟨N, hN⟩ := ContourLift.scalar_jet_cauchy_uniform A Ω f hf.1 hj c ρ hρ hclosed hhol
    K hK hKA m r hr hrρ ε hε
  refine ⟨N, ?_⟩
  intro M hM z hz α x
  rw [coordinate_derivative_taylor_remainder A b (fun j => (hb j).1) (f z) (hf.1 z (hclosed ((Metric.closedBall_subset_closedBall hrρ.le) hz)))
    (z - c) M α (hKA x.property)]
  have hd : ∀ j, coordinateDerivative α (b j) x = scalarCauchy
      (fun s => coordinateDerivative α (f s) x) c ρ j := fun j => (hb j).2 m α (hKA x.property)
  simp only [hd]
  exact hN M hM z hz α x

 theorem scalarCauchy_const_mul (a : ℂ) (f : ℂ → ℂ) (c : ℂ) (ρ : ℝ) (j : ℕ) :
    scalarCauchy (fun z => a * f z) c ρ j = a * scalarCauchy f c ρ j := by
  simp only [scalarCauchy, cauchyPowerSeries_apply, one_div, smul_eq_mul]
  have he : (fun z => (z - c)⁻¹ ^ j * ((z - c)⁻¹ * (a * f z))) =
      fun z => a * ((z - c)⁻¹ ^ j * ((z - c)⁻¹ * f z)) := by funext z; ring
  rw [he, circleIntegral.integral_const_mul]
  ring

open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContSectorScalarLineAlgebra KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry
open KPContActualChartRestrictionDensity KPContActualSmoothLineGluing
open NumberField IsDedekindDomain
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
  (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
  (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
  (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

private theorem coefficient_identity (w : Sections F ζ hζ U R P H)
    (A : ChartBall F ζ hζ U R P H) (hphase : A.phase = phaseClass F ζ hζ U 1)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    coefficient F ζ hζ U R P H w A p = (w A.component).val (coordinates F p) := by
  unfold coefficient
  rw [hphase, frameCoefficient_class, scalarRepresentative_eq_symm, LinearEquiv.apply_symm_apply]
  simp

 def cauchySections (w : ℂ → smoothSections F ζ hζ U R P H)
    (c : ℂ) (ρ : ℝ) (j : ℕ) : Sections F ζ hζ U R P H := by
  intro i
  refine ⟨fun x => scalarCauchy (fun s => ((w s).val i).val x) c ρ j, ?_, ?_⟩
  · intro x ε hε
    exact (scalarCauchy_const_mul _ _ c ρ j).symm.trans (congrArg (fun f => scalarCauchy f c ρ j) (funext fun s => ((w s).val i).property.1 x ε hε))
  · intro γ x
    exact (congrArg (fun f => scalarCauchy f c ρ j) (funext fun s => ((w s).val i).property.2 γ x)).trans (scalarCauchy_const_mul _ _ c ρ j)

 section

variable (w : ℂ → smoothSections F ζ hζ U R P H) (Ω : Set ℂ)
    (hlocal : ∀ A : ChartBall F ζ hζ U R P H, KPCutoffSource.ChartSmoothHolomorphicOn A.ball (fun s => coefficient F ζ hζ U R P H (w s).val A) Ω)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hclosed : Metric.closedBall c ρ ⊆ Ω) (j : ℕ)

include hlocal hρ hclosed in
theorem cauchySections_smooth :
    IsSmoothSections F ζ hζ U R P H (cauchySections F ζ hζ U R P H w c ρ j) := by
  intro i
  let cauchySections₀ := cauchySections F ζ hζ U R P H w c ρ j i
  have hsp : ContDiff ℝ (⊤ : ℕ∞) (fun p =>
      (cauchySections₀).val (coordinates F p)) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    let A := canonicalChartBall F ζ hζ U R P H i (coordinates F p) (phaseClass F ζ hζ U 1)
    have hp : p ∈ A.ball.carrier := by
      simpa only [Homeomorph.symm_apply_apply] using canonicalChartBall_mem F ζ hζ U R P H i
        (coordinates F p) (phaseClass F ζ hζ U 1)
    have hf := hlocal A
    refine ((((ContourLift.coefficient_smooth_and_derivatives A.ball Ω _ hf.1
      (chartJetContinuous A.ball Ω _ hf) c ρ hρ hclosed j).1) p hp).contDiffAt (Metric.isOpen_ball.mem_nhds hp)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (congrFun ?_))
    funext q
    apply congrArg (fun f => scalarCauchy f c ρ j)
    funext s
    exact (coefficient_identity F ζ hζ U R P H (w s).val A rfl q).symm
  have hc := hsp.comp (CoreChartLocalizers.CutoffConstruction.ChartDensityConstruction.coordinates_symm_contDiff
    (KPCuspLogShape.dimension F))
  have he : ((fun p => (cauchySections₀).val (coordinates F p)) ∘
      (coordinates F).symm) = (cauchySections₀).val := by
    funext x
    exact congrArg (cauchySections₀).val ((coordinates F).apply_symm_apply x)
  change ContDiff ℝ (⊤ : ℕ∞) ((fun p => (cauchySections₀).val
    (coordinates F p)) ∘ (coordinates F).symm) at hc
  rwa [he] at hc

 def cauchySmoothSections :
    smoothSections F ζ hζ U R P H :=
  ⟨cauchySections F ζ hζ U R P H w c ρ j,
    cauchySections_smooth F ζ hζ U R P H w Ω hlocal c ρ hρ hclosed j⟩

end

variable (w : ℂ → smoothSections F ζ hζ U R P H)

private theorem cauchySections_coefficient
    (c : ℂ) (ρ : ℝ) (j : ℕ) (A : ChartBall F ζ hζ U R P H)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    coefficient F ζ hζ U R P H (cauchySections F ζ hζ U R P H w c ρ j) A p =
      scalarCauchy (fun s => coefficient F ζ hζ U R P H (w s).val A p) c ρ j := by
  obtain ⟨ε, hε⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) A.phase
  change phaseClass F ζ hζ U ε = A.phase at hε
  have hcoef (v : Sections F ζ hζ U R P H) : coefficient F ζ hζ U R P H v A p =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * (v A.component).val (coordinates F p) := by
    unfold coefficient
    rw [← hε, frameCoefficient_class, scalarRepresentative_eq_symm, LinearEquiv.apply_symm_apply, chi_coe]
  rw [hcoef]
  change _ * scalarCauchy (fun s => ((w s).val A.component).val (coordinates F p)) c ρ j = _
  rw [← scalarCauchy_const_mul]
  apply congrArg (fun f => scalarCauchy f c ρ j)
  funext s
  exact (hcoef (w s).val).symm

private theorem genuineCommonDisk (Ω : Set ℂ)
    (hlocal : ∀ A : ChartBall F ζ hζ U R P H, KPCutoffSource.ChartSmoothHolomorphicOn A.ball
      (fun s => coefficient F ζ hζ U R P H (w s).val A) Ω)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hclosed : Metric.closedBall c ρ ⊆ Ω) :
    ∃ b : ℕ → smoothSections F ζ hζ U R P H, ∀ A : ChartBall F ζ hζ U R P H,
      SmoothPowerSeriesOn A.ball c ρ (fun j => coefficient F ζ hζ U R P H (b j).val A)
        (fun s => coefficient F ζ hζ U R P H (w s).val A) := by
  refine ⟨cauchySmoothSections F ζ hζ U R P H w Ω hlocal c ρ hρ hclosed, ?_⟩
  intro A
  have he : (fun j => coefficient F ζ hζ U R P H
      (cauchySmoothSections F ζ hζ U R P H w Ω hlocal c ρ hρ hclosed j).val A) =
      fun j p => scalarCauchy (fun s => coefficient F ζ hζ U R P H (w s).val A p) c ρ j := by
    funext j p
    exact cauchySections_coefficient F ζ hζ U R P H w c ρ j A p
  rw [he]
  exact scalarCauchySeries A.ball Ω _ (hlocal A) c ρ hρ hclosed

end CauchyHelpers

theorem actual_cutoff_common_disk_coefficients
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
    {T : ℝ}
    (Ω : Set ℂ) (f : ℂ → S)
    (χ : KPContActualAllCuspSource.Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
      (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H T)
    (source : KPContActualAllCuspSource.Source F ζ hζ C R P H U ι buffer Ω f χ)
    (hΩ : IsOpen Ω) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hclosed : Metric.closedBall c ρ ⊆ Ω) :
    ∃ b : ℕ → KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U,
      ∀ A : KPContActualSmoothLineGluing.ChartBall F ζ hζ
        (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H,
      KPContLocalNorm.SmoothPowerSeriesOn A.ball c ρ
        (fun j => KPContActualSmoothLineGluing.coefficient F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H (b j).val A)
        (fun s => KPContActualSmoothLineGluing.coefficient F ζ hζ
          (KPContActualAllCuspSource.level F ζ hζ C R P H U) R P H
          (source.descent.cutoff s).val A) := by
  let V := KPContActualAllCuspSource.level F ζ hζ C R P H U
  have hlocal : ∀ A : KPContActualSmoothLineGluing.ChartBall F ζ hζ V R P H,
      KPCutoffSource.ChartSmoothHolomorphicOn A.ball
        (fun s => KPContActualSmoothLineGluing.coefficient F ζ hζ V R P H
          (source.descent.cutoff s).val A) Ω := by
    intro A
    have hcoef (w : KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U) :
        KPContActualAllCuspSource.chartCoefficient F ζ hζ C R P H U w A.component A.phase =
          KPContActualSmoothLineGluing.coefficient F ζ hζ V R P H w.val A := by
      unfold KPContActualAllCuspSource.chartCoefficient KPContActualSmoothLineGluing.coefficient
      have he : ((KPContSectorSmoothFramesSupport.smoothS F ζ hζ V R P H).symm w).val =
          KPContSectorLineL2Isometry.scalarRepresentative F ζ hζ V R P H w.val := by
        rw [KPContSectorLineL2Isometry.scalarRepresentative_eq_symm]
        rfl
      rw [he]
    simpa only [hcoef] using ((source.local_holomorphy A.component A.center A.chart A.phase A.ball A.contained).1)
  exact genuineCommonDisk F ζ hζ V R P H source.descent.cutoff Ω hlocal c ρ hρ hclosed

end DedekindZetaZeroFree.KPContActualCutoffPlusClearedGerm

end
