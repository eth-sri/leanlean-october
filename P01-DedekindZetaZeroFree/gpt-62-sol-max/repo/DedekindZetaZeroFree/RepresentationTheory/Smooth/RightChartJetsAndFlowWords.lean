module

public import DedekindZetaZeroFree.Adeles.Archimedean.RightFlowCharts
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.UpperAndLowerBigCellTransitions

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ContDiff Matrix Matrix.Norms.Operator

namespace DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets

export KPGlobalResidualConstruction.RightFlowChart (word word_add word_smul theta theta_zero
  theta_smooth theta_chart rightWord_hasDerivAt_of_chart_smooth rightWord_level
  rightWord_continuous_of_chart_smooth)

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem scalar_smooth_native_right_chart
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (v : KPGlobalTorusFunctionData.BorelFunctions F ζ hζ Q)
    (hv : v ∈ KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ Q) :
    ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => v.val (g * KPGlobalResidualConstruction.archChart F ζ hζ x))
      (KPGlobalResidualConstruction.archDomain F) := by
  obtain ⟨b, rfl⟩ := LinearMap.mem_range.mp hv
  have hb : ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (b.val.val
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)).val.val 1)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
    apply Submodule.iSup_induction _ (motive := fun b => ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (b.val
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)).val.val 1)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) b.property
    · intro J b hb
      exact hb.1
    · intro g
      exact contDiffOn_const
    · intro b c hb hc g
      exact (hb g).add (hc g)
  intro g
  apply contDiffOn_of_locally_contDiffOn
  intro x₀ hx₀
  obtain ⟨O, q, hO, hxO, hq, hqO, heq⟩ :=
    KPLiteralChamber.literal_right_to_left_chart_local_transition F ζ hζ g x₀ hx₀
  refine ⟨O, hO, hxO, ?_⟩
  have hc := (hb (g * KPGlobalResidualConstruction.archChart F ζ hζ x₀)).comp hq hqO
  apply (hc.congr (fun x hx => ?_)).mono Set.inter_subset_right
  rw [KPGlobalTorusBorelTwistCompatibility.scalarSection_formula, heq x hx]
  rfl

open Filter KPGlobalResidualConstruction
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

variable (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
  (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
  (T : KPGlobalEisensteinData.CompactTypeStage
    ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).comp D.K.subtype))

 theorem stage_chart_smooth (v : KPMsRationalCompactCrossPairing.sourceStage F ζ hζ D U T) :
    ∀ g, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => v.val.val (g * archChart F ζ hζ x)) (archDomain F) :=
  scalar_smooth_native_right_chart _ v.val v.property.1.1

 theorem stage_level (v : KPMsRationalCompactCrossPairing.sourceStage F ζ hζ D U T) :
    ∀ g, ∀ u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      v.val.val (g * u.val) = v.val.val g := by
  intro g u
  obtain ⟨j, hj, heq⟩ := u.property
  have hh := v.property.1.2 ⟨j, hj⟩
  have h := congrArg (fun f => f.val g) hh
  change v.val.val (g * j.val) = v.val.val g at h
  change j.val = u.val at heq
  rwa [heq] at h

def stageWords : List (KPSmoothActualFlowData.B F) →
    KPMsRationalCompactCrossPairing.sourceStage F ζ hζ D U T →ₗ[ℂ]
      C(KPGlobalTorusFunctionData.G F ζ hζ, ℂ) := fun w =>
  { toFun := fun v => ⟨word F ζ hζ w v.val.val,
      rightWord_continuous_of_chart_smooth F ζ hζ U v.val.val
        (stage_chart_smooth F ζ hζ D U T v) (stage_level F ζ hζ D U T v) w⟩
    map_add' := fun v u => ContinuousMap.ext fun g => congrFun
      (word_add F ζ hζ v.val.val u.val.val
        (stage_chart_smooth F ζ hζ D U T v) (stage_chart_smooth F ζ hζ D U T u) w) g
    map_smul' := fun c v => ContinuousMap.ext fun g => congrFun
      (word_smul F ζ hζ c v.val.val (stage_chart_smooth F ζ hζ D U T v) w) g }

end DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets

end
end
