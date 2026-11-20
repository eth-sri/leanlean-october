module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripComponentMixtures

/-! # The literal nested Green and exit identities at a finite-union starting pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
  (hsub : H1.carrier ⊆ H2.carrier)
include lam Lam A hsub

/-- Both actual union measure identities hold on every certified nested component. -/
theorem nested_union_component_identity (i : Fin H1.count) (j : Fin H2.count)
    (hij : (H1.component i).carrier ⊆ (H2.component j).carrier) (sMinus T : ℝ)
    (e : StripPole (H1.component i) (T : WithTop ℝ)) (he : sMinus < e.1.time) :
    let ep := componentPoleInclusion H1 i T e
    let eb := finiteUnionNestedPoleInclusion H1 H2 hsub T ep
    let τ := finiteUnionPointRestartPoles A H1 H2 sMinus T ep
    finiteUnionGreen A H2 T eb =
      finiteUnionGreen A H1 T ep +
        τ.bind (finiteUnionGreen A H2 T) ∧
    finiteUnionExit A H2 T eb =
      (finiteUnionExit A H1 T ep).restrict
        (finiteUnionExitSet H2 sMinus T) + τ.bind (finiteUnionExit A H2 T) := by
  dsimp only
  let e2 := nestedPoleInclusion (H1.component i) (H2.component j) hij T e
  have hp := finiteUnionNestedPoleInclusion_component H1 H2 hsub i j hij T e
  have hGb := (congrArg (finiteUnionGreen A H2 T) hp).trans
    (finiteUnionGreen_component A H2 j T e2)
  have hOb := (congrArg (finiteUnionExit A H2 T) hp).trans
    (finiteUnionExit_component A H2 j T e2)
  have hGs := finiteUnionGreen_component A H1 i T e
  have hOs := finiteUnionExit_component A H1 i T e
  have hGτ := nested_restart_bind_component A H1 H2 i j hij sMinus T e he
    (finiteUnionGreen A H2 T)
    (finiteUnionGreen_measurable A H2 T)
    (stripGreen A (H2.component j) T)
    (fun ep => finiteUnionGreen_component A H2 j T ep)
  have hOτ := nested_restart_bind_component A H1 H2 i j hij sMinus T e he
    (finiteUnionExit A H2 T)
    (finiteUnionExit_measurable A H2 T)
    (stripExit A (H2.component j) T)
    (fun ep => finiteUnionExit_component A H2 j T ep)
  have houter := (congrArg (fun μ : Measure Point =>
    μ.restrict (finiteUnionExitSet H2 sMinus T)) hOs).trans
      (nested_component_outer_restriction A H1 H2 i j hij sMinus T e he)
  constructor
  · exact hGb.trans ((nestedIntervalGreen_identity A
      (H1.component i) (H2.component j) hij sMinus T e he).trans
        (congrArg₂ (· + ·) hGs.symm hGτ.symm))
  · exact hOb.trans ((nestedIntervalExit_identity A
      (H1.component i) (H2.component j) hij sMinus T e he).trans
        (congrArg₂ (· + ·) houter.symm hOτ.symm))

/-- The literal nested identities hold for every physical pole of a finite interval union. -/
theorem strip_nested_union_point (sMinus T : ℝ)
    (e : FiniteUnionPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time) :
    finiteUnionGreen A H2 T
      (finiteUnionNestedPoleInclusion H1 H2 hsub T e) =
      finiteUnionGreen A H1 T e +
        (finiteUnionPointRestartPoles A H1 H2 sMinus T e).bind
          (finiteUnionGreen A H2 T) ∧
    finiteUnionExit A H2 T
      (finiteUnionNestedPoleInclusion H1 H2 hsub T e) =
      (finiteUnionExit A H1 T e).restrict (finiteUnionExitSet H2 sMinus T) +
        (finiteUnionPointRestartPoles A H1 H2 sMinus T e).bind
          (finiteUnionExit A H2 T) := by
  let i := finiteUnionPoleIndex H1 T e
  let ep := finiteUnionComponentPole H1 T e
  obtain ⟨j, hij⟩ := H1.component_contained H2 hsub i
  have hh := nested_union_component_identity A H1 H2 hsub i j hij
    sMinus T ep he
  have heq : componentPoleInclusion H1 i T ep = e := by apply Subtype.ext; rfl
  dsimp only at hh
  rw [heq] at hh
  exact hh

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
