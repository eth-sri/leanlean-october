module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripComponentMixtures

/-! # The literal nested Green and exit identities at a finite-union starting pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H1 H2 : FiniteIntervalUnion) (hsub : H1.carrier ⊆ H2.carrier) (i : Fin H1.count)
    (j : Fin H2.count) (hij : (H1.component i).carrier ⊆ (H2.component j).carrier) (sMinus T : ℝ)

include hij in
/-- Both actual union measure identities hold on every certified nested component. -/
theorem nested_union_component_identity
    (e : StripPole (H1.component i) (T : WithTop ℝ)) (he : sMinus < e.1.time) :
    let ep := componentPoleInclusion H1 i T e
    let eb := finiteUnionNestedPoleInclusion H1 H2 hsub T ep
    let τ := finiteUnionPointRestartPoles hlam hLam A H1 H2 sMinus T ep
    finiteUnionGreen hlam hLam A H2 T eb =
      finiteUnionGreen hlam hLam A H1 T ep +
        τ.bind (finiteUnionGreen hlam hLam A H2 T) ∧
    finiteUnionExit hlam hLam A H2 T eb =
      (finiteUnionExit hlam hLam A H1 T ep).restrict
        (finiteUnionExitSet H2 sMinus T) + τ.bind (finiteUnionExit hlam hLam A H2 T) := by
  dsimp only
  let e2 := nestedPoleInclusion (H1.component i) (H2.component j) hij T e
  have hp := finiteUnionNestedPoleInclusion_component H1 H2 hsub i j hij T e
  have hOs := finiteUnionExit_component hlam hLam A H1 i T e
  have hGτ := nested_restart_bind_component hlam hLam A H1 H2 i j hij sMinus T e he
    (finiteUnionGreen hlam hLam A H2 T)
    (finiteUnionGreen_measurable hlam hLam A H2 T)
    (stripGreen hlam hLam A (H2.component j) T)
    (fun ep => finiteUnionGreen_component hlam hLam A H2 j T ep)
  have hOτ := nested_restart_bind_component hlam hLam A H1 H2 i j hij sMinus T e he
    (finiteUnionExit hlam hLam A H2 T)
    (finiteUnionExit_measurable hlam hLam A H2 T)
    (stripExit hlam hLam A (H2.component j) T)
    (fun ep => finiteUnionExit_component hlam hLam A H2 j T ep)
  constructor
  · exact ((congrArg (finiteUnionGreen hlam hLam A H2 T) hp).trans (finiteUnionGreen_component hlam hLam A H2 j T e2)).trans ((nestedIntervalGreen_identity hlam hLam A
      (H1.component i) (H2.component j) hij sMinus T e he).trans
        (congrArg₂ (· + ·) (finiteUnionGreen_component hlam hLam A H1 i T e).symm hGτ.symm))
  · exact ((congrArg (finiteUnionExit hlam hLam A H2 T) hp).trans (finiteUnionExit_component hlam hLam A H2 j T e2)).trans ((nestedIntervalExit_identity hlam hLam A
      (H1.component i) (H2.component j) hij sMinus T e he).trans
        (congrArg₂ (· + ·) ((congrArg (fun μ : Measure Point => μ.restrict (finiteUnionExitSet H2 sMinus T)) hOs).trans (nested_component_outer_restriction hlam hLam A H1 H2 i j hij sMinus T e he)).symm hOτ.symm))

/-- The literal nested identities hold for every physical pole of a finite interval union. -/
theorem strip_nested_union_point
    (e : FiniteUnionPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time) :
    finiteUnionGreen hlam hLam A H2 T
      (finiteUnionNestedPoleInclusion H1 H2 hsub T e) =
      finiteUnionGreen hlam hLam A H1 T e +
        (finiteUnionPointRestartPoles hlam hLam A H1 H2 sMinus T e).bind
          (finiteUnionGreen hlam hLam A H2 T) ∧
    finiteUnionExit hlam hLam A H2 T
      (finiteUnionNestedPoleInclusion H1 H2 hsub T e) =
      (finiteUnionExit hlam hLam A H1 T e).restrict (finiteUnionExitSet H2 sMinus T) +
        (finiteUnionPointRestartPoles hlam hLam A H1 H2 sMinus T e).bind
          (finiteUnionExit hlam hLam A H2 T) := by
  let i := finiteUnionPoleIndex H1 T e
  let ep := finiteUnionComponentPole H1 T e
  obtain ⟨j, hij⟩ := H1.component_contained H2 hsub i
  have hh := nested_union_component_identity hlam hLam A H1 H2 hsub i j hij
    sMinus T ep he
  have heq : componentPoleInclusion H1 i T ep = e := by rfl
  dsimp only at hh
  exact hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
