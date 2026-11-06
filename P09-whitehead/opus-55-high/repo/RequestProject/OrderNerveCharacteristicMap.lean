import RequestProject.OrderNerveClosedBallChart
import Mathlib.Logic.Equiv.PartialEquiv
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

/-- Extend the genuine closed-ball chart to an ambient function, using its centre
value outside the closed ball. Only its closed-ball restriction is characteristic data. -/
def orderNerveCharacteristicFunction {P} [PartialOrder P]
    {n} (s : (nerve P).nonDegenerate n) (x : Fin n → ℝ) :=
  if hx : x ∈ Metric.closedBall 0 1 then orderNerveClosedBallChart s ⟨x, hx⟩
  else orderNerveClosedBallChart s ⟨0, Metric.mem_closedBall_self (by norm_num)⟩

 theorem orderNerveCharacteristicFunction_closedBall {P} [PartialOrder P]
    {n} (s : (nerve P).nonDegenerate n) x :
    orderNerveCharacteristicFunction s x.val = orderNerveClosedBallChart s x := by
  simp [orderNerveCharacteristicFunction, x.property]

 theorem orderNerveCharacteristicFunction_continuousOn {P} [PartialOrder P]
    {n} (s : (nerve P).nonDegenerate n) :
    ContinuousOn (orderNerveCharacteristicFunction s) (Metric.closedBall 0 1) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have h : (Metric.closedBall 0 1).domRestrict
      (orderNerveCharacteristicFunction s) = orderNerveClosedBallChart s := by
    funext x
    exact orderNerveCharacteristicFunction_closedBall s x
  rwd [h]
  fun_prop

 theorem orderNerveCharacteristicFunction_injOn {P} [PartialOrder P]
    {n} (s : (nerve P).nonDegenerate n) :
    Set.InjOn (orderNerveCharacteristicFunction s) (Metric.ball 0 1) := by
  intro x hx y hy h
  have hx' := Metric.ball_subset_closedBall hx
  have hy' := Metric.ball_subset_closedBall hy
  have hc : orderNerveClosedBallChart s ⟨x, hx'⟩ = orderNerveClosedBallChart s ⟨y, hy'⟩ := by
    simp_all [orderNerveCharacteristicFunction_closedBall s ⟨x, hx'⟩, orderNerveCharacteristicFunction_closedBall s ⟨y, hy'⟩]
  exact congrArg Subtype.val (orderNerveClosedBallChart_injective s hc)

/-- The genuine realization characteristic map as a PartialEquiv with open-ball source. -/
def orderNerveCharacteristicMap {P} [PartialOrder P]
    {n} (s : (nerve P).nonDegenerate n) :=
  (orderNerveCharacteristicFunction_injOn s).toPartialEquiv
    _ _

 theorem orderNerveCharacteristicMap_source {P} [PartialOrder P]
    {n} (s : (nerve P).nonDegenerate n) :
    (orderNerveCharacteristicMap s).source = Metric.ball 0 1 := rfl

 theorem orderNerveCharacteristicMap_continuousOn {P} [PartialOrder P]
    {n} (s : (nerve P).nonDegenerate n) :
    ContinuousOn (orderNerveCharacteristicMap s) (Metric.closedBall 0 1) :=
  orderNerveCharacteristicFunction_continuousOn s

/-- The inverse characteristic map is continuous on its actual open-cell target. -/
theorem orderNerveCharacteristicMap_continuousOn_symm {P} [PartialOrder P]
    {n} (s : (nerve P).nonDegenerate n) :
    ContinuousOn (orderNerveCharacteristicMap s).symm (orderNerveCharacteristicMap s).target := by
  let e := orderNerveCharacteristicMap s
  let g : e.target → (Metric.closedBall 0 1 : Set (Fin n → ℝ)) := fun x =>
    ⟨e.symm x.val, Metric.ball_subset_closedBall (by
      have h := e.map_target x.property
      tauto)⟩
  have hc :=
    ((orderNerveClosedBallChart s).continuous.isClosedEmbedding
      (orderNerveClosedBallChart_injective s)).isEmbedding
  have hg : Continuous g := by
    apply hc.isInducing.continuous_iff.mpr
    have he : orderNerveClosedBallChart s ∘ g = Subtype.val := by
      funext x
      have h := orderNerveCharacteristicFunction_closedBall s (g x)
      change e (e.symm x.val) = orderNerveClosedBallChart s (g x) at h
      simp_all
    rwd [he]
    exact continuous_subtype_val
  apply continuousOn_iff_continuous_restrict.mpr
  exact continuous_subtype_val.comp hg
