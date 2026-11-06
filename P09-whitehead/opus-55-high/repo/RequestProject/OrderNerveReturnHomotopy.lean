import RequestProject.OrderNerveReturnHomotopyZero
import RequestProject.Tac
noncomputable section


set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open CategoryTheory
variable {P : Type} [PartialOrder P]

theorem orderReturnHomotopyNext_fill (H : OrderReturnHomotopyStage P n)
    s :
    ∃ b, b ∈ Nerve.IncOn (Set.range s.obj) ∧
      Nerve.lengthProjection (n + 3) b = b ∧ Nerve.bdry b =
        orderNerveGradedEncode (n + 1) (Finsupp.single s 1) -
          orderNerveRoundTrip P (n + 1) (Finsupp.single s 1) -
            H.map (orderSimplicialBoundary P n (Finsupp.single s 1)) := by
  apply orderNerveCarriedFill s
  · exact AddSubgroup.sub_mem _
      (AddSubgroup.sub_mem _ (orderNerveGradedEncode_single_supported _ s)
        (orderNerveRoundTrip_supported _ s))
      (orderSimplicialBoundary_map_carrier H.map H.carrier s)
  · rwd [map_sub, map_sub, orderNerveGradedEncode_length, H.homogeneous]
    congr 2
    exact orderSingularToNerve_length _ _
  · rwd [map_sub, map_sub, ← orderNerveGradedEncode_boundary,
      orderNerveRoundTrip_boundary, H.on_boundary, sub_self]

def orderReturnHomotopyNextMap (H : OrderReturnHomotopyStage P n) :
    (ComposableArrows P (n + 1) →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun s => (orderReturnHomotopyNext_fill H s).choose)

theorem orderReturnHomotopyNextMap_single H
    (s : ComposableArrows P (n + 1)) :
    orderReturnHomotopyNextMap H (Finsupp.single s 1) = (orderReturnHomotopyNext_fill H s).choose := by
  simp [orderReturnHomotopyNextMap, Finsupp.linearCombination_single, one_smul]

theorem orderReturnHomotopyNextMap_identity H
    c :
    Nerve.bdry (orderReturnHomotopyNextMap H c) =
      orderNerveGradedEncode (n + 1) c - orderNerveRoundTrip P (n + 1) c -
        H.map (orderSimplicialBoundary P n c) := by
  let D : (ComposableArrows P (n + 1) →₀ ℤ) →ₗ[ℤ] (ComposableArrows P n →₀ ℤ) :=
    orderSimplicialBoundary P n
  have he : Nerve.bdry.toIntLinearMap.comp (orderReturnHomotopyNextMap H) =
      orderNerveGradedEncode _ - orderNerveRoundTrip P _ -
        H.map.comp D := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply]
    rwd [orderReturnHomotopyNextMap_single]
    exact (orderReturnHomotopyNext_fill H s).choose_spec.2.2
  exact DFunLike.congr_fun he c

def orderReturnHomotopyStageNext (H : OrderReturnHomotopyStage P n) :
    OrderReturnHomotopyStage P (n + 1) where
  map := orderReturnHomotopyNextMap H
  carrier s := by
    grind [orderReturnHomotopyNextMap_single]
  homogeneous c := by
    have he : (Nerve.lengthProjection (n + 3)).toIntLinearMap.comp (orderReturnHomotopyNextMap H) =
        orderReturnHomotopyNextMap H := by
      apply Finsupp.lhom_ext'
      intro s
      apply LinearMap.ext_ring
      change Nerve.lengthProjection (n + 3) (orderReturnHomotopyNextMap H (Finsupp.single s 1)) = _
      rwd [orderReturnHomotopyNextMap_single]
      grind
    exact DFunLike.congr_fun he c
  on_boundary c := by
    simp [orderReturnHomotopyNextMap_identity, orderSimplicialBoundary_squared, map_zero, sub_zero]

def orderReturnHomotopyStage P [PartialOrder P] :
    (n : ℕ) → OrderReturnHomotopyStage P n
  | 0 => orderReturnHomotopyStageZero
  | n + 1 => orderReturnHomotopyStageNext (orderReturnHomotopyStage P n)

def orderReturnHomotopy (P : Type) [PartialOrder P] n :=
  (orderReturnHomotopyStage P n).map

/-- Going through actual singular chains and returning to the nerve is
chain homotopic to the original simplicial chain map. -/
theorem orderReturnHomotopy_identity n c :
    Nerve.bdry (orderReturnHomotopy P (n + 1) c) =
      orderNerveGradedEncode (n + 1) c - orderNerveRoundTrip P (n + 1) c -
        orderReturnHomotopy P n (orderSimplicialBoundary P n c) :=
  orderReturnHomotopyNextMap_identity _ c

theorem orderReturnHomotopy_mem_inc n c :
    orderReturnHomotopy P n c ∈ Nerve.Inc P :=
  orderSimplicialMap_mem_inc _ (orderReturnHomotopyStage P n).carrier c
