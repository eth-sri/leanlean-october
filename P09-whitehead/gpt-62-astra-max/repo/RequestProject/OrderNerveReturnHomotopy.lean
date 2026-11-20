module

public import RequestProject.OrderNerveReturnHomotopyZero

@[expose] public section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
variable {P : Type} [PartialOrder P]

variable {n : ℕ} (H : OrderReturnHomotopyStage P n)

theorem orderReturnHomotopyNext_fill
    (s : ComposableArrows P (n + 1)) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (Set.range s.obj) ∧
      Nerve.lengthProjection (n + 3) b = b ∧ Nerve.bdry b =
        orderNerveGradedEncode (n + 1) (Finsupp.single s 1) -
          orderNerveRoundTrip P (n + 1) (Finsupp.single s 1) -
            H.map (orderSimplicialBoundary P n (Finsupp.single s 1)) := by
  apply orderNerveCarriedFill s
  · exact AddSubgroup.sub_mem _
      (AddSubgroup.sub_mem _ (orderNerveGradedEncode_single_supported (n + 1) s)
        (orderNerveRoundTrip_supported (n + 1) s))
      (orderSimplicialBoundary_map_carrier H.map H.carrier s)
  · erw [map_sub, map_sub, orderNerveGradedEncode_length, H.homogeneous]
    congr 2
    apply orderSingularToNerve_length
  · erw [map_sub, map_sub, ← orderNerveGradedEncode_boundary,
      orderNerveRoundTrip_boundary, H.on_boundary, sub_self]

def orderReturnHomotopyNextMap :=
  Finsupp.linearCombination ℤ (fun s => (orderReturnHomotopyNext_fill H s).choose)

theorem orderReturnHomotopyNextMap_single
    (s : ComposableArrows P (n + 1)) :
    orderReturnHomotopyNextMap H (Finsupp.single s 1) = (orderReturnHomotopyNext_fill H s).choose := by
  simp_all [orderReturnHomotopyNextMap]

theorem orderReturnHomotopyNextMap_identity
    (c : ComposableArrows P (n + 1) →₀ ℤ) :
    Nerve.bdry (orderReturnHomotopyNextMap H c) =
      orderNerveGradedEncode (n + 1) c - orderNerveRoundTrip P (n + 1) c -
        H.map (orderSimplicialBoundary P n c) := by
  let D : (ComposableArrows P (n + 1) →₀ ℤ) →ₗ[ℤ] (ComposableArrows P n →₀ ℤ) :=
    orderSimplicialBoundary P n
  have he : Nerve.bdry.toIntLinearMap.comp (orderReturnHomotopyNextMap H) =
      orderNerveGradedEncode (n + 1) - orderNerveRoundTrip P (n + 1) -
        H.map.comp D := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    change Nerve.bdry (orderReturnHomotopyNextMap H (Finsupp.single s 1)) = _; erw [orderReturnHomotopyNextMap_single]; exact (orderReturnHomotopyNext_fill H s).choose_spec.2.2
  exact DFunLike.congr_fun he c

def orderReturnHomotopyStageNext :
    OrderReturnHomotopyStage P (n + 1) where
  map := orderReturnHomotopyNextMap H
  carrier s := by
    erw [orderReturnHomotopyNextMap_single] <;> grind
  homogeneous c := by
    have he : (Nerve.lengthProjection (n + 3)).toIntLinearMap.comp (orderReturnHomotopyNextMap H) =
        orderReturnHomotopyNextMap H := by
      apply Finsupp.lhom_ext'
      intro s
      apply LinearMap.ext_ring
      change Nerve.lengthProjection (n + 3) (orderReturnHomotopyNextMap H (Finsupp.single s 1)) = _; erw [orderReturnHomotopyNextMap_single]; exact (orderReturnHomotopyNext_fill H s).choose_spec.2.1
    exact DFunLike.congr_fun he c
  on_boundary c := by
    simp_all [orderReturnHomotopyNextMap_identity, orderSimplicialBoundary_squared]

def orderReturnHomotopyStage (P : Type) [PartialOrder P] :
    (n : ℕ) → OrderReturnHomotopyStage P n
  | 0 => orderReturnHomotopyStageZero
  | n + 1 => orderReturnHomotopyStageNext (orderReturnHomotopyStage P n)

def orderReturnHomotopy (P : Type) [PartialOrder P] (n : ℕ) :=
  (orderReturnHomotopyStage P n).map

variable (n : ℕ)

/-- Going through actual singular chains and returning to the nerve is
chain homotopic to the original simplicial chain map. -/
theorem orderReturnHomotopy_identity (c : ComposableArrows P (n + 1) →₀ ℤ) :
    Nerve.bdry (orderReturnHomotopy P (n + 1) c) =
      orderNerveGradedEncode (n + 1) c - orderNerveRoundTrip P (n + 1) c -
        orderReturnHomotopy P n (orderSimplicialBoundary P n c) :=
  orderReturnHomotopyNextMap_identity (orderReturnHomotopyStage P n) c

theorem orderReturnHomotopy_mem_inc (c : ComposableArrows P n →₀ ℤ) :
    orderReturnHomotopy P n c ∈ Nerve.Inc P :=
  orderSimplicialMap_mem_inc _ (orderReturnHomotopyStage P n).carrier c

end FiniteChains.Comb
