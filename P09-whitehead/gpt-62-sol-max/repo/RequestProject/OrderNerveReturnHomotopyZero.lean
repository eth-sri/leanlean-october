module

public import RequestProject.OrderNerveSimplicialCarriers

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
variable {P : Type} [PartialOrder P]

structure OrderReturnHomotopyStage (P : Type) [PartialOrder P] (n : ℕ) where
  map : (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P
  carrier : ∀ s, map (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj)
  homogeneous : ∀ c, Nerve.lengthProjection (n + 2) (map c) = map c
  on_boundary : ∀ c : ComposableArrows P (n + 1) →₀ ℤ,
    Nerve.bdry (map (orderSimplicialBoundary P n c)) =
      orderNerveGradedEncode n (orderSimplicialBoundary P n c) -
        orderNerveRoundTrip P n (orderSimplicialBoundary P n c)

theorem orderNerveCarriedFill {n : ℕ} (s : ComposableArrows P n) (c : Nerve.Ch P)
    (hc : c ∈ Nerve.IncOn (Set.range s.obj)) (hlen : Nerve.lengthProjection (n + 1) c = c)
    (hz : Nerve.bdry c = 0) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (Set.range s.obj) ∧
      Nerve.lengthProjection (n + 2) b = b ∧ Nerve.bdry b = c := by
  obtain ⟨b, hb, he⟩ := orderNerveSimplexCarrier_acyclic s c hc hz
  refine ⟨Nerve.lengthProjection (n + 2) b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he, hlen]

theorem orderReturnHomotopyZero_fill (s : ComposableArrows P 0) :
    ∃ b : Nerve.Ch P, b ∈ Nerve.IncOn (Set.range s.obj) ∧
      Nerve.lengthProjection 2 b = b ∧ Nerve.bdry b =
        orderNerveGradedEncode 0 (Finsupp.single s 1) - orderNerveRoundTrip P 0 (Finsupp.single s 1) := by
  apply orderNerveCarriedFill s
  · exact AddSubgroup.sub_mem _ (orderNerveGradedEncode_single_supported 0 s)
      (orderNerveRoundTrip_supported 0 s)
  · rw [map_sub, orderNerveGradedEncode_length]
    congr 1
    exact orderSingularToNerve_length 0 _
  · rw [map_sub, orderNerveRoundTrip_zero_boundary, sub_self]

noncomputable def orderReturnHomotopyZeroLift :
    CarriedLift (Finsupp.basisSingleOne : Module.Basis (ComposableArrows P 0) ℤ _)
      (fun s b => b ∈ Nerve.IncOn (Set.range s.obj) ∧ Nerve.lengthProjection 2 b = b)
      Nerve.bdry.toIntLinearMap (orderNerveGradedEncode 0 - orderNerveRoundTrip P 0) :=
  .ofExists fun s => by
    simpa only [Finsupp.coe_basisSingleOne, LinearMap.sub_apply, AddMonoidHom.coe_toIntLinearMap, and_assoc]
      using orderReturnHomotopyZero_fill s

noncomputable def orderReturnHomotopyStageZero : OrderReturnHomotopyStage P 0 where
  map := orderReturnHomotopyZeroLift.map
  carrier s := (orderReturnHomotopyZeroLift.carried s).1
  homogeneous := orderReturnHomotopyZeroLift.fixed (Nerve.lengthProjection 2).toIntLinearMap fun _ _ h => h.2
  on_boundary _ := orderReturnHomotopyZeroLift.boundary _

end FiniteChains.Comb
