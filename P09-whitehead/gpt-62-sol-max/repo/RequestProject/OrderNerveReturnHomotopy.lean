module

public import RequestProject.OrderNerveReturnHomotopyZero

@[expose] public section


namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
variable {P : Type} [PartialOrder P]

theorem orderReturnHomotopyNext_fill {n : ℕ} (H : OrderReturnHomotopyStage P n)
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
    exact orderSingularToNerve_length (n + 1) _
  · erw [map_sub, map_sub, ← orderNerveGradedEncode_boundary,
      orderNerveRoundTrip_boundary, H.on_boundary, sub_self]

noncomputable def orderReturnHomotopyLift {n : ℕ} (H : OrderReturnHomotopyStage P n) :
    CarriedLift (Finsupp.basisSingleOne : Module.Basis (ComposableArrows P (n + 1)) ℤ _)
      (fun s b => b ∈ Nerve.IncOn (Set.range s.obj) ∧ Nerve.lengthProjection (n + 3) b = b)
      Nerve.bdry.toIntLinearMap (orderNerveGradedEncode (n + 1) - orderNerveRoundTrip P (n + 1) -
        H.map.comp (orderSimplicialBoundary P n)) :=
  .ofExists fun s => by
    simpa only [Finsupp.coe_basisSingleOne, LinearMap.sub_apply, LinearMap.comp_apply,
      AddMonoidHom.coe_toIntLinearMap, and_assoc] using orderReturnHomotopyNext_fill H s

noncomputable def orderReturnHomotopyStageNext {n : ℕ} (H : OrderReturnHomotopyStage P n) :
    OrderReturnHomotopyStage P (n + 1) where
  map := (orderReturnHomotopyLift H).map
  carrier s := ((orderReturnHomotopyLift H).carried s).1
  homogeneous := (orderReturnHomotopyLift H).fixed (Nerve.lengthProjection (n + 3)).toIntLinearMap fun _ _ h => h.2
  on_boundary c := by
    have h := (orderReturnHomotopyLift H).boundary (orderSimplicialBoundary P (n + 1) c)
    simp_all [LinearMap.sub_apply, orderSimplicialBoundary_squared]

noncomputable def orderReturnHomotopyStage (P : Type) [PartialOrder P] :
    (n : ℕ) → OrderReturnHomotopyStage P n
  | 0 => orderReturnHomotopyStageZero
  | n + 1 => orderReturnHomotopyStageNext (orderReturnHomotopyStage P n)

noncomputable def orderReturnHomotopy (P : Type) [PartialOrder P] (n : ℕ) :
    (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  (orderReturnHomotopyStage P n).map

/-- Going through actual singular chains and returning to the nerve is
chain homotopic to the original simplicial chain map. -/
theorem orderReturnHomotopy_identity (n : ℕ) (c : ComposableArrows P (n + 1) →₀ ℤ) :
    Nerve.bdry (orderReturnHomotopy P (n + 1) c) =
      orderNerveGradedEncode (n + 1) c - orderNerveRoundTrip P (n + 1) c -
        orderReturnHomotopy P n (orderSimplicialBoundary P n c) :=
  (orderReturnHomotopyLift (orderReturnHomotopyStage P n)).boundary c

theorem orderReturnHomotopy_mem_inc (n : ℕ) (c : ComposableArrows P n →₀ ℤ) :
    orderReturnHomotopy P n c ∈ Nerve.Inc P :=
  orderSimplicialMap_mem_inc _ (orderReturnHomotopyStage P n).carrier c

end FiniteChains.Comb
