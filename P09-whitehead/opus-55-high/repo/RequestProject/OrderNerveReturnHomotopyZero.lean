import RequestProject.OrderNerveSimplicialCarriers
noncomputable section


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

theorem orderNerveCarriedFill (s : ComposableArrows P n) c
    (hc : c ∈ Nerve.IncOn (Set.range s.obj)) (hlen : Nerve.lengthProjection (n + 1) c = c)
    (hz : Nerve.bdry c = 0) :
    ∃ b, b ∈ Nerve.IncOn (Set.range s.obj) ∧
      Nerve.lengthProjection (n + 2) b = b ∧ Nerve.bdry b = c := by
  obtain ⟨b, hb, he⟩ := orderNerveSimplexCarrier_acyclic s c hc hz
  refine ⟨Nerve.lengthProjection (n + 2) b, Nerve.lengthProjection_mem_incOn _ hb,
    Nerve.lengthProjection_idempotent _ _, ?_⟩
  rw [← Nerve.lengthProjection_bdry, he, hlen]

theorem orderReturnHomotopyZero_fill s :
    ∃ b, b ∈ Nerve.IncOn (Set.range s.obj) ∧
      Nerve.lengthProjection 2 b = b ∧ Nerve.bdry b =
        orderNerveGradedEncode 0 (Finsupp.single s 1) - orderNerveRoundTrip P 0 (Finsupp.single s 1) := by
  apply orderNerveCarriedFill s
  · exact AddSubgroup.sub_mem _ (orderNerveGradedEncode_single_supported 0 s)
      (orderNerveRoundTrip_supported 0 s)
  · rw [map_sub, orderNerveGradedEncode_length]
    congr 1
    exact orderSingularToNerve_length 0 _
  · rw [map_sub, orderNerveRoundTrip_zero_boundary, sub_self]

def orderReturnHomotopyZero : (ComposableArrows P 0 →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  Finsupp.linearCombination ℤ (fun s => (orderReturnHomotopyZero_fill s).choose)

theorem orderReturnHomotopyZero_single (s : ComposableArrows P 0) :
    orderReturnHomotopyZero (Finsupp.single s 1) = (orderReturnHomotopyZero_fill s).choose := by
  rw [orderReturnHomotopyZero, Finsupp.linearCombination_single, one_smul]

theorem orderReturnHomotopyZero_identity c :
    Nerve.bdry (orderReturnHomotopyZero c) = orderNerveGradedEncode 0 c - orderNerveRoundTrip P 0 c := by
  have he : Nerve.bdry.toIntLinearMap.comp orderReturnHomotopyZero =
      orderNerveGradedEncode 0 - orderNerveRoundTrip P 0 := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simp [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sub_apply]
    grind [orderReturnHomotopyZero_single]
  exact DFunLike.congr_fun he c

def orderReturnHomotopyStageZero : OrderReturnHomotopyStage P 0 where
  map := orderReturnHomotopyZero
  carrier s := by
    rw [orderReturnHomotopyZero_single]
    grind
  homogeneous c := by
    have he : (Nerve.lengthProjection 2).toIntLinearMap.comp orderReturnHomotopyZero =
        (orderReturnHomotopyZero : (ComposableArrows P 0 →₀ ℤ) →ₗ[ℤ] Nerve.Ch P) := by
      apply Finsupp.lhom_ext'
      intro s
      apply LinearMap.ext_ring
      simp [LinearMap.comp_apply, Finsupp.lsingle_apply]
      grind [orderReturnHomotopyZero_single]
    exact DFunLike.congr_fun he c
  on_boundary c := orderReturnHomotopyZero_identity _
