module

public import RequestProject.OrderNerveSmallSingularApproximationAll

@[expose] public section

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Carried homotopy data, with the identity on boundaries needed for extension. -/
structure OrderSmallHomotopyStage (P : Type) [PartialOrder P] (n : ℕ) where
  map : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ]
    Chain (orderNerveRealization P) (n + 1)
  carrier : ∀ σ : OrderSmallSimplex P n,
    map (orderSmallSingle σ 1) ∈ orderSingularCarrierChains σ.val (n + 1)
  on_boundary : ∀ c : smallChains (orderNerveRealizationOpenStar P) (n + 1),
    boundary n (map (smallBoundary (orderNerveRealizationOpenStar P) n c)) =
      boundary n c.val - orderSmallSingularApproximation P n
        (smallBoundary (orderNerveRealizationOpenStar P) n c)

noncomputable def orderSmallHomotopyZeroLift :
    CarriedLift (orderSmallBasis P 0) (fun σ b => b ∈ orderSingularCarrierChains σ.val 1)
      (boundary 0) ((smallChains (orderNerveRealizationOpenStar P) 0).subtype -
        orderSmallSingularApproximation P 0) := by
  apply CarriedLift.ofExists
  intro σ
  rw [orderSmallBasis_apply, LinearMap.sub_apply]
  apply orderSingularCarrierChains_zero_bounds σ.val σ.property
  · exact Submodule.sub_mem _ (orderSingularCarrierChains_single σ.val 1)
      (orderSmallSingularApproximation_carrier 0 σ)
  · change augmentation (Finsupp.single σ.val 1 - _) = 0
    rw [orderSmallSingularApproximation_zero]
    simp only [map_sub, augmentation_single, sub_self]

noncomputable def orderSmallHomotopyStageZero : OrderSmallHomotopyStage P 0 where
  map := orderSmallHomotopyZeroLift.map
  carrier σ := by simpa only [orderSmallBasis_apply] using orderSmallHomotopyZeroLift.carried σ
  on_boundary c := orderSmallHomotopyZeroLift.boundary _

theorem orderSmallHomotopyStage_fill {n : ℕ} (s : OrderSmallHomotopyStage P n)
    (σ : OrderSmallSimplex P (n + 1)) :
    ∃ b : Chain (orderNerveRealization P) (n + 2),
      b ∈ orderSingularCarrierChains σ.val (n + 2) ∧
      boundary (n + 1) b = Finsupp.single σ.val 1 -
        orderSmallSingularApproximation P (n + 1) (orderSmallSingle σ 1) -
        s.map (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) := by
  apply orderSingularCarrierChains_cycle_bounds σ.val σ.property n
  · exact Submodule.sub_mem _
      (Submodule.sub_mem _ (orderSingularCarrierChains_single σ.val 1)
        (orderSmallSingularApproximation_carrier (n + 1) σ))
      (orderSmallBoundary_map_carrier s.map s.carrier σ)
  · rw [map_sub, map_sub, orderSmallSingularApproximation_boundary, s.on_boundary]
    exact sub_self _

noncomputable def orderSmallHomotopyStageLift {n : ℕ} (s : OrderSmallHomotopyStage P n) :
    CarriedLift (orderSmallBasis P (n + 1))
      (fun σ b => b ∈ orderSingularCarrierChains σ.val (n + 2)) (boundary (n + 1))
      ((smallChains (orderNerveRealizationOpenStar P) (n + 1)).subtype -
        orderSmallSingularApproximation P (n + 1) -
        s.map.comp (smallBoundary (orderNerveRealizationOpenStar P) n)) :=
  .ofExists fun σ => by
    simpa only [orderSmallBasis_apply, LinearMap.sub_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      using! orderSmallHomotopyStage_fill s σ

noncomputable def orderSmallHomotopyStageNext {n : ℕ} (s : OrderSmallHomotopyStage P n) :
    OrderSmallHomotopyStage P (n + 1) where
  map := (orderSmallHomotopyStageLift s).map
  carrier σ := by simpa only [orderSmallBasis_apply] using (orderSmallHomotopyStageLift s).carried σ
  on_boundary c := by
    have h := (orderSmallHomotopyStageLift s).boundary (smallBoundary (orderNerveRealizationOpenStar P) (n + 1) c)
    have hd := DFunLike.congr_fun (smallBoundary_squared (orderNerveRealizationOpenStar P) n) c
    aesop

noncomputable def orderSmallHomotopyStage (P : Type) [PartialOrder P] :
    (n : ℕ) → OrderSmallHomotopyStage P n
  | 0 => orderSmallHomotopyStageZero
  | n + 1 => orderSmallHomotopyStageNext (orderSmallHomotopyStage P n)

noncomputable def orderSmallHomotopy (P : Type) [PartialOrder P] (n : ℕ) :
    smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ]
      Chain (orderNerveRealization P) (n + 1) :=
  (orderSmallHomotopyStage P n).map

/-- A carried chain homotopy from the realized approximation to inclusion, in every degree. -/
theorem orderSmallHomotopy_boundary (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    boundary (n + 1) (orderSmallHomotopy P (n + 1) c) =
      c.val - orderSmallSingularApproximation P (n + 1) c -
        orderSmallHomotopy P n (smallBoundary (orderNerveRealizationOpenStar P) n c) :=
  (orderSmallHomotopyStageLift (orderSmallHomotopyStage P n)).boundary c

theorem orderSmallSingularApproximation_homologous (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1))
    (hc : smallBoundary (orderNerveRealizationOpenStar P) n c = 0) :
    ∃ b : Chain (orderNerveRealization P) (n + 2),
      boundary (n + 1) b = c.val - orderSmallSingularApproximation P (n + 1) c := by
  refine ⟨orderSmallHomotopy P (n + 1) c, ?_⟩
  rw [orderSmallHomotopy_boundary, hc, map_zero, sub_zero]

end FiniteChains.Comb
