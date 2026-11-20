module

public import RequestProject.OrderNerveSmallSingularApproximationAll

@[expose] public section

noncomputable section

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Carried homotopy data, with the identity on boundaries needed for extension. -/
structure OrderSmallHomotopyStage (P : Type) [PartialOrder P] (n : ℕ) where
  map : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ]
    Chain (orderNerveRealization P) _
  carrier : ∀ σ : OrderSmallSimplex P n,
    map (orderSmallSingle σ 1) ∈ orderSingularCarrierChains σ.val _
  on_boundary : ∀ c : smallChains (orderNerveRealizationOpenStar P) _,
    boundary n (map (smallBoundary (orderNerveRealizationOpenStar P) n c)) =
      boundary n c.val - orderSmallSingularApproximation P n
        (smallBoundary (orderNerveRealizationOpenStar P) n c)

def orderSmallHomotopyStageZero : OrderSmallHomotopyStage P 0 where
  map := orderSmallHomotopy0
  carrier := orderSmallHomotopy0_carrier
  on_boundary c := by
    rw [orderSmallHomotopy0_boundary, orderSmallSingularApproximation_zero]
    rfl

variable {n : ℕ} (s : OrderSmallHomotopyStage P n)

theorem orderSmallHomotopyStage_fill
    (σ : OrderSmallSimplex P _) :
    ∃ b : Chain (orderNerveRealization P) _,
      b ∈ orderSingularCarrierChains σ.val _ ∧
      boundary _ b = Finsupp.single σ.val 1 -
        orderSmallSingularApproximation P _ (orderSmallSingle σ 1) -
        s.map (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) := by
  apply orderSingularCarrierChains_cycle_bounds σ.val σ.property n
  · exact Submodule.sub_mem _
      (Submodule.sub_mem _ (orderSingularCarrierChains_single σ.val 1)
        (orderSmallSingularApproximation_carrier (n + 1) σ))
      (orderSmallBoundary_map_carrier s.map s.carrier σ)
  · rw [map_sub, map_sub, orderSmallSingularApproximation_boundary, s.on_boundary]
    exact sub_self _

def orderSmallHomotopyStageNextMap :=
  (Finsupp.linearCombination ℤ (fun σ => (orderSmallHomotopyStage_fill s σ).choose)).comp
    (orderSmallChainEquiv P _).toLinearMap

theorem orderSmallHomotopyStageNextMap_single
    (σ : OrderSmallSimplex P _) :
    orderSmallHomotopyStageNextMap s (orderSmallSingle σ 1) =
      (orderSmallHomotopyStage_fill s σ).choose := by
  have he := (orderSmallChainEquiv P _).apply_symm_apply (Finsupp.single σ 1)
  rw [orderSmallChainEquiv_symm_single] at he
  change (Finsupp.linearCombination ℤ (fun τ : OrderSmallSimplex P _ =>
    (orderSmallHomotopyStage_fill s τ).choose))
      _ = _
  simp_all

theorem orderSmallHomotopyStageNextMap_boundary
    (c : smallChains (orderNerveRealizationOpenStar P) _) :
    boundary _ (orderSmallHomotopyStageNextMap s c) =
      c.val - orderSmallSingularApproximation P _ c -
        s.map (smallBoundary (orderNerveRealizationOpenStar P) n c) := by
  have he : (boundary (n + 1)).comp (orderSmallHomotopyStageNextMap s) =
      (smallChains (orderNerveRealizationOpenStar P) _).subtype -
        orderSmallSingularApproximation P _ -
        s.map.comp (smallBoundary _ n) := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, orderSmallHomotopyStageNextMap_single]
    exact (orderSmallHomotopyStage_fill s σ).choose_spec.2
  exact DFunLike.congr_fun he c

def orderSmallHomotopyStageNext :
    OrderSmallHomotopyStage P (n + 1) where
  map := orderSmallHomotopyStageNextMap s
  carrier σ := by
    rw [orderSmallHomotopyStageNextMap_single] <;> grind
  on_boundary c := by
    rw [orderSmallHomotopyStageNextMap_boundary]
    have hd := DFunLike.congr_fun (smallBoundary_squared (orderNerveRealizationOpenStar P) n) c
    change smallBoundary _ n
      (smallBoundary _ _ c) = 0 at hd
    rw [hd, map_zero, sub_zero]
    rfl

def orderSmallHomotopyStage (P : Type) [PartialOrder P] :
    (n : ℕ) → OrderSmallHomotopyStage P n
  | 0 => orderSmallHomotopyStageZero
  | n + 1 => orderSmallHomotopyStageNext (orderSmallHomotopyStage P n)

def orderSmallHomotopy (P : Type) [PartialOrder P] (n : ℕ) :=
  (orderSmallHomotopyStage P n).map

variable (n : ℕ) (c : smallChains (orderNerveRealizationOpenStar P) (n + 1))

/-- A carried chain homotopy from the realized approximation to inclusion, in every degree. -/
theorem orderSmallHomotopy_boundary :
    boundary _ (orderSmallHomotopy P _ c) =
      c.val - orderSmallSingularApproximation P _ c -
        orderSmallHomotopy P n (smallBoundary (orderNerveRealizationOpenStar P) n c) :=
  by apply orderSmallHomotopyStageNextMap_boundary

theorem orderSmallSingularApproximation_homologous
    (hc : smallBoundary _ n c = 0) :
    ∃ b : Chain (orderNerveRealization P) _,
      boundary _ b = c.val - orderSmallSingularApproximation P _ c := by
  refine ⟨orderSmallHomotopy P _ c, ?_⟩
  rw [orderSmallHomotopy_boundary, hc, map_zero, sub_zero]

end FiniteChains.Comb
