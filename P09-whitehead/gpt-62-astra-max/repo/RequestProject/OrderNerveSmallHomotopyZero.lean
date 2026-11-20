module

public import RequestProject.OrderNerveSmallChainMapLow
public import RequestProject.OrderNerveExplicitSingularMap
public import RequestProject.OrderNerveSingularCarrierExactness

@[expose] public section

noncomputable section

namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision

variable {P : Type} [PartialOrder P]

variable (σ : OrderSmallSimplex P 0)

def orderSmallVertexSimplex :=
  orderNerveSingularSimplex (ComposableArrows.mk₀ (orderSmallChosenVertex σ))

theorem orderSmallVertexSimplex_carrier (r : ℤ) :
    Finsupp.single (orderSmallVertexSimplex σ) r ∈ orderSingularCarrierChains σ.val 0 := by
  solve_by_elim [single_mem_subChains, orderNerveSingularSimplex_supported, orderSmallChosenVertex_mem]

def orderSmallSingularApproximation0 :
    smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] Chain (orderNerveRealization P) 0 :=
  (Finsupp.linearCombination ℤ (fun σ => Finsupp.single (orderSmallVertexSimplex σ) 1)).comp
    (orderSmallChainEquiv P 0).toLinearMap

variable (σ : OrderSmallSimplex P 0)

theorem orderSmallSingularApproximation0_single :
    orderSmallSingularApproximation0 (orderSmallSingle σ 1) =
      Finsupp.single (orderSmallVertexSimplex σ) 1 := by
  rw [← orderSmallChainEquiv_symm_single]
  simp [orderSmallSingularApproximation0, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single, one_smul]

/-- The first comparison homotopy stays inside the simplex's actual CW carrier. -/
theorem orderSmallHomotopyZeroFill_exists :
    ∃ b : Chain (orderNerveRealization P) 1, b ∈ orderSingularCarrierChains σ.val 1 ∧
      boundary 0 b = Finsupp.single σ.val 1 - Finsupp.single (orderSmallVertexSimplex σ) 1 := by
  apply orderSingularCarrierChains_zero_bounds σ.val σ.property
  · exact Submodule.sub_mem _ (orderSingularCarrierChains_single σ.val 1)
      (orderSmallVertexSimplex_carrier σ 1)
  · simp

def orderSmallHomotopy0 :=
  (Finsupp.linearCombination ℤ (fun σ => (orderSmallHomotopyZeroFill_exists σ).choose)).comp
    (orderSmallChainEquiv P 0).toLinearMap

variable (σ : OrderSmallSimplex P 0)

theorem orderSmallHomotopy0_single :
    orderSmallHomotopy0 (orderSmallSingle σ 1) = (orderSmallHomotopyZeroFill_exists σ).choose := by
  rw [← orderSmallChainEquiv_symm_single]
  simp [orderSmallHomotopy0, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single, one_smul]

theorem orderSmallHomotopy0_carrier :
    orderSmallHomotopy0 (orderSmallSingle σ 1) ∈ orderSingularCarrierChains σ.val 1 := by
  rw [orderSmallHomotopy0_single] <;> grind

theorem orderSmallHomotopy0_boundary
    (c : smallChains (orderNerveRealizationOpenStar P) 0) :
    boundary 0 (orderSmallHomotopy0 c) = c.val - orderSmallSingularApproximation0 c := by
  have he : (boundary 0).comp orderSmallHomotopy0 =
      (smallChains (orderNerveRealizationOpenStar P) 0).subtype - orderSmallSingularApproximation0 := by
    apply orderSmallSingle_spans
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, orderSmallHomotopy0_single,
      orderSmallSingularApproximation0_single]
    exact (orderSmallHomotopyZeroFill_exists σ).choose_spec.2
  exact DFunLike.congr_fun he c

end FiniteChains.Comb
