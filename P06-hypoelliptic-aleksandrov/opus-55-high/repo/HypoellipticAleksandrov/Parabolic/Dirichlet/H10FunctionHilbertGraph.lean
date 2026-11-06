module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolev

/-!
# Representative-level functions in the Hilbert `H¹₀` graph

This module sends an existing representative-level `H¹₀` function through
the inverse of the canonical equivalence with the Hilbert graph and records the
selected value and weak-gradient representatives.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The canonical Hilbert-graph point associated to a representative-level
`H¹₀` function. -/
def h10HilbertGraphOfH10Function
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (u : PDE.H10Function Ω) : H10HilbertGraph hΩ :=
  (h10HilbertGraphContinuousLinearEquiv hΩ).symm (u.toH10Graph hΩ)

variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (u : PDE.H10Function Ω)

/-- The selected value representative of the canonical Hilbert-graph point
agrees almost everywhere with the original representative. -/
theorem valueCLM_h10HilbertGraphOfH10Function
     :
    (valueCLM hΩ (h10HilbertGraphOfH10Function hΩ u) :
      PDE.Vec d → ℝ) =ᵐ[PDE.volumeOn Ω] u.toH1Function.toFun := by
  have hfst := PDE.W1pFunction.coeFn_toW1pGraph_fst
    u.toH1Function.toW1pFunction
  aesop

/-- Every selected weak-gradient coordinate of the canonical Hilbert-graph
point agrees almost everywhere with the corresponding original coordinate. -/
theorem gradientCoord_h10HilbertGraphOfH10Function
     (i : Fin d) :
    (fun x => PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i
      (gradientCLM hΩ (h10HilbertGraphOfH10Function hΩ u)) x)
      =ᵐ[PDE.volumeOn Ω]
    fun x => u.toH1Function.grad x i := by
  have hgraph :
      h10HilbertGraphContinuousLinearEquiv hΩ
          (h10HilbertGraphOfH10Function hΩ u) = u.toH10Graph hΩ :=
    (h10HilbertGraphContinuousLinearEquiv hΩ).apply_symm_apply _
  have hgradient :
      gradientCLM hΩ (h10HilbertGraphOfH10Function hΩ u) =
        u.toH1Function.toW1pFunction.toW1pGraph.1.2 := by
    aesop
  rw [hgradient]
  filter_upwards [PDE.coeFn_hilbertVectorLpCoord Ω _ i
      u.toH1Function.toW1pFunction.toW1pGraph.1.2,
    PDE.W1pFunction.coeFn_toW1pGraph_snd
      u.toH1Function.toW1pFunction] with x hcoord hgrad
  simp_all

end HypoellipticAleksandrov.Parabolic.Dirichlet
