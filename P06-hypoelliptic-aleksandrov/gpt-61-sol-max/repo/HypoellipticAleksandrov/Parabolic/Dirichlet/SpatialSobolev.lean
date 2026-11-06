module

public import PDEFoundation.Sobolev.H1.HilbertGraph
public import PDEFoundation.Sobolev.H1.ZeroBoundary

/-!
# Hilbert realization of spatial `H¹₀`

This module defines spatial `H¹₀(Ω)` as the closure in the Hilbert realization
of the weak-gradient graph of the image of actual bundled smooth compactly
supported test functions.  It then proves that this carrier agrees with the
existing maximum-norm graph realization from `PDEFoundation`.

No density result for the value map into spatial `L²` is asserted here.
-/

@[expose] public section

open Filter
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

/-- The continuous linear equivalence from the Hilbert-norm weak-gradient
graph to the corresponding maximum-norm graph. -/
def h1HilbertGraphContinuousLinearEquiv
    (Ω : PDE.VelocityRegion d) :
    PDE.H1HilbertGraph Ω ≃L[ℝ] PDE.H1Graph Ω :=
  (PDE.h1HilbertAmbientEquiv Ω).ofSubmodule'
    (PDE.weakGradientGraph Ω (2 )).toSubmodule

@[simp]
theorem h1HilbertGraphContinuousLinearEquiv_apply
    (z : PDE.H1HilbertGraph Ω) :
    h1HilbertGraphContinuousLinearEquiv Ω z =
      PDE.H1HilbertGraph.toH1Graph z :=
  rfl

variable (hΩ : IsOpen Ω)

/-- The linear map taking an actual bundled smooth compactly supported test
function to the Hilbert-norm weak-gradient graph. -/
def smoothCompactlySupportedH1HilbertGraphLinearMap
     :
    PDE.WeakTestFunction Ω →ₗ[ℝ] PDE.H1HilbertGraph Ω :=
  (h1HilbertGraphContinuousLinearEquiv Ω).symm.toLinearMap.comp
    (PDE.smoothCompactlySupportedW1pGraphLinearMap
       hΩ)

/-- The submodule of Hilbert-graph points coming from actual bundled smooth
compactly supported test functions. -/
def smoothCompactlySupportedH1HilbertGraphSubmodule
     :
    Submodule ℝ (PDE.H1HilbertGraph Ω) :=
  LinearMap.range (smoothCompactlySupportedH1HilbertGraphLinearMap hΩ)

/-- The closed Hilbert-graph submodule defining spatial `H¹₀`. -/
def h10HilbertGraphClosedSubmodule
     :
    ClosedSubmodule ℝ (PDE.H1HilbertGraph Ω) :=
  (smoothCompactlySupportedH1HilbertGraphSubmodule hΩ).closure

/-- The complete Hilbert realization of spatial `H¹₀(Ω)`. -/
abbrev H10HilbertGraph (hΩ : IsOpen Ω) :=
  ↥((h10HilbertGraphClosedSubmodule hΩ).toSubmodule)

instance (hΩ : IsOpen Ω) :
    SeminormedAddCommGroup (H10HilbertGraph hΩ) := inferInstance

instance (hΩ : IsOpen Ω) :
    NormedAddCommGroup (H10HilbertGraph hΩ) := inferInstance

instance (hΩ : IsOpen Ω) :
    NormedSpace ℝ (H10HilbertGraph hΩ) := inferInstanceAs
    (NormedSpace ℝ ((h10HilbertGraphClosedSubmodule hΩ).toSubmodule))

instance (hΩ : IsOpen Ω) :
    InnerProductSpace ℝ (H10HilbertGraph hΩ) := inferInstance

instance (hΩ : IsOpen Ω) :
    CompleteSpace (H10HilbertGraph hΩ) :=
  (h10HilbertGraphClosedSubmodule hΩ).isClosed.completeSpace_coe

variable (hΩ : IsOpen Ω)

/-- The continuous scalar-value map from spatial `H¹₀` to spatial `L²`. -/
def valueCLM  :
    H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 ) :=
  PDE.H1HilbertGraph.valueCLM.comp
    (h10HilbertGraphClosedSubmodule hΩ).toSubmodule.subtypeL

/-- The continuous weak-gradient map from spatial `H¹₀` to vector-valued
spatial `L²`. -/
def gradientCLM  :
    H10HilbertGraph hΩ →L[ℝ]
      PDE.HilbertVectorLp Ω (2 ) :=
  PDE.H1HilbertGraph.gradientCLM.comp
    (h10HilbertGraphClosedSubmodule hΩ).toSubmodule.subtypeL

variable (u : H10HilbertGraph hΩ)

@[simp]
theorem valueCLM_apply   :
    valueCLM hΩ u = PDE.H1HilbertGraph.value (u : PDE.H1HilbertGraph Ω) :=
  rfl

@[simp]
theorem gradientCLM_apply   :
    gradientCLM hΩ u = PDE.H1HilbertGraph.gradient (u : PDE.H1HilbertGraph Ω) :=
  rfl

/-- The canonical inclusion of an actual bundled smooth compactly supported
test function into the Hilbert realization of spatial `H¹₀`. -/
def smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph
     (φ : PDE.WeakTestFunction Ω) : H10HilbertGraph hΩ :=
  ⟨_,
    subset_closure
      (LinearMap.mem_range_self
        _ φ)⟩

/-- Every Hilbert-graph `H¹₀` point is a sequential limit of images of actual
bundled smooth compactly supported test functions. -/
theorem exists_tendsto_smooth
     (u : H10HilbertGraph hΩ) :
    ∃ φ : ℕ → PDE.WeakTestFunction Ω,
      Tendsto
        (fun n => smoothCompactlySupportedH1HilbertGraphLinearMap hΩ (φ n))
        atTop (𝓝 (u : PDE.H1HilbertGraph Ω)) := by

  rcases mem_closure_iff_seq_limit.mp (by
      have hu := u.property
      assumption) with ⟨v, hv, hvTendsto⟩
  have hactual : ∀ n, ∃ φ : PDE.WeakTestFunction Ω,
      smoothCompactlySupportedH1HilbertGraphLinearMap hΩ φ = v n := by
    intro n
    rcases hv n with ⟨φ, hφ⟩
    exact ⟨φ, hφ⟩
  choose φ hφ using hactual
  refine ⟨φ, ?_⟩
  simpa only [hφ] using hvTendsto

/-- The direct Hilbert closure of actual tests is the pullback of the sibling
maximum-norm zero-boundary graph through the Hilbert/max-norm equivalence. -/
theorem h10HilbertGraphClosedSubmodule_eq_comap
     :
    h10HilbertGraphClosedSubmodule hΩ =
      (PDE.h10GraphClosedSubmodule hΩ).comap
        (h1HilbertGraphContinuousLinearEquiv Ω).toContinuousLinearMap := by
  apply le_antisymm
  · refine (Submodule.closure_le).2 ?_
    intro z hz
    rcases hz with ⟨φ, hφ⟩
    rw [← hφ]
    change h1HilbertGraphContinuousLinearEquiv Ω
        ((h1HilbertGraphContinuousLinearEquiv Ω).symm
          (PDE.smoothCompactlySupportedH1Graph hΩ φ)) ∈
      (PDE.h10GraphClosedSubmodule hΩ).toSubmodule
    rw [(h1HilbertGraphContinuousLinearEquiv Ω).apply_symm_apply]
    exact PDE.smoothCompactlySupportedH1Graph_mem_h10Graph hΩ φ
  · intro z hz
    let u : PDE.H10Graph hΩ :=
      ⟨_, hz⟩
    rcases PDE.H10Graph.exists_tendsto_smooth hΩ u with ⟨φ, hφ⟩

    apply (h10HilbertGraphClosedSubmodule hΩ).isClosed.mem_of_tendsto (by
        have hcontinuous :=
          (h1HilbertGraphContinuousLinearEquiv Ω).symm.continuous.tendsto
            (h1HilbertGraphContinuousLinearEquiv Ω z)
        simpa only [u, Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
          hcontinuous.comp hφ)
    filter_upwards with n
    change smoothCompactlySupportedH1HilbertGraphLinearMap hΩ (φ n) ∈
      (h10HilbertGraphClosedSubmodule hΩ).toSubmodule
    exact subset_closure
      (LinearMap.mem_range_self
        _ (φ n))

/-- The continuous linear equivalence between the direct Hilbert `H¹₀`
closure and the sibling maximum-norm `H¹₀` graph. -/
def h10HilbertGraphContinuousLinearEquiv
     :
    H10HilbertGraph hΩ ≃L[ℝ] PDE.H10Graph hΩ :=
  (ContinuousLinearEquiv.ofEq
    (h10HilbertGraphClosedSubmodule hΩ).toSubmodule
    _
    (congrArg ClosedSubmodule.toSubmodule
      (h10HilbertGraphClosedSubmodule_eq_comap hΩ))).trans
    ((h1HilbertGraphContinuousLinearEquiv Ω).ofSubmodule'
      (PDE.h10GraphClosedSubmodule hΩ).toSubmodule)

end HypoellipticAleksandrov.Parabolic.Dirichlet
