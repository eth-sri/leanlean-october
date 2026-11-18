module

public import PDEFoundation.Sobolev.H1.Graph
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import PDEFoundation.Sobolev.H1.ZeroBoundary

@[expose] public noncomputable section

namespace PDE
section
open scoped ENNReal RealInnerProductSpace

/-- The `ℓ²`-normed product ambient for the `p = 2` weak-gradient graph. -/
abbrev H1HilbertAmbient {d : ℕ} (U : Set (Vec d)) :=
  WithLp 2
    (ScalarLp U (2 : ℝ≥0∞) × HilbertVectorLp U (2 : ℝ≥0∞))

/-- The standard continuous linear equivalence from the `ℓ²` product
realization to the ordinary product carrier. -/
abbrev h1HilbertAmbientEquiv {d : ℕ} (U : Set (Vec d)) :
    H1HilbertAmbient U ≃L[ℝ]
      WeakGradientLpPair U (2 : ℝ≥0∞) :=
  WithLp.prodContinuousLinearEquiv 2 ℝ
    (ScalarLp U (2 : ℝ≥0∞))
    (HilbertVectorLp U (2 : ℝ≥0∞))

/-- The same weak-gradient graph, pulled back to the Hilbert product norm. -/
abbrev h1HilbertClosedSubmodule {d : ℕ} (U : Set (Vec d)) :
    ClosedSubmodule ℝ (H1HilbertAmbient U) :=
  (weakGradientGraph U (2 : ℝ≥0∞)).comap
    (h1HilbertAmbientEquiv U).toContinuousLinearMap

/-- Submodule view used to inherit the Hilbert-space instances. -/
abbrev h1HilbertSubmodule {d : ℕ} (U : Set (Vec d)) :
    Submodule ℝ (H1HilbertAmbient U) :=
  (h1HilbertClosedSubmodule U).toSubmodule

/-- The complete Hilbert realization of `H1Graph U`. -/
abbrev H1HilbertGraph {d : ℕ} (U : Set (Vec d)) :=
  ↥(h1HilbertSubmodule U)

namespace H1HilbertGraph

variable {d : ℕ} {U : Set (Vec d)}

noncomputable instance : SeminormedAddCommGroup (H1HilbertGraph U) := by
  exact inferInstanceAs (SeminormedAddCommGroup (h1HilbertSubmodule U))

noncomputable instance : NormedAddCommGroup (H1HilbertGraph U) := by
  exact inferInstanceAs (NormedAddCommGroup (h1HilbertSubmodule U))

noncomputable instance : NormedSpace ℝ (H1HilbertGraph U) := by
  exact inferInstanceAs (NormedSpace ℝ (h1HilbertSubmodule U))

noncomputable instance : InnerProductSpace ℝ (H1HilbertGraph U) := by
  exact inferInstanceAs (InnerProductSpace ℝ (h1HilbertSubmodule U))

noncomputable instance : CompleteSpace (H1HilbertGraph U) := by
  exact (h1HilbertClosedSubmodule U).isClosed.completeSpace_coe

/-- Forget the Hilbert product norm while retaining the same graph pair. -/
def toH1Graph (z : H1HilbertGraph U) : H1Graph U :=
  ⟨h1HilbertAmbientEquiv U z.1, z.2⟩

/-- Equip a point of the maximum-norm graph with the equivalent Hilbert
product norm. -/
def ofH1Graph (z : H1Graph U) : H1HilbertGraph U :=
  ⟨(h1HilbertAmbientEquiv U).symm z.1, by
    change
      h1HilbertAmbientEquiv U
          ((h1HilbertAmbientEquiv U).symm z.1) ∈
        weakGradientGraph U (2 : ℝ≥0∞)
    rw [(h1HilbertAmbientEquiv U).apply_symm_apply]
    exact z.2⟩

@[simp]
theorem toH1Graph_ofH1Graph (z : H1Graph U) :
    toH1Graph (ofH1Graph z) = z := by
  apply Subtype.ext
  exact (h1HilbertAmbientEquiv U).apply_symm_apply z.1

@[simp]
theorem ofH1Graph_toH1Graph (z : H1HilbertGraph U) :
    ofH1Graph (toH1Graph z) = z := by
  apply Subtype.ext
  exact (h1HilbertAmbientEquiv U).symm_apply_apply z.1

/-- The max-norm and Hilbert-norm graph carriers have exactly the same
elements. Their norms remain intentionally distinct. -/
def equivH1Graph : H1HilbertGraph U ≃ H1Graph U where
  toFun := toH1Graph
  invFun := ofH1Graph
  left_inv := ofH1Graph_toH1Graph
  right_inv := toH1Graph_ofH1Graph

/-- Scalar `L²` value component. -/
abbrev value (z : H1HilbertGraph U) :
    ScalarLp U (2 : ℝ≥0∞) :=
  z.1.fst

/-- Euclidean Hilbert-vector `L²` gradient component. -/
abbrev gradient (z : H1HilbertGraph U) :
    HilbertVectorLp U (2 : ℝ≥0∞) :=
  z.1.snd

/-- Continuous scalar-value projection from the Hilbert graph. -/
def valueCLM :
    H1HilbertGraph U →L[ℝ] ScalarLp U (2 : ℝ≥0∞) :=
  (WithLp.fstL
      (p := 2) (𝕜 := ℝ)
      (α := ScalarLp U (2 : ℝ≥0∞))
      (β := HilbertVectorLp U (2 : ℝ≥0∞))).comp
    (h1HilbertSubmodule U).subtypeL

@[simp]
theorem valueCLM_apply (z : H1HilbertGraph U) :
    valueCLM z = value z :=
  rfl

/-- Continuous Euclidean-gradient projection from the Hilbert graph. -/
def gradientCLM :
    H1HilbertGraph U →L[ℝ]
      HilbertVectorLp U (2 : ℝ≥0∞) :=
  (WithLp.sndL
      (p := 2) (𝕜 := ℝ)
      (α := ScalarLp U (2 : ℝ≥0∞))
      (β := HilbertVectorLp U (2 : ℝ≥0∞))).comp
    (h1HilbertSubmodule U).subtypeL

@[simp]
theorem gradientCLM_apply (z : H1HilbertGraph U) :
    gradientCLM z = gradient z :=
  rfl

end H1HilbertGraph

end
end PDE

namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open Filter
open scoped ENNReal RealInnerProductSpace Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The continuous linear equivalence from the Hilbert-norm weak-gradient
graph to the corresponding maximum-norm graph. -/
noncomputable def h1HilbertGraphContinuousLinearEquiv
    (Ω : Set (PDE.Vec d)) :
    PDE.H1HilbertGraph Ω ≃L[ℝ] PDE.H1Graph Ω :=
  (PDE.h1HilbertAmbientEquiv Ω).ofSubmodule'
    (PDE.weakGradientGraph Ω (2 : ℝ≥0∞)).toSubmodule

@[simp]
theorem h1HilbertGraphContinuousLinearEquiv_apply
    (z : PDE.H1HilbertGraph Ω) :
    h1HilbertGraphContinuousLinearEquiv Ω z =
      PDE.H1HilbertGraph.toH1Graph z :=
  rfl

/-- The linear map taking an actual bundled smooth compactly supported test
function to the Hilbert-norm weak-gradient graph. -/
noncomputable def smoothCompactlySupportedH1HilbertGraphLinearMap
    (hΩ : IsOpen Ω) :
    PDE.WeakTestFunction Ω →ₗ[ℝ] PDE.H1HilbertGraph Ω :=
  (h1HilbertGraphContinuousLinearEquiv Ω).symm.toLinearMap.comp
    (PDE.smoothCompactlySupportedW1pGraphLinearMap
      (p := (2 : ℝ≥0∞)) hΩ)

/-- The submodule of Hilbert-graph points coming from actual bundled smooth
compactly supported test functions. -/
noncomputable def smoothCompactlySupportedH1HilbertGraphSubmodule
    (hΩ : IsOpen Ω) :
    Submodule ℝ (PDE.H1HilbertGraph Ω) :=
  LinearMap.range (smoothCompactlySupportedH1HilbertGraphLinearMap hΩ)

/-- The closed Hilbert-graph submodule defining spatial `H¹₀`. -/
noncomputable def h10HilbertGraphClosedSubmodule
    (hΩ : IsOpen Ω) :
    ClosedSubmodule ℝ (PDE.H1HilbertGraph Ω) :=
  (smoothCompactlySupportedH1HilbertGraphSubmodule hΩ).closure

/-- The complete Hilbert realization of spatial `H¹₀(Ω)`. -/
noncomputable abbrev H10HilbertGraph (hΩ : IsOpen Ω) :=
  ↥((h10HilbertGraphClosedSubmodule hΩ).toSubmodule)

noncomputable instance (hΩ : IsOpen Ω) :
    SeminormedAddCommGroup (H10HilbertGraph hΩ) := by
  exact inferInstanceAs
    (SeminormedAddCommGroup
      ((h10HilbertGraphClosedSubmodule hΩ).toSubmodule))

noncomputable instance (hΩ : IsOpen Ω) :
    NormedAddCommGroup (H10HilbertGraph hΩ) := by
  exact inferInstanceAs
    (NormedAddCommGroup ((h10HilbertGraphClosedSubmodule hΩ).toSubmodule))

noncomputable instance (hΩ : IsOpen Ω) :
    NormedSpace ℝ (H10HilbertGraph hΩ) := by
  exact inferInstanceAs
    (NormedSpace ℝ ((h10HilbertGraphClosedSubmodule hΩ).toSubmodule))

noncomputable instance (hΩ : IsOpen Ω) :
    InnerProductSpace ℝ (H10HilbertGraph hΩ) := by
  exact inferInstanceAs
    (InnerProductSpace ℝ
      ((h10HilbertGraphClosedSubmodule hΩ).toSubmodule))

noncomputable instance (hΩ : IsOpen Ω) :
    CompleteSpace (H10HilbertGraph hΩ) :=
  (h10HilbertGraphClosedSubmodule hΩ).isClosed.completeSpace_coe

/-- The continuous scalar-value map from spatial `H¹₀` to spatial `L²`. -/
noncomputable def valueCLM (hΩ : IsOpen Ω) :
    H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  PDE.H1HilbertGraph.valueCLM.comp
    (h10HilbertGraphClosedSubmodule hΩ).toSubmodule.subtypeL

/-- The continuous weak-gradient map from spatial `H¹₀` to vector-valued
spatial `L²`. -/
noncomputable def gradientCLM (hΩ : IsOpen Ω) :
    H10HilbertGraph hΩ →L[ℝ]
      PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
  PDE.H1HilbertGraph.gradientCLM.comp
    (h10HilbertGraphClosedSubmodule hΩ).toSubmodule.subtypeL

@[simp]
theorem valueCLM_apply (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    valueCLM hΩ u = PDE.H1HilbertGraph.value (u : PDE.H1HilbertGraph Ω) :=
  rfl

@[simp]
theorem gradientCLM_apply (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    gradientCLM hΩ u = PDE.H1HilbertGraph.gradient (u : PDE.H1HilbertGraph Ω) :=
  rfl

/-- The canonical inclusion of an actual bundled smooth compactly supported
test function into the Hilbert realization of spatial `H¹₀`. -/
noncomputable def smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph
    (hΩ : IsOpen Ω) (φ : PDE.WeakTestFunction Ω) : H10HilbertGraph hΩ :=
  ⟨smoothCompactlySupportedH1HilbertGraphLinearMap hΩ φ,
    subset_closure
      (LinearMap.mem_range_self
        (smoothCompactlySupportedH1HilbertGraphLinearMap hΩ) φ)⟩

/-- Every Hilbert-graph `H¹₀` point is a sequential limit of images of actual
bundled smooth compactly supported test functions. -/
theorem exists_tendsto_smooth
    (hΩ : IsOpen Ω) (u : H10HilbertGraph hΩ) :
    ∃ φ : ℕ → PDE.WeakTestFunction Ω,
      Tendsto
        (fun n => smoothCompactlySupportedH1HilbertGraphLinearMap hΩ (φ n))
        atTop (𝓝 (u : PDE.H1HilbertGraph Ω)) := by
  have huClosure :
      (u : PDE.H1HilbertGraph Ω) ∈
        closure
          ((smoothCompactlySupportedH1HilbertGraphSubmodule hΩ :
            Submodule ℝ (PDE.H1HilbertGraph Ω)) : Set (PDE.H1HilbertGraph Ω)) := by
    have hu := u.property
    change (u : PDE.H1HilbertGraph Ω) ∈
      (smoothCompactlySupportedH1HilbertGraphSubmodule hΩ).topologicalClosure at hu
    change (u : PDE.H1HilbertGraph Ω) ∈
      ((smoothCompactlySupportedH1HilbertGraphSubmodule hΩ).topologicalClosure :
        Set (PDE.H1HilbertGraph Ω)) at hu
    rwa [Submodule.topologicalClosure_coe] at hu
  rcases mem_closure_iff_seq_limit.mp huClosure with ⟨v, hv, hvTendsto⟩
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
    (hΩ : IsOpen Ω) :
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
      ⟨h1HilbertGraphContinuousLinearEquiv Ω z, hz⟩
    rcases PDE.H10Graph.exists_tendsto_smooth hΩ u with ⟨φ, hφ⟩
    have hTendsto :
        Tendsto
          (fun n => (h1HilbertGraphContinuousLinearEquiv Ω).symm
            (PDE.smoothCompactlySupportedH1Graph hΩ (φ n)))
          atTop (𝓝 z) := by
      have hcontinuous :=
        (h1HilbertGraphContinuousLinearEquiv Ω).symm.continuous.tendsto
          (h1HilbertGraphContinuousLinearEquiv Ω z)
      simpa only [u, Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using
        hcontinuous.comp hφ
    apply (h10HilbertGraphClosedSubmodule hΩ).isClosed.mem_of_tendsto hTendsto
    filter_upwards with n
    exact subset_closure
      (LinearMap.mem_range_self
        (smoothCompactlySupportedH1HilbertGraphLinearMap hΩ) (φ n))

/-- The continuous linear equivalence between the direct Hilbert `H¹₀`
closure and the sibling maximum-norm `H¹₀` graph. -/
noncomputable def h10HilbertGraphContinuousLinearEquiv
    (hΩ : IsOpen Ω) :
    H10HilbertGraph hΩ ≃L[ℝ] PDE.H10Graph hΩ :=
  (ContinuousLinearEquiv.ofEq
    (h10HilbertGraphClosedSubmodule hΩ).toSubmodule
    ((PDE.h10GraphClosedSubmodule hΩ).comap
      (h1HilbertGraphContinuousLinearEquiv Ω).toContinuousLinearMap).toSubmodule
    (congrArg ClosedSubmodule.toSubmodule
      (h10HilbertGraphClosedSubmodule_eq_comap hΩ))).trans
    ((h1HilbertGraphContinuousLinearEquiv Ω).ofSubmodule'
      (PDE.h10GraphClosedSubmodule hΩ).toSubmodule)

end HypoellipticAleksandrov.Parabolic.Dirichlet

