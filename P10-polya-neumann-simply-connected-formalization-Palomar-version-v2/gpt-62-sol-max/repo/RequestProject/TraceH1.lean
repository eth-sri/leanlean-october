module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import RequestProject.NeumannSobolev
public import RequestProject.ReconDensity
public import RequestProject.TraceIneq

/-!
# The actual continuous boundary trace of H¹

The boundary space below uses ordinary coordinate measure `dθ` on `(0, 2π]`.
Thus its squared norm is the boundary integral, without a factor `1 / (2π)`.
In the orthonormal boundary Fourier basis `(2π)^(-1/2) exp(i n θ)`, the
coefficients are `sqrt (2π)` times the averaged `fourierCoeffOn` coefficients.

The trace is constructed from smooth compactly supported functions on the
whole plane. Their restrictions are dense in the genuine weak-gradient H¹
space, and the established trace inequality bounds their boundary values.
No fractional Sobolev trace theorem is assumed here.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology
open scoped Real InnerProductSpace ComplexConjugate

/-- Boundary L² for ordinary parameter measure, rather than normalized Haar
measure. The choice of an open left endpoint is irrelevant to its integrals. -/
abbrev BoundaryL2 := Lp ℂ 2 (volume.restrict (Ioc (0 : ℝ) (2 * π)))

/-- The smooth functions used to construct the trace are compactly supported
in the whole plane; they need not vanish on the boundary of the domain. -/
def smoothTraceTests : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | TestFunction univ f}
  zero_mem' := by
    refine ⟨contDiff_const, ?_, subset_univ _⟩
    exact HasCompactSupport.zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c f hf => id (TestFunction.const_mul hf c)


instance smoothTraceTestsCoeFun : CoeFun smoothTraceTests (fun _ => ℂ → ℂ) :=
  ⟨fun f => f.1⟩
lemma smoothTraceTests_memLp (Ω : Set ℂ) (f : smoothTraceTests) :
    MemLp (f : ℂ → ℂ) 2 (volume.restrict Ω) :=
  f.property.memLp' 2

lemma smoothTraceTests_memLp_deriv (Ω : Set ℂ) (f : smoothTraceTests)
    (i : Fin 2) : MemLp (fun z => fderiv ℝ (f : ℂ → ℂ) z (coordDir i)) 2
      (volume.restrict Ω) :=
  (f.property.dirD (coordDir i)).memLp' 2

/-- A smooth test function as an element of the genuine weak-gradient H¹
space. Its value and derivatives are the corresponding L² classes. -/
def smoothTraceH1 (Ω : Set ℂ) (f : smoothTraceTests) : NeumannH1 Ω :=
  h1Vector (isWeakGradient_of_smooth f.property.1 (smoothTraceTests_memLp Ω f)
    (smoothTraceTests_memLp_deriv Ω f))

@[simp] theorem h1Value_smoothTraceH1 (Ω : Set ℂ) (f : smoothTraceTests) :
    h1Value Ω (smoothTraceH1 Ω f) =
      (smoothTraceTests_memLp Ω f).toLp (f : ℂ → ℂ) := rfl

@[simp] theorem h1Gradient_smoothTraceH1 (Ω : Set ℂ) (f : smoothTraceTests) (i : Fin 2) :
    h1Gradient Ω i (smoothTraceH1 Ω f) =
      (smoothTraceTests_memLp_deriv Ω f i).toLp
        (fun z => fderiv ℝ (f : ℂ → ℂ) z (coordDir i)) := rfl

/-- Restriction of smooth functions to H¹ is a linear map. Gradient
uniqueness makes its linearity follow from that of the value restriction. -/
def smoothTraceH1Lin {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    smoothTraceTests →ₗ[ℂ] NeumannH1 Ω where
  toFun := smoothTraceH1 Ω
  map_add' f g := by
    apply h1Value_injective hΩ
    rfl
  map_smul' c f := by
    apply h1Value_injective hΩ
    rfl

@[simp] theorem smoothTraceH1Lin_apply {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (f : smoothTraceTests) : smoothTraceH1Lin hΩ f = smoothTraceH1 Ω f := rfl

private lemma tendsto_toLp_of_approx {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℂ) (hf : ∀ n, MemLp (f n) 2 μ) (u : Lp ℂ 2 μ)
    (hu : Tendsto (fun n => eLpNorm (f n - (u : α → ℂ)) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 u) := by
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf (u : α → ℂ) (Lp.memLp u)).2 hu
  simp_all

/-- Smooth functions on the whole plane have dense restrictions in the true
H¹ norm, including both weak derivatives. -/
theorem denseRange_smoothTraceH1Lin {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) : DenseRange (smoothTraceH1Lin hL.1.1) := by
  intro u
  obtain ⟨φ, hφ, hu, hg⟩ := exists_testFunction_approx hb hL (h1Value_weakGradient Ω u)
  let F : ℕ → smoothTraceTests := fun n => ⟨φ n, hφ n⟩
  have ht0 :=
    tendsto_toLp_of_approx φ (fun n => smoothTraceTests_memLp Ω (F n)) (h1Value Ω u) hu
  have hti :=
    fun i => tendsto_toLp_of_approx _
      (fun n => smoothTraceTests_memLp_deriv Ω (F n) i) (h1Gradient Ω i u) (hg i)
  have htcoord : Tendsto
      (fun n => WithLp.ofLp ((smoothTraceH1 Ω (F n) : NeumannH1 Ω) : H1Jet Ω))
      atTop (𝓝 (WithLp.ofLp (u : H1Jet Ω))) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    all_goals tauto
  have ht : Tendsto (fun n => smoothTraceH1Lin hL.1.1 (F n)) atTop (𝓝 u) := by
    apply tendsto_subtype_rng.2
    have h := ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => L2 Ω)).tendsto
        (WithLp.ofLp (u : H1Jet Ω))).comp htcoord
    assumption
  exact mem_closure_of_tendsto ht (Eventually.of_forall fun n =>
    Set.mem_range_self (f := smoothTraceH1Lin hL.1.1) (F n))

lemma IsBoundaryParam.continuous {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    Continuous γ := hγ.lipschitz.elim fun _ h => h.continuous

lemma smoothBoundary_memLp {γ : ℝ → ℂ} (hγ : Continuous γ) (f : smoothTraceTests) :
    MemLp (fun θ => f (γ θ)) 2 (volume.restrict (Ioc (0 : ℝ) (2 * π))) := by
  obtain ⟨B, hB⟩ := f.property.2.1.exists_bound_of_continuous f.property.1.continuous
  exact MemLp.of_bound (f.property.1.continuous.comp hγ).aestronglyMeasurable
    B (Eventually.of_forall fun θ => hB (γ θ))

/-- Restrict smooth tests to a continuous boundary parameter, with measure `dθ`. -/
def smoothBoundaryLin {γ : ℝ → ℂ} (hγ : Continuous γ) : smoothTraceTests →ₗ[ℂ] BoundaryL2 where
  toFun f := (smoothBoundary_memLp hγ f).toLp (fun θ => f (γ θ))
  map_add' f g := rfl
  map_smul' c f := rfl

def smoothTraceBoundaryLin {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    smoothTraceTests →ₗ[ℂ] BoundaryL2 := smoothBoundaryLin hγ.continuous

/-- The norm of a smooth H¹ vector is exactly its shifted energy norm. -/
theorem norm_sq_smoothTraceH1 (Ω : Set ℂ) (f : smoothTraceTests) :
    ‖smoothTraceH1 Ω f‖ ^ 2 =
      (∫ z in Ω, ‖f z‖ ^ 2) + ∫ z in Ω, gradSq (f : ℂ → ℂ) z := by
  rw [h1_norm_sq, h1Value_smoothTraceH1, norm_sq_toLp_eq_integral]
  simp only [Fin.sum_univ_two, h1Gradient_smoothTraceH1, norm_sq_toLp_eq_integral]
  have h0 := (smoothTraceTests_memLp_deriv Ω f 0).integrable_norm_pow (by decide : 2 ≠ 0)
  have h1 := (smoothTraceTests_memLp_deriv Ω f 1).integrable_norm_pow (by decide : 2 ≠ 0)
  rw [← integral_add h0 h1]
  rfl

/-- Boundary norms use ordinary coordinate measure exactly. -/
theorem norm_sq_smoothBoundary {γ : ℝ → ℂ} (hγ : Continuous γ) (f : smoothTraceTests) :
    ‖smoothBoundaryLin hγ f‖ ^ 2 = ∫ θ in (0 : ℝ)..(2 * π), ‖f (γ θ)‖ ^ 2 := by
  change ‖(smoothBoundary_memLp hγ f).toLp (fun θ => f (γ θ))‖ ^ 2 = _
  rw [norm_sq_toLp_eq_integral, intervalIntegral.integral_of_le Real.two_pi_pos.le]

theorem norm_sq_smoothTraceBoundary {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (f : smoothTraceTests) :
    ‖smoothTraceBoundaryLin hγ f‖ ^ 2 = ∫ θ in (0 : ℝ)..(2 * π), ‖f (γ θ)‖ ^ 2 :=
  norm_sq_smoothBoundary hγ.continuous f

/-- The already proved geometric trace inequality supplies the bound required
to extend the smooth trace; boundedness is not an extra hypothesis. -/
theorem exists_bound_smoothTraceBoundary {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : smoothTraceTests,
      ‖smoothTraceBoundaryLin hγ f‖ ≤ C * ‖smoothTraceH1Lin hL.1.1 f‖ := by
  obtain ⟨C, hC, hbound⟩ := trace_sq_le hb hL hγ
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, fun f => ?_⟩
  obtain ⟨Kf, hKf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    f.property.2.1 f.property.1 (by simp)
  obtain ⟨B, hB⟩ := f.property.2.1.exists_bound_of_continuous f.property.1.continuous
  have hs := hbound (f : ℂ → ℂ) Kf hKf B hB
  rw [← norm_sq_smoothTraceBoundary hγ f, ← norm_sq_smoothTraceH1 Ω f] at hs
  apply le_of_sq_le_sq ?_ (by positivity)
  rwa [mul_pow, Real.sq_sqrt hC]

/-- The true boundary trace, constructed by bounded extension from the dense
smooth restrictions in H¹. -/
def h1BoundaryTrace {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    NeumannH1 Ω →L[ℂ] BoundaryL2 :=
  (smoothTraceBoundaryLin hγ).extendOfNorm (smoothTraceH1Lin hL.1.1)

/-- The constructed trace agrees with the actual pointwise boundary values
on every smooth compactly supported test function on the plane. -/
theorem h1BoundaryTrace_smooth {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (f : smoothTraceTests) :
    h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f) = smoothTraceBoundaryLin hγ f := by
  obtain ⟨C, _, hC⟩ := exists_bound_smoothTraceBoundary hb hL hγ
  exact LinearMap.extendOfNorm_eq (denseRange_smoothTraceH1Lin hb hL) ⟨C, hC⟩ f

theorem h1BoundaryTrace_smooth_ae {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (f : smoothTraceTests) :
    (h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * π))] fun θ => f (γ θ) := by
  rw [h1BoundaryTrace_smooth hb hL hγ f]
  exact (smoothBoundary_memLp hγ.continuous f).coeFn_toLp

/-- Pairing the actual smooth trace with a boundary density is the ordinary
coordinate boundary integral. -/
theorem h1BoundaryTrace_inner_smooth {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (f : smoothTraceTests) (g : BoundaryL2) :
    ⟪h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f), g⟫_ℂ =
      ∫ θ in Ioc (0 : ℝ) (2 * π), conj (f (γ θ)) * g θ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hθ
  simp only [RCLike.inner_apply', hθ]

/-- The boundary load in the shifted H¹ variational equation is the adjoint
of the actual trace. This is the input needed to construct a genuine NtD map. -/
def h1BoundaryLoad {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    BoundaryL2 →L[ℂ] NeumannH1 Ω :=
  ContinuousLinearMap.adjoint (h1BoundaryTrace hb hL hγ)

theorem h1BoundaryLoad_inner {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (u : NeumannH1 Ω) (g : BoundaryL2) :
    ⟪u, h1BoundaryLoad hb hL hγ g⟫_ℂ = ⟪h1BoundaryTrace hb hL hγ u, g⟫_ℂ := by
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

end PolyaNeumann

end
