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

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

/-- Boundary L² for ordinary parameter measure, rather than normalized Haar
measure. The choice of an open left endpoint is irrelevant to its integrals. -/
abbrev BoundaryL2 := Lp ℂ 2 (volume.restrict (Ioc 0 (2 * π)))

/-- The smooth functions used to construct the trace are compactly supported
in the whole plane; they need not vanish on the boundary of the domain. -/
def smoothTraceTests : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | TestFunction univ f}
  zero_mem' := by
    refine ⟨contDiff_const, ?_, subset_univ _⟩
    exact HasCompactSupport.zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c f hf => by
    change TestFunction univ (fun z => c * f z)
    exact hf.const_mul c


instance : CoeFun smoothTraceTests fun _ => ℂ → ℂ := ⟨Subtype.val⟩

lemma smoothTraceTests_memLp (Ω : Set ℂ) (f : smoothTraceTests) :
    MemLp f 2 (volume.restrict Ω) :=
  f.2.memLp' 2

lemma smoothTraceTests_memLp_deriv (Ω : Set ℂ) (f : smoothTraceTests)
    (i : Fin 2) : MemLp (fun z => fderiv ℝ f z (coordDir i)) 2
      (volume.restrict Ω) :=
  (f.2.dirD (coordDir i)).memLp' 2

/-- A smooth test function as an element of the genuine weak-gradient H¹
space. Its value and derivatives are the corresponding L² classes. -/
def smoothTraceH1 Ω (f : smoothTraceTests) : NeumannH1 Ω :=
  h1Vector (isWeakGradient_of_smooth f.2.1 (smoothTraceTests_memLp Ω f)
    (smoothTraceTests_memLp_deriv Ω f))

@[simp] theorem h1Value_smoothTraceH1 (Ω : Set ℂ) (f : smoothTraceTests) :
    h1Value Ω (smoothTraceH1 Ω f) =
      (smoothTraceTests_memLp Ω f).toLp f := rfl

@[simp] theorem h1Gradient_smoothTraceH1 (Ω : Set ℂ) (f : smoothTraceTests) (i : Fin 2) :
    h1Gradient Ω i (smoothTraceH1 Ω f) =
      (smoothTraceTests_memLp_deriv Ω f i).toLp
        (fun z => fderiv ℝ f z (coordDir i)) := rfl

/-- Restriction of smooth functions to H¹ is a linear map. Gradient
uniqueness makes its linearity follow from that of the value restriction. -/
def smoothTraceH1Lin  (hΩ : IsOpen Ω) :
    smoothTraceTests →ₗ[ℂ] NeumannH1 Ω where
  toFun := smoothTraceH1 Ω
  map_add' f g := by
    apply h1Value_injective hΩ
    rw [map_add]
    simp
    exact MemLp.toLp_add (smoothTraceTests_memLp Ω f) (smoothTraceTests_memLp Ω g)
  map_smul' c f := by
    apply h1Value_injective hΩ
    rw [map_smul]
    simp
    exact MemLp.toLp_const_smul c (smoothTraceTests_memLp Ω f)

@[simp] theorem smoothTraceH1Lin_apply  hΩ
    f : smoothTraceH1Lin hΩ f = smoothTraceH1 Ω f := rfl

private lemma tendsto_toLp_of_approx {α : Type*} [MeasurableSpace α] {μ}
    (f : ℕ → α → ℂ) (hf : ∀ n, MemLp (f n) 2 μ) (u : Lp ℂ 2 μ)
    (hu : Tendsto (fun n => eLpNorm (f n - (u : α → ℂ)) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 u) := by
  simpa using (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u (Lp.memLp u)).2 hu

/-- Smooth functions on the whole plane have dense restrictions in the true
H¹ norm, including both weak derivatives. -/
theorem denseRange_smoothTraceH1Lin  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) : DenseRange (smoothTraceH1Lin hL.1.1) := by
  intro u
  obtain ⟨φ, hφ, hu, hg⟩ := exists_testFunction_approx hb hL (h1Value_weakGradient Ω u)
  let F : ℕ → smoothTraceTests := fun n => ⟨φ n, hφ n⟩
  have hti : ∀ i : Fin 2, Tendsto
      (fun n => (smoothTraceTests_memLp_deriv Ω (F n) i).toLp
        (fun z => fderiv ℝ (φ n) z (coordDir i))) atTop (𝓝 (h1Gradient Ω i u)) :=
    fun i => tendsto_toLp_of_approx _
      (fun n => smoothTraceTests_memLp_deriv Ω (F n) i) (h1Gradient Ω i u) (hg i)
  exact mem_closure_of_tendsto (show Tendsto (fun n => smoothTraceH1Lin hL.1.1 (F n)) atTop (𝓝 u) by
    apply tendsto_subtype_rng.2
    have h := ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => L2 Ω)).tendsto
        (WithLp.ofLp (u : H1Jet Ω))).comp (show Tendsto (fun n => WithLp.ofLp ((smoothTraceH1 Ω (F n) : NeumannH1 Ω) : H1Jet Ω)) atTop (𝓝 (WithLp.ofLp (u : H1Jet Ω))) by
          refine tendsto_pi_nhds.2 fun i => ?_
          refine Fin.cases ?_ (fun j => ?_) i
          · exact tendsto_toLp_of_approx φ (fun n => smoothTraceTests_memLp Ω (F n)) (h1Value Ω u) hu
          · exact hti j)
    simp [Function.comp_def] at h
    exact h) (Eventually.of_forall fun n =>
    Set.mem_range_self (f := smoothTraceH1Lin hL.1.1) (F n))

local notation "Φ0" => IsBoundaryParam Ω γ

lemma smoothTraceBoundary_memLp  
    (hγ : Φ0) (f : smoothTraceTests) :
    MemLp (fun θ => f (γ θ)) 2 (volume.restrict (Ioc 0 (2 * π))) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨B, hB⟩ := f.property.2.1.exists_bound_of_continuous f.property.1.continuous
  exact MemLp.of_bound (f.property.1.continuous.comp hK.continuous).aestronglyMeasurable
    B (Eventually.of_forall fun θ => hB (γ θ))

/-- The actual boundary values of a smooth test function, with measure `dθ`. -/
def smoothTraceBoundaryLin   (hγ : Φ0) :
    smoothTraceTests →ₗ[ℂ] BoundaryL2 where
  toFun f := (smoothTraceBoundary_memLp hγ f).toLp (fun θ => f (γ θ))
  map_add' f g := by
    exact MemLp.toLp_add (smoothTraceBoundary_memLp hγ f) (smoothTraceBoundary_memLp hγ g)
  map_smul' c f := by
    exact MemLp.toLp_const_smul c (smoothTraceBoundary_memLp hγ f)

lemma norm_sq_toLp_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  let u := hf.toLp f
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) u u)
  rw [inner_self_eq_norm_sq, ← integral_re (L2.integrable_inner u u)] at h
  simp_rw [inner_self_eq_norm_sq] at h
  rw [h]
  exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun z => ‖z‖ ^ 2))

/-- The norm of a smooth H¹ vector is exactly its shifted energy norm. -/
theorem norm_sq_smoothTraceH1 (Ω : Set ℂ) (f : smoothTraceTests) :
    ‖smoothTraceH1 Ω f‖ ^ 2 =
      (∫ z in Ω, ‖f z‖ ^ 2) + ∫ z in Ω, gradSq (f : ℂ → ℂ) z := by
  rw [h1_norm_sq, h1Value_smoothTraceH1, norm_sq_toLp_eq_integral]
  simp only [Fin.sum_univ_two, h1Gradient_smoothTraceH1, norm_sq_toLp_eq_integral]
  rw [← integral_add ((smoothTraceTests_memLp_deriv Ω f 0).integrable_norm_pow (by decide : 2 ≠ 0)) ((smoothTraceTests_memLp_deriv Ω f 1).integrable_norm_pow (by decide : 2 ≠ 0))]
  rfl

/-- The true boundary trace, constructed by bounded extension from the dense
smooth restrictions in H¹. -/
def h1BoundaryTrace  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hγ : Φ0) :
    NeumannH1 Ω →L[ℂ] BoundaryL2 :=
  (smoothTraceBoundaryLin hγ).extendOfNorm (smoothTraceH1Lin hL.1.1)

theorem h1BoundaryTrace_smooth_ae  (hb : Bornology.IsBounded Ω)
    hL  (hγ : Φ0)
    (f : smoothTraceTests) :
    (h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * π))] fun θ => f (γ θ) := by
  rw [show h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f) = smoothTraceBoundaryLin hγ f by
    obtain ⟨C, _, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : smoothTraceTests, ‖smoothTraceBoundaryLin hγ f‖ ≤ C * ‖smoothTraceH1Lin hL.1.1 f‖ := by
      obtain ⟨C, hC, hbound⟩ := trace_sq_le hb hL hγ
      refine ⟨Real.sqrt C, Real.sqrt_nonneg C, fun f => ?_⟩
      obtain ⟨Kf, hKf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
        f.property.2.1 f.property.1 (by simp)
      obtain ⟨B, hB⟩ := f.property.2.1.exists_bound_of_continuous f.property.1.continuous
      have hs := hbound f Kf hKf B hB
      rw [← (show ‖smoothTraceBoundaryLin hγ f‖ ^ 2 = ∫ θ in 0..(2 * π), ‖f (γ θ)‖ ^ 2 by
        change ‖(smoothTraceBoundary_memLp hγ f).toLp (fun θ => f (γ θ))‖ ^ 2 = _
        rw [norm_sq_toLp_eq_integral, intervalIntegral.integral_of_le (by positivity)]), ← norm_sq_smoothTraceH1 Ω f] at hs
      have heq : (Real.sqrt C * ‖smoothTraceH1 Ω f‖) ^ 2 = C * ‖smoothTraceH1 Ω f‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hC]
      have hn : 0 ≤ Real.sqrt C * ‖smoothTraceH1 Ω f‖ := by positivity
      change ‖smoothTraceBoundaryLin hγ f‖ ≤ Real.sqrt C * ‖smoothTraceH1 Ω f‖
      nlinarith [norm_nonneg (smoothTraceBoundaryLin hγ f)]
    exact LinearMap.extendOfNorm_eq (denseRange_smoothTraceH1Lin hb hL) ⟨C, hC⟩ f]
  exact (smoothTraceBoundary_memLp hγ f).coeFn_toLp

/-- Pairing the actual smooth trace with a boundary density is the ordinary
coordinate boundary integral. -/
theorem h1BoundaryTrace_inner_smooth  (hb : Bornology.IsBounded Ω)
    hL  (hγ : Φ0)
    (f : smoothTraceTests) g :
    ⟪h1BoundaryTrace hb hL hγ (smoothTraceH1 Ω f), g⟫_ℂ =
      ∫ θ in Ioc 0 (2 * π), conj (f (γ θ)) * g θ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f] with θ hθ
  simp only [RCLike.inner_apply', hθ]

/-- The boundary load in the shifted H¹ variational equation is the adjoint
of the actual trace. This is the input needed to construct a genuine NtD map. -/
def h1BoundaryLoad  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hγ : Φ0) :
    BoundaryL2 →L[ℂ] NeumannH1 Ω :=
  ContinuousLinearMap.adjoint (h1BoundaryTrace hb hL hγ)

theorem h1BoundaryLoad_inner  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hγ : Φ0)
    (u : NeumannH1 Ω) g :
    ⟪u, h1BoundaryLoad hb hL hγ g⟫_ℂ = ⟪h1BoundaryTrace hb hL hγ u, g⟫_ℂ := by
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

end PolyaNeumann

end
