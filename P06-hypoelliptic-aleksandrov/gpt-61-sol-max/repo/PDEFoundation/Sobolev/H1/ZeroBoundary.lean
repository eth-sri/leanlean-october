module

public import PDEFoundation.Sobolev.H1.Graph
public import PDEFoundation.Sobolev.W1p.ZeroBoundary
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Zero-boundary `H¹` graph

This file is the `p = 2` facade for the canonical zero-boundary graph from
`PDEFoundation.Sobolev.W1p.ZeroBoundary`.  In particular, `H10Graph hU` is
definitionally the closure in `H1Graph U` of the range of actual bundled
smooth compactly supported test functions.  No second weak-gradient relation
or boundary-condition predicate is introduced here.

For compatibility with `LeanIntoHomogenization`, the file also exposes its
representative-level `H10Function` field surface.  That structure merely
bundles an `H1Function` with the same supported smooth approximation
certificate used to enter the closed graph.

## Main definitions

- `H10Function`: the LIH-compatible representative facade.
- `MemH10`: concrete-function membership through that facade.
- `h10GraphClosedSubmodule`: the closed `H¹₀` submodule of `H1Graph U`.
- `H10Graph`: its complete carrier.
- `H1Function.SupportedSmoothApproximation`: the exact representative-level
  `p = 2` specialization of the generic certificate.

## Main results

- `H1Function.mem_h10Graph_of_supportedSmoothApproximation` sends an explicit
  supported approximation to the complete carrier.
- `H10Graph.exists_tendsto_smooth` supplies actual bundled test functions
  converging to every point of the complete carrier.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter

variable {d : ℕ} {U : Set (Vec d)}

/-- A representative-level `H¹₀(U)` witness with the exact field surface used
by `LeanIntoHomogenization`.

The additional fields are precisely a supported smooth approximation
certificate for `toH1Function`; they do not define a second boundary
condition. -/
structure H10Function {d : ℕ} (U : Set (Vec d)) extends H1Function U where
  approx : ℕ → Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ PDE.smoothOrder (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx :
    Filter.Tendsto
      (fun n =>
        MeasureTheory.eLpNorm
          (fun x => approx n x - toH1Function.toFun x)
          (2 ) (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0)
  tendsto_approx_grad :
    ∀ i : Fin d,
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ (approx n) x) (basisVec i) -
                toH1Function.grad x i)
            (2 ) (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0)

instance : CoeFun (H10Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toH1Function.toFun

/-- Representative-level membership of a concrete function in `H¹₀(U)`.
This is the LIH-compatible existential wrapper around `H10Function`. -/
def MemH10 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∃ v : H10Function U, v.toH1Function.toFun = u

/-- The canonical closed `H¹₀(U)` submodule, definitionally inherited from
the generic `W¹,p` zero-boundary construction at `p = 2`. -/
noncomputable abbrev h10GraphClosedSubmodule (hU : IsOpen U) :
    ClosedSubmodule ℝ (H1Graph U) :=
  w10pGraphClosedSubmodule  hU

/-- The canonical complete quotient-level `H¹₀(U)` carrier. -/
noncomputable abbrev H10Graph (hU : IsOpen U) :=
  W10pGraph (p := (2 )) hU

/-- The `H¹` graph point associated to an actual bundled smooth compactly
supported test function. -/
noncomputable abbrev smoothCompactlySupportedH1Graph (hU : IsOpen U)
    (φ : WeakTestFunction U) : H1Graph U :=
  smoothCompactlySupportedW1pGraph  hU φ

/-- The actual smooth test-function image belongs to the canonical
zero-boundary `H¹` graph. -/
theorem smoothCompactlySupportedH1Graph_mem_h10Graph
    (hU : IsOpen U) (φ : WeakTestFunction U) :
    smoothCompactlySupportedH1Graph hU φ ∈
      (h10GraphClosedSubmodule hU).toSubmodule :=
  smoothCompactlySupportedW1pGraph_mem_w10pGraph  hU φ

namespace H1Function

variable {u : H1Function U}

/-- Explicit supported smooth approximation data for an `H1Function`,
definitionally the generic `W¹,2` certificate. -/
abbrev SupportedSmoothApproximation (u : H1Function U) : Type :=
  W1pFunction.SupportedSmoothApproximation u.toW1pFunction

section
variable (u : H1Function U) (happrox : u.SupportedSmoothApproximation)

/-- Bundle an `H1Function` with an explicit supported smooth approximation.
This is the representative facade constructor; it adds no data beyond the
certificate. -/
def toH10Function  : H10Function U where
  toH1Function := u
  approx := happrox.approx
  approx_smooth := happrox.approx_smooth
  approx_hasCompactSupport := happrox.approx_hasCompactSupport
  approx_support_subset := happrox.approx_tsupport_subset
  tendsto_approx := happrox.tendsto_value
  tendsto_approx_grad := happrox.tendsto_grad


end


/-- Regard a member of an `H¹` supported approximation as an actual bundled
smooth compactly supported test function. -/
noncomputable abbrev SupportedSmoothApproximation.toWeakTestFunction
    (happrox : u.SupportedSmoothApproximation) (n : ℕ) : WeakTestFunction U :=
  W1pFunction.SupportedSmoothApproximation.toWeakTestFunction happrox n

/-- An explicit supported smooth approximation puts the representative's
graph image in the canonical complete `H¹₀` carrier. -/
theorem mem_h10Graph_of_supportedSmoothApproximation
    (hU : IsOpen U) (u : H1Function U)
    (happrox : u.SupportedSmoothApproximation) :
    u.toW1pFunction.toW1pGraph ∈ (h10GraphClosedSubmodule hU).toSubmodule :=
  u.toW1pFunction.mem_w10pGraph_of_supportedSmoothApproximation hU happrox

end H1Function

namespace H10Function

variable {u : H10Function U}



variable (u : H10Function U)

/-- Recover the exact supported smooth approximation certificate bundled by an
`H10Function`. -/
def supportedSmoothApproximation  :
    u.toH1Function.SupportedSmoothApproximation where
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_tsupport_subset := u.approx_support_subset
  tendsto_value := u.tendsto_approx
  tendsto_grad := u.tendsto_approx_grad







variable (hU : IsOpen U)

variable (u : H10Function U)

/-- The graph image of an `H10Function` belongs to the same canonical closed
`H10Graph` used by the quotient-level API. -/
theorem mem_h10Graph   :
    u.toH1Function.toW1pFunction.toW1pGraph ∈
      (h10GraphClosedSubmodule hU).toSubmodule :=
  u.toH1Function.mem_h10Graph_of_supportedSmoothApproximation
    hU u.supportedSmoothApproximation

/-- Send a representative-level `H10Function` to its canonical complete graph
point. -/
noncomputable def toH10Graph   :
    H10Graph hU :=
  ⟨u.toH1Function.toW1pFunction.toW1pGraph, u.mem_h10Graph hU⟩

@[simp]
theorem coe_toH10Graph   :
    (u.toH10Graph hU : H1Graph U) =
      u.toH1Function.toW1pFunction.toW1pGraph :=
  rfl

variable {f : Vec d → ℝ} (hf : ContDiff ℝ PDE.smoothOrder f) (hcompact : HasCompactSupport f) (hsub : tsupport f ⊆ U)

/-- Package a globally smooth compactly supported function as an
LIH-compatible representative-level `H¹₀` test.

The underlying `H1Function` is the existing `W1pFunction.ofContDiff`
constructor at `p = 2`; the constant approximation sequence is only its
supported-smooth certificate. -/
noncomputable def ofContDiff
     :
    H10Function U where
  toH1Function :=
    (W1pFunction.ofContDiff hU (hf.of_le (by simp)) hcompact
      (2 )).toH1Function
  approx := fun _ => f
  approx_smooth := fun _ => hf
  approx_hasCompactSupport := fun _ => hcompact
  approx_support_subset := fun _ => hsub
  tendsto_approx := by
    simpa only [W1pFunction.ofContDiff, W1pFunction.toH1Function_toFun,
      sub_self, MeasureTheory.eLpNorm_fun_zero] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  tendsto_approx_grad := by
    intro i
    simpa only [W1pFunction.ofContDiff, W1pFunction.toH1Function_grad,
      sub_self, MeasureTheory.eLpNorm_fun_zero] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))







end H10Function



namespace H10Graph

/-- Every complete `H¹₀` graph point is a limit of actual bundled smooth
compactly supported test functions. -/
theorem exists_tendsto_smooth (hU : IsOpen U) (u : H10Graph hU) :
    ∃ φ : ℕ → WeakTestFunction U,
      Tendsto (fun n => smoothCompactlySupportedH1Graph hU (φ n))
        atTop (𝓝 (u : H1Graph U)) :=
  W10pGraph.exists_tendsto_smooth  hU u

end H10Graph

end PDE
