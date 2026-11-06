module

public import Expdb.Basic.Asymptotics
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Expdb.Basic.AutomaticUniformity
import Expdb.Mathlib.IteratedDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Phase functions

This module formalizes the phase function definitions from the blueprint's Exponential sum growth
exponents chapter (`beta-chapter`).
A phase function is smooth on `[1, 2]`. A model phase function is a variable family
of phase functions whose successive derivatives asymptotically agree with those of
`u ↦ u ^ (-σ)` for some fixed positive exponent `σ`.
-/

@[expose] public section

open Filter Topology
open scoped ContDiff

noncomputable section

namespace Expdb

/-- The interval on which phase functions are considered. -/
def phaseInterval : Set ℝ := Set.Icc 1 2

/-- A phase function is a variable real-valued function that is smooth on `[1, 2]` at every
ambient index. -/
def IsPhaseFunction (F : VariableFunction (VariableObject.fixed ℝ) ℝ) : Prop :=
  ∀ i : ℕ, ContDiffOn ℝ ∞ (F i) phaseInterval

/-- The reference phase `u ↦ u ^ (-σ)` whose derivatives a model phase follows. -/
def modelPhase (σ : ℝ) : ℝ → ℝ := fun u ↦ u ^ (-σ)

/-- The fixed-data model-phase error at derivative order `p`. -/
def modelPhaseErrorAt (F : ℝ → ℝ) (σ : ℝ) (p : ℕ) (u : ℝ) : ℝ :=
  iteratedDerivWithin (p + 1) F phaseInterval u -
    iteratedDerivWithin p (modelPhase σ) phaseInterval u

/-- The variable error function in the model phase condition at derivative order `p`. -/
def modelPhaseError
    (F : VariableFunction (VariableObject.fixed ℝ) ℝ) (σ : ℝ) (p : ℕ) :
    VariableFunction (VariableObject.fixed phaseInterval) ℝ :=
  fun i u ↦ modelPhaseErrorAt (F i) σ p u

@[simp] theorem modelPhaseError_apply
    (F : VariableFunction (VariableObject.fixed ℝ) ℝ) (σ : ℝ) (p i : ℕ)
    (u : phaseInterval) :
    modelPhaseError F σ p i u = modelPhaseErrorAt (F i) σ p u :=
  rfl

/-- The phase interval has unique derivatives. -/
theorem uniqueDiffOn_phaseInterval : UniqueDiffOn ℝ phaseInterval :=
  uniqueDiffOn_Icc (by norm_num [phaseInterval])

/-- Every reference model phase is smooth on the phase interval. -/
theorem contDiffOn_modelPhase (σ : ℝ) :
    ContDiffOn ℝ ∞ (modelPhase σ) phaseInterval := by
  intro u hu
  exact (Real.contDiffAt_rpow_const_of_ne
    (ne_of_gt (zero_lt_one.trans_le hu.1))).contDiffWithinAt

/-- The derivatives of the reference model phase have the expected falling-factorial
formula on the phase interval. -/
theorem iteratedDerivWithin_modelPhase (σ : ℝ) (p : ℕ) {u : ℝ}
    (hu : u ∈ phaseInterval) :
    iteratedDerivWithin p (modelPhase σ) phaseInterval u =
      (descPochhammer ℝ p).eval (-σ) * u ^ (-σ - p) := by
  have hu0 : u ≠ 0 := ne_of_gt (zero_lt_one.trans_le hu.1)
  have hsmooth : ContDiffAt ℝ p (modelPhase σ) u := by
    change ContDiffAt ℝ p (fun x : ℝ ↦ x ^ (-σ)) u
    exact Real.contDiffAt_rpow_const_of_ne hu0
  rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hsmooth hu,
    iteratedDeriv_eq_iterate]
  exact Real.iter_deriv_rpow_const (-σ) u p

/-- On `[1, 2]`, the falling-factorial coefficient bounds the corresponding derivative
of a model phase with nonnegative exponent. -/
theorem norm_iteratedDerivWithin_modelPhase_le {σ : ℝ} (hσ : 0 ≤ σ) (p : ℕ)
    {u : ℝ} (hu : u ∈ phaseInterval) :
    ‖iteratedDerivWithin p (modelPhase σ) phaseInterval u‖ ≤
      ‖(descPochhammer ℝ p).eval (-σ)‖ := by
  rw [iteratedDerivWithin_modelPhase σ p hu, norm_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hu.1) _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.rpow_le_one_of_one_le_of_nonpos hu.1 (by
      have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
      linarith))
    (norm_nonneg ((descPochhammer ℝ p).eval (-σ)))

/-- The iterated derivatives of a reference model phase vary continuously on the phase
interval. -/
theorem continuousOn_iteratedDerivWithin_modelPhase (σ : ℝ) (p : ℕ) :
    ContinuousOn (iteratedDerivWithin p (modelPhase σ) phaseInterval) phaseInterval :=
  (contDiffOn_modelPhase σ).continuousOn_iteratedDerivWithin
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl p) uniqueDiffOn_phaseInterval

/-- A fixed phase function whose model-phase errors through order `P` are at most `δ`. -/
def IsApproximateModelPhaseFunction
    (F : ℝ → ℝ) (σ : ℝ) (P : ℕ) (δ : ℝ) : Prop :=
  ContDiffOn ℝ ∞ F phaseInterval ∧
    ∀ p : ℕ, p ≤ P → ∀ u : phaseInterval,
      ‖modelPhaseErrorAt F σ p u‖ ≤ δ

/-- The derivatives of orders `1, …, n` of `F` are bounded by `K` on the phase interval. -/
def HasPhaseDerivBound (F : ℝ → ℝ) (n : ℕ) (K : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ n → ∀ u ∈ phaseInterval,
    ‖iteratedDerivWithin k F phaseInterval u‖ ≤ K

/-- A derivative bound may be restricted to a smaller order. -/
theorem HasPhaseDerivBound.of_le {F : ℝ → ℝ} {m n : ℕ} {K : ℝ}
    (hF : HasPhaseDerivBound F n K) (hmn : m ≤ n) :
    HasPhaseDerivBound F m K :=
  fun k hk hkm u hu ↦ hF k hk (hkm.trans hmn) u hu

/-- The data defining a model phase when its reference exponent `σ` has already been fixed. -/
structure IsModelPhaseFunctionWith
    (F : VariableFunction (VariableObject.fixed ℝ) ℝ) (σ : ℝ) : Prop where
  /-- Every member of the family is smooth on the phase interval. -/
  isPhaseFunction : IsPhaseFunction F
  /-- Every fixed-order model-phase error is choicewise infinitesimal. -/
  error_isChoicewiseInfinitesimal :
    ∀ p : ℕ, (modelPhaseError F σ p).IsChoicewiseInfinitesimal

/-- A variable phase function is a model phase function when, for some fixed `σ > 0`,
the error between its `(p + 1)`st derivative and the `p`th derivative of `u ↦ u ^ (-σ)` is
choicewise infinitesimal for every fixed derivative order `p`. -/
def IsModelPhaseFunction (F : VariableFunction (VariableObject.fixed ℝ) ℝ) : Prop :=
  IsPhaseFunction F ∧
    ∃ σ : ℝ, 0 < σ ∧
      ∀ p : ℕ, (modelPhaseError F σ p).IsChoicewiseInfinitesimal

/-- At every fixed finite order, fixed-exponent model-phase data is eventually a uniformly
approximate model phase. -/
theorem IsModelPhaseFunctionWith.eventually_isApproximate
    {F : VariableFunction (VariableObject.fixed ℝ) ℝ} {σ : ℝ}
    (hF : IsModelPhaseFunctionWith F σ) (P : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ i in atTop, IsApproximateModelPhaseFunction (F i) σ P δ := by
  have hp : ∀ p ∈ Finset.range (P + 1), ∀ᶠ i in atTop,
      ∀ u : phaseInterval, ‖modelPhaseError F σ p i u‖ < δ :=
    fun p _ ↦
      (VariableFunction.isChoicewiseInfinitesimal_iff_forall_pos_uniform
        (VariableObject.fixed phaseInterval)
        (fun _ ↦ ⟨1, by simp [phaseInterval]⟩)
        (modelPhaseError F σ p)).1
        (hF.error_isChoicewiseInfinitesimal p) δ hδ
  have hall :
      ∀ᶠ i in atTop, ∀ p ∈ Finset.range (P + 1),
        ∀ u : phaseInterval, ‖modelPhaseError F σ p i u‖ < δ :=
    (Finset.range (P + 1)).eventually_all.mpr hp
  filter_upwards [hall] with i hi
  refine ⟨hF.isPhaseFunction i, ?_⟩
  intro p hp' u
  exact (hi p (Finset.mem_range.mpr (by omega)) u).le

end Expdb
