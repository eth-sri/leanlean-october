module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import PDEFoundation.Ambient.Basis
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Support

/-!
# Raw spatial difference quotients

This module records the algebra, smoothness, and support transport of forward
translations in one native velocity coordinate. It deliberately makes no
domain, equation, or nonzero-increment assumption.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

section
variable {d : ℕ}

/-- Translation by `h` in the `k`th native velocity coordinate, fixing time. -/
def spatialShift (k : Fin d) (h : ℝ) :
    TimeVelocity d → TimeVelocity d :=
  fun z => z + (0, h • PDE.basisVec k)

/-- Precomposition by the forward spatial translation. -/
def spatialTranslate {α : Type*} (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) : TimeVelocity d → α :=
  fun z => f (spatialShift k h z)

/-- The forward spatial difference quotient, totalized at zero increment. -/
noncomputable def spatialDifferenceQuotient (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → ℝ) : TimeVelocity d → ℝ :=
  fun z => (spatialTranslate k h f z - f z) / h

/-- A spatial shift changes only the selected native velocity coordinate. -/
@[simp] theorem spatialShift_apply (k : Fin d) (h r : ℝ) (y : PDE.Vec d) :
    spatialShift k h (r, y) = (r, y + h • PDE.basisVec k) := by
  simp [spatialShift]

/-- A spatial translate evaluates at the corresponding shifted point. -/
@[simp] theorem spatialTranslate_apply {α : Type*} (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) (z : TimeVelocity d) :
    spatialTranslate k h f z = f (spatialShift k h z) :=
  rfl

/-- A spatial difference quotient has its literal pointwise value. -/
@[simp] theorem spatialDifferenceQuotient_apply (k : Fin d) (h : ℝ) (f : TimeVelocity d → ℝ)
    (z : TimeVelocity d) :
    spatialDifferenceQuotient k h f z =
      (spatialTranslate k h f z - f z) / h :=
  rfl

end

section
variable {d : ℕ}

section
variable (k : Fin d)

/-- The spatial quotient as a scaled difference, with no nonzero-step assumption. -/
theorem spatialDifferenceQuotient_eq_smul (h : ℝ) (f : TimeVelocity d → ℝ) :
    spatialDifferenceQuotient k h f = h⁻¹ • (spatialTranslate k h f - f) := by
  funext z
  simp only [spatialDifferenceQuotient_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

/-- A zero spatial shift is the identity. -/
@[simp] theorem spatialShift_zero :
    spatialShift k 0 = id := by
  funext z
  rcases z with ⟨r, y⟩
  simp [spatialShift]

/-- Successive shifts in one coordinate add their increments. -/
theorem spatialShift_comp (h₁ h₂ : ℝ) :
    spatialShift k h₂ ∘ spatialShift k h₁ =
      spatialShift k (h₁ + h₂) := by
  funext z
  rcases z with ⟨r, y⟩
  simp [spatialShift, add_smul, add_assoc]

end

/-- Translation by zero fixes every function. -/
@[simp] theorem spatialTranslate_zero {α : Type*} (k : Fin d) (f : TimeVelocity d → α) :
    spatialTranslate k 0 f = f := by
  funext z
  simp [spatialTranslate]

/-- Global continuous differentiability is preserved by spatial translation. -/
theorem ContDiff.spatialTranslate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {k : Fin d} {h : ℝ} {f : TimeVelocity d → E}
    (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (spatialTranslate k h f) := by
  exact hf.comp (contDiff_id.add contDiff_const)

end

/-- Global continuous differentiability is preserved by spatial difference quotients. -/
theorem ContDiff.spatialDifferenceQuotient
    {d : ℕ} {n : ℕ∞} {k : Fin d} {h : ℝ}
    {f : TimeVelocity d → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (spatialDifferenceQuotient k h f) := by
  exact (ContDiff.spatialTranslate hf |>.sub hf).div_const h

section
variable {d : ℕ} {α : Type*}

/-- Spatial translation pulls topological support back exactly by the shift. -/
theorem tsupport_spatialTranslate [Zero α] (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) :
    tsupport (spatialTranslate k h f) =
      (spatialShift k h) ⁻¹' tsupport f := by
  exact id (tsupport_comp_eq_preimage f (Homeomorph.addRight (0, h • PDE.basisVec k)))

/-- Translated-support membership is support membership after shifting. -/
theorem mem_tsupport_spatialTranslate_iff [Zero α] (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) (z : TimeVelocity d) :
    z ∈ tsupport (spatialTranslate k h f) ↔
      spatialShift k h z ∈ tsupport f := by
  rw [tsupport_spatialTranslate]
  rfl

end

end HypoellipticAleksandrov.Parabolic
