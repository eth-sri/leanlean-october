module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import PDEFoundation.Ambient.Basis
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.Ring



/-!
# Raw spatial difference quotients

This module records the algebra, smoothness, and support transport of forward
translations in one native velocity coordinate. It deliberately makes no
domain, equation, or nonzero-increment assumption.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- Translation by `h` in the `k`th native velocity coordinate, fixing time. -/
def spatialShift {d : ℕ} (k : Fin d) (h : ℝ) :
    TimeVelocity d → TimeVelocity d :=
  fun z => z + (0, h • PDE.basisVec k)

variable {d : ℕ}

/-- Precomposition by the forward spatial translation. -/
def spatialTranslate  {α : Type*} (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) : TimeVelocity d → α :=
  fun z => f (spatialShift k h z)

variable (k : Fin d)

/-- The forward spatial difference quotient, totalized at zero increment. -/
noncomputable def spatialDifferenceQuotient   (h : ℝ)
    (f : HypoellipticAleksandrov.Parabolic.ScalarField d) : HypoellipticAleksandrov.Parabolic.ScalarField d :=
  fun z => (spatialTranslate k h f z - f z) / h

/-- A spatial shift changes only the selected native velocity coordinate. -/
@[simp] theorem spatialShift_apply
      (h r : ℝ) (y : PDE.Vec d) :
    spatialShift k h (r, y) = (r, y + h • PDE.basisVec k) := by
  simp [spatialShift]

/-- A spatial translate evaluates at the corresponding shifted point. -/
@[simp] theorem spatialTranslate_apply
     {α : Type*} (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) (z : TimeVelocity d) :
    spatialTranslate k h f z = f (spatialShift k h z) :=
  rfl

variable (k : Fin d)

/-- A spatial difference quotient has its literal pointwise value. -/
@[simp] theorem spatialDifferenceQuotient_apply
      (h : ℝ) (f : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (z : TimeVelocity d) :
    spatialDifferenceQuotient k h f z =
      (spatialTranslate k h f z - f z) / h :=
  rfl

/-- A zero spatial shift is the identity. -/
@[simp] theorem spatialShift_zero   :
    spatialShift k 0 = id := by
  funext z
  rcases z with ⟨r, y⟩
  simp [spatialShift]

/-- Successive shifts in one coordinate add their increments. -/
theorem spatialShift_comp   (h₁ h₂ : ℝ) :
    spatialShift k h₂ ∘ spatialShift k h₁ =
      spatialShift k (h₁ + h₂) := by
  funext z
  rcases z with ⟨r, y⟩
  simp [spatialShift, add_smul, add_assoc]

variable {α : Type*}



/-- Spatial translation preserves pointwise negation. -/
theorem spatialTranslate_neg
      [Neg α] (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) :
    spatialTranslate k h (-f) = -spatialTranslate k h f :=
  rfl

/-- Spatial difference quotients preserve negation. -/
theorem spatialDifferenceQuotient_neg
     (k : Fin d) (h : ℝ) (f : HypoellipticAleksandrov.Parabolic.ScalarField d) :
    spatialDifferenceQuotient k h (-f) =
      -spatialDifferenceQuotient k h f := by
  ext <;> simp_all [spatialDifferenceQuotient_apply, spatialTranslate_apply] <;> ring

/-- Global continuous differentiability is preserved by spatial translation. -/
theorem ContDiff.spatialTranslate
     {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {k : Fin d} {h : ℝ} {f : TimeVelocity d → E}
    (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (spatialTranslate k h f) := (id (ContDiff.comp hf (ContDiff.add contDiff_id contDiff_const)))

/-- Global continuous differentiability is preserved by spatial difference quotients. -/
theorem ContDiff.spatialDifferenceQuotient
     {n : ℕ∞} {k : Fin d} {h : ℝ}
    {f : HypoellipticAleksandrov.Parabolic.ScalarField d} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (spatialDifferenceQuotient k h f) := (id (ContDiff.div_const (ContDiff.sub (spatialTranslate hf) hf) h))

variable {α : Type*}

/-- Spatial translation pulls topological support back exactly by the shift. -/
theorem tsupport_spatialTranslate
      [Zero α] (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) :
    tsupport (spatialTranslate k h f) =
      (spatialShift k h) ⁻¹' tsupport f := (id (tsupport_comp_eq_preimage f (Homeomorph.addRight (0, h • PDE.basisVec k))))

/-- Translated-support membership is support membership after shifting. -/
theorem mem_tsupport_spatialTranslate_iff
      [Zero α] (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) (z : TimeVelocity d) :
    z ∈ tsupport (spatialTranslate k h f) ↔
      spatialShift k h z ∈ tsupport f := by
  rw [tsupport_spatialTranslate]
  rfl

end HypoellipticAleksandrov.Parabolic
