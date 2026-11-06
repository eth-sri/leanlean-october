module

public import GS.GlobalGeometry.ExactSharing

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The constrained adjoint and coupled normal equations for actual sharing

The parameter spaces here are the supported skew matrices with the concrete
entry equalities of `TiedEntries`.  The adjoint is projected separately into
these two spaces.  In particular, overlap contributes the conjugated cross
terms to the normal operator; no independent averaging rule is used.

The normal equations below are equivalent to least-squares optimality, and
always have a solution.  Their synthesized matrix is unique even when the
factor generators have a nontrivial kernel.  This file makes no manifold or
local factor-lifting assertion.
-/

noncomputable section
open Matrix GS GS.Extensions
namespace GS.GlobalGeometry
variable {n : ℕ}

/-- Frobenius metric on the two expanded physical generator matrices. -/
def sharedPairInner (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (u v : sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) : ℝ :=
  frobInner u.1.val v.1.val + frobInner u.2.val v.2.val

theorem sharedPairInner_self_eq_zero_iff (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ)
    (v : sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) :
    sharedPairInner b₁ b₂ τ₁ τ₂ v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    change frobSq v.1.val + frobSq v.2.val = 0 at h
    have h₁ : frobSq v.1.val = 0 := by
      linarith [frobSq_nonneg v.1.val, frobSq_nonneg v.2.val]
    have h₂ : frobSq v.2.val = 0 := by
      linarith [frobSq_nonneg v.1.val, frobSq_nonneg v.2.val]
    apply Prod.ext <;> apply Subtype.ext
    · exact (frobSq_eq_zero_iff _).mp h₁
    · exact (frobSq_eq_zero_iff _).mp h₂
  · rintro rfl
    simp [sharedPairInner]

end GS.GlobalGeometry
