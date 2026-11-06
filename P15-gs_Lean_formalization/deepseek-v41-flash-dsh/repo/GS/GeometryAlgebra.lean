module
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import GS.Core
public import GS.Frobenius
public import GS.Projection


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Algebra underlying tangent operations and transport

The Taylor identity is an exact polynomial identity. It is not asserted to be
a proof of existence of an embedded manifold, a quotient retraction, or of a
geodesic. These analytic obligations are separated in the coverage report.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS

variable {n : ℕ}

def tangentParam (B₂ P B₁ C Ω : Mat n) : Mat n :=
  B₂ * C * P * B₁ + B₂ * P * Ω * B₁

theorem conjugate_skew (B C : Mat n) (hC : IsSkew C) : IsSkew (B*C*Bᵀ) := by
  unfold IsSkew at *
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hC]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem tangentParam_factored (B₂ P B₁ C Ω : Mat n) (hP : Orthogonal P) :
    tangentParam B₂ P B₁ C Ω = B₂ * (C + P*Ω*Pᵀ) * (P*B₁) := by
  symm
  calc
    B₂ * (C + P*Ω*Pᵀ) * (P*B₁) =
        B₂*C*P*B₁ + B₂*P*Ω*(Pᵀ*P)*B₁ := by noncomm_ring
    _ = tangentParam B₂ P B₁ C Ω := by
      rw [hP.1]
      simp [tangentParam]

/-- Frobenius norm identity once the nonoverlap inner product is zero. -/
theorem tangentParam_frobSq (B₂ P B₁ C Ω : Mat n)
    (h₂ : Orthogonal B₂) (hP : Orthogonal P) (h₁ : Orthogonal B₁)
    (hcross : frobInner C (P*Ω*Pᵀ) = 0) :
    frobSq (tangentParam B₂ P B₁ C Ω) = frobSq C + frobSq Ω := by
  rw [tangentParam_factored _ _ _ _ _ hP]
  have hbase : frobSq (B₂*(C+P*Ω*Pᵀ)*(P*B₁)) = frobSq (C+P*Ω*Pᵀ) := by
    unfold frobSq
    rw [frobInner_right_orthogonal _ (hP.mul h₁), frobInner_left_orthogonal _ h₂]
  rw [hbase, frobSq_add, hcross]
  have hΩ : frobSq (P*Ω*Pᵀ) = frobSq Ω := by
    unfold frobSq
    rw [frobInner_right_orthogonal _ hP.transpose, frobInner_left_orthogonal _ hP]
  rw [hΩ]
  ring

def blockProjection (block : Fin n → ℕ) (A : Mat n) : Mat n :=
  mask (fun i j => block i = block j) A

/-- The outer factor normalization used in the paper's m=4 construction. -/
theorem gram_completion (C H G L W : Mat n)
    (hC : C*H*Cᵀ=G) (hL : L*Lᵀ=H) (hW : W*G*Wᵀ=1) :
    Orthogonal (W*C*L) := by
  apply Orthogonal.of_mul_transpose
  calc
    (W*C*L)*(W*C*L)ᵀ = W*(C*(L*Lᵀ)*Cᵀ)*Wᵀ := by
      simp only [Matrix.transpose_mul,Matrix.mul_assoc]
    _ = 1 := by rw [hL,hC,hW]

end GS
