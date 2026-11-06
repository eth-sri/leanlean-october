/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import ArithmeticHeights.BombieriVaaler
public import CCDN.Algebra.OriginShift
public import CCDN.Determinant.LocalDeterminant
public import Mathlib.RingTheory.MvPolynomial.Ideal
import CCDN.Determinant.BlockDeterminant
import CCDN.Determinant.SingularLocalDeterminant

/-! Translation and residue-block assembly for the singular local
plane-curve determinant theorem. -/

public section
namespace CCDN
open MvPolynomial

variable {p μ s : ℕ} [Fact p.Prime] (f : CCDN.IntegerPolynomial 2) (F : Fin s → CCDN.IntegerPolynomial 2) (x : Fin s → CCDN.IntPoint 2) (a : CCDN.IntPoint 2) (hf : map (Int.castRingHom (ZMod p)) (originShift a f) ∈ idealOfVars (Fin 2) (ZMod p) ^ μ) (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) (originShift a f)) ≠ 0) (hx : ∀ i j, ↑p ∣ x i j - a j)

include hf hμ hx in
/-- Singular local divisibility at an arbitrary integral representative of a
residue point; multiplicity is measured on the translated reduction. -/
theorem singular_plane_chart_det_divisibility_mod 
    (hfx : ∀ i, (p : ℤ) ^ multiplicityExponent s μ ∣ eval (x i) f) :
    (p : ℤ) ^ multiplicityExponent s μ ∣
      (Matrix.of fun i j => eval (x i) (F j)).det := by
  have he (i : Fin s) (u : CCDN.IntegerPolynomial 2) :
      eval (fun j => x i j - a j) (originShift a u) = eval (x i) u := eval_sub_originShift a (x i) u
  have h := singular_plane_pow_dvd_det_mod (originShift a f) hf hμ
    (fun i j => x i j - a j) hx (fun i => by rw [he]; exact hfx i)
    (fun j => originShift a (F j))
  simpa only [he] using h


/-- Summed multiplicity exponents for arbitrary residue blocks, including
singular blocks. Each local hypothesis describes the reduced equation. -/
theorem singular_plane_residue_minorGcd {p c s N : ℕ} [Fact p.Prime]
    (f : CCDN.IntegerPolynomial 2) (F : Fin N → CCDN.IntegerPolynomial 2)
    (x : Fin s → CCDN.IntPoint 2) (label : Fin s → Fin c)
    (a : Fin c → CCDN.IntPoint 2) (μ : Fin c → ℕ)
    (hf : ∀ i, map (Int.castRingHom (ZMod p)) (originShift (a i) f) ∈
      idealOfVars (Fin 2) (ZMod p) ^ μ i)
    (hμ : ∀ i, homogeneousComponent (μ i)
      (map (Int.castRingHom (ZMod p)) (originShift (a i) f)) ≠ 0)
    (hx : ∀ i j, ↑p ∣ x i j - a (label i) j) (hfx : ∀ i, eval (x i) f = 0) :
    (p : ℤ) ^ (∑ i : Fin c, multiplicityExponent
      (Fintype.card {k : Fin s // label k = i}) (μ i)) ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (x i) (F j)) := by
  apply residue_prime_powers_dvd_minorGcd _ label
  intro i cols
  apply singular_plane_chart_det_divisibility_mod f (fun j => F (cols j))
    (fun k => x (residueRows label i k)) (a i) (hf i) (hμ i)
  · grind [residueRows_label]
  · intro k
    rw [hfx]
    exact dvd_zero _

end CCDN
