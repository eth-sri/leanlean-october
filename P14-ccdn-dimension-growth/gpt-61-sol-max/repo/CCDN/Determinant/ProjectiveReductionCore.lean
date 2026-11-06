/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates
public import CCDN.Height.ProjectiveZeroLocus
import Mathlib

@[expose] public section
namespace CCDN
open MvPolynomial

/-- The projective space `ℙⁿ(𝔽_p)` over the prime field `𝔽_p`. -/
abbrev ProjectiveResidueSpace (n p : ℕ) [Fact p.Prime] :=
  Projectivization (ZMod p) (Fin (n + 1) → ZMod p)

variable {n p : ℕ} [Fact p.Prime]

/-- A primitive integer vector has nonzero reduction modulo every prime. -/
lemma primitive_mod_ne_zero 
    (z : IntPoint n) (hz : Finset.univ.gcd z = 1) :
    (fun i => (z i : ZMod p)) ≠ 0 := by
  intro h
  have hd : ↑p ∣ Finset.univ.gcd z := by
    apply Finset.dvd_gcd
    intro i _
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun h i)
  rw [hz] at hd
  exact have hp := Nat.prime_iff_prime_int.mp Fact.out;
  Prime.not_isUnit hp (isUnit_of_dvd_one hd)

/-- The reduction modulo `p` of a primitive integer point, as a point of `ℙⁿ(𝔽_p)`. -/
def primitiveProjectiveReduction 
    (z : IntPoint (n + 1)) (hz : Finset.univ.gcd z = 1)  :=
  Projectivization.mk (ZMod p) (fun i => (z i : ZMod p)) (primitive_mod_ne_zero z hz)

/-- Homogeneous equations remain zero at the projective reduction. -/
theorem primitiveProjectiveReduction_zero {n p d : ℕ} [Fact p.Prime]
    (f : CCDN.IntegerPolynomial (n + 1)) (hf : f.IsHomogeneous d)
    (z : IntPoint (n + 1)) (hz : Finset.univ.gcd z = 1) (hzf : eval z f = 0) :
    eval (primitiveProjectiveReduction  z hz).rep
      (map (Int.castRingHom (ZMod p)) f) = 0 := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep
    (ZMod p) (fun i => (z i : ZMod p)) (primitive_mod_ne_zero z hz)
  change eval (Projectivization.mk (ZMod p) _ _).rep _ = 0
  rw [← hu]
  change eval ((u : ZMod p) • (fun i => (z i : ZMod p))) _ = 0
  rw [homogeneous_eval_smul (hf.map _)]
  have he : eval (fun i => (z i : ZMod p)) (map (Int.castRingHom (ZMod p)) f) = 0 := by
    have h := congrArg (Int.castRingHom (ZMod p)) hzf
    rw [map_eval, map_zero] at h
    exact h
  rw [he, mul_zero]


end CCDN
