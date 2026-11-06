/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.Noether.FormalImplicitRoot

/-! Formal branches of plane equations at nonsingular points, in either
coordinate chart. The other coordinate is the parameter X plus its base value. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A point of the plane is recovered from its coordinate `j` and its other coordinate `j.rev`. -/
lemma plane_coordinate_cases {K : Type*} (z : Fin 2 → K) (j : Fin 2) :
    (fun k => if k = j then z j else z j.rev) = z := by
  funext k; fin_cases j <;> fin_cases k <;> simp

/-- A nonzero chosen partial derivative supplies a unique formal branch
through the given point. This works in arbitrary characteristic. -/
theorem exists_unique_formal_plane_branch {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0) (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0) :
    ∃! g : PowerSeries K, PowerSeries.constantCoeff g = z j ∧
      MvPolynomial.eval₂ PowerSeries.C
        (fun k => if k = j then g else PowerSeries.X + PowerSeries.C (z j.rev)) f = 0 := by
  /- Turn coordinate j into a polynomial variable and the other coordinate
  into the formal parameter X+a. -/
  /- `formalPlanePolynomial j a` sends variable `j` to the polynomial variable and the other
  variable to the constant polynomial with value the power series `X + a`. -/
  let φ : MvPolynomial (Fin 2) K →+* Polynomial (PowerSeries K) :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp PowerSeries.C)
      (fun k => if k = j then Polynomial.X else Polynomial.C (PowerSeries.X + PowerSeries.C (z j.rev)))
  have hX (k : Fin 2) : φ (MvPolynomial.X k) =
      if k = j then Polynomial.X else Polynomial.C (PowerSeries.X + PowerSeries.C (z j.rev)) := by
    simp [φ]
  have hconst_eval (p : MvPolynomial (Fin 2) K) :
      ((φ p).map PowerSeries.constantCoeff).eval (z j) = MvPolynomial.eval z p := by
    conv_rhs => rw [← plane_coordinate_cases z j]
    induction p using MvPolynomial.induction_on with
    | C c => simp [φ]
    | add p h hp hh => simp [map_add, hp, hh]
    | mul_X p k hp => by_cases h : k = j <;> simp [map_mul, hX, hp, h]
  have hder_eq (p : MvPolynomial (Fin 2) K) :
      (φ p).derivative = φ (MvPolynomial.pderiv j p) := by
    induction p using MvPolynomial.induction_on with
    | C c => simp [φ]
    | add p g hp hg => simp [map_add, hp, hg]
    | mul_X p k hp =>
      by_cases h : k = j
      · subst k; simp [map_mul, Polynomial.derivative_mul, hX, hp]; ring
      · simp [map_mul, Polynomial.derivative_mul, hX, hp, h]; ring
  have heval (p : MvPolynomial (Fin 2) K) (g : PowerSeries K) :
      (φ p).eval g = MvPolynomial.eval₂ PowerSeries.C
        (fun k => if k = j then g else PowerSeries.X + PowerSeries.C (z j.rev)) p := by
    induction p using MvPolynomial.induction_on with
    | C c => simp [φ]
    | add p h hp hh => simp [map_add, hp, hh]
    | mul_X p k hp => by_cases h : k = j <;> simp [map_mul, hX, hp, h]
  let F := φ f
  have hroot : (F.map PowerSeries.constantCoeff).eval (z j) = 0 := (hconst_eval f).trans hz
  have hder : (F.derivative.map PowerSeries.constantCoeff).eval (z j) ≠ 0 := by
    dsimp only [F]; rwa [hder_eq f, hconst_eval]
  obtain ⟨g, hg, hfg⟩ := exists_formal_simple_root F (z j) hroot hder
  exact ⟨g, ⟨hg, (heval f g).symm.trans hfg⟩, fun h hh =>
    formal_simple_root_unique F (z j) hder hh.1 hg ((heval f h).trans hh.2) hfg⟩

end
end CCDN
