/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.HomogeneousTranslation
public import CCDN.Algebra.ScaledHomogenization
public import CCDN.AuxiliaryPolynomial.Nonmultiple
import CCDN.AuxiliaryPolynomial.ScaledAuxiliaryCount

/-! Polynomial coordinates for a translated scaled model, with exact point
transport and transport of an auxiliary nonmultiple back to the original slice. -/

@[expose] public section
namespace CCDN
open MvPolynomial

variable {n : ℕ}

/-- The integer polynomial coordinate change `(h, x₁ - a₁ h, …, xₙ - aₙ h)` from affine
coordinates to the coordinates of the translated scaled projective model. -/
noncomputable def scaledModelCoordinates  (h : ℤ) (a : CCDN.IntPoint n) :
    Fin (n + 1) → CCDN.IntegerPolynomial n :=
  Fin.cons (C h) (fun j => X j - C (a j * h))

private lemma scaledModelCoordinates_eval  (h : ℤ) (a z : CCDN.IntPoint n) :
    (fun j => eval z (scaledModelCoordinates h a j)) =
      Fin.cons h (fun j => z j - a j * h) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [scaledModelCoordinates]

/-- The translated scaled homogenization of `f`, evaluated at the scaled model coordinates of `z`,
equals `h ^ deg f * f(z)`. -/
lemma scaledModelCoordinates_model_eval  (h : ℤ) (a z : CCDN.IntPoint n)
    (f : CCDN.IntegerPolynomial n) :
    eval (fun j => eval z (scaledModelCoordinates h a j))
      (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f)) =
        h ^ f.totalDegree * eval z f := by
  simp_all [scaledModelCoordinates_eval, homogeneousTranslation_eval, Fin.cons_zero, Fin.cons_succ, sub_add_cancel, scaledHomogenize_eval]

/-- For `0 ≤ h ≤ B`, translation parameters `0 ≤ a j ≤ d` and `z` in the box of size `B ≥ 1`, all
scaled model coordinates of `z` have absolute value at most `(d + 1) * B`. -/
lemma scaledModelCoordinates_box  {B : ℝ} {d : ℕ} {h : ℤ}
    (hB : 1 ≤ B) (hh : 0 ≤ h) (hhB : ↑h ≤ B)
    (a z : CCDN.IntPoint n) (ha : ∀ j, 0 ≤ a j ∧ a j ≤ d)
    (hz : InBox z B) (j : Fin (n + 1)) :
    |(eval z (scaledModelCoordinates h a j) : ℝ)| ≤ (↑d + 1) * B := by
  have hhR : (0 : ℝ) ≤ h := by exact_mod_cast hh
  have he := congrFun (scaledModelCoordinates_eval h a z) j
  rw [he]
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [Fin.cons_zero, abs_of_nonneg hhR]
    nlinarith
  · simp only [Fin.cons_succ, Int.cast_sub, Int.cast_mul]
    have ha0 : (0 : ℝ) ≤ a k := by exact_mod_cast (ha k).1
    have had : (a k : ℝ) ≤ d := by exact_mod_cast (ha k).2
    calc
      |(z k : ℝ) - (a k : ℝ) * h| ≤ |(z k : ℝ)| + |(a k : ℝ) * h| := abs_sub _ _
      _ = |(z k : ℝ)| + (a k : ℝ) * h := by rw [abs_of_nonneg (mul_nonneg ha0 hhR)]
      _ ≤ (↑d + 1) * B := by nlinarith [hz k]

/-- A homogeneous auxiliary polynomial `g` of degree `M` not divisible by the translated scaled
homogenization of `f` transports to a homogeneous `g'` of degree `M` not divisible by the scaled
homogenization of `f`, with `g'(h, z)` equal to `g` at the scaled model coordinates of `z`. -/
lemma scaledModelCoordinates_auxiliary_transport {n M : ℕ}
    (h : ℤ) (a : CCDN.IntPoint n) (f : CCDN.IntegerPolynomial n)
    (g : CCDN.IntegerPolynomial (n + 1)) (hg : g.IsHomogeneous M)
    (hnd : ¬ homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f) ∣ g) :
    ∃ g' : CCDN.IntegerPolynomial (n + 1), g'.IsHomogeneous M ∧
      (∀ z, eval (Fin.cons h z) g' = eval (fun j => eval z (scaledModelCoordinates h a j)) g) ∧
      ¬ scaledHomogenize f.totalDegree h f ∣ g' := by
  refine ⟨homogeneousTranslation ℤ (-a) g, homogeneousTranslation_homogeneous _ hg, ?_, ?_⟩
  · simp_all [homogeneousTranslation_eval, scaledModelCoordinates_eval, Fin.cons_zero, Fin.cons_succ, Pi.neg_apply, neg_mul, sub_eq_add_neg]
  · intro hdiv
    apply hnd
    have he := map_dvd (homogeneousTranslation ℤ a).toRingHom hdiv
    change homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f) ∣
      homogeneousTranslation ℤ a ((homogeneousTranslation ℤ a).symm g) at he
    simpa only [AlgEquiv.apply_symm_apply] using he

/-- A nonmultiple on the translated scaled model counts the original
integer points. The bound uses only the auxiliary degree and original degree. -/
theorem scaled_positioned_points_card_le {M t : ℕ}
    (f : CCDN.IntegerPolynomial 2) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible (CCDN.rationalPolynomial f))
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ ↑p ∣ f.coeff 0)
    (a : CCDN.IntPoint 2) (z : Fin t → CCDN.IntPoint 2) (hinj : Function.Injective z)
    (hz : ∀ i, eval (z i) f = 0) (g : CCDN.IntegerPolynomial 3)
    (hg : IsPointAuxiliary (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree ↑p f))
      g M (fun i j => eval (z i) (scaledModelCoordinates ↑p a j))) :
    t ≤ f.totalDegree * M := by
  obtain ⟨g', hg', he, hnd'⟩ := scaledModelCoordinates_auxiliary_transport ↑p a f g
    hg.isHomogeneous hg.not_dvd
  exact scaled_plane_points_card_le_auxiliary_degree f hprim hir hp hp0 g' hg' hnd' z hinj hz fun i =>
    Eq.trans (he (z i)) (hg.eval_eq_zero i)

end CCDN
