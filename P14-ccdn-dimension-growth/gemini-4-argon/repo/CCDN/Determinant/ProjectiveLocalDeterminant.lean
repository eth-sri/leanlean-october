/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
public import CCDN.Determinant.SingularPlaneChart
import CCDN.Determinant.BlockDeterminant
import CCDN.ForMathlib.Matrix
import CCDN.Height.ProjectiveZeroLocus

/-! Local divisibility for homogeneous evaluation matrices at projective
points. Normalize a unit coordinate modulo the required prime power,
apply the singular affine estimate to the resulting approximate zeros,
then cancel the invertible row factors. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- If `x ≡ y` coordinatewise modulo `q`, then `f(x) ≡ f(y)` modulo `q` for every integer polynomial
`f`. -/
lemma dvd_eval_sub_of_dvd_coordinates {σ : Type*} (q : ℤ)
    (x y : σ → ℤ) (hxy : ∀ j, q ∣ x j - y j) (f : MvPolynomial σ ℤ) :
    q ∣ eval x f - eval y f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simpa only [eval_add, add_sub_add_comm] using dvd_add hf hg
  | mul_X f j hf =>
    rw [eval_mul, eval_mul, eval_X, eval_X,
      show eval x f * x j - eval y f * y j =
        (eval x f - eval y f) * x j + eval y f * (x j - y j) by ring]
    exact dvd_add (dvd_mul_of_dvd_left hf _) (dvd_mul_of_dvd_right (hxy j) _)

/-- An integer `a` coprime to `q` has an inverse `u` modulo `q`, itself coprime to `q`. -/
lemma exists_integer_inverse_of_isCoprime {q a : ℤ} (h : IsCoprime q a) :
    ∃ u : ℤ, q ∣ u * a - 1 ∧ IsCoprime q u := by
  obtain ⟨v, u, he⟩ := h
  exact ⟨u, ⟨-v, by linear_combination he⟩, v, a, by simpa only [mul_comm a u] using he⟩

/-- Move coordinate `k` to the first position before taking the affine chart. -/
def projectivePlaneChart (k : Fin 3) (f : MvPolynomial (Fin 3) ℤ) :
    MvPolynomial (Fin 2) ℤ :=
  affineChart 2 (rename (Equiv.swap 0 k) f)

/-- Assemble local projective residue classes in their own coordinate charts.
Every maximal minor acquires the sum of their local multiplicity exponents. -/
theorem projective_plane_residue_minorGcd {p c s N d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin N → MvPolynomial (Fin 3) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin 3 → ℤ) (label : Fin s → Fin c)
    (k : Fin c → Fin 3) (a : Fin c → Fin 2 → ℤ) (μ : Fin c → ℕ)
    (hf : ∀ i, map (Int.castRingHom (ZMod p))
      (originShift (a i) (projectivePlaneChart (k i) f)) ∈
        idealOfVars (Fin 2) (ZMod p) ^ μ i)
    (hμ : ∀ i, homogeneousComponent (μ i) (map (Int.castRingHom (ZMod p))
      (originShift (a i) (projectivePlaneChart (k i) f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i (k (label i))))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 (k (label i)) j.succ) -
      a (label i) j * z i (k (label i)))
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ (∑ i : Fin c, multiplicityExponent
      (Fintype.card {j : Fin s // label j = i}) (μ i)) ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  classical
  have hcongr {D : ℕ} {q u : ℤ} (y : Fin 3 → ℤ) (hu : q ∣ u * y 0 - 1)
      (G : MvPolynomial (Fin 3) ℤ) (hG : G.IsHomogeneous D) :
      q ∣ eval (fun j : Fin 2 => u * y j.succ) (affineChart 2 G) - u ^ D * eval y G := by
    rw [affineChart_eval, ← homogeneous_eval_smul hG]
    refine dvd_eval_sub_of_dvd_coordinates _ _ _ (fun j => Fin.cases ?_ (fun _ => by simp) j) _
    simpa only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul, neg_sub] using dvd_neg.mpr hu
  have hswap (r : Fin 3) (y : Fin 3 → ℤ) (G : MvPolynomial (Fin 3) ℤ) :
      eval (y ∘ Equiv.swap 0 r) (rename (Equiv.swap 0 r) G) = eval y G := by
    rw [eval_rename, show (y ∘ Equiv.swap 0 r) ∘ Equiv.swap 0 r = y by funext; simp]
  apply residue_prime_powers_dvd_minorGcd _ label
  intro l cols
  let s' := Fintype.card {j : Fin s // label j = l}
  let E := multiplicityExponent s' (μ l)
  by_cases hE : E = 0
  · change (p : ℤ) ^ E ∣ _; simp [hE]
  let q : ℤ := (p : ℤ) ^ E
  have hpq : (p : ℤ) ∣ q := by
    simpa only [pow_one] using pow_dvd_pow (p : ℤ) (Nat.one_le_iff_ne_zero.mpr hE)
  let w : Fin s' → Fin 3 → ℤ := fun i => z (residueRows label l i) ∘ Equiv.swap 0 (k l)
  choose u hu huc using fun i : Fin s' => exists_integer_inverse_of_isCoprime
    (show IsCoprime q (w i 0) from (by
      simpa only [w, Function.comp_apply, Equiv.swap_apply_left, residueRows_label] using
        hunit (residueRows label l i) : IsCoprime (p : ℤ) (w i 0)).pow_left)
  let x : Fin s' → Fin 2 → ℤ := fun i j => u i * w i j.succ
  have hx (i : Fin s') (j : Fin 2) : (p : ℤ) ∣ x i j - a l j := by
    rw [show x i j - a l j = u i * (w i j.succ - a l j * w i 0) + a l j * (u i * w i 0 - 1) by
      dsimp [x]; ring]
    exact dvd_add (dvd_mul_of_dvd_right (by
      simpa only [w, Function.comp_apply, Equiv.swap_apply_left, residueRows_label] using
        hres (residueRows label l i) j) _)
      (dvd_mul_of_dvd_right (hpq.trans (hu i)) _)
  have hxf (i : Fin s') : q ∣ eval (x i) (projectivePlaneChart (k l) f) := by
    have h := hcongr (w i) (hu i) (rename (Equiv.swap 0 (k l)) f) hfhom.rename_isHomogeneous
    simpa only [projectivePlaneChart, w, hswap, hz, mul_zero, sub_zero] using h
  let A := Matrix.of fun i j : Fin s' =>
    eval (x i) (affineChart 2 (rename (Equiv.swap 0 (k l)) (F (cols j))))
  let D := Matrix.of fun i j : Fin s' => u i ^ M * eval (z (residueRows label l i)) (F (cols j))
  have hA : q ∣ A.det :=
    singular_plane_chart_det_divisibility_mod (projectivePlaneChart (k l) f)
      (fun j => affineChart 2 (rename (Equiv.swap 0 (k l)) (F (cols j)))) x (a l)
      (hf l) (hμ l) hx hxf
  have hAD : q ∣ A.det - D.det := by
    apply Matrix.dvd_det_sub_det_of_dvd_sub
    intro i j
    dsimp only [A, D, x, Matrix.of_apply]
    simpa only [w, hswap] using hcongr (w i) (hu i)
      (rename (Equiv.swap 0 (k l)) (F (cols j))) (hF (cols j)).rename_isHomogeneous
  have hD : q ∣ D.det := by simpa only [sub_sub_cancel] using dvd_sub hA hAD
  rw [show D.det = (∏ i, u i ^ M) *
    (Matrix.of fun i j => eval (z (residueRows label l i)) (F (cols j))).det from
      Matrix.det_mul_column _ _] at hD
  exact (IsCoprime.prod_right fun i _ => (huc i).pow_right).dvd_of_dvd_mul_left hD

end
end CCDN
