/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
public import CCDN.Determinant.HypersurfaceLocalDeterminant
public import CCDN.Determinant.PlaneMultiplicity
import CCDN.Determinant.BlockDeterminant
import CCDN.Determinant.ProjectiveLocalDeterminant
import CCDN.ForMathlib.Matrix
import CCDN.Height.ProjectiveZeroLocus

/-!
Projective hypersurface determinants in all positive dimensions.
Unit normalization modulo prime powers transfers the local affine
bound to homogeneous evaluation matrices of a common degree.

Singular local determinant bounds at a residue point in arbitrary
dimension. Multiplicity is obtained from the first nonzero translated homogeneous
component.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Unit normalization in the first homogeneous coordinate preserves the
evaluation of a degree-M form, up to the corresponding unit row factor. -/
lemma projective_hypersurface_chart_eval_congr {n M : ℕ} {q u : ℤ}
    (z : Fin (n + 3) → ℤ) (hu : q ∣ u * z 0 - 1)
    (F : MvPolynomial (Fin (n + 3)) ℤ) (hF : F.IsHomogeneous M) :
    q ∣ eval (fun j : Fin (n + 2) => u * z j.succ) (affineChart (n + 2) F) -
      u ^ M * eval z F := by
  rw [affineChart_eval, ← homogeneous_eval_smul hF]
  apply dvd_eval_sub_of_dvd_coordinates
  intro j
  refine Fin.cases ?_ (fun _ => by simp) j
  simpa only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul, neg_sub] using dvd_neg.mpr hu

/-- Move coordinate `k` to the first position before taking the affine chart. -/
def projectiveHypersurfaceChart {n : ℕ} (k : Fin (n + 3)) (f : MvPolynomial (Fin (n + 3)) ℤ) :
    MvPolynomial (Fin (n + 2)) ℤ :=
  affineChart (n + 2) (rename (Equiv.swap 0 k) f)

/-- The local projective divisor is available in every coordinate chart. -/
theorem projective_hypersurface_local_det_divisibility {p n μ s d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin s → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin (n + 3) → ℤ) (k : Fin (n + 3)) (a : Fin (n + 2) → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a (projectiveHypersurfaceChart k f)) ∈
      idealOfVars (Fin (n + 2)) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ
      (map (Int.castRingHom (ZMod p)) (originShift a (projectiveHypersurfaceChart k f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i k))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 k j.succ) - a j * z i k)
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
      (Matrix.of fun i j => eval (z i) (F j)).det := by
  classical
  have hswap (v : Fin (n + 3) → ℤ) (g : MvPolynomial (Fin (n + 3)) ℤ) :
      eval (v ∘ Equiv.swap 0 k) (rename (Equiv.swap 0 k) g) = eval v g := by
    rw [eval_rename, show (v ∘ Equiv.swap 0 k) ∘ Equiv.swap 0 k = v by funext; simp]
  let N := hypersurfaceMultiplicityExponent (n + 1) μ s
  by_cases hN : N = 0
  · change (p : ℤ) ^ N ∣ _; simp [hN]
  let q : ℤ := (p : ℤ) ^ N
  have hpq : (p : ℤ) ∣ q := by
    simpa only [pow_one] using pow_dvd_pow (p : ℤ) (Nat.one_le_iff_ne_zero.mpr hN)
  let w : Fin s → Fin (n + 3) → ℤ := fun i => z i ∘ Equiv.swap 0 k
  choose u hu huc using fun i : Fin s => exists_integer_inverse_of_isCoprime
    (show IsCoprime q (w i 0) from (by simpa [w] using hunit i : IsCoprime (p : ℤ) (w i 0)).pow_left)
  let x : Fin s → Fin (n + 2) → ℤ := fun i j => u i * w i j.succ
  have hx (i : Fin s) (j : Fin (n + 2)) : (p : ℤ) ∣ x i j - a j := by
    rw [show x i j - a j = u i * (w i j.succ - a j * w i 0) + a j * (u i * w i 0 - 1) by
      dsimp [x]; ring]
    exact dvd_add (dvd_mul_of_dvd_right (by simpa [w] using hres i j) _)
      (dvd_mul_of_dvd_right (hpq.trans (hu i)) _)
  have hxf (i : Fin s) : q ∣ eval (x i) (projectiveHypersurfaceChart k f) := by
    simpa only [projectiveHypersurfaceChart, w, hswap, hz, mul_zero, sub_zero] using
      projective_hypersurface_chart_eval_congr (w i) (hu i)
        (rename (Equiv.swap 0 k) f) hfhom.rename_isHomogeneous
  let A := Matrix.of fun i j : Fin s =>
    eval (x i) (affineChart (n + 2) (rename (Equiv.swap 0 k) (F j)))
  let D := Matrix.of fun i j : Fin s => u i ^ M * eval (z i) (F j)
  have hA : q ∣ A.det := by
    simpa only [A, eval_sub_originShift] using
      hypersurface_pow_dvd_det_mod (originShift a (projectiveHypersurfaceChart k f))
        hf hμ (fun i j => x i j - a j) hx
        (fun i => by simpa only [eval_sub_originShift] using hxf i)
        (fun j => originShift a (affineChart (n + 2) (rename (Equiv.swap 0 k) (F j))))
  have hAD : q ∣ A.det - D.det := by
    apply Matrix.dvd_det_sub_det_of_dvd_sub
    intro i j
    dsimp only [A, D, x, Matrix.of_apply]
    simpa only [w, hswap] using
      projective_hypersurface_chart_eval_congr (w i) (hu i)
        (rename (Equiv.swap 0 k) (F j)) (hF j).rename_isHomogeneous
  have hD : q ∣ D.det := by simpa only [sub_sub_cancel] using dvd_sub hA hAD
  rw [show D.det = (∏ i, u i ^ M) * (Matrix.of fun i j => eval (z i) (F j)).det from
    Matrix.det_mul_column _ _] at hD
  exact (IsCoprime.prod_right fun i _ => (huc i).pow_right).dvd_of_dvd_mul_left hD

/-- Assemble local projective residue classes in their own coordinate charts.
Every maximal minor acquires the sum of their local multiplicity exponents. -/
theorem projective_hypersurface_residue_minorGcd {p n c s N d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin (n + 3) → ℤ) (label : Fin s → Fin c)
    (k : Fin c → Fin (n + 3)) (a : Fin c → Fin (n + 2) → ℤ) (μ : Fin c → ℕ)
    (hf : ∀ i, map (Int.castRingHom (ZMod p))
      (originShift (a i) (projectiveHypersurfaceChart (k i) f)) ∈
        idealOfVars (Fin (n + 2)) (ZMod p) ^ μ i)
    (hμ : ∀ i, homogeneousComponent (μ i) (map (Int.castRingHom (ZMod p))
      (originShift (a i) (projectiveHypersurfaceChart (k i) f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i (k (label i))))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 (k (label i)) j.succ) -
      a (label i) j * z i (k (label i)))
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ (∑ i : Fin c, hypersurfaceMultiplicityExponent (n + 1) (μ i)
      (Fintype.card {j : Fin s // label j = i})) ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  apply residue_prime_powers_dvd_minorGcd _ label
  intro i cols
  exact projective_hypersurface_local_det_divisibility f hfhom
    (fun j => F (cols j)) (fun j => hF (cols j))
    (fun j => z (residueRows label i j)) (k i) (a i) (hf i) (hμ i)
    (fun j => by simpa only [residueRows_label] using hunit (residueRows label i j))
    (fun j l => by simpa only [residueRows_label] using hres (residueRows label i j) l)
    (fun _ => hz _)

end
end CCDN
