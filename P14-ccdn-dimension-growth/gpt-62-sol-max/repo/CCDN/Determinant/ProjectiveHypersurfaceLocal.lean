/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
public import CCDN.Determinant.HypersurfaceLocalDeterminant
public import CCDN.Determinant.PlaneMultiplicity
public import CCDN.Determinant.BlockDeterminant
import CCDN.ForMathlib.MvPolynomial
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

/-- An integer `a` coprime to `q` has an inverse `u` modulo `q`, itself coprime to `q`. -/
private lemma exists_integer_inverse_of_isCoprime {q a : ℤ} (h : IsCoprime q a) :
    ∃ u : ℤ, q ∣ u * a - 1 ∧ IsCoprime q u := by
  obtain ⟨v, u, he⟩ := h
  refine ⟨u, ⟨-v, by linear_combination he⟩, v, a, ?_⟩
  simpa only [mul_comm a u] using he

/-- Translation carries the finite-precision determinant theorem to any
residue class. Its divisor and its precision use the same explicit exponent. -/
theorem hypersurface_residue_pow_dvd_det_mod {p n μ s : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 2)) ℤ) (a : Fin (n + 2) → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a f) ∈
      idealOfVars (Fin (n + 2)) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) (originShift a f)) ≠ 0)
    (x : Fin s → Fin (n + 2) → ℤ) (hx : ∀ i j, (p : ℤ) ∣ x i j - a j)
    (hfx : ∀ i, (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣ eval (x i) f)
    (F : Fin s → MvPolynomial (Fin (n + 2)) ℤ) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
      (Matrix.of fun i j => eval (x i) (F j)).det := by
  have h := hypersurface_pow_dvd_det_mod (originShift a f) hf hμ
    (fun i j => x i j - a j) hx
    (fun i => by simpa only [eval_sub_originShift] using hfx i)
    (fun j => originShift a (F j))
  simpa only [eval_sub_originShift] using h

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- Unit normalization in the first homogeneous coordinate preserves the
evaluation of a degree-M form, up to the corresponding unit row factor. -/
private lemma projective_hypersurface_chart_eval_congr {n M : ℕ} {q u : ℤ}
    (k : Fin (n + 3)) (z : Fin (n + 3) → ℤ) (hu : q ∣ u * z k - 1)
    (F : MvPolynomial (Fin (n + 3)) ℤ) (hF : F.IsHomogeneous M) :
    q ∣ eval (fun j : Fin (n + 2) => u * z (Equiv.swap 0 k j.succ)) (affineChartAt k F) -
      u ^ M * eval z F := by
  have hswap : eval (z ∘ Equiv.swap 0 k) (rename (Equiv.swap 0 k) F) = eval z F := by
    simp [eval_rename, Function.comp_def]
  rw [affineChartAt, affineChart_eval, ← hswap,
    ← homogeneous_eval_smul hF.rename_isHomogeneous]
  apply dvd_eval_sub_of_dvd_coordinates
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul, neg_sub, Function.comp_apply, Equiv.swap_apply_left] using
      (show q ∣ -(u * z k - 1) from dvd_neg.mpr hu)
  · simp

/-- The local projective divisor in a chart whose pivot coordinate is a unit. -/
theorem projective_hypersurface_local_det_divisibility {p n μ s d M : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin s → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin (n + 3) → ℤ) (k : Fin (n + 3)) (a : Fin (n + 2) → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a (affineChartAt k f)) ∈
      idealOfVars (Fin (n + 2)) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ
      (map (Int.castRingHom (ZMod p)) (originShift a (affineChartAt k f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i k))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 k j.succ) - a j * z i k)
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
      (Matrix.of fun i j => eval (z i) (F j)).det := by
  classical
  let N := hypersurfaceMultiplicityExponent (n + 1) μ s
  by_cases hN : N = 0
  · change (p : ℤ) ^ N ∣ _
    simp [hN]
  let q : ℤ := (p : ℤ) ^ N
  have hpq : (p : ℤ) ∣ q := by
    simpa only [pow_one] using pow_dvd_pow (p : ℤ) (Nat.one_le_iff_ne_zero.mpr hN)
  have hex (i : Fin s) := exists_integer_inverse_of_isCoprime
    (show IsCoprime q (z i k) from (hunit i).pow_left)
  choose u hu huc using hex
  let x : Fin s → Fin (n + 2) → ℤ := fun i j => u i * z i (Equiv.swap 0 k j.succ)
  have hx (i : Fin s) (j : Fin (n + 2)) : (p : ℤ) ∣ x i j - a j := by
    have he : x i j - a j =
        u i * (z i (Equiv.swap 0 k j.succ) - a j * z i k) + a j * (u i * z i k - 1) := by
      dsimp [x]
      ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_right (hres i j) _)
      (dvd_mul_of_dvd_right (hpq.trans (hu i)) _)
  have hxf (i : Fin s) : q ∣ eval (x i) (affineChartAt k f) := by
    have h := projective_hypersurface_chart_eval_congr k (z i) (hu i) f hfhom
    simpa only [hz, mul_zero, sub_zero] using h
  let A := Matrix.of fun i j : Fin s => eval (x i) (affineChartAt k (F j))
  let D := Matrix.of fun i j : Fin s => u i ^ M * eval (z i) (F j)
  have hA : q ∣ A.det :=
    hypersurface_residue_pow_dvd_det_mod (affineChartAt k f) a hf hμ x hx hxf
      (fun j => affineChartAt k (F j))
  have hAD : q ∣ A.det - D.det := by
    apply Matrix.dvd_det_sub_det_of_dvd_sub
    intro i j
    exact projective_hypersurface_chart_eval_congr k (z i) (hu i) (F j) (hF j)
  have hD : q ∣ D.det := by
    simpa only [sub_sub_cancel] using dvd_sub hA hAD
  have hprod : IsCoprime q (∏ i, u i ^ M) :=
    IsCoprime.prod_right fun i _ => (huc i).pow_right
  have he : D.det = (∏ i, u i ^ M) *
      (Matrix.of fun i j => eval (z i) (F j)).det :=
    Matrix.det_mul_column _ _
  rw [he] at hD
  exact hprod.dvd_of_dvd_mul_left hD

end
end CCDN
