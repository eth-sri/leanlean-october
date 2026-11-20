/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Algebra.Equations
public import CCDN.AuxiliaryPolynomial.AbsoluteAuxiliary
public import CCDN.AuxiliaryPolynomial.ScaledAuxiliaryCount
public import CCDN.AuxiliaryPolynomial.AffineTranslationCount
public import CCDN.Height.ScaledHypersurfaceHeight
import CCDN.ForMathlib.MvPolynomial
import CCDN.AuxiliaryPolynomial.AffineLeadingTranslation
import CCDN.Height.MultivariateGridHeight
import CCDN.Height.PolynomialBoxHeight
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.NumberTheory.Bertrand

/-! Choose the scaling prime first, then choose the origin in a residue class on which the equation does not vanish. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

section

variable {n : ℕ} (f : IntegerPolynomial n)

/-- After choosing the scaling prime, choose the origin modulo it.  Primitivity and
`d < p` guarantee a nonzero value on the residue grid.  Centered lifts cost at most `p/2`. -/
private theorem exists_scaling_origin {p : ℕ} (hp : p.Prime)
    (f : IntegerPolynomial n) (hprim : PrimitiveIntegerPolynomial f) (hd : f.totalDegree < p) :
    ∃ a : IntPoint n, InBox a ((p : ℝ) / 2) ∧ ¬ (p : ℤ) ∣ (affineTranslation ℤ a f).coeff 0 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let g := residueEquation p f
  have hg : g ≠ 0 := by
    intro hz
    apply (show Prime (p : ℤ) from Int.prime_iff_natAbs_prime.mpr (by simpa)).not_isUnit (hprim p ?_)
    intro m
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa [g, coeff_map] using congrArg (fun u : MvPolynomial (Fin n) (ZMod p) => u.coeff m) hz
  obtain ⟨x, hx⟩ : ∃ x, eval x g ≠ 0 := by
    by_contra! hz
    apply hg (eq_zero_of_eval_zero_at_prod_finset g (fun _ => Finset.univ) ?_ fun x _ => hz x)
    simpa using fun i => ((degreeOf_le_totalDegree g i).trans (totalDegree_map_le _ _)).trans_lt hd
  refine ⟨fun i => (x i).valMinAbs, fun i => ?_, fun h => hx ?_⟩
  · have h := (x i).natAbs_valMinAbs_le
    have h' : 2 * (x i).valMinAbs.natAbs ≤ p := by omega
    have : (2 : ℝ) * |((x i).valMinAbs : ℝ)| ≤ p := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast h'
    linarith
  · rw [affineTranslation_constantCoeff, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    change Int.castRingHom (ZMod p) (eval (fun i => (x i).valMinAbs) f) = 0 at h
    simpa only [map_eval, Function.comp_def, Int.coe_castRingHom, ZMod.coe_valMinAbs] using h

include f in
/-- Scale and origin for a primitive equation: the box and short integer grid
both fit in the scale and the new constant coefficient is prime to it. -/
structure BoxScaling (B : ℝ) where
  p : ℕ
  prime : p.Prime
  a : IntPoint n
  origin : InBox a (p/2)
  avoids : ¬ (p:ℤ) ∣ (affineTranslation ℤ a f).coeff 0
  large : 2*B ≤ p
  degree_lt : f.totalDegree < p
  small : (p:ℝ) ≤ 6*B*f.totalDegree

theorem exists_boxScaling (hprim : PrimitiveIntegerPolynomial f)
    (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) : Nonempty (BoxScaling f B) := by
  let d := f.totalDegree
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (d + ⌊2 * B⌋₊) (by omega)
  have hpd : d < p := by omega
  have hBpos : 0 ≤ B := by linarith
  have hsize : (p : ℝ) ≤ 6 * B * d := by
    have : (p : ℝ) ≤ 2 * (d + (⌊2 * B⌋₊ : ℕ)) := by exact_mod_cast hhi
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [Nat.floor_le (show 0 ≤ 2 * B by positivity), mul_nonneg (sub_nonneg.mpr hB) (Nat.cast_nonneg (α := ℝ) d),
      mul_nonneg hBpos (sub_nonneg.mpr hd1)]
  obtain ⟨a, ha, hc⟩ := exists_scaling_origin hp f hprim hpd
  exact ⟨⟨p,hp,a,ha,hc,(Nat.lt_floor_add_one _).le.trans (by exact_mod_cast (show ⌊2 * B⌋₊ + 1 ≤ p by omega)),hpd,hsize⟩⟩

end

namespace BoxScaling
variable {n : ℕ} {f : IntegerPolynomial n} {B : ℝ} (S : BoxScaling f B)

abbrev equation := scaledHomogenize f.totalDegree (S.p : ℤ) (affineTranslation ℤ S.a f)
abbrev point (x : IntPoint n) : IntPoint (n+1) := Fin.cons (S.p : ℤ) (x-S.a)
abbrev pull (G : IntegerPolynomial (n+1)) := affineTranslation ℤ (-S.a) (homogeneousSlice n (S.p : ℤ) G)

lemma homogeneous : S.equation.IsHomogeneous f.totalDegree := scaledHomogenize_homogeneous _ _ (affineTranslation_totalDegree_le _ _)
lemma ne_zero (hf : f ≠ 0) : S.equation ≠ 0 := scaledHomogenize_ne_zero _ (by exact_mod_cast S.prime.ne_zero)
  (by simp_all)
lemma eval_eq (x) : eval (S.point x) S.equation = (S.p : ℤ)^f.totalDegree * eval x f := by
  simp [point, equation, scaledHomogenize_eval _ _ (affineTranslation_totalDegree_le S.a f), affineTranslation_eval]
lemma pull_eval (x G) : eval x (S.pull G) = eval (S.point x) G := by
  simp [pull, point, affineTranslation_eval, homogeneousSlice_eval, sub_eq_add_neg]
lemma pull_degree {M} {G : IntegerPolynomial (n+1)} (hG : G.IsHomogeneous M) : (S.pull G).totalDegree ≤ M :=
  (affineTranslation_totalDegree_le _ _).trans (homogeneousSlice_degree_le _ hG)
lemma point_bound {x} (hx : InBox x B) : InBox (S.point x) S.p := by
  intro i; refine Fin.cases (by simp [point]) (fun j => ?_) i
  change |((x j - S.a j : ℤ) : ℝ)| ≤ _
  rw [Int.cast_sub]; exact (abs_sub _ _).trans (by linarith [hx j,S.origin j,S.large])
lemma pull_proper (hf : f ≠ 0) (hprim : PrimitiveIntegerPolynomial f) {M G} (hG : G.IsHomogeneous M)
    (hnd : ¬ S.equation ∣ G) : ¬ f ∣ S.pull G := by
  have h := scaled_auxiliary_rational_not_dvd _
    (by simp_all) (hprim.translate_affine _) S.prime S.avoids G hG
    (by simp_all [affineTranslation_totalDegree])
  intro hdiv; apply h
  apply map_dvd
  have hh := map_dvd (affineTranslation ℤ S.a).toRingHom hdiv
  change _ ∣ affineTranslation ℤ S.a ((affineTranslation ℤ S.a).symm _) at hh
  rwa [AlgEquiv.apply_symm_apply] at hh

lemma leading_height : (S.p : ℝ)^f.totalDegree * integerCoefficientHeight (homogeneousComponent f.totalDegree f) ≤
    integerCoefficientHeight S.equation := by
  have h := scaledHomogenize_leading_height_lower (affineTranslation ℤ S.a f) (show (1:ℤ) ≤ S.p by exact_mod_cast S.prime.one_le)
  rw [affineTranslation_leading_homogeneousComponent] at h
  simp_all [equation, affineTranslation_totalDegree, Int.cast_natCast]

/-- Even the unscaled coefficients are controlled by the height of the lift:
evaluate on the short grid, where the lifted points have norm at most `2p`. -/
lemma height_control (hd : 0 < f.totalDegree) (hf : f ≠ 0) : let d := f.totalDegree
    Real.log (integerCoefficientHeight f) ≤ (4*(n:ℝ)+4)*(d:ℝ)^2 + Real.log (integerCoefficientHeight S.equation) := by
  let d := f.totalDegree
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  let H : ℝ := integerCoefficientHeight S.equation
  let U := (d+1:ℝ)
  have hU : 0 < U := by positivity
  have hH : 0 < H := by dsimp only [H]; exact_mod_cast integerCoefficientHeight_pos _ (S.ne_zero hf)
  have hp : (0:ℝ) < S.p := by exact_mod_cast S.prime.pos
  have hcoeff := integer_multivariate_coefficient_bound_of_grid f le_rfl (show 0 ≤ U^(n+1)*H*2^d by positivity) (fun x hx => by
    let v := S.point (fun i => (x i))
    have hv (i) : |(v i : ℝ)| ≤ 2*S.p := by
      refine Fin.cases (by simp [v,point]; linarith) (fun j => ?_) i
      change |(((x j) - S.a j : ℤ):ℝ)| ≤ _
      rw [Int.cast_sub,Int.cast_natCast]
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      have hh : (x j : ℝ) ≤ S.p := by exact_mod_cast (hx j).trans S.degree_lt.le
      linarith [S.origin j]
    have hh := polynomial_eval₂_box_bound S.equation H _ hH.le (by linarith [show (1:ℝ) ≤ S.p by exact_mod_cast S.prime.one_le])
      (coefficient_abs_le_integerCoefficientHeight _) _ hv
    rw [show eval₂ _ (fun i => (v i : ℝ)) S.equation = (eval v S.equation : ℝ) from by rw [← eval_map]; exact (map_eval (Int.castRingHom ℝ) v S.equation).symm] at hh
    rw [(S.homogeneous.totalDegree (S.ne_zero hf)), Fintype.card_fin, S.eval_eq, Int.cast_mul, Int.cast_pow,Int.cast_natCast,abs_mul,abs_of_pos (pow_pos hp _), mul_pow] at hh
    exact le_of_mul_le_mul_left (a := (S.p:ℝ)^d) (by linarith only [hh]) (pow_pos hp d))
  have hh := Real.log_le_log (by exact_mod_cast integerCoefficientHeight_pos f hf) (integerCoefficientHeight_le f (by positivity) hcoeff)
  rw [Real.log_mul (pow_pos hU _).ne' (by positivity),Real.log_mul (mul_pos (pow_pos hU _) hH).ne' (by positivity),Real.log_mul (pow_pos hU _).ne' hH.ne'] at hh
  simp only [Real.log_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hh
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
  nlinarith [mul_le_mul_of_nonneg_left (show Real.log U ≤ d by simpa [U] using Real.log_le_sub_one_of_pos hU) (by positivity),
    mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (α := ℝ) d),mul_le_mul_of_nonneg_left (show (d:ℝ) ≤ d^2 by nlinarith [sq_nonneg (d-1)]) (by positivity), mul_nonneg (sub_nonneg.mpr hd1) (Nat.cast_nonneg (α := ℝ) n)]

end BoxScaling
end
end CCDN
