/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.RankNumerics

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.ProjectiveTranslation
public import CCDN.AuxiliaryPolynomial.PositionedAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import CCDN.AuxiliaryPolynomial.HypersurfacePositionHeight

/-!
The coefficient-sensitive auxiliary theorem for arbitrary absolutely
irreducible homogeneous equations in arbitrary coordinates.

The equation is moved into position by a homogeneous translation fixing the
homogenizing coordinate; zeros, primitivity, absolute irreducibility and
nondivisibility are transported along it, and the box grows from `B` to
`(d + 1) B`. `absolute_auxiliary_degree_of_comparison` does this for any finite
prime set whose normalized comparison holds for every translate.

The geometric bad-prime predicate is invariant under integral shears.

The box enlargement by d+1 costs only a dimension constant in the
auxiliary degree, with no added power of d in its leading term.
-/

@[expose] public section
namespace CCDN
noncomputable section

variable {r d : ℕ} (hr : 0 < r) (hd : 0 < d)

include hr hd in
/-- For positive `r` and `d`, the box enlargement factor
$(d + 1)^{(r + 1) / (r d^{1/r})}$ is at most $\exp((r + 1)^2 / r)$, a bound depending only
on `r`. -/
lemma auxiliary_box_rpow_factor  :
    (↑d + 1) ^ ((↑r + 1) / (↑r * dimensionRoot r d)) ≤
      Real.exp ((↑r + 1) ^ 2 / r) := by
  rw [Real.rpow_def_of_pos (by positivity)]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right (log_nat_add_one_le_root hr hd)
    (show 0 ≤ (↑r + 1) / (↑r * dimensionRoot r d) by positivity)
  convert hh using 1
  field_simp

include hr hd in
private lemma auxiliary_box_log_cost  :
    ↑d ^ (1 - 1 / (r : ℝ)) * Real.log (↑d + 1) ≤ (↑r + 1) * d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hh := mul_le_mul_of_nonneg_left (log_nat_add_one_le_root hr hd)
    (Real.rpow_nonneg hd0.le (1 - 1 / ↑r))
  have he : ↑d ^ (1 - 1 / (r : ℝ)) * dimensionRoot r d = d := by
    rw [← Real.rpow_add hd0, sub_add_cancel, Real.rpow_one]
  calc
    _ ≤ _ := hh
    _ = (↑r + 1) * d := by rw [← mul_left_comm, he]

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- A prime is bad for the homogeneous translate of a nonzero integral form `f` if and only
if it is bad for `f`. -/
lemma hypersurfaceBadReduction_homogeneousTranslation {n d : ℕ}
    (f : CCDN.IntegerPolynomial (n + 1)) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (a : CCDN.IntPoint n) (p : ℕ) :
    HypersurfaceBadReduction (homogeneousTranslation ℤ a f) p ↔ HypersurfaceBadReduction f p := by
  by_cases hp : p.Prime
  · let : Fact p.Prime := ⟨hp⟩
    have hg0 : homogeneousTranslation ℤ a f ≠ 0 := by
      simp_all
    rw [homogeneous_hypersurfaceBadReduction_iff _ (homogeneousTranslation_homogeneous a hf) hg0,
      homogeneous_hypersurfaceBadReduction_iff _ hf hf0, homogeneousTranslation_map]
    solve_by_elim [not_congr, MulEquiv.irreducible_iff]
  · constructor <;> intro h <;> exact (hp h.1).elim

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- The dimension constant $(5(n + 2) + 5)(n + 2)$ of the positioning step: after a suitable
homogeneous translation, the logarithm of the coefficient height exceeds that of the
lexicographic leading coefficient by at most this constant times $d^{1 + 1/(n + 1)}$. -/
def hypersurfaceAuxiliaryPositionConstant (n : ℕ)  := (5 * (n + 2 : ℝ) + 5) * (n + 2 : ℝ)

/-- The dimension constant in the absolutely irreducible case of CCDN Theorem 3.1.1 for forms
in `n + 3` variables: the positioned constant times a factor absorbing the enlargement of the
box from `B` to `(d + 1) B` and the passage to the original coefficient height. -/
def hypersurfaceAbsoluteAuxiliaryConstant (n : ℕ) : ℝ :=
  hypersurfacePositionedAuxiliaryConstant n (hypersurfaceAuxiliaryPositionConstant n) *
    (Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ)) + (n + 3 : ℝ))

/-- The constant `hypersurfaceAbsoluteAuxiliaryConstant n` is positive. -/
lemma hypersurfaceAbsoluteAuxiliaryConstant_pos (n : ℕ) :
    0 < hypersurfaceAbsoluteAuxiliaryConstant n := by
  unfold hypersurfaceAbsoluteAuxiliaryConstant hypersurfacePositionedAuxiliaryConstant
  positivity

/-- The auxiliary degree bound of CCDN Theorem 3.1.1 with bad-prime factor `b` and
coefficient height `H`. -/
def hypersurfaceAuxiliaryDegreeBound (n d : ℕ) (B b H : ℝ) : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant n * auxDegreeBound n d B b H

section Translation

variable {n : ℕ}

private lemma irreducible_map_homogeneousTranslation {K : Type*} [Field K] (a : CCDN.IntPoint (n + 2))
    {f : CCDN.IntegerPolynomial (n + 3)} (hir : Irreducible (map (Int.castRingHom K) f)) :
    Irreducible (map (Int.castRingHom K) (homogeneousTranslation ℤ a f)) := by
  grind [homogeneousTranslation_map, MulEquiv.irreducible_iff]

variable (a : CCDN.IntPoint (n + 2))

/-- Evaluating the homogeneous translate of `f` by `a` at the point translated by `-a` gives
the value of `f` at the original point. -/
lemma eval_homogeneousTranslation_neg 
    (f : CCDN.IntegerPolynomial (n + 3)) (z : IntPoint (n + 3)) :
    eval (homogeneousPointTranslation (-a) z) (homogeneousTranslation ℤ a f) = eval z f := by
  rw [homogeneousTranslation_eval]
  change eval (homogeneousPointTranslation a (homogeneousPointTranslation (-a) z)) f = _
  have he := homogeneousPointTranslation_inverse (-a) z
  simp only [neg_neg] at he
  rw [he]

/-- A form `g` not divisible by the translate of `f` translates back to a
nonmultiple of `f`. -/
private lemma not_dvd_homogeneousTranslation_neg 
    {f g : CCDN.IntegerPolynomial (n + 3)} (hgnd : ¬homogeneousTranslation ℤ a f ∣ g) :
    ¬f ∣ homogeneousTranslation ℤ (-a) g := by
  intro hdvd
  apply hgnd
  have hh := map_dvd (homogeneousTranslation ℤ a).toRingHom hdvd
  exact id
    (fun hh =>
      Eq.mp
        (congrArg (fun _a => (homogeneousTranslation ℤ a) f ∣ _a)
          (have this := AlgEquiv.apply_symm_apply (homogeneousTranslation ℤ a) g;
          this))
        hh)
    hh

end Translation

/-- Enlarging the box from `B` to `(d + 1) B` and lowering the coefficient height from
`H` to `h ≤ H` cost a factor depending only on the dimension. -/
private lemma auxDegreeBound_translate_le {n d : ℕ} (hd : 0 < d) {B b H h : ℝ} (hB : 1 ≤ B)
    (hb : 0 ≤ b) (hh0 : 0 < h) (hhH : h ≤ H) :
    auxDegreeBound n d ((↑d + 1) * B) b H ≤
      (Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ)) + (n + 3 : ℝ)) * auxDegreeBound n d B b h := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  let R := (↑d + 1) * B
  let D := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  let α := boxExponent n d
  let q := heightExponent n d
  let Q := D * b * B ^ α / h ^ q
  let l := ↑d ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  let E := Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hl : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hB)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hfactor := by
    simpa only [dimensionRoot, degreeRoot, boxExponent, α, E, Nat.cast_add, Nat.cast_one, hnR] using
      auxiliary_box_rpow_factor (r := n + 1) (by omega) hd
  have hRpow : R ^ α ≤ E * B ^ α := by
    rw [show R = (↑d + 1) * B from rfl, Real.mul_rpow (by positivity) (by linarith)]
    exact mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (by linarith) _)
  have hQ' : D * b * R ^ α / H ^ q ≤ E * Q := by
    calc
      _ ≤ D * b * R ^ α / h ^ q := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (Real.rpow_le_rpow hh0.le hhH (by dsimp [q]; positivity))
      _ ≤ D * b * (E * B ^ α) / h ^ q :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRpow (mul_nonneg hD hb))
          (by positivity)
      _ = _ := by dsimp [Q]; ring
  have hlogcost := by
    simpa only [Nat.cast_add, Nat.cast_one, hnR] using
      auxiliary_box_log_cost (r := n + 1) (by omega) hd
  have hdD : ↑d ≤ D := le_rpow_four_sub_inv hd
  have hl' : ↑d ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R ≤ l + (n + 2 : ℝ) * D := by
    rw [Real.log_mul (by positivity) (by linarith), mul_add]
    have hh := mul_le_mul_of_nonneg_left hdD (show 0 ≤ (n + 2 : ℝ) by positivity)
    linarith
  change D * b * R ^ α / H ^ q + ↑d ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R + D ≤
    (E + (n + 3 : ℝ)) * (Q + l + D)
  nlinarith

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ} (f : CCDN.IntegerPolynomial (n + 3)) (hf : f.IsHomogeneous d) (hd : 0 < d) (hir : Irreducible (map (Int.castRingHom K) f))

include hf hd hir in
/-- The absolutely irreducible case of CCDN Theorem 3.1.1 for any finite prime set
`bad` whose normalized comparison holds for every homogeneous translate of `f` and the
translated points. The constant depends only on dimension; the coefficient height
belongs to the original equation. -/
theorem absolute_auxiliary_degree_of_comparison
    
    {B : ℝ} {z : Fin t → IntPoint (n + 3)} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (bad : Finset ℕ)
    (hcomp : ∀ a : CCDN.IntPoint (n + 2), AuxiliaryRankComparison MonomialOrder.lex
      (homogeneousTranslation ℤ a f) d (fun i => homogeneousPointTranslation (-a) (z i)) bad) :
    ∃ M : ℕ,
      ↑M ≤ hypersurfaceAuxiliaryDegreeBound n d B (primeSetFactor bad)
        (integerCoefficientHeight f) ∧
      ∃ g, IsPointAuxiliary f g M z := by
  obtain ⟨⟨hB, hz, hbox⟩, hprim⟩ := hzB
  have hf0 := ne_zero_of_irreducible_map hir
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  obtain ⟨a, H, ha, hH, hcf, hcg, hpos⟩ := exists_hypersurface_coefficient_position
    (r := n + 1) (by omega) hd f hf hf0
  let model := homogeneousTranslation ℤ a f
  let w := fun i => homogeneousPointTranslation (-a) (z i)
  have hposition : Real.log H ≤ Real.log |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| +
      hypersurfaceAuxiliaryPositionConstant n * d * degreeRoot n d := by
    simp_all [CCDN.hypersurfaceAuxiliaryPositionConstant, CCDN.degreeRoot, CCDN.dimensionRoot]; omega
  obtain ⟨M, hbound, g, hgh, hgz, hgnd⟩ := positioned_auxiliary_degree_of_comparison
    MonomialOrder.lex model (homogeneousTranslation_homogeneous a hf) hd
    (irreducible_map_homogeneousTranslation a hir) H hH hcg (z := w)
    ⟨⟨one_le_mul_of_one_le_of_one_le (by simp_all) hB,
      fun i => (eval_homogeneousTranslation_neg a f (z i)).trans (hz i),
      fun i j => homogeneousPointTranslation_box hB a ha (z i) (hbox i) j⟩,
      fun i => (homogeneousPointTranslation_gcd (-a) (z i)).trans (hprim i)⟩ bad (hcomp a)
    (hypersurfaceAuxiliaryPositionConstant n)
    (by unfold hypersurfaceAuxiliaryPositionConstant; positivity) hposition
  refine ⟨M, ?_, homogeneousTranslation ℤ (-a) g,
    homogeneousTranslation_homogeneous (-a) hgh,
    fun i => by rw [homogeneousTranslation_eval]; exact hgz i,
    not_dvd_homogeneousTranslation_neg a hgnd⟩
  have hC : 0 ≤ hypersurfacePositionedAuxiliaryConstant n
      (hypersurfaceAuxiliaryPositionConstant n) := by
    unfold hypersurfacePositionedAuxiliaryConstant; positivity
  have htr := auxDegreeBound_translate_le (n := n) hd hB (Real.exp_pos _).le
    (by exact_mod_cast integerCoefficientHeight_pos f hf0)
    (integerCoefficientHeight_le f (by linarith) hcf) (b := primeSetFactor bad)
  refine hbound.trans ((mul_le_mul_of_nonneg_left htr hC).trans_eq ?_)
  unfold hypersurfaceAuxiliaryDegreeBound hypersurfaceAbsoluteAuxiliaryConstant
  ring

include hf hd hir in
/-- The absolutely irreducible case of CCDN Theorem 3.1.1. The constant depends
only on dimension. The coefficient height and bad-prime factor belong to the
original equation. -/
theorem hypersurface_absolute_auxiliary_degree
    
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B) :
    ∃ (bad : Finset ℕ) (M : ℕ),
      (∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) ∧
      ↑M ≤ hypersurfaceAuxiliaryDegreeBound n d B (primeSetFactor bad)
        (integerCoefficientHeight f) ∧
      ∃ g : CCDN.IntegerPolynomial (n + 3), g.IsHomogeneous M ∧
        (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g := by
  have hf0 := ne_zero_of_irreducible_map hir
  obtain ⟨bad, hbad⟩ := exists_hypersurface_bad_prime_finset f hf hd hir
  obtain ⟨M, hM, g, hg⟩ := absolute_auxiliary_degree_of_comparison f hf hd hir
    ⟨⟨hB, hz, hbox⟩, hprim⟩ bad
    (fun a => hypersurface_auxiliaryRankComparison MonomialOrder.lex _
      (homogeneousTranslation_homogeneous a hf)
      ((homogeneousTranslation ℤ a).injective.ne (by simpa using hf0)) hd _
      (fun i => (homogeneousPointTranslation_gcd (-a) (z i)).trans (hprim i))
      (fun i => (eval_homogeneousTranslation_neg a f (z i)).trans (hz i)) bad
      fun p => by grind [hypersurfaceBadReduction_homogeneousTranslation])
  exact ⟨bad, M, hbad, hM, g, isPointAuxiliary_iff.mp hg⟩

end
end CCDN
