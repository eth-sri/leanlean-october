/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.ProjectiveTranslation
import CCDN.AuxiliaryPolynomial.PositionedAuxiliary
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

namespace CCDN
section

variable {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
include hr hd

/-- For positive `r` and `d`, the box enlargement factor
$(d + 1)^{(r + 1) / (r d^{1/r})}$ is at most $\exp((r + 1)^2 / r)$, a bound depending only
on `r`. -/
lemma auxiliary_box_rpow_factor :
    ((d : ℝ) + 1) ^ (((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      Real.exp (((r : ℝ) + 1) ^ 2 / r) := by
  have hr0 : (0 : ℝ) < r := mod_cast hr
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hroot : (0 : ℝ) < d ^ (1 / r) := by positivity
  rw [Real.rpow_def_of_pos (by positivity)]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right (log_nat_add_one_le_root hr hd)
    (show 0 ≤ ((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) by positivity)
  convert hh using 1
  field_simp

lemma auxiliary_box_log_cost :
    (d : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log ((d : ℝ) + 1) ≤ ((r : ℝ) + 1) * d := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hh := mul_le_mul_of_nonneg_left (log_nat_add_one_le_root hr hd)
    (Real.rpow_nonneg hd0.le (1 - 1 / (r : ℝ)))
  have he : (d : ℝ) ^ (1 - 1 / (r : ℝ)) * (d : ℝ) ^ (1 / (r : ℝ)) = d := by
    rw [← Real.rpow_add hd0, sub_add_cancel, Real.rpow_one]
  calc
    _ ≤ _ := hh
    _ = ((r : ℝ) + 1) * d := by grind

end

noncomputable section
open MvPolynomial

/-- A prime is bad for the homogeneous translate of a nonzero integral form `f` if and only
if it is bad for `f`. -/
lemma hypersurfaceBadReduction_homogeneousTranslation {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (a : Fin n → ℤ) (p : ℕ) :
    HypersurfaceBadReduction (homogeneousTranslation ℤ a f) p ↔ HypersurfaceBadReduction f p := by
  by_cases hp : p.Prime
  · let : Fact p.Prime := ⟨hp⟩
    have hg0 : homogeneousTranslation ℤ a f ≠ 0 := by simp_all
    rw [homogeneous_hypersurfaceBadReduction_iff _ (homogeneousTranslation_homogeneous a hf) hg0,
      homogeneous_hypersurfaceBadReduction_iff _ hf hf0, homogeneousTranslation_map]
    exact not_congr (MulEquiv.irreducible_iff
      (f := homogeneousTranslation (AlgebraicClosure (ZMod p)) ((Int.castRingHom _) ∘ a)))
  · constructor <;> intro h <;> exact (hp h.1).elim

section
variable (n : ℕ)

/-- The dimension constant $(5(n + 2) + 5)(n + 2)$ of the positioning step: after a suitable
homogeneous translation, the logarithm of the coefficient height exceeds that of the
lexicographic leading coefficient by at most this constant times $d^{1 + 1/(n + 1)}$. -/
def hypersurfaceAuxiliaryPositionConstant : ℝ := (5 * (n + 2 : ℝ) + 5) * (n + 2 : ℝ)

/-- The dimension constant in the absolutely irreducible case of CCDN Theorem 3.1.1 for forms
in `n + 3` variables: the positioned constant times a factor absorbing the enlargement of the
box from `B` to `(d + 1) B` and the passage to the original coefficient height. -/
def hypersurfaceAbsoluteAuxiliaryConstant : ℝ :=
  hypersurfacePositionedAuxiliaryConstant n (hypersurfaceAuxiliaryPositionConstant n) *
    (Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ)) + (n + 3 : ℝ))

/-- The constant `hypersurfaceAbsoluteAuxiliaryConstant n` is positive. -/
lemma hypersurfaceAbsoluteAuxiliaryConstant_pos :
    0 < hypersurfaceAbsoluteAuxiliaryConstant n := by
  unfold hypersurfaceAbsoluteAuxiliaryConstant hypersurfacePositionedAuxiliaryConstant
  positivity

end

/-- The auxiliary degree bound of CCDN Theorem 3.1.1 with bad-prime factor `b` and
coefficient height `H`. -/
def hypersurfaceAuxiliaryDegreeBound (n d : ℕ) (B b H : ℝ) : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant n * auxDegreeBound n d B b H

section Translation

variable {n : ℕ}

variable (a : Fin (n + 2) → ℤ)

/-- Evaluating the homogeneous translate of `f` by `a` at the point translated by `-a` gives
the value of `f` at the original point. -/
lemma eval_homogeneousTranslation_neg
    (f : MvPolynomial (Fin (n + 3)) ℤ) (z : IntPoint (n + 3)) :
    eval (homogeneousPointTranslation (-a) z) (homogeneousTranslation ℤ a f) = eval z f := by
  rw [homogeneousTranslation_eval]
  change eval (homogeneousPointTranslation a (homogeneousPointTranslation (-a) z)) f = _
  have he := homogeneousPointTranslation_inverse (-a) z
  simp at he
  rw [he]

/-- A form `g` not divisible by the translate of `f` translates back to a
nonmultiple of `f`. -/
lemma not_dvd_homogeneousTranslation_neg
    {f g : MvPolynomial (Fin (n + 3)) ℤ} (hgnd : ¬homogeneousTranslation ℤ a f ∣ g) :
    ¬f ∣ homogeneousTranslation ℤ (-a) g := by
  intro hdvd
  apply hgnd
  have hh := map_dvd (homogeneousTranslation ℤ a).toRingHom hdvd
  change homogeneousTranslation ℤ a f ∣
    homogeneousTranslation ℤ a (homogeneousTranslation ℤ (-a) g) at hh
  rwa [show homogeneousTranslation ℤ a (homogeneousTranslation ℤ (-a) g) = g from
    (homogeneousTranslation ℤ a).apply_symm_apply g] at hh

end Translation

/-- Enlarging the box from `B` to `(d + 1) B` and lowering the coefficient height from
`H` to `h ≤ H` cost a factor depending only on the dimension. -/
lemma auxDegreeBound_translate_le {n d : ℕ} (hd : 0 < d) {B b H h : ℝ} (hB : 1 ≤ B)
    (hb : 0 ≤ b) (hh0 : 0 < h) (hhH : h ≤ H) :
    auxDegreeBound n d (((d : ℝ) + 1) * B) b H ≤
      (Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ)) + (n + 3 : ℝ)) * auxDegreeBound n d B b h := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  let R := ((d : ℝ) + 1) * B
  let D := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  let α := boxExponent n d
  let q := heightExponent n d
  let Q := D * b * B ^ α / h ^ q
  let l := d ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  let E := Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ))
  have hD : 0 ≤ D := by positivity
  have hQ : 0 ≤ Q := by positivity
  have hl : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hB)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hfactor : (d + 1) ^ α ≤ E := by
    simpa only [α, E, Nat.cast_add, Nat.cast_one, hnR] using
      auxiliary_box_rpow_factor (r := n + 1) (by omega) hd
  have hRpow : R ^ α ≤ E * B ^ α := by
    rw [show R = (d + 1) * B from rfl, Real.mul_rpow (by positivity) (by linarith)]
    bound
  have hQ' : D * b * R ^ α / H ^ q ≤ E * Q := by
    calc
      _ ≤ D * b * R ^ α / h ^ q := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (Real.rpow_le_rpow hh0.le hhH (by positivity))
      _ ≤ D * b * (E * B ^ α) / h ^ q :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRpow (mul_nonneg hD hb))
          (by positivity)
      _ = _ := by grind
  have hlogcost : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log ((d : ℝ) + 1) ≤
      (n + 2 : ℝ) * d := by
    simpa [Nat.cast_add, Nat.cast_one, hnR] using
      auxiliary_box_log_cost (r := n + 1) (by omega) hd
  have hdD : (d : ℝ) ≤ D := le_rpow_four_sub_inv hd
  have hl' : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R ≤ l + (n + 2 : ℝ) * D := by
    rw [Real.log_mul (by positivity) (by linarith), mul_add]
    nlinarith
  change D * b * R ^ α / H ^ q + (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R + D ≤
    (E + (n + 3 : ℝ)) * (Q + l + D)
  have h1 := mul_nonneg (show 0 ≤ (n + 3 : ℝ) by positivity) hQ
  have h2 := mul_nonneg (show 0 ≤ E + (n + 2 : ℝ) by positivity) hl
  have h3 := mul_nonneg hE hD
  nlinarith

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ} (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d) (hir : Irreducible (map (Int.castRingHom K) f)) {B : ℝ}
include hf hd hir

/-- The absolutely irreducible case of CCDN Theorem 3.1.1 for any finite prime set
`bad` whose normalized comparison holds for every homogeneous translate of `f` and the
translated points. The constant depends only on dimension; the coefficient height
belongs to the original equation. -/
theorem absolute_auxiliary_degree_of_comparison
    {z : Fin t → IntPoint (n + 3)} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (bad : Finset ℕ)
    (hcomp : ∀ a : Fin (n + 2) → ℤ, AuxiliaryRankComparison MonomialOrder.lex
      (homogeneousTranslation ℤ a f) d (fun i => homogeneousPointTranslation (-a) (z i)) bad) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d B (primeSetFactor bad)
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
      hypersurfaceAuxiliaryPositionConstant n * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    simpa [hypersurfaceAuxiliaryPositionConstant, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, hnR] using hpos
  obtain ⟨M, hbound, g, hg0, hgh, hgz, hgnd⟩ := positioned_auxiliary_degree_of_comparison
    MonomialOrder.lex model (homogeneousTranslation_homogeneous a hf) hd
    (show Irreducible (map (Int.castRingHom K) (homogeneousTranslation ℤ a f)) by
        rw [homogeneousTranslation_map]
        exact (MulEquiv.irreducible_iff
          (f := homogeneousTranslation K ((Int.castRingHom K) ∘ a))).mpr hir) H hH hcg (z := w)
    ⟨⟨one_le_mul_of_one_le_of_one_le (by linarith) hB,
      fun i => (eval_homogeneousTranslation_neg a f (z i)).trans (hz i),
      fun i j => homogeneousPointTranslation_box hB a ha (z i) (hbox i) j⟩,
      fun i => (homogeneousPointTranslation_gcd (-a) (z i)).trans (hprim i)⟩ bad (hcomp a)
    (hypersurfaceAuxiliaryPositionConstant n)
    (by unfold hypersurfaceAuxiliaryPositionConstant; positivity) hposition
  refine ⟨M, ?_, homogeneousTranslation ℤ (-a) g,
    (homogeneousTranslation ℤ (-a)).injective.ne (by omega),
    homogeneousTranslation_homogeneous (-a) hgh,
    fun i => by rw [homogeneousTranslation_eval]; exact hgz i,
    not_dvd_homogeneousTranslation_neg a hgnd⟩
  have hC : 0 ≤ hypersurfacePositionedAuxiliaryConstant n
      (hypersurfaceAuxiliaryPositionConstant n) := by
    unfold hypersurfacePositionedAuxiliaryConstant; positivity
  have htr := auxDegreeBound_translate_le (n := n) hd hB (Real.exp_pos _).le
    (mod_cast integerCoefficientHeight_pos f hf0)
    (integerCoefficientHeight_le f (by linarith) hcf) (b := primeSetFactor bad)
  refine hbound.trans ((mul_le_mul_of_nonneg_left htr hC).trans_eq ?_)
  unfold hypersurfaceAuxiliaryDegreeBound hypersurfaceAbsoluteAuxiliaryConstant
  ring

