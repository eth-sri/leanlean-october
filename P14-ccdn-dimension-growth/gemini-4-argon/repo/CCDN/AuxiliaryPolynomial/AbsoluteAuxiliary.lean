/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

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
open MvPolynomial

/-- The dimension constant $(5(n + 2) + 5)(n + 2)$ of the positioning step: after a suitable
homogeneous translation, the logarithm of the coefficient height exceeds that of the
lexicographic leading coefficient by at most this constant times $d^{1 + 1/(n + 1)}$. -/
def hypersurfaceAuxiliaryPositionConstant (n : ℕ) : ℝ := (5 * (n + 2 : ℝ) + 5) * (n + 2 : ℝ)

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

/-- The absolutely irreducible case of CCDN Theorem 3.1.1. The constant depends
only on dimension. The coefficient height and bad-prime factor belong to the
original equation. -/
theorem hypersurface_absolute_auxiliary_degree
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d t : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B) :
    ∃ (bad : Finset ℕ) (M : ℕ),
      (∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) ∧
      (M : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d B (primeSetFactor bad)
        (integerCoefficientHeight f) ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, eval (z i) g = 0) ∧ ¬ f ∣ g := by
  /- For positive `r` and `d`, the box enlargement factor
  $(d + 1)^{(r + 1) / (r d^{1/r})}$ is at most $\exp((r + 1)^2 / r)$, a bound depending only
  on `r`. -/
  /- A prime is bad for the homogeneous translate of a nonzero integral form `f` if and only
  if it is bad for `f`. -/
  /- Evaluating the homogeneous translate of `f` by `a` at the point translated by `-a` gives
  the value of `f` at the original point. -/
  /- The absolutely irreducible case of CCDN Theorem 3.1.1 for any finite prime set
  `bad` whose normalized comparison holds for every homogeneous translate of `f` and the
  translated points. The constant depends only on dimension; the coefficient height
  belongs to the original equation. -/
  have hf0 := ne_zero_of_irreducible_map hir
  obtain ⟨bad, hbad⟩ := exists_hypersurface_bad_prime_finset f hf hd hir
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  obtain ⟨a, H, ha, hH, hcf, hcg, hpos⟩ := exists_hypersurface_coefficient_position
    (r := n + 1) (by omega) hd f hf hf0
  let model := homogeneousTranslation ℤ a f
  have hmodel_hom := homogeneousTranslation_homogeneous a hf
  have hmodel0 : model ≠ 0 := (homogeneousTranslation ℤ a).injective.ne (by simpa using hf0)
  have hev_neg (i : Fin t) : eval (homogeneousPointTranslation (-a) (z i)) model = 0 := by
    rw [show model = homogeneousTranslation ℤ a f from rfl, homogeneousTranslation_eval]
    exact (by simpa only [neg_neg] using
      congrArg (fun x => eval x f) (homogeneousPointTranslation_inverse (-a) (z i)) :
      eval (homogeneousPointTranslation a (homogeneousPointTranslation (-a) (z i))) f =
        eval (z i) f).trans (hz i)
  have hgcd_neg (i : Fin t) : Finset.univ.gcd (homogeneousPointTranslation (-a) (z i)) = 1 :=
    (homogeneousPointTranslation_gcd (-a) (z i)).trans (hprim i)
  have hposition : Real.log H ≤ Real.log |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| +
      hypersurfaceAuxiliaryPositionConstant n * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    simpa only [hypersurfaceAuxiliaryPositionConstant, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, hnR] using hpos
  obtain ⟨M, hbound, g, hg0, hgh, hgz, hgnd⟩ := positioned_auxiliary_degree_of_comparison
    MonomialOrder.lex model hmodel_hom hd
    (by
      change Irreducible (map (Int.castRingHom K) (homogeneousTranslation ℤ a f))
      rw [homogeneousTranslation_map]
      exact (MulEquiv.irreducible_iff
        (f := homogeneousTranslation K ((Int.castRingHom K) ∘ a))).mpr hir)
    H hH hcg (z := fun i => homogeneousPointTranslation (-a) (z i))
    ⟨⟨one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) d]) hB,
      hev_neg, fun i j => homogeneousPointTranslation_box hB a ha (z i) (hbox i) j⟩,
      hgcd_neg⟩ bad
    (hypersurface_auxiliaryRankComparison MonomialOrder.lex model hmodel_hom hmodel0 hd _
      hgcd_neg hev_neg bad fun p => by
        rw [hbad]
        refine and_congr_right' ?_
        by_cases hp : p.Prime
        · let : Fact p.Prime := ⟨hp⟩
          rw [homogeneous_hypersurfaceBadReduction_iff _ hmodel_hom hmodel0,
            homogeneous_hypersurfaceBadReduction_iff _ hf hf0, homogeneousTranslation_map]
          exact (not_congr (MulEquiv.irreducible_iff
            (f := homogeneousTranslation (AlgebraicClosure (ZMod p))
              ((Int.castRingHom _) ∘ a)))).symm
        · exact ⟨fun h => (hp h.1).elim, fun h => (hp h.1).elim⟩)
    (hypersurfaceAuxiliaryPositionConstant n)
    (by unfold hypersurfaceAuxiliaryPositionConstant; positivity) hposition
  refine ⟨bad, M, hbad, ?_, homogeneousTranslation ℤ (-a) g,
    (homogeneousTranslation ℤ (-a)).injective.ne (by simpa using hg0),
    homogeneousTranslation_homogeneous (-a) hgh,
    fun i => by rw [homogeneousTranslation_eval]; exact hgz i,
    fun hdvd => hgnd (by
      have hh := map_dvd (homogeneousTranslation ℤ a).toRingHom hdvd
      change model ∣ homogeneousTranslation ℤ a (homogeneousTranslation ℤ (-a) g) at hh
      rwa [show homogeneousTranslation ℤ a (homogeneousTranslation ℤ (-a) g) = g from
        (homogeneousTranslation ℤ a).apply_symm_apply g] at hh)⟩
  let b := primeSetFactor bad
  let h : ℝ := integerCoefficientHeight f
  have hb : 0 ≤ b := (Real.exp_pos _).le
  have hh0 : 0 < h := Nat.cast_pos.mpr (integerCoefficientHeight_pos f hf0)
  have hhH : h ≤ H := integerCoefficientHeight_le f (by linarith) hcf
  have hd0 : (0 : ℝ) < d := mod_cast hd
  let R := ((d : ℝ) + 1) * B
  let D := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  let α := boxExponent n d
  let q := heightExponent n d
  let Q := D * b * B ^ α / h ^ q
  let l := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  let E := Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hl : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hB)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hfactor : ((d : ℝ) + 1) ^ α ≤ E := by
    have hr0 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hroot : (0 : ℝ) < (d : ℝ) ^ (1 / ((n + 1 : ℕ) : ℝ)) := by positivity
    have haux : ((d : ℝ) + 1) ^ ((((n + 1 : ℕ) : ℝ) + 1) /
        (((n + 1 : ℕ) : ℝ) * (d : ℝ) ^ (1 / ((n + 1 : ℕ) : ℝ)))) ≤
        Real.exp ((((n + 1 : ℕ) : ℝ) + 1) ^ 2 / (n + 1 : ℕ)) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right
        (log_nat_add_one_le_root (r := n + 1) (by omega) hd) (by positivity)).trans_eq (by field_simp))
    simpa only [α, E, Nat.cast_add, Nat.cast_one, hnR] using haux
  have hRpow : R ^ α ≤ E * B ^ α := by
    rw [show R = ((d : ℝ) + 1) * B from rfl, Real.mul_rpow (by positivity) (by linarith)]
    exact mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg (by linarith) _)
  have hQ' : D * b * R ^ α / H ^ q ≤ E * Q := calc
    _ ≤ D * b * R ^ α / h ^ q := div_le_div_of_nonneg_left (by positivity)
      (by positivity) (Real.rpow_le_rpow hh0.le hhH (by dsimp [q]; positivity))
    _ ≤ D * b * (E * B ^ α) / h ^ q :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRpow (mul_nonneg hD hb)) (by positivity)
    _ = E * Q := by dsimp [Q]; ring
  have hlogcost : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log ((d : ℝ) + 1) ≤ (n + 2 : ℝ) * d := by
    have hh := mul_le_mul_of_nonneg_left (log_nat_add_one_le_root (r := n + 1) (by omega) hd)
      (Real.rpow_nonneg hd0.le (1 - 1 / (n + 1 : ℝ)))
    have he : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * (d : ℝ) ^ (1 / (n + 1 : ℝ)) = d := by
      rw [← Real.rpow_add hd0, sub_add_cancel, Real.rpow_one]
    exact hh.trans_eq (by rw [Nat.cast_add, Nat.cast_one, ← mul_left_comm, he]; ring)
  have hdD : (d : ℝ) ≤ D := le_rpow_four_sub_inv hd
  have hl' : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R ≤ l + (n + 2 : ℝ) * D := by
    dsimp only [R, l]
    rw [Real.log_mul (by positivity) (by linarith), mul_add]
    linarith [mul_le_mul_of_nonneg_left hdD (show 0 ≤ (n + 2 : ℝ) by positivity)]
  have htr : auxDegreeBound n d R b H ≤ (E + (n + 3 : ℝ)) * auxDegreeBound n d B b h := by
    change D * b * R ^ α / H ^ q + (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R + D ≤
      (E + (n + 3 : ℝ)) * (Q + l + D)
    nlinarith [mul_nonneg (show 0 ≤ (n + 3 : ℝ) by positivity) hQ,
      mul_nonneg (show 0 ≤ E + (n + 2 : ℝ) by positivity) hl]
  have hC : 0 ≤ hypersurfacePositionedAuxiliaryConstant n
      (hypersurfaceAuxiliaryPositionConstant n) := by
    unfold hypersurfacePositionedAuxiliaryConstant; positivity
  refine hbound.trans ((mul_le_mul_of_nonneg_left htr hC).trans_eq ?_)
  unfold hypersurfaceAuxiliaryDegreeBound hypersurfaceAbsoluteAuxiliaryConstant
  ring

end
end CCDN
