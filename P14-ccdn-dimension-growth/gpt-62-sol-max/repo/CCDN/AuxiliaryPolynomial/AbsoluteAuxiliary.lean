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
`(d + 1) B`. The normalized determinant comparison retains the geometric
bad-prime factor, which is invariant under the translation.

The geometric bad-prime predicate is invariant under integral shears.

The box enlargement by d+1 costs only a dimension constant in the
auxiliary degree, with no added power of d in its leading term.
-/

@[expose] public section
namespace CCDN
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
    have hg0 : homogeneousTranslation ℤ a f ≠ 0 := by
      simp_all
    rw [homogeneous_hypersurfaceBadReduction_iff _ (homogeneousTranslation_homogeneous a hf) hg0,
      homogeneous_hypersurfaceBadReduction_iff _ hf hf0, homogeneousTranslation_map]
    exact not_congr (MulEquiv.irreducible_iff
      (f := homogeneousTranslation (AlgebraicClosure (ZMod p)) ((Int.castRingHom _) ∘ a)))
  · constructor <;> intro h <;> exact (hp h.1).elim

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- The dimension constant $(5(n + 2) + 5)(n + 2)$ of the positioning step: after a suitable
homogeneous translation, the logarithm of the coefficient height exceeds that of the
lexicographic leading coefficient by at most this constant times $d^{1 + 1/(n + 1)}$. -/
def hypersurfaceAuxiliaryPositionConstant (n : ℕ) : ℝ := (5 * (n + 2 : ℝ) + 5) * (n + 2 : ℝ)

/-- The cost of enlarging the box by a factor of `d + 1`. -/
abbrev projectiveAuxiliaryBoxLoss (n : ℕ) : ℝ := Real.exp ((n + 2 : ℝ) / (n + 1 : ℝ) * (n + 2 : ℝ))

/-- The dimension constant in the absolutely irreducible case of CCDN Theorem 3.1.1 for forms
in `n + 3` variables: the positioned constant times a factor absorbing the enlargement of the
box from `B` to `(d + 1) B` and the passage to the original coefficient height. -/
def hypersurfaceAbsoluteAuxiliaryConstant (n : ℕ) : ℝ :=
  hypersurfacePositionedAuxiliaryConstant n (hypersurfaceAuxiliaryPositionConstant n) *
    (projectiveAuxiliaryBoxLoss n + (n + 3 : ℝ))

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

private lemma irreducible_map_homogeneousTranslation {K : Type*} [Field K] (a : Fin (n + 2) → ℤ)
    {f : MvPolynomial (Fin (n + 3)) ℤ} (hir : Irreducible (map (Int.castRingHom K) f)) :
    Irreducible (map (Int.castRingHom K) (homogeneousTranslation ℤ a f)) := by
  rw [homogeneousTranslation_map]
  exact (MulEquiv.irreducible_iff (homogeneousTranslation K (⇑(Int.castRingHom K) ∘ a))).mpr hir

/-- Evaluating the homogeneous translate of `f` by `a` at the point translated by `-a` gives
the value of `f` at the original point. -/
lemma eval_homogeneousTranslation_neg (a : Fin (n + 2) → ℤ)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (z : IntPoint (n + 3)) :
    eval (homogeneousPointTranslation (-a) z) (homogeneousTranslation ℤ a f) = eval z f := by
  rw [homogeneousTranslation_eval]
  change eval (homogeneousPointTranslation a (homogeneousPointTranslation (-a) z)) f = _
  have he := homogeneousPointTranslation_inverse (-a) z
  simp_all

/-- A form `g` not divisible by the translate of `f` translates back to a
nonmultiple of `f`. -/
private lemma not_dvd_homogeneousTranslation_neg (a : Fin (n + 2) → ℤ)
    {f g : MvPolynomial (Fin (n + 3)) ℤ} (hgnd : ¬homogeneousTranslation ℤ a f ∣ g) :
    ¬f ∣ homogeneousTranslation ℤ (-a) g := by
  intro hdvd
  apply hgnd
  have hh := map_dvd (homogeneousTranslation ℤ a).toRingEquiv.toRingHom hdvd
  exact ((homogeneousTranslation ℤ a).apply_symm_apply g) ▸ hh

end Translation

/-- Enlarging the box from `B` to `(d + 1) B` and lowering the coefficient height from
`H` to `h ≤ H` cost a factor depending only on the dimension. -/
private lemma auxDegreeBound_translate_le {n d : ℕ} (hd : 0 < d) {B b H h : ℝ} (hB : 1 ≤ B)
    (hb : 0 ≤ b) (hh0 : 0 < h) (hhH : h ≤ H) :
    auxDegreeBound n d (((d : ℝ) + 1) * B) b H ≤
      (projectiveAuxiliaryBoxLoss n + (n + 3 : ℝ)) * auxDegreeBound n d B b h := by
  let E := projectiveAuxiliaryBoxLoss n
  let D := auxDegreeScale n d
  let l := auxLogTerm n d B
  let Q := auxMainTerm n d B b h
  let R := ((d : ℝ) + 1) * B
  have hB0 : 0 < B := by linarith
  have hE : 0 ≤ E := by positivity
  have hQ : 0 ≤ Q := by dsimp [Q, auxMainTerm]; positivity
  have hl : 0 ≤ l := by dsimp only [l, auxLogTerm]; have := Real.log_nonneg hB; positivity
  have hH0 := hh0.trans_le hhH
  have hfactor : ((d : ℝ) + 1) ^ boxExponent n d ≤ E := degreeRoot_weight_power_le hd (by positivity)
  have hmain : auxMainTerm n d R b H ≤ E * Q := by
    unfold Q auxMainTerm
    change auxDegreeScale n d * (((d : ℝ) + 1) * B) ^ boxExponent n d * _ ≤ _
    rw [Real.mul_rpow (by positivity) hB0.le]
    calc
      _ ≤ D * (E * B ^ boxExponent n d) * (b / h ^ heightExponent n d) := by gcongr
      _ = _ := by dsimp only [D]; ring
  have hlog : auxLogTerm n d R ≤ l + (n + 2 : ℝ) * D := by
    have h := (div_le_iff₀ (show 0 < degreeRoot n d by positivity)).mpr (log_nat_add_one_le_degreeRoot hd)
    have h' := mul_le_mul (le_auxDegreeScale hd) h
      (div_nonneg (Real.log_nonneg (by simp)) (by positivity)) (show 0 ≤ D by positivity)
    dsimp only [R, l, auxLogTerm]
    rw [Real.log_mul (by positivity) hB0.ne', mul_add, add_div, mul_div_assoc]
    linarith
  change auxMainTerm n d R b H + auxLogTerm n d R + D ≤ (E + (n + 3 : ℝ)) * (Q + l + D)
  nlinarith only [hmain, hlog, mul_nonneg (show 0 ≤ (n + 3 : ℝ) by positivity) hQ,
    mul_nonneg (show 0 ≤ E + (n + 2 : ℝ) by positivity) hl,
    mul_nonneg hE (show 0 ≤ D by positivity)]

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
  have hf0 := ne_zero_of_irreducible_map hir
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  obtain ⟨a, H, ha, hH, hcf, hcg, hpos⟩ := exists_hypersurface_coefficient_position
    (r := n + 1) (by omega) hd f hf hf0
  let model := homogeneousTranslation ℤ a f
  let w := fun i => homogeneousPointTranslation (-a) (z i)
  have hposition : Real.log H ≤ Real.log |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| +
      hypersurfaceAuxiliaryPositionConstant n * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    simpa only [hypersurfaceAuxiliaryPositionConstant, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, hnR] using hpos
  have hirm : Irreducible (map (Int.castRingHom K) model) :=
    irreducible_map_homogeneousTranslation a hir
  have hm0 := ne_zero_of_irreducible_map hirm
  have hhm := homogeneousTranslation_homogeneous a hf
  have hdeg := hhm.totalDegree hm0
  obtain ⟨bad, hbad, hcharge⟩ := exists_fin_hypersurface_bad_prime_charge model hirm
    (hdeg ▸ hd) H hH hcg
  rw [hdeg] at hbad hcharge
  have hcomp := hypersurface_auxiliaryRankComparison MonomialOrder.lex model hhm hm0 hd w
    (fun i => (homogeneousPointTranslation_gcd (-a) (z i)).trans (hprim i))
    (fun i => (eval_homogeneousTranslation_neg a f (z i)).trans (hz i)) bad hbad
  obtain ⟨M, hbound, g, hg0, hgh, hgz, hgnd⟩ := positioned_auxiliary_degree_of_comparison
    MonomialOrder.lex model hm0 hd H hH hcg w
    (one_le_mul_of_one_le_of_one_le (by simp) hB)
    (fun i j => homogeneousPointTranslation_box hB a ha (z i) (hbox i) j) bad hcomp hcharge
    (hypersurfaceAuxiliaryPositionConstant n)
    (by unfold hypersurfaceAuxiliaryPositionConstant; positivity) hposition
  refine ⟨bad, M, fun p => (hbad p).trans
    (and_congr_right fun _ => hypersurfaceBadReduction_homogeneousTranslation f hf hf0 a p),
    ?_, homogeneousTranslation ℤ (-a) g,
    (homogeneousTranslation ℤ (-a)).injective.ne (by simpa using hg0),
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

end
end CCDN
