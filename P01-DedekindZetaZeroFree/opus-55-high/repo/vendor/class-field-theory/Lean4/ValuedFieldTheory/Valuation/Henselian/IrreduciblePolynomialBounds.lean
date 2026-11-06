module

public import ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
public import Mathlib.Algebra.Polynomial.Div

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# reduction input for the coefficient estimate

This file isolates the residue-polynomial input used in the
irreducible-polynomial coefficient estimate.  For the closed-unit-ball valuation ring attached to a nonarchimedean
absolute value, coefficients of value `< 1` reduce to zero and coefficients of
value `1` reduce to nonzero elements.  Hence the first coefficient of value
`1` gives the exact initial `X`-power dividing the reduced polynomial.
-/


open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- reduction input: a coefficient of absolute value `< 1`
reduces to the zero coefficient of the residue polynomial. -/
theorem irreduciblePolynomial_reduction_coeff_eq_zero_of_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {i : ℕ} (hi : v (F.coeff i : K) < 1) :
    (F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch))).coeff i =
      0 := by
  rw [Polynomial.coeff_map]
  exact
    (absoluteValueUnitBallSubringAsValuationSubring_residue_eq_zero_iff_abs_lt_one
      v hnonarch (F.coeff i)).2 hi

/-- reduction input: a coefficient of absolute value `1`
reduces to a nonzero coefficient of the residue polynomial. -/
theorem irreduciblePolynomial_reduction_coeff_ne_zero_of_abs_eq_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {i : ℕ} (hi : v (F.coeff i : K) = 1) :
    (F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch))).coeff i ≠
      0 := by
  rw [Polynomial.coeff_map]
  exact
    (absoluteValueUnitBallSubringAsValuationSubring_residue_ne_zero_iff_abs_eq_one
      v hnonarch (F.coeff i)).2 hi

/-- reduction input: if all coefficients below `r` have
absolute value `< 1`, then `X^r` divides the reduced polynomial. -/
theorem irreduciblePolynomial_reduction_X_pow_dvd_of_initial_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ} (hinit : ∀ i : ℕ, i < r → v (F.coeff i : K) < 1) :
    Polynomial.X ^ r ∣
      F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro i hi
  exact irreduciblePolynomial_reduction_coeff_eq_zero_of_abs_lt_one
    v hnonarch F (hinit i hi)

/-- reduction input: if `r` is the first coefficient with
absolute value `1`, then the reduced polynomial is divisible by exactly
`X^r` at the origin. -/
theorem irreduciblePolynomial_reduction_exact_X_pow_of_first_abs_eq_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ} (hinit : ∀ i : ℕ, i < r → v (F.coeff i : K) < 1)
    (hr : v (F.coeff r : K) = 1) :
    Polynomial.X ^ r ∣
        F.map (IsLocalRing.residue
          (absoluteValueValuationSubring v hnonarch)) ∧
      ¬ Polynomial.X ^ (r + 1) ∣
        F.map (IsLocalRing.residue
          (absoluteValueValuationSubring v hnonarch)) := by
  constructor
  · exact irreduciblePolynomial_reduction_X_pow_dvd_of_initial_abs_lt_one
      v hnonarch F hinit
  · intro hdiv
    have hcoeff_zero :
        (F.map (IsLocalRing.residue
          (absoluteValueValuationSubring v hnonarch))).coeff r =
          0 := by
      rw [Polynomial.X_pow_dvd_iff] at hdiv
      exact hdiv r (Nat.lt_succ_self r)
    exact (irreduciblePolynomial_reduction_coeff_ne_zero_of_abs_eq_one
      v hnonarch F hr) hcoeff_zero

/-- reduction input: from any coefficient of value `1`, choose
the first such coefficient.  Every earlier coefficient then has value `< 1`
because all coefficients already lie in the closed unit ball. -/
theorem irreduciblePolynomial_exists_first_abs_eq_one_coeff
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {n : ℕ} (hn : v (F.coeff n : K) = 1) :
    ∃ r : ℕ,
      v (F.coeff r : K) = 1 ∧
        ∀ i : ℕ, i < r → v (F.coeff i : K) < 1 := by
  classical
  let P : ℕ → Prop := fun i => v (F.coeff i : K) = 1
  have hex : ∃ i : ℕ, P i := ⟨n, hn⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro i hi
  have hne : v (F.coeff i : K) ≠ 1 :=
    Nat.find_min hex hi
  have hle : v (F.coeff i : K) ≤ 1 :=
    (mem_absoluteValueValuationSubring_iff
      v hnonarch (F.coeff i : K)).1 (F.coeff i).property
  exact lt_of_le_of_ne hle hne

/-- reduction input: if some coefficient has value `1`, then
the reduced polynomial has an exact initial `X^r` divisor for the first such
coefficient `r`. -/
theorem irreduciblePolynomial_exists_exact_X_pow_reduction_of_abs_eq_one_coeff
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {n : ℕ} (hn : v (F.coeff n : K) = 1) :
    ∃ r : ℕ,
      v (F.coeff r : K) = 1 ∧
        Polynomial.X ^ r ∣
            F.map (IsLocalRing.residue
              (absoluteValueValuationSubring v hnonarch)) ∧
          ¬ Polynomial.X ^ (r + 1) ∣
            F.map (IsLocalRing.residue
              (absoluteValueValuationSubring v hnonarch)) := by
  rcases irreduciblePolynomial_exists_first_abs_eq_one_coeff v hnonarch F hn with
    ⟨r, hr, hinit⟩
  exact ⟨r, hr,
    irreduciblePolynomial_reduction_exact_X_pow_of_first_abs_eq_one
      v hnonarch F hinit hr⟩

/-- reduction input: if the degree-zero coefficient has absolute
value `< 1`, then the first coefficient of value `1` has positive index. -/
theorem irreduciblePolynomial_first_abs_eq_one_index_pos_of_const_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ} (hconst : v (F.coeff 0 : K) < 1)
    (hr : v (F.coeff r : K) = 1) :
    0 < r := by
  refine Nat.pos_of_ne_zero ?_
  intro hr0
  simp_all

/-- A coefficient whose absolute value is `1` is nonzero.  This small
field-level fact is used repeatedly when passing from coefficient estimates to
degree bounds. -/
theorem irreduciblePolynomial_coeff_ne_zero_of_abs_eq_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {i : ℕ} (hi : v (F.coeff i : K) = 1) :
    F.coeff i ≠ 0 := by
  intro hzero
  simp [hzero] at hi

/-- reduction input: if the leading coefficient has absolute
value `< 1`, then a coefficient of value `1` occurs strictly before the
natural degree. -/
theorem irreduciblePolynomial_abs_eq_one_index_lt_natDegree_of_leading_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ} (hlead : v (F.leadingCoeff : K) < 1)
    (hr : v (F.coeff r : K) = 1) :
    r < F.natDegree := by
  have hle : r ≤ F.natDegree :=
    Polynomial.le_natDegree_of_ne_zero
      (irreduciblePolynomial_coeff_ne_zero_of_abs_eq_one v hnonarch F hr)
  have hne : r ≠ F.natDegree := by
    intro hrdeg
    simp_all
  omega

/-- reduction input: exact `X^r` divisibility rewrites the
reduced polynomial as `X^r` times its monic quotient. -/
theorem irreduciblePolynomial_reduction_eq_X_pow_mul_divByMonic_of_X_pow_dvd
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ}
    (hdiv : Polynomial.X ^ r ∣
      F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch))) :
    F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) =
      Polynomial.X ^ r *
        (F.map (IsLocalRing.residue
          (absoluteValueValuationSubring v hnonarch)) /ₘ
            Polynomial.X ^ r) := by
  let P :=
    F.map (IsLocalRing.residue
      (absoluteValueValuationSubring v hnonarch))
  have hmonic : (Polynomial.X ^ r :
      (IsLocalRing.ResidueField
        (absoluteValueValuationSubring v hnonarch))[X]).Monic :=
    Polynomial.monic_X_pow r
  have hmod : P %ₘ Polynomial.X ^ r = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).2 hdiv
  have hdecomp := Polynomial.modByMonic_add_div P (Polynomial.X ^ r)
  rw [hmod, zero_add] at hdecomp
  simpa [P] using hdecomp.symm

/-- reduction input: exact nondivisibility by `X^(r+1)` says
that the monic quotient by `X^r` has nonzero degree-zero coefficient. -/
theorem irreduciblePolynomial_reduction_divByMonic_X_pow_coeff_zero_ne_zero
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ}
    (hdiv : Polynomial.X ^ r ∣
      F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)))
    (hnotdiv : ¬ Polynomial.X ^ (r + 1) ∣
      F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch))) :
    ((F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r).coeff 0) ≠ 0 := by
  let P :=
    F.map (IsLocalRing.residue
      (absoluteValueValuationSubring v hnonarch))
  let Q := P /ₘ Polynomial.X ^ r
  have hfac : P = Polynomial.X ^ r * Q := by
    simpa [P, Q] using
      irreduciblePolynomial_reduction_eq_X_pow_mul_divByMonic_of_X_pow_dvd
        v hnonarch F hdiv
  intro hQ0
  have hXdvdQ : Polynomial.X ∣ Q := by
    rw [Polynomial.X_dvd_iff]
    exact hQ0
  rcases hXdvdQ with ⟨T, hT⟩
  apply hnotdiv
  refine ⟨T, ?_⟩
  calc
    P = Polynomial.X ^ r * Q := hfac
    _ = Polynomial.X ^ r * (Polynomial.X * T) := by rw [hT]
    _ = Polynomial.X ^ (r + 1) * T := by
      rw [pow_succ, mul_assoc]

/-- Hensel input: if the quotient after removing the exact
initial `X^r` factor has nonzero degree-zero coefficient, then it is coprime
to `X^r`. -/
theorem irreduciblePolynomial_reduction_X_pow_isCoprime_divByMonic_of_coeff_zero_ne_zero
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ}
    (hQ0 :
      ((F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r).coeff 0) ≠ 0) :
    IsCoprime (Polynomial.X ^ r)
      (F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r) := by
  let P :=
    F.map (IsLocalRing.residue
      (absoluteValueValuationSubring v hnonarch))
  let Q := P /ₘ Polynomial.X ^ r
  have hnotX :
      ¬ (Polynomial.X :
          (IsLocalRing.ResidueField
            (absoluteValueValuationSubring v hnonarch))[X]) ∣
        Q := by
    intro hX
    exact hQ0 (by
      simpa [P, Q] using (Polynomial.X_dvd_iff.mp hX))
  have hcopX :
      IsCoprime
        (Polynomial.X :
          (IsLocalRing.ResidueField
            (absoluteValueValuationSubring v hnonarch))[X])
        Q := by
    exact
      (Polynomial.prime_X
        (R := IsLocalRing.ResidueField
          (absoluteValueValuationSubring v hnonarch))).coprime_iff_not_dvd.2
        hnotX
  simpa [P, Q] using (hcopX.pow_left (m := r))

/-- Hensel input: exact `X^r` divisibility of the reduction
supplies the coprime factor pair `X^r` and the remaining quotient. -/
theorem irreduciblePolynomial_reduction_X_pow_isCoprime_divByMonic_of_exact
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ}
    (hdiv : Polynomial.X ^ r ∣
      F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)))
    (hnotdiv : ¬ Polynomial.X ^ (r + 1) ∣
      F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch))) :
    IsCoprime (Polynomial.X ^ r)
      (F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r) := by
  exact
    irreduciblePolynomial_reduction_X_pow_isCoprime_divByMonic_of_coeff_zero_ne_zero
      v hnonarch F
      (irreduciblePolynomial_reduction_divByMonic_X_pow_coeff_zero_ne_zero
        v hnonarch F hdiv hnotdiv)

/-- reduction input: under the endpoint inequalities used in
the proof, the first coefficient of value `1` gives a nontrivial exact
initial `X^r` divisor with `0 < r < natDegree`. -/
theorem irreduciblePolynomial_exists_nontrivial_exact_X_pow_reduction
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    (hconst : v (F.coeff 0 : K) < 1)
    (hlead : v (F.leadingCoeff : K) < 1)
    {n : ℕ} (hn : v (F.coeff n : K) = 1) :
    ∃ r : ℕ,
      0 < r ∧ r < F.natDegree ∧
        v (F.coeff r : K) = 1 ∧
          Polynomial.X ^ r ∣
              F.map (IsLocalRing.residue
                (absoluteValueValuationSubring v hnonarch)) ∧
            ¬ Polynomial.X ^ (r + 1) ∣
              F.map (IsLocalRing.residue
                (absoluteValueValuationSubring v hnonarch)) := by
  rcases irreduciblePolynomial_exists_exact_X_pow_reduction_of_abs_eq_one_coeff
      v hnonarch F hn with
    ⟨r, hr, hdiv, hnotdiv⟩
  exact ⟨r,
    irreduciblePolynomial_first_abs_eq_one_index_pos_of_const_abs_lt_one
      v hnonarch F hconst hr,
    irreduciblePolynomial_abs_eq_one_index_lt_natDegree_of_leading_abs_lt_one
      v hnonarch F hlead hr,
    hr, hdiv, hnotdiv⟩

/-- Hensel input: under the endpoint inequalities used in the
proof, the reduction has a nontrivial monic factor `X^r`, the remaining
quotient, and these two factors are coprime. -/
theorem irreduciblePolynomial_exists_hensel_reduction_factor_input
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    (hconst : v (F.coeff 0 : K) < 1)
    (hlead : v (F.leadingCoeff : K) < 1)
    {n : ℕ} (hn : v (F.coeff n : K) = 1) :
    ∃ r : ℕ,
      0 < r ∧ r < F.natDegree ∧
        F.map (IsLocalRing.residue
            (absoluteValueValuationSubring v hnonarch)) =
          Polynomial.X ^ r *
            (F.map (IsLocalRing.residue
              (absoluteValueValuationSubring v hnonarch)) /ₘ
                Polynomial.X ^ r) ∧
          (Polynomial.X ^ r :
            (IsLocalRing.ResidueField
              (absoluteValueValuationSubring v hnonarch))[X]).natDegree =
            r ∧
            IsCoprime (Polynomial.X ^ r)
              (F.map (IsLocalRing.residue
                (absoluteValueValuationSubring v hnonarch)) /ₘ
                  Polynomial.X ^ r) ∧
              ((F.map (IsLocalRing.residue
                (absoluteValueValuationSubring v hnonarch)) /ₘ
                  Polynomial.X ^ r).coeff 0) ≠ 0 := by
  rcases irreduciblePolynomial_exists_nontrivial_exact_X_pow_reduction
      v hnonarch F hconst hlead hn with
    ⟨r, hrpos, hrlt, _hr, hdiv, hnotdiv⟩
  refine ⟨r, hrpos, hrlt, ?_, ?_, ?_, ?_⟩
  · exact irreduciblePolynomial_reduction_eq_X_pow_mul_divByMonic_of_X_pow_dvd
      v hnonarch F hdiv
  · exact Polynomial.natDegree_X_pow r
  · exact irreduciblePolynomial_reduction_X_pow_isCoprime_divByMonic_of_exact
      v hnonarch F hdiv hnotdiv
  · exact irreduciblePolynomial_reduction_divByMonic_X_pow_coeff_zero_ne_zero
      v hnonarch F hdiv hnotdiv

/-- field-polynomial input: once a field polynomial has been
normalized so that every coefficient lies in the closed unit ball and one
coefficient has value `1`, the endpoint inequalities produce the same Hensel
reduction factor data after choosing a degree-preserving valuation-ring lift. -/
theorem irreduciblePolynomial_exists_hensel_reduction_factor_input_of_field_coeffs
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (f : K[X])
    (hfcoeff : ∀ i : ℕ, v (f.coeff i) ≤ 1)
    (hconst : v (f.coeff 0) < 1)
    (hlead : v f.leadingCoeff < 1)
    {n : ℕ} (hn : v (f.coeff n) = 1) :
    ∃ F : (absoluteValueValuationSubring v hnonarch)[X],
      ∃ r : ℕ,
        F.map (algebraMap
            (absoluteValueValuationSubring v hnonarch) K) =
          f ∧
        F.natDegree = f.natDegree ∧
          0 < r ∧ r < F.natDegree ∧
            F.map (IsLocalRing.residue
                (absoluteValueValuationSubring v hnonarch)) =
              Polynomial.X ^ r *
                (F.map (IsLocalRing.residue
                  (absoluteValueValuationSubring v hnonarch)) /ₘ
                    Polynomial.X ^ r) ∧
              (Polynomial.X ^ r :
                (IsLocalRing.ResidueField
                  (absoluteValueValuationSubring v hnonarch))[X]).natDegree =
                r ∧
                IsCoprime (Polynomial.X ^ r)
                  (F.map (IsLocalRing.residue
                    (absoluteValueValuationSubring v hnonarch)) /ₘ
                      Polynomial.X ^ r) ∧
                  ((F.map (IsLocalRing.residue
                    (absoluteValueValuationSubring v hnonarch)) /ₘ
                      Polynomial.X ^ r).coeff 0) ≠ 0 := by
  rcases
      exists_polynomial_over_absoluteValueUnitBallSubringAsValuationSubring_of_coeff_abs_le_one
        v hnonarch f hfcoeff with
    ⟨F, hmap, hdegree, hcoeff_abs⟩
  have hconstF : v (F.coeff 0 : K) < 1 := by
    simpa [hcoeff_abs 0] using hconst
  have hleadF : v (F.leadingCoeff : K) < 1 := by
    have hlead_abs :
        v (F.leadingCoeff : K) = v f.leadingCoeff := by
      rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, ← hdegree]
      exact hcoeff_abs F.natDegree
    simpa [hlead_abs] using hlead
  have hnF : v (F.coeff n : K) = 1 := by
    simpa [hcoeff_abs n] using hn
  rcases irreduciblePolynomial_exists_hensel_reduction_factor_input
      v hnonarch F hconstF hleadF hnF with
    ⟨r, hrpos, hrlt, hfactor, hnatDegree, hcoprime, hQ0⟩
  exact
    ⟨F, r, hmap, hdegree, hrpos, hrlt, hfactor, hnatDegree, hcoprime, hQ0⟩

/-- normalization source: a nonzero polynomial has a positive
maximum among the absolute values of its coefficients, attained within the
finite coefficient range up to `natDegree`. -/
theorem irreduciblePolynomial_exists_coeff_abs_max_of_ne_zero
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {f : K[X]} (hf : f ≠ 0) :
    ∃ m : ℝ, ∃ n : ℕ,
      0 < m ∧ n ≤ f.natDegree ∧ v (f.coeff n) = m ∧
        ∀ i : ℕ, v (f.coeff i) ≤ m := by
  classical
  let S : Finset ℕ := Finset.range (f.natDegree + 1)
  let T : Finset ℝ := S.image fun i => v (f.coeff i)
  have hdegmem : f.natDegree ∈ S := by
    simp [S]
  have hT : T.Nonempty := 
    ⟨v (f.coeff f.natDegree),
      Finset.mem_image.mpr ⟨f.natDegree, hdegmem, rfl⟩⟩
  let m : ℝ := T.max' hT
  have hlead_ne : f.leadingCoeff ≠ 0 :=
    (Polynomial.leadingCoeff_ne_zero).2 hf
  have hlead_pos : 0 < v f.leadingCoeff := by
    simp_all
  have hlead_le_m : v f.leadingCoeff ≤ m := by
    have hmem : v (f.coeff f.natDegree) ∈ T :=
      Finset.mem_image.mpr ⟨f.natDegree, hdegmem, rfl⟩
    change v (f.coeff f.natDegree) ≤ m
    exact T.le_max' _ hmem
  have hmpos : 0 < m := hlead_pos.trans_le hlead_le_m
  have hmaxmem : m ∈ T := T.max'_mem hT
  rcases Finset.mem_image.mp hmaxmem with ⟨n, hnS, hnmax⟩
  have hnle : n ≤ f.natDegree := 
    Nat.lt_succ_iff.mp (by simpa [S] using hnS)
  refine ⟨m, n, hmpos, hnle, hnmax, ?_⟩
  intro i
  by_cases hi : i ≤ f.natDegree
  · have hiS : i ∈ S := by
      simp [S, Nat.lt_succ_of_le hi]
    have himem : v (f.coeff i) ∈ T :=
      Finset.mem_image.mpr ⟨i, hiS, rfl⟩
    exact T.le_max' _ himem
  · have hlt : f.natDegree < i := Nat.lt_of_not_ge hi
    have hzero : f.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    rw [hzero, map_zero]
    exact hmpos.le

/-- normalization source: dividing a nonzero polynomial by a
coefficient whose absolute value is the positive coefficient maximum preserves
degree, puts every coefficient in the closed unit ball, and makes that chosen
coefficient have value `1`. -/
theorem irreduciblePolynomial_scale_by_max_coeff_abs_data
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hbound : ∀ i : ℕ, v (f.coeff i) ≤ m) :
    let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
    g.natDegree = f.natDegree ∧
      (∀ i : ℕ, v (g.coeff i) = m⁻¹ * v (f.coeff i)) ∧
        (∀ i : ℕ, v (g.coeff i) ≤ 1) ∧
          v (g.coeff n) = 1 := by
  let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
  have hmne : m ≠ 0 := ne_of_gt hmpos
  have hn_ne : f.coeff n ≠ 0 := by
    intro hzero
    simp_all
  have hdegree : g.natDegree = f.natDegree := by
    dsimp [g]
    exact Polynomial.natDegree_C_mul (p := f) (a0 := inv_ne_zero hn_ne)
  have hcoeff_abs : ∀ i : ℕ, v (g.coeff i) = m⁻¹ * v (f.coeff i) := by
    intro i
    dsimp [g]
    simp_all
  have hcoeff_le : ∀ i : ℕ, v (g.coeff i) ≤ 1 := by
    intro i
    rw [hcoeff_abs i]
    calc
      m⁻¹ * v (f.coeff i) ≤ m⁻¹ * m :=
        mul_le_mul_of_nonneg_left (hbound i) (inv_nonneg.mpr hmpos.le)
      _ = 1 := inv_mul_cancel₀ hmne
  have hn_one : v (g.coeff n) = 1 := by
    simp_all
  exact ⟨hdegree, hcoeff_abs, hcoeff_le, hn_one⟩

/-- normalization source: if the original constant and
leading coefficients are strictly smaller than the coefficient maximum, then
after scaling by a maximum coefficient they are strictly inside the open unit
ball. -/
theorem irreduciblePolynomial_normalized_scale_endpoint_abs_lt_one
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {f g : K[X]} {m : ℝ}
    (hmpos : 0 < m)
    (hdegree : g.natDegree = f.natDegree)
    (hcoeff_abs : ∀ i : ℕ, v (g.coeff i) = m⁻¹ * v (f.coeff i))
    (hconst : v (f.coeff 0) < m)
    (hlead : v f.leadingCoeff < m) :
    v (g.coeff 0) < 1 ∧ v g.leadingCoeff < 1 := by
  have hmne : m ≠ 0 := ne_of_gt hmpos
  constructor
  · rw [hcoeff_abs 0]
    calc
      m⁻¹ * v (f.coeff 0) < m⁻¹ * m :=
        mul_lt_mul_of_pos_left hconst (inv_pos.mpr hmpos)
      _ = 1 := inv_mul_cancel₀ hmne
  · have hlead_abs :
        v g.leadingCoeff = m⁻¹ * v f.leadingCoeff := by
      rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, ← hdegree]
      exact hcoeff_abs g.natDegree
    rw [hlead_abs]
    calc
      m⁻¹ * v f.leadingCoeff < m⁻¹ * m :=
        mul_lt_mul_of_pos_left hlead (inv_pos.mpr hmpos)
      _ = 1 := inv_mul_cancel₀ hmne

/-- normalized Hensel input: after scaling by a coefficient
that attains the positive coefficient maximum, strict endpoint bounds below
that maximum give the exact Hensel reduction factor input for the scaled
polynomial. -/
theorem irreduciblePolynomial_normalized_scale_hensel_reduction_factor_input
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hbound : ∀ i : ℕ, v (f.coeff i) ≤ m)
    (hconst : v (f.coeff 0) < m)
    (hlead : v f.leadingCoeff < m) :
    let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
    ∃ F : (absoluteValueValuationSubring v hnonarch)[X],
      ∃ r : ℕ,
        F.map (algebraMap
            (absoluteValueValuationSubring v hnonarch) K) =
          g ∧
        F.natDegree = g.natDegree ∧
          0 < r ∧ r < F.natDegree ∧
            F.map (IsLocalRing.residue
                (absoluteValueValuationSubring v hnonarch)) =
              Polynomial.X ^ r *
                (F.map (IsLocalRing.residue
                  (absoluteValueValuationSubring v hnonarch)) /ₘ
                    Polynomial.X ^ r) ∧
              (Polynomial.X ^ r :
                (IsLocalRing.ResidueField
                  (absoluteValueValuationSubring v hnonarch))[X]).natDegree =
                r ∧
                IsCoprime (Polynomial.X ^ r)
                  (F.map (IsLocalRing.residue
                    (absoluteValueValuationSubring v hnonarch)) /ₘ
                      Polynomial.X ^ r) ∧
                  ((F.map (IsLocalRing.residue
                    (absoluteValueValuationSubring v hnonarch)) /ₘ
                      Polynomial.X ^ r).coeff 0) ≠ 0 := by
  let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
  rcases irreduciblePolynomial_scale_by_max_coeff_abs_data
      v hmpos hnmax hbound with
    ⟨hdegree, hcoeff_abs, hcoeff_le, hn_one⟩
  rcases irreduciblePolynomial_normalized_scale_endpoint_abs_lt_one
      v hmpos hdegree hcoeff_abs hconst hlead with
    ⟨hconstg, hleadg⟩
  exact
    irreduciblePolynomial_exists_hensel_reduction_factor_input_of_field_coeffs
      v hnonarch g hcoeff_le hconstg hleadg hn_one
