module

public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/









set_option autoImplicit false

/-!
# Ray class groups of the rational numbers

This file computes ray class groups of the rational numbers. A positive integer
`m` determines a full narrow ray modulus: its finite part has exponent
`m.factorization p` at `p`, and its real place imposes positivity. The
positive generator of an ideal prime to this modulus gives the explicit
isomorphism with `(ZMod m)ˣ`.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section


namespace RayClass

local instance rationalRingOfIntegersIsPrincipalIdealRing :
    IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm
    Rat.ringOfIntegersEquiv.symm.surjective

local instance rationalNatGeneratorPrimeFact
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.natGenerator v)) :=
  ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩

local instance rationalPrimesEquivPrimeFact
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact
      (Nat.Prime
        ((Rat.HeightOneSpectrum.primesEquiv
          (R := 𝓞 ℚ) v : Nat.Primes) : ℕ)) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv
    (R := 𝓞 ℚ) v).property⟩

/-- The height-one prime of `𝓞 ℚ` associated with a natural prime. -/
noncomputable abbrev rationalPrime (p : Nat.Primes) :
    HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p

@[simp]
theorem natGenerator_rationalPrime (p : Nat.Primes) :
    Rat.HeightOneSpectrum.natGenerator (rationalPrime p) = p := by
  exact congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)

theorem rational_natGenerator_injective :
    Function.Injective
      (Rat.HeightOneSpectrum.natGenerator :
        HeightOneSpectrum (𝓞 ℚ) → ℕ) := by
  intro v w hvw
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext hvw

/-- The finite part of the modulus `(m)` of `ℚ`.  At the prime over `p` it has
exponent `m.factorization p`. The later equivalences use the hypothesis
`0 < m`; the definition itself is harmless at `m = 0`.
-/
noncomputable def rationalFiniteModulus (m : ℕ) : FiniteModulus ℚ :=
  Finsupp.comapDomain
    Rat.HeightOneSpectrum.natGenerator
    m.factorization
    rational_natGenerator_injective.injOn

@[simp]
theorem rationalFiniteModulus_apply
    (m : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    rationalFiniteModulus m v =
      m.factorization (Rat.HeightOneSpectrum.natGenerator v) := rfl

/-- The full rational ray modulus has the finite part `(m)` and positivity
at the unique real place. -/
noncomputable def rationalModulus (m : ℕ) : Modulus ℚ :=
  Modulus.narrowOfFinite (rationalFiniteModulus m)

@[simp]
theorem rationalModulus_finitePart_apply
    (m : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (rationalModulus m).finitePart v =
      m.factorization (Rat.HeightOneSpectrum.natGenerator v) := rfl

theorem mem_rationalFiniteModulus_support_iff
    {m : ℕ} (hm : m ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ (rationalFiniteModulus m).support ↔
      Rat.HeightOneSpectrum.natGenerator v ∣ m := by
  rw [Finsupp.mem_support_iff, rationalFiniteModulus_apply]
  constructor
  · exact Nat.dvd_of_factorization_pos
  · intro hdiv
    exact (Rat.HeightOneSpectrum.prime_natGenerator v).factorization_pos_of_dvd hm hdiv |>.ne'

/-- The fractional ideal underlying a rational fractional-ideal unit. -/
abbrev rationalFractionalIdeal (I : FractionalIdealGroup ℚ) :
    FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ :=
  I

/-- An arbitrary principal generator of a nonzero rational fractional
ideal, before choosing its sign. -/
 noncomputable def rawRationalIdealGenerator
    (I : FractionalIdealGroup ℚ) : ℚ :=
  Submodule.IsPrincipal.generator
    ((rationalFractionalIdeal I : FractionalIdeal
      (nonZeroDivisors (𝓞 ℚ)) ℚ) : Submodule (𝓞 ℚ) ℚ)

private theorem rawRationalIdealGenerator_ne_zero
    (I : FractionalIdealGroup ℚ) :
    rawRationalIdealGenerator I ≠ 0 := by
  apply mt
    (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero
      ((rationalFractionalIdeal I : FractionalIdeal
        (nonZeroDivisors (𝓞 ℚ)) ℚ) : Submodule (𝓞 ℚ) ℚ)).2
  exact FractionalIdeal.coeToSubmodule_ne_bot.mpr (Units.ne_zero I)

/-- The unique positive generator of a nonzero rational fractional ideal. -/
noncomputable def positiveRationalIdealGenerator
    (I : FractionalIdealGroup ℚ) : ℚ :=
  if 0 < rawRationalIdealGenerator I then
    rawRationalIdealGenerator I
  else
    -rawRationalIdealGenerator I

theorem positiveRationalIdealGenerator_pos
    (I : FractionalIdealGroup ℚ) :
    0 < positiveRationalIdealGenerator I := by
  rw [positiveRationalIdealGenerator]
  split_ifs with h
  · exact h
  · exact neg_pos.mpr
      (lt_of_le_of_ne (not_lt.mp h)
        (rawRationalIdealGenerator_ne_zero I))

theorem rationalFractionalIdeal_eq_span_positiveGenerator
    (I : FractionalIdealGroup ℚ) :
    rationalFractionalIdeal I =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
        (positiveRationalIdealGenerator I) := by
  calc
    rationalFractionalIdeal I =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
          (rawRationalIdealGenerator I) :=
      FractionalIdeal.eq_spanSingleton_of_principal _
    _ = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
          (positiveRationalIdealGenerator I) := by
      rw [positiveRationalIdealGenerator]
      split_ifs with h
      · rfl
      · apply
          (FractionalIdeal.spanSingleton_eq_spanSingleton
            (S := nonZeroDivisors (𝓞 ℚ))).2
        refine ⟨-1, ?_⟩
        simp

/-- Positive rational generators of the same principal fractional ideal
are equal. -/
theorem eq_of_spanSingleton_eq_of_pos
    {x y : ℚ} (hx : 0 < x) (hy : 0 < y)
    (h :
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ)) x =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ)) y) :
    x = y := by
  obtain ⟨u, hu⟩ :=
    (FractionalIdeal.spanSingleton_eq_spanSingleton
      (S := nonZeroDivisors (𝓞 ℚ))).1 h
  rcases Rat.RingOfIntegers.isUnit_iff.mp u.isUnit with hu1 | hu1
  · simp_all
  · have hxy : -x = y := by
      simpa [Units.smul_def, Algebra.smul_def, hu1] using hu
    linarith

@[simp]
theorem positiveRationalIdealGenerator_one :
    positiveRationalIdealGenerator (1 : FractionalIdealGroup ℚ) = 1 := by
  apply eq_of_spanSingleton_eq_of_pos
    (positiveRationalIdealGenerator_pos 1) zero_lt_one
  rw [← rationalFractionalIdeal_eq_span_positiveGenerator]
  exact FractionalIdeal.spanSingleton_one.symm

theorem positiveRationalIdealGenerator_mul
    (I J : FractionalIdealGroup ℚ) :
    positiveRationalIdealGenerator (I * J) =
      positiveRationalIdealGenerator I *
        positiveRationalIdealGenerator J := by
  apply eq_of_spanSingleton_eq_of_pos
    (positiveRationalIdealGenerator_pos (I * J))
    (mul_pos (positiveRationalIdealGenerator_pos I)
      (positiveRationalIdealGenerator_pos J))
  rw [← rationalFractionalIdeal_eq_span_positiveGenerator,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← rationalFractionalIdeal_eq_span_positiveGenerator,
    ← rationalFractionalIdeal_eq_span_positiveGenerator]
  rfl

/-- The positive generator, regarded as a nonzero rational number. -/
noncomputable def positiveRationalIdealGeneratorUnit
    (I : FractionalIdealGroup ℚ) : ℚˣ :=
  Units.mk0 (positiveRationalIdealGenerator I)
    (ne_of_gt (positiveRationalIdealGenerator_pos I))

@[simp]
theorem positiveRationalIdealGeneratorUnit_val
    (I : FractionalIdealGroup ℚ) :
    (positiveRationalIdealGeneratorUnit I : ℚ) =
      positiveRationalIdealGenerator I :=
  rfl

theorem toPrincipalIdeal_positiveRationalIdealGeneratorUnit
    (I : FractionalIdealGroup ℚ) :
    toPrincipalIdeal (𝓞 ℚ) ℚ
        (positiveRationalIdealGeneratorUnit I) = I := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ℚ))
        (positiveRationalIdealGenerator I) =
      rationalFractionalIdeal I
  exact (rationalFractionalIdeal_eq_span_positiveGenerator I).symm

@[simp]
theorem positiveRationalIdealGeneratorUnit_one :
    positiveRationalIdealGeneratorUnit
      (1 : FractionalIdealGroup ℚ) = 1 := by
  apply Units.ext
  exact positiveRationalIdealGenerator_one


/-- An element of `WithZero (Multiplicative ℤ)` with logarithm zero is
one. -/
theorem withZero_eq_one_of_log_eq_zero
    {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0)
    (hlog : WithZero.log x = 0) :
    x = 1 := by
  calc
    x = WithZero.exp (WithZero.log x) :=
      (WithZero.exp_log hx).symm
    _ = WithZero.exp 0 := congrArg WithZero.exp hlog
    _ = 1 := rfl

/-- Zero principal-ideal exponent at a rational finite place forces
valuation one. -/
theorem valuation_eq_one_of_principal_count_eq_zero
    (x : ℚˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (hcount :
      FractionalIdeal.count ℚ v
        (toPrincipalIdeal (𝓞 ℚ) ℚ x :
          FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ) = 0) :
    v.valuation ℚ (x : ℚ) = 1 := by
  rw [IdeleGroup.count_toPrincipalIdeal] at hcount
  have hlog :
      WithZero.log (v.valuation ℚ (x : ℚ)) = 0 :=
    neg_eq_zero.mp hcount
  have hvne : v.valuation ℚ (x : ℚ) ≠ 0 :=
    (v.valuation ℚ).ne_zero_of_unit x
  exact withZero_eq_one_of_log_eq_zero hvne hlog

/-- A rational prime with zero principal-ideal exponent does not divide
the denominator. -/
theorem not_dvd_den_of_principal_count_eq_zero
    (x : ℚˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (hcount :
      FractionalIdeal.count ℚ v
        (toPrincipalIdeal (𝓞 ℚ) ℚ x :
          FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ) = 0) :
    ¬ Rat.HeightOneSpectrum.natGenerator v ∣ (x : ℚ).den := by
  let p := Rat.HeightOneSpectrum.natGenerator v
  let : Fact p.Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hequiv :=
    Rat.HeightOneSpectrum.valuation_equiv_padicValuation v
  have hpval : Rat.padicValuation p (x : ℚ) = 1 :=
    hequiv.eq_one_iff_eq_one.mp
      (valuation_eq_one_of_principal_count_eq_zero x v hcount)
  apply Rat.padicValuation_le_one_iff.mp
  exact le_of_eq hpval

/-- A rational prime with zero principal-ideal exponent does not divide
the numerator. -/
theorem not_dvd_num_of_principal_count_eq_zero
    (x : ℚˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (hcount :
      FractionalIdeal.count ℚ v
        (toPrincipalIdeal (𝓞 ℚ) ℚ x :
          FractionalIdeal (nonZeroDivisors (𝓞 ℚ)) ℚ) = 0) :
    ¬ Rat.HeightOneSpectrum.natGenerator v ∣ (x : ℚ).num.natAbs := by
  let p := Rat.HeightOneSpectrum.natGenerator v
  let : Fact p.Prime :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  have hpval :
      Rat.padicValuation p (x : ℚ) = 1 :=
    (Rat.HeightOneSpectrum.valuation_equiv_padicValuation v).eq_one_iff_eq_one.mp
      (valuation_eq_one_of_principal_count_eq_zero x v hcount)
  have hden : ¬ p ∣ (x : ℚ).den :=
    not_dvd_den_of_principal_count_eq_zero x v hcount
  have hdenval :
      Int.padicValuation p ((x : ℚ).den : ℤ) = 1 :=
    Int.padicValuation_eq_one_iff.mpr
      (by simpa only [Int.natCast_dvd_natCast] using hden)
  rw [← (x : ℚ).num_div_den, map_div₀,
    Rat.padicValuation_cast, ← Int.cast_natCast,
    Rat.padicValuation_cast, hdenval, div_one] at hpval
  exact fun hpdiv =>
    (Int.padicValuation_eq_one_iff.mp hpval)
      (Int.natCast_dvd.mpr hpdiv)

theorem positiveGenerator_den_coprime
    {m : ℕ} (hm : m ≠ 0)
    (I : primeToModulusIdeals (rationalModulus m)) :
    Nat.Coprime
      (positiveRationalIdealGenerator (I : FractionalIdealGroup ℚ)).den m := by
  rw [Nat.coprime_comm]
  by_contra hcop
  obtain ⟨p, hp, hpm, hpden⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hcop
  let v := rationalPrime ⟨p, hp⟩
  have hvgen : Rat.HeightOneSpectrum.natGenerator v = p :=
    natGenerator_rationalPrime ⟨p, hp⟩
  have hv : v ∈ (rationalModulus m).finitePart.support := by
    rw [rationalModulus, Modulus.finitePart_narrowOfFinite]
    rw [mem_rationalFiniteModulus_support_iff hm]
    rw [hvgen]
    exact hpm
  have hcount := I.property v hv
  rw [← toPrincipalIdeal_positiveRationalIdealGeneratorUnit
    (I : FractionalIdealGroup ℚ)] at hcount
  exact
    (not_dvd_den_of_principal_count_eq_zero
      (positiveRationalIdealGeneratorUnit
        (I : FractionalIdealGroup ℚ)) v hcount)
      (by
        rw [hvgen]
        exact hpden)

theorem positiveGenerator_num_coprime
    {m : ℕ} (hm : m ≠ 0)
    (I : primeToModulusIdeals (rationalModulus m)) :
    Nat.Coprime
      (positiveRationalIdealGenerator
        (I : FractionalIdealGroup ℚ)).num.natAbs m := by
  rw [Nat.coprime_comm]
  by_contra hcop
  obtain ⟨p, hp, hpm, hpnum⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hcop
  let v := rationalPrime ⟨p, hp⟩
  have hvgen : Rat.HeightOneSpectrum.natGenerator v = p :=
    natGenerator_rationalPrime ⟨p, hp⟩
  have hv : v ∈ (rationalModulus m).finitePart.support := by
    rw [rationalModulus, Modulus.finitePart_narrowOfFinite]
    rw [mem_rationalFiniteModulus_support_iff hm]
    rw [hvgen]
    exact hpm
  have hcount := I.property v hv
  rw [← toPrincipalIdeal_positiveRationalIdealGeneratorUnit
    (I : FractionalIdealGroup ℚ)] at hcount
  exact
    (not_dvd_num_of_principal_count_eq_zero
      (positiveRationalIdealGeneratorUnit
        (I : FractionalIdealGroup ℚ)) v hcount)
      (by
        rw [hvgen]
        exact hpnum)

/-- The numerator of a rational number as a residue-class unit. -/
def rationalNumeratorResidueUnit
    (m : ℕ) (q : ℚ) (hq : Nat.Coprime q.num.natAbs m) :
    (ZMod m)ˣ :=
  ZMod.unitOfIsCoprime q.num <| by
    simpa [Int.isCoprime_iff_nat_coprime] using hq

/-- The denominator of a rational number as a residue-class unit. -/
def rationalDenominatorResidueUnit
    (m : ℕ) (q : ℚ) (hq : Nat.Coprime q.den m) :
    (ZMod m)ˣ :=
  ZMod.unitOfIsCoprime (q.den : ℤ) <| by
    simpa [Int.isCoprime_iff_nat_coprime] using hq

/-- Reduction of a rational number whose numerator and denominator are
both prime to `m`. -/
def rationalResidueUnit
    (m : ℕ) (q : ℚ)
    (hnum : Nat.Coprime q.num.natAbs m)
    (hden : Nat.Coprime q.den m) :
    (ZMod m)ˣ :=
  rationalNumeratorResidueUnit m q hnum *
    (rationalDenominatorResidueUnit m q hden)⁻¹

/-- Rational residue units are independent of the chosen equality proof. -/
theorem rationalResidueUnit_congr
    (m : ℕ) {q r : ℚ} (hqr : q = r)
    (hqnum : Nat.Coprime q.num.natAbs m)
    (hqden : Nat.Coprime q.den m)
    (hrnum : Nat.Coprime r.num.natAbs m)
    (hrden : Nat.Coprime r.den m) :
    rationalResidueUnit m q hqnum hqden =
      rationalResidueUnit m r hrnum hrden := by
  subst r
  rfl

/-- Reduction of rational numbers prime to a modulus is multiplicative. -/
theorem rationalResidueUnit_mul
    (m : ℕ) (q r : ℚ)
    (hqnum : Nat.Coprime q.num.natAbs m)
    (hqden : Nat.Coprime q.den m)
    (hrnum : Nat.Coprime r.num.natAbs m)
    (hrden : Nat.Coprime r.den m)
    (hqrnum : Nat.Coprime (q * r).num.natAbs m)
    (hqrden : Nat.Coprime (q * r).den m) :
    rationalResidueUnit m (q * r) hqrnum hqrden =
      rationalResidueUnit m q hqnum hqden *
        rationalResidueUnit m r hrnum hrden := by
  let Nq := rationalNumeratorResidueUnit m q hqnum
  let Dq := rationalDenominatorResidueUnit m q hqden
  let Nr := rationalNumeratorResidueUnit m r hrnum
  let Dr := rationalDenominatorResidueUnit m r hrden
  let Nqr := rationalNumeratorResidueUnit m (q * r) hqrnum
  let Dqr := rationalDenominatorResidueUnit m (q * r) hqrden
  have hcross : Nqr * Dq * Dr = Nq * Nr * Dqr := by
    apply Units.ext
    have h :=
      congrArg (Int.castRingHom (ZMod m)) (Rat.mul_num_den' q r)
    simpa [Nq, Dq, Nr, Dr, Nqr, Dqr,
      rationalNumeratorResidueUnit,
      rationalDenominatorResidueUnit, map_mul] using h
  change Nqr * Dqr⁻¹ = (Nq * Dq⁻¹) * (Nr * Dr⁻¹)
  calc
    Nqr * Dqr⁻¹ =
        (Nqr * Dq * Dr) * (Dq⁻¹ * Dr⁻¹ * Dqr⁻¹) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = (Nq * Nr * Dqr) * (Dq⁻¹ * Dr⁻¹ * Dqr⁻¹) := by
      rw [hcross]
    _ = (Nq * Dq⁻¹) * (Nr * Dr⁻¹) := by
      simp [mul_comm, mul_left_comm, mul_assoc]

/-- The rational residue unit of one is one. -/
theorem rationalResidueUnit_one (m : ℕ) :
    rationalResidueUnit m 1 (by simp) (by simp) = 1 := by
  apply Units.ext
  simp [rationalResidueUnit, rationalNumeratorResidueUnit,
    rationalDenominatorResidueUnit]


/-- Send an ideal prime to `(m)` to the residue class of its positive
generator. -/
noncomputable def primeToIdealResidueHom
    (m : ℕ) (hm : m ≠ 0) :
    primeToModulusIdeals (rationalModulus m) →* (ZMod m)ˣ where
  toFun I :=
    rationalResidueUnit m
      (positiveRationalIdealGenerator (I : FractionalIdealGroup ℚ))
      (positiveGenerator_num_coprime hm I)
      (positiveGenerator_den_coprime hm I)
  map_one' := by
    change rationalResidueUnit m
      (positiveRationalIdealGenerator
        (1 : FractionalIdealGroup ℚ)) _ _ = 1
    calc
      rationalResidueUnit m
          (positiveRationalIdealGenerator
            (1 : FractionalIdealGroup ℚ)) _ _ =
        rationalResidueUnit m 1 (by simp) (by simp) :=
          rationalResidueUnit_congr m
            positiveRationalIdealGenerator_one _ _ _ _
      _ = 1 := rationalResidueUnit_one m
  map_mul' I J := by
    let q :=
      positiveRationalIdealGenerator (I : FractionalIdealGroup ℚ)
    let r :=
      positiveRationalIdealGenerator (J : FractionalIdealGroup ℚ)
    have hprodnum : Nat.Coprime (q * r).num.natAbs m := by
      rw [← positiveRationalIdealGenerator_mul]
      exact positiveGenerator_num_coprime hm (I * J)
    have hprodden : Nat.Coprime (q * r).den m := by
      rw [← positiveRationalIdealGenerator_mul]
      exact positiveGenerator_den_coprime hm (I * J)
    change rationalResidueUnit m
        (positiveRationalIdealGenerator
          ((I : FractionalIdealGroup ℚ) *
            (J : FractionalIdealGroup ℚ))) _ _ =
      rationalResidueUnit m q _ _ * rationalResidueUnit m r _ _
    calc
      rationalResidueUnit m
          (positiveRationalIdealGenerator
            ((I : FractionalIdealGroup ℚ) *
              (J : FractionalIdealGroup ℚ))) _ _ =
        rationalResidueUnit m (q * r) hprodnum hprodden :=
          rationalResidueUnit_congr m
            (positiveRationalIdealGenerator_mul I J) _ _ _ _
      _ = rationalResidueUnit m q
              (positiveGenerator_num_coprime hm I)
              (positiveGenerator_den_coprime hm I) *
            rationalResidueUnit m r
              (positiveGenerator_num_coprime hm J)
              (positiveGenerator_den_coprime hm J) :=
        rationalResidueUnit_mul m q r
          (positiveGenerator_num_coprime hm I)
          (positiveGenerator_den_coprime hm I)
          (positiveGenerator_num_coprime hm J)
          (positiveGenerator_den_coprime hm J)
          hprodnum hprodden

@[simp]
theorem primeToIdealResidueHom_apply
    (m : ℕ) (hm : m ≠ 0)
    (I : primeToModulusIdeals (rationalModulus m)) :
    primeToIdealResidueHom m hm I =
      rationalResidueUnit m
        (positiveRationalIdealGenerator
          (I : FractionalIdealGroup ℚ))
        (positiveGenerator_num_coprime hm I)
        (positiveGenerator_den_coprime hm I) :=
  rfl







/-! ### The local congruence condition over `ℚ` -/







/-- The rational-prime equivalence identifies the local prime value with
the natural prime generator. -/
@[simp]
theorem primesEquiv_val_eq_natGenerator
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((Rat.HeightOneSpectrum.primesEquiv
      (R := 𝓞 ℚ) v : Nat.Primes) : ℕ) =
      Rat.HeightOneSpectrum.natGenerator v :=
  rfl

















end RayClass

end
