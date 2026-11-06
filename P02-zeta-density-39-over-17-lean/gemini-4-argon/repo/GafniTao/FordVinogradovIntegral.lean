module
public import GafniTao.FordZeroRepresentation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section

/-!
# Ford's complete Vinogradov system

This file formalizes the finite counting side of equations (1.3)--(1.5) in
Ford's source.  A coordinate of `FordVinogradovTuple s Q` represents the
source integer `x_i` by the value `x_i.val + 1`, so its literal range is
`1 ≤ x_i ≤ Q`.  The power-vector has coordinates of degrees `1, ..., k`.

The normalized-Haar orthogonality calculation below proves the integral
identity (1.3).  Equation (1.4), shifted domination, and both lower-bound
terms in (1.5) are then proved from the same exact finite count.
-/

open Finset MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

/-- The `s` source variables, each ranging over the integers `1, ..., Q`. -/
abbrev FordVinogradovTuple (s Q : ℕ) := Fin s → Fin Q

/-- The vector `(∑ᵢ xᵢ, ..., ∑ᵢ xᵢ^k)` attached to a source tuple. -/
def fordVinogradovPowerVector (s k Q : ℕ) (x : FordVinogradovTuple s Q) :
    Fin k → ℤ :=
  fun j => ∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ ((j : ℕ) + 1)

/-- Ford's shifted solution count `J_{s,k}(P; h)` with `Q = floor P`. -/
def fordVinogradovShiftedCountNat
    (s k Q : ℕ) (h : Fin k → ℤ) : ℕ :=
  fordRepresentationCount (Finset.univ : Finset (FordVinogradovTuple s Q))
    (fordVinogradovPowerVector s k Q) h

/-- The combinatorial form (1.4) of Ford's complete Vinogradov mean value. -/
def fordVinogradovMomentNat (s k Q : ℕ) : ℕ :=
  fordVinogradovShiftedCountNat s k Q 0

/-- Ford's conventional abbreviation `k(k+1)/2`. -/
def fordVinogradovKappa (k : ℕ) : ℕ := k * (k + 1) / 2

theorem fordVinogradovPowerVector_bounds
    {s k Q : ℕ} (x : FordVinogradovTuple s Q) (j : Fin k) :
    (s : ℤ) ≤ fordVinogradovPowerVector s k Q x j ∧
      fordVinogradovPowerVector s k Q x j ≤
        (s : ℤ) * (Q : ℤ) ^ ((j : ℕ) + 1) := by
  let d : ℕ := (j : ℕ) + 1
  have htermLower (i : Fin s) :
      (1 : ℤ) ≤ ((x i : ℕ) + 1 : ℤ) ^ d := by
    apply one_le_pow₀
    omega
  have htermUpper (i : Fin s) :
      ((x i : ℕ) + 1 : ℤ) ^ d ≤ (Q : ℤ) ^ d := by
    have hbase : (x i : ℕ) + 1 ≤ Q := Nat.succ_le_iff.mpr (x i).isLt
    have hpow : ((x i : ℕ) + 1) ^ d ≤ Q ^ d := Nat.pow_le_pow_left hbase d
    exact_mod_cast hpow
  constructor
  · change (s : ℤ) ≤ ∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d
    calc
      (s : ℤ) = ∑ _i : Fin s, (1 : ℤ) := by simp
      _ ≤ ∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d :=
        Finset.sum_le_sum fun i _hi => htermLower i
  · change (∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d) ≤
      (s : ℤ) * (Q : ℤ) ^ d
    calc
      (∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d) ≤
          ∑ _i : Fin s, (Q : ℤ) ^ d :=
        Finset.sum_le_sum fun i _hi => htermUpper i
      _ = (s : ℤ) * (Q : ℤ) ^ d := by simp

/-! ## The normalized-Haar identity, equation (1.3) -/

/-- The degree vector contributed by one source integer `1 ≤ n ≤ Q`. -/
def fordVinogradovExponent {k Q : ℕ} (n : Fin Q) : Fin k → ℤ :=
  fun j => (((n : ℕ) + 1) ^ ((j : ℕ) + 1) : ℕ)

/-- One exponential monomial in Ford's complete Weyl sum. -/
def fordVinogradovMonomial {k Q : ℕ} (n : Fin Q)
    (α : UnitAddTorus (Fin k)) : ℂ :=
  UnitAddTorus.mFourier (fordVinogradovExponent n) α

/-- The complete Weyl sum over the literal integer range `1, ..., Q`. -/
def fordVinogradovWeylSum (k Q : ℕ) (α : UnitAddTorus (Fin k)) : ℂ :=
  ∑ n : Fin Q, fordVinogradovMonomial n α

/-- A nonzero Fourier character has normalized Haar integral zero; the zero
character has integral one. -/
theorem ford_integral_fourier_haar_eq (n : ℤ) :
    ∫ x : UnitAddCircle, fourier n x ∂AddCircle.haarAddCircle =
      if n = 0 then 1 else 0 := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  split_ifs with hn
  · subst n
    simp
  · exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hn (by norm_num))

/-- Product orthogonality on the `k`-dimensional unit torus. -/
theorem ford_integral_mFourier_pi_haar_eq {k : ℕ} (h : Fin k → ℤ) :
    ∫ α : UnitAddTorus (Fin k), UnitAddTorus.mFourier h α
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) =
      if h = 0 then 1 else 0 := by
  change (∫ α : UnitAddTorus (Fin k), ∏ i, fourier (h i) (α i)
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) = _
  rw [MeasureTheory.integral_fintype_prod_eq_prod]
  simp_rw [ford_integral_fourier_haar_eq]
  split_ifs with hh
  · subst h
    simp
  · simp only [Finset.prod_ite_zero, Finset.prod_const_one]
    rw [ite_eq_right]
    simpa [funext_iff] using hh

theorem fordVinogradovPowerVector_eq_sum_exponent
    {s k Q : ℕ} (x : FordVinogradovTuple s Q) :
    fordVinogradovPowerVector s k Q x =
      ∑ i : Fin s, fordVinogradovExponent (x i) := by
  ext j
  simp [fordVinogradovPowerVector, fordVinogradovExponent]

theorem ford_prod_monomial_eq
    {s k Q : ℕ} (x : FordVinogradovTuple s Q) (α : UnitAddTorus (Fin k)) :
    ∏ i : Fin s, fordVinogradovMonomial (x i) α =
      UnitAddTorus.mFourier (fordVinogradovPowerVector s k Q x) α := by
  classical
  rw [fordVinogradovPowerVector_eq_sum_exponent]
  induction (Finset.univ : Finset (Fin s)) using Finset.induction_on with
  | empty => simp [UnitAddTorus.mFourier_zero]
  | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [UnitAddTorus.mFourier_add]
      exact congrArg (fun z => fordVinogradovMonomial (x a) α * z) ih

theorem ford_vinogradov_weyl_pow
    (s k Q : ℕ) (α : UnitAddTorus (Fin k)) :
    fordVinogradovWeylSum k Q α ^ s =
      ∑ x : FordVinogradovTuple s Q,
        UnitAddTorus.mFourier (fordVinogradovPowerVector s k Q x) α := by
  rw [fordVinogradovWeylSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x hx
  exact ford_prod_monomial_eq x α

theorem ford_conj_vinogradov_weyl_pow
    (s k Q : ℕ) (α : UnitAddTorus (Fin k)) :
    conj (fordVinogradovWeylSum k Q α) ^ s =
      ∑ y : FordVinogradovTuple s Q,
        UnitAddTorus.mFourier (-fordVinogradovPowerVector s k Q y) α := by
  have h := congrArg conj (ford_vinogradov_weyl_pow s k Q α)
  simpa only [map_pow, map_sum, UnitAddTorus.mFourier_neg] using h

theorem ford_pair_character
    {s k Q : ℕ} (x y : FordVinogradovTuple s Q)
    (α : UnitAddTorus (Fin k)) :
    UnitAddTorus.mFourier (fordVinogradovPowerVector s k Q x) α *
        UnitAddTorus.mFourier (-fordVinogradovPowerVector s k Q y) α =
      UnitAddTorus.mFourier
        (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α := by
  rw [sub_eq_add_neg, UnitAddTorus.mFourier_add]

/-- Complex-valued orthogonality form of Ford's equation (1.3). -/
theorem ford_vinogradov_torus_mean_eq (s k Q : ℕ) :
    ∫ α : UnitAddTorus (Fin k),
        fordVinogradovWeylSum k Q α ^ s *
          conj (fordVinogradovWeylSum k Q α) ^ s
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) =
      (fordVinogradovMomentNat s k Q : ℂ) := by
  simp_rw [ford_vinogradov_weyl_pow, ford_conj_vinogradov_weyl_pow,
    Finset.sum_mul_sum]
  simp_rw [ford_pair_character]
  let μ : Measure (UnitAddTorus (Fin k)) :=
    Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)
  have hchar (x y : FordVinogradovTuple s Q) :
      Integrable
        (fun α : UnitAddTorus (Fin k) =>
          UnitAddTorus.mFourier
            (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α) μ := by
    rw [← integrableOn_univ]
    have hc : Continuous (fun α : UnitAddTorus (Fin k) =>
        UnitAddTorus.mFourier
          (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α) :=
      (UnitAddTorus.mFourier
        (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y)).continuous
    exact hc.continuousOn.integrableOn_compact isCompact_univ
  have hinner (x : FordVinogradovTuple s Q) :
      Integrable
        (fun α : UnitAddTorus (Fin k) =>
          ∑ y : FordVinogradovTuple s Q,
            UnitAddTorus.mFourier
              (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α) μ := by
    exact integrable_finsetSum Finset.univ fun y _hy => hchar x y
  change (∫ α : UnitAddTorus (Fin k),
      ∑ x : FordVinogradovTuple s Q,
        ∑ y : FordVinogradovTuple s Q,
          UnitAddTorus.mFourier
            (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α ∂μ) = _
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun x _hx => hinner x)]
  calc
    _ = ∑ x : FordVinogradovTuple s Q,
          ∑ y : FordVinogradovTuple s Q,
            ∫ α : UnitAddTorus (Fin k),
              UnitAddTorus.mFourier
                (fordVinogradovPowerVector s k Q x -
                  fordVinogradovPowerVector s k Q y) α ∂μ := by
        apply Finset.sum_congr rfl
        intro x hx
        exact MeasureTheory.integral_finsetSum Finset.univ (fun y _hy => hchar x y)
    _ = ∑ x : FordVinogradovTuple s Q,
          ∑ y : FordVinogradovTuple s Q,
            if fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y = 0
            then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact ford_integral_mFourier_pi_haar_eq _
    _ = (fordVinogradovMomentNat s k Q : ℂ) := by
        simp only [fordVinogradovMomentNat, fordVinogradovShiftedCountNat,
          fordRepresentationCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero]
        rw [Finset.sum_product]

theorem ford_pow_mul_conj_pow (z : ℂ) (s : ℕ) :
    z ^ s * conj z ^ s = ((‖z‖ : ℝ) : ℂ) ^ (2 * s) := by
  rw [← mul_pow, Complex.mul_conj']
  rw [← pow_mul]

theorem ford_vinogradov_torus_real_mean_eq (s k Q : ℕ) :
    ∫ α : UnitAddTorus (Fin k), ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s)
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) =
      (fordVinogradovMomentNat s k Q : ℝ) := by
  apply Complex.ofReal_injective
  have hcast :
      (∫ α : UnitAddTorus (Fin k),
          ((‖fordVinogradovWeylSum k Q α‖ ^ (2 * s) : ℝ) : ℂ)
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
        ((∫ α : UnitAddTorus (Fin k),
          ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s)
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) : ℝ) : ℂ) :=
    integral_ofReal
  rw [← hcast]
  simpa only [ford_pow_mul_conj_pow, Complex.ofReal_natCast, Complex.ofReal_pow] using
    ford_vinogradov_torus_mean_eq s k Q

/-- Every torus character used in the shifted identity is integrable against
the explicit product of normalized Haar measures. -/
theorem ford_integrable_mFourier_pi_haar {k : ℕ} (h : Fin k → ℤ) :
    Integrable (fun α : UnitAddTorus (Fin k) => UnitAddTorus.mFourier h α)
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) := by
  rw [← integrableOn_univ]
  exact (UnitAddTorus.mFourier h).continuous.continuousOn.integrableOn_compact
    isCompact_univ


