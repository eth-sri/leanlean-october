module
import Mathlib
public import GafniTao.WooleySection4Holder
public import GafniTao.WooleyNormalization
public import GafniTao.WooleySection4Lemma41

@[expose] public section

/-!
# Wooley Lemma 4.2

This file performs the complete normalization following equation (4.15).
The two restricted-mean estimates are kept as explicit inputs here; the
source Lemma 4.1 module supplies them from the defining exponent.  No
Vinogradov constant is discarded in this exact, eventual-bound form.
-/

namespace GafniTao



/-- The source Lemma 4.2 calculation after the two instances of Lemma 4.1
have been supplied.  This is the precise terminal estimate used in Section
10, with normalization parameter `Delta = 0`. -/
theorem wooleySourcePolynomial_lemma_4_2_of_conditioned_bounds_with_constant
    {k : ℕ} (phi : WooleyPolynomialSystem k)
    (p B H a b nu r : ℕ) [NeZero p] [NeZero (p ^ B)]
    (Lambda epsilon C : ℝ) (gamma : WooleySourceSequence)
    (hp : 2 ≤ p) (hr : 1 ≤ r) (hrk : r < k)
    (haH : a ≤ H) (hbH : b ≤ H)
    (hC : 0 ≤ C)
    (hLambdaEpsilon : 0 ≤ Lambda + epsilon)
    (hupperA :
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ a) phi gamma ≤
        C * (p : ℝ) ^ (((H - a : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma)
    (hupperB :
      wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ b) phi gamma ≤
        C * (p : ℝ) ^ (((H - b : ℕ) : ℝ) * (Lambda + epsilon)) *
          wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ B) (p ^ H) phi gamma) :
    wooleySourceNormalizedMixedMean
        phi p B H (wooleyTriangular k) r a b nu 0 gamma ≤
      max 1 C * (p : ℝ) ^
        (((H : ℝ) * (Lambda + epsilon)) *
          wooleyNormalizationExponent k r) := by
  let s := wooleyTriangular k
  let R := wooleyTriangular r
  let u := (R : ℝ) / (s : ℝ)
  let e := wooleyNormalizationExponent k r
  let K := wooleySourcePolynomialMixedMean phi s r p B a b nu gamma
  let X := wooleySourcePolynomialConditionedMean s (p ^ B) (p ^ a) phi gamma
  let Y := wooleySourcePolynomialConditionedMean s (p ^ B) (p ^ b) phi gamma
  let Z := wooleySourcePolynomialConditionedMean s (p ^ B) (p ^ H) phi gamma
  have hk : 2 ≤ k := by omega
  have hs : 1 ≤ s := by
    dsimp [s]
    unfold wooleyTriangular
    grind
  have hRle : R ≤ s := by
    dsimp [R, s]
    exact wooleyTriangular_mono hrk.le
  have hu0 : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by exact_mod_cast (show 0 < s by omega))]
    exact_mod_cast hRle
  have hRpos : 0 < R := by
    dsimp [R]
    unfold wooleyTriangular
    have hrpos : 0 < r := by omega
    have htwo : 2 ≤ r * (r + 1) := by nlinarith
    omega
  have hRlt : R < s := by
    have hrReal : (r : ℝ) < k := by exact_mod_cast hrk
    have hpositive : 0 < ((k : ℝ) - r) * ((k : ℝ) + r + 1) := by
      positivity
    have hreal : (R : ℝ) < s := by
      dsimp [R, s]
      rw [wooleyTriangular_cast, wooleyTriangular_cast]
      nlinarith
    exact_mod_cast hreal
  have huPos : 0 < u := by positivity
  have huLt : u < 1 := by
    dsimp [u]
    rw [div_lt_one (by exact_mod_cast (show 0 < s by omega))]
    exact_mod_cast hRlt
  have he0 : 0 ≤ e :=
    (wooleyNormalizationExponent_pos hr hrk).le
  have he1 : e ≤ 1 :=
    wooleyNormalizationExponent_le_one hr hrk
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact wooleySourcePolynomialMixedMean_nonneg
      phi s r p B a b nu gamma
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact wooleySourcePolynomialConditionedMean_nonneg
      phi s (p ^ B) (p ^ a) gamma
  have hY0 : 0 ≤ Y := by
    dsimp [Y]
    exact wooleySourcePolynomialConditionedMean_nonneg
      phi s (p ^ B) (p ^ b) gamma
  have hZ0 : 0 ≤ Z := by
    dsimp [Z]
    exact wooleySourcePolynomialConditionedMean_nonneg phi s (p ^ B)
      (p ^ H) gamma
  have hKholder : K ≤ X ^ u * Y ^ (1 - u) := by
    exact wooleySourcePolynomial_equation_4_15
        phi p B a b nu r (by omega) hrk.le gamma
  by_cases hZzero : Z = 0
  · have hupperA' : X ≤
        C * (p : ℝ) ^ (((H - a : ℕ) : ℝ) * (Lambda + epsilon)) * Z := by
      simpa only [X, Z, s] using hupperA
    have hupperB' : Y ≤
        C * (p : ℝ) ^ (((H - b : ℕ) : ℝ) * (Lambda + epsilon)) * Z := by
      simpa only [Y, Z, s] using hupperB
    have hXzero : X = 0 := by
      apply le_antisymm _ hX0
      simpa only [hZzero, mul_zero] using hupperA'
    have hYzero : Y = 0 := by
      apply le_antisymm _ hY0
      simpa only [hZzero, mul_zero] using hupperB'
    have hKzero : K = 0 := by
      apply le_antisymm _ hK0
      simpa only [hXzero, hYzero, Real.zero_rpow huPos.ne',
        Real.zero_rpow (sub_pos.mpr huLt).ne', zero_mul] using hKholder
    unfold wooleySourceNormalizedMixedMean
    rw [show wooleySourcePolynomialMixedMean phi s r p B a b nu gamma = 0 by
      simpa only [K] using hKzero]
    simp only [zero_div,
      Real.zero_rpow (ne_of_gt (wooleyNormalizationExponent_pos hr hrk))]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hZ : 0 < Z := lt_of_le_of_ne hZ0 (Ne.symm hZzero)
  by_cases hCzero : C = 0
  · have hXzero : X = 0 := by
      apply le_antisymm _ hX0
      simpa only [hCzero, zero_mul] using hupperA
    have hYzero : Y = 0 := by
      apply le_antisymm _ hY0
      simpa only [hCzero, zero_mul] using hupperB
    have hKzero : K = 0 := by
      apply le_antisymm _ hK0
      simpa only [hXzero, hYzero, Real.zero_rpow huPos.ne',
        Real.zero_rpow (sub_pos.mpr huLt).ne', zero_mul] using hKholder
    unfold wooleySourceNormalizedMixedMean
    rw [show wooleySourcePolynomialMixedMean phi s r p B a b nu gamma = 0 by
      simpa only [K] using hKzero]
    simp only [zero_div,
      Real.zero_rpow (ne_of_gt (wooleyNormalizationExponent_pos hr hrk))]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
  have hnormalized :
      (K / Z) ^ e ≤
        (X / Z) ^ (u * e) * (Y / Z) ^ ((1 - u) * e) := by
    have h := wooley_normalized_two_factor
      hK0 hX0 hY0 hZ (show 0 ≤ (1 : ℝ) by norm_num) he0
      (show u + (1 - u) = 1 by ring)
      (show K ≤ 1 * (X ^ u * Y ^ (1 - u)) by simpa using hKholder)
    simpa using h
  let A := ((H - a : ℕ) : ℝ) * (Lambda + epsilon)
  let D := ((H - b : ℕ) : ℝ) * (Lambda + epsilon)
  have hratioA : X / Z ≤ C * (p : ℝ) ^ A := by
    rw [div_le_iff₀ hZ]
    simpa only [X, Z, A, s] using hupperA
  have hratioB : Y / Z ≤ C * (p : ℝ) ^ D := by
    rw [div_le_iff₀ hZ]
    simpa only [Y, Z, D, s] using hupperB
  have hratioA0 : 0 ≤ X / Z := div_nonneg hX0 hZ.le
  have hratioB0 : 0 ≤ Y / Z := div_nonneg hY0 hZ.le
  have hue0 : 0 ≤ u * e := mul_nonneg hu0 he0
  have hve0 : 0 ≤ (1 - u) * e :=
    mul_nonneg (sub_nonneg.mpr hu1) he0
  have hpowA :=
    Real.rpow_le_rpow hratioA0 hratioA hue0
  have hpowB :=
    Real.rpow_le_rpow hratioB0 hratioB hve0
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hA0 : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) hLambdaEpsilon
  have hD0 : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) hLambdaEpsilon
  have hweighted0 : 0 ≤ A * u + D * (1 - u) := by positivity
  have hAle : A ≤ (H : ℝ) * (Lambda + epsilon) := by
    dsimp [A]
    rw [Nat.cast_sub haH]
    nlinarith
  have hDle : D ≤ (H : ℝ) * (Lambda + epsilon) := by
    dsimp [D]
    rw [Nat.cast_sub hbH]
    nlinarith
  have hweighted :
      (A * u + D * (1 - u)) * e ≤
        ((H : ℝ) * (Lambda + epsilon)) * e := by
    have hblend :
        A * u + D * (1 - u) ≤ (H : ℝ) * (Lambda + epsilon) := by
      nlinarith
    exact mul_le_mul_of_nonneg_right hblend he0
  have hrearrange :
      (C * (p : ℝ) ^ A) ^ (u * e) *
          (C * (p : ℝ) ^ D) ^ ((1 - u) * e) =
        C ^ e * (p : ℝ) ^ ((A * u + D * (1 - u)) * e) := by
    rw [Real.mul_rpow hC (Real.rpow_nonneg hpR.le _),
      Real.mul_rpow hC (Real.rpow_nonneg hpR.le _)]
    calc
      C ^ (u * e) * (((p : ℝ) ^ A) ^ (u * e)) *
          (C ^ ((1 - u) * e) * (((p : ℝ) ^ D) ^ ((1 - u) * e))) =
          (C ^ (u * e) * C ^ ((1 - u) * e)) *
            (((p : ℝ) ^ A) ^ (u * e) *
              ((p : ℝ) ^ D) ^ ((1 - u) * e)) := by ring_nf
      _ = C ^ e * (p : ℝ) ^ ((A * u + D * (1 - u)) * e) := by
        rw [← Real.rpow_add hCpos, ← Real.rpow_mul hpR.le,
          ← Real.rpow_mul hpR.le, ← Real.rpow_add hpR]
        congr 1 <;> ring_nf
  have hCpow : C ^ e ≤ max 1 C := by
    rcases le_total C 1 with hCle | hCle
    · exact (Real.rpow_le_one hC hCle he0).trans (le_max_left 1 C)
    · exact (Real.rpow_le_self_of_one_le hCle he1).trans (le_max_right 1 C)
  have hfinalPow :
      (p : ℝ) ^ ((A * u + D * (1 - u)) * e) ≤
        (p : ℝ) ^ (((H : ℝ) * (Lambda + epsilon)) * e) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ p by omega))
      hweighted
  have hscaleZero :
      wooleySourceNormalizationScale phi p B H s 0 gamma = Z := by
    simp [wooleySourceNormalizationScale, Z]
  calc
    wooleySourceNormalizedMixedMean phi p B H s r a b nu 0 gamma =
        (K / Z) ^ e := by
          simp only [wooleySourceNormalizedMixedMean, K, e, hscaleZero]
    _ ≤ (X / Z) ^ (u * e) * (Y / Z) ^ ((1 - u) * e) := hnormalized
    _ ≤ (C * (p : ℝ) ^ A) ^ (u * e) *
          (C * (p : ℝ) ^ D) ^ ((1 - u) * e) :=
      mul_le_mul hpowA hpowB (Real.rpow_nonneg hratioB0 _) (by positivity)
    _ = C ^ e * (p : ℝ) ^ ((A * u + D * (1 - u)) * e) := hrearrange
    _ ≤ max 1 C * (p : ℝ) ^ ((A * u + D * (1 - u)) * e) :=
      mul_le_mul_of_nonneg_right hCpow (Real.rpow_nonneg hpR.le _)
    _ ≤ max 1 C * (p : ℝ) ^
        (((H : ℝ) * (Lambda + epsilon)) * e) :=
      mul_le_mul_of_nonneg_left hfinalPow (le_trans (by norm_num) (le_max_left 1 C))

/-- Converting the paper's natural prime-power base to the real-exponent
form used by the normalized interpolation theorem. -/
theorem wooley_natPrimePower_rpow
    (p n : ℕ) (Lambda : ℝ) (hp : 0 < p) :
    (((p ^ n : ℕ) : ℝ) ^ Lambda) =
      (p : ℝ) ^ ((n : ℝ) * Lambda) := by
  rw [Nat.cast_pow]
  exact (Real.rpow_natCast_mul (by exact_mod_cast hp.le) n Lambda).symm




