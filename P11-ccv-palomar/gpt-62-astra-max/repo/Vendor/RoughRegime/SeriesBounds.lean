module

public import Mathlib

@[expose] public section

/-!
The combined-index coefficient and tail estimates used in Lemma 5(a).
These generic results are separated from the unproved determinant power-series bridge.
-/
noncomputable section
open scoped BigOperators
namespace RoughRegime.SeriesBounds

lemma weighted_geometric_summable (ν : ℕ) (ρ : ℝ) (hp : 0 < ρ) (h1 : ρ < 1) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k) := by
  have hn : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hp] using h1
  have hraw := summable_pow_mul_geometric_of_norm_lt_one ν hn
  convert ((summable_nat_add_iff 1).mpr hraw).mul_right ρ⁻¹ using 1
  ext k
  rw [pow_succ]
  field_simp

variable {R E : Type*}

/-- The exact tail bound used in Lemma 5(a), valid in every complete normed space. -/
theorem series_truncation_bound [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → E} (ν m : ℕ) {ρ A : ℝ} (hp : 0 < ρ) (h1 : ρ < 1) (hA : 0 ≤ A)
    (hcoeff : ∀ k, ‖f k‖ ≤ A * (k + 1 : ℕ) ^ ν * ρ ^ k) :
    ‖(∑' k, f k) - ∑ k ∈ Finset.range (m + 1), f k‖ ≤
      A * (m + 1 : ℕ) ^ ν * ρ ^ m *
        ∑' k, (k + 1 : ℕ) ^ ν * ρ ^ k := by
  let w  := fun k => (k + 1 : ℕ) ^ ν * ρ ^ k
  have hw  := weighted_geometric_summable ν ρ hp h1
  have hmajor  := hw.mul_left A
  have hcoeff' k : ‖f k‖ ≤ A * w k := by
    simpa only [ mul_assoc] using hcoeff k
  have hnorm  :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoeff' hmajor
  have htail : (∑' k, f k) - ∑ k ∈ Finset.range (m + 1), f k =
      ∑' k, f (k + (m + 1)) := by
    rw [← ((hmajor.of_norm_bounded hcoeff').sum_add_tsum_nat_add (m + 1))]
    abel
  have hn0  :=
    (summable_nat_add_iff m).mpr hnorm
  have hn1  :=
    (summable_nat_add_iff (m + 1)).mpr hnorm
  have htmono : (∑' k, ‖f (k + (m + 1))‖) ≤ ∑' k, ‖f (k + m)‖ := by
    have h := hn0.tsum_eq_zero_add
    have he : (fun k => ‖f (k + 1 + m)‖) = (fun k => ‖f (k + (m + 1))‖) := by
      ext k
      congr 2
      omega
    simp_all
  let C := A * (m + 1 : ℕ) ^ ν * ρ ^ m
  have htbound k : ‖f (k + m)‖ ≤ C * w k := by
    apply (hcoeff (k + m)).trans
    have hindex : (k + m + 1 : ℝ) ≤ (m + 1) * (k + 1) := by
      nlinarith
    have hpow := pow_le_pow_left₀ (by positivity) hindex ν
    have hpow' : ((k + m + 1 : ℕ)) ^ ν ≤
        (m + 1 : ℕ) ^ ν * ((k + 1 : ℕ) : ℝ) ^ ν := by
      simpa [mul_pow] using hpow
    convert (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow' hA) (pow_nonneg hp.le (k + m))) using 1 <;> rw [pow_add] <;> ring
  rw [htail]
  calc
    _ ≤ _ := norm_tsum_le_tsum_norm hn1
    _ ≤ _ := htmono
    _ ≤ _ := Summable.tsum_le_tsum htbound hn0 (hw.mul_left C)
    _ = _ := by rw [tsum_mul_left]

/-- Combined-index Cauchy product. -/
def convolution [NonUnitalNonAssocSemiring R] (f g : ℕ → R) (k : ℕ) : R :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, f ij.1 * g ij.2

/-- Adding one reciprocal factor increases the polynomial coefficient weight by one.
This proves the counting estimate in Lemma 5(a) without using eigenvalue-defined polynomials. -/
theorem convolution_coefficient_bound [NormedRing R]
    {f g : ℕ → R} (ν k : ℕ) {ρ A B : ℝ} (hp : 0 < ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i, ‖f i‖ ≤ A * (i + 1 : ℕ) ^ ν * ρ ^ i)
    (hg : ∀ j, ‖g j‖ ≤ B * ρ ^ j) :
    ‖convolution f g k‖ ≤ A * B * (k + 1 : ℕ) ^ (ν + 1) * ρ ^ k := by
  have hterm ij (hij : ij ∈ Finset.HasAntidiagonal.antidiagonal k) :
      ‖f ij.1 * g ij.2‖ ≤ A * B * (k + 1 : ℕ) ^ ν * ρ ^ k := by
    have he  := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hnorm := (norm_mul_le (f ij.1) (g ij.2)).trans
      (mul_le_mul (hf ij.1) (hg ij.2) (norm_nonneg _) (by positivity))
    calc
      _ ≤ _ := hnorm
      _ = A * B * (ij.1 + 1 : ℕ) ^ ν * ρ ^ k := by rw [← he]; ring
      _ ≤ _ := by bound
  calc
    _ ≤ _ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum hterm
    _ = _ := by simp; rw [pow_succ]; ring

/-- Exact Cauchy product identity used for the scalar factors of Lemma 5(a). -/
theorem convolution_tsum [NormedRing R] [CompleteSpace R]
    {f g : ℕ → R} (hf : Summable (fun i => ‖f i‖)) (hg : Summable (fun i => ‖g i‖)) :
    ∑' k, convolution f g k = (∑' i, f i) * ∑' j, g j := (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg).symm

/-- Form a combined-index product, starting with a distinguished matrix-valued factor. -/
def addFactors [NonUnitalNonAssocSemiring R] (f : ℕ → R) :
    List (ℕ → R) → ℕ → R
  | [] => f
  | g :: gs => convolution (addFactors f gs) g

/-- Coefficient bound for any finite number of reciprocal-type factors. -/
theorem addFactors_coefficient_bound [NormedRing R]
    {f : ℕ → R} {gs : List (ℕ → R)} {ρ A B : ℝ} (hp : 0 < ρ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ k, ‖f k‖ ≤ A * ρ ^ k)
    (hg : ∀ g ∈ gs, ∀ k, ‖g k‖ ≤ B * ρ ^ k) (k : ℕ) :
    ‖addFactors f gs k‖ ≤ A * B ^ gs.length * (k + 1 : ℕ) ^ gs.length * ρ ^ k := by
  induction gs generalizing k with
  | nil => simpa [addFactors] using hf k
  | cons g gs ih =>
    have ht : ∀ k, ‖addFactors f gs k‖ ≤
        A * B ^ gs.length * (k + 1 : ℕ) ^ gs.length * ρ ^ k := by
      aesop
    have hh := convolution_coefficient_bound gs.length k hp (by positivity) hB ht (hg g (List.mem_cons_self ..))
    change ‖convolution (addFactors f gs) g k‖ ≤ _
    convert hh using 1
    simp only [List.length_cons, pow_succ]
    ring

end RoughRegime.SeriesBounds
