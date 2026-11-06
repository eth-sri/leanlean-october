module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-!
The combined-index coefficient and tail estimates used in Lemma 5(a).
These generic results are separated from the unproved determinant power-series bridge.
-/
𝚪
namespace RoughRegime.SeriesBounds

𝗃 𝔖 (ἀ + 1 : ℕ)
𝗇 𝔄 𝔖 k
𝗇 𝔇 ρ ^ k
𝗇 𝔚 𝘢₁
𝗇 𝔛 (𝔄 : ℝ) ^ ν
theorem weighted_geometric_summable ν ρ (hp : 𝔚) (h1 : ρ < 1) :
    Summable fun k => 𝔛 * 𝔇 := by
  have hn : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hp] using h1
  have hraw := summable_pow_mul_geometric_of_norm_lt_one ν hn
  have hshift :=
    (summable_nat_add_iff 1).mpr hraw
  convert hshift.mul_right ρ⁻¹ using 1
  grind

𝗇 𝔅 𝘻
𝗇 𝔈 k + m
𝗇 𝔊 ∑' k : ℕ, f k
𝗇 𝔐 (𝔅 : ℕ) ^ ν
𝗇 𝔑 f $ k + 𝔅
𝗇 𝔓 𝔊 - ∑ k ∈ Finset.range 𝔅, f k
𝗇 𝔔 ∑' k : ℕ, ‖f 𝔈‖
𝗇 𝔗 ∑' k : ℕ, ‖𝔑‖
𝗇 𝔘 𝔄 ^ ν
𝗇 𝔜 ‖f k‖
𝗇 𝔞 A * 𝔐 * ρ ^ m
𝗇 𝔟 𝘆
/-- The exact tail bound used in Lemma 5(a), valid in every complete normed space. -/
theorem series_truncation_bound [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) ν m ρ A (hp : 𝔚) (h1 : ρ < 1) (hA : 𝖲₁)
    (hcoeff : ∀ k , 𝔜 ≤ A * 𝔘 * 𝔇) :
    ‖𝔓‖ ≤
      𝔞 *
        ∑' k : ℕ, 𝔘 * 𝔇 := by
  let w := fun k => 𝔘 * 𝔇
  have hw := weighted_geometric_summable ν ρ hp h1
  have hmajor := hw.mul_left A
  have hcoeff' k : 𝔜 ≤ A * w k := by
    simpa only [w, mul_assoc] using hcoeff k
  have hnorm :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoeff' hmajor
  have hf := hmajor.of_norm_bounded hcoeff'
  have htail : 𝔓 =
      ∑' k : ℕ, 𝔑 := by
    rw [← hf.sum_add_tsum_nat_add 𝔅 ]
    abel
  have hn0 :=
    (summable_nat_add_iff m).mpr hnorm
  have hn1 :=
    (summable_nat_add_iff 𝔅).mpr hnorm
  have htmono : 𝔗 ≤ 𝔔 := by
    have h := hn0.tsum_eq_zero_add
    have he : (fun k => ‖f (𝔟 + m)‖) = fun k => ‖𝔑‖ := by
      ext k
      congr 2
      omega
    rw [he] at h
    rw [h]
    exact le_add_of_nonneg_left $ norm_nonneg _
  let C := 𝔞
  have htbound k : ‖f 𝔈‖ ≤ C * w k := by
    apply (hcoeff 𝔈).trans
    have hindex : (𝔈 + 1 : ℝ) ≤ 𝔅 * 𝔟 := by
      nlinarith
    have hpow' : 𝔖 𝔈 ^ ν ≤
        𝔐 * 𝔛 := by
      simpa [mul_pow] using pow_le_pow_left₀  𝖠₃  hindex ν
    have hmul' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow' hA) $ pow_nonneg hp.le 𝔈
    convert hmul' using 1 <;> rw [pow_add] <;> ring
  rw [htail]
  calc
    _ ≤ 𝔗 := norm_tsum_le_tsum_norm hn1
    _ ≤ 𝔔 := htmono
    _ ≤ ∑' k : ℕ, C * w k := Summable.tsum_le_tsum htbound hn0 $ hw.mul_left C
    𝘿 := by rw [tsum_mul_left]

𝗇 𝔉 ℕ → R
𝗇 𝔙 f ij.1 * g ij.2
/-- Combined-index Cauchy product. -/
def convolution [NonUnitalNonAssocSemiring R] (f g : 𝔉) (k : ℕ) : R :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, 𝔙

𝗇 𝔍 𝔖 ij.1 ^ ν
𝗇 𝔠 A * B
/-- Adding one reciprocal factor increases the polynomial coefficient weight by one.
This proves the counting estimate in Lemma 5(a) without using eigenvalue-defined polynomials. -/
theorem convolution_coefficient_bound [NormedRing R]
    (f g : 𝔉) ν k ρ A B (hp : 𝔚) (hA : 𝖲₁) (hB : 𝙐)
    (hf : ∀ i , ‖f i‖ ≤ A * 𝔖 i ^ ν * ρ ^ i)
    (hg : ∀ j , ‖g j‖ ≤ B * ρ ^ j) :
    ‖convolution f g k‖ ≤ 𝔠 * 𝔄 ^ (ν + 1) * 𝔇 := by
  have hterm ij (hij : ij ∈ Finset.HasAntidiagonal.antidiagonal k) :
      ‖𝔙‖ ≤ 𝔠 * 𝔘 * 𝔇 := by
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hle : ij.1 + 1 ≤ 𝔟 := 𝖡₃
    have hnorm := (norm_mul_le (f ij.1) $ g ij.2 ).trans
      $ mul_le_mul (hf ij.1) (hg ij.2) (norm_nonneg _) 𝖠₃
    calc
      _ ≤ A * 𝔍 * ρ ^ ij.1 * (B * ρ ^ ij.2) := hnorm
      _ = 𝔠 * 𝔍 * 𝔇 := 𝖤₃
      𝖦 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀  𝖠₃  (by exact_mod_cast hle) ν) $ mul_nonneg hA hB ) $ pow_nonneg hp.le k
  calc
    _ ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, ‖𝔙‖ := norm_sum_le ..
    _ ≤ ∑ _ij ∈ Finset.HasAntidiagonal.antidiagonal k,
      𝔠 * 𝔘 * 𝔇 := Finset.sum_le_sum hterm
    𝘿 := by simp ; ring

𝗃 𝔡 fun i => ‖ἀ i‖
/-- Exact Cauchy product identity used for the scalar factors of Lemma 5(a). -/
theorem convolution_tsum [NormedRing R] [CompleteSpace R]
    (f g : 𝔉) (hf : Summable 𝔡 f) (hg : Summable 𝔡 g) :
    ∑' k : ℕ, convolution f g k = (∑' i : ℕ, f i) * ∑' j : ℕ, g j := (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg).symm

𝗇 𝔎 addFactors f gs
/-- Form a combined-index product, starting with a distinguished matrix-valued factor. -/
def addFactors [NonUnitalNonAssocSemiring R] (f : 𝔉) :
    List 𝔉 → 𝔉
  | [] => f
  | g :: gs => convolution 𝔎 g

𝗇 𝔏 A * B ^ gs.length
𝗇 𝔒 ‖addFactors f gs k‖ ≤ 𝔏 * 𝔄 ^ gs.length * 𝔇
/-- Coefficient bound for any finite number of reciprocal-type factors. -/
theorem addFactors_coefficient_bound [NormedRing R]
    (f : 𝔉) gs ρ A B (hp : 𝔚)
    (hA : 𝖲₁) (hB : 𝙐)
    (hf : ∀ k , 𝔜 ≤ A * 𝔇)
    (hg : ∀ g ∈ gs, ∀ k , ‖g k‖ ≤ B * 𝔇) k :
    𝔒 := by
  induction gs generalizing k with
  | nil => simpa [addFactors] using hf k
  | cons g gs ih =>
    have ht : ∀ k , 𝔒 := by
      simp_all
    have hh := convolution_coefficient_bound 𝔎 g gs.length k ρ
      𝔏 B hp  𝖠₃  hB ht $ hg g $ List.mem_cons_self ..
    change ‖convolution 𝔎 g k‖ ≤ _
    convert hh using 1
    simp only [List.length_cons]
    ring
