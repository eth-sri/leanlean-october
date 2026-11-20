module

public import Mathlib

@[expose] public section

/-!
The combined-index coefficient and tail estimates used in Lemma 5(a).
Absolute coefficient bounds are propagated through genuine power-series products.
-/
noncomputable section
open scoped BigOperators
namespace RoughRegime.SeriesBounds

lemma weighted_geometric_summable (ν : ℕ) (ρ : ℝ) (hp : 0 < ρ) (h1 : ρ < 1) :
    Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k) := by
  have hn : ‖ρ‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hp] using h1
  have hraw := summable_pow_mul_geometric_of_norm_lt_one ν hn
  have hshift :=
    (summable_nat_add_iff 1).mpr hraw
  convert hshift.mul_right ρ⁻¹ using 1
  grind [pow_succ]

/-- The exact tail bound used in Lemma 5(a), valid in every complete normed space. -/
theorem series_truncation_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (ν m : ℕ) (ρ A : ℝ) (hp : 0 < ρ) (h1 : ρ < 1) (hA : 0 ≤ A)
    (hcoeff : ∀ k : ℕ, ‖f k‖ ≤ A * ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k) :
    ‖(∑' k : ℕ, f k) - ∑ k ∈ Finset.range (m + 1), f k‖ ≤
      A * ((m + 1 : ℕ) : ℝ) ^ ν * ρ ^ m *
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := by
  let w := fun k => ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k
  have hw := weighted_geometric_summable ν ρ hp h1
  have hmajor := hw.mul_left A
  have hcoeff' (k : ℕ) : ‖f k‖ ≤ A * w k := by
    grind
  have hnorm :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcoeff' hmajor
  have hf := hmajor.of_norm_bounded hcoeff'
  have htail : (∑' k : ℕ, f k) - ∑ k ∈ Finset.range (m + 1), f k =
      ∑' k : ℕ, f (k + (m + 1)) := by
    have h := hf.sum_add_tsum_nat_add (m + 1)
    simp [← h]
  have hn0 :=
    (summable_nat_add_iff (f := fun k => ‖f k‖) m).mpr hnorm
  have hn1 :=
    (summable_nat_add_iff (f := fun k => ‖f k‖) (m + 1)).mpr hnorm
  have htmono : (∑' k : ℕ, ‖f (k + (m + 1))‖) ≤ ∑' k : ℕ, ‖f (k + m)‖ := by
    have h := hn0.tsum_eq_zero_add
    simp only [zero_add] at h
    have he : (fun k : ℕ => ‖f (k + 1 + m)‖) = (fun k : ℕ => ‖f (k + (m + 1))‖) := by
      ext k
      ring
    simp [he, h]
  let C := A * ((m + 1 : ℕ) : ℝ) ^ ν * ρ ^ m
  have htbound (k : ℕ) : ‖f (k + m)‖ ≤ C * w k := by
    apply (hcoeff (k + m)).trans
    have hindex : (k + m + 1 : ℝ) ≤ (m + 1) * (k + 1) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
        (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (k + m + 1 : ℝ)) hindex ν
    have hpow' : (((k + m + 1 : ℕ) : ℝ)) ^ ν ≤
        ((m + 1 : ℕ) : ℝ) ^ ν * ((k + 1 : ℕ) : ℝ) ^ ν := by
      simpa [mul_pow] using hpow
    have hmul := mul_le_mul_of_nonneg_left hpow' hA
    have hmul' := mul_le_mul_of_nonneg_right hmul (pow_nonneg hp.le (k + m))
    dsimp [C, w]
    convert hmul' using 1 <;> rw [pow_add] <;> ring
  have hsbound :=
    Summable.tsum_le_tsum htbound hn0 (hw.mul_left C)
  rw [htail]
  calc
    _ ≤ ∑' k : ℕ, ‖f (k + (m + 1))‖ := norm_tsum_le_tsum_norm hn1
    _ ≤ ∑' k : ℕ, ‖f (k + m)‖ := htmono
    _ ≤ ∑' k : ℕ, C * w k := hsbound
    _ = _ := by rw [tsum_mul_left]

section
variable {R : Type*} [NormedRing R]

/-- A geometric factor raises the polynomial weight of the coefficient bound by one. -/
theorem coeff_mul_geometric_bound
    (f g : PowerSeries R) (ν k : ℕ) (ρ A B : ℝ) (hp : 0 < ρ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ i, ‖PowerSeries.coeff i f‖ ≤ A * ((i + 1 : ℕ) : ℝ) ^ ν * ρ ^ i)
    (hg : ∀ j, ‖PowerSeries.coeff j g‖ ≤ B * ρ ^ j) :
    ‖PowerSeries.coeff k (f * g)‖ ≤ A * B * ((k + 1 : ℕ) : ℝ) ^ (ν + 1) * ρ ^ k := by
  rw [PowerSeries.coeff_mul]
  calc
    _ ≤ ((Finset.HasAntidiagonal.antidiagonal k).card : ℝ) * (A * B * ((k + 1 : ℕ) : ℝ) ^ ν * ρ ^ k) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply norm_sum_le_of_le
      intro ij hij
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have hle : ij.1 + 1 ≤ k + 1 := by omega
      calc
        _ ≤ (A * ((ij.1 + 1 : ℕ) : ℝ) ^ ν * ρ ^ ij.1) * (B * ρ ^ ij.2) :=
          (norm_mul_le _ _).trans (mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity))
        _ = A * B * ((ij.1 + 1 : ℕ) : ℝ) ^ ν * ρ ^ k := by rw [← he, pow_add]; ring
        _ ≤ _ := by gcongr
    _ = _ := by simp [pow_succ]; ring

/-- Exact Cauchy product identity for absolutely summable coefficient sequences. -/
theorem coeff_mul_tsum [CompleteSpace R] (f g : PowerSeries R)
    (hf : Summable (fun i => ‖PowerSeries.coeff i f‖))
    (hg : Summable (fun i => ‖PowerSeries.coeff i g‖)) :
    (∑' k, PowerSeries.coeff k (f * g)) =
      (∑' i, PowerSeries.coeff i f) * ∑' j, PowerSeries.coeff j g := by
  simp_rw [PowerSeries.coeff_mul]
  exact (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg).symm

/-- The bound iterated along an ordered list of factors, also for noncommutative coefficients. -/
theorem coeff_mul_list_geometric_bound
    (f : PowerSeries R) (gs : List (PowerSeries R)) (ρ A B : ℝ) (hp : 0 < ρ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ k, ‖PowerSeries.coeff k f‖ ≤ A * ρ ^ k)
    (hg : ∀ g ∈ gs, ∀ k, ‖PowerSeries.coeff k g‖ ≤ B * ρ ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k (f * gs.prod)‖ ≤ A * B ^ gs.length * ((k + 1 : ℕ) : ℝ) ^ gs.length * ρ ^ k := by
  induction gs using List.reverseRecOn generalizing k with
  | nil => simpa using hf k
  | append_singleton gs g ih =>
    rw [List.prod_append, List.prod_singleton, ← mul_assoc]
    have h := coeff_mul_geometric_bound (f * gs.prod) g gs.length k ρ
      (A * B ^ gs.length) B hp (by positivity) hB
      (ih (fun i hi => hg i (List.mem_append_left _ hi))) (hg g (by simp))
    simpa only [List.length_append, List.length_singleton, pow_succ B, mul_assoc] using h

end

theorem coeff_finsetProd_geometric_bound {R I : Type*} [NormedCommRing R] [NormOneClass R]
    (s : Finset I) (f : I → PowerSeries R) (ρ B : ℝ) (hp : 0 < ρ) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, ∀ k, ‖PowerSeries.coeff k (f i)‖ ≤ B * ρ ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k (∏ i ∈ s, f i)‖ ≤ B ^ s.card * ((k + 1 : ℕ) : ℝ) ^ s.card * ρ ^ k := by
  have h := coeff_mul_list_geometric_bound (R := R) 1 (s.toList.map f) ρ 1 B hp zero_le_one hB
    (fun j => by cases j <;> simp [PowerSeries.coeff_one, hp.le])
    (by simpa only [List.forall_mem_map, Finset.mem_toList] using hf) k
  simpa [Finset.prod_map_toList] using h

end RoughRegime.SeriesBounds
