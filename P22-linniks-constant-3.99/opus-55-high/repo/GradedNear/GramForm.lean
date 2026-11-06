module

public import GradedNear.Entries

/-!
# The Gram form bound

For all large `q`, entries of height `≤ T ≤ (log q)/3`, the safe anchor at height `2T + 1`
and `a ≥ 0`:
`𝓛⁻¹ Σ_{j,k} a_j a_k Re primeSum(χ_j χ_k⁻¹, g, s_{jk}) ≤
  Σ_j (∫ g e^{(s₁ - 2δ_j)u} - d₁ + e_j) a_j² + (d₁ + ε)(Σ a)²` (paper §8.5).
Principal entries come from [X, Lemma 3.1], non-principal ones from [X, Lemma 3.2].
-/

@[expose] public section

open Complex MeasureTheory Finset

noncomputable section

namespace GradedNear
/-- Gram bookkeeping: with `M_{jk} ≤ R_{jk} + ε` on same-character pairs and `M_{jk} ≤ d + ε`
otherwise, the pair excess uses `2 a_j a_k ≤ a_j² + a_k²`. -/
lemma gram_bookkeeping {ι α : Type*} [Fintype ι] (χ : ι → α) (M R : ι → ι → ℝ)
    (hR : ∀ j k, R j k = R k j) (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (d ε : ℝ)
    (hsame : ∀ j k, χ k = χ j → M j k ≤ R j k + ε) (hdiff : ∀ j k, χ k ≠ χ j → M j k ≤ d + ε) :
    ∑ j, ∑ k, a j * a k * M j k ≤
      ∑ j, (R j j - d + ∑ k ∈ sameCharOthers χ j, max 0 (R j k - d)) * a j ^ 2 +
        (d + ε) * (∑ j, a j) ^ 2 := by
  classical
  set P : ι → ι → ℝ := fun j k => if k ∈ sameCharOthers χ j then max 0 (R j k - d) else 0
  have hP : ∀ j k, 0 ≤ P j k := fun j k => by grind
  calc _ ≤ ∑ j, ∑ k, (a j * a k * (d + ε) + (if k = j then a j * a k * (R j k - d) else 0) +
        (a j ^ 2 * P j k + a k ^ 2 * P k j) / 2) := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
        have := hP j k; have := hP k j; have := mul_nonneg (ha j) (ha k)
        by_cases hkj : k = j
        · subst hkj; simp; nlinarith [hsame k k rfl]
        by_cases hs : χ k = χ j
        · simp [P, sameCharOthers, hkj, hs, Ne.symm hkj, hR k j]
          nlinarith [hsame j k hs, le_max_right 0 (R j k - d), mul_nonneg (sq_nonneg (a j - a k)) (le_max_left 0 (R j k - d))]
        · simp [hkj]; nlinarith [hdiff j k hs]
    _ = _ := by
      simp [sum_add_distrib, ← sum_div, sum_ite_eq', ite_true]
      rw [sum_comm (f := fun j k => a k ^ 2 * P k j)]
      simp [P, ← mul_sum, sum_ite_mem, univ_inter, ← sum_mul]
      simp [add_mul, sum_add_distrib, sq, mul_comm (a _ * a _)]
      ring
/-- The real part of the Laplace transform of a real function is conjugation invariant. -/
lemma laplace_re_conj (g : ℝ → ℝ) (z : ℂ) :
    (laplace g ((starRingEnd ℂ) z)).re = (laplace g z).re := by
  rw [← conj_re (laplace g z), laplace, laplace, ← integral_conj]
  simp [map_mul, conj_ofReal, ← exp_conj, map_neg]

/-- **The Gram form bound.** -/
theorem gram_form_bound (hX31 : XylourisLemma31) (hX32 : XylourisLemma32) (D : NearData)
    (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι), (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
      ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
        (∑ j, ∑ k, a j * a k * (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re) /
            Real.log q ≤
          ∑ j, ((∫ u in Set.Ioi (0 : ℝ), D.g u * Real.exp ((D.s₁ - 2 * E.δ j) * u)) - D.d₁ +
            pairExcess D E j) * a j ^ 2 + (D.d₁ + ε) * (∑ j, a j) ^ 2 := by
  obtain ⟨C, q₁, hC⟩ := hX31 _ _ _ hD.g_cond1
  obtain ⟨δ, -, hδ1, q₂, hq₂⟩ := hX32 _ _ _ hD.g_cond1 (hD.g_cond2.nonneg 0 le_rfl) ε hε
  obtain ⟨q₃, hq₃⟩ := eventually_loglog_ge (max (|D.s₁| + 2 * ∑ δ ∈ D.Δ, δ) (|C| / ε + 1))
  refine ⟨max q₁ (max q₂ q₃), fun q _ hq T hT hTq hsafe ι _ E hγ hΔ a ha => ?_⟩
  simp at hq
  obtain ⟨hsq, hll, hq2⟩ := hq₃ q hq.2.2
  have hℓ := log_q_pos hq2
  have hs : ∀ j k, (sjk D E j k).re = 1 - (D.s₁ - E.δ j - E.δ k) / Real.log q ∧
      (sjk D E j k).im = E.γ j - E.γ k := by simp [sjk, -ofReal_sub]
  have hσ : ∀ j k, 0 ≤ E.δ j + E.δ k ∧ E.δ j + E.δ k ≤ 2 * ∑ δ ∈ D.Δ, δ := fun j k =>
    ⟨add_nonneg (hD.Δ_nonneg _ (hΔ j)) (hD.Δ_nonneg _ (hΔ k)), by
      linarith [Finset.single_le_sum hD.Δ_nonneg (hΔ j), Finset.single_le_sum hD.Δ_nonneg (hΔ k)]⟩
  have hreg : ∀ j k, LemmaRegion q (sjk D E j k) := fun j k => by
    rw [LemmaRegion, (hs j k).1, (hs j k).2, sub_sub_cancel_left, abs_neg, abs_div, abs_of_pos hℓ]
    refine ⟨div_le_div_of_nonneg_right ((abs_le.2 ⟨?_, ?_⟩).trans ((le_max_left ..).trans hsq))
      hℓ.le, ?_⟩ <;>
      linarith [neg_abs_le D.s₁, le_abs_self D.s₁, hσ j k, abs_sub (E.γ j) (E.γ k), hγ j, hγ k]
  have key := gram_bookkeeping E.χ
    (fun j k => (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re / Real.log q)
    (fun j k => (laplace D.g (((-(D.s₁ - E.δ j - E.δ k)) : ℝ) +
      (((E.γ j - E.γ k) * Real.log q : ℝ) : ℂ) * I)).re)
    (fun j k => by
      rw [← laplace_re_conj]; congr 2; simp only [map_add, map_mul, conj_ofReal, conj_I]; push_cast; ring) a ha D.d₁ ε ?_ ?_
  · rw [Finset.sum_div]
    simp_rw [Finset.sum_div, mul_div_assoc]
    refine key.trans_eq ?_
    unfold pairExcess
    simp only [sub_self, zero_mul, ofReal_zero, add_zero, sub_sub, ← two_mul, laplace, ofReal_neg, neg_mul, neg_neg, ← ofReal_mul, ← ofReal_exp, integral_complex_ofReal, ofReal_re]
  · intro j k h
    rw [h, mul_inv_cancel, div_le_iff₀ hℓ]
    have h1 := (re_le_norm _).trans (hC q hq.1 _ (hreg j k))
    rw [sub_re, re_ofReal_mul, show (sjk D E j k - 1) * (Real.log q : ℂ) =
      (((-(D.s₁ - E.δ j - E.δ k)) : ℝ) : ℂ) + (((E.γ j - E.γ k) * Real.log q : ℝ) : ℂ) * I by
        rw [sjk]; generalize Real.log q = L at hℓ; push_cast; field_simp [hℓ.ne']; ring] at h1
    have hLL := (le_max_right ..).trans hll
    have h2 := (div_le_iff₀ hε).1 (by linarith : |C| / ε ≤ Real.log (Real.log q))
    have : C * Real.log q / Real.log (Real.log q) ≤ ε * Real.log q := by
      rw [div_le_iff₀ (by linarith [div_nonneg (abs_nonneg C) hε.le])]
      nlinarith [le_abs_self C]
    linarith
  · intro j k h
    have h1 : E.χ j * (E.χ k)⁻¹ ≠ 1 := fun e => h (mul_inv_eq_one.1 e).symm
    have h2 := hq₂ q hq.2.1 _ h1 _ (hreg j k)
    have : 0 ≤ zeroSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k) δ := by
      refine finsum_nonneg fun ρ => finsum_nonneg fun hρ => mul_nonneg (Nat.cast_nonneg _)
        (hD.g_cond2.re_nonneg _ ?_)
      rw [re_mul_ofReal, sub_re, (hs j k).1]
      have h3 : |(sjk D E j k).im - ρ.im| ≤ δ := by simpa using (abs_im_le_norm _).trans hρ.1
      have : |ρ.im| ≤ 2 * T + 1 := by grind
      have := hsafe _ h1 ρ hρ.2 this
      have := div_le_div_of_nonneg_right (by linarith [hσ j k] : D.s₁ - E.δ j - E.δ k ≤ D.s₁) hℓ.le
      nlinarith
    rw [div_le_iff₀ hℓ]
    unfold NearData.d₁
    nlinarith
end GradedNear
