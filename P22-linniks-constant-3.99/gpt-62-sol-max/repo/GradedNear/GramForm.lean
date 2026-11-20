module

public import GradedNear.Expansion
public import GradedNear.Bookkeeping

/-!
# The Gram form bound

For all large `q`, entries of height `≤ T ≤ (log q)/3`, the safe anchor at height `2T + 1`
and `a ≥ 0`:
`𝓛⁻¹ Σ_{j,k} a_j a_k Re primeSum(χ_j χ_k⁻¹, g, s_{jk}) ≤
  Σ_j (∫ g e^{(s₁ - 2δ_j)u} - d₁ + e_j) a_j² + (d₁ + ε)(Σ a)²` (paper §8.5).
-/

@[expose] public section

open Complex MeasureTheory Filter Finset
open scoped ArithmeticFunction.vonMangoldt ComplexConjugate

noncomputable section

namespace GradedNear

/-- Conjugating the argument of a real Laplace transform leaves its real part unchanged. -/
lemma laplace_re_conj (g : ℝ → ℝ) (z : ℂ) :
    (laplace g ((starRingEnd ℂ) z)).re = (laplace g z).re := by
  rw [← Complex.conj_re (laplace g z)]
  simp [laplace, ← integral_conj, ← Complex.exp_conj]

lemma laplace_integrand_real (a x t : ℝ) :
    (a : ℂ) * cexp (-((x : ℂ) * t)) = ((a * Real.exp (-(x * t)) : ℝ) : ℂ) := by
  push_cast; rfl

/-- The diagonal Gram value `∫ g(u) e^{(s₁ - 2δ) u} du`. -/
def gramDiag (D : NearData) (δ : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), D.g u * Real.exp ((D.s₁ - 2 * δ) * u)

variable {q : ℕ} {ι : Type*}

/-- The test point of a Gram entry. -/
def sjk (D : NearData) (E : Entries q ι) (j k : ι) : ℂ :=
  spectralPoint q (D.s₁ - E.δ j - E.δ k) (E.γ j - E.γ k)

/-- The value `R_{jk} = Re G(-σ_{jk} + i y_{jk})` of a same-character Gram entry. -/
def pairValue (D : NearData) (E : Entries q ι) (j k : ι) : ℝ :=
  (laplace D.g (((-(D.s₁ - E.δ j - E.δ k)) : ℝ) +
    (((E.γ j - E.γ k) * Real.log q : ℝ) : ℂ) * I)).re

lemma pairValue_symm (D : NearData) (E : Entries q ι) (j k : ι) :
    pairValue D E j k = pairValue D E k j := by
  unfold pairValue
  rw [← laplace_re_conj]
  congr 2
  simp [-natCast_log]; push_cast; ring

lemma pairValue_self (D : NearData) (E : Entries q ι) (j : ι) :
    pairValue D E j j = gramDiag D (E.δ j) := by
  simp only [pairValue, gramDiag, sub_self, zero_mul, ofReal_zero, add_zero,
    laplace, laplace_integrand_real, neg_mul, neg_neg, integral_complex_ofReal, ofReal_re, sub_sub, two_mul]

/-- `|σ_{jk}| ≤ |s₁| + 2 Σ_{δ ∈ Δ} δ` for offsets in `Δ`. -/
lemma sigma_bound (D : NearData) (hD : D.Valid) {δj δk : ℝ} (hj : δj ∈ D.Δ) (hk : δk ∈ D.Δ) :
    |D.s₁ - δj - δk| ≤ |D.s₁| + 2 * ∑ δ ∈ D.Δ, δ := by
  linarith [abs_sub (D.s₁ - δj) δk, abs_sub D.s₁ δj, abs_of_nonneg (hD.Δ_nonneg _ hj),
    abs_of_nonneg (hD.Δ_nonneg _ hk), single_le_sum hD.Δ_nonneg hj, single_le_sum hD.Δ_nonneg hk]

/-- **The Gram form bound.** -/
theorem gram_part_bound (hX31 : XylourisLemma31) (hX32 : XylourisLemma32) (D : NearData)
    (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, ∀ [NeZero q], ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι), (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
      ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) → ∀ N : ℕ, ⌊(q : ℝ) ^ D.xg⌋₊ ≤ N →
        (∑ n ∈ Ioc 0 N, Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) * ‖Yn E a n‖ ^ 2) /
          Real.log q ≤
          ∑ j, (gramDiag D (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
            (D.d₁ + ε) * (∑ j, a j) ^ 2 := by
  let K := |D.s₁| + 2 * ∑ δ ∈ D.Δ, δ
  obtain ⟨C, q₁, h₁⟩ := hX31 D.g D.xg D.Bg hD.g_cond1
  obtain ⟨δ, -, hδ, q₂, h₂⟩ := hX32 D.g D.xg D.Bg hD.g_cond1 (hD.g_cond2.nonneg 0 le_rfl) ε hε
  have hC := tendsto_const_nhds (x := C) |>.div_atTop tendsto_loglog_nat
  filter_upwards [eventually_ge_atTop q₁, eventually_ge_atTop q₂, hC.eventually_le_const hε,
    eventually_loglog_ge K] with q hq₁ hq₂ hC ⟨hK, hq⟩
  intro _ T hT hTq hsafe ι _ E hγ hΔ a ha N hN
  have hℓ := log_q_pos hq
  have him j k : |(sjk D E j k).im| ≤ 2 * T := by
    grind [sjk, spectralPoint_im]
  have hs j k : LemmaRegion q (sjk D E j k) :=
    spectralPoint_region hq ((sigma_bound D hD (hΔ j) (hΔ k)).trans hK)
      (by simpa only [sjk, spectralPoint_im] using (him j k).trans (show 2 * T ≤ _ by linarith))
  let M j k := (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re / Real.log q
  have hsame j k (e : E.χ j = E.χ k) : M j k ≤ pairValue D E j k + ε := by
    dsimp only [M]
    rw [e, mul_inv_cancel, div_le_iff₀ hℓ]
    have H := (Complex.re_le_norm _).trans (h₁ q hq₁ _ (hs j k))
    simp only [sub_re, re_ofReal_mul, sjk] at H
    rw [spectralPoint_sub _ _ _ hℓ.ne', mul_comm C, mul_div_assoc] at H
    simp only [one_re, one_im, sub_self, zero_mul, zero_sub, sub_zero] at H
    change (primeSum (1 : DirichletCharacter ℂ q) D.g (sjk D E j k)).re - Real.log q * pairValue D E j k ≤ _ at H
    nlinarith
  have hdiff j k (e : E.χ j ≠ E.χ k) : M j k ≤ D.d₁ + ε := by
    have hχ : E.χ j * (E.χ k)⁻¹ ≠ 1 := fun h => e (mul_inv_eq_one.mp h)
    let s := sjk D E j k
    have hz ρ (hρ : DirichletCharacter.LFunction (E.χ j * (E.χ k)⁻¹) ρ = 0)
        (hd : ‖1 + (s.im : ℂ) * I - ρ‖ ≤ δ) : ρ.re ≤ s.re := by
      have hdist := Complex.abs_im_le_norm ((1 + (s.im : ℂ) * I) - ρ)
      simp [abs_sub_comm _ ρ.im] at hdist
      have hb : |ρ.im| ≤ 2 * T + 1 := by
        linarith [abs_sub_abs_le_abs_sub ρ.im s.im, him j k]
      refine (hsafe _ hχ ρ hρ hb).trans ?_
      simp only [s, sjk, spectralPoint_re]
      gcongr; linarith [hD.Δ_nonneg _ (hΔ j), hD.Δ_nonneg _ (hΔ k)]
    have hzs : 0 ≤ zeroSum (E.χ j * (E.χ k)⁻¹) D.g s δ := by
      unfold zeroSum
      refine finsum_nonneg fun ρ => finsum_nonneg fun hρ =>
        mul_nonneg (Nat.cast_nonneg _) (hD.g_cond2.re_nonneg _ ?_)
      simpa [Complex.mul_re, -Complex.natCast_log] using mul_nonneg (sub_nonneg.mpr (hz ρ hρ.2 hρ.1)) hℓ.le
    dsimp only [M, NearData.d₁]
    rw [div_le_iff₀ hℓ]
    linarith only [h₂ q hq₂ _ hχ s (hs j k), mul_nonneg hℓ.le hzs]
  classical
  let : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  let P j k := if k ≠ j ∧ E.χ k = E.χ j then max 0 (pairValue D E j k - D.d₁) else 0
  rw [weighted_Yn]
  simp_rw [phase_pair, mul_comm (D.g (tn q _)), ← mul_assoc (Λ _ / _),
    ← primeSum_eq_phase_sum hq _ _ hD.g_cond1.vanish hN, ← sub_sub]
  have H := quadratic_rows M P a (fun j => pairValue D E j j - D.d₁) (D.d₁ + ε) ha
    (fun j k => by dsimp [P]; split_ifs <;> positivity) ?_ ?_
  · simpa only [M, sjk, P, pairValue_self, pairExcess, sameCharOthers, sum_filter] using! H
  · intro j k
    simp [P, ne_comm (a := k), eq_comm (a := E.χ k), pairValue_symm D E j k]
  · grind

end GradedNear
