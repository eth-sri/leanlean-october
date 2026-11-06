import GradedNear.Tactics
import GradedNear.SieveError

import GradedNear.Entries
import GradedNear.Bookkeeping

/-!
# The Gram form bound

For all large `q`, entries of height `≤ T ≤ (log q)/3`, the safe anchor at height `2T + 1`
and `a ≥ 0`:
`𝓛⁻¹ Σ_{j,k} a_j a_k Re primeSum(χ_j χ_k⁻¹, g, s_{jk}) ≤
  Σ_j (∫ g e^{(s₁ - 2δ_j)u} - d₁ + e_j) a_j² + (d₁ + ε)(Σ a)²` (paper §8.5).
-/

open Complex MeasureTheory Finset

namespace GradedNear

/-- The real part of the Laplace transform is invariant under conjugation. -/
lemma laplace_re_conj (g : ℝ → ℝ) (z : ℂ) :
    (laplace g ((starRingEnd ℂ) z)).re = (laplace g z).re := by
  unfold laplace
  conv_rhs => rw [← Complex.conj_re, ← integral_conj]
  simp [← Complex.exp_conj]

set_option maxHeartbeats 1000000 in
/-- **The Gram form bound.** -/
theorem gram_form_bound (hX31 : XylourisLemma31) (hX32 : XylourisLemma32) (D : NearData)
    (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ [NeZero q], ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι), HeightBound E T → Offsets E D →
      ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
        (∑ j, ∑ k, a j * a k * (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re) /
            Real.log q ≤
          ∑ j, (gramDiag D (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
            (D.d₁ + ε) * (∑ j, a j) ^ 2 := by
  set K : ℝ := |D.s₁| + 2 * ∑ δ ∈ D.Δ, δ
  obtain ⟨C, q₁, hC⟩ := hX31 D.g D.xg D.Bg hD.g_cond1
  obtain ⟨δ, hδ0, hδ1, q₂, hC₂⟩ := hX32 D.g D.xg D.Bg hD.g_cond1
    (hD.g_cond2.nonneg 0 le_rfl) ε hε

  filter_upwards [Filter.eventually_ge_atTop q₁, Filter.eventually_ge_atTop q₂,
    eventually_loglog_ge K,  ((Real.tendsto_log_atTop.comp
      tendsto_log_nat_atTop).const_div_atTop C).eventually_le_const hε
     ] with q hq₁ hq₂ hlog hsmall
  obtain ⟨hsq, hq2⟩ := hlog
  dsimp at hsmall
  intro _ T hT hTq hsafe ι _ E hγ hΔ a ha
  have hℓ := log_q_pos hq2
  classical
  -- bounds on the Gram point
  have hre j k : |(sjk D E j k).re - 1| ≤ K / Real.log q := by
    suffices |D.s₁ - E.δ j - E.δ k| ≤ K by
      simpa [sjk, abs_div, abs_of_pos hℓ, -Complex.natCast_log] using
        div_le_div_of_nonneg_right this hℓ.le
    have hnn := hD.Δ_nonneg
    grind [Finset.single_le_sum]
  have him : ∀ j k, |(sjk D E j k).im| ≤ 2 * T := by

    simp [sjk, -Complex.natCast_log]
    grind
  have him' : ∀ j k, |(sjk D E j k).im| ≤ Real.log q := by grind
  have hreg (j k) : LemmaRegion q (sjk D E j k) :=
    ⟨(hre j k).trans (by gcongr), him' j k⟩
  -- the bookkeeping
  let M j k := (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re / Real.log q
  let R j k := pairValue q D E j k
  have hR j k : R j k = R k j := by
    dsimp only [R]
    rw [← laplace_re_conj]

    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hsame j k : E.χ j = E.χ k → M j k ≤ R j k + ε := by
    intro hjk
    dsimp only [M, R]
    rw [mul_inv_eq_one.mpr hjk]
    have hr := (Complex.re_le_norm _).trans (hC q hq₁ _ (hreg j k))
    rw [Complex.sub_re, Complex.re_ofReal_mul] at hr
    convert show (primeSum (1 : DirichletCharacter ℂ q) D.g (sjk D E j k)).re / Real.log q ≤
      (laplace D.g ((sjk D E j k - 1) * ↑(Real.log q))).re + ε from by
        rw [div_le_iff₀ hℓ]
        linear_combination hr + Real.log q * hsmall using 1
    congr 3
    unfold sjk
    apply Complex.ext <;> simp [-Complex.natCast_log] <;> grind
  have hdiff j k : E.χ j ≠ E.χ k → M j k ≤ D.d₁ + ε := by
    intro hjk
    dsimp only [M, R]
    have h1 := mul_inv_eq_one.not.mpr hjk
    have hzs : 0 ≤ zeroSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k) δ := by
      refine finsum_nonneg fun ρ => finsum_nonneg fun hρ => ?_
      refine mul_nonneg (Nat.cast_nonneg _) (hD.g_cond2.re_nonneg _ ?_)
      have hle : ρ.re ≤ (sjk D E j k).re := by


        have hsafe' := hsafe _ h1 ρ hρ.2 (by
          have h2 : |ρ.im - (sjk D E j k).im| ≤ δ := by
            have := Complex.abs_im_le_norm (1 + ↑ (sjk D E j k).im * I - ρ)
            rw [show (1 + ↑ (sjk D E j k).im * I - ρ).im = (sjk D E j k).im - ρ.im by
              simp] at this
            grind
          grind
        )
        simp [sjk, -Complex.natCast_log]
        have hδs : D.s₁ - E.δ j - E.δ k ≤ D.s₁ := by
          linarith [hD.Δ_nonneg _ (hΔ j), hD.Δ_nonneg _ (hΔ k)]
        have :=
          div_le_div_of_nonneg_right hδs hℓ.le
        linarith
      rw [Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re]
      positivity
    have hb := hC₂ q hq₂ _ h1 _ (hreg j k)
    unfold NearData.d₁
    field_simp; nlinarith
  have hdiag j : R j j = gramDiag D (E.δ j) := by
    dsimp only [R]
    simp only [sub_self, zero_mul, Complex.ofReal_zero, add_zero, laplace]
    simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    rw [integral_complex_ofReal, Complex.ofReal_re]

    ring
  -- excess over `D.d₁`, only on distinct pairs of the same class
  set P : ι → ι → ℝ := fun j k => if k ≠ j ∧ E.χ k = E.χ j then max 0 (R j k - D.d₁) else 0
  have hex j :  ∑ k, P j k  = pairExcess D E j := by
    dsimp only [P]
    grind [GradedNear.pairExcess, GradedNear.sameCharOthers, Finset.sum_filter]
  have hPsymm : ∀ j k, P j k = P k j := by clear_value R; aesop
  -- the pair excess via 2 a_j a_k ≤ a_j² + a_k²
  have hpair : ∑ j, ∑ k, a j * a k * P j k ≤ ∑ j, (∑ k, P j k) * a j ^ 2 := by
    clear_value M R
    have h : 0 ≤ ∑ j, ∑ k, (a j - a k) ^ 2 * P j k := by dsimp only [P]; positivity
    linear_combination (norm := sum_ring_nf) h / 2
    norm_num
    rw [sum_comm]
    simp_rw [hPsymm]
    rfl
  -- assemble
  simp_rw [Finset.sum_div, mul_div_assoc]
  refine (sum_le_sum fun j _ => sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left
      (show M j k ≤ D.d₁ + ε + (if k = j then R j k - D.d₁ else 0) + P j k by clear_value M R; grind)
      (mul_nonneg (ha j) (ha k))).trans ?_
  simp only [mul_add, mul_ite_zero, sum_add_distrib]
  grw [hpair]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [hex, hdiag]
  clear_value M R
  apply le_of_eq
  sum_ring

end GradedNear
