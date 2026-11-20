module

public import GradedNear.LaplaceDecay

public import GradedNear.Entries
public import GradedNear.Bookkeeping

/-!
# The Gram form bound

For all large `q`, entries of height `≤ T ≤ (log q)/3`, the safe anchor at height `2T + 1`
and `a ≥ 0`:
`𝓛⁻¹ Σ_{j,k} a_j a_k Re primeSum(χ_j χ_k⁻¹, g, s_{jk}) ≤
  Σ_j (∫ g e^{(s₁ - 2δ_j)u} - d₁ + e_j) a_j² + (d₁ + ε)(Σ a)²` (paper §8.5).
-/

@[expose] public section

open Complex MeasureTheory Filter
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

/-- Real test functions have the same transform real part at reflected arguments. -/
lemma laplace_reflect (f : ℝ → ℝ) {x x' y y' : ℝ} (hx : x = x') (hy : y = -y') :
    (laplace f xy[x,y]).re = (laplace f xy[x',y']).re := by
  subst x'; subst y
  rw [← conj_re (laplace f xy[x,y']), laplace, laplace, ← integral_conj]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp [← Complex.exp_conj]

variable {q : ℕ} {ι : Type*}

lemma pairValue_symm (D : NearData) (E : Entries q ι) (j k : ι) :
    gramAt[q] D E j k = gramAt[q] D E k j := by
  apply laplace_reflect <;> ring

lemma pairValue_self (D : NearData) (E : Entries q ι) (j : ι) :
    gramAt[q] D E j j = gramDiag D (E.δ j) := by
  simp only [sub_self, zero_mul, ofReal_zero, add_zero, sub_sub, ← two_mul,
    laplace_real, neg_neg]

lemma offset_bound {D : NearData} (hD : D.Valid) (s : ℝ) {δ : ℝ} (hδ : δ ∈ D.Δ) :
    |s - δ| ≤ |s| + ∑ d ∈ D.Δ, d := by
  grw [abs_sub, abs_of_nonneg (hD.Δ_nonneg _ hδ), Finset.single_le_sum hD.Δ_nonneg hδ]

/-- `|σ_{jk}| ≤ |s₁| + 2 Σ_{δ ∈ Δ} δ` for offsets in `Δ`. -/
lemma sigma_bound (D : NearData) (hD : D.Valid) {δj δk : ℝ} (hj : δj ∈ D.Δ) (hk : δk ∈ D.Δ) :
    |D.s₁ - δj - δk| ≤ |D.s₁| + 2 * ∑ δ ∈ D.Δ, δ := by
  linarith [offset_bound hD (D.s₁ - δj) hk, offset_bound hD D.s₁ hj]

/-- **The Gram form bound.** -/
theorem gram_form_bound (hX31 : XylourisLemma31) (hX32 : XylourisLemma32) (D : NearData)
    (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ [NeZero q] {ι : Type} [Fintype ι] (E : Entries q ι) (w : Window D E),
      SafeAnchor q D.s₁ (2*w.T+1) →
      ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
        (∑ j, ∑ k, a j * a k * (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re) /
            Real.log q ≤
          ∑ j, (gramDiag D (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
            (D.d₁ + ε) * (∑ j, a j) ^ 2 := by
  classical
  let K := |D.s₁| + 2 * ∑ δ ∈ D.Δ, δ
  obtain ⟨δ, _, hδ, q₂, hq₂⟩ := hX32 _ _ _ hD.g_cond1 (hD.g_cond2.nonneg 0 le_rfl) _ hε
  filter_upwards [eventually_region K, principal_entry hX31 hD.g_cond1 hε, Filter.eventually_ge_atTop q₂]
    with q ⟨hℓ, hreg⟩ hpr hq _ ι _ E w hsafe a ha
  have hs j k := hreg _ _ (sigma_bound D hD (w.offsets j) (w.offsets k)) (by linarith [w.gap j k, w.cap])
  simp_rw [Finset.sum_div, mul_div_assoc]
  refine (gram_bookkeeping E.χ
    _ _ (pairValue_symm D E) a ha D.d₁ ε ?_ ?_).trans ?_
  rotate_left 2
  · simp only [pairValue_self]
    rfl
  · intro j k (h : E.χ j = E.χ k)
    simpa only [h, mul_inv_cancel, sjk, point_arg _ _ _ hℓ.ne', one_re, one_im, sub_self,
      zero_mul, zero_sub, sub_zero] using hpr _ (hs j k)
  · intro j k h
    have hχ := mt mul_inv_eq_one.mp h
    have hn := hq₂ q hq _ hχ _ (hs j k)
    have hz : 0 ≤ zeroSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k) δ := by
      refine zeroSum_nonneg hD.g_cond2 fun ρ hρ hdist => ?_
      have hd := (abs_im_le_norm _).trans hdist
      simp only [sub_im, add_im, one_im, mul_I_im, ofReal_re, ofReal_im, zero_add, sjk] at hd
      have hρim : |ρ.im| ≤ 2*w.T + 1 := by
        linarith [abs_sub_comm (E.γ j - E.γ k) ρ.im, abs_sub_abs_le_abs_sub ρ.im (E.γ j - E.γ k), w.gap j k]
      apply (hsafe _ hχ ρ hρ hρim).trans
      simp only [sjk, point_re]; gcongr
      linarith [hD.Δ_nonneg _ (w.offsets j), hD.Δ_nonneg _ (w.offsets k)]
    rw [div_le_iff₀ hℓ]
    dsimp [NearData.d₁]; nlinarith only [hn, mul_nonneg hℓ.le hz]

end GradedNear
