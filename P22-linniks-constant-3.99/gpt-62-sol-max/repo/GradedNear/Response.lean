module

public import GradedNear.LaplaceDecay
public import GradedNear.ZeroFinite

/-!
# The response lemma (paper Lemma 8.7)

For an entry `(χ, γ, σ)`, the response `R = -𝓛⁻¹ Re Σ Λ(n) χ(n) n^{-((1 - σ/𝓛) + iγ)} f(t_n)`
is bounded below by the zeros kept in a finite set `S` of zeros of `L(s, χ)` in the local disc:
`R ≥ Σ_{ρ ∈ S} m_ρ Re F((1 - Re ρ)𝓛 - σ + i(γ - Im ρ)𝓛) - f(0)/6 - η`, provided every disc zero
not in `S` either lies to the right of the anchor (`(1 - Re ρ)𝓛 ≥ σ`) or is at normalized
height distance `≥ M`, and at most `K₀` of the latter (with multiplicity) lie to the left.

Proof: [X, Lemma 3.2]; the disc zeros are finite; zeros to the right have `Re F ≥ 0` by
Condition 2; the adverse zeros have `|F| ≤ η/(2(K₀+1))` by the decay of `F`.
-/

@[expose] public section

open Complex Finset Filter
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

lemma zeroTerm_nonneg {f : ℝ → ℝ} (hf : Condition2 f) {q : ℕ} {σ γ : ℝ} {ρ : ℂ}
    (h : σ ≤ zeroOffset q ρ) : 0 ≤ zeroTerm f q σ γ ρ :=
  hf.re_nonneg _ (by simpa [-natCast_log] using sub_nonneg.mpr h)

/-- **The response lemma** (paper Lemma 8.7; [X, Lemma 3.2]). Fix a test `f` satisfying Conditions 1
and 2, a bound `σmax` for the anchors, a count `K₀` and `η > 0`. There are a separation `M > 0`, a
disc radius `δ < 1` and a `q₀` such that the following holds for `q ≥ q₀`, a non-principal `χ`,
an anchor `|σ| ≤ σmax` and a height `|γ| ≤ log q`. Keep a finite set `S` of zeros of `L(s, χ)` in
the disc of radius `δ` about `1 + iγ`. Suppose every other disc zero with `λ_ρ = (1 - Re ρ) log q
< σ` is at normalized height distance `≥ M`, and there are at most `K₀` of them, with
multiplicity. Then the response of `(χ, γ, σ)` is at least
`Σ_{ρ ∈ S} m_ρ Re F((λ_ρ - σ) + i(γ - Im ρ) log q) - f(0)/6 - η`. -/
theorem response_lemma (hX32 : XylourisLemma32) {f : ℝ → ℝ} {x₀ B : ℝ}
    (hf1 : Condition1 f x₀ B) (hf2 : Condition2 f) (σmax : ℝ) (K₀ : ℕ) {η : ℝ}
    (hη : 0 < η) :
    SeparatedModuli[M, δ, q =>
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ σ γ : ℝ, |σ| ≤ σmax → |γ| ≤ Real.log q →
      ∀ Sz : Finset ℂ,
        (∀ ρ ∈ Sz, DirichletCharacter.LFunction χ ρ = 0 ∧ discGap γ ρ ≤ δ) →
        (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → discGap γ ρ ≤ δ →
          ρ ∉ Sz → zeroOffset q ρ < σ → M ≤ heightGap q γ ρ) →
        (∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
            discGap γ ρ ≤ δ ∧ ρ ∉ Sz ∧ zeroOffset q ρ < σ},
          zmult χ ρ) ≤ K₀ →
        ∑ ρ ∈ Sz, zmult χ ρ * zeroTerm f q σ γ ρ - f 0 / 6 - η ≤ responseAt χ f σ γ] := by
  obtain ⟨δ, hδ0, hδ1, q₁, hq₁⟩ := hX32 f x₀ B hf1 (hf2.nonneg 0 le_rfl) (η / 2) (half_pos hη)
  let ε' := η / 2 / ((K₀ : ℝ) + 1)
  obtain ⟨M, hM, hdecay⟩ := laplace_decay hf1 σmax (ε := ε') (by dsimp [ε']; positivity)
  refine ⟨M, hM, δ, hδ0, hδ1, eventually_neZero ?_⟩
  filter_upwards [eventually_ge_atTop q₁, eventually_loglog_ge σmax] with q hq1 ⟨hsq, hq2'⟩
  intro _ χ hχ σ γ hσ hγ Sz hSz hsep hK
  have hℓ := log_q_pos hq2'
  let s := spectralPoint q σ γ
  have hX := hq₁ q hq1 χ hχ s (spectralPoint_region hq2' (hσ.trans hsq) hγ)
  classical
  let hZ := LFunction_zeros_finite hχ (1 + (s.im : ℂ) * I) δ
  let Z := hZ.toFinset
  have hmem ρ : ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧ discGap γ ρ ≤ δ := by
    simp [Z, s, and_comm]
  rw [zeroSum, finsum_mem_eq_finite_toFinset_sum _ hZ] at hX
  simp_rw [s, spectralPoint_sub σ γ _ hℓ.ne', ← zeroTerm.eq_def] at hX
  rw [← sum_sdiff (fun ρ hρ => (hmem ρ).mpr (hSz ρ hρ))] at hX
  let U := Z \ Sz
  let A := U.filter fun ρ => zeroOffset q ρ < σ
  have hmass : ∑ ρ ∈ A, zmult χ ρ ≤ K₀ := by
    rw [← finsum_mem_coe_finset]
    simp_all [A, U, and_assoc]
  have hsum : ∑ ρ ∈ A, -ε' * zmult χ ρ ≤ ∑ ρ ∈ U, zmult χ ρ * zeroTerm f q σ γ ρ := by
    rw [sum_filter]
    refine sum_le_sum fun ρ hρ => ?_
    have hm : 0 ≤ zmult χ ρ := Nat.cast_nonneg _
    by_cases hb : zeroOffset q ρ < σ
    · obtain ⟨hz, hn⟩ := mem_sdiff.mp hρ
      obtain ⟨hL, hdist⟩ := (hmem ρ).mp hz
      have hre : ρ.re ≤ 1 := not_lt.mp fun h =>
        DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) h.le hL
      have hreal := mul_nonneg (sub_nonneg.mpr hre) hℓ.le
      have hx : zeroOffset q ρ - σ ∈ Set.Icc (-σmax) σmax := by
        grind
      have H := hdecay _ hx ((γ - ρ.im) * Real.log q) (by simpa only [abs_mul, abs_of_pos hℓ] using hsep ρ hL hdist hn hb)
      rw [ite_eq_left hb, mul_comm (-ε')]
      exact mul_le_mul_of_nonneg_left ((neg_le_neg H).trans (abs_le.mp (Complex.abs_re_le_norm _)).1) hm
    · rw [ite_eq_right hb]
      exact mul_nonneg hm (zeroTerm_nonneg hf2 (not_lt.mp hb))
  rw [← mul_sum] at hsum
  have hεK : ε' * (∑ ρ ∈ A, zmult χ ρ) ≤ η / 2 := by
    dsimp [ε']
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  change _ ≤ -(primeSum χ f s).re / Real.log q
  rw [le_div_iff₀ hℓ]
  nlinarith only [hX, mul_le_mul_of_nonneg_right hsum hℓ.le, mul_le_mul_of_nonneg_right hεK hℓ.le]

end GradedNear
