module

public import GradedNear.Defs
public import GradedNear.LaplaceDecay
public import GradedNear.ZeroFinite
public import GradedNear.Entries

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

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

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
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ σ γ : ℝ, |σ| ≤ σmax → |γ| ≤ Real.log q →
      ∀ Sz : Finset ℂ,
        (∀ ρ ∈ Sz, DirichletCharacter.LFunction χ ρ = 0 ∧ ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ) →
        (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ →
          ρ ∉ Sz → (1 - ρ.re) * Real.log q < σ → M ≤ |γ - ρ.im| * Real.log q) →
        (∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
            ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ ∧ ρ ∉ Sz ∧ (1 - ρ.re) * Real.log q < σ},
          zmult χ ρ) ≤ K₀ →
        ∑ ρ ∈ Sz, zmult χ ρ * zeroTerm f q σ γ ρ - f 0 / 6 - η ≤ responseAt χ f σ γ := by
  obtain ⟨δ, hδ0, hδ1, q₁, hq₁⟩ := hX32 f x₀ B hf1 (hf2.nonneg 0 le_rfl) (η / 2) (half_pos hη)
  obtain ⟨M, hM, hdecay⟩ := laplace_decay hf1 σmax (by positivity : 0 < η / 2 / ((K₀ : ℝ) + 1))
  obtain ⟨q₂, hq₂⟩ := eventually_loglog_ge σmax
  refine ⟨M, hM, δ, hδ0, hδ1, max q₁ q₂, fun q _ hq χ hχ σ γ hσ hγ Sz hSz hsep hK => ?_⟩
  obtain ⟨hsq, -, hq2⟩ := hq₂ q (le_of_max_le_right hq)
  have hℓ := log_q_pos hq2
  set s : ℂ := (((1 - σ / Real.log q : ℝ)) : ℂ) + (γ : ℂ) * I
  have hs : s.re = 1 - σ / Real.log q ∧ s.im = γ := by simp [s, -ofReal_sub]
  have hX := hq₁ q (le_of_max_le_left hq) χ hχ s ⟨by
    rw [hs.1, sub_sub_cancel_left, abs_neg, abs_div, abs_of_pos hℓ]
    exact div_le_div_of_nonneg_right (hσ.trans hsq) hℓ.le, hs.2 ▸ hγ⟩
  have hZ := LFunction_zeros_finite hχ (1 + (γ : ℂ) * I) δ
  have hA := hZ.subset (t := {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
    ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ ∧ ρ ∉ Sz ∧ (1 - ρ.re) * Real.log q < σ}) fun ρ h => ⟨h.2.1, h.1⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hA] at hK
  have harg : ∀ ρ : ℂ, (laplace f ((s - ρ) * (Real.log q : ℂ))).re = zeroTerm f q σ γ ρ := by
    intro ρ
    simp only [zeroTerm, s]
    generalize Real.log q = L at hℓ
    congr 2
    apply Complex.ext <;> simp <;> field_simp <;> ring
  have hzs : ∑ ρ ∈ Sz, zmult χ ρ * zeroTerm f q σ γ ρ - η / 2 ≤ zeroSum χ f s δ := by
    unfold zeroSum
    rw [hs.2, finsum_mem_eq_finite_toFinset_sum _ hZ]
    simp_rw [harg]
    have hterm : ∀ ρ ∈ hA.toFinset, zmult χ ρ * -(η / 2 / ((K₀ : ℝ) + 1)) ≤
        zmult χ ρ * zeroTerm f q σ γ ρ := fun ρ h => by
      simp at h
      have := mul_nonneg (sub_nonneg.2 (not_le.1 fun h' =>
        DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h' h.1).le) hℓ.le
      exact mul_le_mul_of_nonneg_left (abs_le.1 ((abs_re_le_norm _).trans (hdecay _
        ⟨by linarith [le_abs_self σ], by linarith [abs_nonneg σ]⟩ _
        (by rw [abs_mul, abs_of_pos hℓ]; exact hsep ρ h.1 h.2.1 h.2.2.1 h.2.2.2)))).1
        (Nat.cast_nonneg _)
    have := Finset.sum_le_sum hterm
    rw [← Finset.sum_mul] at this
    have : (K₀ : ℝ) * (η / 2 / (K₀ + 1)) ≤ η / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    calc _ ≤ ∑ ρ ∈ Sz ∪ hA.toFinset, zmult χ ρ * zeroTerm f q σ γ ρ := by
          rw [Finset.sum_union (Finset.disjoint_left.2 fun ρ h h' => by simp_all)]
          nlinarith [mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ η / 2 / ((K₀ : ℝ) + 1))]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset
          (fun ρ h => by simp_all) fun ρ h => by simp_all)
          fun ρ hρ hn => mul_nonneg (Nat.cast_nonneg _) (hf2.re_nonneg _ ?_)
    rw [add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero, sub_nonneg]
    simp_all
  unfold responseAt
  rw [le_div_iff₀ hℓ]
  nlinarith

end GradedNear
