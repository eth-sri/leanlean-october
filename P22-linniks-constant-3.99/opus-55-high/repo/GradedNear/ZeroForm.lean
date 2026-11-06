module

public import GradedNear.Statement
public import GradedNear.Response
public import GradedNear.Threshold

/-!
# The graded near lemma in zero form (paper §§8.2, 8.6)

`graded_near_threshold` combines the graded near lemma (`graded_near_lemma`), the response lemma
(`response_lemma`) and the threshold identity (`threshold_of_quadratic`). Its hypotheses and
conclusion mention zeros of `L(s, χ)` and the data of the row, but no prime sums.

For each entry `j` a finite set `S_j` of zeros of `L(s, χ_j)` in the local disc about
`1 + iγ_j` is kept. Put

* `r_j = Σ_{ρ ∈ S_j} m_ρ Re F((λ_ρ - s_j) + i(γ_j - Im ρ)𝓛) - f(0)/6 - η`, where
  `λ_ρ = (1 - Re ρ)𝓛` and `s_j = s - δ_j` (`keptBound`);
* `v_j = r_j / N` with `N = √((1 + η) I_B(s) D_n)`;
* `D_j = (D(δ_j) - d₁ + e_j) / D_n` and `d = (d₁ + η) / D_n`.

Then some `τ ∈ [0, √d]` satisfies `Σ_j (v_j - τ)_+² / D_j ≤ 1 - τ²/d`. Any normalizer
`D_n > 0` works (Corollary 8.10 of the paper calls it `D_u`), since the quadratic form inequality is homogeneous.
-/

@[expose] public section

open Complex

noncomputable section

namespace GradedNear

/-- **The graded near lemma in zero form.** Fix the row data `D`, a zero count `K₀` and `η > 0`.
There are a separation `M`, a disc radius `δ < 1` and a `q₀` such that the following holds for
`q ≥ q₀`, a height `T ≤ log q / 3` and a safe anchor `s₁` at height `2T + 1`. Take entries as in
`graded_near_lemma`, and for each entry a finite set `S_j` of zeros of `L(s, χ_j)` in the disc
of radius `δ` about `1 + iγ_j`. Suppose that every other disc zero with `λ_ρ < s_j` is at
normalized height distance `≥ M` from `γ_j`, and that there are at most `K₀` of them, with
multiplicity. Then the entries satisfy the threshold form (T) with the features
`keptBound / N`, provided every diagonal numerator `D(δ_j) - d₁ + e_j` is positive, for any
normalizer `D_n > 0`. -/
theorem graded_near_threshold (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid)
    (hf2 : Condition2 D.f) (K₀ : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 → SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ Sz : ι → Finset ℂ,
          (∀ j, ∀ ρ ∈ Sz j, DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
            ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ) →
          (∀ j, ∀ ρ : ℂ, DirichletCharacter.LFunction (E.χ j) ρ = 0 →
            ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ → ρ ∉ Sz j →
            (1 - ρ.re) * Real.log q < D.s - E.δ j → M ≤ |E.γ j - ρ.im| * Real.log q) →
          (∀ j, (∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
              ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ ∧ ρ ∉ Sz j ∧
              (1 - ρ.re) * Real.log q < D.s - E.δ j}, zmult (E.χ j) ρ) ≤ K₀) →
          ∀ Dn : ℝ, 0 < Dn → (∀ j, 0 < D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) →
            ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt ((D.d₁ + η) / Dn) ∧
              ∑ j, (max 0 (keptBound D E Sz η j / Real.sqrt ((1 + η) * D.IB * Dn) - τ)) ^ 2 /
                  ((D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / Dn) ≤
                1 - τ ^ 2 / ((D.d₁ + η) / Dn) := by
  obtain ⟨q₁, hq₁⟩ := graded_near_lemma hX31 hX32 hBur hGr D hD hη
  obtain ⟨M, hM, δ, hδ0, hδ1, q₂, hq₂⟩ :=
    response_lemma hX32 hD.f_cond hf2 (|D.s| + ∑ δ ∈ D.Δ, |δ|) K₀ hη
  refine ⟨M, hM, δ, hδ0, hδ1, max q₁ q₂, fun q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj Sz hSz hsep
    hK Dn hDn hDj => ?_⟩
  have hd₁ : 0 ≤ D.d₁ := div_nonneg (hD.g_cond2.nonneg 0 le_rfl) (by norm_num)
  have hIB := hD.IB_pos
  refine threshold_of_quadratic _ _ _ (fun j => div_pos (hDj j) hDn) (div_pos (by linarith) hDn)
    fun a ha => ?_
  have h2 : ∑ j, a j * keptBound D E Sz η j ≤ ∑ j, a j * response D E j := by
    gcongr with j
    · grind
    refine hq₂ q (le_of_max_le_right hq) (E.χ j) (hχ j) (D.s - E.δ j) (E.γ j) ((abs_sub ..).trans ?_)
      (by grind) (Sz j) (hSz j) (hsep j) (hK j)
    grind [Finset.single_le_sum, abs_nonneg]
  have hmain := hq₁ q (le_of_max_le_left hq) T hT0 hTl hsafe ι E hχ hγ hΔ hinj a ha
  simp only [mul_div_assoc', ← Finset.sum_div, div_mul_eq_mul_div]
  rw [← add_div, ← zero_div (√_), max_div_div_right (Real.sqrt_nonneg _), div_pow,
    Real.sq_sqrt (by positivity), div_le_div_iff₀ (by positivity) hDn]
  nlinarith [pow_le_pow_left₀ (le_max_left ..) (max_le_max le_rfl h2) 2]

end GradedNear
