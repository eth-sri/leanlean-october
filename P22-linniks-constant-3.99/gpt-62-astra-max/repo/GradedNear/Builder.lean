module

public import GradedNear.Entry

/-!
# The graded near lemma in the leaf builders' normalization

The leaf builders (`computations/sieve_near/sieve_inputs.py` in the research repository) normalize the threshold form
as in Corollary 8.10 of the paper, not as in Proposition 8.8. For a row with an upper bound `I_u ≥ I_B` and a normalizer `D_u > 0`
(an upper bound for `D(0)`), they compute:
* the feature `r_j / √(I_u D_u) - η` of an entry, where `r_j` is a lower bound for its kept terms
  minus `f(0)/6`;
* the diagonal `(1 + η) D_j⁺ / D_u`, where `D_j⁺ ≥ D(δ_j) - d₁ + e_j`;
* the radius `(1 + η)(d₁ / D_u + η)`.

`builder_threshold` proves (T) for exactly these quantities, with no numerical side conditions.
It applies the zero form `graded_near_threshold` with the smaller allowance
`η' = η · min(1, √(I_B D_u), D_u)` and the normalizer `D_n = D_u / (1 + η')`. Every builder
quantity is then on the safe side of the corresponding quantity of the zero form
(`threshold_weaken`).

`pairExcess_eq_zero` shows that same-character pairs at separated normalized heights have no pair
excess, as the rows of §6.5 assume for them.
-/

@[expose] public section

open Complex

noncomputable section

namespace GradedNear

/-- **Same-character pairs at separated heights have no pair excess.** If `g(0) > 0`, there is an
`M > 0` such that an entry `j` has `e_j = 0` whenever every other entry of the same character is
at normalized height distance `|γ_j - γ_k| log q ≥ M` from it. The reason is that
`|G(x + iY)| ≤ d₁` for `|Y| ≥ M` and `x` in the fixed range of `-σ_jk`. -/
theorem pairExcess_eq_zero (D : NearData) (hD : D.Valid) (hg0 : 0 < D.g 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ {q : ℕ} {ι : Type} [Fintype ι] (E : Entries q ι), (∀ j, E.δ j ∈ D.Δ) →
      ∀ j, (∀ k, k ≠ j → E.χ k = E.χ j → M ≤ |E.γ j - E.γ k| * Real.log q) →
        pairExcess D E j = 0 := by
  classical
  have hd₁ : 0 < D.d₁ := by unfold NearData.d₁; linarith
  obtain ⟨M, hM, hdec⟩ := laplace_decay hD.g_cond1 (|D.s₁| + 2 * ∑ δ ∈ D.Δ, δ) hd₁
  refine ⟨M, hM, fun {q} {ι} _ E hΔ j hsep => ?_⟩
  refine Finset.sum_eq_zero fun k hk => ?_
  obtain ⟨hne, heq⟩ := (Finset.mem_filter.mp hk).2
  apply max_eq_left (sub_nonpos.mpr ((re_le_norm _).trans (hdec _ ?_ _ ?_)))
  · simpa only [Set.mem_Icc, ← abs_le, abs_neg] using sigma_bound D hD (hΔ j) (hΔ k)
  · simpa [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg q)] using hsep k hne heq

/-- **The graded near lemma in the normalization of the leaf builders.** Fix the row data `D`, a
zero count `K₀`, the allowance `η > 0`, an upper bound `I_u ≥ I_B` and a normalizer `D_u > 0`.
There are `M`, `δ < 1` and `q₀` such that, for entries with kept zeros as in
`graded_near_threshold`, the following holds. Suppose each `r_j` is at most the entry's kept
terms minus `f(0)/6` (`keptBound … 0`), or `r_j ≤ 0`, and each `D_j⁺` is at least the entry's
diagonal numerator `D(δ_j) - d₁ + e_j > 0`. Then (T) holds with the features
`r_j / √(I_u D_u) - η`, the diagonals `(1 + η) D_j⁺ / D_u` and the radius
`(1 + η)(d₁ / D_u + η)`. -/
theorem builder_threshold (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid)
    (hf2 : Condition2 D.f) (K₀ : ℕ) {η : ℝ} (hη : 0 < η) {Iu Du : ℝ} (hIu : D.IB ≤ Iu)
    (hDu : 0 < Du) :
    ExistsDiscControls M δ,
      ForLargeEntries q ι E of D,
        ForKept Sz of D E q ι with δ M K₀,
          ∀ r De : ι → ℝ, (∀ j, r j ≤ keptBound D E Sz 0 j ∨ r j ≤ 0) →
            (∀ j, 0 < rowDiag D E j) →
            (∀ j, rowDiag D E j ≤ De j) →
            HasThreshold[(1+η)*(D.d₁/Du + η)] j ↦
              (r j / Real.sqrt (Iu*Du) - η, (1+η)*De j/Du) := by
  have hIB := hD.IB_pos
  let N := Real.sqrt (D.IB * Du)
  have hN : 0 < N := Real.sqrt_pos.2 (by positivity)
  let η' := min η (min (η*N) (η*Du))
  have hη'pos : 0 < η' := lt_min hη (lt_min (mul_pos hη hN) (mul_pos hη hDu))
  obtain ⟨he, heN, heD⟩ : η' ≤ η ∧ η' ≤ η*N ∧ η' ≤ η*Du := by simp [η']
  gconvert graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ hη'pos
  intro r De hr hDj hDe
  have hn : 0 < Du / (1 + η') := by positivity
  have hT := this _ hn hDj
  have hd := hD.d₁_nonneg
  have hnorm : (1 + η') * D.IB * (Du / (1 + η')) = D.IB * Du := by field_simp
  rw [hnorm] at hT
  refine threshold_weaken (fun j => div_pos (hDj j) hn) (fun j => ?_) (fun j => ?_)
    (div_pos (by positivity) hn) ?_ hT
  · rw [div_div_eq_mul_div, mul_comm _ (1+η')]
    gcongr <;> first | exact he | exact hDe _ | exact (hDj _).le
  · rcases le_or_gt (r j) 0 with hr0 | hr0
    · exact .inr (sub_nonpos.mpr ((div_nonpos_of_nonpos_of_nonneg hr0 (Real.sqrt_nonneg _)).trans hη.le))
    · left
      have hu := div_le_div_of_nonneg_left hr0.le hN (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hIu hDu.le))
      have hrk := (hr j).resolve_right hr0.not_ge
      simp only [keptBound, sub_zero] at hrk ⊢
      rw [sub_div]
      exact sub_le_sub (hu.trans (div_le_div_of_nonneg_right hrk hN.le)) ((div_le_iff₀ hN).mpr heN)
  · rw [div_div_eq_mul_div, mul_comm _ (1+η'), mul_div_assoc, add_div]
    gcongr <;> first | positivity | exact he | exact (div_le_iff₀ hDu).mpr heD

end GradedNear
