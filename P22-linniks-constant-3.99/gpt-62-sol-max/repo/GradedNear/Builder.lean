module

public import GradedNear.Entry
public import GradedNear.Cert.Bins

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
`η' = min(η, η √(I_B D_u), η D_u)` and the normalizer `D_n = D_u / (1 + η')`. Every builder
quantity is then on the safe side of the corresponding quantity of the zero form
by monotonicity of the threshold terms.

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
  let K := |D.s₁| + 2 * ∑ δ ∈ D.Δ, δ
  obtain ⟨M, hM, hdec⟩ := laplace_decay hD.g_cond1 K hd₁
  refine ⟨M, hM, fun {q} {ι} _ E hΔ j hsep => ?_⟩
  unfold pairExcess
  refine Finset.sum_eq_zero fun k hk => ?_
  obtain ⟨hk₁, hk₂⟩ := (Finset.mem_filter.mp hk).2
  refine max_eq_left (sub_nonpos.mpr ((Complex.re_le_norm _).trans (hdec _ ?_ _ ?_)))
  · simpa only [Set.mem_Icc, ← abs_le, abs_neg] using sigma_bound D hD (hΔ j) (hΔ k)
  · simpa only [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg q)] using hsep k hk₁ hk₂

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
    SeparatedModuli[M, δ, q => NearFamily[D, q; ι, E => KeptFamily[D, q; ι, E; M, δ, K₀; Sz =>
          ∀ r De : ι → ℝ, (∀ j, r j ≤ keptBound D E Sz 0 j ∨ r j ≤ 0) →
            (∀ j, 0 < diagNumerator D E j) →
            (∀ j, diagNumerator D E j ≤ De j) →
            ThresholdForm[j; r j / Real.sqrt (Iu * Du) - η, (1 + η) * De j / Du;
              (1 + η) * (D.d₁ / Du + η)]]]] := by
  let N := Real.sqrt (D.IB * Du)
  have hN : 0 < N := Real.sqrt_pos.2 (mul_pos hD.IB_pos hDu)
  let ε := min η (min (η * N) (η * Du))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have ⟨hεη, hεN, hεD⟩ : ε ≤ η ∧ ε ≤ η * N ∧ ε ≤ η * Du := by simp [ε, min_le_iff]
  obtain ⟨M, hM, δ, hδ0, hδ1, q₀, h⟩ :=
    graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ hε
  refine ⟨M, hM, δ, hδ0, hδ1, q₀, ?_⟩
  intro q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj Sz hSz hsep hK r De hr hDj hDe
  have hpos : 0 < 1 + ε := by linarith
  have hDn := div_pos hDu hpos
  obtain ⟨τ, hτ0, hτd, hT⟩ := h q hq T hT0 hTl hsafe ι E hχ hγ hΔ hinj Sz hSz hsep hK _ hDn hDj
  have hNn : Real.sqrt ((1 + ε) * D.IB * (Du / (1 + ε))) = N := by
    dsimp [N]; congr 1; field_simp
  rw [hNn] at hT
  have hd := hD.d₁_nonneg
  have hradius : (D.d₁ + ε) / (Du / (1 + ε)) ≤ (1 + η) * (D.d₁ / Du + η) := by
    rw [div_div_eq_mul_div, mul_comm _ (1 + ε), mul_div_assoc]
    gcongr
    rwa [add_div, add_le_add_iff_left, div_le_iff₀ hDu]
  refine ⟨τ, hτ0, hτd.trans (Real.sqrt_le_sqrt hradius), (le_trans ?_ hT).trans ?_⟩
  · refine Finset.sum_le_sum fun j _ => Cert.term_le ?_ hτ0 (div_pos (hDj j) hDn) ?_
    · rcases le_or_gt (r j) 0 with h0 | hp
      · right
        grw [h0, zero_div]
        linarith
      have hsq : N ≤ Real.sqrt (Iu * Du) := Real.sqrt_le_sqrt (by gcongr)
      left
      rw [show keptBound D E Sz ε j = keptBound D E Sz 0 j - ε by simp [keptBound], sub_div]
      grw [← hsq, (hr j).resolve_right hp.not_ge]
      gcongr
      exact (div_le_iff₀ hN).mpr hεN
    · rw [div_div_eq_mul_div, mul_comm _ (1 + ε)]
      gcongr
      · exact (hDj j).le
      · exact hDe j
  · gcongr

end GradedNear
