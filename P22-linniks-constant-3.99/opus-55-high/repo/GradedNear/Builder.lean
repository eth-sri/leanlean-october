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
  obtain ⟨M, hM, hdec⟩ := laplace_decay hD.g_cond1 (|D.s₁| + 2 * ∑ δ ∈ D.Δ, |δ|)
    (by unfold NearData.d₁; linarith : 0 < D.d₁)
  refine ⟨M, hM, fun {q} {ι} _ E hΔ j hsep => Finset.sum_eq_zero fun k hk => max_eq_left ?_⟩
  have hk' := (Finset.mem_filter.1 hk).2
  have hj := Finset.single_le_sum (f := fun δ => |δ|) (fun _ _ => abs_nonneg _) (hΔ j)
  have hk2 := Finset.single_le_sum (f := fun δ => |δ|) (fun _ _ => abs_nonneg _) (hΔ k)
  have := (abs_le.1 (Complex.abs_re_le_norm _)).2.trans (hdec (-(D.s₁ - E.δ j - E.δ k)) (by grind)
    ((E.γ j - E.γ k) * Real.log q) (by
    rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg q)]
    exact hsep k hk'.1 hk'.2))
  linarith

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
          ∀ r De : ι → ℝ, (∀ j, r j ≤ keptBound D E Sz 0 j ∨ r j ≤ 0) →
            (∀ j, 0 < D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) →
            (∀ j, D.Dδ (E.δ j) - D.d₁ + pairExcess D E j ≤ De j) →
            ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt ((1 + η) * (D.d₁ / Du + η)) ∧
              ∑ j, (max 0 (r j / Real.sqrt (Iu * Du) - η - τ)) ^ 2 / ((1 + η) * De j / Du) ≤
                1 - τ ^ 2 / ((1 + η) * (D.d₁ / Du + η)) := by
  have hIB := hD.IB_pos
  set N := Real.sqrt (D.IB * Du)
  have hN : 0 < N := Real.sqrt_pos.2 (by positivity)
  set η' := η * min 1 (min N Du)
  obtain ⟨h1, h2, h3⟩ : η' ≤ η ∧ η' ≤ η * N ∧ η' ≤ η * Du := by simp [η', hη]
  have h0 : 0 < η' := by positivity
  obtain ⟨M, hM, δ, hδ0, hδ1, q₀, h⟩ := graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ h0
  refine ⟨M, hM, δ, hδ0, hδ1, q₀, fun q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj Sz hSz hsep hK
    r De hr hDj hDe => ?_⟩
  have hDn : 0 < Du / (1 + η') := by positivity
  obtain ⟨τ, hτ0, hτd, hT⟩ := h q hq T hT0 hTl hsafe ι E hχ hγ hΔ hinj Sz hSz hsep hK _ hDn hDj
  have hd₁ : 0 ≤ D.d₁ := div_nonneg (hD.g_cond2.nonneg 0 le_rfl) (by norm_num)
  have hd : (D.d₁ + η') / (Du / (1 + η')) ≤ (1 + η) * (D.d₁ / Du + η) :=
    by field_simp; nlinarith
  rw [show Real.sqrt ((1 + η') * D.IB * (Du / (1 + η'))) = N by grind] at hT
  refine ⟨τ, hτ0, hτd.trans (Real.sqrt_le_sqrt hd), (Finset.sum_le_sum fun j _ =>
    Cert.term_le ?_ hτ0 (div_pos (hDj j) hDn) ?_).trans (hT.trans (sub_le_sub_left
      (div_le_div_of_nonneg_left (sq_nonneg _) (div_pos (by linarith) hDn) hd) 1))⟩
  · rcases le_or_gt (r j) 0 with hr0 | hr0
    · exact .inr (by linarith [div_nonpos_of_nonpos_of_nonneg hr0 (Real.sqrt_nonneg (Iu * Du))])
    refine .inl ?_
    have := div_le_div_of_nonneg_left hr0.le hN
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hIu hDu.le))
    have := div_le_div_of_nonneg_right ((hr j).resolve_right hr0.not_ge) hN.le
    have : η' / N ≤ η := (div_le_iff₀ hN).2 (by linarith)
    rw [show keptBound D E Sz η' j = keptBound D E Sz 0 j - η' by unfold keptBound; ring, sub_div]
    linarith
  · rw [div_div_eq_mul_div, mul_comm _ (1 + η')]
    have := hDj j
    gcongr
    grind

end GradedNear
