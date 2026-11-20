module

public import GradedNear.Main
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

lemma NearData.Valid.d₁_nonneg {D : NearData} (h : D.Valid) : 0 ≤ D.d₁ :=
  div_nonneg (h.g_cond2.nonneg 0 le_rfl) (by norm_num)

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
    ExistsDiscControls M δ,
      ForLargeEntries q ι E of D,
        ForKept Sz of D E q ι with δ M K₀,
          ∀ Dn : ℝ, 0 < Dn → (∀ j, 0 < rowDiag D E j) →
            HasThreshold[(D.d₁ + η)/Dn] j ↦
              (keptBound D E Sz η j / Real.sqrt ((1+η)*D.IB*Dn), (rowDiag D E j)/Dn) := by
  obtain ⟨q₁, hq₁⟩ := graded_near_lemma hX31 hX32 hBur hGr D hD hη
  obtain ⟨M, hM, δ, hδ0, hδ1, q₂, hq₂⟩ :=
    response_lemma hX32 hD.f_cond hf2 (|D.s| + ∑ δ ∈ D.Δ, δ) K₀ hη
  refine ⟨M, hM, δ, hδ0, hδ1, max q₁ q₂, ?_⟩
  intro q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj Sz hSz hsep hK Dn hDn hDj
  have hresp j : keptBound D E Sz η j ≤ response D E j :=
    hq₂ q (by omega) _ (hχ j) _ _ (offset_bound hD _ (hΔ j)) (by linarith [hγ j]) _ (hSz j) (hsep j) (hK j)
  have hIB := hD.IB_pos
  let N := Real.sqrt ((1 + η) * D.IB * Dn)
  have hN : 0 < N := Real.sqrt_pos.mpr (by positivity)
  refine threshold_of_quadratic _ _ _ (fun j => div_pos (hDj j) hDn)
    (div_pos (add_pos_of_nonneg_of_pos hD.d₁_nonneg hη) hDn) fun a ha => ?_
  have hmax (x : ℝ) := max_div_div_right hN.le 0 x
  simp [N] at hmax
  simp [← mul_div_assoc, div_mul_eq_mul_div, ← Finset.sum_div, ← add_div, hmax, div_pow, Real.sq_sqrt (show 0 ≤ (1+η)*D.IB*Dn by positivity)]
  grw [hresp, hq₁ q (by omega) T hT0 hTl hsafe ι E hχ hγ hΔ hinj a ha] <;> first | positivity | exact ha _ | (field_simp; rfl)

end GradedNear
