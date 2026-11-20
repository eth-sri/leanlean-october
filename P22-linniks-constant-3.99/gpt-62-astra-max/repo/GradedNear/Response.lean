module

public import GradedNear.TestFamilies
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

/-- A zero at or left of the test point has a nonnegative Laplace term. -/
lemma zeroTerm_nonneg {f : ℝ → ℝ} (hf : Condition2 f) {q : ℕ} {σ γ : ℝ} {ρ : ℂ}
    (h : σ ≤ λρ[q] ρ) : 0 ≤ zeroTerm f q σ γ ρ := by
  apply hf.re_nonneg
  simpa only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero] using sub_nonneg.mpr h

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
    ExistsDiscControls M δ, ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ σ γ : ℝ, |σ| ≤ σmax → |γ| ≤ Real.log q →
      ∀ Sz : Finset ℂ,
        (keptInDisc χ γ δ Sz) →
        (adverseFar q χ γ σ δ M where ρ ↦ (ρ ∉ Sz)) →
        adverseCount q χ γ σ δ where ρ ↦ (ρ ∉ Sz) ≤ K₀ →
        ∑ ρ ∈ Sz, zmult χ ρ * zeroTerm f q σ γ ρ - f 0 / 6 - η ≤ responseAt χ f σ γ := by
  obtain ⟨δ, hδ0, hδ1, q₁, hq₁⟩ := hX32 f x₀ B hf1 (hf2.nonneg 0 le_rfl) (η / 2) (half_pos hη)
  let ε' := η / 2 / (K₀ + 1 : ℝ)
  have hε' : 0 < ε' := by positivity
  obtain ⟨M, hM, hdecay⟩ := laplace_decay hf1 σmax hε'
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.mp (eventually_region σmax)
  refine ⟨M, hM, δ, hδ0, hδ1, max q₁ q₂, fun q _ hq χ hχ σ γ hσ hγ Sz hSz hsep hK => ?_⟩
  obtain ⟨hℓ, hreg⟩ := hq₂ q (by omega)
  have hX := hq₁ q (by omega) χ hχ _ (hreg _ _ hσ hγ)
  let Z := (LFunction_zeros_finite hχ (1 + (γ : ℂ) * I) δ).toFinset
  let w ρ := zmult χ ρ * zeroTerm f q σ γ ρ
  have hz : zeroSum χ f (point q σ γ) δ = ∑ ρ ∈ Z, w ρ := by
    simp_rw [zeroSum, point_im, finsum_mem_eq_finite_toFinset_sum _ (LFunction_zeros_finite hχ _ _),
      point_arg _ _ _ hℓ.ne']; rfl
  have hsub : Sz ⊆ Z := fun ρ hρ => (Set.Finite.mem_toFinset _).mpr (hSz ρ hρ).symm
  let bad := (Z \ Sz).filter fun ρ => λρ[q] ρ < σ
  have hm : ∑ ρ ∈ bad, zmult χ ρ ≤ K₀ := by
    rw [← finsum_mem_coe_finset]
    refine le_trans (le_of_eq (finsum_mem_congr ?_ fun _ _ => rfl)) hK
    aesop
  have herr : -(η / 2) ≤ ∑ ρ ∈ Z \ Sz, w ρ := calc
    _ ≤ ∑ ρ ∈ bad, zmult χ ρ * (-ε') := by
      rw [← Finset.sum_mul, mul_neg, neg_le_neg_iff]
      calc _ ≤ ((K₀ : ℝ) + 1) * ε' := by bound
           _ = _ := by dsimp [ε']; field_simp
    _ ≤ _ := by
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      obtain ⟨hZ, hn⟩ := Finset.mem_sdiff.mp hρ
      obtain ⟨hd, hL⟩ := (Set.Finite.mem_toFinset _).mp hZ
      split_ifs with ha
      · refine mul_le_mul_of_nonneg_left (abs_le.mp ((abs_re_le_norm _).trans (hdecay _ ?_ _ ?_))).1
          (Nat.cast_nonneg _)
        · have hr := lt_of_not_ge fun h =>
            DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) h hL
          constructor <;> linarith [mul_nonneg (sub_nonneg.mpr hr.le) hℓ.le, abs_le.mp hσ]
        · simpa [abs_mul, abs_of_pos hℓ] using hsep ρ hL hd hn ha
      · exact mul_nonneg (Nat.cast_nonneg _) (zeroTerm_nonneg hf2 (le_of_not_gt ha))
  rw [hz, ← Finset.sum_sdiff hsub] at hX
  change (∑ ρ ∈ Sz, w ρ) - _ - η ≤ -(primeSum χ f (point q σ γ)).re / _
  rw [le_div_iff₀ hℓ]
  nlinarith

end GradedNear
