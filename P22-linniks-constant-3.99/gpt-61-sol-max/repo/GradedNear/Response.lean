import GradedNear.Tactics

import GradedNear.Defs
import GradedNear.LaplaceDecay
import GradedNear.ZeroFinite
import GradedNear.Entries

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

open Complex

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
        (∀ ρ ∈ Sz, DirichletCharacter.LFunction χ ρ = 0 ∧ InDisc γ δ ρ) →
        DistantZeros q χ σ γ δ Sz M →
         ∑ᶠ ρ ∈ discardedZeros q χ σ γ δ Sz,
          zmult χ ρ ≤ K₀ →
        ∑ ρ ∈ Sz, zmult χ ρ * zeroTerm f q σ γ ρ - f 0 / 6 - η ≤ responseAt χ f σ γ := by
  obtain ⟨δ, hδ0, hδ1, q₁, hq₁⟩ := hX32 f x₀ B hf1 (hf2.nonneg 0 le_rfl) (η / 2) (half_pos hη)
  set ε' : ℝ := η / 2 / ((K₀ : ℝ) + 1) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨M, hM, hdecay⟩ := laplace_decay hf1 σmax hε'pos
  obtain ⟨q₂, hq₂⟩ := Filter.eventually_atTop.1 (eventually_loglog_ge σmax)
  refine ⟨M, hM, δ, hδ0, hδ1, max q₁ q₂, fun q _ hq χ hχ σ γ hσ hγ Sz hSz hsep hK => ?_⟩

  obtain ⟨hsq, hq2⟩ := hq₂ q (le_of_max_le_right hq)
  have hℓ := log_q_pos hq2
  set s : ℂ := testPoint q σ γ with hs
  have hsre : s.re = 1 - σ / Real.log q := by simp [hs, -Complex.natCast_log]
  have hsim : s.im = γ := by simp [hs, -Complex.natCast_log]
  have hreg : LemmaRegion q s := by
    refine ⟨?_, by exact?⟩
    rw [hsre, show 1 - σ / Real.log q - 1 = -(σ / Real.log q) by ring, abs_neg, abs_div,
      abs_of_pos hℓ]
    bound
  have hX := hq₁ q (le_of_max_le_left hq) χ hχ s hreg
  -- the zeros in the disc
  set Z : Set ℂ := {ρ : ℂ | InDisc s.im δ ρ ∧
    DirichletCharacter.LFunction χ ρ = 0} with hZ
  have hZfin : Z.Finite := by

    have h := (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (DirichletCharacter.differentiable_LFunction hχ)
    ).preimage_zero_mem_codiscrete
      (DirichletCharacter.LFunction_apply_one_ne_zero hχ)
    have hfin := (isCompact_closedBall (1 + ↑s.im * I) δ).finite_sdiff_of_mem_codiscreteWithin
      (Filter.codiscreteWithin_mono (Set.subset_univ _) h)
    convert hfin using 1
    ext ρ
    simp [Z, dist_eq_norm']
  have hzs : zeroSum χ f s δ = ∑ ρ ∈ hZfin.toFinset, zmult χ ρ * zeroTerm f q σ γ ρ := by
    unfold zeroSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hZfin]
    congr! 1 with ρ _
    unfold zeroTerm
    rw [hs]
    congr 3
    apply Complex.ext <;> simp [-Complex.natCast_log] <;> grind
  have hmem ρ : ρ ∈ hZfin.toFinset ↔
      DirichletCharacter.LFunction χ ρ = 0 ∧ InDisc γ δ ρ := by
    grind [Set.Finite.mem_toFinset]

  -- split the zeros: kept, to the right of the anchor, adverse
  set g : ℂ → ℝ := fun ρ => zmult χ ρ * zeroTerm f q σ γ ρ
  set T := hZfin.toFinset \ Sz with hT
  have hsplit := Finset.sum_sdiff (f := g)  fun ρ hρ => (hmem ρ).2 (hSz ρ hρ)
  -- zeros of L lie in Re ρ < 1
  have hre1 ρ : DirichletCharacter.LFunction χ ρ = 0 → ρ.re < 1 := by
    grind [DirichletCharacter.LFunction_ne_zero_of_one_le_re]
  -- adverse zeros: each term ≥ -ε', and their multiplicity is ≤ K₀
  have hadv_mult : ∑ ρ ∈ T.filter fun ρ => zeroLambda q ρ < σ , zmult χ ρ ≤ K₀ := by
    have hset : discardedZeros q χ σ γ δ Sz =
        ↑(T.filter fun ρ => zeroLambda q ρ < σ) := by
      ext ρ
      grind
    rwa [hset, finsum_mem_coe_finset] at hK
  have hadv : -(η / 2) ≤ ∑ ρ ∈ T, g ρ := by
    have h1 : ∑ ρ ∈ T.filter fun ρ => zeroLambda q ρ < σ , zmult χ ρ * -ε' ≤
        ∑ ρ ∈ T, g ρ := by
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun ρ hρ => ?_
      by_cases hσ : zeroLambda q ρ < σ
      · simp only [ite_eq_left hσ]
        apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        rw [hT, Finset.mem_sdiff] at hρ
        obtain ⟨hL, hd⟩ := (hmem ρ).1 hρ.1
        have hsepρ := hsep ρ hL hd hρ.2 hσ
        have hr1 := hre1 ρ hL
        have hx : zeroLambda q ρ - σ ∈ Set.Icc (-σmax) σmax := by
          have h0 : 0 ≤ zeroLambda q ρ := by positivity
          grind
        have hY : M ≤ |(γ - ρ.im) * Real.log q| := by
          grind [abs_of_pos]
        exact (abs_le.mp ((Complex.abs_re_le_norm _).trans (hdecay _ hx _ hY))).1
      · simp only [ite_eq_right hσ]
        refine mul_nonneg (Nat.cast_nonneg _) (hf2.re_nonneg _ ?_)
        simpa [-Complex.natCast_log] using sub_nonneg.mpr (not_lt.mp hσ)
    rw [← Finset.sum_mul] at h1
    have h2 : (K₀ : ℝ) * ε' ≤ η / 2 := by
      rw [hε']
      field_simp; bound
    nlinarith
  -- assemble

  unfold responseAt
  rw [← hs]
  rw [le_div_iff₀ hℓ]
  have : ∑ ρ ∈ Sz, zmult χ ρ * zeroTerm f q σ γ ρ = ∑ ρ ∈ Sz, g ρ := rfl
  rw [this]
  nlinarith

end GradedNear
