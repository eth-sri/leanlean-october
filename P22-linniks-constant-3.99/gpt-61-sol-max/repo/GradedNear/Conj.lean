import GradedNear.Tactics

import GradedNear.Entry

/-!
# Conjugate zeros of a real character's `L`-function

For a non-principal Dirichlet character `χ` with real values, the Dirichlet series and the
identity theorem give `L(s̄, χ) = conj L(s, χ)` everywhere. Conjugating an analytic function
preserves the order of vanishing (`analyticOrderAt_conj_conj`), so conjugate zeros have equal
multiplicity (`zmult_conj`). Consequently the multiplicity hypothesis of `keptBound_pair_neg`
is automatic for a real character (`keptBound_pair_neg_real`).

Real values are stated as `∀ a, conj (χ a) = χ a`; a character equal to its own inverse has real
values (`conj_apply_of_inv_eq_self`).
-/

open Complex Filter Topology
open scoped ComplexConjugate

namespace GradedNear

/-! ## Conjugation and the order of vanishing -/

/-- Conjugation maps neighbourhoods of `z̄` into neighbourhoods of `z`. -/
lemma tendsto_conj_nhds_conj (z : ℂ) : Tendsto (starRingEnd ℂ) (𝓝 (conj z)) (𝓝 z) := by
  simpa using Complex.continuous_conj.tendsto (conj z)

/-- If `g` is analytic at `z₀`, then `z ↦ conj (g (conj z))` is analytic at `conj z₀`. -/
lemma analyticAt_conj_conj {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) :
    AnalyticAt ℂ (fun z => conj (g (conj z))) (conj z₀) := by
  rw [analyticAt_iff_eventually_differentiableAt] at hg ⊢
  filter_upwards [(tendsto_conj_nhds_conj z₀).eventually hg] with z hz
  exact differentiableAt_conj_conj_iff.mpr hz

/-- The order of vanishing is invariant under `f ↦ conj ∘ f ∘ conj`, taken at `conj z₀`: if
`f(z) = (z - z₀)ⁿ g(z)` near `z₀` with `g(z₀) ≠ 0`, then
`conj f(z̄) = (z - z̄₀)ⁿ conj g(z̄)` near `z̄₀`; and `f` vanishes near `z₀` iff `conj ∘ f ∘ conj`
vanishes near `z̄₀`. -/
lemma analyticOrderAt_conj_conj {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    analyticOrderAt (fun z => conj (f (conj z))) (conj z₀) = analyticOrderAt f z₀ := by
  have hT := tendsto_conj_nhds_conj z₀
  rcases eq_or_ne (analyticOrderAt f z₀) ⊤ with htop | htop
  · rw [htop, analyticOrderAt_eq_top]
    filter_upwards [hT.eventually (analyticOrderAt_eq_top.mp htop)] with z hz
    simp_all
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hn]
    obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp hn.symm
    refine (analyticAt_conj_conj hf).analyticOrderAt_eq_natCast.mpr
      ⟨fun z => conj (g (conj z)), analyticAt_conj_conj hg, by simp_all, ?_⟩
    filter_upwards [hT.eventually hfg] with z hz
    simp_all

/-! ## `L(s̄, χ) = conj L(s, χ)` for a real character -/

variable {q : ℕ} [NeZero q]

/-- **Conjugate zeros of a real character's `L`-function have equal multiplicity**: for a
non-principal real-valued `χ`, `m(ρ̄) = m(ρ)`. -/
theorem zmult_conj {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, conj (χ a) = χ a) (ρ : ℂ) :
    zmult χ (conj ρ) = zmult χ ρ := by
  unfold zmult analyticOrderNatAt

  have hL := DirichletCharacter.differentiable_LFunction hχ

  have heq :=
    (analyticOnNhd_univ_iff_differentiable.mpr fun z => differentiableAt_conj_conj_iff.mpr (hL _)).eq_of_eventuallyEq (analyticOnNhd_univ_iff_differentiable.mpr hL) (z₀ := 2) <|
      eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)) fun z hz => by
          dsimp only [Function.comp_def]
          rw [DirichletCharacter.LFunction_eq_LSeries χ (by simp_all),
            DirichletCharacter.LFunction_eq_LSeries χ hz, LSeries, LSeries, conj_tsum]
          refine tsum_congr fun n => ?_
          rcases eq_or_ne n 0 with rfl | hn
          · simp
          · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, hreal,
              ← conj_cpow _ _ (by norm_cast; positivity), conj_natCast]
  dsimp only [Function.comp_def] at heq
  rw [← analyticOrderAt_conj_conj (hL.analyticAt ρ), heq]

variable {ι : Type*}

/-- **`keptBound_pair_neg` for the conjugate pair of a real character**: the entry keeps a zero
`ρ` at its height and the conjugate zero `ρ̄`. For a real character, conjugate zeros have equal
multiplicity (`zmult_conj`), so the multiplicity hypothesis of `keptBound_pair_neg` is automatic.
All other hypotheses are those of `keptBound_pair_neg` with `ρ' = ρ̄`; the zero hypothesis
`hρ'` follows from `L(ρ, χ) = 0` by `LFunction_conj_eq_zero_iff`. -/
theorem keptBound_pair_neg_real (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (j : ι) (hχ : E.χ j ≠ 1)
    (hreal : ∀ a : ZMod q, starRingEnd ℂ (E.χ j a) = E.χ j a) {ρ : ℂ} {hi C : ℝ}
    (hne : ρ ≠ starRingEnd ℂ ρ) (hS : Sz j = {ρ, starRingEnd ℂ ρ}) (hγ : ρ.im = E.γ j)
    (hhi : zeroLambda q ρ ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) (starRingEnd ℂ ρ) = 0)
    (hC : -C ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) (starRingEnd ℂ ρ)) :
    realLaplace D.f (hi - (D.s - E.δ j)) - C - D.f 0 / 6 ≤ keptBound D E Sz 0 j ∨
      realLaplace D.f (hi - (D.s - E.δ j)) - C - D.f 0 / 6 ≤ 0 :=
  keptBound_pair_neg D hD hf2 E Sz j hχ hne hS hγ hhi hρ' (zmult_conj hχ hreal ρ).le hC

end GradedNear
