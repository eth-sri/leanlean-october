module

public import GradedNear.Entry

/-!
# Conjugate zeros of a real character's `L`-function

For a non-principal Dirichlet character `χ` with real values, `L(s̄, χ) = conj L(s, χ)` for every
`s`: the Dirichlet series has real coefficients, so the identity holds termwise
for `Re s > 1`, and the identity theorem extends it to all `s`, since both `L(·, χ)` and
`s ↦ conj L(s̄, χ)` are entire. The zeros therefore come in conjugate pairs; since conjugation commutes with iterated differentiation, `ρ` and `ρ̄` have the same multiplicity (`zmult_conj`).
Hence the multiplicity hypothesis of `keptBound_pair_neg` holds automatically for the conjugate
pair `{ρ, ρ̄}` of a real character (`keptBound_pair_neg_real`).

-/

@[expose] public section

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GradedNear

/-! ## Conjugation and the order of vanishing -/

variable {q : ℕ} [NeZero q]

-- Extend the termwise conjugation identity from `Re s > 1` by analyticity.
private lemma LFunction_conj {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, conj (χ a) = χ a) :
    (fun z => conj (DirichletCharacter.LFunction χ (conj z))) = DirichletCharacter.LFunction χ := by
  have hL := DirichletCharacter.differentiable_LFunction hχ
  have h1 : AnalyticOnNhd ℂ (fun z => conj (DirichletCharacter.LFunction χ (conj z))) Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr fun z => differentiableAt_conj_conj_iff.mpr (hL _)
  refine h1.eq_of_eventuallyEq (analyticOnNhd_LFunction hχ) (z₀ := 2) <|
    eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)) fun z hz => ?_
  change 1 < z.re at hz
  rw [DirichletCharacter.LFunction_eq_LSeries χ (by rwa [conj_re]),
    DirichletCharacter.LFunction_eq_LSeries χ hz, LSeries, LSeries, conj_tsum]
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, hreal,
      ← conj_cpow _ _ (by simp; positivity), conj_natCast]

/-- **Conjugate zeros of a real character's `L`-function have equal multiplicity**: for a
non-principal real-valued `χ`, `m(ρ̄) = m(ρ)`. -/
theorem zmult_conj {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, conj (χ a) = χ a) (ρ : ℂ) :
    zmult χ (conj ρ) = zmult χ ρ := by
  let f := DirichletCharacter.LFunction χ
  have hf z : AnalyticAt ℂ f z := analyticOnNhd_LFunction hχ z (Set.mem_univ z)
  have hDeriv n : conj ∘ iteratedDeriv n f ∘ conj = iteratedDeriv n f := by
    induction n with
    | zero => simpa [Function.comp_def] using LFunction_conj hχ hreal
    | succ n ih => simpa [iteratedDeriv_succ] using congrArg deriv ih
  have h : analyticOrderAt f (conj ρ) = analyticOrderAt f ρ :=
    ENat.eq_of_forall_natCast_le_iff fun n => by
      simp only [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf _)]
      refine forall_congr' fun i => imp_congr_right fun _ => ?_
      rw [← congrFun (hDeriv i) ρ]
      simp
  exact congrArg (fun o : ENat => (o.toNat : ℝ)) h

variable {ι : Type*}

/-- **`keptBound_pair_neg` for the conjugate pair of a real character**: the entry keeps a zero
`ρ` at its height and the conjugate zero `ρ̄`. For a real character, conjugate zeros have equal
multiplicity (`zmult_conj`), so the multiplicity hypothesis of `keptBound_pair_neg` is automatic.
All other hypotheses are those of `keptBound_pair_neg` with `ρ' = ρ̄`. -/
theorem keptBound_pair_neg_real (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (j : ι) (hχ : E.χ j ≠ 1)
    (hreal : ∀ a : ZMod q, starRingEnd ℂ (E.χ j a) = E.χ j a) {ρ : ℂ} {hi C : ℝ}
    (hne : ρ ≠ starRingEnd ℂ ρ) (hS : Sz j = {ρ, starRingEnd ℂ ρ}) (hγ : ρ.im = E.γ j)
    (hhi : zeroOffset q ρ ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) (starRingEnd ℂ ρ) = 0)
    (hC : -C ≤ entryTerm D E q j (starRingEnd ℂ ρ)) :
    heightTerm D E j hi - C - D.f 0 / 6 ≤ keptBound D E Sz 0 j ∨
      heightTerm D E j hi - C - D.f 0 / 6 ≤ 0 :=
  keptBound_pair_neg D hD hf2 E Sz j hχ hne hS hγ hhi hρ' (zmult_conj hχ hreal ρ).le hC

end GradedNear
