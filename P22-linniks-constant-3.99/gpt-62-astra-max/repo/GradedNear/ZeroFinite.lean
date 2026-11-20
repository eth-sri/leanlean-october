module

public import GradedNear.Defs

/-!
# Zeros of a non-principal `L`-function in a closed disc are finite

`L(s, χ)` is entire for `χ ≠ 1` and not identically zero (it does not vanish at `s = 2`), so
its zeros are isolated and a compact disc contains finitely many.
-/

@[expose] public section

namespace GradedNear

open Complex DirichletCharacter Set

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
include hχ

lemma L_analytic : AnalyticOnNhd ℂ (LFunction χ) univ :=
  analyticOnNhd_univ_iff_differentiable.mpr (differentiable_LFunction hχ)

lemma L_ne_two : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by norm_num)

/-- A zero of a non-principal `L`-function has positive finite order. -/
lemma one_le_zmult {ρ : ℂ} (hρ : LFunction χ ρ = 0) : 1 ≤ zmult χ ρ := by
  have ha z := L_analytic hχ z trivial
  have hn : LFunction χ ≠ 0 := fun h => L_ne_two hχ (congrFun h 2)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
    simp [analyticOrderNatAt, ENat.toNat_eq_zero, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ ha, hn, (ha ρ).analyticOrderAt_ne_zero.mpr hρ])

theorem LFunction_zeros_finite (c : ℂ) (r : ℝ) :
    {ρ : ℂ | ‖c - ρ‖ ≤ r ∧ LFunction χ ρ = 0}.Finite := by
  -- Restrict to the compact disc, where a codiscrete set has finite complement.
  have hfin := (isCompact_closedBall c r).finite_sdiff_of_mem_codiscreteWithin
    (Filter.codiscreteWithin_mono (Set.subset_univ _) ((L_analytic hχ).preimage_zero_mem_codiscreteWithin (L_ne_two hχ) trivial isConnected_univ))
  refine hfin.subset ?_
  rintro ρ ⟨hρ, hL⟩
  refine ⟨?_, ?_⟩
  · rwa [Metric.mem_closedBall, dist_comm, dist_eq_norm]
  · bound

/-! ### Reflection across the real line -/

open Filter Topology
open scoped ComplexConjugate

variable (hreal : ∀ a : ZMod q, conj (χ a) = χ a)
include hreal

/-- Reflection preserves the entire `L`-function of a real non-principal character. -/
lemma reflect_LFunction : conj ∘ LFunction χ ∘ conj = LFunction χ := by
  apply (analyticOnNhd_univ_iff_differentiable.mpr fun z =>
    differentiableAt_conj_conj_iff.mpr (differentiable_LFunction hχ _)).eq_of_eventuallyEq
    (L_analytic hχ) (z₀ := 2)
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
  simp [LFunction_eq_LSeries χ (by simpa using hs : 1 < (conj s).re), LFunction_eq_LSeries χ hs, LSeries, conj_tsum]
  apply tsum_congr; intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, hreal,
      ← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast]

/-- **Conjugate zeros of a real character's `L`-function have equal multiplicity.** -/
theorem zmult_conj (ρ : ℂ) : zmult χ (conj ρ) = zmult χ ρ := by
  have symm i : conj ∘ iteratedDeriv i (LFunction χ) ∘ conj = iteratedDeriv i (LFunction χ) := by
    induction i with
    | zero => simpa using reflect_LFunction hχ hreal
    | succ i ih => rw [iteratedDeriv_succ, ← deriv_conj_conj, ih]
  suffices analyticOrderAt (LFunction χ) (conj ρ) = analyticOrderAt (LFunction χ) ρ by
    simp [zmult, analyticOrderNatAt, this]
  apply ENat.eq_of_forall_natCast_le_iff; intro n
  simp [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (L_analytic hχ _ trivial)]
  congr! 2 with i
  simp [← congrFun (symm i) ρ]

end GradedNear
