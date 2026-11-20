/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Cubic Taylor estimates for families of numerators with vanishing low-order terms. -/

@[expose] public section

open Set
namespace DOZZ.Proofs

/-- Restriction to the real line preserves each derivative of a complex smooth function. -/
theorem iteratedDeriv_comp_ofReal {f : ℂ → ℂ} {n : ℕ} (h : ContDiff ℂ n f) (t : ℝ) :
    iteratedDeriv n (fun t : ℝ => f t) t = iteratedDeriv n f t := by
  rw [iteratedDeriv_eq_iteratedFDeriv (𝕜 := ℝ)]
  change iteratedFDeriv ℝ n (f ∘ Complex.ofRealCLM) t _ = _
  rw [Complex.ofRealCLM.iteratedFDeriv_comp_right (h.restrict_scalars ℝ) t le_rfl]
  rw [← h.contDiffAt.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp [iteratedDeriv_eq_iteratedFDeriv]

private theorem taylorWithinEval_two_eq_zero {f : ℝ → ℂ}
    (hf : ContDiffAt ℝ 3 f 0) (hz : ∀ j ≤ 2, iteratedDeriv j f 0 = 0) (t : ℝ) :
    taylorWithinEval f 2 (Icc 0 1) 0 t = 0 := by
  have hw (j : ℕ) (hj : j ≤ 2) : iteratedDerivWithin j f (Icc 0 1) 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      (hf.of_le (by exact_mod_cast hj.trans (by decide : 2 ≤ 3))) (by simp)]
    exact hz j hj
  simp [taylor_within_apply,
    hw 0 (by decide), hw 1 (by decide), hw 2 le_rfl]

/-- A third time derivative is a fixed evaluation of the third Fréchet derivative. -/
private theorem iteratedDeriv_three_prod_mk {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E × ℝ → ℂ} {a : E} {t : ℝ}
    (hF : ContDiffAt ℝ 3 F (a,t)) :
    iteratedDeriv 3 (fun s : ℝ => F (a,s)) t =
      iteratedFDeriv ℝ 3 F (a,t) (fun _ => (0,1)) := by
  let line : ℝ → E × ℝ := fun s => (a,s)
  have hd : deriv line = fun _ => (0, (1 : ℝ)) := funext fun s =>
    ((hasDerivAt_const s a).prodMk (hasDerivAt_id s)).deriv
  have h2 : iteratedDeriv 2 line = fun _ => 0 := by
    simp [iteratedDeriv_succ, hd]
  have h3 : iteratedDeriv 3 line t = 0 := by rw [iteratedDeriv_succ, h2]; simp
  have hh := iteratedDeriv_vcomp_three
    (hg := (show ContDiffAt ℝ 3 F (line t) from hF))
    (hf := (by fun_prop : ContDiffAt ℝ 3 line t))
  rw [h3] at hh
  have hzero₁ : iteratedFDeriv ℝ 2 F (a,t) ![0, (0,1)] = 0 :=
    ContinuousMultilinearMap.map_coord_zero _ 0 (by simp)
  have hzero₂ : iteratedFDeriv ℝ 2 F (a,t) ![(0,1), 0] = 0 :=
    ContinuousMultilinearMap.map_coord_zero _ 1 (by simp)
  simpa [line, hd, h2, hzero₁, hzero₂, Function.comp_def] using hh

/-- Compact parameter sets admit a common cubic bound for a smooth numerator whose Taylor
coefficients of degrees zero, one and two vanish. -/
theorem exists_uniform_cubic_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {F : E × ℝ → ℂ} (hK : IsCompact K)
    (hF : ∀ p ∈ K ×ˢ Icc 0 1, ContDiffAt ℝ 3 F p)
    (hz : ∀ a ∈ K, ∀ j ≤ 2, iteratedDeriv j (fun t : ℝ => F (a,t)) 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ K, ∀ t ∈ Icc 0 1, ‖F (a,t)‖ ≤ C * t ^ 3 := by
  let D := fun p => iteratedFDeriv ℝ 3 F p (fun _ => (0,1))
  have hD : ContinuousOn D (K ×ˢ Icc 0 1) := by
    intro p hp
    have h := (hF p hp).continuousAt_iteratedFDeriv (k := 3) (by norm_num)
    have he : Continuous (fun m : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E × ℝ) ℂ =>
        m (fun _ => (0,1))) := by fun_prop
    exact (he.continuousAt.comp h).continuousWithinAt
  obtain ⟨C, hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hD
  refine ⟨max C 0, le_max_right _ _, fun a ha t ht => ?_⟩
  let f : ℝ → ℂ := fun y => F (a,y)
  have hf y (hy : y ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 3 f y :=
    (hF (a,y) ⟨ha,hy⟩).comp y (by fun_prop)
  have hb y (hy : y ∈ Icc (0 : ℝ) 1) : ‖iteratedDerivWithin 3 f (Icc 0 1) y‖ ≤ max C 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num)) (hf y hy) hy]
    change ‖iteratedDeriv 3 (fun s : ℝ => F (a,s)) y‖ ≤ _
    rw [iteratedDeriv_three_prod_mk (hF (a,y) ⟨ha,hy⟩)]
    exact (hC (a,y) ⟨ha,hy⟩).trans (le_max_left _ _)
  have h := taylor_mean_remainder_bound (n := 2) (by norm_num : (0 : ℝ) ≤ 1)
    (fun y hy => (hf y hy).contDiffWithinAt) ht hb
  rw [taylorWithinEval_two_eq_zero (hf 0 (by simp)) (hz a ha)] at h
  norm_num at h
  exact h.trans (by linarith only [mul_nonneg (le_max_right C 0) (pow_nonneg ht.1 3)])

end DOZZ.Proofs
