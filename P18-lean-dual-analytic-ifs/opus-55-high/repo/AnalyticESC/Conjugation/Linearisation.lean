module

public import AnalyticESC.Conjugation.Koenigs

public section

/-!
# Lemma 5.1

A map of the class has a unique fixed point `p ∈ [0,1]`. For `a, b ∈ ℝ` with `b ≠ 0` there is an
invertible `g ∈ C^ω_ε([0,1])` with `g'' = Ĥ_f g'`, `g(p) = a` and `g'(p) = b`; and every solution
`g` of `g'' = Ĥ_f g'` on `[0,1]` conjugates `f` to the affine map `y ↦ f'(p) y + g(p)(1 - f'(p))`.
-/

namespace AnalyticESC

open Set

variable {f : ℂ → ℂ}

/-- A function with zero derivative within `[0,1]` at every point of `[0,1]` is constant there. -/
theorem eq_of_hasDerivWithinAt_zero_I {u : ℝ → ℝ}
    (hu : Ɐ HasDerivWithinAt u 0 I x) (hy : y ∈ I) : Ɐ u x = u y := by
  have h := constant_of_derivWithin_zero (fun z hz => (hu z hz).differentiableWithinAt) fun z hz =>
    (hu z (Ico_subset_Icc_self hz)).derivWithin
      (uniqueDiffOn_Icc zero_lt_one z (Ico_subset_Icc_self hz))
  simp_all

/-- A map of the class has a unique fixed point in `[0,1]`. -/
theorem existsUnique_fixedPoint (hε : 0 < ε) (hf : InClass ε f) :
    ∃! p : ℝ, p ∈ I ∧ f p = p := by
  -- `F(x) = f(x) - x` on `I`, which is strictly decreasing since `|f'| < 1`
  set F : ℝ → ℝ := fun x => (f x).re - x with hF
  have hderiv : Ɐ HasDerivAt F ((deriv f x).re - 1) x := fun x hx =>
    (hasDerivAt_re_ofReal (hf.differentiableOn.differentiableAt
      (isOpen_nbhd.mem_nhds (ofReal_mem_nbhd (by linarith) hx)))).sub (hasDerivAt_id x)
  have hcont : ContinuousOn F I := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hfix : Ɐ f x = x ↔ F x = 0 := by
    intro x hx
    have hreal : f x = ((f x).re : ℂ) :=
      Complex.ext (by simp) (by simp [hf.im_eq_zero x (ofReal_mem_nbhd (by linarith) hx)])
    rw [hreal, Complex.ofReal_inj, hF, sub_eq_zero]
  have hanti : StrictAntiOn F I := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 1) hcont fun x hx => ?_
    rw [(hderiv x (interior_subset hx)).deriv, sub_neg]
    exact (Complex.re_le_norm _).trans_lt
      (hf.norm_deriv_lt_one x (ofReal_mem_closure hε (interior_subset hx)))
  -- the intermediate value theorem gives a zero of `F`
  obtain ⟨p, hp, hFp⟩ : 0 ∈ F '' I := by
    refine intermediate_value_Icc' zero_le_one hcont ⟨?_, ?_⟩
    · have := (hf.re_mem_I 1 one_mem_I).2
      linarith
    · have := (hf.re_mem_I 0 zero_mem_I).1
      linarith
  refine ⟨p, ⟨hp, (hfix p hp).2 hFp⟩, fun q ⟨hq, hfq⟩ => hanti.injOn hq hp ?_⟩
  simp_all

end AnalyticESC
