module

public import AnalyticESC.Conjugation.Uniqueness
public import AnalyticESC.Conjugation.Composite

@[expose] public section

/-!
# Single-map conjugation

Individual-map linearisation for Theorem 1.12 and the single-map ODE tools used in its proof.
The equivalences, including the two-map subsystem argument for part (b), are proved in
`Conjugation.PeriodicPoints`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-! ## Single maps of the class -/

section Single

variable {ε : ℝ} {f : ℂ → ℂ}

/-- At points of `[0,1]`, the derivative of a map of the class is real, nonzero and of modulus
less than one. -/
theorem char_re_deriv_ne_zero_abs_lt_one (hε : 0 < ε) (hf : InClass ε f) {x : ℝ}
    (hx : x ∈ I) : (deriv f x).re ≠ 0 ∧ |(deriv f x).re| < 1 := by
  have hcl : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd hε hx)
  have him : (deriv f x).im = 0 := im_deriv_eq_zero (isOpen_nbhd _) hf.differentiableOn
    hf.im_eq_zero (ofReal_mem_nbhd (by linarith) hx)
  exact ⟨fun h => hf.deriv_ne_zero _ hcl (Complex.ext h him),
    (Complex.abs_re_le_norm _).trans_lt (hf.norm_deriv_lt_one _ hcl)⟩

theorem char_re_koenigs_spec (hε : 0 < ε) (hf : InClass ε f) :
    ∃ g : ℝ → ℝ, IsAnalyticCoord g ∧ (∀ x ∈ I, 0 < deriv g x) ∧
      ∀ x ∈ I, deriv (deriv g) x = (hatH f x).re * deriv g x := by
  obtain ⟨p, hp, hfp⟩ := exists_fixedPoint hε hf
  have hkd := differentiableOn_koenigs hε hf hp hfp
  have han : AnalyticOnNhd ℝ (fun t : ℝ => (koenigs f p t).re) I := analyticOnNhd_re_ofReal hε hkd
  have hd1 (x : ℝ) (hx : x ∈ I) :
      deriv (fun t : ℝ => (koenigs f p t).re) x = (deriv (koenigs f p) x).re := by
    simpa using iteratedDeriv_re_ofReal (isOpen_nbhd ε) hkd 1 (ofReal_mem_nbhd hε hx)
  have hd (x : ℝ) (hx : x ∈ I) : 0 < deriv (fun t : ℝ => (koenigs f p t).re) x := by
    rw [hd1 x hx]; exact (deriv_koenigs_ofReal hε hf hp hfp hx).2
  refine ⟨_, ⟨han, (strictMonoOn_of_deriv_pos (convex_Icc 0 1) han.continuousOn
    fun x hx => hd x (interior_subset hx)).injOn⟩, hd, fun x hx => ?_⟩
  have h2 := iteratedDeriv_re_ofReal (isOpen_nbhd ε) hkd 2 (ofReal_mem_nbhd hε hx)
  rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one] at h2
  rw [h2, hd1 x hx, deriv_deriv_koenigs hε hf hp hfp (ofReal_mem_nbhd hε hx), Complex.mul_re,
    (deriv_koenigs_ofReal hε hf hp hfp hx).1, mul_zero, sub_zero]

/-- A solution of `φ'' = Re Ĥ_f φ'` on `[0,1]` conjugates `f` to an affine contraction. -/
theorem char_exists_conj_of_ode (hε : 0 < ε) (hf : InClass ε f) {φ : ℝ → ℝ}
    (hφ : AnalyticOnNhd ℝ φ I)
    (hode : ∀ x ∈ I, deriv (deriv φ) x = (hatH f x).re * deriv φ x) :
    ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, φ (f x).re = lam * φ x + t := by
  obtain ⟨p, hp, hfp⟩ := exists_fixedPoint hε hf
  have h := eq_add_mul_koenigs hε hf hp hfp hφ hode
  obtain ⟨h0, h1⟩ := char_re_deriv_ne_zero_abs_lt_one hε hf hp
  refine ⟨(deriv f p).re, φ p * (1 - (deriv f p).re), h0, h1, fun x hx => ?_⟩
  have hx' := ofReal_mem_nbhd hε hx
  have hfx : (((f x).re : ℝ) : ℂ) = f x :=
    Complex.ext (by simp) (by simp [hf.im_eq_zero x (ofReal_mem_nbhd (by linarith) hx)])
  rw [h _ (hf.re_mem_I x hx), h x hx, hfx, koenigs_comp hε hf hp hfp hx', Complex.mul_re,
    im_koenigs_ofReal hε hf hp hfp hx', mul_zero, sub_zero]
  ring

end Single

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- Individual-map linearisation for Theorem 1.12. -/
theorem theorem_1_12_similarity (i : Fin N) :
    ∃ g, IsAnalyticCoord g ∧ (∀ x ∈ I, deriv g x ≠ 0) ∧
      ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, g (Φ.f i x).re = lam * g x + t := by
  obtain ⟨g, hco, hd, hode⟩ := char_re_koenigs_spec Φ.ε_pos (Φ.inClass i)
  exact ⟨g, hco, fun x hx => (hd x hx).ne',
    char_exists_conj_of_ode Φ.ε_pos (Φ.inClass i) hco.1 hode⟩

end IFS

end AnalyticESC
