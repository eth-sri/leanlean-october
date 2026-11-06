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
  have hcl := subset_closure (ofReal_mem_nbhd hε hx)
  have him := im_deriv_eq_zero (isOpen_nbhd _) hf.differentiableOn
    hf.im_eq_zero (ofReal_mem_nbhd (by linarith) hx)
  exact ⟨fun h => hf.deriv_ne_zero _ hcl (Complex.ext h him),
    (Complex.abs_re_le_norm _).trans_lt (hf.norm_deriv_lt_one _ hcl)⟩

/-- `Re ĝ ∘ f = Re f'(p) · Re ĝ` on `[0,1]`. -/
theorem char_re_koenigs_conj (hε : 0 < ε) (hf : InClass ε f) {p : ℝ} (hp : p ∈ I)
    (hfp : f p = p) {x : ℝ} (hx : x ∈ I) :
    (koenigs f p ((f x).re : ℂ)).re = (deriv f p).re * (koenigs f p x).re := by
  have hx' := ofReal_mem_nbhd hε hx
  have hfx : (((f x).re : ℝ) : ℂ) = f x :=
    Complex.ext (by simp) (by simp [hf.im_eq_zero x (ofReal_mem_nbhd (by linarith) hx)])
  rw [hfx, koenigs_comp hε hf hp hfp hx', Complex.mul_re, im_koenigs_ofReal hε hf hp hfp hx',
    mul_zero, sub_zero]

/-- The real restriction `Re ĝ` of the linearising map is an analytic coordinate with positive
derivative on `[0,1]`, vanishes at `p` and solves `φ'' = Re Ĥ_f φ'` on `[0,1]`. -/
theorem char_re_koenigs_spec (hε : 0 < ε) (hf : InClass ε f) {p : ℝ} (hp : p ∈ I)
    (hfp : f p = p) :
    IsAnalyticCoord (fun t => (koenigs f p t).re) ∧
      (∀ x ∈ I, 0 < deriv (fun t : ℝ => (koenigs f p t).re) x) ∧
      (koenigs f p p).re = 0 ∧
      ∀ x ∈ I, deriv (deriv (fun t : ℝ => (koenigs f p t).re)) x =
        (hatH f x).re * deriv (fun t : ℝ => (koenigs f p t).re) x := by
  have han :=
    analyticOnNhd_re_ofReal hε (differentiableOn_koenigs hε hf hp hfp)
  have hd : ∀ x ∈ I, 0 < deriv (fun t : ℝ => (koenigs f p t).re) x := fun x hx => by
    rw [(hasDerivAt_re_ofReal ((differentiableOn_koenigs hε hf hp hfp).differentiableAt
      ((isOpen_nbhd ε).mem_nhds (ofReal_mem_nbhd hε hx)))).deriv]
    exact (deriv_koenigs_ofReal hε hf hp hfp hx).2
  refine ⟨⟨han, (strictMonoOn_of_deriv_pos (convex_Icc 0 1) han.continuousOn
    fun x hx => hd x (interior_subset hx)).injOn⟩, hd, by simp [koenigs_self hε hf hp hfp], ?_⟩
  exact deriv_deriv_eq_hatH_mul hε hf han (fun x hx => (hd x hx).ne') (lam := (deriv f p).re)
    (t := 0) fun x hx => by rw [add_zero]; exact char_re_koenigs_conj hε hf hp hfp hx

/-- A solution of `φ'' = Re Ĥ_f φ'` on `[0,1]` conjugates `f` to an affine contraction. -/
theorem char_exists_conj_of_ode (hε : 0 < ε) (hf : InClass ε f) {p : ℝ} (hp : p ∈ I)
    (hfp : f p = p) {φ : ℝ → ℝ} (hφ : AnalyticOnNhd ℝ φ I)
    (hode : ∀ x ∈ I, deriv (deriv φ) x = (hatH f x).re * deriv φ x) :
    ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, φ (f x).re = lam * φ x + t := by
  have h := eq_add_mul_koenigs hε hf hp hfp hφ hode
  refine ⟨(deriv f p).re, φ p * (1 - (deriv f p).re), (char_re_deriv_ne_zero_abs_lt_one hε hf hp).1,
    (char_re_deriv_ne_zero_abs_lt_one hε hf hp).2, fun x hx => ?_⟩
  rw [h _ (hf.re_mem_I x hx), h x hx, char_re_koenigs_conj hε hf hp hfp hx]
  ring

end Single

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- Individual-map linearisation for Theorem 1.12: an analytic coordinate with nonvanishing
derivative conjugates `f_i` to a contracting similarity. Contraction of the other conjugated
maps is not asserted. -/
theorem theorem_1_12_similarity (i : Fin N) :
    ∃ g, IsAnalyticCoord g ∧ (∀ x ∈ I, deriv g x ≠ 0) ∧
      ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, g (Φ.f i x).re = lam * g x + t := by
  have hf := Φ.inClass i
  obtain ⟨p, ⟨hp, hfp⟩, -⟩ := existsUnique_fixedPoint Φ.ε_pos hf
  obtain ⟨hco, hd, -, -⟩ := char_re_koenigs_spec Φ.ε_pos hf hp hfp
  obtain ⟨h0, h1⟩ := char_re_deriv_ne_zero_abs_lt_one Φ.ε_pos hf hp
  exact ⟨_, hco, fun x hx => (hd x hx).ne', _, 0, h0, h1, fun x hx => by
    rw [add_zero]; exact char_re_koenigs_conj Φ.ε_pos hf hp hfp hx⟩

end IFS

end AnalyticESC
