module

public import AnalyticESC.Conjugation.Linearisation
public import AnalyticESC.Conjugation.Basic

@[expose] public section

/-!
# Uniqueness of linearisations of a single map

For a map `f` of the class: `Ĥ_f` satisfies the fixed-point equation of the dual operator of `f`;
a linearisation `φ` of `f` with `φ' ≠ 0` satisfies `φ'' = Ĥ_f φ'`; solutions of `φ'' = Ĥ_f φ'`
are affine functions of the linearising map `ĝ` of (5.2); and `Ĥ_f` depends only on `f` on `[0,1]`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

variable {ε : ℝ} {f : ℂ → ℂ}

/-- A function with zero derivative at every point of `[0,1]` is constant there. -/
theorem eq_of_hasDerivAt_zero_I {u : ℝ → ℝ}
    (hu : ∀ x ∈ I, HasDerivAt u 0 x) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    u x = u y := by
  have h := constant_of_derivWithin_zero
    (fun z hz => (hu z hz).differentiableAt.differentiableWithinAt) fun z hz =>
      (hu z (Ico_subset_Icc_self hz)).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc zero_lt_one z (Ico_subset_Icc_self hz))
  rw [h x hx, h y hy]

/-! ## The main statements -/

/-- The real restriction of a map holomorphic on `B_ε` is analytic near `[0,1]`. -/
theorem analyticOnNhd_re_ofReal (hε : 0 < ε) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (nbhd ε)) :
    AnalyticOnNhd ℝ (fun x : ℝ => (g x).re) I := fun x hx =>
  (hg.analyticOnNhd (isOpen_nbhd ε) x (ofReal_mem_nbhd hε hx)).re_ofReal

/-- Solutions of `φ'' = Ĥ_f φ'` on `[0,1]` are affine functions of the linearising map `ĝ`. -/
theorem eq_add_mul_koenigs (hε : 0 < ε) (hf : InClass ε f) {p : ℝ} (hp : p ∈ I) (hfp : f p = p)
    {φ : ℝ → ℝ} (hφ : AnalyticOnNhd ℝ φ I)
    (hode : ∀ x ∈ I, deriv (deriv φ) x = (hatH f x).re * deriv φ x) :
    ∀ x ∈ I, φ x = φ p + deriv φ p * (koenigs f p x).re := by
  have hmem {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ nbhd ε := ofReal_mem_nbhd hε hx
  have hkd := differentiableOn_koenigs hε hf hp hfp
  set G : ℝ → ℝ := fun t => (deriv (koenigs f p) t).re
  set c := deriv φ p
  have hGpos (x : ℝ) (hx : x ∈ I) : 0 < G x := (deriv_koenigs_ofReal hε hf hp hfp hx).2
  have hu : ∀ x ∈ I, HasDerivAt (fun t => deriv φ t / G t) 0 x := fun x hx => by
    have hGderiv : HasDerivAt G ((hatH f x).re * G x) x := by
      have h := hasDerivAt_re_ofReal ((hkd.deriv (isOpen_nbhd ε)).differentiableAt
        ((isOpen_nbhd ε).mem_nhds (hmem hx)))
      rwa [deriv_deriv_koenigs hε hf hp hfp (hmem hx), Complex.mul_re,
        (deriv_koenigs_ofReal hε hf hp hfp hx).1, mul_zero, sub_zero] at h
    have h1 : HasDerivAt (deriv φ) ((hatH f x).re * deriv φ x) x :=
      hode x hx ▸ (hφ x hx).deriv.differentiableAt.hasDerivAt
    exact (h1.div hGderiv (hGpos x hx).ne').congr_deriv (by ring)
  have hv : ∀ x ∈ I, HasDerivAt (fun t => φ t - c * (koenigs f p t).re) 0 x := fun x hx => by
    have h := eq_of_hasDerivAt_zero_I hu hx hp
    rw [show G p = 1 by simp [G, deriv_koenigs_self hε hf hp hfp], div_one,
      div_eq_iff (hGpos x hx).ne'] at h
    exact (((hφ x hx).differentiableAt.hasDerivAt.sub
      ((hasDerivAt_re_ofReal (hkd.differentiableAt ((isOpen_nbhd ε).mem_nhds (hmem hx)))).const_mul
        c)).congr_deriv (by rw [h, sub_self]))
  intro x hx
  have h := eq_of_hasDerivAt_zero_I hv hx hp
  rw [koenigs_self hε hf hp hfp, Complex.zero_re, mul_zero, sub_zero] at h
  linarith

/-- `Ĥ_f` depends only on `f` on `[0,1]`. -/
theorem hatH_eq_of_eqOn_I {g : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f) (hg : InClass ε g)
    (h : ∀ x ∈ I, f x = g x) : ∀ x ∈ I, hatH f x = hatH g x := by
  have hU := isOpen_nbhd (2 * ε)
  have h2 : nbhd ε ⊆ nbhd (2 * ε) := IFS.nbhd_subset_two
  have hfg : EqOn f g (nbhd (2 * ε)) :=
    eqOn_nbhd_of_eqOn_Icc (by linarith) hf.differentiableOn hg.differentiableOn zero_lt_one
      subset_rfl h
  have hiter (k : ℕ) : ∀ z ∈ nbhd ε, f^[k] z = g^[k] z ∧ f^[k] z ∈ nbhd ε := by
    induction k with
    | zero => exact fun z hz => ⟨rfl, hz⟩
    | succ k ih =>
      intro z hz
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← hfg (h2 hz)]
      exact ih (f z) (hf.mapsTo (subset_closure hz))
  intro x hx
  have hxε := ofReal_mem_nbhd hε hx
  refine tsum_congr fun k => ?_
  obtain ⟨h1, h2'⟩ := hiter k x hxε
  rw [EqOn.deriv (fun z hz => (hiter k z hz).1) (isOpen_nbhd ε) hxε, ← h1,
    (hfg.deriv hU) (h2 h2'), ((hfg.deriv hU).deriv hU) (h2 h2')]

end AnalyticESC
