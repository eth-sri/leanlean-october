module

public import AnalyticESC.Conjugation.Koenigs
public import AnalyticESC.Separation

@[expose] public section

/-! The logarithmic derivative of a coordinate satisfies a cocycle equation
exactly when the coordinate conjugates the map to an affine map. -/

namespace AnalyticESC

open Set Metric Filter Topology

variable {ε : ℝ} {f : ℂ → ℂ}

section Restriction

variable (hf : InClass ε f) (hε : 0 < ε) {x : ℝ} (hx : x ∈ I)

include hε hx

include hf

theorem _root_.Challenge.InClass.deriv_eq_ofReal_re : deriv f x = ((deriv f x).re : ℂ) :=
  Complex.ext rfl (im_deriv_eq_zero (isOpen_nbhd _) hf.differentiableOn hf.im_eq_zero
    (ofReal_mem_nbhd_two hε hx))

theorem _root_.Challenge.InClass.deriv_deriv_eq_ofReal_re : deriv (deriv f) x = ((deriv (deriv f) x).re : ℂ) :=
  Complex.ext rfl (im_deriv_eq_zero (isOpen_nbhd _) (hf.differentiableOn.deriv (isOpen_nbhd _))
    (fun _ => im_deriv_eq_zero (isOpen_nbhd _) hf.differentiableOn hf.im_eq_zero)
    (ofReal_mem_nbhd_two hε hx))

theorem _root_.Challenge.InClass.re_deriv_ne_zero : (deriv f x).re ≠ 0 := fun he =>
  hf.deriv_ne_zero x (ofReal_mem_closure hε hx)
    (by rw [hf.deriv_eq_ofReal_re hε hx, he, Complex.ofReal_zero])

theorem _root_.Challenge.InClass.hasDerivAt_re : HasDerivAt (fun y : ℝ => (f y).re) (deriv f x).re x :=
  hasDerivAt_re_ofReal (hf.differentiableOn.differentiableAt
    (nbhd_mem_nhds (ofReal_mem_nbhd_two hε hx)))

theorem _root_.Challenge.InClass.hasDerivAt_re_deriv : HasDerivAt (fun y : ℝ => (deriv f y).re) (deriv (deriv f) x).re x :=
  hasDerivAt_re_ofReal ((hf.differentiableOn.deriv (isOpen_nbhd _)).differentiableAt
    (nbhd_mem_nhds (ofReal_mem_nbhd_two hε hx)))

end Restriction

theorem hasDerivAt_unique_of_eqOn_I {u v : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ I)
    (hu : HasDerivAt u a x) (hv : HasDerivAt v b x) (huv : ∀ y ∈ I, u y = v y) : a = b :=
  (uniqueDiffOn_Icc zero_lt_one x hx).eq_deriv _ hu.hasDerivWithinAt
    (hv.hasDerivWithinAt.congr huv (huv x hx))

theorem conj_deriv_eq (hε : 0 < ε) (hf : InClass ε f) {φ : ℝ → ℝ} (hφ : AnalyticOnNhd ℝ φ I)
    {lam t : ℝ} (hconj : ∀ x ∈ I, φ (f x).re = lam * φ x + t) {x : ℝ} (hx : x ∈ I) :
    deriv φ (f x).re * (deriv f x).re = lam * deriv φ x :=
  hasDerivAt_unique_of_eqOn_I hx
    ((hφ _ (hf.re_mem_I x hx)).differentiableAt.hasDerivAt.comp x (hf.hasDerivAt_re hε hx))
    (((hφ x hx).differentiableAt.hasDerivAt.const_mul lam).add_const t) hconj

/-- Affine conjugacy follows by differentiating the ratio of derivatives. -/
theorem IFS.exists_conj_of_dual_fixed {N : ℕ} (Φ : IFS N ε) (i : Fin N) {φ : ℝ → ℝ} {G : ℝ → ℂ}
    (hφ : AnalyticOnNhd ℝ φ I) (hφ' : ∀ x ∈ I, deriv φ x ≠ 0)
    (hG : IsDualFixed (Φ.f i) G) (h : ∀ x ∈ I, logDeriv φ x = (G x).re) :
    ∃ lam t : ℝ, lam ≠ 0 ∧ |lam| < 1 ∧ ∀ x ∈ I, φ (Φ.f i x).re = lam * φ x + t := by
  let f := Φ.f i
  change IsDualFixed f G at hG
  have hf : InClass ε f := Φ.inClass i
  have hε := Φ.ε_pos
  let p := Φ.natProj fun _ => i
  have hp : p ∈ I := Φ.natProj_mem_I _
  let F (x : ℝ) := (f x).re
  let lam := (deriv f p).re
  have hpF : F p = p := Φ.natProj_const_fixed i
  have hJ x (hx : x ∈ I) : logDeriv φ x =
      (deriv (deriv f) x).re / (deriv f x).re + (deriv f x).re * logDeriv φ (f x).re := by
    rw [h x hx, h _ (hf.re_mem_I x hx), hG x hx,
      hf.deriv_eq_ofReal_re hε hx, hf.deriv_deriv_eq_ofReal_re hε hx]
    simp
  let R (x : ℝ) := deriv φ (F x) * (deriv f x).re / deriv φ x
  have hR (x : ℝ) (hx : x ∈ I) : HasDerivAt R 0 x := by
    convert (((hφ _ (hf.re_mem_I x hx)).deriv.differentiableAt.hasDerivAt.comp x (hf.hasDerivAt_re hε hx)).fun_mul (hf.hasDerivAt_re_deriv hε hx)).fun_div ((hφ x hx).deriv.differentiableAt.hasDerivAt) (hφ' x hx) using 1 <;> try rfl
    simp only [Function.comp_apply]
    have he := hJ x hx
    unfold logDeriv at he
    field_simp [hφ' x hx, hφ' _ (hf.re_mem_I x hx), hf.re_deriv_ne_zero hε hx] at he ⊢
    linarith
  have hRp : R p = lam := by grind
  have hA (x : ℝ) (hx : x ∈ I) : deriv φ (f x).re * (deriv f x).re = lam * deriv φ x :=
    (div_eq_iff (hφ' x hx)).1 ((eq_of_hasDerivAt_zero_I hR hx hp).trans hRp)
  have hQ (x : ℝ) (hx : x ∈ I) : HasDerivAt (fun x => φ (F x) - lam * φ x) 0 x := by
    have h := ((hφ _ (hf.re_mem_I x hx)).differentiableAt.hasDerivAt.comp x (hf.hasDerivAt_re hε hx)).fun_sub
      ((hφ x hx).differentiableAt.hasDerivAt.const_mul lam)
    grind
  refine ⟨lam, φ p - lam * φ p, hf.re_deriv_ne_zero hε hp, ?_, fun x hx => ?_⟩
  · exact (Complex.abs_re_le_norm _).trans_lt (hf.norm_deriv_lt_one p (ofReal_mem_closure hε hp))
  · have h := eq_of_hasDerivAt_zero_I hQ hx hp
    grind

end AnalyticESC
