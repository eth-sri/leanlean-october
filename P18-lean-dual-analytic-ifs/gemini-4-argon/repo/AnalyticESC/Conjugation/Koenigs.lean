module

public import AnalyticESC.Dual.Projection
public import AnalyticESC.Analysis
public import AnalyticESC.Analysis.Primitive

@[expose] public section

/-!
# The linearisation of a single map

For a map `f` of the class with fixed point `p ∈ I`, define `Ĥ_f` by (5.1) and
`ĝ(z) = ∫ₚᶻ exp(∫ₚʷ Ĥ_f) dw`, as in Lemma 5.1. Segment integration gives holomorphy on
`B_ε`, the ODE `ĝ'' = Ĥ_f ĝ'`, positivity of `ĝ'` on `I`, and `ĝ ∘ f = f'(p) ĝ`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- The function `Ĥ_f(z) = ∑_{k ≥ 0} (f''/f')(f^k(z)) · (f^k)'(z)` of (5.1). -/
noncomputable def hatH (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' k, deriv (deriv f) (f^[k] z) / deriv f (f^[k] z) * deriv (f^[k]) z

/-- The ODE solution `ĝ(z) = ∫ₚᶻ exp(∫ₚʷ Ĥ_f) dw` from Lemma 5.1. -/
noncomputable def koenigs (f : ℂ → ℂ) (p : ℂ) (z : ℂ) : ℂ :=
  segmentPrimitive (fun w => Complex.exp (segmentPrimitive (hatH f) p w)) p z

/-- The system consisting of the single map `f`. -/
def koenigsIFS {ε : ℝ} {f : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f) : IFS 1 ε :=
  ⟨fun _ => f, hε, fun _ => hf⟩

section

variable {ε : ℝ} {f : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f)

include hε hf

private theorem koenigsIFS_comp (n : ℕ) : (koenigsIFS hε hf).comp (List.replicate n 0) = f^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, IFS.comp_cons, ih, Function.iterate_succ']
    rfl

theorem hatH_eq_dualProj : hatH f = (koenigsIFS hε hf).dualProj (.inf fun _ => 0) := by
  funext z
  simp only [hatH, IFS.dualProj]
  refine tsum_congr fun k => ?_
  rw [(koenigsIFS hε hf).dualTerm_of_get?_eq_some (Word.get?_inf _ k)]
  simp only [Word.take_inf, List.ofFn_const, List.reverse_replicate, koenigsIFS_comp hε hf,
    IFS.nonlin]
  rfl

theorem differentiableOn_hatH : DifferentiableOn ℂ (hatH f) (nbhd ε) := by
  rw [hatH_eq_dualProj hε hf]
  exact (koenigsIFS hε hf).differentiableOn_dualProj _

theorem im_hatH_ofReal {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) : (hatH f t).im = 0 := by
  rw [hatH_eq_dualProj hε hf]
  exact (koenigsIFS hε hf).im_dualProj_ofReal _ ht

theorem hatH_eq_add {z : ℂ} (hz : z ∈ nbhd ε) :
    hatH f z = deriv (deriv f) z / deriv f z + deriv f z * hatH f (f z) := by
  have hw : (Word.inf fun _ : ℕ => (0 : Fin 1)).prepend [0] = .inf fun _ => 0 := by
    simp only [Word.prepend]
    congr 1; funext n; exact Subsingleton.elim _ _
  have h := (koenigsIFS hε hf).dualProj_prepend [0] (.inf fun _ => 0) (subset_closure hz)
  rw [hw, IFS.dualProj_singleton] at h
  rw [hatH_eq_dualProj hε hf, h]
  rfl

variable {p : ℝ} (hp : p ∈ I) (hfp : f p = p)

include hp hfp

set_option linter.unusedSectionVars false

private theorem hasDerivAt_hatHPrimitive {z : ℂ} (hz : z ∈ nbhd ε) :
    HasDerivAt (segmentPrimitive (hatH f) p) (hatH f z) z :=
  hasDerivAt_segmentPrimitive (isOpen_nbhd ε) (convex_nbhd ε)
    (differentiableOn_hatH hε hf) (ofReal_mem_nbhd hε hp) hz

private theorem hasDerivAt_koenigs {z : ℂ} (hz : z ∈ nbhd ε) :
    HasDerivAt (koenigs f p) (Complex.exp (segmentPrimitive (hatH f) p z)) z :=
  hasDerivAt_segmentPrimitive (isOpen_nbhd ε) (convex_nbhd ε)
    (fun _ hw => ((hasDerivAt_hatHPrimitive hε hf hp hfp hw).cexp).differentiableAt.differentiableWithinAt)
    (ofReal_mem_nbhd hε hp) hz

theorem differentiableOn_koenigs : DifferentiableOn ℂ (koenigs f p) (nbhd ε) :=
  fun _ hz => (hasDerivAt_koenigs hε hf hp hfp hz).differentiableAt.differentiableWithinAt

private theorem deriv_koenigs_eq {z : ℂ} (hz : z ∈ nbhd ε) :
    deriv (koenigs f p) z = Complex.exp (segmentPrimitive (hatH f) p z) :=
  (hasDerivAt_koenigs hε hf hp hfp hz).deriv

private theorem hasDerivAt_deriv_koenigs {z : ℂ} (hz : z ∈ nbhd ε) :
    HasDerivAt (deriv (koenigs f p)) (hatH f z * deriv (koenigs f p) z) z := by
  have heq : deriv (koenigs f p) =ᶠ[𝓝 z] fun w => Complex.exp (segmentPrimitive (hatH f) p w) :=
    Filter.eventuallyEq_of_mem ((isOpen_nbhd ε).mem_nhds hz)
      (fun _ hw => deriv_koenigs_eq hε hf hp hfp hw)
  refine ((hasDerivAt_hatHPrimitive hε hf hp hfp hz).cexp.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [deriv_koenigs_eq hε hf hp hfp hz, mul_comm]

theorem deriv_deriv_koenigs {z : ℂ} (hz : z ∈ nbhd ε) :
    deriv (deriv (koenigs f p)) z = hatH f z * deriv (koenigs f p) z :=
  (hasDerivAt_deriv_koenigs hε hf hp hfp hz).deriv

theorem koenigs_self : koenigs f p p = 0 :=
  segmentPrimitive_self _ _

theorem deriv_koenigs_self : deriv (koenigs f p) p = 1 := by
  rw [deriv_koenigs_eq hε hf hp hfp (ofReal_mem_nbhd hε hp), segmentPrimitive_self, Complex.exp_zero]

theorem koenigs_comp {z : ℂ} (hz : z ∈ nbhd ε) :
    koenigs f p (f z) = deriv f p * koenigs f p z := by
  have hO2 := isOpen_nbhd (2 * ε)
  let g := koenigs f p
  let D (w : ℂ) := deriv g (f w) * deriv f w
  have hg_ne : ∀ w ∈ nbhd ε, deriv g w ≠ 0 := fun w hw => by
    rw [deriv_koenigs_eq hε hf hp hfp hw]; exact Complex.exp_ne_zero _
  have hconst {F : ℂ → ℂ} (hF : ∀ w ∈ nbhd ε, HasDerivAt F 0 w) {w : ℂ} (hw : w ∈ nbhd ε) :
      F w = F p :=
    (isOpen_nbhd ε).is_const_of_deriv_eq_zero (isPreconnected_nbhd ε)
      (fun u hu => (hF u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hF u hu).deriv) hw (ofReal_mem_nbhd hε hp)
  have hD_eq : ∀ w ∈ nbhd ε, D w = deriv f p * deriv g w := fun w hw => by
    have hc := hconst (F := fun w => D w / deriv g w) (fun u hu => by
      have hfu : f u ∈ nbhd ε := hf.mapsTo (subset_closure hu)
      have hu2 : u ∈ nbhd (2 * ε) := IFS.nbhd_subset_two hu
      have hfu_ne : deriv f u ≠ 0 := hf.deriv_ne_zero u (subset_closure hu)
      have hf1 := (hf.differentiableOn.differentiableAt (hO2.mem_nhds hu2)).hasDerivAt
      have hf2 := ((hf.differentiableOn.deriv hO2).differentiableAt (hO2.mem_nhds hu2)).hasDerivAt
      have hDu : HasDerivAt D (hatH f u * D u) u :=
        (((hasDerivAt_deriv_koenigs hε hf hp hfp hfu).comp u hf1).fun_mul hf2).congr_deriv
          (by rw [hatH_eq_add hε hf hu]; dsimp [D]; field_simp; ring)
      exact (hDu.div (hasDerivAt_deriv_koenigs hε hf hp hfp hu) (hg_ne u hu)).congr_deriv
        (by field_simp [hg_ne u hu]; ring)) hw
    dsimp [D, g] at hc
    rwa [hfp, deriv_koenigs_self hε hf hp hfp, one_mul, div_one, div_eq_iff (hg_ne w hw)] at hc
  have hc := hconst (F := fun w => g (f w) - deriv f p * g w) (fun w hw => by
    have hfw : f w ∈ nbhd ε := hf.mapsTo (subset_closure hw)
    have hf1 := (hf.differentiableOn.differentiableAt
      (hO2.mem_nhds (IFS.nbhd_subset_two hw))).hasDerivAt
    exact (((hasDerivAt_koenigs hε hf hp hfp hfw).comp w hf1).sub
      ((hasDerivAt_koenigs hε hf hp hfp hw).const_mul (deriv f p))).congr_deriv
      (by rw [← deriv_koenigs_eq hε hf hp hfp hfw, ← deriv_koenigs_eq hε hf hp hfp hw,
        ← hD_eq w hw, sub_self])) hz
  dsimp [g] at hc
  rwa [hfp, koenigs_self hε hf hp hfp, mul_zero, sub_zero, sub_eq_zero] at hc

private theorem im_hatHPrimitive_eq_zero {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) :
    (segmentPrimitive (hatH f) p t).im = 0 :=
  im_segmentPrimitive_eq_zero (convex_nbhd ε) (differentiableOn_hatH hε hf).continuousOn
    (fun _ hx => im_hatH_ofReal hε hf hx) (ofReal_mem_nbhd hε hp) ht

theorem im_koenigs_ofReal {t : ℝ} (ht : (t : ℂ) ∈ nbhd ε) : (koenigs f p t).im = 0 := by
  have hd : DifferentiableOn ℂ (segmentPrimitive (hatH f) p) (nbhd ε) :=
    fun _ hz => (hasDerivAt_hatHPrimitive hε hf hp hfp hz).differentiableAt.differentiableWithinAt
  refine im_segmentPrimitive_eq_zero (convex_nbhd ε) hd.continuousOn.cexp
    (fun _ hx => ?_) (ofReal_mem_nbhd hε hp) ht
  simp [Complex.exp_im, im_hatHPrimitive_eq_zero hε hf hp hfp hx]

/-- On `I`, the derivative of `ĝ` is real and positive. -/
theorem deriv_koenigs_ofReal {x : ℝ} (hx : x ∈ I) :
    (deriv (koenigs f p) x).im = 0 ∧ 0 < (deriv (koenigs f p) x).re := by
  have hx' := ofReal_mem_nbhd hε hx
  rw [deriv_koenigs_eq hε hf hp hfp hx', Complex.exp_im, Complex.exp_re,
    im_hatHPrimitive_eq_zero hε hf hp hfp hx']
  simpa using Real.exp_pos (segmentPrimitive (hatH f) p x).re

end

end AnalyticESC
