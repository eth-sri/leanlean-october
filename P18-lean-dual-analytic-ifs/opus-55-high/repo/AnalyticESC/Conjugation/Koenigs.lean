module

public import AnalyticESC.Dual.Projection
public import AnalyticESC.Analysis
public import AnalyticESC.Analysis.Primitive
set_option hygiene false
local notation "𝔞" => subset_closure hw
local notation "𝖄" => Complex.exp_ne_zero _
local notation "𝖃" => IFS.nbhd_subset_two hw
local notation "𝖂" => nbhd ε
local notation "𝖁" => f^[k] z
local notation "𝖏" => ofReal_mem_nbhd hε hp

local notation "𝖎" => convex_nbhd ε

local notation "𝖍" => hatH f

local notation "𝖌" => koenigs f p


@[expose] public section

/-!
# The linearisation of a single map

For a map `f` of the class with fixed point `p ∈ I`, define `Ĥ_f` by (5.1) and
`ĝ(z) = ∫ₚᶻ exp(∫ₚʷ Ĥ_f) dw`, as in Lemma 5.1. Segment integration gives holomorphy on
`B_ε`, the ODE `ĝ'' = Ĥ_f ĝ'`, and positivity of `ĝ'` on `I`. The functional equation
`Ĥ_f = f''/f' + f' · Ĥ_f ∘ f` shows that `ĝ ∘ f = f'(p) ĝ`.
-/

namespace AnalyticESC

variable {t : ℝ} {z : ℂ}



/-- The function `Ĥ_f(z) = ∑_{k ≥ 0} (f''/f')(f^k(z)) · (f^k)'(z)` of (5.1). -/
noncomputable def hatH (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' k, 𝔇 f 𝖁 / deriv f 𝖁 * deriv (f^[k]) z

/-- The ODE solution `ĝ(z) = ∫ₚᶻ exp(∫ₚʷ Ĥ_f) dw` from Lemma 5.1. -/
noncomputable def koenigs (f : ℂ → ℂ) (p z : ℂ) : ℂ :=
  segmentPrimitive (fun w => Complex.exp (segmentPrimitive 𝖍 p w)) p z

/-- The system consisting of the single map `f`. -/
def koenigsIFS (hε : 0 < ε) (hf : InClass ε f) : IFS 1 ε :=
  ⟨fun _ => f, hε, fun _ => hf⟩

theorem koenigs_self f p : koenigs f p p = 0 := segmentPrimitive_self _ _

section

variable {f : ℂ → ℂ} (hε : 0 < ε) (hf : InClass ε f)

include hε hf

/-! ## The function `Ĥ_f` -/

theorem hatH_eq_dualProj : hatH f = (koenigsIFS hε hf).dualProj (.inf fun _ => 0) := by
  have hc n : (koenigsIFS hε hf).comp (List.replicate n 0) = f^[n] := by
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, IFS.comp_cons, ih, Function.iterate_succ']; rfl
  funext z
  refine tsum_congr fun k => ?_
  rw [(koenigsIFS hε hf).dualTerm_of_get?_eq_some (Word.get?_inf _ k)]
  aesop

/-- `Ĥ_f = f''/f' + f' · Ĥ_f ∘ f`: `Ĥ_f` is fixed by the dual operator of `f`. -/
theorem hatH_eq_add (hz : z ∈ nbhd ε) :
    hatH f z = 𝔇 f z / deriv f z + deriv f z * hatH f (f z) := by
  have h := (koenigsIFS hε hf).dualProj_prepend [0] (.inf fun _ => 0) (subset_closure hz)
  rw [show (Word.inf fun _ : ℕ => (0 : Fin 1)).prepend [0] = .inf fun _ => 0 from
    congrArg Word.inf (funext fun _ => Subsingleton.elim _ _), IFS.dualProj_singleton] at h
  rw [hatH_eq_dualProj hε hf, h]
  rfl

theorem differentiableOn_hatH : DifferentiableOn ℂ 𝖍 𝖂 := by
  exact hatH_eq_dualProj hε hf ▸ (koenigsIFS hε hf).differentiableOn_dualProj _

theorem im_hatH_ofReal (ht : (t : ℂ) ∈ nbhd ε) : (hatH f t).im = 0 := by
  exact hatH_eq_dualProj hε hf ▸ (koenigsIFS hε hf).im_dualProj_ofReal _ ht

/-! ## The solution of the ODE -/

variable {p : ℝ} (hp : p ∈ I)

include hp

theorem hasDerivAt_hatHPrimitive (hz : z ∈ nbhd ε) :
    HasDerivAt (segmentPrimitive 𝖍 p) (hatH f z) z :=
  hasDerivAt_segmentPrimitive 𝖎 isOpen_nbhd
    (differentiableOn_hatH hε hf) 𝖏 hz

theorem hasDerivAt_koenigs (hz : z ∈ nbhd ε) :
    HasDerivAt 𝖌 (Complex.exp (segmentPrimitive 𝖍 p z)) z :=
  hasDerivAt_segmentPrimitive 𝖎 isOpen_nbhd
    (fun _ hw => ((hasDerivAt_hatHPrimitive hε hf hp hw).cexp).differentiableAt.differentiableWithinAt)
    𝖏 hz

theorem differentiableOn_koenigs : DifferentiableOn ℂ 𝖌 𝖂 :=
  fun _ hz => (hasDerivAt_koenigs hε hf hp hz).differentiableAt.differentiableWithinAt

theorem deriv_deriv_koenigs (hz : z ∈ nbhd ε) :
    𝔇 𝖌 z = hatH f z * deriv 𝖌 z := by
  rw [(Filter.eventuallyEq_of_mem (isOpen_nbhd.mem_nhds hz) fun w hw =>
    (hasDerivAt_koenigs hε hf hp hw).deriv).deriv_eq,
    ((hasDerivAt_hatHPrimitive hε hf hp hz).cexp).deriv, (hasDerivAt_koenigs hε hf hp hz).deriv]
  ring

/-- `ĝ ∘ f = f'(p) ĝ` on `B_ε`. -/
theorem koenigs_comp (hfp : f p = p) (hz : z ∈ nbhd ε) :
    koenigs f p (f z) = deriv f p * koenigs f p z := by
  have hconst : ∀ {g : ℂ → ℂ}, (∀ w ∈ nbhd ε, HasDerivAt g 0 w) → ∀ w ∈ nbhd ε, g w = g p :=
    fun h w hw => isOpen_nbhd.is_const_of_deriv_eq_zero (isPreconnected_nbhd ε)
      (fun w hw => (h w hw).differentiableAt.differentiableWithinAt) (fun w hw => (h w hw).deriv)
        hw 𝖏
  -- `exp(∫ₚ^{f(w)} Ĥ_f) f'(w) / exp(∫ₚʷ Ĥ_f)` is constant, equal to `f'(p)`
  have h1 := hconst (fun w hw => by
    convert ((((hasDerivAt_hatHPrimitive hε hf hp ((fun w hw => hf.mapsTo 𝔞) w hw)).cexp.comp w ((fun w hw => (hf.differentiableOn.differentiableAt (isOpen_nbhd.mem_nhds 𝖃)).hasDerivAt) w hw)).mul
      ((hf.differentiableOn.deriv isOpen_nbhd w 𝖃).differentiableAt
        (isOpen_nbhd.mem_nhds 𝖃)).hasDerivAt).div
      (hasDerivAt_hatHPrimitive hε hf hp hw).cexp 𝖄) using 1
    have := hf.deriv_ne_zero w 𝔞
    simp
    rw [hatH_eq_add hε hf hw]
    field_simp
    ring)
  have h2 := hconst (fun w hw => by
    convert ((hasDerivAt_koenigs hε hf hp ((fun w hw => hf.mapsTo 𝔞) w hw)).comp w ((fun w hw => (hf.differentiableOn.differentiableAt (isOpen_nbhd.mem_nhds 𝖃)).hasDerivAt) w hw)).sub
      ((hasDerivAt_koenigs hε hf hp hw).const_mul (deriv f p)) using 1
    have := h1 w hw
    simp only [Pi.mul_apply, Pi.div_apply, Function.comp_apply, hfp] at this
    rw [mul_div_cancel_left₀ _ 𝖄, div_eq_iff 𝖄] at this
    rw [this, sub_self]) z hz
  simp at h2
  rw [hfp, koenigs_self, mul_zero, sub_zero, sub_eq_zero] at h2
  exact h2

theorem im_koenigs_ofReal (ht : (t : ℂ) ∈ nbhd ε) : (koenigs f p t).im = 0 := by
  have hp' := ofReal_mem_nbhd hε hp
  have hd : DifferentiableOn ℂ (segmentPrimitive 𝖍 p) 𝖂 :=
    fun z hz => (hasDerivAt_hatHPrimitive hε hf hp hz).differentiableAt.differentiableWithinAt
  apply im_segmentPrimitive_eq_zero 𝖎 hd.continuousOn.cexp _ hp' ht
  intro x hx
  simp [Complex.exp_im, (im_segmentPrimitive_eq_zero 𝖎 (differentiableOn_hatH hε hf).continuousOn (fun x hx => im_hatH_ofReal hε hf hx) hp' hx)]

/-- On `I`, the derivative of `ĝ` is real and positive. -/
theorem deriv_koenigs_ofReal (hx : x ∈ I) :
    (deriv 𝖌 x).im = 0 ∧ 0 < (deriv 𝖌 x).re := by
  have hx' := ofReal_mem_nbhd hε hx
  rw [(hasDerivAt_koenigs hε hf hp hx').deriv, Complex.exp_im, Complex.exp_re, (im_segmentPrimitive_eq_zero 𝖎 (differentiableOn_hatH hε hf).continuousOn (fun t ht => im_hatH_ofReal hε hf ht) 𝖏 hx')]
  bound

end

end AnalyticESC
