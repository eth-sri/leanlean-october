module

public import RequestProject.LocalDirichletBoundaryJets
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Actual inverse derivatives from Green boundary fields

The graph gradient fields here are representatives of actual interior
derivatives.  The inverse boundary ODE is deduced from the original interior
Green derivative formula and the limiting horizontal FTC.  Smoothness of the
inverse trace is a conclusion, not a field hypothesis.  The pole-subtracted
Dirichlet remainder is related to Green with its actual logarithmic correction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory InnerProductSpace
open scoped Topology ContDiff ComplexConjugate InnerProductSpace

def riemannMappingFlattenedGreen (F : ℂ → ℂ) (Ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (riemannMappingGreen F (Ψ z) : ℂ)

def riemannMappingGreenBoundaryCoefficient (f : ℝ → ℝ) (P Q : ℂ → ℂ) (z : ℂ) : ℂ :=
  (-(P z - ((deriv f z.re : ℝ) : ℂ) * Q z) + Complex.I * Q z) *
    (1 + Complex.I * ((deriv f z.re : ℝ) : ℂ))

/-- Pure complex algebra for the two actual logarithmic gradient components. -/
theorem complex_eq_mul_log_gradient (j D : ℂ) (hj : j ≠ 0) :
    D = j * (-(-⟪j, D⟫_ℝ / ‖j‖ ^ 2 : ℝ) +
      Complex.I * (-⟪j, D * Complex.I⟫_ℝ / ‖j‖ ^ 2 : ℝ)) := by
  have hn : j.re * j.re + j.im * j.im ≠ 0 := by
    simp_all [← Complex.normSq_apply]
  have hn₂ : j.re ^ 2 + j.im ^ 2 ≠ 0 := by
    grind
  apply Complex.ext <;>
    simp only [Complex.inner, Complex.sq_norm, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im] <;>
    field_simp  <;> ring

section ActualMap

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)

include hb hS hsc hF hinj himage

variable (p c : ℂ) (hc : c ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {z : ℂ}

theorem riemannMappingGreen_complex_fderiv {w : ℂ}
    (hw : w ∈ Ω) (hne : w ≠ F 0) (v : ℂ) :
    fderiv ℝ (fun z  => (riemannMappingGreen F z : ℂ)) w v =
      (-⟪riemannMappingClosedInverse F w,
        deriv (riemannMappingClosedInverse F) w * v⟫_ℝ /
          ‖riemannMappingClosedInverse F w‖ ^ 2 : ℝ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ riemannMappingGreen F) w v = _
  simp [fderiv_comp w Complex.ofRealCLM.differentiableAt ((riemannMappingGreen_harmonicOnNhd hb hS hsc F hF hinj himage w ⟨hw, hne⟩).1.differentiableAt       (by norm_num)), riemannMappingGreen_fderiv hb hS hsc F hF hinj himage hw hne]

/-- The actual graph gradient reconstructs the interior inverse derivative.
The shear cancellation is applied to the genuine real Green function. -/
theorem riemannMappingClosedInverse_deriv_graph_green
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω)
    (hne : smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     let G := riemannMappingFlattenedGreen F Ψ
     deriv (riemannMappingClosedInverse F) (Ψ z) / c =
       riemannMappingClosedInverse F (Ψ z) *
          (-(dirD G 1 z - deriv f z.re * dirD G Complex.I z) +
           Complex.I * dirD G Complex.I z)) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let J := riemannMappingClosedInverse F
  let G := riemannMappingFlattenedGreen F Ψ
  have hdG : DifferentiableAt ℝ (fun w  => (riemannMappingGreen F w : ℂ)) (Ψ z) :=
    Complex.ofRealCLM.differentiableAt.comp _
      ((riemannMappingGreen_harmonicOnNhd hb hS hsc F hF hinj himage (Ψ z)
        ⟨hz, hne⟩).1.differentiableAt (by norm_num))
  obtain ⟨hX, hY⟩ := smoothDirichletGraphChart_pullback_gradient p c hc hf hdG
  change dirD G 1 z - deriv f z.re * dirD G Complex.I z = _ at hX
  change dirD G Complex.I z = _ at hY
  rw [riemannMappingGreen_complex_fderiv hb hS hsc F hF hinj himage hz hne] at hX hY
  have h1 : deriv J (Ψ z) * (1 / c) = deriv J (Ψ z) / c := by ring
  have hI : deriv J (Ψ z) * (Complex.I / c) =
      (deriv J (Ψ z) / c) * Complex.I := by ring
  rw [h1] at hX
  rw [hI] at hY
  change deriv J (Ψ z) / c = J (Ψ z) * _
  rw [hX, hY]
  exact complex_eq_mul_log_gradient (J (Ψ z)) (deriv J (Ψ z) / c)
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage
      (subset_closure hz) hne)

theorem riemannMappingClosedInverse_graph_dirD_one
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     dirD (riemannMappingClosedInverse F ∘ Ψ) 1 z =
       (deriv (riemannMappingClosedInverse F) (Ψ z) / c) *
          (1 + Complex.I * deriv f z.re)) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let J := riemannMappingClosedInverse F
  have hdJ  :=
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).differentiableAt
      (hS.1.1.mem_nhds hz)
  change fderiv ℝ (J ∘ Ψ) z 1 = _
  rw [fderiv_comp z (hdJ.restrictScalars ℝ)
    (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt,
    hdJ.fderiv_restrictScalars ℝ]
  change fderiv ℂ J (Ψ z) (fderiv ℝ Ψ z 1) = _
  rw [fderiv_eq_deriv_mul, smoothDirichletGraphChart_fderiv_apply p c hc hf z 1]
  simp only [Complex.one_re, mul_one, Complex.real_smul]
  ring

theorem riemannMappingClosedInverse_graph_dirD_one_of_green_fields
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω)
    (hne : smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0)
    {P Q : ℂ → ℂ}
    (hP : P z = dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) 1 z)
    (hQ : Q z = dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) Complex.I z) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     dirD (riemannMappingClosedInverse F ∘ Ψ) 1 z =
        riemannMappingClosedInverse F (Ψ z) * riemannMappingGreenBoundaryCoefficient f P Q z) := by
  dsimp only
  rw [riemannMappingClosedInverse_graph_dirD_one hb hS hsc F hF hinj himage p c hc hf hz,
    riemannMappingClosedInverse_deriv_graph_green hb hS hsc F hF hinj himage p c hc hf hz hne]
  rw [← hP, ← hQ]
  unfold riemannMappingGreenBoundaryCoefficient
  ring

/-- True physical directions recovered from the two graph derivatives.
This real-linear identity is also valid along the actual inward ray. -/
theorem riemannMappingGreen_graph_fderiv_apply
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω)
    (hne : smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0) (v : ℂ) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     let G := riemannMappingFlattenedGreen F Ψ
     fderiv ℝ (fun w  => (riemannMappingGreen F w : ℂ)) (Ψ z) v =
       (c * v).re * dirD G 1 z +
          ((c * v).im - deriv f z.re * (c * v).re : ℝ) * dirD G Complex.I z) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let G := riemannMappingFlattenedGreen F Ψ
  let T := fderiv ℝ (fun w  => (riemannMappingGreen F w : ℂ)) (Ψ z)
  obtain ⟨hX, hY⟩ := smoothDirichletGraphChart_pullback_gradient p c hc hf (Complex.ofRealCLM.differentiableAt.comp _
      ((riemannMappingGreen_harmonicOnNhd hb hS hsc F hF hinj himage (Ψ z)
        ⟨hz, hne⟩).1.differentiableAt (by norm_num)))
  change dirD G 1 z - deriv f z.re * dirD G Complex.I z = T (1 / c) at hX
  change dirD G Complex.I z = T (Complex.I / c) at hY
  calc
    T v = T ((c * v).re • (1 / c) + (c * v).im • (Complex.I / c)) :=
      congrArg T (by
    calc
      v = (c * v) / c := (mul_div_cancel_left₀ v hc).symm
      _ = ((c * v).re + (c * v).im * Complex.I) / c := by
        rw [Complex.re_add_im]
      _ = _ := by simp ; ring)
    _ = (c * v).re * (dirD G 1 z - deriv f z.re * dirD G Complex.I z) +
        (c * v).im * dirD G Complex.I z := by
      rw [map_add, map_smul, map_smul, ← hX, ← hY, Complex.real_smul, Complex.real_smul]
    _ = _ := by
      push_cast
      ring

end ActualMap

/-- A continuous inverse trace satisfying the deduced derivative ODE is
smooth at the center once its actual coefficient is smooth there. -/
theorem contDiffAt_of_eventually_hasDerivAt_mul {α B : ℝ → ℂ} {x₀ : ℝ}
    (hB : ContDiffAt ℝ (⊤ : ℕ∞) B x₀)
    (hd : ∀ᶠ x in 𝓝 x₀, HasDerivAt α (α x * B x) x) :
    ContDiffAt ℝ (⊤ : ℕ∞) α x₀ := by
  apply contDiffAt_infty.mpr
  intro n
  induction n with
  | zero =>
      apply contDiffAt_zero.mpr
      refine ⟨{x | HasDerivAt α (α x * B x) x}, hd, ?_⟩
      intro x hx
      exact hx.continuousAt.continuousWithinAt
  | succ n ih =>
      apply contDiffAt_succ_iff_hasFDerivAt.mpr
      refine ⟨fun x => ContinuousLinearMap.toSpanSingleton ℝ (α x * B x), ?_, ?_⟩
      · exact ⟨{x | HasDerivAt α (α x * B x) x}, hd,
          fun x hx => hx.hasFDerivAt⟩
      · exact ContinuousLinearMap.toSpanSingletonCLE.contDiff.contDiffAt.comp x₀ (ih.mul (hB.of_le (WithTop.coe_le_coe.mpr le_top)))

theorem riemannMappingGreenBoundaryCoefficient_continuousOn {a b : ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {P Q : ℂ → ℂ}
    (hP : ContinuousOn P (smoothDirichletClosedHalfBox a b))
    (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b)) :
    ContinuousOn (riemannMappingGreenBoundaryCoefficient f P Q)
      (smoothDirichletClosedHalfBox a b) := by
  have hd  :=
    Complex.continuous_ofReal.comp
      ((contDiff_infty_iff_deriv.mp hf).2.continuous.comp Complex.continuous_re)
  exact ((hP.sub (hd.continuousOn.mul hQ)).neg.add
    (continuousOn_const.mul hQ)).mul
      (continuousOn_const.add (continuousOn_const.mul hd.continuousOn))

theorem riemannMappingGreenBoundaryCoefficient_bottom_contDiffAt
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {P Q : ℂ → ℂ}
    (hP : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => P x) 0)
    (hQ : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Q x) 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : ℝ => riemannMappingGreenBoundaryCoefficient f P Q x) 0 := by
  have hd : ContDiffAt ℝ (⊤ : ℕ∞) (fun x  => ((deriv f x : ℝ) : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0
      (contDiff_infty_iff_deriv.mp hf).2.contDiffAt
  simpa only [riemannMappingGreenBoundaryCoefficient, Complex.ofReal_re] using
    ((hP.sub (hd.mul hQ)).neg.add (contDiffAt_const.mul hQ)).mul
      (contDiffAt_const.add (contDiffAt_const.mul hd))

section BoundaryTransfer

variable {Ω : Set ℂ} (hbΩ : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    (p c : ℂ) (hc : c ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {a b : ℝ}

include hbΩ hS hsc hF hinj himage

theorem riemannMappingBoundaryTrace_horizontal_hasDerivAt
    (hmap : MapsTo (smoothDirichletGraphChart p c hc f hf.continuous)
      (smoothDirichletHalfBox a b) Ω)
    (hpole : ∀ z ∈ smoothDirichletHalfBox a b,
      smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0)
    {P Q : ℂ → ℂ}
    (hP : EqOn P (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) 1)
      (smoothDirichletHalfBox a b))
    (hQ : EqOn Q (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) Complex.I)
      (smoothDirichletHalfBox a b))
    {x y : ℝ} (hx : x ∈ Ioo (-a) a) (hy : y ∈ Ioo 0 b) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     let z := rectangularComplexCoord (x, y)
     HasDerivAt (fun s  => riemannMappingClosedInverse F
       (Ψ (rectangularComplexCoord (s, y))))
       (riemannMappingClosedInverse F (Ψ z) * riemannMappingGreenBoundaryCoefficient f P Q z) x) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let J := riemannMappingClosedInverse F
  let z := rectangularComplexCoord (x, y)
  have hz : z ∈ smoothDirichletHalfBox a b :=
    rectangularComplexCoord_mem_halfBox ⟨hx, hy⟩
  have hrow := ((((riemannMappingClosedInverse_differentiableOn hbΩ hS hsc F hF hinj himage).differentiableAt
      (hS.1.1.mem_nhds (hmap hz))).restrictScalars ℝ).comp z
      (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt).hasFDerivAt.comp_hasDerivAt x
    ((Complex.ofRealCLM.hasDerivAt ).add_const (y * Complex.I))
  change HasDerivAt (fun s  => J (Ψ (rectangularComplexCoord (s, y))))
    (dirD (J ∘ Ψ) 1 z) x at hrow
  rwa [riemannMappingClosedInverse_graph_dirD_one_of_green_fields
    hbΩ hS hsc F hF hinj himage p c hc hf (hmap hz) (hpole z hz) (hP hz) (hQ hz)] at hrow

/-- The actual interior derivative formula passes to the bottom by the
proved FTC for continuous fields, rather than by an assumed trace derivative. -/
theorem riemannMappingBoundaryTrace_hasDerivAt_of_green_fields
    (ha : 0 < a) (hb : 0 < b)
    (hmap : MapsTo (smoothDirichletGraphChart p c hc f hf.continuous)
      (smoothDirichletHalfBox a b) Ω)
    (hpole : ∀ z ∈ smoothDirichletHalfBox a b,
      smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0)
    (hJ : ContinuousOn (riemannMappingClosedInverse F ∘
      smoothDirichletGraphChart p c hc f hf.continuous) (smoothDirichletClosedHalfBox a b))
    {P Q : ℂ → ℂ}
    (hPc : ContinuousOn P (smoothDirichletClosedHalfBox a b))
    (hQc : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hP : EqOn P (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) 1)
      (smoothDirichletHalfBox a b))
    (hQ : EqOn Q (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) Complex.I)
      (smoothDirichletHalfBox a b))
    {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     HasDerivAt (fun s : ℝ => riemannMappingClosedInverse F (Ψ s))
       (riemannMappingClosedInverse F (Ψ x) *
         riemannMappingGreenBoundaryCoefficient f P Q x) x) := by
  apply dirichlet_boundary_horizontal_hasDerivAt ha hb hJ
    (hJ.mul (riemannMappingGreenBoundaryCoefficient_continuousOn hf hPc hQc)) _ hx
  intro s hs y hy
  exact riemannMappingBoundaryTrace_horizontal_hasDerivAt hbΩ hS hsc F hF hinj himage
    p c hc hf hmap hpole hP hQ hs hy

theorem riemannMappingBoundaryTrace_contDiffAt_of_green_fields
    (ha : 0 < a) (hb : 0 < b)
    (hmap : MapsTo (smoothDirichletGraphChart p c hc f hf.continuous)
      (smoothDirichletHalfBox a b) Ω)
    (hpole : ∀ z ∈ smoothDirichletHalfBox a b,
      smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0)
    (hJ : ContinuousOn (riemannMappingClosedInverse F ∘
      smoothDirichletGraphChart p c hc f hf.continuous) (smoothDirichletClosedHalfBox a b))
    {P Q : ℂ → ℂ}
    (hPc : ContinuousOn P (smoothDirichletClosedHalfBox a b))
    (hQc : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hP : EqOn P (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) 1)
      (smoothDirichletHalfBox a b))
    (hQ : EqOn Q (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) Complex.I)
      (smoothDirichletHalfBox a b))
    (hPs : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => P x) 0)
    (hQs : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Q x) 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : ℝ => riemannMappingClosedInverse F
        (smoothDirichletGraphChart p c hc f hf.continuous x)) 0 := by
  have hx₀ : 0 ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  apply contDiffAt_of_eventually_hasDerivAt_mul
    (riemannMappingGreenBoundaryCoefficient_bottom_contDiffAt hf hPs hQs)
  filter_upwards [isOpen_Ioo.mem_nhds hx₀] with x hx
  exact riemannMappingBoundaryTrace_hasDerivAt_of_green_fields hbΩ hS hsc F hF hinj himage
    p c hc hf ha hb hmap hpole hJ hPc hQc hP hQ hx

end BoundaryTransfer

/-- The smooth datum needed for Green is the Dirichlet datum minus
the logarithmic pole term, with its genuine sign. -/
def riemannMappingGreenLogDatum (F : ℂ → ℂ) (d : smoothTraceTests)
    (Ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  d (Ψ z) - (((1 / 2 : ℝ) * Real.log (‖Ψ z - F 0‖ ^ 2) : ℝ) : ℂ)

theorem riemannMappingGreenLogDatum_contDiffAt
    (F : ℂ → ℂ) (d : smoothTraceTests) {Ψ : ℂ → ℂ} {z : ℂ}
    (hΨ : ContDiffAt ℝ (⊤ : ℕ∞) Ψ z) (hne : Ψ z ≠ F 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (riemannMappingGreenLogDatum F d Ψ) z := (d.property.1.contDiffAt.comp z hΨ).sub
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_const.mul (((hΨ.sub contDiffAt_const).norm_sq ℂ).log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))))))

theorem contDiffAt_infty_dirD {φ : ℂ → ℂ} {z : ℂ}
    (hφ : ContDiffAt ℝ (⊤ : ℕ∞) φ z) (v : ℂ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (dirD φ v) z :=
  (hφ.fderiv_right  le_rfl).clm_apply contDiffAt_const

theorem riemannMappingFlattenedGreen_eq_remainder_add_datum {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    (d : smoothTraceTests) (Ψ : ℂ → ℂ) {z : ℂ}
    (hz : Ψ z ∈ closure Ω) (hne : Ψ z ≠ F 0) :
    riemannMappingFlattenedGreen F Ψ z =
      riemannMappingDirichletRemainder F d (Ψ z) + riemannMappingGreenLogDatum F d Ψ z := by
  simp [riemannMappingFlattenedGreen, riemannMappingDirichletRemainder, riemannMappingGreenLogDatum, riemannMappingGreenCorrection_eq hb hS hsc F hF hinj himage hz hne]

theorem riemannMappingGraph_origin (p c : ℂ) (hc : c ≠ 0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf₀ : f 0 = 0) :
    smoothDirichletGraphChart p c hc f hf.continuous 0 = p := by
  simp [smoothDirichletGraphShear, hf₀]

section NonzeroBoundaryTransfer

variable {Ω : Set ℂ} (hbΩ : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    (p c : ℂ) (hc : c ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf₀ : f 0 = 0) (hp : p ∈ frontier Ω) {a b : ℝ}

include hbΩ hS hsc hF hinj himage hf₀ hp

/-- The Green lower bound is applied on its proved physical inward ray.
The genuine graph membership equivalence locates that ray in the same
upper halfbox. If both graph gradients vanished, the ray derivative
would tend to zero, contradicting the strictly positive Green slope. -/
theorem riemannMappingGreen_graph_vertical_field_ne_zero
    (ha : 0 < a) (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im))
    {P Q : ℂ → ℂ}
    (hPc : ContinuousOn P (smoothDirichletClosedHalfBox a b))
    (hQc : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hP : EqOn P (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) 1)
      (smoothDirichletHalfBox a b))
    (hQ : EqOn Q (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) Complex.I)
      (smoothDirichletHalfBox a b))
    (hP₀ : P 0 = 0) : Q 0 ≠ 0 := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  have hpin  := frontier_subset_closure hp
  have hpne : p ≠ F 0 := by
    intro he
    rw [he, hS.1.1.frontier_eq] at hp
    exact hp.2 (riemannMapping_pole_mem F himage)
  obtain ⟨v, δ, A, _, hδ, hA, hray⟩ :=
    exists_riemannMappingGreen_inward_ray_lower hbΩ hS hsc F hF hinj himage hp
  let w : ℝ → ℂ := fun t => p + t * v
  let ζ  := fun t => Ψ.symm (w t)
  let R : ℝ → ℂ := fun t => riemannMappingGreen F (w t)
  have hw : Continuous w := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hw₀ : w 0 = p := by simp [w]
  have hζ₀ : ζ 0 = 0 := by
    change Ψ.symm (w 0) = 0
    rw [hw₀, ← riemannMappingGraph_origin p c hc hf hf₀, Ψ.symm_apply_apply]
  have hζlim : Tendsto ζ (𝓝[>] 0) (𝓝 0) := by
    have hh : Tendsto ζ (𝓝[>] 0) (𝓝 (ζ 0)) :=
      (Ψ.symm.continuous.comp hw).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simp_all
  have hrelim : Tendsto (fun t  => |(ζ t).re|) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Complex.zero_re, abs_zero, Function.comp_def] using
      continuous_abs.continuousAt.tendsto.comp
        (Complex.continuous_re.continuousAt.tendsto.comp hζlim)
  have himlim : Tendsto (fun t  => |(ζ t).im|) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Complex.zero_im, abs_zero, Function.comp_def] using
      continuous_abs.continuousAt.tendsto.comp
        (Complex.continuous_im.continuousAt.tendsto.comp hζlim)
  have hζbox : ∀ᶠ t in 𝓝[>] 0, ζ t ∈ smoothDirichletHalfBox a b := by
    filter_upwards [self_mem_nhdsWithin, hrelim.eventually_lt_const ha,
      himlim.eventually_lt_const hb,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htr hti htδ
    have hwt  := (hray t ht htδ).1
    exact ⟨htr, (hchart (ζ t) htr hti).mp (by
      rw [Ψ.apply_symm_apply (w t)]
      assumption), lt_of_le_of_lt (le_abs_self _) hti⟩
  have hzclosed : ∀ᶠ t in 𝓝[>] 0, ζ t ∈ smoothDirichletClosedHalfBox a b :=
    hζbox.mono fun t ht => ⟨ht.1.le, ht.2.1.le, ht.2.2.le⟩
  have hz₀ : 0 ∈ smoothDirichletClosedHalfBox a b := ⟨by simpa using ha.le, by simp, by positivity⟩
  have hζwithin := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    ζ hζlim hzclosed
  have hpLim  :=
    (hPc 0 hz₀).tendsto.comp hζwithin
  have hcoef : Continuous (fun z : ℂ =>
      (((c * v).im - deriv f z.re * (c * v).re : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_const.sub (((contDiff_infty_iff_deriv.mp hf).2.continuous.comp Complex.continuous_re).mul continuous_const))
  have hder : ∀ᶠ t in 𝓝[>] 0,
      HasDerivAt R ((c * v).re * P (ζ t) +
        ((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) * Q (ζ t)) t := by
    filter_upwards [hζbox, self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t hzt ht htδ
    obtain ⟨hwt, hwne, _⟩ := hray t ht htδ
    have hdG : DifferentiableAt ℝ (fun z  => (riemannMappingGreen F z : ℂ)) (w t) :=
      Complex.ofRealCLM.differentiableAt.comp _
        ((riemannMappingGreen_harmonicOnNhd hbΩ hS hsc F hF hinj himage (w t)
          ⟨hwt, hwne⟩).1.differentiableAt (by norm_num))
    have hdR := hdG.hasFDerivAt.comp_hasDerivAt t (by
      have hcast : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
        simpa only [id, Complex.ofReal_one] using (hasDerivAt_id t).ofReal_comp
      simpa only [one_mul] using (hcast.mul_const v).const_add p)
    have he  := Ψ.apply_symm_apply (w t)
    have hfd := riemannMappingGreen_graph_fderiv_apply hbΩ hS hsc F hF hinj himage
      p c hc hf  (by
        rw [he]
        assumption) (by
        grind) v
    change fderiv ℝ (fun z  => (riemannMappingGreen F z : ℂ)) (Ψ (ζ t)) v =
      (c * v).re * dirD (riemannMappingFlattenedGreen F Ψ) 1 (ζ t) +
        ((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) *
          dirD (riemannMappingFlattenedGreen F Ψ) Complex.I (ζ t) at hfd
    rw [he, ← hP hzt, ← hQ hzt] at hfd
    rwa [hfd] at hdR
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hder
  have hdiff : DifferentiableOn ℝ R (Ioo 0 ε) :=
    fun t ht => (hsub ht).differentiableAt.differentiableWithinAt
  have hRlim : Tendsto R (𝓝[>] 0) (𝓝 (R 0)) := by
    simpa only [R, hw₀, Function.comp_def] using (Complex.continuous_ofReal.comp_continuousOn
    (riemannMappingGreen_continuousOn hbΩ hS hsc F hF hinj himage) p ⟨hpin, hpne⟩).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within w (by
    have hh : Tendsto w (𝓝[>] 0) (𝓝 (w 0)) :=
      hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simp_all) (by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
    exact ⟨subset_closure (hray t ht htδ).1, (hray t ht htδ).2.1⟩))
  intro hQ₀
  have hR₀ : R 0 = 0 := by
    simp [R, hw₀, riemannMappingGreen_frontier hbΩ hS hsc F hF hinj himage hp]
  have hlower : ∀ᶠ t in 𝓝[>] 0, A ≤ (slope R 0 t).re := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
    simp only [slope_def_module, hR₀, sub_zero, Complex.smul_re, smul_eq_mul,
      R, Complex.ofReal_re]
    simpa only [w, div_eq_mul_inv, mul_comm] using (le_div_iff₀ ht).mpr (hray t ht htδ).2.2
  exact (not_le_of_gt hA) (ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp ((hasDerivWithinAt_iff_tendsto_slope'
    (by simp)).mp ((hasDerivWithinAt_Ici_of_tendsto_deriv hdiff (hRlim.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self))
    (Ioo_mem_nhdsGT hε) (by
    have hcoeflim : Tendsto (fun t  =>
        (((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 ((c * v).im - deriv f 0 * (c * v).re : ℝ)) := by
      simpa only [Complex.zero_re, Function.comp_def] using hcoef.continuousAt.tendsto.comp hζlim
    have hh : Tendsto (fun t  => (c * v).re * P (ζ t) +
        ((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) * Q (ζ t))
        (𝓝[>] 0)
        (𝓝 ((c * v).re * P 0 +
          ((c * v).im - deriv f 0 * (c * v).re : ℝ) * Q 0)) :=
      (tendsto_const_nhds.mul hpLim).add (hcoeflim.mul ((hQc 0 hz₀).tendsto.comp hζwithin))
    rw [hP₀, hQ₀, mul_zero, mul_zero, add_zero] at hh
    exact hh.congr' (hder.mono fun t ht => ht.deriv.symm))).mono Ioi_subset_Ici_self))) hlower)

/-- The zero Green boundary value forces its actual horizontal field to
vanish. The physical inward-ray estimate then gives a nonzero inverse
boundary derivative. Neither boundary smoothness nor a Hopf derivative
value occurs as a hypothesis. -/
theorem riemannMappingBoundaryTrace_deriv_ne_zero_of_green_fields
    (ha : 0 < a) (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im))
    (hmap : MapsTo (smoothDirichletGraphChart p c hc f hf.continuous)
      (smoothDirichletHalfBox a b) Ω)
    (hpole : ∀ z ∈ smoothDirichletHalfBox a b,
      smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0)
    (hJ : ContinuousOn (riemannMappingClosedInverse F ∘
      smoothDirichletGraphChart p c hc f hf.continuous) (smoothDirichletClosedHalfBox a b))
    (hGc : ContinuousOn (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) (smoothDirichletClosedHalfBox a b))
    (hGs : ContDiffOn ℝ (⊤ : ℕ∞) (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) (smoothDirichletHalfBox a b))
    {P Q : ℂ → ℂ}
    (hPc : ContinuousOn P (smoothDirichletClosedHalfBox a b))
    (hQc : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hP : EqOn P (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) 1)
      (smoothDirichletHalfBox a b))
    (hQ : EqOn Q (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) Complex.I)
      (smoothDirichletHalfBox a b)) :
    deriv (fun x : ℝ => riemannMappingClosedInverse F
      (smoothDirichletGraphChart p c hc f hf.continuous x)) 0 ≠ 0 := by
  have hz : 0 ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hP₀ : P 0 = 0 := by
    simpa only [Complex.ofReal_zero] using
      dirichlet_zero_boundary_horizontal_extension ha hb hGs hGc (by
    intro x hx
    simp only [riemannMappingFlattenedGreen,
      riemannMappingGreen_frontier hbΩ hS hsc F hF hinj himage (smoothDirichletGraphChart_mem_frontier hS.1.1 p c hc f hf.continuous
      hb hchart (abs_lt.mpr hx)), Complex.ofReal_zero]) hPc hP hz
  have hQ₀ := riemannMappingGreen_graph_vertical_field_ne_zero hbΩ hS hsc F hF hinj himage
    p c hc hf hf₀ hp ha hb hchart hPc hQc hP hQ hP₀
  have hj : riemannMappingClosedInverse F
      (smoothDirichletGraphChart p c hc f hf.continuous 0) ≠ 0 := by
    rw [riemannMappingGraph_origin p c hc hf hf₀]
    exact norm_ne_zero_iff.mp (by
      simp [riemannMappingClosedInverse_norm_frontier hbΩ hS hsc F hF hinj himage hp])
  have hleft : deriv f 0 + Complex.I ≠ 0 := by
    intro he
    exact one_ne_zero (by simpa only [Complex.add_im, Complex.ofReal_im, Complex.I_im,
      Complex.zero_im, zero_add] using congrArg Complex.im he)
  have hright : 1 + Complex.I * deriv f 0 ≠ 0 := by
    intro he
    exact one_ne_zero (by simpa only [Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im,
      Complex.zero_re, zero_mul, mul_zero, sub_zero, add_zero] using congrArg Complex.re he)
  have hB : riemannMappingGreenBoundaryCoefficient f P Q 0 =
      Q 0 * (deriv f 0 + Complex.I) * (1 + Complex.I * deriv f 0) := by
    simp only [riemannMappingGreenBoundaryCoefficient, Complex.zero_re, hP₀]
    ring
  rw [(riemannMappingBoundaryTrace_hasDerivAt_of_green_fields hbΩ hS hsc F hF hinj himage
    p c hc hf ha hb hmap hpole hJ hPc hQc hP hQ hz).deriv, Complex.ofReal_zero, hB]
  positivity

end NonzeroBoundaryTransfer

end PolyaNeumann

end
