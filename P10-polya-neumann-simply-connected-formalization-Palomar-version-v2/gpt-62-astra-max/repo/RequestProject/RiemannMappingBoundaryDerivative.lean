module

public import RequestProject.LocalDirichletBoundaryJets
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import RequestProject.PlanarNotation

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

def riemannMappingFlattenedGreen (F Ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (riemannMappingGreen F (Ψ z) : ℂ)

def riemannMappingGreenBoundaryCoefficient (f : ℝ → ℝ) (P Q : ℂ → ℂ) (z : ℂ) : ℂ :=
  (-(P z - ((deriv f z.re : ℝ) : ℂ) * Q z) + Complex.I * Q z) *
    (1 + Complex.I * ((deriv f z.re : ℝ) : ℂ))

/-- Pure complex algebra for the two actual logarithmic gradient components. -/
theorem complex_eq_mul_log_gradient (j D : ℂ) (hj : j ≠ 0) :
    D = j * (-((-⟪j, D⟫_ℝ / ‖j‖ ^ 2 : ℝ) : ℂ) +
      Complex.I * ((-⟪j, D * Complex.I⟫_ℝ / ‖j‖ ^ 2 : ℝ) : ℂ)) := by
  have hn : j.re * j.re + j.im * j.im ≠ 0 := by
    simpa only [← Complex.normSq_apply, Complex.normSq_eq_norm_sq] using
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hj)
  have hn₂ : j.re ^ 2 + j.im ^ 2 ≠ 0 := by
    simpa only [pow_two] using hn
  apply Complex.ext <;>
    simp only [Complex.inner, Complex.sq_norm, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, mul_one, one_mul, add_zero, zero_add, sub_zero] <;>
    field_simp [hn, hn₂] <;> ring

section ActualMap

variable {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : SmoothUniformization Ω F)

include hΦ

theorem riemannMappingGreen_complex_fderiv {w : ℂ}
    (hw : w ∈ Ω) (hne : w ≠ F 0) (v : ℂ) :
    fderiv ℝ (fun z : ℂ => (riemannMappingGreen F z : ℂ)) w v =
      ((-⟪riemannMappingClosedInverse F w,
        deriv (riemannMappingClosedInverse F) w * v⟫_ℝ /
          ‖riemannMappingClosedInverse F w‖ ^ 2 : ℝ) : ℂ) := by
  have hd  :=
    (riemannMappingGreen_harmonicOnNhd hΦ w ⟨hw, hne⟩).1.differentiableAt
      (by norm_num)
  change fderiv ℝ (Complex.ofRealCLM ∘ riemannMappingGreen F) w v = _
  rw [fderiv_comp w Complex.ofRealCLM.differentiableAt hd,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    riemannMappingGreen_fderiv hΦ hw hne]

section

variable (p c : ℂ) (hc : c ≠ 0)

/-- The actual graph gradient reconstructs the interior inverse derivative.
The shear cancellation is applied to the genuine real Green function. -/
theorem riemannMappingClosedInverse_deriv_graph_green {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {z : ℂ}
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω)
    (hne : smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     let G := riemannMappingFlattenedGreen F Ψ
     deriv (riemannMappingClosedInverse F) (Ψ z) / c =
       riemannMappingClosedInverse F (Ψ z) *
          (-(dirD G 1 z - ((deriv f z.re : ℝ) : ℂ) * dirD G Complex.I z) +
           Complex.I * dirD G Complex.I z)) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let J := riemannMappingClosedInverse F
  let G := riemannMappingFlattenedGreen F Ψ
  have hdG : DifferentiableAt ℝ (fun w : ℂ => (riemannMappingGreen F w : ℂ)) (Ψ z) :=
    Complex.ofRealCLM.differentiableAt.comp _
      ((riemannMappingGreen_harmonicOnNhd hΦ (Ψ z)
        ⟨hz, hne⟩).1.differentiableAt (by norm_num))
  obtain ⟨hX, hY⟩ := smoothDirichletGraphChart_pullback_gradient p c hc hf hdG
  change dirD G 1 z - ((deriv f z.re : ℝ) : ℂ) * dirD G Complex.I z = _ at hX
  change dirD G Complex.I z = _ at hY
  rw [riemannMappingGreen_complex_fderiv hΦ hz hne] at hX hY
  have h1 : deriv J (Ψ z) * (1 / c) = deriv J (Ψ z) / c := by ring
  have hI : deriv J (Ψ z) * (Complex.I / c) =
      (deriv J (Ψ z) / c) * Complex.I := by ring
  rw [h1] at hX
  rw [hI] at hY
  change deriv J (Ψ z) / c = J (Ψ z) * _
  rw [hX, hY]
  exact complex_eq_mul_log_gradient (J (Ψ z)) (deriv J (Ψ z) / c)
    (riemannMappingClosedInverse_nonzero hΦ
      (subset_closure hz) hne)

theorem riemannMappingClosedInverse_graph_dirD_one {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {z : ℂ}
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     dirD (riemannMappingClosedInverse F ∘ Ψ) 1 z =
       (deriv (riemannMappingClosedInverse F) (Ψ z) / c) *
          (1 + Complex.I * ((deriv f z.re : ℝ) : ℂ))) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let J := riemannMappingClosedInverse F
  have hdJ  :=
    (riemannMappingClosedInverse_differentiableOn hΦ).differentiableAt
      (hΦ.smooth.1.1.mem_nhds hz)
  change fderiv ℝ (J ∘ Ψ) z 1 = _
  rw [fderiv_comp z (hdJ.restrictScalars ℝ)
    (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt,
    ContinuousLinearMap.comp_apply, hdJ.fderiv_restrictScalars ℝ]
  change fderiv ℂ J (Ψ z) (fderiv ℝ Ψ z 1) = _
  rw [fderiv_eq_deriv_mul, smoothDirichletGraphChart_fderiv_apply p c hc hf z 1]
  simp only [Complex.one_re, mul_one, Complex.real_smul, div_eq_mul_inv]
  ring

theorem riemannMappingClosedInverse_graph_dirD_one_of_green_fields {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {z : ℂ}
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
  rw [riemannMappingClosedInverse_graph_dirD_one hΦ p c hc hf hz,
    riemannMappingClosedInverse_deriv_graph_green hΦ p c hc hf hz hne]
  rw [← hP, ← hQ]
  unfold riemannMappingGreenBoundaryCoefficient
  ring

/-- True physical directions recovered from the two graph derivatives.
This real-linear identity is also valid along the actual inward ray. -/
theorem riemannMappingGreen_graph_fderiv_apply {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {z : ℂ}
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω)
    (hne : smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0) (v : ℂ) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     let G := riemannMappingFlattenedGreen F Ψ
     fderiv ℝ (fun w : ℂ => (riemannMappingGreen F w : ℂ)) (Ψ z) v =
       ((c * v).re : ℂ) * dirD G 1 z +
          (((c * v).im - deriv f z.re * (c * v).re : ℝ) : ℂ) * dirD G Complex.I z) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let G := riemannMappingFlattenedGreen F Ψ
  let T := fderiv ℝ (fun w : ℂ => (riemannMappingGreen F w : ℂ)) (Ψ z)
  have hd  :=
    Complex.ofRealCLM.differentiableAt.comp _
      ((riemannMappingGreen_harmonicOnNhd hΦ (Ψ z)
        ⟨hz, hne⟩).1.differentiableAt (by norm_num))
  obtain ⟨hX, hY⟩ := smoothDirichletGraphChart_pullback_gradient p c hc hf hd
  change dirD G 1 z - ((deriv f z.re : ℝ) : ℂ) * dirD G Complex.I z = T (1 / c) at hX
  change dirD G Complex.I z = T (Complex.I / c) at hY
  have he : v = (c * v).re • (1 / c : ℂ) + (c * v).im • (Complex.I / c) := calc
      v = _ := (mul_div_cancel_left₀ v hc).symm
      _ = ((c * v).re + (c * v).im * Complex.I) / c := by
        rw [Complex.re_add_im]
      _ = _ := by simp only [Complex.real_smul, div_eq_mul_inv]; ring
  
  calc
    _ = _ :=
      congrArg T he
    _ = (c * v).re * (dirD G 1 z - ((deriv f z.re : ℝ) : ℂ) * dirD G Complex.I z) +
        (c * v).im * dirD G Complex.I z := by
      rw [map_add, map_smul, map_smul, ← hX, ← hY, Complex.real_smul, Complex.real_smul]
    _ = _ := by
      push_cast
      ring

end

end ActualMap

/-- A continuous inverse trace satisfying the deduced derivative ODE is
smooth at the center once its actual coefficient is smooth there. -/
theorem contDiffAt_of_eventually_hasDerivAt_mul {α B : ℝ → ℂ} {x₀ : ℝ}
    (hB : ContDiffAt ℝ ∞ B x₀)
    (hd : ∀ᶠ x in 𝓝 x₀, HasDerivAt α (α x * B x) x) :
    ContDiffAt ℝ ∞ α x₀ := by
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
      · have hprod  :=
          ih.mul (hB.of_le ((by simp)))
        exact (ContinuousLinearMap.toSpanSingletonCLE : ℂ ≃L[ℝ] (ℝ →L[ℝ] ℂ)).contDiff.contDiffAt.comp x₀ hprod

theorem riemannMappingGreenBoundaryCoefficient_continuousOn {a b : ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {P Q : ℂ → ℂ}
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
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {P Q : ℂ → ℂ}
    (hP : ContDiffAt ℝ ∞ (fun x : ℝ => P (x : ℂ)) 0)
    (hQ : ContDiffAt ℝ ∞ (fun x : ℝ => Q (x : ℂ)) 0) :
    ContDiffAt ℝ ∞
      (fun x : ℝ => riemannMappingGreenBoundaryCoefficient f P Q (x : ℂ)) 0 := by
  have hd  :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0
      (contDiff_infty_iff_deriv.mp hf).2.contDiffAt
  exact ((hP.sub (hd.mul hQ)).neg.add (contDiffAt_const.mul hQ)).mul
      (contDiffAt_const.add (contDiffAt_const.mul hd))

section BoundaryTransfer

variable {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : SmoothUniformization Ω F)
    (p c : ℂ) (hc : c ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ}

include hΦ

section

variable (ha : 0 < a) (hb : 0 < b)
    (hmap : MapsTo (smoothDirichletGraphChart p c hc f hf.continuous) (smoothDirichletHalfBox a b) Ω)
    (hpole : ∀ z ∈ smoothDirichletHalfBox a b, smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0)
    (hJ : ContinuousOn (riemannMappingClosedInverse F ∘ smoothDirichletGraphChart p c hc f hf.continuous) (smoothDirichletClosedHalfBox a b))
include hmap hpole

theorem riemannMappingBoundaryTrace_horizontal_hasDerivAt
    {P Q : ℂ → ℂ}
    (hP : EqOn P (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) 1)
      (smoothDirichletHalfBox a b))
    (hQ : EqOn Q (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) Complex.I)
      (smoothDirichletHalfBox a b))
    {x y : ℝ} (hx : x ∈ Ioo (-a) a) (hy : y ∈ Ioo (0 : ℝ) b) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     let z := rectangularComplexCoord (x, y)
     HasDerivAt (fun s : ℝ => riemannMappingClosedInverse F
       (Ψ (rectangularComplexCoord (s, y))))
       (riemannMappingClosedInverse F (Ψ z) * riemannMappingGreenBoundaryCoefficient f P Q z) x) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let J := riemannMappingClosedInverse F
  let z := rectangularComplexCoord (x, y)
  have hz : z ∈ smoothDirichletHalfBox a b :=
    rectangularComplexCoord_mem_halfBox ⟨hx, hy⟩
  have hdJ  :=
    (riemannMappingClosedInverse_differentiableOn hΦ).differentiableAt
      (hΦ.smooth.1.1.mem_nhds (hmap hz))
  have hdcomp  :=
    (hdJ.restrictScalars ℝ).comp z
      (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt
  have hrow := hdcomp.hasFDerivAt.comp_hasDerivAt x
    ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * Complex.I))
  change HasDerivAt (fun s : ℝ => J (Ψ (rectangularComplexCoord (s, y))))
    (dirD (J ∘ Ψ) 1 z) x at hrow
  rw [riemannMappingClosedInverse_graph_dirD_one_of_green_fields
    hΦ p c hc hf (hmap hz) (hpole z hz) (hP hz) (hQ hz)] at hrow
  exact hrow

include hJ ha hb in
/-- The actual interior derivative formula passes to the bottom by the
proved FTC for continuous fields, rather than by an assumed trace derivative. -/
theorem riemannMappingBoundaryTrace_hasDerivAt_of_green_fields
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
     HasDerivAt (fun s : ℝ => riemannMappingClosedInverse F (Ψ (s : ℂ)))
       (riemannMappingClosedInverse F (Ψ (x : ℂ)) *
         riemannMappingGreenBoundaryCoefficient f P Q (x : ℂ)) x) := by
  apply dirichlet_boundary_horizontal_hasDerivAt ha hb hJ
    (hJ.mul (riemannMappingGreenBoundaryCoefficient_continuousOn hf hPc hQc)) _ hx
  intro s hs y hy
  exact riemannMappingBoundaryTrace_horizontal_hasDerivAt hΦ
    p c hc hf hmap hpole hP hQ hs hy

include hJ ha hb in
theorem riemannMappingBoundaryTrace_contDiffAt_of_green_fields
    {P Q : ℂ → ℂ}
    (hPc : ContinuousOn P (smoothDirichletClosedHalfBox a b))
    (hQc : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hP : EqOn P (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) 1)
      (smoothDirichletHalfBox a b))
    (hQ : EqOn Q (dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) Complex.I)
      (smoothDirichletHalfBox a b))
    (hPs : ContDiffAt ℝ ∞ (fun x : ℝ => P (x : ℂ)) 0)
    (hQs : ContDiffAt ℝ ∞ (fun x : ℝ => Q (x : ℂ)) 0) :
    ContDiffAt ℝ ∞
      (fun x : ℝ => riemannMappingClosedInverse F
        (smoothDirichletGraphChart p c hc f hf.continuous (x : ℂ))) 0 := by
  have hx₀ : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  apply contDiffAt_of_eventually_hasDerivAt_mul
    (riemannMappingGreenBoundaryCoefficient_bottom_contDiffAt hf hPs hQs)
  filter_upwards [isOpen_Ioo.mem_nhds hx₀] with x hx
  exact riemannMappingBoundaryTrace_hasDerivAt_of_green_fields hΦ
    p c hc hf ha hb hmap hpole hJ hPc hQc hP hQ hx

end

end BoundaryTransfer

section

variable (F : ℂ → ℂ) (d : smoothTraceTests)
include F d

/-- The smooth datum needed for Green is the Dirichlet datum minus
the logarithmic pole term, with its genuine sign. -/
def riemannMappingGreenLogDatum
    (Ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  d (Ψ z) - ((halfOrder * Real.log (‖Ψ z - F 0‖ ^ 2) : ℝ) : ℂ)

theorem riemannMappingGreenLogDatum_contDiffAt {Ψ : ℂ → ℂ} {z : ℂ}
    (hΨ : ContDiffAt ℝ ∞ Ψ z) (hne : Ψ z ≠ F 0) :
    ContDiffAt ℝ ∞ (riemannMappingGreenLogDatum F d Ψ) z := by
  
  have hlog := ((hΨ.sub contDiffAt_const).norm_sq ℂ).log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)))
  
  exact (d.property.1.contDiffAt.comp z hΨ).sub
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_const.mul hlog))

end

theorem contDiffAt_infty_dirD {φ : ℂ → ℂ} {z : ℂ}
    (hφ : ContDiffAt ℝ ∞ φ z) (v : ℂ) :
    ContDiffAt ℝ ∞ (dirD φ v) z :=
  (hφ.fderiv_right  le_rfl).clm_apply contDiffAt_const

theorem riemannMappingFlattenedGreen_eq_remainder_add_datum {Ω : Set ℂ}
    {F : ℂ → ℂ} (hΦ : SmoothUniformization Ω F)
    (d : smoothTraceTests) (Ψ : ℂ → ℂ) {z : ℂ}
    (hz : Ψ z ∈ closure Ω) (hne : Ψ z ≠ F 0) :
    riemannMappingFlattenedGreen F Ψ z =
      riemannMappingDirichletRemainder F d (Ψ z) + riemannMappingGreenLogDatum F d Ψ z := by
  rw [riemannMappingFlattenedGreen, riemannMappingDirichletRemainder,
    riemannMappingGreenLogDatum,
    riemannMappingGreenCorrection_eq hΦ hz hne, Real.log_pow]
  push_cast
  ring

theorem riemannMappingGraph_origin (p c : ℂ) (hc : c ≠ 0) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf₀ : f 0 = 0) :
    smoothDirichletGraphChart p c hc f hf.continuous 0 = p := by
  simp [smoothDirichletGraphShear, hf₀]

section NonzeroBoundaryTransfer

variable {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : SmoothUniformization Ω F)
    (p c : ℂ) (hc : c ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf₀ : f 0 = 0) (hp : p ∈ frontier Ω) {a b : ℝ}

include hΦ hf₀ hp

section

variable (ha : 0 < a) (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b → (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im))
include ha hb hchart

/-- The Green lower bound is applied on its proved physical inward ray.
The genuine graph membership equivalence locates that ray in the same
upper halfbox. If both graph gradients vanished, the ray derivative
would tend to zero, contradicting the strictly positive Green slope. -/
theorem riemannMappingGreen_graph_vertical_field_ne_zero
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
  have hΨ₀  := riemannMappingGraph_origin p c hc hf hf₀
  have hpin  := frontier_subset_closure hp
  have hpne : p ≠ F 0 := by
    intro he
    rw [he, hΦ.smooth.1.1.frontier_eq] at hp
    exact hp.2 (hΦ.pole_mem)
  obtain ⟨v, δ, A, _, hδ, hA, hray⟩ :=
    exists_riemannMappingGreen_inward_ray_lower hΦ hp
  let w : ℝ → ℂ := fun t => p + (t : ℂ) * v
  let ζ  := fun t => Ψ.symm (w t)
  let R  := fun t => (riemannMappingGreen F (w t) : ℂ)
  have hw : Continuous w := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hw₀ : w 0 = p := by simp [w]
  have hζ₀ : ζ 0 = 0 := by
    change Ψ.symm (w 0) = 0
    rw [hw₀, ← hΨ₀, Ψ.symm_apply_apply]
  have hζlim : Tendsto ζ (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hh : Tendsto ζ (𝓝[>] (0 : ℝ)) (𝓝 (ζ 0)) :=
      (Ψ.symm.continuous.comp hw).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [hζ₀] using hh
  have hrelim : Tendsto (fun t : ℝ => |(ζ t).re|) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Complex.zero_re, abs_zero, Function.comp_def] using
      continuous_abs.continuousAt.tendsto.comp
        (Complex.continuous_re.continuousAt.tendsto.comp hζlim)
  have himlim : Tendsto (fun t : ℝ => |(ζ t).im|) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Complex.zero_im, abs_zero, Function.comp_def] using
      continuous_abs.continuousAt.tendsto.comp
        (Complex.continuous_im.continuousAt.tendsto.comp hζlim)
  have hζbox : ∀ᶠ t in 𝓝[>] (0 : ℝ), ζ t ∈ smoothDirichletHalfBox a b := by
    filter_upwards [self_mem_nhdsWithin, hrelim.eventually_lt_const ha,
      himlim.eventually_lt_const hb,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htr hti htδ
    have hwt  := (hray t ht htδ).1
    have hpos  := (hchart (ζ t) htr hti).mp (by
      
      rw [show Ψ (ζ t) = w t from Ψ.apply_symm_apply (w t)]
      exact hwt)
    exact ⟨htr, hpos, lt_of_le_of_lt (le_abs_self _) hti⟩
  have hzclosed : ∀ᶠ t in 𝓝[>] (0 : ℝ), ζ t ∈ smoothDirichletClosedHalfBox a b :=
    hζbox.mono fun t ht => ⟨ht.1.le, ht.2.1.le, ht.2.2.le⟩
  have hz₀ : (0 : ℂ) ∈ smoothDirichletClosedHalfBox a b := by
    exact ⟨by simpa using ha.le, by simp, by simpa using hb.le⟩
  have hζwithin := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    ζ hζlim hzclosed
  have hpLim  :=
    (hPc 0 hz₀).tendsto.comp hζwithin
  have hqLim  :=
    (hQc 0 hz₀).tendsto.comp hζwithin
  have hdc  := (contDiff_infty_iff_deriv.mp hf).2.continuous
  have hcoef : Continuous (fun z : ℂ =>
      (((c * v).im - deriv f z.re * (c * v).re : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_const.sub ((hdc.comp Complex.continuous_re).mul continuous_const))
  have hder : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      HasDerivAt R (((c * v).re : ℂ) * P (ζ t) +
        (((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) : ℂ) * Q (ζ t)) t := by
    filter_upwards [hζbox, self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t hzt ht htδ
    obtain ⟨hwt, hwne, _⟩ := hray t ht htδ
    have hdG  :=
      Complex.ofRealCLM.differentiableAt.comp _
        ((riemannMappingGreen_harmonicOnNhd hΦ (w t)
          ⟨hwt, hwne⟩).1.differentiableAt (by norm_num))
    have hdw : HasDerivAt w v t := by
      have hcast : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
        simpa only [id, Complex.ofReal_one] using (hasDerivAt_id t).ofReal_comp
      simpa only [one_mul] using (hcast.mul_const v).const_add p
    have hdR := hdG.hasFDerivAt.comp_hasDerivAt t hdw
    change HasDerivAt R
      (fderiv ℝ (fun z : ℂ => (riemannMappingGreen F z : ℂ)) (w t) v) t at hdR
    have he  := Ψ.apply_symm_apply (w t)
    have hfd := riemannMappingGreen_graph_fderiv_apply hΦ
      p c hc hf (z := ζ t) (by
        
        rw [he]
        exact hwt) (by
        
        rw [he]
        exact hwne) v
    change fderiv ℝ (fun z : ℂ => (riemannMappingGreen F z : ℂ)) (Ψ (ζ t)) v =
      ((c * v).re : ℂ) * dirD (riemannMappingFlattenedGreen F Ψ) 1 (ζ t) +
        (((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) : ℂ) *
          dirD (riemannMappingFlattenedGreen F Ψ) Complex.I (ζ t) at hfd
    rw [he, ← hP hzt, ← hQ hzt] at hfd
    rw [hfd] at hdR
    exact hdR
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hder
  have hdiff : DifferentiableOn ℝ R (Ioo (0 : ℝ) ε) :=
    fun t ht => (hsub ht).differentiableAt.differentiableWithinAt
  have hGreenC  := Complex.continuous_ofReal.comp_continuousOn
    (riemannMappingGreen_continuousOn hΦ)
  have hRayDomain : ∀ᶠ t in 𝓝[>] (0 : ℝ), w t ∈ closure Ω \ {F 0} := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
    exact ⟨subset_closure (hray t ht htδ).1, (hray t ht htδ).2.1⟩
  have hwlim : Tendsto w (𝓝[>] (0 : ℝ)) (𝓝 p) := by
    have hh : Tendsto w (𝓝[>] (0 : ℝ)) (𝓝 (w 0)) :=
      hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [hw₀] using hh
  have hRlim : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 (R 0)) := by
    have hh := (hGreenC p ⟨hpin, hpne⟩).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within w hwlim hRayDomain)
    simpa [R, hw₀, Function.comp_def] using hh
  have hRcont : ContinuousWithinAt R (Ioo (0 : ℝ) ε) 0 :=
    hRlim.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self)
  intro hQ₀
  have hDlim : Tendsto (deriv R) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hcoeflim := hcoef.continuousAt.tendsto.comp hζlim
    have hh : Tendsto (fun t : ℝ => ((c * v).re : ℂ) * P (ζ t) +
        (((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) : ℂ) * Q (ζ t))
        (𝓝[>] (0 : ℝ))
        (𝓝 (((c * v).re : ℂ) * P 0 +
          (((c * v).im - deriv f 0 * (c * v).re : ℝ) : ℂ) * Q 0)) :=
      (tendsto_const_nhds.mul hpLim).add (hcoeflim.mul hqLim)
    rw [hP₀, hQ₀, mul_zero, mul_zero, add_zero] at hh
    exact hh.congr' (hder.mono fun t ht => ht.deriv.symm)
  have hd₀ := hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hRcont
    (Ioo_mem_nhdsGT hε) hDlim
  have hsl := (hasDerivWithinAt_iff_tendsto_slope'
    (show (0 : ℝ) ∉ Ioi (0 : ℝ) by simp)).mp (hd₀.mono Ioi_subset_Ici_self)
  have hR₀ : R 0 = 0 := by
    simp only [R, hw₀, riemannMappingGreen_frontier hΦ hp,
      Complex.ofReal_zero]
  have hlower : ∀ᶠ t in 𝓝[>] (0 : ℝ), A ≤ (slope R 0 t).re := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
    have hlow := (hray t ht htδ).2.2
    simp only [slope_def_module, hR₀, sub_zero, Complex.smul_re, smul_eq_mul,
      R, Complex.ofReal_re]
    simpa [w, div_eq_mul_inv, mul_comm] using (le_div_iff₀ ht).mpr hlow
  have hbad  :=
    ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hsl) hlower
  exact (not_le_of_gt hA) hbad

/-- The zero Green boundary value forces its actual horizontal field to
vanish. The physical inward-ray estimate then gives a nonzero inverse
boundary derivative. Neither boundary smoothness nor a Hopf derivative
value occurs as a hypothesis. -/
theorem riemannMappingBoundaryTrace_deriv_ne_zero_of_green_fields
    (hmap : MapsTo (smoothDirichletGraphChart p c hc f hf.continuous)
      (smoothDirichletHalfBox a b) Ω)
    (hpole : ∀ z ∈ smoothDirichletHalfBox a b,
      smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0)
    (hJ : ContinuousOn (riemannMappingClosedInverse F ∘
      smoothDirichletGraphChart p c hc f hf.continuous) (smoothDirichletClosedHalfBox a b))
    (hGc : ContinuousOn (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) (smoothDirichletClosedHalfBox a b))
    (hGs : ContDiffOn ℝ ∞ (riemannMappingFlattenedGreen F
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
      (smoothDirichletGraphChart p c hc f hf.continuous (x : ℂ))) 0 ≠ 0 := by
  have hz : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hzero : ∀ x ∈ Ioo (-a) a,
      riemannMappingFlattenedGreen F
        (smoothDirichletGraphChart p c hc f hf.continuous) (x : ℂ) = 0 := by
    intro x hx
    have hx'  := abs_lt.mpr hx
    have hp' := smoothDirichletGraphChart_mem_frontier hΦ.smooth.1.1 p c hc f hf.continuous
      hb hchart hx'
    simp only [riemannMappingFlattenedGreen,
      riemannMappingGreen_frontier hΦ hp', Complex.ofReal_zero]
  have hP₀ : P 0 = 0 := by
    simpa only [Complex.ofReal_zero] using
      dirichlet_zero_boundary_horizontal_extension ha hb hGs hGc hzero hPc hP hz
  have hQ₀ := riemannMappingGreen_graph_vertical_field_ne_zero hΦ
    p c hc hf hf₀ hp ha hb hchart hPc hQc hP hQ hP₀
  have hd := riemannMappingBoundaryTrace_hasDerivAt_of_green_fields hΦ
    p c hc hf ha hb hmap hpole hJ hPc hQc hP hQ hz
  have hj : riemannMappingClosedInverse F
      (smoothDirichletGraphChart p c hc f hf.continuous 0) ≠ 0 := by
    rw [riemannMappingGraph_origin p c hc hf hf₀]
    exact norm_ne_zero_iff.mp (by
      rw [riemannMappingClosedInverse_norm_frontier hΦ hp]
      exact one_ne_zero)
  have hleft : ((deriv f 0 : ℝ) : ℂ) + Complex.I ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    exact one_ne_zero (by simpa only [Complex.add_im, Complex.ofReal_im, Complex.I_im,
      Complex.zero_im, zero_add] using hh)
  have hright : 1 + Complex.I * ((deriv f 0 : ℝ) : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    exact one_ne_zero (by simpa only [Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, zero_mul, mul_zero, sub_zero, add_zero] using hh)
  have hB : riemannMappingGreenBoundaryCoefficient f P Q 0 =
      Q 0 * (((deriv f 0 : ℝ) : ℂ) + Complex.I) * (1 + Complex.I * ((deriv f 0 : ℝ) : ℂ)) := by
    simp only [riemannMappingGreenBoundaryCoefficient, Complex.zero_re, hP₀]
    ring
  rw [hd.deriv, Complex.ofReal_zero, hB]
  positivity

end

end NonzeroBoundaryTransfer

end PolyaNeumann

end
