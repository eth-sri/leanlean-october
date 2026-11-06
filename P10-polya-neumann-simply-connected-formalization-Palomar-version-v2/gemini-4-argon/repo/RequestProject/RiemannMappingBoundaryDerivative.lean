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


noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory InnerProductSpace
open scoped Topology ContDiff ComplexConjugate InnerProductSpace

variable {P Q : ℂ → ℂ}

def riemannMappingFlattenedGreen (F : ℂ → ℂ) (Ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
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
  apply Complex.ext <;>
    simp only [Complex.inner, Complex.sq_norm, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, mul_one, one_mul, add_zero, zero_add, sub_zero] <;>
    field_simp [hn, show j.re ^ 2 + j.im ^ 2 ≠ 0 by
      simpa only [pow_two] using hn] <;> ring

section ActualMap

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)

include hb hS hsc hF hinj himage

local notation "Φ5" => riemannMappingGreen_harmonicOnNhd hb hS hsc F hF hinj himage

local notation "Φ7" => riemannMappingClosedInverse F

theorem riemannMappingGreen_complex_fderiv 
    (hw : w ∈ Ω) (hne : w ≠ F 0) v :
    fderiv ℝ (fun z => (riemannMappingGreen F z : ℂ)) w v =
      ((-⟪Φ7 w,
        deriv (Φ7) w * v⟫_ℝ /
          ‖Φ7 w‖ ^ 2 : ℝ) : ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ riemannMappingGreen F) w v = _
  rw [fderiv_comp w Complex.ofRealCLM.differentiableAt ((Φ5 w ⟨hw, hne⟩).1.differentiableAt (by norm_num)),
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    riemannMappingGreen_fderiv hb hS hsc F hF hinj himage hw hne]

/-- The actual graph gradient reconstructs the interior inverse derivative.
The shear cancellation is applied to the genuine real Green function. -/
theorem riemannMappingClosedInverse_deriv_graph_green
    (p c : ℂ) (hc : c ≠ 0) 
    (hf : ContDiff ℝ ∞ f) 
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω)
    (hne : smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     let G := riemannMappingFlattenedGreen F Ψ
     deriv (Φ7) (Ψ z) / c =
       Φ7 (Ψ z) *
          (-(dirD G 1 z - ((deriv f z.re : ℝ) : ℂ) * dirD G Complex.I z) +
           Complex.I * dirD G Complex.I z)) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let J := Φ7
  let G := riemannMappingFlattenedGreen F Ψ
  have hdG : DifferentiableAt ℝ (fun w => (riemannMappingGreen F w : ℂ)) (Ψ z) :=
    Complex.ofRealCLM.differentiableAt.comp _
      ((Φ5 (Ψ z)
        ⟨hz, hne⟩).1.differentiableAt (by norm_num))
  obtain ⟨hX, hY⟩ := smoothDirichletGraphChart_pullback_gradient p c hc hf hdG
  change dirD G 1 z - ((deriv f z.re : ℝ) : ℂ) * dirD G Complex.I z = _ at hX
  change dirD G Complex.I z = _ at hY
  rw [riemannMappingGreen_complex_fderiv hb hS hsc F hF hinj himage hz hne] at hX hY
  have h1 : deriv J (Ψ z) * (1 / c) = deriv J (Ψ z) / c := by ring
  rw [h1] at hX
  rw [show deriv J (Ψ z) * (Complex.I / c) = deriv J (Ψ z) / c * Complex.I by ring] at hY
  change deriv J (Ψ z) / c = _
  rw [hX, hY]
  exact complex_eq_mul_log_gradient (J (Ψ z)) (deriv J (Ψ z) / c)
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage
      (subset_closure hz) hne)

theorem riemannMappingClosedInverse_graph_dirD_one
    (p c : ℂ) (hc : c ≠ 0) 
    (hf : ContDiff ℝ ∞ f) 
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     dirD (Φ7 ∘ Ψ) 1 z =
       deriv (Φ7) (Ψ z) / c *
          (1 + Complex.I * ((deriv f z.re : ℝ) : ℂ))) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let J := Φ7
  have hdJ :=
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).differentiableAt
      (hS.1.1.mem_nhds hz)
  change fderiv ℝ (J ∘ Ψ) z 1 = _
  rw [fderiv_comp z (hdJ.restrictScalars ℝ)
    (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt,
    ContinuousLinearMap.comp_apply, hdJ.fderiv_restrictScalars ℝ]
  change fderiv ℂ J (Ψ z) (fderiv ℝ Ψ z 1) = _
  rw [fderiv_eq_deriv_mul, smoothDirichletGraphChart_fderiv_apply p c hc hf z 1]
  simp only [Complex.one_re, mul_one, Complex.real_smul, div_eq_mul_inv]
  ring

theorem riemannMappingClosedInverse_graph_dirD_one_of_green_fields
    (p c : ℂ) hc 
    (hf : ContDiff ℝ ∞ f) 
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω)
    (hne : smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0)
    
    (hP : P z = dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) 1 z)
    (hQ : Q z = dirD (riemannMappingFlattenedGreen F
      (smoothDirichletGraphChart p c hc f hf.continuous)) Complex.I z) :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     dirD (Φ7 ∘ Ψ) 1 z =
        Φ7 (Ψ z) * riemannMappingGreenBoundaryCoefficient f P Q z) := by
  dsimp only
  rw [riemannMappingClosedInverse_graph_dirD_one hb hS hsc F hF hinj himage p c hc hf hz,
    riemannMappingClosedInverse_deriv_graph_green hb hS hsc F hF hinj himage p c hc hf hz hne, ← hP, ← hQ]
  unfold riemannMappingGreenBoundaryCoefficient
  ring

/-- True physical directions recovered from the two graph derivatives.
This real-linear identity is also valid along the actual inward ray. -/
theorem riemannMappingGreen_graph_fderiv_apply
    (p c : ℂ) hc 
    (hf : ContDiff ℝ ∞ f) 
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω)
    (hne : smoothDirichletGraphChart p c hc f hf.continuous z ≠ F 0) v :
    (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
     let G := riemannMappingFlattenedGreen F Ψ
     fderiv ℝ (fun w => (riemannMappingGreen F w : ℂ)) (Ψ z) v =
       ((c * v).re : ℂ) * dirD G 1 z +
          (((c * v).im - deriv f z.re * (c * v).re : ℝ) : ℂ) * dirD G Complex.I z) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let G := riemannMappingFlattenedGreen F Ψ
  let T := fderiv ℝ (fun w => (riemannMappingGreen F w : ℂ)) (Ψ z)
  obtain ⟨hX, hY⟩ := smoothDirichletGraphChart_pullback_gradient p c hc hf (Complex.ofRealCLM.differentiableAt.comp _ ((Φ5 (Ψ z) ⟨hz, hne⟩).1.differentiableAt (by norm_num)))
  change dirD G 1 z - ((deriv f z.re : ℝ) : ℂ) * dirD G Complex.I z = T (1 / c) at hX
  change dirD G Complex.I z = T (Complex.I / c) at hY
  change T v = _
  calc
    _ = T ((c * v).re • (1 / c) + (c * v).im • (Complex.I / c)) :=
      congrArg T (by
        calc
          v = c * v / c := (mul_div_cancel_left₀ v hc).symm
          _ = (((c * v).re) + (c * v).im * Complex.I) / c := by
            rw [Complex.re_add_im]
          _ = _ := by simp [div_eq_mul_inv]; ring)
    _ = (c * v).re * (dirD G 1 z - (deriv f z.re : ℝ) * dirD G Complex.I z) +
        (c * v).im * dirD G Complex.I z := by
      rw [map_add, map_smul, map_smul, ← hX, ← hY, Complex.real_smul, Complex.real_smul]
    _ = _ := by
      push_cast
      ring

end ActualMap

/-- A continuous inverse trace satisfying the deduced derivative ODE is
smooth at the center once its actual coefficient is smooth there. -/
theorem contDiffAt_of_eventually_hasDerivAt_mul {α B : ℝ → ℂ} 
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
      · have hprod :=
          ih.mul (hB.of_le (show n ≤
            ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top))
        exact (ContinuousLinearMap.toSpanSingletonCLE : ℂ ≃L[ℝ] (ℝ →L[ℝ] ℂ)).contDiff.contDiffAt.comp x₀ hprod

section BoundaryTransfer

variable {Ω : Set ℂ} (hbΩ : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    (p c : ℂ) (hc : c ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ}

include hbΩ hS hsc hF hinj himage

local notation "Φ0" => smoothDirichletGraphChart p c hc f hf.continuous

local notation "Φ2" => smoothDirichletHalfBox a b

theorem riemannMappingBoundaryTrace_horizontal_hasDerivAt
    (hmap : MapsTo (Φ0)
      (Φ2) Ω)
    (hpole : ∀ z ∈ Φ2,
      Φ0 z ≠ F 0)
    
    (hP : EqOn P (dirD (riemannMappingFlattenedGreen F
      (Φ0)) 1)
      (Φ2))
    (hQ : EqOn Q (dirD (riemannMappingFlattenedGreen F
      (Φ0)) Complex.I)
      (Φ2))
     (hx : x ∈ Ioo (-a) a) (hy : y ∈ Ioo 0 b) :
    (let Ψ := Φ0
     let z := rectangularComplexCoord (x, y)
     HasDerivAt (fun s => riemannMappingClosedInverse F
       (Ψ (rectangularComplexCoord (s, y))))
       (riemannMappingClosedInverse F (Ψ z) * riemannMappingGreenBoundaryCoefficient f P Q z) x) := by
  let Ψ := Φ0
  let J := riemannMappingClosedInverse F
  let z := rectangularComplexCoord (x, y)
  have hz : z ∈ Φ2 :=
    rectangularComplexCoord_mem_halfBox ⟨hx, hy⟩
  have hrow := ((((riemannMappingClosedInverse_differentiableOn hbΩ hS hsc F hF hinj himage).differentiableAt (hS.1.1.mem_nhds (hmap hz))).restrictScalars ℝ).comp z (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt).hasFDerivAt.comp_hasDerivAt x
    ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const (y * Complex.I))
  change HasDerivAt (fun s => J (Ψ (rectangularComplexCoord (s, y))))
    (dirD (J ∘ Ψ) 1 z) x at hrow
  rw [riemannMappingClosedInverse_graph_dirD_one_of_green_fields
    hbΩ hS hsc F hF hinj himage p c hc hf (hmap hz) (hpole z hz) (hP hz) (hQ hz)] at hrow
  exact hrow

/-- The actual interior derivative formula passes to the bottom by the
proved FTC for continuous fields, rather than by an assumed trace derivative. -/
local notation "Φ6" => smoothDirichletClosedHalfBox a b

theorem riemannMappingBoundaryTrace_hasDerivAt_of_green_fields
    (ha : 0 < a) (hb : 0 < b)
    (hmap : MapsTo (Φ0)
      (Φ2) Ω)
    (hpole : ∀ z ∈ Φ2,
      Φ0 z ≠ F 0)
    (hJ : ContinuousOn (riemannMappingClosedInverse F ∘
      Φ0) (Φ6))
    
    (hPc : ContinuousOn P (Φ6))
    (hQc : ContinuousOn Q (Φ6))
    (hP : EqOn P (dirD (riemannMappingFlattenedGreen F
      (Φ0)) 1)
      (Φ2))
    (hQ : EqOn Q (dirD (riemannMappingFlattenedGreen F
      (Φ0)) Complex.I)
      (Φ2))
     (hx : x ∈ Ioo (-a) a) :
    (let Ψ := Φ0
     HasDerivAt (fun s : ℝ => riemannMappingClosedInverse F (Ψ (s : ℂ)))
       (riemannMappingClosedInverse F (Ψ (x : ℂ)) *
         riemannMappingGreenBoundaryCoefficient f P Q (x : ℂ)) x) := by
  apply dirichlet_boundary_horizontal_hasDerivAt ha hb hJ
    (hJ.mul (by
      have hd :=
        Complex.continuous_ofReal.comp
          ((contDiff_infty_iff_deriv.mp hf).2.continuous.comp Complex.continuous_re)
      exact ((hPc.sub (hd.continuousOn.mul hQc)).neg.add
        (continuousOn_const.mul hQc)).mul
          (continuousOn_const.add (continuousOn_const.mul hd.continuousOn)))) _ hx
  intro s hs y hy
  exact riemannMappingBoundaryTrace_horizontal_hasDerivAt hbΩ hS hsc F hF hinj himage
    p c hc hf hmap hpole hP hQ hs hy

theorem riemannMappingBoundaryTrace_contDiffAt_of_green_fields
    (ha : 0 < a) (hb : 0 < b)
    (hmap : MapsTo (Φ0)
      (Φ2) Ω)
    (hpole : ∀ z ∈ Φ2,
      Φ0 z ≠ F 0)
    (hJ : ContinuousOn (riemannMappingClosedInverse F ∘
      Φ0) (Φ6))
    
    (hPc : ContinuousOn P (Φ6))
    (hQc : ContinuousOn Q (Φ6))
    (hP : EqOn P (dirD (riemannMappingFlattenedGreen F
      (Φ0)) 1)
      (Φ2))
    (hQ : EqOn Q (dirD (riemannMappingFlattenedGreen F
      (Φ0)) Complex.I)
      (Φ2))
    (hPs : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => P x) 0)
    (hQs : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Q (x : ℂ)) 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x : ℝ => riemannMappingClosedInverse F
        (Φ0 (x : ℂ))) 0 := by
  apply contDiffAt_of_eventually_hasDerivAt_mul
    (show ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => riemannMappingGreenBoundaryCoefficient f P Q (x : ℂ)) 0 by
      have hd :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp 0
          (contDiff_infty_iff_deriv.mp hf).2.contDiffAt
      simpa [riemannMappingGreenBoundaryCoefficient] using
        ((hPs.sub (hd.mul hQs)).neg.add (contDiffAt_const.mul hQs)).mul
          (contDiffAt_const.add (contDiffAt_const.mul hd)))
  filter_upwards [isOpen_Ioo.mem_nhds (⟨by linarith, ha⟩ : 0 ∈ Ioo (-a) a)] with x hx
  exact riemannMappingBoundaryTrace_hasDerivAt_of_green_fields hbΩ hS hsc F hF hinj himage
    p c hc hf ha hb hmap hpole hJ hPc hQc hP hQ hx

end BoundaryTransfer

/-- The smooth datum needed for Green is the Dirichlet datum minus
the logarithmic pole term, with its genuine sign. -/
def riemannMappingGreenLogDatum (F : ℂ → ℂ) (d : smoothTraceTests)
    (Ψ : ℂ → ℂ) (z : ℂ) : ℂ :=
  d (Ψ z) - (((1 / 2 : ℝ) * Real.log (‖Ψ z - F 0‖ ^ 2) : ℝ) : ℂ)

theorem riemannMappingGreenLogDatum_contDiffAt
    F d  
    (hΨ : ContDiffAt ℝ ∞ Ψ z) (hne : Ψ z ≠ F 0) :
    ContDiffAt ℝ ∞ (riemannMappingGreenLogDatum F d Ψ) z := by
  exact (d.property.1.contDiffAt.comp z hΨ).sub
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_const.mul (((hΨ.sub contDiffAt_const).norm_sq ℂ).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))))))

theorem contDiffAt_infty_dirD  
    (hφ : ContDiffAt ℝ ∞ φ z) v :
    ContDiffAt ℝ ∞ (dirD φ v) z :=
  (hφ.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiffAt_const

theorem riemannMappingFlattenedGreen_eq_remainder_add_datum 
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    F (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    d Ψ 
    (hz : Ψ z ∈ closure Ω) (hne : Ψ z ≠ F 0) :
    riemannMappingFlattenedGreen F Ψ z =
      riemannMappingDirichletRemainder F d (Ψ z) + riemannMappingGreenLogDatum F d Ψ z := by
  rw [riemannMappingFlattenedGreen, riemannMappingDirichletRemainder,
    riemannMappingGreenLogDatum,
    riemannMappingGreenCorrection_eq hb hS hsc F hF hinj himage hz hne, Real.log_pow]
  push_cast
  ring

theorem riemannMappingGraph_origin (p c : ℂ) hc 
    (hf : ContDiff ℝ ∞ f) (hf₀ : f 0 = 0) :
    smoothDirichletGraphChart p c hc f hf.continuous 0 = p := by
  simp [smoothDirichletGraphShear, hf₀]

section NonzeroBoundaryTransfer

variable {Ω : Set ℂ} (hbΩ : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
    (p c : ℂ) (hc : c ≠ 0) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hf₀ : f 0 = 0) (hp : p ∈ frontier Ω) {a b : ℝ}

include hbΩ hS hsc hF hinj himage hf₀ hp

/-- The Green lower bound is applied on its proved physical inward ray.
The genuine graph membership equivalence locates that ray in the same
upper halfbox. If both graph gradients vanished, the ray derivative
would tend to zero, contradicting the strictly positive Green slope. -/
local notation "Φ1" => smoothDirichletGraphChart p c hc f hf.continuous

local notation "Φ3" => smoothDirichletHalfBox a b

local notation "Φ4" => smoothDirichletClosedHalfBox a b

theorem riemannMappingGreen_graph_vertical_field_ne_zero
    (ha : 0 < a) (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (Φ1 z ∈ Ω ↔ 0 < z.im))
    
    (hPc : ContinuousOn P (Φ4))
    (hQc : ContinuousOn Q (Φ4))
    (hP : EqOn P (dirD (riemannMappingFlattenedGreen F
      (Φ1)) 1)
      (Φ3))
    (hQ : EqOn Q (dirD (riemannMappingFlattenedGreen F
      (Φ1)) Complex.I)
      (Φ3))
    (hP₀ : P 0 = 0) : Q 0 ≠ 0 := by
  let Ψ := Φ1
  obtain ⟨v, δ, A, _, hδ, hA, hray⟩ :=
    exists_riemannMappingGreen_inward_ray_lower hbΩ hS hsc F hF hinj himage hp
  let w : ℝ → ℂ := fun t => p + t * v
  let ζ : ℝ → ℂ := fun t => Ψ.symm (w t)
  let R : ℝ → ℂ := fun t => riemannMappingGreen F (w t)
  have hw : Continuous w := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hw₀ : w 0 = p := by simp [w]
  have hζlim : Tendsto ζ (𝓝[>] 0) (𝓝 0) := by
    have hh : Tendsto ζ (𝓝[>] 0) (𝓝 (ζ 0)) :=
      (Ψ.symm.continuous.comp hw).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [show ζ 0 = 0 by
      change Ψ.symm (w 0) = 0
      rw [hw₀, ← riemannMappingGraph_origin p c hc hf hf₀, Ψ.symm_apply_apply]] using hh
  have hζbox : ∀ᶠ t in 𝓝[>] 0, ζ t ∈ Φ3 := by
    filter_upwards [self_mem_nhdsWithin, (show Tendsto (fun t => |(ζ t).re|) (𝓝[>] 0) (𝓝 0) by
      simpa [Function.comp_def] using
        continuous_abs.continuousAt.tendsto.comp
          (Complex.continuous_re.continuousAt.tendsto.comp hζlim)).eventually_lt_const ha,
      (show Tendsto (fun t => |(ζ t).im|) (𝓝[>] 0) (𝓝 0) by
        simpa [Function.comp_def] using
          continuous_abs.continuousAt.tendsto.comp
            (Complex.continuous_im.continuousAt.tendsto.comp hζlim)).eventually_lt_const hb,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htr hti htδ
    have hwt := (hray t ht htδ).1
    have hpos : 0 < (ζ t).im := (hchart (ζ t) htr hti).mp (by
      change Ψ (ζ t) ∈ Ω
      rw [show Ψ (ζ t) = w t from Ψ.apply_symm_apply (w t)]
      exact hwt)
    exact ⟨htr, hpos, lt_of_le_of_lt (le_abs_self _) hti⟩
  have hz₀ : 0 ∈ Φ4 := by
    exact ⟨by simpa using ha.le, by simp, by simpa using hb.le⟩
  have hζwithin := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    ζ hζlim (hζbox.mono fun t ht => ⟨ht.1.le, ht.2.1.le, ht.2.2.le⟩ : ∀ᶠ t in 𝓝[>] 0, ζ t ∈ Φ4)
  have hder : ∀ᶠ t in 𝓝[>] 0,
      HasDerivAt R (((c * v).re) * P (ζ t) +
        ((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) * Q (ζ t)) t := by
    filter_upwards [hζbox, self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t hzt ht htδ
    obtain ⟨hwt, hwne, _⟩ := hray t ht htδ
    have hdR := (Complex.ofRealCLM.differentiableAt.comp _ ((riemannMappingGreen_harmonicOnNhd hbΩ hS hsc F hF hinj himage (w t) ⟨hwt, hwne⟩).1.differentiableAt (by norm_num))).hasFDerivAt.comp_hasDerivAt t (by
      change HasDerivAt (fun s : ℝ => p + (s : ℂ) * v) v t
      simpa using ((show HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t by
        simpa using (hasDerivAt_id t).ofReal_comp).mul_const v).const_add p)
    change HasDerivAt R
      (fderiv ℝ (fun z => (riemannMappingGreen F z : ℂ)) (w t) v) t at hdR
    have he := Ψ.apply_symm_apply (w t)
    have hfd := riemannMappingGreen_graph_fderiv_apply hbΩ hS hsc F hF hinj himage
      p c hc hf (z := ζ t) (by
        change Ψ (ζ t) ∈ Ω
        rw [he]
        exact hwt) (by
        change Ψ (ζ t) ≠ F 0
        rw [he]
        exact hwne) v
    change fderiv ℝ (fun z => (riemannMappingGreen F z : ℂ)) (Ψ (ζ t)) v =
      ((c * v).re : ℂ) * dirD (riemannMappingFlattenedGreen F Ψ) 1 (ζ t) +
        ((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) *
          dirD (riemannMappingFlattenedGreen F Ψ) Complex.I (ζ t) at hfd
    rw [he, ← hP hzt, ← hQ hzt] at hfd
    rw [hfd] at hdR
    exact hdR
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hder
  intro hQ₀
  have hd₀ := hasDerivWithinAt_Ici_of_tendsto_deriv (fun t ht => (hsub ht).differentiableAt.differentiableWithinAt) ((show Tendsto R (𝓝[>] 0) (𝓝 (R 0)) by
    have hh := ((Complex.continuous_ofReal.comp_continuousOn (riemannMappingGreen_continuousOn hbΩ hS hsc F hF hinj himage)) p ⟨frontier_subset_closure hp, (by
      intro he
      rw [he, hS.1.1.frontier_eq] at hp
      exact hp.2 (riemannMapping_pole_mem F himage))⟩).tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within w (by
        have hh : Tendsto w (𝓝[>] 0) (𝓝 (w 0)) :=
          hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        simpa [hw₀] using hh) (by
        filter_upwards [self_mem_nhdsWithin,
          (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
        exact ⟨subset_closure (hray t ht htδ).1, (hray t ht htδ).2.1⟩))
    simpa [R, hw₀, Function.comp_def] using hh).mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self))
    (Ioo_mem_nhdsGT hε) (by
      have hh : Tendsto (fun t => (c * v).re * P (ζ t) +
          ((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) * Q (ζ t))
          (𝓝[>] 0)
          (𝓝 (((c * v).re) * P 0 +
            ((c * v).im - deriv f 0 * (c * v).re : ℝ) * Q 0)) :=
        (tendsto_const_nhds.mul ((hPc 0 hz₀).tendsto.comp hζwithin)).add ((show Tendsto (fun t => (((c * v).im - deriv f (ζ t).re * (c * v).re : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ((c * v).im - deriv f 0 * (c * v).re : ℝ)) by
          simpa [Function.comp_def] using (Complex.continuous_ofReal.comp (continuous_const.sub ((((contDiff_infty_iff_deriv.mp hf).2.continuous).comp Complex.continuous_re).mul continuous_const)) : Continuous (fun z : ℂ => (((c * v).im - deriv f z.re * (c * v).re : ℝ) : ℂ))).continuousAt.tendsto.comp hζlim).mul ((hQc 0 hz₀).tendsto.comp hζwithin))
      rw [hP₀, hQ₀, mul_zero, mul_zero, add_zero] at hh
      exact hh.congr' (hder.mono fun t ht => ht.deriv.symm))
  exact (not_le_of_gt hA) (ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp ((hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp (hd₀.mono Ioi_subset_Ici_self))) (by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
    simp [slope_def_module, show R 0 = 0 by
      simp [R, hw₀, riemannMappingGreen_frontier hbΩ hS hsc F hF hinj himage hp], R]
    simpa only [w, div_eq_mul_inv, mul_comm] using (le_div_iff₀ ht).mpr ((hray t ht htδ).2.2)))

/-- The zero Green boundary value forces its actual horizontal field to
vanish. The physical inward-ray estimate then gives a nonzero inverse
boundary derivative. Neither boundary smoothness nor a Hopf derivative
value occurs as a hypothesis. -/
theorem riemannMappingBoundaryTrace_deriv_ne_zero_of_green_fields
    (ha : 0 < a) (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (Φ1 z ∈ Ω ↔ 0 < z.im))
    (hmap : MapsTo (Φ1)
      (Φ3) Ω)
    (hpole : ∀ z ∈ Φ3,
      Φ1 z ≠ F 0)
    (hJ : ContinuousOn (riemannMappingClosedInverse F ∘
      Φ1) (Φ4))
    (hGc : ContinuousOn (riemannMappingFlattenedGreen F
      (Φ1)) (Φ4))
    (hGs : ContDiffOn ℝ ∞ (riemannMappingFlattenedGreen F
      (Φ1)) (Φ3))
    
    (hPc : ContinuousOn P (Φ4))
    (hQc : ContinuousOn Q (Φ4))
    (hP : EqOn P (dirD (riemannMappingFlattenedGreen F
      (Φ1)) 1)
      (Φ3))
    (hQ : EqOn Q (dirD (riemannMappingFlattenedGreen F
      (Φ1)) Complex.I)
      (Φ3)) :
    deriv (fun x : ℝ => riemannMappingClosedInverse F
      (Φ1 (x : ℂ))) 0 ≠ 0 := by
  have hz : 0 ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hP₀ : P 0 = 0 := by
    simpa only [Complex.ofReal_zero] using
      dirichlet_zero_boundary_horizontal_extension ha hb hGs hGc (by
        intro x hx
        simp only [riemannMappingFlattenedGreen,
          riemannMappingGreen_frontier hbΩ hS hsc F hF hinj himage (smoothDirichletGraphChart_mem_frontier hS.1.1 p c hc f hf.continuous hb hchart (abs_lt.mpr hx)), Complex.ofReal_zero]) hPc hP hz
  rw [(riemannMappingBoundaryTrace_hasDerivAt_of_green_fields hbΩ hS hsc F hF hinj himage p c hc hf ha hb hmap hpole hJ hPc hQc hP hQ hz).deriv, Complex.ofReal_zero, show riemannMappingGreenBoundaryCoefficient f P Q 0 = Q 0 * ((deriv f 0 : ℝ) + Complex.I) * (1 + Complex.I * (deriv f 0 : ℝ)) by
    simp only [riemannMappingGreenBoundaryCoefficient, Complex.zero_re, hP₀]
    ring]
  exact mul_ne_zero (by
    rw [riemannMappingGraph_origin p c hc hf hf₀]
    exact norm_ne_zero_iff.mp (by
      rw [riemannMappingClosedInverse_norm_frontier hbΩ hS hsc F hF hinj himage hp]
      exact one_ne_zero)) (mul_ne_zero (mul_ne_zero (riemannMappingGreen_graph_vertical_field_ne_zero hbΩ hS hsc F hF hinj himage p c hc hf hf₀ hp ha hb hchart hPc hQc hP hQ hP₀) (by
    intro he
    exact one_ne_zero (by simpa only [Complex.add_im, Complex.ofReal_im, Complex.I_im,
      Complex.zero_im, zero_add] using (congrArg Complex.im he)))) (by
    intro he
    exact one_ne_zero (by simpa only [Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, zero_mul, mul_zero, sub_zero, add_zero] using (congrArg Complex.re he))))

end NonzeroBoundaryTransfer

end PolyaNeumann

end
