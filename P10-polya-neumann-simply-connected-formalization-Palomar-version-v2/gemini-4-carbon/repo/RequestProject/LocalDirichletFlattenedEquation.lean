module

public import RequestProject.ReconBasic
public import RequestProject.ChainRule
public import RequestProject.SmoothDomain
public import RequestProject.SmoothCompactExtension
public import RequestProject.LocalConformalH1
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory InnerProductSpace
open scoped Topology ContDiff ComplexConjugate

/-! ### Smooth graph coordinates & flattening box -/

def smoothDirichletGraphShear (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  z + (f z.re : ℂ) * Complex.I

@[simp] private theorem smoothDirichletGraphShear_re (f : ℝ → ℝ) (z : ℂ) :
    (smoothDirichletGraphShear f z).re = z.re := by simp [smoothDirichletGraphShear]

@[simp] private theorem smoothDirichletGraphShear_im (f : ℝ → ℝ) (z : ℂ) :
    (smoothDirichletGraphShear f z).im = z.im + f z.re := by simp [smoothDirichletGraphShear]

def smoothDirichletGraphShearHomeomorph (f : ℝ → ℝ) (hf : Continuous f) : ℂ ≃ₜ ℂ where
  toFun := smoothDirichletGraphShear f
  invFun := fun z => z - (f z.re : ℂ) * Complex.I
  left_inv z := by apply Complex.ext <;> simp [smoothDirichletGraphShear]
  right_inv z := by apply Complex.ext <;> simp [smoothDirichletGraphShear]
  continuous_toFun := continuous_id.add
    ((Complex.ofRealCLM.continuous.comp (hf.comp Complex.continuous_re)).mul continuous_const)
  continuous_invFun := continuous_id.sub
    ((Complex.ofRealCLM.continuous.comp (hf.comp Complex.continuous_re)).mul continuous_const)

private theorem smoothDirichletGraphShear_lipschitz {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : LipschitzWith (K + 1) (smoothDirichletGraphShear f) :=
  LipschitzWith.of_dist_le_mul fun z w => by
    simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
    have hre : ‖z.re - w.re‖ ≤ ‖z - w‖ := by
      simpa only [Real.norm_eq_abs, Complex.sub_re] using Complex.abs_re_le_norm (z - w)
    have hfw : ‖((f z.re - f w.re : ℝ) : ℂ) * Complex.I‖ ≤ (K : ℝ) * ‖z - w‖ := by
      simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
      exact (hf.norm_sub_le z.re w.re).trans (mul_le_mul_of_nonneg_left hre K.coe_nonneg)
    calc ‖smoothDirichletGraphShear f z - smoothDirichletGraphShear f w‖
        = ‖(z - w) + ((f z.re - f w.re : ℝ) : ℂ) * Complex.I‖ := by
          congr 1; simp only [smoothDirichletGraphShear, Complex.ofReal_sub]; ring
      _ ≤ ‖z - w‖ + (K : ℝ) * ‖z - w‖ := (norm_add_le _ _).trans (add_le_add le_rfl hfw)
      _ = ((K : ℝ) + 1) * ‖z - w‖ := by ring

def smoothDirichletGraphChart (p c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : Continuous f) :
    ℂ ≃ₜ ℂ :=
  (smoothDirichletGraphShearHomeomorph f hf).trans
    ((Homeomorph.mulRight₀ c hc).symm.trans (Homeomorph.addLeft p))

@[simp] theorem smoothDirichletGraphChart_apply (p c : ℂ) (hc : c ≠ 0)
    (f : ℝ → ℝ) (hf : Continuous f) (z : ℂ) :
    smoothDirichletGraphChart p c hc f hf z = p + smoothDirichletGraphShear f z / c := by
  simp [smoothDirichletGraphChart, div_eq_mul_inv]; exact Or.inl rfl

theorem smoothDirichletGraphChart_contDiff (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothDirichletGraphChart p c hc f hf.continuous) :=
  contDiff_const.add
    ((contDiff_id.add ((Complex.ofRealCLM.contDiff.comp (hf.comp Complex.reCLM.contDiff)).mul
      contDiff_const)).div_const c)

theorem exists_smoothDomain_flattening_rectangle {Ω : Set ℂ} (hS : IsSmoothDomain Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
      (K : NNReal) (a b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      ∀ z : ℂ, |z.re| < a → |z.im| < b →
        (smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω ↔ 0 < z.im) := by
  obtain ⟨c, r, h, K, f, hc₁, hr, hh, hf, hLip, hf₀, _, hchart⟩ := hS.2 p hp
  have hc : c ≠ 0 := fun heq => by simp [heq] at hc₁
  let a := min r (h / (4 * ((K : ℝ) + 1)))
  let b := h / 4
  have hden : 0 < 4 * ((K : ℝ) + 1) := by positivity
  refine ⟨c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, lt_min hr (div_pos hh hden),
    div_pos hh (by norm_num), fun z hzre hzim => ?_⟩
  have hrot : c * (smoothDirichletGraphChart p c hc f hf.continuous z - p) =
      smoothDirichletGraphShear f z := by rw [smoothDirichletGraphChart_apply]; field_simp [hc]; ring
  have hzrer : |z.re| < r := hzre.trans_le (min_le_left _ _)
  have hscale : 4 * ((K : ℝ) + 1) * |z.re| < h := by
    simpa only [mul_comm] using (lt_div_iff₀ hden).mp (hzre.trans_le (min_le_right _ _))
  have hfz : |f z.re| ≤ (K : ℝ) * |z.re| := by
    simpa only [hf₀, sub_zero, Real.norm_eq_abs] using hLip.norm_sub_le z.re 0
  have hy : |z.im + f z.re| < h := by
    have hs := abs_add_le z.im (f z.re); dsimp [b] at hzim; nlinarith [abs_nonneg z.re]
  simpa only [hrot, smoothDirichletGraphShear_re, smoothDirichletGraphShear_im,
    lt_add_iff_pos_left] using hchart (smoothDirichletGraphChart p c hc f hf.continuous z)
      (by simpa only [hrot, smoothDirichletGraphShear_re] using hzrer)
      (by simpa only [hrot, smoothDirichletGraphShear_im] using hy)

theorem smoothDirichletGraphChart_mem_frontier {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (p c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf z ∈ Ω ↔ 0 < z.im))
    {x : ℝ} (hx : |x| < a) :
    smoothDirichletGraphChart p c hc f hf (x : ℂ) ∈ frontier Ω := by
  let Ψ := smoothDirichletGraphChart p c hc f hf
  have hnot : Ψ (x : ℂ) ∉ Ω := by
    simpa only [Complex.ofReal_im, lt_self_iff_false, iff_false] using
      hchart (x : ℂ) (by simpa using hx) (by simpa using hb)
  have hcurve : Tendsto (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
    have h0 : Tendsto (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) (𝓝[>] (0 : ℝ))
        (𝓝 ((x : ℂ) + (0 : ℂ) * Complex.I)) :=
      (tendsto_const_nhds.add ((Complex.ofRealCLM.continuous.tendsto 0).mul_const Complex.I)).mono_left
        nhdsWithin_le_nhds
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using h0
  have hmem : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), Ψ ((x : ℂ) + (t : ℂ) * Complex.I) ∈ Ω := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with t ht htb
    have ht₀ : 0 < t := ht
    exact (hchart _ (by simpa using hx) (by simpa [abs_of_pos ht₀] using htb)).mpr (by simpa using ht₀)
  rw [hΩ.frontier_eq]
  exact ⟨mem_closure_of_tendsto ((Ψ.continuous.tendsto (x : ℂ)).comp hcurve) hmem, hnot⟩

theorem smoothDirichletGraphChart_zero_boundary {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (p c : ℂ) (hc : c ≠ 0) (f : ℝ → ℝ) (hf : Continuous f) {a b : ℝ} (hb : 0 < b)
    (hchart : ∀ z : ℂ, |z.re| < a → |z.im| < b →
      (smoothDirichletGraphChart p c hc f hf z ∈ Ω ↔ 0 < z.im))
    (v : ℂ → ℂ) (hv : ∀ z ∈ frontier Ω, v z = 0) {x : ℝ} (hx : |x| < a) :
    v (smoothDirichletGraphChart p c hc f hf (x : ℂ)) = 0 :=
  hv _ (smoothDirichletGraphChart_mem_frontier hΩ p c hc f hf hb hchart hx)

theorem smoothDirichletGraphChart_pullback_memLp {Ω U : Set ℂ}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    (himage : smoothDirichletGraphChart p c hc f hf.continuous '' U ⊆ Ω)
    {v : ℂ → ℂ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v Ω)
    (hm : MemLp v 2 (volume.restrict Ω))
    (hg : ∀ i : Fin 2, MemLp (dirD v (coordDir i)) 2 (volume.restrict Ω)) :
    MemLp (fun z => v (smoothDirichletGraphChart p c hc f hf.continuous z)) 2
      (volume.restrict U) ∧
    ∀ i : Fin 2, MemLp
      (dirD (fun z => v (smoothDirichletGraphChart p c hc f hf.continuous z)) (coordDir i))
      2 (volume.restrict U) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  have hK : 0 < K + 1 := by positivity
  have hΨ : LipschitzOnWith (K + 1) Ψ U :=
    (LipschitzWith.of_dist_le_mul fun z w => by
      have heq : Ψ z - Ψ w = (smoothDirichletGraphShear f z - smoothDirichletGraphShear f w) / c := by
        simp only [Ψ, smoothDirichletGraphChart_apply]; ring
      simpa only [dist_eq_norm, heq, norm_div, hc₁, div_one] using
        (smoothDirichletGraphShear_lipschitz hLip).dist_le_mul z w).lipschitzOnWith
  have hΨinv : LipschitzOnWith (K + 1) Ψ.symm (Ψ '' U) :=
    (LipschitzWith.of_dist_le_mul fun z w => by
      have hsymm : (smoothDirichletGraphShearHomeomorph f hLip.continuous).symm =
          smoothDirichletGraphShear (-f) :=
        funext fun q => by simp [smoothDirichletGraphShearHomeomorph, smoothDirichletGraphShear, sub_eq_add_neg]
      change dist ((smoothDirichletGraphShearHomeomorph f hLip.continuous).symm ((-p + z) * c))
        ((smoothDirichletGraphShearHomeomorph f hLip.continuous).symm ((-p + w) * c)) ≤ _
      rw [hsymm]
      have hs := (smoothDirichletGraphShear_lipschitz hLip.neg).dist_le_mul ((-p + z) * c) ((-p + w) * c)
      simpa only [dist_eq_norm, show (-p + z) * c - (-p + w) * c = (z - w) * c by ring,
        norm_mul, hc₁, mul_one] using hs).lipschitzOnWith
  have hm' := hm.mono_measure (Measure.restrict_mono_set volume himage)
  have hg' (i : Fin 2) := (hg i).mono_measure (Measure.restrict_mono_set volume himage)
  refine ⟨memLp_comp_bilip' hU hK hΨ hΨinv hm', fun i => ?_⟩
  let G : Fin 2 → L2 (Ψ '' U) := fun j => (hg' j).toLp _
  have hae : ∀ᵐ z ∂(volume.restrict U), ∀ j : Fin 2, G j (Ψ z) = dirD v (coordDir j) (Ψ z) :=
    ae_all_iff.mpr fun j => (quasiMeasurePreserving_restrict hΨinv).ae (hg' j).coeFn_toLp
  refine (memLp_chainGrad hU hK hΨ hΨinv G i).ae_eq ?_
  filter_upwards [hae, ae_restrict_mem hU.measurableSet] with z hz hzU
  have hdv := (hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds (himage (mem_image_of_mem Ψ hzU)))
  have hdΨ := ((smoothDirichletGraphChart_contDiff p c hc hf).differentiable (by simp)) z
  change chainGrad Ψ (fun j => (G j : ℂ → ℂ)) i z = fderiv ℝ (v ∘ Ψ) z (coordDir i)
  rw [fderiv_comp z hdv hdΨ, ContinuousLinearMap.comp_apply, clm_apply_eq_sum_coordRe]
  simp only [chainGrad, smul_eq_mul, hz, dirD]

def smoothDirichletHalfBox (a b : ℝ) : Set ℂ := {z | |z.re| < a ∧ 0 < z.im ∧ z.im < b}

def smoothDirichletClosedHalfBox (a b : ℝ) : Set ℂ := {z | |z.re| ≤ a ∧ 0 ≤ z.im ∧ z.im ≤ b}

theorem isOpen_smoothDirichletHalfBox (a b : ℝ) : IsOpen (smoothDirichletHalfBox a b) :=
  (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))

theorem dirichlet_halfBox_isBounded {a b : ℝ} :
    Bornology.IsBounded (smoothDirichletHalfBox a b) :=
  (isBounded_closedBall (x := (0 : ℂ)) (r := a + b)).subset fun z hz => by
    rw [mem_closedBall, dist_zero_right]
    exact (Complex.norm_le_abs_re_add_abs_im z).trans
      (add_le_add hz.1.le (by rw [abs_of_pos hz.2.1]; exact hz.2.2.le))

/-! ### Graph differential & flattened divergence equation -/

def smoothDirichletGraphDifferential (d : ℝ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.id ℝ ℂ + (d • Complex.reCLM).smulRight Complex.I

@[simp] theorem smoothDirichletGraphDifferential_apply (d : ℝ) (w : ℂ) :
    smoothDirichletGraphDifferential d w = w + (d * w.re) • Complex.I := by
  simp [smoothDirichletGraphDifferential]

theorem smoothDirichletGraphChart_hasFDerivAt (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : ℂ) :
    HasFDerivAt (smoothDirichletGraphChart p c hc f hf.continuous)
      (c⁻¹ • smoothDirichletGraphDifferential (deriv f z.re)) z := by
  have hd := ((hf.differentiable (by simp)) z.re).hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt
  have hs' : HasFDerivAt (smoothDirichletGraphShear f) (smoothDirichletGraphDifferential (deriv f z.re)) z := by
    convert (hasFDerivAt_id z).add (hd.smul_const Complex.I) using 1
    · funext y; simp [smoothDirichletGraphShear, Complex.real_smul]
    · ext w; simp [smoothDirichletGraphDifferential, Complex.real_smul]
  convert (hs'.mul_const c⁻¹).const_add p using 1
  funext x; simp only [smoothDirichletGraphChart_apply, div_eq_mul_inv]

theorem smoothDirichletGraphChart_fderiv_apply (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z w : ℂ) :
    fderiv ℝ (smoothDirichletGraphChart p c hc f hf.continuous) z w =
      c⁻¹ * (w + (deriv f z.re * w.re) • Complex.I) := by
  rw [(smoothDirichletGraphChart_hasFDerivAt p c hc hf z).fderiv]
  simp [smoothDirichletGraphDifferential_apply]

theorem smoothDirichletGraphChart_pullback_gradient (p c : ℂ) (hc : c ≠ 0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {v : ℂ → ℂ} {z : ℂ}
    (hv : DifferentiableAt ℝ v (smoothDirichletGraphChart p c hc f hf.continuous z)) :
    dirD (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) 1 z -
      ((deriv f z.re : ℝ) : ℂ) *
        dirD (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) Complex.I z =
      dirD v (1 / c) (smoothDirichletGraphChart p c hc f hf.continuous z) ∧
    dirD (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) Complex.I z =
      dirD v (Complex.I / c) (smoothDirichletGraphChart p c hc f hf.continuous z) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let T := fderiv ℝ v (Ψ z)
  let d := deriv f z.re
  have hdΨ := (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt
  have hchain (w : ℂ) : dirD (v ∘ Ψ) w z = T (c⁻¹ * (w + (d * w.re) • Complex.I)) := by
    change fderiv ℝ (v ∘ Ψ) z w = _
    rw [fderiv_comp z hv hdΨ, ContinuousLinearMap.comp_apply,
      smoothDirichletGraphChart_fderiv_apply p c hc hf z w]
  have hI : dirD (v ∘ Ψ) Complex.I z = T (Complex.I / c) := by
    rw [hchain]; simp [div_eq_mul_inv, mul_comm]
  have h1 : dirD (v ∘ Ψ) 1 z = T (1 / c) + d • T (Complex.I / c) := by
    rw [hchain, show c⁻¹ * ((1 : ℂ) + (d * (1 : ℂ).re) • Complex.I) =
      (1 / c : ℂ) + d • (Complex.I / c) by simp [Complex.real_smul, div_eq_mul_inv]; ring,
      map_add, map_smul]
  exact ⟨by change dirD (v ∘ Ψ) 1 z - (d : ℂ) * dirD (v ∘ Ψ) Complex.I z = T (1 / c)
            rw [h1, hI, Complex.real_smul, add_sub_cancel_right], hI⟩

def dirichletGraphSlope (f : ℝ → ℝ) (z : ℂ) : ℂ := ((deriv f z.re : ℝ) : ℂ)

theorem dirichletGraphSlope_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletGraphSlope f) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_infty_iff_deriv.mp hf).2.comp Complex.reCLM.contDiff)

@[simp] theorem dirD_dirichletGraphSlope_I {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : ℂ) :
    dirD (dirichletGraphSlope f) Complex.I z = 0 := by
  have hd := ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) z.re
  have hs := Complex.ofRealCLM.hasFDerivAt.comp z
    (hd.hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)
  change fderiv ℝ (Complex.ofRealCLM ∘ (deriv f ∘ Complex.re)) z Complex.I = 0
  rw [hs.fderiv]; simp

def dirichletFlattenedFlux (f : ℝ → ℝ) (u : ℂ → ℂ) (i : Fin 2) (z : ℂ) : ℂ :=
  ![dirD u 1 z - dirichletGraphSlope f z * dirD u Complex.I z,
    -dirichletGraphSlope f z * dirD u 1 z +
      (1 + dirichletGraphSlope f z ^ 2) * dirD u Complex.I z] i

def dirichletFlattenedDivergence (f : ℝ → ℝ) (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  dirD (dirichletFlattenedFlux f u 0) 1 z +
    dirD (dirichletFlattenedFlux f u 1) Complex.I z

theorem dirichletFlattenedDivergence_pullback {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (p c : ℂ) (hc : c ≠ 0) (hc₁ : ‖c‖ = 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {v : ℂ → ℂ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v Ω) {z : ℂ}
    (hz : smoothDirichletGraphChart p c hc f hf.continuous z ∈ Ω) :
    dirichletFlattenedDivergence f
      (v ∘ smoothDirichletGraphChart p c hc f hf.continuous) z =
      lap v (smoothDirichletGraphChart p c hc f hf.continuous z) := by
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := v ∘ Ψ
  let g₀ := dirD v (1 / c)
  let g₁ := dirD v (Complex.I / c)
  have hvc := hv.contDiffAt (hΩ.mem_nhds hz)
  have hv₂ : ContDiffAt ℝ 2 v (Ψ z) := hvc.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdg (w : ℂ) : DifferentiableAt ℝ (dirD v w) (Ψ z) :=
    ((hvc.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiffAt_const).differentiableAt (by simp)
  have hdΨ := (smoothDirichletGraphChart_hasFDerivAt p c hc hf z).differentiableAt
  have hn : ∀ᶠ w in 𝓝 z, Ψ w ∈ Ω := Ψ.continuous.continuousAt.eventually (hΩ.mem_nhds hz)
  have hflux_pb {w : ℂ} (hw : DifferentiableAt ℝ v (Ψ w)) :
      dirichletFlattenedFlux f u 0 w = g₀ (Ψ w) ∧
        dirichletFlattenedFlux f u 1 w = g₁ (Ψ w) - dirichletGraphSlope f w * g₀ (Ψ w) := by
    obtain ⟨hX, hY⟩ := smoothDirichletGraphChart_pullback_gradient p c hc hf hw
    refine ⟨by simpa only [dirichletFlattenedFlux, Matrix.cons_val_zero, dirichletGraphSlope, u, Ψ, g₀] using hX, ?_⟩
    change -dirichletGraphSlope f w * dirD u 1 w +
      (1 + dirichletGraphSlope f w ^ 2) * dirD u Complex.I w = _
    calc _ = dirD u Complex.I w - dirichletGraphSlope f w *
            (dirD u 1 w - dirichletGraphSlope f w * dirD u Complex.I w) := by ring
      _ = _ := by dsimp only [u, Ψ, g₀, g₁, dirichletGraphSlope]; rw [hX, hY]
  have h₀ : dirichletFlattenedFlux f u 0 =ᶠ[𝓝 z] g₀ ∘ Ψ :=
    hn.mono fun w hw => (hflux_pb ((hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hw))).1
  have h₁ : dirichletFlattenedFlux f u 1 =ᶠ[𝓝 z]
      (fun w => g₁ (Ψ w) - dirichletGraphSlope f w * g₀ (Ψ w)) :=
    hn.mono fun w hw => (hflux_pb ((hv.differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hw))).2
  have hcompI (g : ℂ → ℂ) (hg : DifferentiableAt ℝ g (Ψ z)) :
      dirD (g ∘ Ψ) Complex.I z = dirD g (Complex.I / c) (Ψ z) :=
    (smoothDirichletGraphChart_pullback_gradient p c hc hf hg).2
  have hD₀ : dirD (dirichletFlattenedFlux f u 0) 1 z =
      dirD g₀ (1 / c) (Ψ z) + dirichletGraphSlope f z * dirD g₀ (Complex.I / c) (Ψ z) := by
    change fderiv ℝ (dirichletFlattenedFlux f u 0) z 1 = _
    rw [h₀.fderiv_eq (𝕜 := ℝ)]
    have h := sub_eq_iff_eq_add.mp (smoothDirichletGraphChart_pullback_gradient p c hc hf (hdg (1 / c))).1
    rwa [hcompI g₀ (hdg (1 / c))] at h
  have hD₁ : dirD (dirichletFlattenedFlux f u 1) Complex.I z =
      dirD g₁ (Complex.I / c) (Ψ z) - dirichletGraphSlope f z * dirD g₀ (Complex.I / c) (Ψ z) := by
    have hgs := (dirichletGraphSlope_contDiff hf).differentiable (by simp)
    have hd₀ : DifferentiableAt ℝ (g₀ ∘ Ψ) z := (hdg (1 / c)).comp z hdΨ
    have hd₁ : DifferentiableAt ℝ (g₁ ∘ Ψ) z := (hdg (Complex.I / c)).comp z hdΨ
    change fderiv ℝ (dirichletFlattenedFlux f u 1) z Complex.I = _
    rw [h₁.fderiv_eq (𝕜 := ℝ)]
    change fderiv ℝ ((g₁ ∘ Ψ) - (dirichletGraphSlope f * (g₀ ∘ Ψ))) z Complex.I = _
    rw [fderiv_sub hd₁ ((hgs z).mul hd₀), fderiv_mul (hgs z) hd₀]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    change dirD (g₁ ∘ Ψ) Complex.I z -
      (dirichletGraphSlope f z * dirD (g₀ ∘ Ψ) Complex.I z +
        g₀ (Ψ z) * dirD (dirichletGraphSlope f) Complex.I z) = _
    rw [hcompI g₁ (hdg (Complex.I / c)), hcompI g₀ (hdg (1 / c)), dirD_dirichletGraphSlope_I hf]; ring
  have hrot_lap {e : ℂ} (he : ‖e‖ = 1) :
      dirD (dirD v e) e (Ψ z) + dirD (dirD v (Complex.I * e)) (Complex.I * e) (Ψ z) = lap v (Ψ z) := by
    have hdf : DifferentiableAt ℝ (fderiv ℝ v) (Ψ z) :=
      (hv₂.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have hD (w : ℂ) : dirD (dirD v w) w (Ψ z) = fderiv ℝ (fderiv ℝ v) (Ψ z) w w := by
      change fderiv ℝ (fun x => fderiv ℝ v x w) (Ψ z) w = _
      rw [fderiv_clm_apply hdf (differentiableAt_const w)]; simp
    rw [hD, hD, lap, hD, hD]
    let T := fderiv ℝ (fderiv ℝ v) (Ψ z)
    let a := e.re; let b := e.im
    have hE : e = a • (1 : ℂ) + b • Complex.I := by apply Complex.ext <;> simp [a, b]
    have hIE : Complex.I * e = (-b) • (1 : ℂ) + a • Complex.I := by
      apply Complex.ext <;> simp [a, b, Complex.mul_re, Complex.mul_im]
    have hsC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by
      have h := congrArg (fun r : ℝ => r ^ 2) he
      change ‖e‖ ^ 2 = (1 : ℝ) ^ 2 at h
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h
      exact_mod_cast (by simpa only [a, b, pow_two, one_mul] using h : a ^ 2 + b ^ 2 = 1)
    change T e e + T (Complex.I * e) (Complex.I * e) = T 1 1 + T Complex.I Complex.I
    rw [congrArg (fun w => T w w) hE, congrArg (fun w => T w w) hIE]
    simp only [map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply]
    simp only [Complex.real_smul, Complex.ofReal_neg]
    calc _ = ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) * (T 1 1 + T Complex.I Complex.I) := by ring
      _ = _ := by rw [hsC, one_mul]
  calc dirichletFlattenedDivergence f u z
      = dirD g₀ (1 / c) (Ψ z) + dirD g₁ (Complex.I / c) (Ψ z) := by
          rw [dirichletFlattenedDivergence, hD₀, hD₁]; ring
    _ = lap v (Ψ z) := by
          simpa only [g₀, g₁, one_div, div_eq_mul_inv, one_mul] using
            hrot_lap (by rw [norm_inv, hc₁, inv_one] : ‖c⁻¹‖ = 1)

theorem dirichlet_contDiffOn_dirD {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (w : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirD g w) U := fun _ hz =>
  (((hg.contDiffAt (hU.mem_nhds hz)).fderiv_right
    (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiffAt_const).contDiffWithinAt

theorem dirichlet_dirD_comm {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u U) {z : ℂ} (hz : z ∈ U) (v w : ℂ) :
    dirD (dirD u v) w z = dirD (dirD u w) v z := by
  have hu := hs.contDiffAt (hU.mem_nhds hz)
  have hd : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).differentiableAt (by simp)
  have hD (a b : ℂ) : dirD (dirD u a) b z = fderiv ℝ (fderiv ℝ u) z b a := by
    change fderiv ℝ (fun x => fderiv ℝ u x a) z b = _
    rw [fderiv_clm_apply hd (differentiableAt_const a)]; simp
  rw [hD, hD]
  exact (hu.isSymmSndFDerivAt (by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))).eq w v

theorem dirichletFlattenedFlux_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (i : Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletFlattenedFlux f u i) U := by
  have hx := dirichlet_contDiffOn_dirD hU hu 1
  have hy := dirichlet_contDiffOn_dirD hU hu Complex.I
  have hd := (dirichletGraphSlope_contDiff hf).contDiffOn (s := U)
  fin_cases i
  · exact hx.sub (hd.mul hy)
  · exact (hd.neg.mul hx).add ((contDiffOn_const.add (hd.pow 2)).mul hy)

theorem dirichlet_local_smooth_mul_test_integrable {U : Set ℂ} (hU : IsOpen U)
    {g φ : ℂ → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (hφ : TestFunction U φ) :
    IntegrableOn (fun z => g z * φ z) U := by
  obtain ⟨G, hG, hGg⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hg
  rw [show (fun z => g z * φ z) = fun z => G z * φ z from funext fun z => by
    by_cases hz : z ∈ tsupport φ
    · rw [(hGg z hz).self_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hz]]
  exact (hG.memLp' 2).integrable_mul (hφ.memLp' 2)

theorem dirichlet_local_smooth_field_test_eq_neg_dirD {U : Set ℂ} (hU : IsOpen U)
    {g φ : ℂ → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (hφ : TestFunction U φ)
    (i : Fin 2) :
    (∫ z in U, g z * dirD φ (coordDir i) z) =
      -(∫ z in U, dirD g (coordDir i) z * φ z) := by
  obtain ⟨G, hG, hGg⟩ := exists_smooth_compact_extension hφ.2.1 hU hφ.2.2 hg
  have hu := hG.memLp' 2 (μ := volume.restrict U)
  have hgrad (j : Fin 2) := (hG.dirD (coordDir j)).memLp' 2 (μ := volume.restrict U)
  have hw := isWeakGradient_of_smooth hG.1 hu hgrad φ hφ i
  have hl : (fun z => (hu.toLp G : L2 U) z * dirD φ (coordDir i) z) =ᵐ[volume.restrict U]
      (fun z => g z * dirD φ (coordDir i) z) := by
    filter_upwards [hu.coeFn_toLp] with z hzG
    rw [hzG]
    by_cases hz : z ∈ tsupport φ
    · rw [(hGg z hz).self_of_nhds]
    · simp [dirD, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]
  have hr : (fun z => ((hgrad i).toLp _ : L2 U) z * φ z) =ᵐ[volume.restrict U]
      (fun z => dirD g (coordDir i) z * φ z) := by
    filter_upwards [(hgrad i).coeFn_toLp] with z hzG
    rw [hzG]
    by_cases hz : z ∈ tsupport φ
    · rw [show dirD G (coordDir i) z = dirD g (coordDir i) z from
        congrArg (fun A : ℂ →L[ℝ] ℂ => A (coordDir i)) ((hGg z hz).fderiv_eq (𝕜 := ℝ))]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  change (∫ z in U, (hu.toLp G : L2 U) z * dirD φ (coordDir i) z) =
    -(∫ z in U, ((hgrad i).toLp _ : L2 U) z * φ z) at hw
  rwa [integral_congr_ae hl, integral_congr_ae hr] at hw

/-! ### Half-box Fubini, boundary strip mass, and normal cutoff approximation -/

theorem dirichlet_halfBox_vertical_hasDerivAt {a b : ℝ} {v : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    {x y : ℝ} (hx : |x| < a) (hy : y ∈ Ioo 0 b) :
    HasDerivAt (fun s : ℝ => v ((x : ℂ) + (s : ℂ) * Complex.I))
      (dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) y := by
  have hyV : (x : ℂ) + (y : ℂ) * Complex.I ∈ smoothDirichletHalfBox a b := by
    simpa [smoothDirichletHalfBox] using (show |x| < a ∧ 0 < y ∧ y < b from ⟨hx, hy.1, hy.2⟩)
  have hdv := (hs.differentiableOn (by simp)).differentiableAt
    ((isOpen_smoothDirichletHalfBox a b).mem_nhds hyV)
  exact hdv.hasFDerivAt.comp_hasDerivAt y
    (by simpa using (((hasDerivAt_id y).ofReal_comp).mul_const Complex.I).const_add (x : ℂ))

theorem dirichlet_halfBox_sq_integrable_real_prod {a b : ℝ} {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Integrable (fun p : ℝ × ℝ => ‖g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ ^ 2)
      ((volume.restrict (Ioo (-a) a)).prod (volume.restrict (Ioo (0 : ℝ) b))) := by
  let e : (ℝ × ℝ) ≃ᵐ ℂ := Complex.measurableEquivRealProd.symm
  have hp : MeasurePreserving e volume volume := Complex.volume_preserving_equiv_real_prod.symm _
  have he (p : ℝ × ℝ) : e p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by apply Complex.ext <;> simp [e]
  have hpre : e ⁻¹' smoothDirichletHalfBox a b = Ioo (-a) a ×ˢ Ioo (0 : ℝ) b := by
    ext ⟨x, y⟩; simp [e, smoothDirichletHalfBox, abs_lt, and_assoc]
  have hprod := (hp.integrableOn_comp_preimage e.measurableEmbedding).mpr
    (hg.integrable_norm_pow (by norm_num))
  rw [hpre, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hprod
  change Integrable (fun p : ℝ × ℝ => ‖g (e p)‖ ^ 2) _ at hprod
  simpa only [he] using hprod

private theorem dirichlet_halfBox_sq_integral_eq_real_prod {a b : ℝ} (hb : 0 < b)
    {g : ℂ → ℂ} (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    (∫ z in smoothDirichletHalfBox a b, ‖g z‖ ^ 2) =
      ∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..b,
        ‖g ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 := by
  let e := Complex.measurableEquivRealProd.symm
  have hp : MeasurePreserving e volume volume := Complex.volume_preserving_equiv_real_prod.symm _
  have he (p : ℝ × ℝ) : e p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by apply Complex.ext <;> simp [e]
  have hpre : e ⁻¹' smoothDirichletHalfBox a b = Ioo (-a) a ×ˢ Ioo (0 : ℝ) b := by
    ext ⟨x, y⟩; simp [e, smoothDirichletHalfBox, abs_lt, and_assoc]
  have hmeas := (isOpen_smoothDirichletHalfBox a b).measurableSet
  have hi := hp.integral_comp e.measurableEmbedding
    ((smoothDirichletHalfBox a b).indicator fun z => ‖g z‖ ^ 2)
  rw [show (fun p => (smoothDirichletHalfBox a b).indicator (fun z => ‖g z‖ ^ 2) (e p)) =
      (e ⁻¹' smoothDirichletHalfBox a b).indicator (fun p => ‖g (e p)‖ ^ 2) from
      funext fun p => by by_cases hz : e p ∈ smoothDirichletHalfBox a b <;> simp [hz],
    integral_indicator (hmeas.preimage e.measurable), integral_indicator hmeas,
    hpre, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  rw [← hi]
  simpa only [he, intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo] using
    integral_prod (fun p : ℝ × ℝ => ‖g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ ^ 2)
      (dirichlet_halfBox_sq_integrable_real_prod hg)

private theorem dirichlet_zero_endpoint_norm_sq_le {b : ℝ}
    {v dv : ℝ → ℂ} (hv : ContinuousOn v (Icc 0 b)) (hv₀ : v 0 = 0)
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt v (dv t) t)
    (hm : MemLp dv 2 (volume.restrict (Ioc 0 b))) {t : ℝ} (ht : t ∈ Ioc 0 b) :
    ‖v t‖ ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, ‖dv s‖ ^ 2 := by
  let μ := volume.restrict (Ioc (0 : ℝ) t)
  have hm' : MemLp dv 2 μ := hm.mono_measure (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl ht.2))
  have hvc : ContinuousOn v (Icc 0 t) := hv.mono (Icc_subset_Icc le_rfl ht.2)
  have hleft : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 (v 0)) := by
    have h := hvc 0 ⟨le_rfl, ht.1.le⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE ht.1] at h
    exact h.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hright : Tendsto v (𝓝[<] t) (𝓝 (v t)) := by
    have h := hvc t ⟨ht.1.le, le_rfl⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE ht.1] at h
    exact h.mono_left (nhdsWithin_mono t Iio_subset_Iic_self)
  have hi_int : IntervalIntegrable dv volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le).mpr (hm'.integrable (by norm_num))
  have hprim := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht.1
    (fun s hs => hd s ⟨hs.1, hs.2.trans_le ht.2⟩) hi_int hleft hright
  rw [hv₀, sub_zero] at hprim
  have h1 : MemLp (fun _ : ℝ => (1 : ℂ)) 2 μ := memLp_const 1
  have hinner : (∫ s in (0 : ℝ)..t, dv s) = inner ℂ (h1.toLp _) (hm'.toLp _) := by
    rw [intervalIntegral.integral_of_le ht.1.le, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [h1.coeFn_toLp, hm'.coeFn_toLp] with s hs₁ hs₂
    rw [hs₁, hs₂]; simp [RCLike.inner_apply]
  have hnormsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (hinner ▸ norm_inner_le_norm (h1.toLp _) (hm'.toLp _))
  have hn₁ : ‖h1.toLp _‖ ^ 2 = t := by rw [norm_sq_toLp_eq_integral]; simp [μ, Measure.real, ht.1.le]
  have hn₂ : ‖hm'.toLp _‖ ^ 2 = ∫ s in (0 : ℝ)..t, ‖dv s‖ ^ 2 := by
    rw [norm_sq_toLp_eq_integral, intervalIntegral.integral_of_le ht.1.le]
  rw [mul_pow, hn₁, hn₂, hprim] at hnormsq
  exact hnormsq

private theorem dirichlet_halfBox_strip_mass_tendsto_zero {a b : ℝ} (hb : 0 < b)
    {v : ℂ → ℂ} (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ =>
      (∫ (x : ℝ) in Ioo (-a) a, ∫ t in (0 : ℝ)..ε,
        ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hvert : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a),
      MemLp (fun y : ℝ => dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) 2
        (volume.restrict (Ioc (0 : ℝ) b)) := by
    filter_upwards [(dirichlet_halfBox_sq_integrable_real_prod hg).prod_right_ae] with x hx
    have hmeas : Measurable (fun y : ℝ => dirD v Complex.I ((x : ℂ) + (y : ℂ) * Complex.I)) :=
      (measurable_fderiv_apply_const ℝ v Complex.I).comp
        (continuous_const.add (Complex.ofRealCLM.continuous.mul continuous_const)).measurable
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mpr hx
  have hnorm_strip : Tendsto (fun ε : ℝ => ∫ (x : ℝ) in Ioo (-a) a, ∫ t in (0 : ℝ)..ε,
      ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    let B : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..b,
      ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2
    have hB : Integrable B (volume.restrict (Ioo (-a) a)) := by
      simpa only [B, intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo] using
        (dirichlet_halfBox_sq_integrable_real_prod hg).integral_prod_left
    have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
        (fun x : ℝ => ∫ t in (0 : ℝ)..ε, ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        (volume.restrict (Ioo (-a) a)) := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
      have hgm := hg.mono_measure (Measure.restrict_mono_set volume
        (show smoothDirichletHalfBox a ε ⊆ smoothDirichletHalfBox a b from
          fun _ hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans hεb⟩))
      have hc : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..ε,
          ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) (volume.restrict (Ioo (-a) a)) := by
        simpa only [intervalIntegral.integral_of_le (show 0 ≤ ε from hε.le), integral_Ioc_eq_integral_Ioo] using
          (dirichlet_halfBox_sq_integrable_real_prod hgm).integral_prod_left
      exact hc.aestronglyMeasurable
    have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a),
        ‖∫ t in (0 : ℝ)..ε, ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2‖ ≤ B x := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
      filter_upwards [hvert] with x hx
      have hε₀ : 0 < ε := hε
      have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
        (hx.integrable_norm_pow (by norm_num))
      rw [Real.norm_of_nonneg (by rw [intervalIntegral.integral_of_le hε₀.le]; exact integral_nonneg fun _ => sq_nonneg _)]
      exact intervalIntegral.integral_mono_interval le_rfl hε₀.le hεb.le
        (Eventually.of_forall fun _ => sq_nonneg _) hi
    have hlim : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioo (-a) a), Tendsto
        (fun ε : ℝ => ∫ t in (0 : ℝ)..ε, ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      filter_upwards [hvert] with x hx
      have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
        (hx.integrable_norm_pow (by norm_num))
      have hc := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc 0 left_mem_uIcc
      rw [ContinuousWithinAt, uIcc_of_le hb.le, nhdsWithin_Icc_eq_nhdsGE hb] at hc
      simpa only [intervalIntegral.integral_same] using hc.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
    simpa only [integral_zero] using
      MeasureTheory.tendsto_integral_filter_of_dominated_convergence B hmeas hbound hB hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hnorm_strip ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε₀ : 0 < ε := hε
    refine div_nonneg (integral_nonneg fun _ => ?_) (sq_nonneg _)
    change 0 ≤ ∫ t in (0 : ℝ)..ε, _
    rw [intervalIntegral.integral_of_le hε₀.le]; exact integral_nonneg fun _ => sq_nonneg _
  · filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with ε hε hεb
    have hεI : ε ∈ Ioc 0 b := ⟨hε, hεb.le⟩
    have hsub : smoothDirichletHalfBox a ε ⊆ smoothDirichletHalfBox a b :=
      fun _ hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans_le hεI.2⟩
    have hVi : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..ε,
        ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) (volume.restrict (Ioo (-a) a)) := by
      simpa only [intervalIntegral.integral_of_le hεI.1.le, integral_Ioc_eq_integral_Ioo] using
        (dirichlet_halfBox_sq_integrable_real_prod
          (hm.mono_measure (Measure.restrict_mono_set volume hsub))).integral_prod_left
    have hGi : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..ε,
        ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) (volume.restrict (Ioo (-a) a)) := by
      simpa only [intervalIntegral.integral_of_le hεI.1.le, integral_Ioc_eq_integral_Ioo] using
        (dirichlet_halfBox_sq_integrable_real_prod
          (hg.mono_measure (Measure.restrict_mono_set volume hsub))).integral_prod_left
    have hbd : (fun x : ℝ => (∫ t in (0 : ℝ)..ε, ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / ε ^ 2)
        ≤ᵐ[volume.restrict (Ioo (-a) a)]
        (fun x : ℝ => ∫ t in (0 : ℝ)..ε, ‖dirD v Complex.I ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) := by
      filter_upwards [hvert, ae_restrict_mem measurableSet_Ioo] with x hmL hxI
      have hx : |x| < a := abs_lt.mpr hxI
      let L : ℝ → ℂ := fun t => (x : ℂ) + (t : ℂ) * Complex.I
      have hvL : ContinuousOn (v ∘ L) (Icc 0 b) :=
        hv.comp (continuous_const.add (Complex.ofRealCLM.continuous.mul continuous_const)).continuousOn
          fun t ht => by simpa [L, smoothDirichletClosedHalfBox] using ⟨hx.le, ht.1, ht.2⟩
      have hI : IntervalIntegrable (fun t => ‖dirD v Complex.I (L t)‖ ^ 2) volume 0 ε :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hεI.1.le).mpr
          ((show IntegrableOn _ (Ioc 0 b) volume from hmL.integrable_norm_pow (by norm_num)).mono_set
            (Ioc_subset_Ioc le_rfl hεI.2))
      have hV : IntervalIntegrable (fun t => ‖v (L t)‖ ^ 2) volume 0 ε :=
        ((hvL.mono (Icc_subset_Icc le_rfl hεI.2)).norm.pow 2).intervalIntegrable_of_Icc hεI.1.le
      have hE : 0 ≤ ∫ t in (0 : ℝ)..ε, ‖dirD v Complex.I (L t)‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le hεI.1.le]; exact integral_nonneg fun _ => sq_nonneg _
      have hbnd (t : ℝ) (ht : t ∈ Ioo 0 ε) :
          ‖v (L t)‖ ^ 2 ≤ ε * ∫ s in (0 : ℝ)..ε, ‖dirD v Complex.I (L s)‖ ^ 2 := by
        have hpt := dirichlet_zero_endpoint_norm_sq_le hvL (by simpa [L] using hz x hx)
          (fun s hs' => dirichlet_halfBox_vertical_hasDerivAt hs hx hs') hmL ⟨ht.1, ht.2.le.trans hεI.2⟩
        have hmono := intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2.le
          (Eventually.of_forall fun _ => sq_nonneg _) hI
        exact hpt.trans ((mul_le_mul_of_nonneg_left hmono ht.1.le).trans
          (mul_le_mul_of_nonneg_right ht.2.le hE))
      have hbound := intervalIntegral.integral_mono_on_of_le_Ioo hεI.1.le hV
        (intervalIntegrable_const (c := ε * ∫ s in (0 : ℝ)..ε, ‖dirD v Complex.I (L s)‖ ^ 2)) hbnd
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hbound
      exact (div_le_iff₀ (sq_pos_of_pos hεI.1)).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, integral_mul_const] using integral_mono_ae (hVi.div_const (ε ^ 2)) hGi hbd

private def dirichletNormalCutoff (ε : ℝ) (z : ℂ) : ℂ :=
  (Real.smoothTransition (z.im / ε - 1) : ℂ)

private theorem dirichletNormalCutoff_contDiff (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletNormalCutoff ε) :=
  Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    ((Complex.imCLM.contDiff.div_const ε).sub contDiff_const))

private theorem dirichletNormalCutoff_fderiv (ε : ℝ) (z w : ℂ) :
    fderiv ℝ (dirichletNormalCutoff ε) z w =
      ((deriv Real.smoothTransition (z.im / ε - 1) / ε * w.im : ℝ) : ℂ) := by
  have hi : HasFDerivAt (fun u : ℂ => u.im / ε - 1) (ε⁻¹ • Complex.imCLM) z := by
    convert ((Complex.imCLM.hasFDerivAt (x := z)).mul_const ε⁻¹).sub_const (1 : ℝ) using 1
    funext u; simp [div_eq_mul_inv]
  have ht : HasDerivAt (Real.smoothTransition : ℝ → ℝ)
      (deriv (Real.smoothTransition : ℝ → ℝ) (z.im / ε - 1)) (z.im / ε - 1) :=
    ((show ContDiff ℝ 1 (Real.smoothTransition : ℝ → ℝ) from Real.smoothTransition.contDiff).differentiable
      (by norm_num) (z.im / ε - 1)).hasDerivAt
  have hd : HasFDerivAt (dirichletNormalCutoff ε)
      (Complex.ofRealCLM.comp (deriv Real.smoothTransition (z.im / ε - 1) • (ε⁻¹ • Complex.imCLM))) z := by
    change HasFDerivAt (Complex.ofRealCLM ∘ (Real.smoothTransition : ℝ → ℝ) ∘ fun u : ℂ => u.im / ε - 1) _ z
    exact Complex.ofRealCLM.hasFDerivAt.comp z (ht.comp_hasFDerivAt z hi)
  rw [hd.fderiv]
  simp [div_eq_mul_inv, mul_assoc]

private theorem dirichlet_smoothTransition_deriv_eq_zero {t : ℝ}
    (ht : t ≤ 0 ∨ 1 ≤ t) : deriv Real.smoothTransition t = 0 := by
  rcases ht with ht | ht
  · have hmin : IsLocalMin Real.smoothTransition t := by
      change ∀ᶠ s in 𝓝 t, Real.smoothTransition t ≤ Real.smoothTransition s
      rw [Real.smoothTransition.zero_of_nonpos ht]
      exact Eventually.of_forall Real.smoothTransition.nonneg
    exact hmin.deriv_eq_zero
  · have hmax : IsLocalMax Real.smoothTransition t := by
      change ∀ᶠ s in 𝓝 t, Real.smoothTransition s ≤ Real.smoothTransition t
      rw [Real.smoothTransition.one_of_one_le ht]
      exact Eventually.of_forall Real.smoothTransition.le_one
    exact hmax.deriv_eq_zero

private theorem exists_dirichlet_smoothTransition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (show ContDiff ℝ 2 Real.smoothTransition from Real.smoothTransition.contDiff).continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (hC t ht).trans (le_max_left _ _)
  · simp only [mem_Icc, not_and_or, not_le] at ht
    rw [dirichlet_smoothTransition_deriv_eq_zero (ht.elim (Or.inl ∘ le_of_lt) (Or.inr ∘ le_of_lt)), norm_zero]
    exact le_max_right _ _

private theorem dirichletNormalCutoff_weight_error_energy_tendsto_zero {a b : ℝ} {g : ℂ → ℂ}
    (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
      ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let B : ℂ → ℝ := fun z => 4 * ‖g z‖ ^ 2
  have hmeas (ε : ℝ) : AEStronglyMeasurable (fun z => ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2) μ :=
    ((((dirichletNormalCutoff_contDiff ε).continuous.sub continuous_const).aestronglyMeasurable.mul
      hg.aestronglyMeasurable).norm).pow 2
  have hbound (ε : ℝ) : ∀ᵐ z ∂μ, ‖‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2‖ ≤ B z :=
    Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      have hc1 : ‖dirichletNormalCutoff ε z‖ ≤ 1 := by
        rw [dirichletNormalCutoff, Complex.norm_real, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _
      have hsq := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr
        ((norm_sub_le (dirichletNormalCutoff ε z) (1 : ℂ)).trans (by rw [norm_one]; linarith))
      simpa only [B, show (2 : ℝ) ^ 2 = 4 by norm_num] using mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun ε : ℝ => ‖(dirichletNormalCutoff ε z - 1) * g z‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet] with z hz
    have ht1 : Tendsto (fun ε : ℝ => dirichletNormalCutoff ε z) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (half_pos hz.2.1)).filter_mono nhdsWithin_le_nhds] with ε hε hεz
      have ht : 1 ≤ z.im / ε - 1 := by linarith [(le_div_iff₀ hε).mpr (by linarith : 2 * ε ≤ z.im)]
      simp [dirichletNormalCutoff, Real.smoothTransition.one_of_one_le ht]
    have h := ((ht1.sub (tendsto_const_nhds (x := (1 : ℂ)))).mul (tendsto_const_nhds (x := g z))).norm.pow 2
    simpa only [sub_self, zero_mul, norm_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] using h
  simpa only [integral_zero] using
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence B
      (Eventually.of_forall hmeas) (Eventually.of_forall hbound)
      ((hg.integrable_norm_pow (by norm_num)).const_mul 4) hlim

private theorem dirichletNormalCutoff_product_dirD {a b : ℝ} (ε : ℝ) {v : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    {z : ℂ} (hz : z ∈ smoothDirichletHalfBox a b) (w : ℂ) :
    dirD (fun u => dirichletNormalCutoff ε u * v u) w z =
      dirichletNormalCutoff ε z * dirD v w z + dirD (dirichletNormalCutoff ε) w z * v z := by
  have hc := (dirichletNormalCutoff_contDiff ε).differentiable (by simp) z
  have hv := (hs.differentiableOn (by simp)).differentiableAt ((isOpen_smoothDirichletHalfBox a b).mem_nhds hz)
  simp only [dirD]; change (fderiv ℝ (dirichletNormalCutoff ε * v) z) w = _
  rw [fderiv_mul hc hv]; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring

private theorem dirichletNormalCutoff_normal_gradient_error_energy_tendsto_zero {a b : ℝ}
    (hb : 0 < b) {v : ℂ → ℂ}
    (hv : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : MemLp (dirD v Complex.I) 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    Tendsto (fun ε : ℝ => ∫ z in smoothDirichletHalfBox a b,
      ‖dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z -
        dirD v Complex.I z‖ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  obtain ⟨C, hC₀, hC⟩ := exists_dirichlet_smoothTransition_deriv_bound
  let err : ℝ → ℂ → ℂ := fun ε z => dirD (dirichletNormalCutoff ε) Complex.I z * v z
  have herr_bd {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
      ‖dirD (dirichletNormalCutoff ε) Complex.I z‖ ≤ C / ε := by
    simp only [dirD, dirichletNormalCutoff_fderiv, Complex.I_im, mul_one,
      Complex.norm_real, norm_div, Real.norm_of_nonneg hε.le]
    exact div_le_div_of_nonneg_right (hC _) hε.le
  have herr_mem {ε : ℝ} (hε : 0 < ε) : MemLp (err ε) 2 μ := by
    have hd : Continuous (dirD (dirichletNormalCutoff ε) Complex.I) :=
      (((dirichletNormalCutoff_contDiff ε).fderiv_right (m := (⊤ : ℕ∞)) le_rfl).continuous.clm_apply
        continuous_const)
    refine hm.of_le_mul (c := C / ε) (hd.aestronglyMeasurable.mul hm.aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    change ‖dirD (dirichletNormalCutoff ε) Complex.I z * v z‖ ≤ (C / ε) * ‖v z‖
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (herr_bd hε z) (norm_nonneg _)
  have hB : Tendsto (fun ε : ℝ => ∫ z, ‖err ε z‖ ^ 2 ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hscale : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨by simpa only [mul_zero] using
        (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
          Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] 0) (𝓝 (2 * 0))),
        by filter_upwards [self_mem_nhdsWithin] with ε hε; exact mul_pos two_pos hε⟩
    have hstrip := (dirichlet_halfBox_strip_mass_tendsto_zero hb hv hs hz hm hg).comp hscale
    have hupper : Tendsto (fun ε : ℝ => (C ^ 2 / ε ^ 2) *
        (∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..(2 * ε), ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h0 : Tendsto (fun ε : ℝ => (4 * C ^ 2) *
          ((∫ x in Ioo (-a) a, ∫ t in (0 : ℝ)..(2 * ε),
            ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) / (2 * ε) ^ 2))
          (𝓝[>] (0 : ℝ)) (𝓝 ((4 * C ^ 2) * 0)) := tendsto_const_nhds.mul hstrip
      have hsc (ε R : ℝ) : (C ^ 2 / ε ^ 2) * R = (4 * C ^ 2) * (R / (2 * ε) ^ 2) := by
        by_cases hε : ε = 0
        · simp [hε]
        · field_simp [hε]; ring
      simpa only [← hsc, mul_zero] using h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (half_pos hb)).filter_mono nhdsWithin_le_nhds] with ε hε hεb
    have hε₀ : 0 < ε := hε
    have hεb' : 2 * ε ≤ b := by linarith
    rw [dirichlet_halfBox_sq_integral_eq_real_prod hb (herr_mem hε₀)]
    have hEi : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..b,
        ‖err ε ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) (volume.restrict (Ioo (-a) a)) := by
      simpa only [intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo] using
        (dirichlet_halfBox_sq_integrable_real_prod (herr_mem hε₀)).integral_prod_left
    have hmi := hm.mono_measure (Measure.restrict_mono_set volume
      (show smoothDirichletHalfBox a (2 * ε) ⊆ smoothDirichletHalfBox a b from
        fun _ hz' => ⟨hz'.1, hz'.2.1, hz'.2.2.trans_le hεb'⟩))
    have hVi : Integrable (fun x : ℝ => ∫ t in (0 : ℝ)..(2 * ε),
        ‖v ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) (volume.restrict (Ioo (-a) a)) := by
      simpa only [intervalIntegral.integral_of_le (by positivity : 0 ≤ 2 * ε), integral_Ioc_eq_integral_Ioo] using
        (dirichlet_halfBox_sq_integrable_real_prod hmi).integral_prod_left
    simpa only [integral_const_mul] using integral_mono_ae hEi (hVi.const_mul (C ^ 2 / ε ^ 2)) <| by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hxabs : |x| < a := abs_lt.mpr hx
      let L : ℝ → ℂ := fun t => (x : ℂ) + (t : ℂ) * Complex.I
      have hLc : Continuous L := continuous_const.add (Complex.ofRealCLM.continuous.mul continuous_const)
      have hvL : ContinuousOn (v ∘ L) (Icc 0 (2 * ε)) :=
        hv.comp hLc.continuousOn fun t ht => by
          simpa [L, smoothDirichletClosedHalfBox] using ⟨hxabs.le, ht.1, ht.2.trans hεb'⟩
      have hdL : Continuous (fun t => dirD (dirichletNormalCutoff ε) Complex.I (L t)) :=
        (((dirichletNormalCutoff_contDiff ε).fderiv_right (m := (⊤ : ℕ∞)) le_rfl).continuous.clm_apply
          continuous_const).comp hLc
      have hVL : IntervalIntegrable (fun t => ‖v (L t)‖ ^ 2) volume 0 (2 * ε) :=
        (hvL.norm.pow 2).intervalIntegrable_of_Icc (by positivity : 0 ≤ 2 * ε)
      have hEL : IntervalIntegrable (fun t => ‖err ε (L t)‖ ^ 2) volume 0 (2 * ε) :=
        (((hdL.continuousOn.mul hvL).norm).pow 2).intervalIntegrable_of_Icc (by positivity : 0 ≤ 2 * ε)
      have hslice : (∫ t in (0 : ℝ)..b, ‖err ε (L t)‖ ^ 2) = ∫ t in (0 : ℝ)..(2 * ε), ‖err ε (L t)‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le hb.le, intervalIntegral.integral_of_le (by positivity)]
        refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioc
          (Ioc_subset_Ioc le_rfl hεb') fun t ht => ?_
        have ht' : 2 * ε ≤ t := (lt_of_not_ge fun h => ht.2 ⟨ht.1.1, h⟩).le
        have htr : 1 ≤ t / ε - 1 := by linarith [(le_div_iff₀ hε₀).mpr ht']
        simp [err, L, dirD, dirichletNormalCutoff_fderiv, dirichlet_smoothTransition_deriv_eq_zero (Or.inr htr)]
      change (∫ t in (0 : ℝ)..b, ‖err ε (L t)‖ ^ 2) ≤
        (C ^ 2 / ε ^ 2) * ∫ t in (0 : ℝ)..(2 * ε), ‖v (L t)‖ ^ 2
      rw [hslice]
      have h := intervalIntegral.integral_mono_on_of_le_Ioo (by positivity : 0 ≤ 2 * ε)
        hEL (hVL.const_mul (C ^ 2 / ε ^ 2)) fun t _ => by
          dsimp only [err]; rw [norm_mul, mul_pow]
          have hn := (sq_le_sq₀ (norm_nonneg _) (div_nonneg hC₀ hε₀.le)).mpr (herr_bd hε₀ (L t))
          simpa only [div_pow] using mul_le_mul_of_nonneg_right hn (sq_nonneg _)
      simpa only [intervalIntegral.integral_const_mul] using h
  let A : ℝ → ℂ → ℂ := fun ε z => (dirichletNormalCutoff ε z - 1) * dirD v Complex.I z
  have hA := dirichletNormalCutoff_weight_error_energy_tendsto_zero hg
  have hup : Tendsto (fun ε : ℝ => 2 * (∫ z, ‖A ε z‖ ^ 2 ∂μ) + 2 * (∫ z, ‖err ε z‖ ^ 2 ∂μ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [A, μ, mul_zero, add_zero] using (tendsto_const_nhds.mul hA).add (tendsto_const_nhds.mul hB)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hAm : MemLp (A ε) 2 μ := by
    refine hg.of_le_mul (c := 2) ((((dirichletNormalCutoff_contDiff ε).continuous.sub
      continuous_const).aestronglyMeasurable).mul hg.aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    change ‖(dirichletNormalCutoff ε z - 1) * dirD v Complex.I z‖ ≤ 2 * ‖dirD v Complex.I z‖
    rw [norm_mul]
    have hc1 : ‖dirichletNormalCutoff ε z‖ ≤ 1 := by
      rw [dirichletNormalCutoff, Complex.norm_real, Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    exact mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (by rw [norm_one]; linarith)) (norm_nonneg _)
  have hBm : MemLp (err ε) 2 μ := herr_mem hε
  have hsum : (fun z => A ε z + err ε z) =ᵐ[μ]
      (fun z => dirD (fun u => dirichletNormalCutoff ε u * v u) Complex.I z - dirD v Complex.I z) := by
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet] with z hzV
    rw [dirichletNormalCutoff_product_dirD ε hs hzV]; dsimp only [A, err]; ring
  have hAi := hAm.integrable_norm_pow (by norm_num)
  have hBi := hBm.integrable_norm_pow (by norm_num)
  have hDi := ((hAm.add hBm).ae_eq hsum).integrable_norm_pow (by norm_num)
  have hi := integral_mono_ae hDi ((hAi.const_mul 2).add (hBi.const_mul 2)) <| by
    filter_upwards [hsum] with z hzsum
    dsimp only [Pi.add_apply]; rw [← hzsum]
    have hn' := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_add_le (A ε z) (err ε z))
    nlinarith [sq_nonneg (‖A ε z‖ - ‖err ε z‖)]
  simpa only [Pi.add_apply, integral_add (hAi.const_mul 2) (hBi.const_mul 2), integral_const_mul] using hi

/-! ### Localized zero-boundary tests & tangential differences -/

private theorem dirichlet_bounded_mul_memLp {μ : Measure ℂ} {a g : ℂ → ℂ} {C : ℝ}
    (ha : AEStronglyMeasurable a μ) (hbound : ∀ z, ‖a z‖ ≤ C)
    (hg : MemLp g 2 μ) : MemLp (fun z => a z * g z) 2 μ :=
  hg.of_le_mul (c := C) (ha.mul hg.aestronglyMeasurable) (Eventually.of_forall fun z => by
    change ‖a z * g z‖ ≤ C * ‖g z‖; rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound z) (norm_nonneg _))

theorem dirichlet_localized_memLp {μ : Measure ℂ} (η : smoothTraceTests) {g : ℂ → ℂ}
    (hg : MemLp g 2 μ) : MemLp (fun z => η z * g z) 2 μ := by
  obtain ⟨C, hC⟩ := η.property.2.1.exists_bound_of_continuous η.property.1.continuous
  exact dirichlet_bounded_mul_memLp η.property.1.continuous.aestronglyMeasurable hC hg

private theorem dirichlet_localized_gradient_memLp {U : Set ℂ} (hU : IsOpen U)
    (η : smoothTraceTests) {g : ℂ → ℂ} (hs : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hm : MemLp g 2 (volume.restrict U)) {i : Fin 2}
    (hg : MemLp (dirD g (coordDir i)) 2 (volume.restrict U)) :
    MemLp (dirD (fun z => η z * g z) (coordDir i)) 2 (volume.restrict U) := by
  let dη : smoothTraceTests := ⟨dirD (η : ℂ → ℂ) (coordDir i), η.property.dirD (coordDir i)⟩
  refine ((dirichlet_localized_memLp η hg).add (dirichlet_localized_memLp dη hm)).ae_eq ?_
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  have hη := η.property.1.differentiable (by simp) z
  have hgz := (hs.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
  change _ = fderiv ℝ ((η : ℂ → ℂ) * g) z (coordDir i)
  rw [fderiv_mul hη hgz]
  simp only [Pi.add_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, dirD, dη]
  ring

theorem dirichlet_eLpNorm_toReal_eq_sqrt_energy {μ : Measure ℂ} {g : ℂ → ℂ}
    (hg : MemLp g 2 μ) :
    (eLpNorm g 2 μ).toReal = Real.sqrt (∫ z, ‖g z‖ ^ 2 ∂μ) := by
  rw [← Lp.norm_toLp g hg, ← norm_sq_toLp_eq_integral hg,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

private theorem dirichlet_pairing_tendsto_of_energy_approximation {μ : Measure ℂ}
    {g k : ℂ → ℂ} (hg : MemLp g 2 μ) (hk : MemLp k 2 μ) {kε : ℝ → ℂ → ℂ}
    (hmem : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), MemLp (kε ε) 2 μ)
    (hE : Tendsto (fun ε : ℝ => ∫ z, ‖kε ε z - k z‖ ^ 2 ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ∫ z, g z * kε ε z ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 (∫ z, g z * k z ∂μ)) := by
  have h0 : Tendsto (fun ε : ℝ => ∫ z, g z * (kε ε z - k z) ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hup : Tendsto (fun ε : ℝ => (eLpNorm g 2 μ).toReal *
        Real.sqrt (∫ z, ‖kε ε z - k z‖ ^ 2 ∂μ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [Real.sqrt_zero, mul_zero, Function.comp_apply] using
        tendsto_const_nhds.mul ((Real.continuous_sqrt.tendsto 0).comp hE)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
    filter_upwards [hmem.mono fun _ h => h.sub hk] with ε hε
    simpa only [dirichlet_eLpNorm_toReal_eq_sqrt_energy hε, Pi.sub_apply] using norm_integral_mul_le_eLpNorm hg hε
  have hplus : Tendsto (fun ε : ℝ => (∫ z, g z * (kε ε z - k z) ∂μ) + ∫ z, g z * k z ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ z, g z * k z ∂μ)) := by
    simpa only [zero_add] using h0.add (tendsto_const_nhds (x := ∫ z, g z * k z ∂μ))
  refine hplus.congr' ?_
  filter_upwards [hmem] with ε hε
  have hsub := integral_sub (hg.integrable_mul hε) (hg.integrable_mul hk)
  simp only [Pi.mul_apply] at hsub
  simp_rw [mul_sub]; rw [hsub]; ring

private theorem dirichlet_weak_equation_localized_zero_boundary_test {a b : ℝ}
    (hb : 0 < b) (η : smoothTraceTests)
    (hη : tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    {g : ℂ → ℂ} (hc : ContinuousOn g (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) g (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → g (x : ℂ) = 0)
    (hm : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : ∀ i : Fin 2, MemLp (dirD g (coordDir i)) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    {F : Fin 2 → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ i : Fin 2, MemLp (F i) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hG : MemLp G 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hweak : ∀ φ : ℂ → ℂ, TestFunction (smoothDirichletHalfBox a b) φ →
      (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2, F i z * dirD φ (coordDir i) z) =
        ∫ z in smoothDirichletHalfBox a b, G z * φ z) :
    (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2,
      F i z * dirD (fun u => η u * g u) (coordDir i) z) =
      ∫ z in smoothDirichletHalfBox a b, G z * (η z * g z) := by
  let μ := volume.restrict (smoothDirichletHalfBox a b)
  let v : ℂ → ℂ := fun z => η z * g z
  let vε : ℝ → ℂ → ℂ := fun ε z => dirichletNormalCutoff ε z * v z
  have hv : ContinuousOn v (smoothDirichletClosedHalfBox a b) :=
    η.property.1.continuous.continuousOn.mul hc
  have hvS : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b) :=
    η.property.1.contDiffOn.mul hs
  have hvz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0 := fun x hx => by simp [v, hz x hx]
  have hvm : MemLp v 2 μ := dirichlet_localized_memLp η hm
  have hvg (i : Fin 2) : MemLp (dirD v (coordDir i)) 2 μ :=
    dirichlet_localized_gradient_memLp (isOpen_smoothDirichletHalfBox a b) η hs hm (hg i)
  have htest (ε : ℝ) (hε : 0 < ε) : TestFunction (smoothDirichletHalfBox a b) (vε ε) := by
    have hws : ContDiff ℝ (⊤ : ℕ∞) (vε ε) := contDiff_iff_contDiffAt.mpr fun z => by
      by_cases hzB : z ∈ smoothDirichletHalfBox a b
      · exact (dirichletNormalCutoff_contDiff ε).contDiffAt.mul
          (hvS.contDiffAt ((isOpen_smoothDirichletHalfBox a b).mem_nhds hzB))
      · refine (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℂ => (0 : ℂ)).contDiffAt.congr_of_eventuallyEq ?_
        by_cases hzε : z.im < ε
        · filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hzε] with u hu
          have ht : u.im / ε - 1 ≤ 0 := by linarith [(div_le_one hε).mpr hu.le]
          simp [vε, dirichletNormalCutoff, Real.smoothTransition.zero_of_nonpos ht]
        · have hzη : z ∉ tsupport (η : ℂ → ℂ) := fun hzη => by
            obtain ⟨hx, hy⟩ := hη hzη; exact hzB ⟨hx, hε.trans_le (le_of_not_gt hzε), hy⟩
          filter_upwards [(isClosed_tsupport (η : ℂ → ℂ)).isOpen_compl.mem_nhds hzη] with u hu
          simp [vε, v, image_eq_zero_of_notMem_tsupport hu]
    have hwc : HasCompactSupport (vε ε) := by
      rw [show vε ε = fun z => η z * (dirichletNormalCutoff ε z * g z) from funext fun _ => by dsimp [vε, v]; ring]
      exact η.property.2.1.mul_right
    have hwη : tsupport (vε ε) ⊆ tsupport (η : ℂ → ℂ) := by
      rw [show vε ε = fun z => η z * (dirichletNormalCutoff ε z * g z) from funext fun _ => by dsimp [vε, v]; ring]
      exact tsupport_mul_subset_left
    have hheight : tsupport (vε ε) ⊆ {z : ℂ | ε ≤ z.im} :=
      closure_minimal (fun z hz' => by
        by_contra h
        have ht : z.im / ε - 1 ≤ 0 := by linarith [(div_le_one hε).mpr (le_of_not_ge h)]
        exact hz' (by simp [vε, dirichletNormalCutoff, Real.smoothTransition.zero_of_nonpos ht]))
        (isClosed_le continuous_const Complex.continuous_im)
    refine ⟨hws, hwc, fun z hz' => ?_⟩
    obtain ⟨hx, hy⟩ := hη (hwη hz')
    exact ⟨hx, hε.trans_le (hheight hz'), hy⟩
  have hvalue : Tendsto (fun ε : ℝ => ∫ z, ‖vε ε z - v z‖ ^ 2 ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (dirichletNormalCutoff_weight_error_energy_tendsto_zero hvm).congr'
      (Eventually.of_forall fun ε => integral_congr_ae (Eventually.of_forall fun z => by
        change ‖(dirichletNormalCutoff ε z - 1) * v z‖ ^ 2 = ‖dirichletNormalCutoff ε z * v z - v z‖ ^ 2
        congr 2; ring))
  have hgradient (i : Fin 2) :
      Tendsto (fun ε : ℝ => ∫ z, ‖dirD (vε ε) (coordDir i) z - dirD v (coordDir i) z‖ ^ 2 ∂μ)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
    · refine (dirichletNormalCutoff_weight_error_energy_tendsto_zero
        (by simpa only [coordDir, Matrix.cons_val_zero] using hvg 0)).congr'
          (Eventually.of_forall fun ε => integral_congr_ae ?_)
      filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet] with z hz'
      simp only [coordDir, Matrix.cons_val_zero]
      rw [dirichletNormalCutoff_product_dirD ε hvS hz']
      have h0 : dirD (dirichletNormalCutoff ε) 1 z = 0 := by simp [dirD, dirichletNormalCutoff_fderiv]
      rw [h0]; congr 2; ring
    · simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero, vε, μ] using
        dirichletNormalCutoff_normal_gradient_error_energy_tendsto_zero hb hv hvS hvz hvm
          (by simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hvg 1)
  have hεm : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), MemLp (vε ε) 2 μ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε; exact (htest ε hε).memLp' 2
  have hεg (i : Fin 2) : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), MemLp (dirD (vε ε) (coordDir i)) 2 μ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε; exact ((htest ε hε).dirD (coordDir i)).memLp' 2
  have hsum := tendsto_finsetSum Finset.univ fun i _ =>
    dirichlet_pairing_tendsto_of_energy_approximation (hF i) (hvg i) (hεg i) (hgradient i)
  have hright := dirichlet_pairing_tendsto_of_energy_approximation hG hvm hεm hvalue
  have heq : (fun ε : ℝ => ∑ i : Fin 2, ∫ z, F i z * dirD (vε ε) (coordDir i) z ∂μ)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun ε : ℝ => ∫ z, G z * vε ε z ∂μ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← integral_finsetSum Finset.univ (f := fun i z => F i z * dirD (vε ε) (coordDir i) z) fun i _ =>
      (hF i).integrable_mul (((htest ε hε).dirD (coordDir i)).memLp' 2)]
    exact hweak _ (htest ε hε)
  change (∫ z, ∑ i : Fin 2, F i z * dirD v (coordDir i) z ∂μ) = ∫ z, G z * v z ∂μ
  rw [integral_finsetSum Finset.univ (f := fun i z => F i z * dirD v (coordDir i) z)
    fun i _ => (hF i).integrable_mul (hvg i)]
  exact tendsto_nhds_unique hsum (hright.congr' heq.symm)

def dirichletTangentialDifference (h : ℝ) (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  (u (z + (h : ℂ)) - u z) / (h : ℂ)

theorem dirichletTangentialDifference_memLp {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    MemLp (dirichletTangentialDifference h u) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  let T : ℂ ≃ₜ ℂ := Homeomorph.addRight (h : ℂ)
  have hT : Isometry T := Isometry.of_dist_eq fun z w => by
    change dist (z + (h : ℂ)) (w + (h : ℂ)) = dist z w; simp only [dist_eq_norm]; congr 1; abel
  have hTi : Isometry T.symm := Isometry.of_dist_eq fun z w => by
    change dist (z + -(h : ℂ)) (w + -(h : ℂ)) = dist z w; simp only [dist_eq_norm]; congr 1; abel
  have hsubT : T '' smoothDirichletHalfBox a b ⊆ smoothDirichletHalfBox A b := by
    rintro _ ⟨z, hz, rfl⟩
    have hx : |z.re + h| < A :=
      (abs_add_le z.re h).trans_lt ((add_lt_add_of_lt_of_le hz.1 le_rfl).trans_le hmargin)
    simpa [T, smoothDirichletHalfBox] using (show |z.re + h| < A ∧ 0 < z.im ∧ z.im < b from ⟨hx, hz.2⟩)
  have hs := memLp_comp_bilip' (f := T) (K := 1) (isOpen_smoothDirichletHalfBox a b)
    (by norm_num) hT.lipschitz.lipschitzOnWith hTi.lipschitz.lipschitzOnWith
    (hm.mono_measure (Measure.restrict_mono_set volume hsubT))
  have hr := hm.mono_measure (Measure.restrict_mono_set volume
    (show smoothDirichletHalfBox a b ⊆ smoothDirichletHalfBox A b from
      fun _ hz => ⟨hz.1.trans_le ((le_add_of_nonneg_right (abs_nonneg h)).trans hmargin), hz.2⟩))
  have hq := (hs.sub hr).const_smul ((h : ℂ)⁻¹)
  rwa [show ((h : ℂ)⁻¹ • ((fun z => u (T z)) - u)) = dirichletTangentialDifference h u from
    funext fun z => by
      change (h : ℂ)⁻¹ * (u (z + (h : ℂ)) - u z) = (u (z + (h : ℂ)) - u z) / (h : ℂ)
      rw [div_eq_mul_inv, mul_comm]] at hq

theorem dirichlet_halfBox_tangential_difference_energy_le {A a b h : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hmargin : a + h < A)
    {u : ℂ → ℂ} (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hDx : MemLp (dirD u 1) 2 (volume.restrict (smoothDirichletHalfBox A b))) :
    (∫ z in smoothDirichletHalfBox a b, ‖dirichletTangentialDifference h u z‖ ^ 2) ≤
      ∫ z in smoothDirichletHalfBox A b, ‖dirD u 1 z‖ ^ 2 := by
  have hhoriz {a₀ : ℝ} (ha₀ : 0 < a₀) {g : ℂ → ℂ}
      (hg : MemLp g 2 (volume.restrict (smoothDirichletHalfBox a₀ b))) :
      (∫ z in smoothDirichletHalfBox a₀ b, ‖g z‖ ^ 2) =
        ∫ y in Ioo (0 : ℝ) b, ∫ x in (-a₀)..a₀, ‖g ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 := by
    rw [dirichlet_halfBox_sq_integral_eq_real_prod hb hg]
    simp_rw [intervalIntegral.integral_of_le hb.le, integral_Ioc_eq_integral_Ioo]
    rw [integral_integral_swap (dirichlet_halfBox_sq_integrable_real_prod hg)]
    simp_rw [intervalIntegral.integral_of_le (by linarith : -a₀ ≤ a₀), integral_Ioc_eq_integral_Ioo]
  have hA : 0 < A := lt_trans ha (lt_trans (by linarith : a < a + h) hmargin)
  have hq := dirichletTangentialDifference_memLp
    (show a + |h| ≤ A by rw [abs_of_pos hh]; exact hmargin.le) hm
  have hprodQ := dirichlet_halfBox_sq_integrable_real_prod hq
  have hprodD := dirichlet_halfBox_sq_integrable_real_prod hDx
  have hqi : Integrable (fun y : ℝ => ∫ x in (-a)..a,
      ‖dirichletTangentialDifference h u ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (0 : ℝ) b)) := by
    simpa only [intervalIntegral.integral_of_le (by linarith : -a ≤ a), integral_Ioc_eq_integral_Ioo] using
      hprodQ.integral_prod_right
  have hdi : Integrable (fun y : ℝ => ∫ x in (-A)..A,
      ‖dirD u 1 ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2)
      (volume.restrict (Ioo (0 : ℝ) b)) := by
    simpa only [intervalIntegral.integral_of_le (by linarith : -A ≤ A), integral_Ioc_eq_integral_Ioo] using
      hprodD.integral_prod_right
  have hdxs := dirichlet_contDiffOn_dirD (isOpen_smoothDirichletHalfBox A b) hs 1
  rw [hhoriz ha hq, hhoriz hA hDx]
  refine integral_mono_ae hqi hdi ?_
  filter_upwards [hprodD.prod_left_ae, ae_restrict_mem measurableSet_Ioo] with y hdy hy
  let L : ℝ → ℂ := fun x => (x : ℂ) + (y : ℂ) * Complex.I
  have hLc : Continuous L := Complex.ofRealCLM.continuous.add continuous_const
  have hmap : MapsTo L (Icc (-a) (a + h)) (smoothDirichletHalfBox A b) := fun x hx => by
    have hxA : |x| < A := abs_lt.mpr ⟨by linarith [hx.1], hx.2.trans_lt hmargin⟩
    simpa [L, smoothDirichletHalfBox] using (show |x| < A ∧ 0 < y ∧ y < b from ⟨hxA, hy⟩)
  let v := u ∘ L
  let dv := dirD u 1 ∘ L
  have hv : ContinuousOn v (Icc (-a) (a + h)) := hs.continuousOn.comp hLc.continuousOn hmap
  have hdv : ContinuousOn dv (Icc (-a) (a + h)) := hdxs.continuousOn.comp hLc.continuousOn hmap
  have hd (x : ℝ) (hx : x ∈ Icc (-a) (a + h)) : HasDerivAt v (dv x) x :=
    (((hs.contDiffAt ((isOpen_smoothDirichletHalfBox A b).mem_nhds (hmap hx))).differentiableAt
      (by simp)).hasFDerivAt).comp_hasDerivAt x
      (((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * Complex.I))
  have haa : -a ≤ a := by linarith
  have haah : -a ≤ a + h := by linarith
  have hmap_add (x : ℝ) (hx : x ∈ Icc (-a) a) :
      MapsTo (fun s : ℝ => x + s) (Icc 0 h) (Icc (-a) (a + h)) :=
    fun s hs' => ⟨by linarith [hx.1, hs'.1], by linarith [hx.2, hs'.2]⟩
  have hpoint (x : ℝ) (hx : x ∈ Icc (-a) a) :
      ‖(v (x + h) - v x) / (h : ℂ)‖ ^ 2 ≤ h⁻¹ * ∫ s in (0 : ℝ)..h, ‖dv (x + s)‖ ^ 2 := by
    have hvs : ContinuousOn (fun s : ℝ => v (x + s) - v x) (Icc 0 h) :=
      (hv.comp (continuous_const.add continuous_id).continuousOn (hmap_add x hx)).sub continuousOn_const
    have hdvs : ContinuousOn (fun s : ℝ => dv (x + s)) (Icc 0 h) :=
      hdv.comp (continuous_const.add continuous_id).continuousOn (hmap_add x hx)
    have hds (s : ℝ) (hs' : s ∈ Ioo 0 h) :
        HasDerivAt (fun t : ℝ => v (x + t) - v x) (dv (x + s)) s := by
      simpa only [one_smul, Function.comp_apply] using
        ((hd (x + s) (hmap_add x hx (Ioo_subset_Icc_self hs'))).scomp s
          ((hasDerivAt_id s).const_add x)).sub_const (v x)
    have hdvs_mem : MemLp (fun s => dv (x + s)) 2 (volume.restrict (Ioc 0 h)) :=
      (memLp_two_iff_integrable_sq_norm
        ((hdvs.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)).mpr
        ((hdvs.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    have hp := dirichlet_zero_endpoint_norm_sq_le hvs (by simp) hds hdvs_mem ⟨hh, le_rfl⟩
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, div_pow]
    refine (div_le_iff₀ (sq_pos_of_pos hh)).mpr ?_
    calc ‖v (x + h) - v x‖ ^ 2 ≤ h * ∫ s in (0 : ℝ)..h, ‖dv (x + s)‖ ^ 2 := hp
      _ = (h⁻¹ * ∫ s in (0 : ℝ)..h, ‖dv (x + s)‖ ^ 2) * h ^ 2 := by field_simp [hh.ne']
  let E : ℝ × ℝ → ℝ := fun p => ‖dv (p.1 + p.2)‖ ^ 2
  have hiE : Integrable E ((volume.restrict (Ioc (-a) a)).prod (volume.restrict (Ioc (0 : ℝ) h))) := by
    rw [Measure.prod_restrict]
    exact (((hdv.norm.pow 2).comp (continuous_fst.add continuous_snd).continuousOn
      fun p hp => hmap_add p.1 hp.1 hp.2).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hq_cont : ContinuousOn (fun x : ℝ => ‖(v (x + h) - v x) / (h : ℂ)‖ ^ 2) (Icc (-a) a) :=
    (((hv.comp (continuous_id.add continuous_const).continuousOn
      fun x hx => by dsimp; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩).sub
      (hv.mono (Icc_subset_Icc le_rfl (by linarith)))).div_const (h : ℂ)).norm.pow 2
  have hH : Integrable (fun x : ℝ => ∫ s in (0 : ℝ)..h, E (x, s)) (volume.restrict (Ioc (-a) a)) := by
    simpa only [intervalIntegral.integral_of_le hh.le] using hiE.integral_prod_left
  have hfirst : (∫ x in (-a)..a, ‖(v (x + h) - v x) / (h : ℂ)‖ ^ 2) ≤
      h⁻¹ * ∫ x in (-a)..a, ∫ s in (0 : ℝ)..h, E (x, s) := by
    rw [intervalIntegral.integral_of_le haa, intervalIntegral.integral_of_le haa, ← integral_const_mul]
    exact integral_mono_ae (hq_cont.integrableOn_Icc.mono_set Ioc_subset_Icc_self) (hH.const_mul h⁻¹)
      ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => hpoint x (Ioc_subset_Icc_self hx))
  have hwide : IntervalIntegrable (fun x => ‖dv x‖ ^ 2) volume (-a) (a + h) :=
    (hdv.norm.pow 2).intervalIntegrable_of_Icc haah
  have hlast : (∫ s in (0 : ℝ)..h, ∫ x in (-a)..a, E (x, s)) ≤ h * ∫ x in (-a)..(a + h), ‖dv x‖ ^ 2 := by
    have hi_r : IntervalIntegrable (fun s : ℝ => ∫ x in (-a)..a, E (x, s)) volume 0 h := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le]
      simpa only [IntegrableOn, intervalIntegral.integral_of_le haa] using hiE.integral_prod_right
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using
      intervalIntegral.integral_mono_on_of_le_Ioo hh.le hi_r
        (intervalIntegrable_const (c := ∫ x in (-a)..(a + h), ‖dv x‖ ^ 2)) fun s hs' => by
          change (∫ x in (-a)..a, ‖dv (x + s)‖ ^ 2) ≤ _
          rw [intervalIntegral.integral_comp_add_right (f := fun x : ℝ => ‖dv x‖ ^ 2) s]
          exact intervalIntegral.integral_mono_interval (by linarith [hs'.1]) (by linarith)
            (by linarith [hs'.2]) (Eventually.of_forall fun _ => sq_nonneg _) hwide
  have hi_seg : (∫ x in (-a)..a, ‖dirichletTangentialDifference h u (L x)‖ ^ 2) ≤
      ∫ x in (-a)..(a + h), ‖dirD u 1 (L x)‖ ^ 2 := by
    have h1d : (∫ x in (-a)..a, ‖(v (x + h) - v x) / (h : ℂ)‖ ^ 2) ≤
        ∫ x in (-a)..(a + h), ‖dv x‖ ^ 2 :=
      calc _ ≤ h⁻¹ * ∫ x in (-a)..a, ∫ s in (0 : ℝ)..h, E (x, s) := hfirst
        _ = h⁻¹ * ∫ s in (0 : ℝ)..h, ∫ x in (-a)..a, E (x, s) := by
          simp only [intervalIntegral.integral_of_le haa, intervalIntegral.integral_of_le hh.le]
          rw [integral_integral_swap hiE]
        _ ≤ h⁻¹ * (h * ∫ x in (-a)..(a + h), ‖dv x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hlast (inv_nonneg.mpr hh.le)
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
    simpa only [v, dv, Function.comp_apply, dirichletTangentialDifference, L,
      Complex.ofReal_add, add_right_comm] using h1d
  have hDfull : IntervalIntegrable (fun x : ℝ => ‖dirD u 1 (L x)‖ ^ 2) volume (-A) A := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -A ≤ A)]
    simpa only [IntegrableOn, L, restrict_Ioo_eq_restrict_Ioc] using hdy
  exact hi_seg.trans (intervalIntegral.integral_mono_interval (by linarith) haah hmargin.le
    (Eventually.of_forall fun _ => sq_nonneg _) hDfull)

theorem dirichletTangentialDifference_dirD {h : ℝ} {u : ℂ → ℂ} {z : ℂ}
    (hz : DifferentiableAt ℝ u z) (hzh : DifferentiableAt ℝ u (z + (h : ℂ))) (w : ℂ) :
    dirD (dirichletTangentialDifference h u) w z =
      dirichletTangentialDifference h (dirD u w) z := by
  have hq : HasFDerivAt (dirichletTangentialDifference h u)
      ((h : ℂ)⁻¹ • (fderiv ℝ u (z + (h : ℂ)) - fderiv ℝ u z)) z := by
    convert (((hzh.hasFDerivAt.comp z ((hasFDerivAt_id z).add_const (h : ℂ))).sub
      hz.hasFDerivAt).mul_const ((h : ℂ)⁻¹)) using 1
    · funext y; simp [dirichletTangentialDifference, div_eq_mul_inv]
    · simp only [ContinuousLinearMap.comp_id]
  change fderiv ℝ (dirichletTangentialDifference h u) z w = _
  rw [hq.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    smul_eq_mul, dirichletTangentialDifference, dirD, div_eq_mul_inv]
  ring

theorem dirichletTangentialDifference_continuousOn {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b)) :
    ContinuousOn (dirichletTangentialDifference h u) (smoothDirichletClosedHalfBox a b) :=
  ((hc.comp (continuous_id.add continuous_const).continuousOn fun z hz =>
      ⟨by simpa only [Pi.add_apply, id_eq, Complex.add_re, Complex.ofReal_re] using
          (abs_add_le z.re h).trans ((add_le_add hz.1 le_rfl).trans hmargin),
       by simpa using hz.2⟩).sub
    (hc.mono fun _ hz =>
      ⟨hz.1.trans ((le_add_of_nonneg_right (abs_nonneg h)).trans hmargin), hz.2⟩)).div_const (h : ℂ)

theorem dirichletTangentialDifference_contDiffOn {A a b h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletTangentialDifference h u) (smoothDirichletHalfBox a b) :=
  ((hs.comp (contDiff_id.add contDiff_const).contDiffOn fun z hz =>
      ⟨by simpa only [Pi.add_apply, id_eq, Complex.add_re, Complex.ofReal_re] using
          (abs_add_le z.re h).trans_lt ((add_lt_add_of_lt_of_le hz.1 le_rfl).trans_le hmargin),
       by simpa using hz.2⟩).sub
    (hs.mono fun _ hz =>
      ⟨hz.1.trans_le ((le_add_of_nonneg_right (abs_nonneg h)).trans hmargin), hz.2⟩)).div_const (h : ℂ)

theorem dirichletTangentialDifference_zero_bottom {A a h : ℝ}
    (hmargin : a + |h| ≤ A) {u : ℂ → ℂ}
    (hz : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0) {x : ℝ} (hx : |x| < a) :
    dirichletTangentialDifference h u (x : ℂ) = 0 := by
  have hxA : |x| < A := hx.trans_le ((le_add_of_nonneg_right (abs_nonneg h)).trans hmargin)
  have hxh : |x + h| < A :=
    (abs_add_le x h).trans_lt ((add_lt_add_of_lt_of_le hx le_rfl).trans_le hmargin)
  simp only [dirichletTangentialDifference, ← Complex.ofReal_add, hz x hxA, hz (x + h) hxh, sub_self, zero_div]

/-! ### Shifted flux & localized Caccioppoli boundary energy bound -/

def dirichletShiftedFlux (f : ℝ → ℝ) (h : ℝ) (v : ℂ → ℂ) (i : Fin 2) (z : ℂ) : ℂ :=
  ![dirD v 1 z - dirichletGraphSlope f (z + (h : ℂ)) * dirD v Complex.I z,
    -dirichletGraphSlope f (z + (h : ℂ)) * dirD v 1 z +
      (1 + dirichletGraphSlope f (z + (h : ℂ)) ^ 2) * dirD v Complex.I z] i

theorem dirichletShiftedFlux_coercive {f : ℝ → ℝ} {K : NNReal}
    (hLip : LipschitzWith K f) (h : ℝ) (v : ℂ → ℂ) (z : ℂ) :
    (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
      (dirichletShiftedFlux f h v 0 z * conj (dirD v 1 z) +
        dirichletShiftedFlux f h v 1 z * conj (dirD v Complex.I z)).re := by
  let d : ℝ := deriv f (z + (h : ℂ)).re
  let x := dirD v 1 z
  let y := dirD v Complex.I z
  have hpair : ((x - (d : ℂ) * y) * conj x +
      (-(d : ℂ) * x + (1 + (d : ℂ) ^ 2) * y) * conj y).re =
      ‖x - (d : ℂ) * y‖ ^ 2 + ‖y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm, Complex.normSq_apply]
    simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
    ring
  simp only [dirichletShiftedFlux, Matrix.cons_val_zero, Matrix.cons_val_one, dirichletGraphSlope]
  change (‖x‖ ^ 2 + ‖y‖ ^ 2) / (2 * (1 + (K : ℝ) ^ 2)) ≤
    ((x - (d : ℂ) * y) * conj x + (-(d : ℂ) * x + (1 + (d : ℂ) ^ 2) * y) * conj y).re
  rw [hpair]
  have hd : |d| ≤ (K : ℝ) := by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hLip (x₀ := (z + (h : ℂ)).re)
  have hd₂ : d ^ 2 ≤ (K : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg d) K.coe_nonneg).mpr hd
  let a := ‖x - (d : ℂ) * y‖
  let b := ‖y‖
  have htri : ‖x‖ ≤ a + |d| * b := by
    calc ‖x‖ = ‖(x - (d : ℂ) * y) + (d : ℂ) * y‖ := by congr 1; abel
      _ ≤ a + ‖(d : ℂ) * y‖ := norm_add_le _ _
      _ = a + |d| * b := by simp [b, norm_mul]
  have hsq : ‖x‖ ^ 2 ≤ (a + |d| * b) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htri
  refine (div_le_iff₀ (by positivity)).mpr ?_
  have hlow : (a + |d| * b) ^ 2 + b ^ 2 ≤ 2 * (1 + d ^ 2) * (a ^ 2 + b ^ 2) := by
    have : |d| ^ 2 = d ^ 2 := sq_abs d
    nlinarith [sq_nonneg (a - |d| * b), sq_nonneg (d * a), sq_nonneg (d * b)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hd₂) (add_nonneg (sq_nonneg a) (sq_nonneg b))]

theorem dirichletShiftedFlux_norm_sum_bound {f : ℝ → ℝ} {K : NNReal}
    (hLip : LipschitzWith K f) (h : ℝ) (v : ℂ → ℂ) (z : ℂ) :
    ‖dirichletShiftedFlux f h v 0 z‖ + ‖dirichletShiftedFlux f h v 1 z‖ ≤
      2 * (2 * (1 + (K : ℝ) ^ 2)) * (‖dirD v 1 z‖ + ‖dirD v Complex.I z‖) := by
  let M := 2 * (1 + (K : ℝ) ^ 2)
  let d := dirichletGraphSlope f (z + (h : ℂ))
  let x := dirD v 1 z
  let y := dirD v Complex.I z
  have hd : ‖d‖ ≤ (K : ℝ) := by
    simpa only [d, dirichletGraphSlope, Complex.norm_real] using
      norm_deriv_le_of_lipschitz hLip (x₀ := (z + (h : ℂ)).re)
  have h₁ : 1 ≤ M := by dsimp [M]; nlinarith [sq_nonneg (K : ℝ)]
  have hdM : ‖d‖ ≤ M := hd.trans (by dsimp [M]; nlinarith [sq_nonneg ((K : ℝ) - 1)])
  have haM : ‖(1 : ℂ) + d ^ 2‖ ≤ M :=
    calc ‖(1 : ℂ) + d ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖d ^ 2‖ := norm_add_le _ _
      _ ≤ 1 + (K : ℝ) ^ 2 := by
          rw [norm_one, norm_pow]
          exact add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hd 2)
      _ ≤ M := by dsimp [M]; nlinarith [sq_nonneg (K : ℝ)]
  have hx : ‖x - d * y‖ ≤ M * (‖x‖ + ‖y‖) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (norm_nonneg x),
      mul_le_mul_of_nonneg_right hdM (norm_nonneg y)]
  have hy : ‖-d * x + (1 + d ^ 2) * y‖ ≤ M * (‖x‖ + ‖y‖) := by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, norm_neg]
    nlinarith [mul_le_mul_of_nonneg_right hdM (norm_nonneg x),
      mul_le_mul_of_nonneg_right haM (norm_nonneg y)]
  change ‖x - d * y‖ + ‖-d * x + (1 + d ^ 2) * y‖ ≤ 2 * M * (‖x‖ + ‖y‖)
  linarith

theorem dirichletShiftedFlux_memLp {U : Set ℂ} {f : ℝ → ℝ} {K : NNReal}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hLip : LipschitzWith K f) (h : ℝ) {v : ℂ → ℂ}
    (hg : ∀ i : Fin 2, MemLp (dirD v (coordDir i)) 2 (volume.restrict U)) (i : Fin 2) :
    MemLp (dirichletShiftedFlux f h v i) 2 (volume.restrict U) := by
  let d : ℂ → ℂ := fun z => dirichletGraphSlope f (z + (h : ℂ))
  have hd : Continuous d := (dirichletGraphSlope_contDiff hf).continuous.comp (continuous_id.add continuous_const)
  have hdb (z : ℂ) : ‖d z‖ ≤ (K : ℝ) := by
    simpa only [d, dirichletGraphSlope, Complex.norm_real] using
      norm_deriv_le_of_lipschitz hLip (x₀ := (z + (h : ℂ)).re)
  have hdx : MemLp (dirD v 1) 2 (volume.restrict U) := by simpa only [coordDir, Matrix.cons_val_zero] using hg 0
  have hdy : MemLp (dirD v Complex.I) 2 (volume.restrict U) := by
    simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hg 1
  fin_cases i
  · exact hdx.sub (dirichlet_bounded_mul_memLp hd.aestronglyMeasurable hdb hdy)
  · exact (dirichlet_bounded_mul_memLp hd.neg.aestronglyMeasurable
      (fun z => by rw [Pi.neg_apply, norm_neg]; exact hdb z) hdx).add
      (dirichlet_bounded_mul_memLp (a := fun z : ℂ => 1 + d z ^ 2) (C := 1 + (K : ℝ) ^ 2)
        (continuous_const.add (hd.pow 2)).aestronglyMeasurable
        (fun z => by
          refine (norm_add_le (1 : ℂ) (d z ^ 2)).trans ?_
          rw [norm_one, norm_pow]
          exact add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) (hdb z) 2)) hdy)

private theorem dirichlet_localized_energy_absorption {M B : ℝ}
    (hM : 0 < M) (hB : 0 ≤ B) (η α β v x y F₀ F₁ C₀ C₁ G : ℂ)
    (hη : ‖η‖ ≤ 1) (hα : ‖α‖ ≤ B) (hβ : ‖β‖ ≤ B)
    (hcoer : (‖x‖ ^ 2 + ‖y‖ ^ 2) / M ≤ (F₀ * conj x + F₁ * conj y).re)
    (hF : ‖F₀‖ + ‖F₁‖ ≤ 2 * M * (‖x‖ + ‖y‖)) :
    let ρ := η * conj η
    let b₀ := α * conj η + η * conj α
    let b₁ := β * conj η + η * conj β
    let L := (F₀ + C₀) * (ρ * conj x + b₀ * conj v) +
      (F₁ + C₁) * (ρ * conj y + b₁ * conj v)
    ‖η‖ ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) / (2 * M) ≤
      (L - G * ρ * conj v).re + ‖G‖ ^ 2 +
        (4 * M + 2 * B ^ 2) * (‖C₀‖ ^ 2 + ‖C₁‖ ^ 2) +
        (32 * B ^ 2 * M ^ 3 + 2) * ‖v‖ ^ 2 := by
  let ρ := η * conj η
  let b₀ := α * conj η + η * conj α
  let b₁ := β * conj η + η * conj β
  let L := (F₀ + C₀) * (ρ * conj x + b₀ * conj v) + (F₁ + C₁) * (ρ * conj y + b₁ * conj v)
  let X := ‖x‖ + ‖y‖
  let c := ‖C₀‖ + ‖C₁‖
  let Y := ‖η‖ * X
  let T := ‖η‖ ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)
  let S := c + 4 * B * M * ‖v‖
  let main := ρ * (F₀ * conj x + F₁ * conj y)
  let err := (F₀ * b₀ + F₁ * b₁) * conj v + ρ * (C₀ * conj x + C₁ * conj y) +
    (C₀ * b₀ + C₁ * b₁) * conj v - G * ρ * conj v
  have hX₀ : 0 ≤ X := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hc₀ : 0 ≤ c := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hρnorm : ‖ρ‖ = ‖η‖ ^ 2 := by simp only [ρ, norm_mul, norm_conj, pow_two]
  have hρ : ρ = ((‖η‖ ^ 2 : ℝ) : ℂ) := by simpa only [← Complex.ofReal_pow] using Complex.mul_conj' η
  have hb₀ : ‖b₀‖ ≤ 2 * B * ‖η‖ :=
    (norm_add_le _ _).trans (by simp only [norm_mul, norm_conj]; nlinarith [norm_nonneg η])
  have hb₁ : ‖b₁‖ ≤ 2 * B * ‖η‖ :=
    (norm_add_le _ _).trans (by simp only [norm_mul, norm_conj]; nlinarith [norm_nonneg η])
  have hηsq : ‖η‖ ^ 2 ≤ ‖η‖ := by nlinarith only [hη, norm_nonneg η]
  have hAerr : ‖(F₀ * b₀ + F₁ * b₁) * conj v‖ ≤ 4 * B * M * Y * ‖v‖ := by
    rw [norm_mul, norm_conj]
    calc _ ≤ (‖F₀ * b₀‖ + ‖F₁ * b₁‖) * ‖v‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (‖F₀‖ * (2 * B * ‖η‖) + ‖F₁‖ * (2 * B * ‖η‖)) * ‖v‖ := by simp only [norm_mul]; gcongr
      _ = 2 * B * ‖η‖ * (‖F₀‖ + ‖F₁‖) * ‖v‖ := by ring
      _ ≤ 2 * B * ‖η‖ * (2 * M * X) * ‖v‖ := by gcongr
      _ = _ := by dsimp [Y]; ring
  have hCdot : ‖C₀ * conj x + C₁ * conj y‖ ≤ c * X := by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, norm_conj]; dsimp [c, X]
    nlinarith [mul_nonneg (norm_nonneg C₀) (norm_nonneg y), mul_nonneg (norm_nonneg C₁) (norm_nonneg x)]
  have hCmain : ‖ρ * (C₀ * conj x + C₁ * conj y)‖ ≤ c * Y := by
    rw [norm_mul, hρnorm]
    calc _ ≤ ‖η‖ ^ 2 * (c * X) := mul_le_mul_of_nonneg_left hCdot (sq_nonneg _)
      _ ≤ ‖η‖ * (c * X) := mul_le_mul_of_nonneg_right hηsq (mul_nonneg hc₀ hX₀)
      _ = _ := by dsimp [Y]; ring
  have hCerr : ‖(C₀ * b₀ + C₁ * b₁) * conj v‖ ≤ 2 * B * c * ‖v‖ := by
    rw [norm_mul, norm_conj]
    calc _ ≤ (‖C₀ * b₀‖ + ‖C₁ * b₁‖) * ‖v‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (‖C₀‖ * (2 * B * ‖η‖) + ‖C₁‖ * (2 * B * ‖η‖)) * ‖v‖ := by simp only [norm_mul]; gcongr
      _ = 2 * B * c * ‖η‖ * ‖v‖ := by dsimp [c]; ring
      _ ≤ 2 * B * c * 1 * ‖v‖ := by gcongr
      _ = _ := by ring
  have hGerr : ‖G * ρ * conj v‖ ≤ ‖G‖ * ‖v‖ := by
    rw [norm_mul, norm_mul, hρnorm, norm_conj]
    have hηsq₁ : ‖η‖ ^ 2 ≤ 1 := hηsq.trans hη
    calc _ ≤ ‖G‖ * 1 * ‖v‖ := by gcongr
      _ = _ := by ring
  have herr : ‖err‖ ≤ Y * S + 2 * B * c * ‖v‖ + ‖G‖ * ‖v‖ := by
    calc _ ≤ ‖(F₀ * b₀ + F₁ * b₁) * conj v + ρ * (C₀ * conj x + C₁ * conj y) +
            (C₀ * b₀ + C₁ * b₁) * conj v‖ + ‖G * ρ * conj v‖ := norm_sub_le _ _
      _ ≤ ((‖(F₀ * b₀ + F₁ * b₁) * conj v‖ + ‖ρ * (C₀ * conj x + C₁ * conj y)‖) +
            ‖(C₀ * b₀ + C₁ * b₁) * conj v‖) + ‖G * ρ * conj v‖ := by
            gcongr; exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ((4 * B * M * Y * ‖v‖ + c * Y) + 2 * B * c * ‖v‖) + ‖G‖ * ‖v‖ := by gcongr
      _ = _ := by dsimp [S]; ring
  have hYsq : Y ^ 2 ≤ 2 * T := by
    dsimp [Y, X, T]
    have hxy : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by nlinarith only [sq_nonneg (‖x‖ - ‖y‖)]
    convert mul_le_mul_of_nonneg_left hxy (sq_nonneg ‖η‖) using 1 <;> ring
  have hSsq : S ^ 2 ≤ 2 * c ^ 2 + 32 * B ^ 2 * M ^ 2 * ‖v‖ ^ 2 := by
    dsimp [S]; nlinarith only [sq_nonneg (c - 4 * B * M * ‖v‖)]
  have hfourM : 0 < 4 * M := by positivity
  have hYoung : Y * S ≤ Y ^ 2 / (4 * M) + M * S ^ 2 := by
    calc Y * S = (4 * M * Y * S) / (4 * M) := by field_simp [hM.ne']
      _ ≤ (Y ^ 2 + 4 * M ^ 2 * S ^ 2) / (4 * M) :=
        div_le_div_of_nonneg_right (by nlinarith only [sq_nonneg (Y - 2 * M * S)]) hfourM.le
      _ = _ := by field_simp [hM.ne']
  have hYoung' : Y * S ≤ T / (2 * M) + 2 * M * c ^ 2 + 32 * B ^ 2 * M ^ 3 * ‖v‖ ^ 2 := by
    calc _ ≤ Y ^ 2 / (4 * M) + M * S ^ 2 := hYoung
      _ ≤ (2 * T) / (4 * M) + M * (2 * c ^ 2 + 32 * B ^ 2 * M ^ 2 * ‖v‖ ^ 2) :=
        add_le_add (div_le_div_of_nonneg_right hYsq hfourM.le) (mul_le_mul_of_nonneg_left hSsq hM.le)
      _ = _ := by field_simp [hM.ne']; ring
  have hBc : 2 * B * c * ‖v‖ ≤ B ^ 2 * c ^ 2 + ‖v‖ ^ 2 := by nlinarith only [sq_nonneg (B * c - ‖v‖)]
  have hGv : ‖G‖ * ‖v‖ ≤ ‖G‖ ^ 2 + ‖v‖ ^ 2 := by
    nlinarith only [sq_nonneg (‖G‖ - ‖v‖), sq_nonneg ‖G‖, sq_nonneg ‖v‖]
  have hcsq : c ^ 2 ≤ 2 * (‖C₀‖ ^ 2 + ‖C₁‖ ^ 2) := by dsimp [c]; nlinarith only [sq_nonneg (‖C₀‖ - ‖C₁‖)]
  have herr' : ‖err‖ ≤ T / (2 * M) + ‖G‖ ^ 2 +
      (4 * M + 2 * B ^ 2) * (‖C₀‖ ^ 2 + ‖C₁‖ ^ 2) + (32 * B ^ 2 * M ^ 3 + 2) * ‖v‖ ^ 2 := by
    have hcBound := mul_le_mul_of_nonneg_left hcsq (by positivity : 0 ≤ 2 * M + B ^ 2)
    linarith only [herr, hYoung', hBc, hGv, hcBound]
  have hmain : T / M ≤ main.re := by
    rw [show main = ((‖η‖ ^ 2 : ℝ) : ℂ) * (F₀ * conj x + F₁ * conj y) by rw [← hρ]]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc _ = ‖η‖ ^ 2 * ((‖x‖ ^ 2 + ‖y‖ ^ 2) / M) := by dsimp [T]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoer (sq_nonneg _)
  have hmainBound : main.re ≤ (L - G * ρ * conj v).re + ‖err‖ := by
    rw [show L - G * ρ * conj v = main + err by dsimp [L, main, err]; ring, Complex.add_re]
    have h := Complex.re_le_norm (-err); simp only [Complex.neg_re, norm_neg] at h; linarith only [h]
  have hTsplit : T / M = T / (2 * M) + T / (2 * M) := by field_simp [hM.ne']; ring
  change T / (2 * M) ≤ _; linarith only [hmain, hmainBound, herr', hTsplit]

private def dirichletCutoffWeight (η : smoothTraceTests) : smoothTraceTests :=
  ⟨fun z => η z * conj (η z),
    ⟨η.property.1.mul (Complex.conjCLE.contDiff.comp η.property.1),
      η.property.2.1.mul_right, subset_univ _⟩⟩

theorem dirichlet_localized_boundary_energy_bound {a b M B : ℝ}
    (hb : 0 < b) (hM : 0 < M) (hB : 0 ≤ B)
    (η : smoothTraceTests)
    (hηsupp : tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b})
    (hη : ∀ z : ℂ, ‖η z‖ ≤ 1)
    (hηgrad : ∀ z : ℂ, ∀ i : Fin 2, ‖dirD (η : ℂ → ℂ) (coordDir i) z‖ ≤ B)
    {v : ℂ → ℂ} (hc : ContinuousOn v (smoothDirichletClosedHalfBox a b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b))
    (hz : ∀ x : ℝ, |x| < a → v (x : ℂ) = 0)
    (hm : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hg : ∀ i : Fin 2, MemLp (dirD v (coordDir i)) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    {F C : Fin 2 → ℂ → ℂ} {G : ℂ → ℂ}
    (hF : ∀ i : Fin 2, MemLp (F i) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hC : ∀ i : Fin 2, MemLp (C i) 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hG : MemLp G 2 (volume.restrict (smoothDirichletHalfBox a b)))
    (hcoer : ∀ z ∈ smoothDirichletHalfBox a b,
      (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2) / M ≤
        (F 0 z * conj (dirD v 1 z) + F 1 z * conj (dirD v Complex.I z)).re)
    (hFbound : ∀ z ∈ smoothDirichletHalfBox a b,
      ‖F 0 z‖ + ‖F 1 z‖ ≤ 2 * M * (‖dirD v 1 z‖ + ‖dirD v Complex.I z‖))
    (hweak : ∀ φ : ℂ → ℂ, TestFunction (smoothDirichletHalfBox a b) φ →
      (∫ z in smoothDirichletHalfBox a b, ∑ i : Fin 2,
        (F i z + C i z) * dirD φ (coordDir i) z) =
      ∫ z in smoothDirichletHalfBox a b, G z * φ z) :
    (∫ z in smoothDirichletHalfBox a b,
      ‖η z‖ ^ 2 * (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2)) / (2 * M) ≤
      (∫ z in smoothDirichletHalfBox a b, ‖G z‖ ^ 2) +
        (4 * M + 2 * B ^ 2) *
          (∫ z in smoothDirichletHalfBox a b, ‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
        (32 * B ^ 2 * M ^ 3 + 2) *
          (∫ z in smoothDirichletHalfBox a b, ‖v z‖ ^ 2) := by
  let U := smoothDirichletHalfBox a b
  let μ := volume.restrict U
  let φ : ℂ → ℂ := fun z => dirichletCutoffWeight η z * conj (v z)
  let J : ℂ → ℝ := fun z => ‖η z‖ ^ 2 * (‖dirD v 1 z‖ ^ 2 + ‖dirD v Complex.I z‖ ^ 2)
  let R : ℂ → ℂ := fun z => (∑ i : Fin 2, (F i z + C i z) * dirD φ (coordDir i) z) - G z * φ z
  have hU : IsOpen U := isOpen_smoothDirichletHalfBox a b
  have hvc : ContinuousOn (fun z => conj (v z)) (smoothDirichletClosedHalfBox a b) :=
    Complex.conjCLE.continuous.comp_continuousOn hc
  have hvs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => conj (v z)) U :=
    Complex.conjCLE.contDiff.comp_contDiffOn hs
  have hvz : ∀ x : ℝ, |x| < a → conj (v (x : ℂ)) = 0 := fun x hx => by simp [hz x hx]
  have hvg (i : Fin 2) : MemLp (dirD (fun z => conj (v z)) (coordDir i)) 2 μ := by
    refine (hg i).star.ae_eq ?_
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hzU
    have hdv := (hs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
    change conj (dirD v (coordDir i) z) = fderiv ℝ (Complex.conjCLE ∘ v) z (coordDir i)
    rw [(Complex.conjCLE.hasFDerivAt.comp z hdv.hasFDerivAt).fderiv]; rfl
  have hφ : MemLp φ 2 μ := dirichlet_localized_memLp (dirichletCutoffWeight η) hm.star
  have hφg (i : Fin 2) : MemLp (dirD φ (coordDir i)) 2 μ :=
    dirichlet_localized_gradient_memLp hU (dirichletCutoffWeight η) hvs hm.star (hvg i)
  have heq : (∫ z, ∑ i : Fin 2, (F i z + C i z) * dirD φ (coordDir i) z ∂μ) = ∫ z, G z * φ z ∂μ :=
    dirichlet_weak_equation_localized_zero_boundary_test hb (dirichletCutoffWeight η)
      (tsupport_mul_subset_left.trans hηsupp) hvc hvs hvz hm.star hvg
      (fun i => (hF i).add (hC i)) hG hweak
  have hFluxInt : Integrable (fun z => ∑ i : Fin 2, (F i z + C i z) * dirD φ (coordDir i) z) μ :=
    integrable_finset_sum _ fun i _ => ((hF i).add (hC i)).integrable_mul (hφg i)
  have hLoadInt : Integrable (fun z => G z * φ z) μ := hG.integrable_mul hφ
  have hRi : Integrable R μ := hFluxInt.sub hLoadInt
  have hRzero : (∫ z, (R z).re ∂μ) = 0 := by
    change (∫ z, RCLike.re (R z) ∂μ) = 0
    rw [integral_re hRi, show (∫ z, R z ∂μ) = 0 by dsimp [R]; rw [integral_sub hFluxInt hLoadInt, heq, sub_self]]
    simp
  have hηDx := dirichlet_localized_memLp η
    (by simpa only [coordDir, Matrix.cons_val_zero] using hg 0 : MemLp (dirD v 1) 2 μ)
  have hηDy := dirichlet_localized_memLp η
    (by simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hg 1 : MemLp (dirD v Complex.I) 2 μ)
  have hJ : Integrable J μ :=
    ((hηDx.integrable_norm_pow (by norm_num)).add (hηDy.integrable_norm_pow (by norm_num))).congr
      (Eventually.of_forall fun z => by
        change ‖η z * dirD v 1 z‖ ^ 2 + ‖η z * dirD v Complex.I z‖ ^ 2 = J z
        simp only [J, norm_mul, mul_pow]; ring)
  have hGsq := hG.integrable_norm_pow (by norm_num)
  have hCsq : Integrable (fun z => ‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) μ :=
    ((hC 0).integrable_norm_pow (by norm_num)).add ((hC 1).integrable_norm_pow (by norm_num))
  have hvsq := hm.integrable_norm_pow (by norm_num)
  have hRre : Integrable (fun z => (R z).re) μ := hRi.re
  have hRG : Integrable (fun z => (R z).re + ‖G z‖ ^ 2) μ := hRre.add hGsq
  have hRGC : Integrable (fun z => (R z).re + ‖G z‖ ^ 2 + (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2)) μ :=
    hRG.add (hCsq.const_mul (4 * M + 2 * B ^ 2))
  have hright : Integrable (fun z => (R z).re + ‖G z‖ ^ 2 + (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
      (32 * B ^ 2 * M ^ 3 + 2) * ‖v z‖ ^ 2) μ :=
    hRGC.add (hvsq.const_mul (32 * B ^ 2 * M ^ 3 + 2))
  have hprod_dir (z : ℂ) (hv_at : DifferentiableAt ℝ v z) (w : ℂ) :
      dirD φ w z = dirichletCutoffWeight η z * conj (dirD v w z) +
        (dirD (η : ℂ → ℂ) w z * conj (η z) + η z * conj (dirD (η : ℂ → ℂ) w z)) * conj (v z) := by
    have hη_fd := ((η.property.1.differentiable (by simp)) z).hasFDerivAt
    have hw_fd : HasFDerivAt (dirichletCutoffWeight η : ℂ → ℂ) _ z :=
      hη_fd.mul (Complex.conjCLE.hasFDerivAt.comp z hη_fd)
    have hprod_fd := (hw_fd.mul (Complex.conjCLE.hasFDerivAt.comp z hv_at.hasFDerivAt)).fderiv
    change fderiv ℝ ((dirichletCutoffWeight η : ℂ → ℂ) * (Complex.conjCLE ∘ v)) z w = _
    rw [hprod_fd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_apply,
      Function.comp_apply, Complex.conjCLE_apply, smul_eq_mul, dirD]
    ring
  have hmono : (∫ z, J z / (2 * M) ∂μ) ≤
      ∫ z, (R z).re + ‖G z‖ ^ 2 + (4 * M + 2 * B ^ 2) * (‖C 0 z‖ ^ 2 + ‖C 1 z‖ ^ 2) +
        (32 * B ^ 2 * M ^ 3 + 2) * ‖v z‖ ^ 2 ∂μ := by
    refine integral_mono_ae (hJ.div_const (2 * M)) hright ?_
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hzU
    have hdv := (hs.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)
    have hp := dirichlet_localized_energy_absorption hM hB (η z)
      (dirD (η : ℂ → ℂ) 1 z) (dirD (η : ℂ → ℂ) Complex.I z)
      (v z) (dirD v 1 z) (dirD v Complex.I z) (F 0 z) (F 1 z) (C 0 z) (C 1 z) (G z)
      (hη z) (by simpa only [coordDir, Matrix.cons_val_zero] using hηgrad z 0)
      (by simpa only [coordDir, Matrix.cons_val_one, Matrix.cons_val_zero] using hηgrad z 1)
      (hcoer z hzU) (hFbound z hzU)
    have hRpoint : R z =
        (F 0 z + C 0 z) * (dirichletCutoffWeight η z * conj (dirD v 1 z) +
          (dirD (η : ℂ → ℂ) 1 z * conj (η z) + η z * conj (dirD (η : ℂ → ℂ) 1 z)) * conj (v z)) +
        (F 1 z + C 1 z) * (dirichletCutoffWeight η z * conj (dirD v Complex.I z) +
          (dirD (η : ℂ → ℂ) Complex.I z * conj (η z) + η z * conj (dirD (η : ℂ → ℂ) Complex.I z)) * conj (v z)) -
        G z * dirichletCutoffWeight η z * conj (v z) := by
      dsimp only [R]; rw [Fin.sum_univ_two]
      simp only [coordDir, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hprod_dir z hdv 1, hprod_dir z hdv Complex.I]; dsimp only [φ]; ring
    dsimp only [J]
    rw [hRpoint]
    exact hp
  rw [integral_add hRGC (hvsq.const_mul _), integral_add hRG (hCsq.const_mul _),
    integral_add hRre hGsq, hRzero, zero_add, integral_const_mul, integral_const_mul] at hmono
  simpa only [J, div_eq_mul_inv, integral_mul_const] using hmono

theorem exists_dirichlet_boundary_energy_cutoff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ r : ℝ, 0 < r ∧ r < a ∧ r < b ∧ ∃ (η : smoothTraceTests) (B : ℝ),
      0 ≤ B ∧ tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b} ∧
      (∀ z : ℂ, ‖η z‖ ≤ 1) ∧
      (∀ z : ℂ, ∀ i : Fin 2, ‖dirD (η : ℂ → ℂ) (coordDir i) z‖ ≤ B) ∧
      ∀ z ∈ smoothDirichletHalfBox (r / 2) (r / 2), η z = 1 := by
  let r := min a b / 8
  have hr : 0 < r := div_pos (lt_min ha hb) (by norm_num)
  have h2a : 2 * r < a := by dsimp [r]; linarith [min_le_left a b, lt_min ha hb]
  have h2b : 2 * r < b := by dsimp [r]; linarith [min_le_right a b, lt_min ha hb]
  let κ : ContDiffBump (0 : ℂ) := ⟨r, 2 * r, hr, by linarith⟩
  let η : smoothTraceTests := ⟨fun z => (κ z : ℂ),
    ⟨Complex.ofRealCLM.contDiff.comp κ.contDiff,
      κ.hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero,
      subset_univ _⟩⟩
  have hηsupp : tsupport (η : ℂ → ℂ) ⊆ {z : ℂ | |z.re| < a ∧ z.im < b} := fun z hz => by
    have hzκ : z ∈ closedBall (0 : ℂ) (2 * r) := by
      have hsub : tsupport (fun w => (κ w : ℂ)) ⊆ closedBall (0 : ℂ) κ.rOut := by
        rw [← κ.tsupport_eq]
        exact tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero (κ : ℂ → ℝ)
      exact hsub hz
    have hzn : ‖z‖ ≤ 2 * r := by simpa only [mem_closedBall, dist_zero_right] using hzκ
    exact ⟨((Complex.abs_re_le_norm z).trans hzn).trans_lt h2a,
      ((le_abs_self z.im).trans ((Complex.abs_im_le_norm z).trans hzn)).trans_lt h2b⟩
  have hη (z : ℂ) : ‖η z‖ ≤ 1 := by
    change ‖(κ z : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (κ.nonneg' z)]
    exact κ.le_one
  have hηone (z : ℂ) (hz : z ∈ smoothDirichletHalfBox (r / 2) (r / 2)) : η z = 1 := by
    have hzn : ‖z‖ ≤ r := (Complex.norm_le_abs_re_add_abs_im z).trans
      (by rw [abs_of_pos hz.2.1]; linarith [hz.1, hz.2.2])
    change (κ z : ℂ) = 1
    rw [κ.one_of_mem_closedBall (by simpa only [mem_closedBall, dist_zero_right] using hzn), Complex.ofReal_one]
  have h₀ := η.property.dirD 1
  have h₁ := η.property.dirD Complex.I
  obtain ⟨B₀, hB₀⟩ := h₀.2.1.exists_bound_of_continuous h₀.1.continuous
  obtain ⟨B₁, hB₁⟩ := h₁.2.1.exists_bound_of_continuous h₁.1.continuous
  let B := max 0 (max B₀ B₁)
  refine ⟨r, hr, by linarith, by linarith, η, B, le_max_left _ _, hηsupp, hη, fun z i => ?_, hηone⟩
  fin_cases i
  · exact (hB₀ z).trans ((le_max_left B₀ B₁).trans (le_max_right 0 _))
  · exact (hB₁ z).trans ((le_max_right B₀ B₁).trans (le_max_right 0 _))

end PolyaNeumann
end
