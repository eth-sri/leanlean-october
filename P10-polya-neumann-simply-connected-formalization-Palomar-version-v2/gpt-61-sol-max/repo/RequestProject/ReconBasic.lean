module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.FixedSpace
public import RequestProject.ChainRule
public import RequestProject.WeakCompact
public import RequestProject.GreenWinding

/-!
# Basic notions for the Cauchy reconstruction (Lemma 4.8)

* `lap φ` : the Laplacian `∂ₓ² φ + ∂ᵧ² φ` written with real Fréchet derivatives;
* `dbar F` : the Wirtinger derivative `∂̄F = (∂ₓF + i ∂ᵧF)/2`;
* `ePlane ξ` : the Fourier character `z ↦ e^{-2πi⟨z, ξ⟩}`;
* `doubleLayer γ h φ` : the double-layer pairing `∫₀^{2π} h(θ) Dφ(γ(θ))(-iγ'(θ)) dθ`;
* `IsWeakGradOn D w g` : `g` is a weak gradient of `w` on the open set `D`, tested against
  smooth compactly supported functions with support in `D` (integrals over `ℂ`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-- The directional derivative `z ↦ Dφ(z) v`. -/
def dirD (φ : PlaneMap) v  := fun z => fderiv ℝ φ z v

/-- The Laplacian `∂ₓ²φ + ∂ᵧ²φ`. -/
def lap φ  := fun z => dirD (dirD φ 1) 1 z + dirD (dirD φ Complex.I) Complex.I z

/-- The Wirtinger derivative `∂̄F = (∂ₓF + i ∂ᵧF)/2`. -/
def dbar F z  := (fderiv ℝ F z 1 + Complex.I * fderiv ℝ F z Complex.I) / 2

/-- The Fourier character `z ↦ e^{-2πi⟨z, ξ⟩}` (with `⟨z, ξ⟩ = Re(conj z · ξ)`). -/
def ePlane (ξ z : ℂ)  := Complex.exp (-(2 * π * Complex.I) * ((conj z * ξ).re : ℂ))

/-- The double-layer pairing `μ_h(φ) = ∫₀^{2π} h(θ) Dφ(γ(θ))(-iγ'(θ)) dθ` of a boundary density
`h` (in the parameter `θ`) with a smooth function `φ`. -/
def doubleLayer (γ h : ComplexCurve) φ  :=
  ∫ θ in (0 : ℝ)..circlePeriod, h θ * fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))

/-- `g` is a weak gradient of `w` on `D`: `∫ w ∂ᵢφ = -∫ gᵢ φ` for every smooth compactly
supported `φ` with support in `D`. -/
def IsWeakGradOn D (w : PlaneMap) (g : Coord → PlaneMap)  :=
  ∀ φ : PlaneMap, TestFunction D φ → ∀ i : Coord,
    ∫ z, w z * fderiv ℝ φ z (coordDir i) = -∫ z, g i z * φ z

/-! ### Test functions -/

section
variable {D } {φ } (hφ : TestFunction D φ)

section
include D φ hφ

/-- A smooth compactly supported function is in every `Lᵖ`. -/
lemma TestFunction.memLp' p
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] : MemLp φ p μ :=
  (hφ.1.continuous).memLp_of_hasCompactSupport hφ.2.1



lemma TestFunction.univ' :
    TestFunction univ φ := (⟨hφ.left, ⟨hφ.right.left, LE.le.trans hφ.right.right (subset_univ D)⟩⟩)

/-- Directional derivatives of test functions are test functions. -/
lemma TestFunction.dirD v :
    TestFunction D (dirD φ v) := (⟨ContDiff.clm_apply (ContDiff.fderiv_right hφ.left le_rfl) contDiff_const, ⟨HasCompactSupport.fderiv_apply ℝ hφ.right.left v, LE.le.trans (tsupport_fderiv_apply_subset ℝ v) hφ.right.right⟩⟩)

end


lemma TestFunction.add   (hφ : TestFunction D φ)
    (hψ : TestFunction D ψ) : TestFunction D (fun z => φ z + ψ z) :=
  ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, (tsupport_add φ ψ).trans (union_subset hφ.2.2 hψ.2.2)⟩

section
include D φ hφ

lemma TestFunction.const_mul c :
    TestFunction D (fun z => c * φ z) :=
  ⟨contDiff_const.mul hφ.1, hφ.2.1.mul_left, (tsupport_mul_subset_right).trans hφ.2.2⟩

/-- The Laplacian of a test function is a test function. -/
lemma TestFunction.lap :
    TestFunction D (lap φ) :=
  ((hφ.dirD 1).dirD 1).add ((hφ.dirD Complex.I).dirD Complex.I)

/-- `Δφ + Eφ` is a test function. -/
lemma TestFunction.helm (E : ℝ) :
    TestFunction D (fun z => PolyaNeumann.lap φ z + E * φ z) :=
  hφ.lap.add (hφ.const_mul _)

/-- Complex conjugates of test functions are test functions. -/
lemma TestFunction.conj :
    TestFunction D (fun z => conj (φ z)) := by
  refine ⟨Complex.conjCLE.contDiff.comp hφ.1, hφ.2.1.comp_left (by simp), ?_⟩
  exact (tsupport_comp_subset (g := conj) (by simp) φ).trans hφ.2.2

end


end


lemma dirD_conj  (hφ : ContDiff ℝ 1 φ) v z :
    dirD (fun z => conj (φ z)) v z = conj (dirD φ v z) := by
  unfold dirD
  have := (Complex.conjCLE.hasFDerivAt.comp z
    ((hφ.differentiable one_ne_zero) z).hasFDerivAt).fderiv
  rw [show (fun z => conj (φ z)) = Complex.conjCLE ∘ φ from rfl, this]
  rfl

/-- `L²` functions times test functions are integrable. -/
lemma integrable_mul_test  {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    (hu : MemLp u 2 μ)   (hφ : TestFunction D φ) :
    Integrable (fun z => u z * φ z) μ :=
  hu.integrable_mul (hφ.memLp' 2)

/-- Fundamental lemma of the calculus of variations on an open set, for complex functions. -/
lemma ae_eq_zero_of_integral_mul_test  (hU : IsOpen U) 
    (hf : LocallyIntegrable f volume)
    (h : ∀ φ : PlaneMap, TestFunction U φ → ∫ z, f z * φ z = 0) :
    ∀ᵐ z ∂(volume.restrict U), f z = 0 := by
  have h0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.locallyIntegrableOn U)
    (fun ψ hψ hψc hψs => by
      have ht : TestFunction U (fun w => ((ψ w : ℝ) : ℂ)) :=
        ⟨Complex.ofRealCLM.contDiff.comp hψ, hψc.comp_left Complex.ofReal_zero,
          (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψs⟩
      have e := h _ ht
      simp_rw [Complex.real_smul, mul_comm]
      exact e)
  exact (ae_restrict_iff' hU.measurableSet).mpr h0

/-- A product of bounded Lipschitz functions is Lipschitz. -/
lemma lipschitzWith_mul_of_bounded {f g : PlaneMap}  (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g)  (hCf : ∀ z, ‖f z‖ ≤ Cf) (hCg : ∀ z, ‖g z‖ ≤ Cg) :
    ∃ K : NNReal, LipschitzWith K (fun z => f z * g z) := by
  have hCf0  := (norm_nonneg _).trans (hCf 0)
  have hCg0  := (norm_nonneg _).trans (hCg 0)
  refine ⟨⟨Cf * Kg + Cg * Kf, by positivity⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [e]
  calc ‖f x * (g x - g y) + g y * (f x - f y)‖
      ≤ ‖f x‖ * ‖g x - g y‖ + ‖g y‖ * ‖f x - f y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ Cf * (Kg * ‖x - y‖) + Cg * (Kf * ‖x - y‖) := by
        have h1 := hg.dist_le_mul x y
        have h2 := hf.dist_le_mul x y
        rw [dist_eq_norm, dist_eq_norm] at h1 h2
        gcongr
        · exact hCf x
        · exact hCg y
    _ = (Cf * Kg + Cg * Kf) * ‖x - y‖ := by ring

open scoped ContDiff

theorem dirichlet_contDiffOn_dirD {U } (hU : IsOpen U) {g }
    (hg : RealSmoothOn g U) w :
    RealSmoothOn (dirD g w) U := by
  intro z hz
  exact (((hg.contDiffAt (hU.mem_nhds hz)).fderiv_right
    (m := ∞) le_rfl).clm_apply contDiffAt_const).contDiffWithinAt


theorem dirichlet_dirD_comm {U } (hU : IsOpen U) {u }
    (hs : RealSmoothOn u U) {z } (hz : z ∈ U) v w :
    dirD (dirD u v) w z = dirD (dirD u w) v z := by
  have hu := hs.contDiffAt (hU.mem_nhds hz)
  have hd  :=
    (hu.fderiv_right (m := ∞) le_rfl).differentiableAt (by simp)
  have hD (v w : ℂ) : dirD (dirD u v) w z = fderiv ℝ (fderiv ℝ u) z w v := by
    change fderiv ℝ (fun x => fderiv ℝ u x v) z w = _
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  rw [hD, hD]
  exact (hu.isSymmSndFDerivAt (by
    simp_all)).eq w v


end PolyaNeumann
