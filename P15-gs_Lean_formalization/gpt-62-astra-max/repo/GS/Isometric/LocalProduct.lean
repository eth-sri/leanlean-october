module

public import GS.Isometric.HorizontalModel
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Local horizontal--stabilizer product for shared factors

The derivative of multiplication in the actual shared Cayley coordinates is
addition.  The horizontal/kernel splitting makes this derivative invertible,
so the inverse function theorem supplies the needed local product chart.
No product decomposition of the image is assumed.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS Filter Set
open scoped Topology Manifold
namespace GS.Isometric
section Axes
variable {E F V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

@[fun_prop] private lemma smooth_subtype (S : Submodule ℝ E) : ContDiff ℝ ⊤ (Subtype.val : S → E) := S.subtypeL.contDiff

private lemma axis {f : V → W} (hf : DifferentiableAt ℝ f 0) (D : V →L[ℝ] W) (i : E →L[ℝ] V)
    (h : ∀ x, f (i x) = D (i x)) : (fderiv ℝ f 0).comp i = D.comp i := by
  have hi : HasFDerivAt f (fderiv ℝ f 0) (i 0) := by simpa using hf.hasFDerivAt
  have hd := hi.comp 0 i.hasFDerivAt
  rw [show f ∘ i = D.comp i from funext h] at hd
  exact hd.unique (D.comp i).hasFDerivAt

/-- The derivative of a differentiable map on a product is determined by its axes. -/
private lemma axes {f : E × F → W} (hf : DifferentiableAt ℝ f 0) (D : E × F →L[ℝ] W)
    (hl : ∀ x, f (x,0) = D (x,0)) (hr : ∀ y, f (0,y) = D (0,y)) : HasFDerivAt f D 0 := by
  rw [← ContinuousLinearMap.prod_ext (axis hf D (.inl ℝ E F) hl) (axis hf D (.inr ℝ E F) hr)]
  exact hf.hasFDerivAt
end Axes

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (r l : Layer 𝕜 n) (P : Square 𝕜 n)
local notation "H" => HorizontalModel r l P
local notation "K" => OrbitKernel r l P
local notation "G" => Factors r l
local notation "V" => PairGenerator r l
local instance : NormedSpace ℝ H := Submodule.normedSpace _
local instance : NormedSpace ℝ K := Submodule.normedSpace _
attribute [local irreducible] skewSpace orbitDerivative GS.OverlapGeometry.horizontalComplement

/-- The horizontal/stabilizer product fills a neighbourhood of the identity. -/
lemma product_nhds : map (fun z : H × K => frames z.1.val * frames z.2.val) (𝓝 0) = 𝓝 1 := by
  let w (z : H × K) := frames z.1.val * frames z.2.val
  let c := pairChart r l
  let f := c.symm ∘ w
  have w₀ : w 0 = 1 := by change frames (0:V) * frames 0 = 1; simp only [frames_zero,mul_one]
  have hc : w 0 ∈ c.target := w₀ ▸ ⟨admissible_one,admissible_one⟩
  have hw : Continuous w := by
    have h : Continuous (frames : V → G) := (frame_continuous.comp continuous_fst).prodMk (frame_continuous.comp continuous_snd)
    exact (h.comp (continuous_subtype_val.comp continuous_fst)).mul (h.comp (continuous_subtype_val.comp continuous_snd))
  have hs : ContDiffAt ℝ ⊤ f 0 := by
    have block {s : Layer 𝕜 n} (b d : H × K → Generator s) (hb : ContDiff ℝ ⊤ b) (hd : ContDiff ℝ ⊤ d)
        (b₀ : b 0 = 0) (d₀ : d 0 = 0) : ContDiffAt ℝ ⊤ (fun z => coord s ((frame (b z)).matrix * (frame (d z)).matrix)) 0 := by
      apply (coord_smooth (X := (frame (b 0)).matrix * (frame (d 0)).matrix) (by simp [b₀,d₀,Factor.matrix])).comp (f := fun z => (frame (b z)).matrix * (frame (d z)).matrix) 0
      exact smooth_mul_at (frame_smooth.contDiffAt.comp _ hb.contDiffAt) (frame_smooth.contDiffAt.comp _ hd.contDiffAt)
    have h := (smooth_subtype H).comp (contDiff_fst (F := K))
    have k := (smooth_subtype K).comp (contDiff_snd (E := H))
    exact (block _ _ h.fst k.fst rfl rfl).prodMk (block _ _ h.snd k.snd rfl rfl)
  let e := GS.OverlapGeometry.complementKernelEquiv (orbitDerivative r l P)
  have can (v : V) : c.symm (frames v) = v := c.left_inv ⟨trivial,trivial⟩
  have hd : HasFDerivAt f (e : _ →L[ℝ] _) 0 := by
    apply axes (hs.differentiableAt (by simp))
    · intro v; change c.symm (frames v.val * frames 0) = v.val + 0; simp [can]
    · intro v; change c.symm (frames 0 * frames v.val) = 0 + v.val; simp [can]
  rw [← w₀]
  calc map w (𝓝 0) = map c (map f (𝓝 0)) := by
        rw [Filter.map_map]; apply Filter.map_congr
        filter_upwards [hw.continuousAt.eventually (c.open_target.mem_nhds hc)] with z hz using (c.right_inv hz).symm
       _ = map c (𝓝 (f 0)) := congrArg (map c) ((hs.hasStrictFDerivAt' hd (by simp)).map_nhds_eq_of_equiv (f' := e))
       _ = 𝓝 (w 0) := c.symm.symm_map_nhds_eq hc
end GS.Isometric
