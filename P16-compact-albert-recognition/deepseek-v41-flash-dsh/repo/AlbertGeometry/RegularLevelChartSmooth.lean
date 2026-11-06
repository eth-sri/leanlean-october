/-
The genuine normal-chart derivative is invertible
at every point with nonzero normal derivative. A fixed restriction of the actual
inverse-theorem chart is smooth throughout its actual open level-chart domain.
No inverse, chart jet, metric or curvature conclusion is supplied as input.
-/
module

public import AlbertGeometry.RegularLevelChart
public import AlbertGeometry.LogHessianPositiveNeighborhood
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
public import Mathlib.Tactic.FieldSimp

@[expose] public section
open scoped ContDiff Topology

namespace AlbertGeometry.Cubic
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (P : SymmetricTrilinearForm E)
include P in

/-- The fixed projection is the identity on the actual basepoint tangent kernel. -/
theorem tangentProjection_tangent  (e : E)
    (he : diagonalCubic P.form e = 1) (v : tangentSpace P e) :
    tangentProjection P e he (v : E) = v := by
  have hv : fderiv ℝ (diagonalCubic P.form) e (v : E) = 0 := v.property
  apply Subtype.ext
  simp only [tangentProjection_coe, hv, zero_div, zero_smul, sub_zero]
include P in

/-- The actual normal-chart derivative at an arbitrary ambient point. -/
theorem hasFDerivAt_normalChartMap_at  (e : E)
    (he : diagonalCubic P.form e = 1) (x : E) :
    HasFDerivAt (normalChartMap P e he)
      ((fderiv ℝ (diagonalCubic P.form) x).prod (tangentProjection P e he)) x := by
  have hN := (hasFDerivAt_diagonalCubic P.form x).congr_fderiv
    (fderiv_diagonalCubic P.form x).symm
  exact hN.prodMk (tangentProjection P e he).hasFDerivAt
include P in

/-- The inverse formula uses the actual derivative at x and the fixed tangent
projection at e. It is a function to be proved inverse, not an inverse premise. -/
def normalDerivativeInverse  (e x : E)
    (p : ℝ × tangentSpace P e) : E :=
  (p.2 : E) +
    ((p.1 - fderiv ℝ (diagonalCubic P.form) x (p.2 : E)) /
      fderiv ℝ (diagonalCubic P.form) x e) • e
include P in

theorem normalDerivative_left_inverse  (e x : E)
    (he : diagonalCubic P.form e = 1)
    (hx : fderiv ℝ (diagonalCubic P.form) x e ≠ 0) (w : E) :
    normalDerivativeInverse P e x
      (fderiv ℝ (diagonalCubic P.form) x w, tangentProjection P e he w) = w := by
  have hproj : fderiv ℝ (diagonalCubic P.form) x
      (tangentProjection P e he w : E) =
      fderiv ℝ (diagonalCubic P.form) x w -
        (fderiv ℝ (diagonalCubic P.form) e w / 3) *
          fderiv ℝ (diagonalCubic P.form) x e := by
    simp only [tangentProjection_coe, map_sub, map_smul, smul_eq_mul]
  have hcoef :
      (fderiv ℝ (diagonalCubic P.form) x w -
        fderiv ℝ (diagonalCubic P.form) x (tangentProjection P e he w : E)) /
          fderiv ℝ (diagonalCubic P.form) x e =
        fderiv ℝ (diagonalCubic P.form) e w / 3 := by
    rw [hproj]
    field_simp [hx] <;> ring
  simp only [normalDerivativeInverse]
  rw [hcoef]
  simp only [tangentProjection_coe]
  module
include P in

theorem normalDerivative_right_inverse  (e x : E)
    (he : diagonalCubic P.form e = 1)
    (hx : fderiv ℝ (diagonalCubic P.form) x e ≠ 0)
    (p : ℝ × tangentSpace P e) :
    (fderiv ℝ (diagonalCubic P.form) x (normalDerivativeInverse P e x p),
      tangentProjection P e he (normalDerivativeInverse P e x p)) = p := by
  have hn : fderiv ℝ (diagonalCubic P.form) x
      (normalDerivativeInverse P e x p) = p.1 := by
    simp only [normalDerivativeInverse, map_add, map_smul, smul_eq_mul]
    field_simp [hx] <;> ring
  apply Prod.ext hn
  simp only [normalDerivativeInverse, map_add, map_smul,
    tangentProjection_tangent, tangentProjection_basepoint, smul_zero, add_zero]
include P in

/-- Continuous invertibility of the actual derivative, with proved explicit
inverse laws. No extra inverse or regularity fields are assumptions. -/
def normalDerivativeSplit  (e : E)
    (he : diagonalCubic P.form e = 1) (x : E)
    (hx : fderiv ℝ (diagonalCubic P.form) x e ≠ 0) :
    E ≃L[ℝ] ℝ × tangentSpace P e :=
  { ((fderiv ℝ (diagonalCubic P.form) x).prod
      (tangentProjection P e he)).toLinearMap with
    invFun := normalDerivativeInverse P e x
    left_inv := normalDerivative_left_inverse P e x he hx
    right_inv := normalDerivative_right_inverse P e x he hx
    continuous_toFun :=
      (fderiv ℝ (diagonalCubic P.form) x).continuous.prodMk
        (tangentProjection P e he).continuous
    continuous_invFun :=
      (continuous_subtype_val.comp continuous_snd).add
        (((continuous_fst.sub
          ((fderiv ℝ (diagonalCubic P.form) x).continuous.comp
            (continuous_subtype_val.comp continuous_snd))).div_const
          (fderiv ℝ (diagonalCubic P.form) x e)).smul continuous_const) }
include P in

@[simp] theorem normalDerivativeSplit_apply 
    (e : E) (he : diagonalCubic P.form e = 1) (x : E)
    (hx : fderiv ℝ (diagonalCubic P.form) x e ≠ 0) (w : E) :
    normalDerivativeSplit P e he x hx w =
      (fderiv ℝ (diagonalCubic P.form) x w, tangentProjection P e he w) := rfl
include P in

theorem hasFDerivAt_normalChartMap_split 
    (e : E) (he : diagonalCubic P.form e = 1) (x : E)
    (hx : fderiv ℝ (diagonalCubic P.form) x e ≠ 0) :
    HasFDerivAt (normalChartMap P e he)
      (normalDerivativeSplit P e he x hx : E →L[ℝ] (ℝ × tangentSpace P e)) x :=
  hasFDerivAt_normalChartMap_at P e he x
include P in

/-- This open set is defined by an actual derivative evaluation, not by desired
chart regularity. Its openness uses continuity of the true DN map. -/
def normalNonzeroLocus  (e : E) : Set E :=
  {x | fderiv ℝ (diagonalCubic P.form) x e ≠ 0}
include P in

theorem isOpen_normalNonzeroLocus  (e : E) :
    IsOpen (normalNonzeroLocus P e) :=
  isOpen_ne.preimage ((continuous_fderiv_diagonalCubic P).clm_apply continuous_const)
include P in

theorem basepoint_mem_normalNonzeroLocus 
    (e : E) (he : diagonalCubic P.form e = 1) : e ∈ normalNonzeroLocus P e := by
  change fderiv ℝ (diagonalCubic P.form) e e ≠ 0
  rw [fderiv_diagonalCubic_at_one P.form e he]
  norm_num

variable [CompleteSpace E]
include P in

/-- Restrict the actual C1 inverse-theorem chart to the proved open nonzero
normal locus. This is one fixed chart, independent of differentiation order. -/
def regularSmoothLevelChart  (e : E)
    (he : diagonalCubic P.form e = 1) :
    OpenPartialHomeomorph E (ℝ × tangentSpace P e) :=
  (regularLevelChart P e he).restrOpen (normalNonzeroLocus P e)
    (isOpen_normalNonzeroLocus P e)
include P in

@[simp] theorem regularSmoothLevelChart_apply 
    (e x : E) (he : diagonalCubic P.form e = 1) :
    regularSmoothLevelChart P e he x = normalChartMap P e he x := rfl
include P in

theorem regularSmoothLevelChart_coe 
    (e : E) (he : diagonalCubic P.form e = 1) :
    (regularSmoothLevelChart P e he : E → ℝ × tangentSpace P e) =
      normalChartMap P e he := by
  funext x
  exact regularSmoothLevelChart_apply P e x he
include P in

@[simp] theorem regularSmoothLevelChart_symm_apply 
    (e : E) (he : diagonalCubic P.form e = 1) (y : ℝ × tangentSpace P e) :
    (regularSmoothLevelChart P e he).symm y = (regularLevelChart P e he).symm y := rfl
include P in

theorem regularSmoothLevelChart_source 
    (e : E) (he : diagonalCubic P.form e = 1) :
    (regularSmoothLevelChart P e he).source =
      (regularLevelChart P e he).source ∩ normalNonzeroLocus P e := rfl
include P in

theorem regularSmoothLevelChart_target 
    (e : E) (he : diagonalCubic P.form e = 1) :
    (regularSmoothLevelChart P e he).target =
      (regularLevelChart P e he).target ∩
        (regularLevelChart P e he).symm ⁻¹' normalNonzeroLocus P e := rfl
include P in

theorem regularSmoothLevelChart_basepoint_mem 
    (e : E) (he : diagonalCubic P.form e = 1) :
    e ∈ (regularSmoothLevelChart P e he).source := by
  rw [regularSmoothLevelChart_source]
  exact ⟨regularLevelChart_basepoint_mem P e he, basepoint_mem_normalNonzeroLocus P e he⟩
include P in

/-- At every actual inverse point, use the proved derivative equivalence and
smoothness of the genuine forward map to obtain inverse smoothness. -/
theorem contDiffAt_regularSmoothLevelChart_symm 
    (e : E) (he : diagonalCubic P.form e = 1) (n : ℕ∞ω)
    (y : ℝ × tangentSpace P e) (hy : y ∈ (regularSmoothLevelChart P e he).target) :
    ContDiffAt ℝ n (regularSmoothLevelChart P e he).symm y := by
  have hsource := (regularSmoothLevelChart P e he).map_target hy
  rw [regularSmoothLevelChart_source] at hsource
  have hx : fderiv ℝ (diagonalCubic P.form)
      ((regularSmoothLevelChart P e he).symm y) e ≠ 0 := hsource.2
  have hd : HasFDerivAt (regularSmoothLevelChart P e he)
      (normalDerivativeSplit P e he ((regularSmoothLevelChart P e he).symm y) hx :
        E →L[ℝ] (ℝ × tangentSpace P e)) ((regularSmoothLevelChart P e he).symm y) :=
    by simpa only [regularSmoothLevelChart_coe] using
      hasFDerivAt_normalChartMap_split P e he
        ((regularSmoothLevelChart P e he).symm y) hx
  have hs : ContDiffAt ℝ n (regularSmoothLevelChart P e he)
      ((regularSmoothLevelChart P e he).symm y) :=
    by simpa only [regularSmoothLevelChart_coe] using
      (contDiff_normalChartMap P e he n).contDiffAt
  exact (regularSmoothLevelChart P e he).contDiffAt_symm hy hd hs
include P in

/-- The level-domain is selected from the actual restricted chart target. -/
def smoothLevelChartDomain  (e : E)
    (he : diagonalCubic P.form e = 1) : Set (tangentSpace P e) :=
  {v | (1, v) ∈ (regularSmoothLevelChart P e he).target}
include P in

theorem isOpen_smoothLevelChartDomain 
    (e : E) (he : diagonalCubic P.form e = 1) :
    IsOpen (smoothLevelChartDomain P e he) :=
  (regularSmoothLevelChart P e he).open_target.preimage
    (continuous_const.prodMk continuous_id)
include P in

theorem zero_mem_smoothLevelChartDomain 
    (e : E) (he : diagonalCubic P.form e = 1) :
    (0 : tangentSpace P e) ∈ smoothLevelChartDomain P e he := by
  have h := (regularSmoothLevelChart P e he).map_source
    (regularSmoothLevelChart_basepoint_mem P e he)
  simpa only [regularSmoothLevelChart_apply, normalChartMap_basepoint,
    smoothLevelChartDomain, Set.mem_setOf_eq] using h
include P in

theorem smoothLevelChartDomain_subset 
    (e : E) (he : diagonalCubic P.form e = 1) :
    smoothLevelChartDomain P e he ⊆ levelChartDomain P e he := by
  intro v hv
  change (1, v) ∈ (regularSmoothLevelChart P e he).target at hv
  rw [regularSmoothLevelChart_target] at hv
  exact hv.1
include P in

/-- The ORIGINAL inverse-theorem levelChartPoint is smooth on the new fixed
open domain. Only its domain is restricted; its function is unchanged. -/
theorem contDiffAt_levelChartPoint_smoothDomain 
    (e : E) (he : diagonalCubic P.form e = 1) (n : ℕ∞ω)
    (v : tangentSpace P e) (hv : v ∈ smoothLevelChartDomain P e he) :
    ContDiffAt ℝ n (levelChartPoint P e he) v := by
  have h := contDiffAt_regularSmoothLevelChart_symm P e he n (1, v) hv
  have hp : ContDiffAt ℝ n
      (fun w : tangentSpace P e => ((1 : ℝ), w)) v :=
    contDiffAt_const.prodMk contDiffAt_id
  have hcomp : ContDiffAt ℝ n
      (fun w : tangentSpace P e =>
        (regularSmoothLevelChart P e he).symm (1, w)) v :=
    h.fun_comp v hp
  have hsame : (fun w : tangentSpace P e =>
      (regularSmoothLevelChart P e he).symm (1, w)) =
      levelChartPoint P e he := by
    funext w
    change (regularSmoothLevelChart P e he).symm (1, w) =
      (regularLevelChart P e he).symm (1, w)
    exact regularSmoothLevelChart_symm_apply P e he (1, w)
  rw [hsame] at hcomp
  exact hcomp
include P in

theorem contDiffOn_levelChartPoint_smoothDomain 
    (e : E) (he : diagonalCubic P.form e = 1) (n : ℕ∞ω) :
    ContDiffOn ℝ n (levelChartPoint P e he) (smoothLevelChartDomain P e he) := by
  intro v hv
  exact (contDiffAt_levelChartPoint_smoothDomain P e he n v hv).contDiffWithinAt

end
end AlbertGeometry.Cubic
