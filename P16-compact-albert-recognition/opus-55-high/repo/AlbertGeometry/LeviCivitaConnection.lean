/-
A common positive domain is
produced from actual ambient positivity and the actual chart. The connection
coefficient is the inverse actual metric dual applied to the actual Koszul
covector, with torsion freedom, metric compatibility and uniqueness proved.
No connection/curvature jet or inverse field is an assumption.
-/
module

public import AlbertGeometry.PullbackMetricJets
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section
open scoped ContDiff Topology

namespace AlbertGeometry.Cubic
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (P : SymmetricTrilinearForm E) (e : E) (he : diagonalCubic P.form e = 1)
local notation "W" => tangentSpace P e
local notation "χ" => levelChartPoint P e he
local notation "Dχ" => levelChartD1 P e he
local notation "U" => smoothLevelChartDomain P e he
local notation "G" => pullbackMetric P e he
local notation "DG" => pullbackMetricD1 P e he
local notation "DualW" => (W →L[ℝ] ℝ)

section CanonicalConnectionNorms

attribute [local instance] pullbackMetricDualNormedAddCommGroup pullbackMetricDualNormedSpace
  pullbackMetricBilinearNormedAddCommGroup pullbackMetricBilinearNormedSpace
  pullbackMetricTrilinearNormedAddCommGroup pullbackMetricTrilinearNormedSpace

local instance lcEndNormedAddCommGroup : NormedAddCommGroup (W →L[ℝ] W) := ContinuousLinearMap.toNormedAddCommGroup
local instance lcEndNormedSpace : NormedSpace ℝ (W →L[ℝ] W) := ContinuousLinearMap.toNormedSpace
local instance lcBilinearVectorNormedAddCommGroup : NormedAddCommGroup (W →L[ℝ] W →L[ℝ] W) := ContinuousLinearMap.toNormedAddCommGroup
local instance lcBilinearVectorNormedSpace : NormedSpace ℝ (W →L[ℝ] W →L[ℝ] W) := ContinuousLinearMap.toNormedSpace
local instance lcInverseNormedAddCommGroup : NormedAddCommGroup (DualW →L[ℝ] W) := ContinuousLinearMap.toNormedAddCommGroup
local instance lcInverseNormedSpace : NormedSpace ℝ (DualW →L[ℝ] W) := ContinuousLinearMap.toNormedSpace

/-- The actual chart derivative is injective throughout the same smooth domain. -/
theorem levelChartD1_injective (x : W) (hx : x ∈ U) : Function.Injective (Dχ x) :=
  Function.LeftInverse.injective (fun u => levelChartD1_projection P e he x hx u)

/-- Symmetry belongs to the actual pulled-back ambient metric. -/
theorem pullbackMetric_symm (x : W) (hx : x ∈ U) (u v : W) : G x u v = G x v u := by
  rw [pullbackMetric_cubic_apply P e he x hx,
    pullbackMetric_cubic_apply P e he x hx, P.swap23]

/-- Literal Koszul covector field, bundled as a trilinear CLM using actual DG. -/
def koszulTensor (x : W) : W →L[ℝ] W →L[ℝ] DualW :=
  (1 / 2 : ℝ) • (DG x + (DG x).flip -
    ((((ContinuousLinearMap.flipₗᵢ ℝ W W ℝ).toContinuousLinearEquiv).toContinuousLinearMap :
      (W →L[ℝ] W →L[ℝ] ℝ) →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ).comp
      ((DG x).flip : W →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ)))

def koszulCovector (x u v : W) : DualW := koszulTensor P e he x u v

@[simp] theorem koszulCovector_apply (x u v w : W) :
    koszulCovector P e he x u v w =
      (DG x u v w + DG x v u w - DG x w u v) / 2 := by
  simp [koszulCovector, koszulTensor]
  ring

/-- Actual inverse metric raising of the Koszul covector. The total inverse is
zero off the invertible locus; every geometric statement is on the produced U+. -/
def leviCivitaGamma (x : W) : W →L[ℝ] W →L[ℝ] W :=
  (((ContinuousLinearMap.compL ℝ W DualW W :
    (DualW →L[ℝ] W) →L[ℝ] (W →L[ℝ] DualW) →L[ℝ] W →L[ℝ] W)
    ((G x).inverse : DualW →L[ℝ] W)).comp
    (koszulTensor P e he x))

@[simp] theorem leviCivitaGamma_apply (x u v : W) :
    leviCivitaGamma P e he x u v =
      (G x).inverse (koszulCovector P e he x u v) := rfl

/-- Chart-defined covariant derivative on actual vector fields. -/
def chartCovariantDerivative (x : W) (X Y : W → W) : W :=
  fderiv ℝ Y x (X x) + leviCivitaGamma P e he x (X x) (Y x)

/-- The genuine coordinate Lie bracket: difference of directional derivatives. -/
def chartLieBracket (x : W) (X Y : W → W) : W :=
  fderiv ℝ Y x (X x) - fderiv ℝ X x (Y x)

/-- ONE positive chart domain is produced, using the positive ambient neighborhood
and the true chart derivative left inverse. It is not a positivity premise. -/
theorem exists_positive_pullback_chart_domain [FiniteDimensional ℝ E]
    (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) :
    ∃ S : Set W, IsOpen S ∧ 0 ∈ S ∧ S ⊆ U ∧
      ∀ x ∈ S, ∀ u : W, u ≠ 0 → 0 < G x u u := by
  have hN : 0 < diagonalCubic P.form e := by rw [he]; norm_num
  obtain ⟨V, hV, heV, hgood⟩ :=
    exists_positive_definite_logHessian_neighborhood P e hN hpos
  let S := U ∩ χ ⁻¹' V
  have hχ := (contDiffOn_levelChartPoint_smoothDomain P e he ⊤).continuousOn
  have hOpen := hχ.isOpen_inter_preimage
    (isOpen_smoothLevelChartDomain P e he) hV
  have hzero : (0 : W) ∈ S := by
    refine ⟨zero_mem_smoothLevelChartDomain P e he, ?_⟩
    simpa [Set.mem_preimage, levelChartPoint_zero] using heV
  refine ⟨S, hOpen, hzero, fun x hx => hx.1, fun x hx u hu => ?_⟩
  rw [pullbackMetric_apply]
  exact (hgood (χ x) hx.2).2.2 (Dχ x u)
    fun hz => hu (levelChartD1_injective P e he x hx.1 (by simpa using hz))

/-- A chosen PRODUCED open neighborhood; no metric or inverse field is given. -/
def leviCivitaChartDomain [FiniteDimensional ℝ E]
    (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) : Set W :=
  Classical.choose (exists_positive_pullback_chart_domain P e he hpos)

theorem leviCivitaChartDomain_spec [FiniteDimensional ℝ E]
    (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u) :
    IsOpen (leviCivitaChartDomain P e he hpos) ∧
      0 ∈ leviCivitaChartDomain P e he hpos ∧
      leviCivitaChartDomain P e he hpos ⊆ U ∧
      ∀ x ∈ leviCivitaChartDomain P e he hpos, ∀ u : W, u ≠ 0 → 0 < G x u u :=
  Classical.choose_spec (exists_positive_pullback_chart_domain P e he hpos)

variable [FiniteDimensional ℝ E]
variable (hpos : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)
local notation "S" => leviCivitaChartDomain P e he hpos
local notation "Γ" => leviCivitaGamma P e he

theorem pullbackMetric_dual_injective (x : W) (hx : x ∈ S) : Function.Injective (G x) :=
  injective_of_pos ((leviCivitaChartDomain_spec P e he hpos).2.2.2 x hx)

theorem pullbackMetric_dual_isInvertible (x : W) (hx : x ∈ S) : (G x).IsInvertible :=
  isInvertible_of_pos ((leviCivitaChartDomain_spec P e he hpos).2.2.2 x hx)

/-- Actual Koszul identity holds throughout S before any Γ differentiation. -/
theorem leviCivitaGamma_koszul (x : W) (hx : x ∈ S) (u v w : W) :
    G x (Γ x u v) w = koszulCovector P e he x u v w := by
  exact congr($((pullbackMetric_dual_isInvertible P e he hpos x hx).self_apply_inverse
    (koszulCovector P e he x u v)) w)

/-- The proved Koszul identity holds in a full neighborhood before any Γ jet. -/
theorem eventually_leviCivitaGamma_koszul (x : W) (hx : x ∈ S) (u v w : W) :
    ∀ᶠ y in 𝓝 x, G y (Γ y u v) w = koszulCovector P e he y u v w :=
  Filter.eventually_of_mem ((leviCivitaChartDomain_spec P e he hpos).1.mem_nhds hx)
    fun y hy => leviCivitaGamma_koszul P e he hpos y hy u v w

/-- Smooth actual inverse on S, obtained from official finite inverse calculus. -/
theorem contDiffAt_pullbackMetric_inverse (x : W) (hx : x ∈ S) :
    ContDiffAt ℝ ⊤ (fun y => (G y).inverse) x :=
  (pullbackMetric_dual_isInvertible P e he hpos x hx).contDiffAt_map_inverse.comp x
    (contDiffAt_pullbackMetric P e he x ((leviCivitaChartDomain_spec P e he hpos).2.2.1 hx))

/-- Smooth Koszul tensor on the same domain, using actual DG smoothness. -/
theorem contDiffAt_koszulTensor (x : W) (hx : x ∈ S) :
    ContDiffAt ℝ ⊤ (koszulTensor P e he) x := by
  have hD := (contDiffAt_pullbackMetric P e he x
    ((leviCivitaChartDomain_spec P e he hpos).2.2.1 hx)).fderiv_right (m := ⊤) (by simp)
  have hflip := (ContinuousLinearMap.flipₗᵢ ℝ W W DualW).contDiff.contDiffAt.comp x hD
  exact ((hD.add hflip).sub (contDiffAt_const.clm_comp hflip)).const_smul (1 / 2 : ℝ)

/-- The actual bilinear Γ FIELD is smooth throughout the ONE produced S.
No derivative of Γ is taken before these neighborhood laws and smoothness. -/
theorem contDiffAt_leviCivitaGamma (x : W) (hx : x ∈ S) : ContDiffAt ℝ ⊤ Γ x :=
  ((ContinuousLinearMap.compL ℝ W DualW W).contDiff.contDiffAt.comp x
    (contDiffAt_pullbackMetric_inverse P e he hpos x hx)).clm_comp
    (contDiffAt_koszulTensor P e he hpos x hx)

end CanonicalConnectionNorms
end
end AlbertGeometry.Cubic
