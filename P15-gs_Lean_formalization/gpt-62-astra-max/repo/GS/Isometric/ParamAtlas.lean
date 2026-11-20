module
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
@[expose] public section

/-! An atlas on an actual subset from smooth regular parametrizations open at
 their centres. Project along a left inverse of the differential and apply IFT
 in the model space. Only the *interior* of the parametrized patch is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold
namespace GS
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set F} {x : S}
structure ParamAt (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (x : S) where
  param : E → S
  centre : param 0 = x
  smooth : ContDiff ℝ ⊤ (fun v => (param v).val)
  openAt : map param (𝓝 0) = 𝓝 x
  D : E →L[ℝ] F
  deriv : HasFDerivAt (fun v => (param v).val) D 0
  regular : D.HasLeftInverse

namespace ParamAt
variable (p : ParamAt E x)
lemma inverseData : ∃ (c : F → E) (V : Set E), IsOpen V ∧ 0 ∈ V ∧
    ∀ v ∈ V, c (p.param v).val = v ∧ ContDiffAt ℝ ⊤ c (p.param v).val := by
  let L := p.regular.leftInverse
  let f v := L (p.param v).val
  have hs : ContDiffAt ℝ ⊤ f 0 := L.contDiff.contDiffAt.comp 0 p.smooth.contDiffAt
  let e := ContinuousLinearEquiv.refl ℝ E
  have hd : HasFDerivAt f (e : E →L[ℝ] E) 0 := by
    have he : L.comp p.D = e.toContinuousLinearMap := ContinuousLinearMap.ext p.regular.leftInverse_leftInverse
    exact he ▸ L.hasFDerivAt.comp 0 p.deriv
  have hi := hs.hasStrictFDerivAt' hd (by simp)
  let c := hs.localInverse hd (by simp) ∘ L
  have hc : ContDiffAt ℝ ⊤ c (p.param 0).val := (hs.to_localInverse hd (by simp)).comp (f := L) (p.param 0).val L.contDiff.contDiffAt
  have h : ∀ᶠ v in 𝓝 0, c (p.param v).val = v ∧ ContDiffAt ℝ ⊤ c (p.param v).val :=
    hi.eventually_left_inverse.and (p.smooth.continuous.continuousAt.eventually (hc.eventually (by simp)))
  obtain ⟨V,hV,ho,h₀⟩ := mem_nhds_iff.mp h
  exact ⟨c,V,ho,h₀,hV⟩
def c := p.inverseData.choose
def V := p.inverseData.choose_spec.choose
lemma good : IsOpen p.V ∧ 0 ∈ p.V ∧ ∀ v ∈ p.V, p.c (p.param v).val = v ∧ ContDiffAt ℝ ⊤ p.c (p.param v).val := p.inverseData.choose_spec.choose_spec
def U := interior (p.param '' p.V)
lemma cancel {y : S} (hy : y ∈ p.U) : p.param (p.c y.val) = y ∧ p.c y.val ∈ p.V ∧ ContDiffAt ℝ ⊤ p.c y.val := by
  obtain ⟨v,hv,rfl⟩ := interior_subset hy
  rw [(p.good.2.2 v hv).1]; exact ⟨rfl,hv,(p.good.2.2 v hv).2⟩

def chart : OpenPartialHomeomorph S E where
  toFun y := p.c y.val
  invFun := p.param
  source := p.U
  target := p.V ∩ p.param ⁻¹' p.U
  open_source := isOpen_interior
  open_target := p.good.1.inter (isOpen_interior.preimage (p.smooth.continuous.subtype_mk _))
  map_source' y hy := ⟨(p.cancel hy).2.1, by change p.param (p.c y.val) ∈ p.U; rwa [(p.cancel hy).1]⟩
  map_target' _ hv := hv.2
  left_inv' _ hy := (p.cancel hy).1
  right_inv' v hv := (p.good.2.2 v hv.1).1
  continuousOn_toFun _ hy := ((p.cancel hy).2.2.continuousAt.comp continuous_subtype_val.continuousAt).continuousWithinAt
  continuousOn_invFun := (p.smooth.continuous.subtype_mk _).continuousOn
lemma mem_chart : x ∈ p.chart.source := by
  apply mem_interior_iff_mem_nhds.mpr; rw [← p.openAt]; exact image_mem_map (p.good.1.mem_nhds p.good.2.1)
lemma chart_centre : p.chart x = 0 := (congrArg p.chart p.centre).symm.trans (p.good.2.2 0 p.good.2.1).1

variable (a : ∀ x : S, ParamAt E x)
@[reducible] def atlas : ChartedSpace E S where
  atlas := range fun x => (a x).chart
  chartAt x := (a x).chart
  mem_chart_source x := (a x).mem_chart
  chart_mem_atlas x := ⟨x,rfl⟩
include a
lemma manifold : letI := atlas a; IsManifold 𝓘(ℝ,E) ⊤ S := by
  let := atlas a
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩
  suffices ContDiffOn ℝ ⊤ ((a x).chart.symm.trans (a y).chart) ((a x).chart.symm.trans (a y).chart).source by simpa using this
  intro v hv; exact (((a y).cancel hv.2).2.2.comp v (a x).smooth.contDiffAt).contDiffWithinAt
lemma inclusion : letI := atlas a; ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ⊤ (Subtype.val : S → F) := by
  let := atlas a
  intro x; rw [contMDiffAt_iff]; exact ⟨continuous_subtype_val.continuousAt,(a x).smooth.contDiffAt.contDiffWithinAt⟩
lemma differential (x : S) : letI := atlas a; mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (Subtype.val : S → F) x = (a x).D := by
  let := atlas a
  have hd := (inclusion a x).mdifferentiableAt (by simp)
  suffices mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) (Subtype.val : S → F) x = fderiv ℝ (fun y => ((a x).param y).val) ((a x).chart x) by
    rwa [(a x).chart_centre,(a x).deriv.fderiv] at this
  unfold mfderiv; aesop
lemma out {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {f : S → B}
    (h : ∀ x, ContDiff ℝ ⊤ (f ∘ (a x).param)) : letI := atlas a; ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,B) ⊤ f := by
  let := atlas a
  intro x; exact contMDiffAt_iff_source.2 (h x).contMDiff.contMDiffAt.contMDiffWithinAt
lemma into {G H M : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ G H} {f : M → S}
    (h : ContMDiff I 𝓘(ℝ,F) ⊤ (fun z => (f z).val)) : letI := atlas a; ContMDiff I 𝓘(ℝ,E) ⊤ f := by
  let := atlas a
  intro z; rw [contMDiffAt_iff_target]; exact ⟨(h.continuous.subtype_mk _).continuousAt,
    ((a (f z)).cancel (a (f z)).mem_chart).2.2.comp_contMDiffAt (f := fun y => (f y).val) (h z)⟩
end ParamAt
end GS
