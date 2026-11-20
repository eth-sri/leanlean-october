module
public import GS.Extensions.TangentSections
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
@[expose] public section

/-! An ambient step `F(x,z)` induces both a bundle retraction and a smooth
lift of ambient vector fields, by differentiation in its second variable. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
namespace GS.Extensions.AmbientStep
variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace M] [ChartedSpace E M]
local notation "I" => 𝓘(ℝ,E)
local notation "J" => 𝓘(ℝ,V)
variable [IsManifold (𝓘(ℝ,E)) ⊤ M] {i : M → V} {F : M × V → M}
local notation "dι" => mfderiv I J i
local notation "D" => fun x : M => mfderiv J I (fun z : V => F (x,z)) (0 : V)
variable (hi : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,V) ⊤ i) (hF : ContMDiff ((𝓘(ℝ,E)).prod 𝓘(ℝ,V)) 𝓘(ℝ,E) ⊤ F) (h₀ : ∀ x : M, F (x,0) = x)

include hF in
lemma fixedSmooth (x : M) : ContMDiff J I ⊤ (fun z : V => F (x,z)) :=
  hF.comp (contMDiff_const.prodMk contMDiff_id)

include hi hF h₀ in
lemma differential {x : M} {v w : V} (h : HasDerivAt (fun t : ℝ => i (F (x,t • v))) w 0) :
    dι x (D x v) = w := by
  have hh := mfderiv_comp_apply_of_eq (0 : V) (hi.mdifferentiable (by simp) x)
    ((fixedSmooth hF x).mdifferentiable (by simp) 0) (h₀ x) v
  rw [mfderiv_eq_fderiv] at hh
  rw [← hh]; let f := fun z : V => i (F (x,z))
  have hf : ContDiff ℝ ⊤ f := (contMDiff_iff_contDiff.mp (hi.comp (fixedSmooth hF x)))
  have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact (((hf.differentiable (by simp) 0).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (zero_smul ℝ v).symm).unique h)

include hi hF h₀ in
/-- A step fixing the ambient images of true tangents to first order. -/
lemma retraction (hinj : ∀ x : M, Function.Injective (dι x))
    (h : ∀ (x : M) (v : E), dι x (D x (dι x v)) = dι x v) :
    ∃ R : TangentBundle I M → M, ContMDiff (I).tangent I ⊤ R ∧ (∀ x, R ⟨x,0⟩ = x) ∧
      ∀ x : M, mfderiv I I (fun v : E => R ⟨x,v⟩) 0 = ContinuousLinearMap.id ℝ E := by
  refine ⟨fun p => F (p.proj,dι p.proj p.2), ?_, fun x => by simp [h₀], ?_⟩
  · exact hF.comp ((Bundle.contMDiff_proj (TangentSpace I)).prodMk
      ((contMDiff_snd_tangentBundle_modelSpace V J).comp (hi.contMDiff_tangentMap (by simp))))
  · intro x; ext v
    let L : E →L[ℝ] V := dι x
    have hc := mfderiv_comp_apply_of_eq (0 : E) ((fixedSmooth hF x).mdifferentiable (by simp) 0)
      L.mdifferentiableAt (map_zero L) v
    simp only [TangentSpace, ContinuousLinearMap.mfderiv_eq] at hc
    exact hc.trans (hinj x (h x v))

include hF h₀ in
lemma liftSmooth {a : M → V} (ha : ContMDiff I J ∞ a) :
    ContMDiff I (I).tangent ∞ (fun x => (⟨x,D x (a x)⟩ : TangentBundle I M)) := by
  have he (x : M) : (⟨x,D x (a x)⟩ : TangentBundle I M) =
      tangentMap ((I).prod J) I F ⟨(x,0),(0,a x)⟩ := by
    simp only [tangentMap, GS.Extensions.mfderiv_partial_right _ F x (hF.mdifferentiable (by simp) _)]; congr 1
    exact (h₀ x).symm
  simp_rw [he]
  exact (((hF.contMDiff_tangentMap (by simp)).comp (contMDiff_vertical_input (M := M) (V := V) I)).of_le le_top).comp
    (contMDiff_id.prodMk ha)
end GS.Extensions.AmbientStep
