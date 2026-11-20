module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Product inputs for tangent-section constructions

These generic lemmas keep the manifold model abstract during elaboration.
They apply to both real and complex matrix orbits regarded as real manifolds.
-/

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace GS.Extensions
variable {E H M V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (I : ModelWithCorners ℝ E H)

theorem mfderiv_fibre {E' H' N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] [TopologicalSpace N] [ChartedSpace H' N] {J : ModelWithCorners ℝ E' H'}
    (F : M × V → N) (x : M) (hF : MDifferentiableAt (I.prod 𝓘(ℝ,V)) J F (x,0)) (v : V) :
    mfderiv 𝓘(ℝ,V) J (fun z : V => F (x,z)) 0 v = mfderiv (I.prod 𝓘(ℝ,V)) J F (x,0) (0,v) := by
  have hc : MDifferentiableAt 𝓘(ℝ,V) (I.prod 𝓘(ℝ,V)) (fun z : V => (x,z)) (0 : V) :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have h := mfderiv_comp_apply (0 : V) hF hc v
  erw [mfderiv_prod_right] at h
  exact h

theorem contMDiff_vertical_input [IsManifold I ⊤ M] :
    ContMDiff (I.prod (𝓘(ℝ, V))) (I.prod (𝓘(ℝ, V))).tangent ⊤
      (fun p : M × V =>
        (⟨(p.1, 0), (0, p.2)⟩ : TangentBundle (I.prod (𝓘(ℝ, V))) (M × V))) := by
  have hzero : ContMDiff (I.prod (𝓘(ℝ, V))) I.tangent ⊤
      (fun p : M × V => (⟨p.1, 0⟩ : TangentBundle I M)) :=
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_fst
  have hvector : ContMDiff (I.prod (𝓘(ℝ, V))) (𝓘(ℝ, V)).tangent ⊤
      (fun p : M × V => (⟨0, p.2⟩ : TangentBundle (𝓘(ℝ, V)) V)) := by
    have hp : ContMDiff (M' := ModelProd V V)
        (I.prod (𝓘(ℝ, V))) ((𝓘(ℝ, V)).prod (𝓘(ℝ, V))) ⊤
        (fun p : M × V => ((0, p.2) : ModelProd V V)) := by
      rw [← modelWithCornersSelf_prod]
      exact contMDiff_const.prodMk_space contMDiff_snd
    exact (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, V))).comp hp
  exact (contMDiff_equivTangentBundleProd_symm
    (I := I) (I' := 𝓘(ℝ, V)) (M := M) (M' := V)).comp (hzero.prodMk hvector)

end GS.Extensions
