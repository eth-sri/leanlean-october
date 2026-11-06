module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Product inputs for tangent-section constructions

These generic lemmas keep the manifold model abstract during elaboration.
They apply to both real and complex matrix orbits regarded as real manifolds.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GS.Extensions
variable {E H M V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  (I : ModelWithCorners ℝ E H)

theorem contMDiff_vertical_input [IsManifold I ⊤ M] :
    ContMDiff (I.prod (𝓘(ℝ, V))) (I.prod (𝓘(ℝ, V))).tangent ⊤
      (fun p : M × V =>
        (⟨(p.1, 0), (0, p.2)⟩ : TangentBundle (I.prod (𝓘(ℝ, V))) (M × V))) := by
  exact (contMDiff_equivTangentBundleProd_symm (I := I) (I' := 𝓘(ℝ, V)) (M := M) (M' := V)).comp
    (((Bundle.contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_fst).prodMk
      ((contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, V))).comp
        (contMDiff_const.prodMk_space contMDiff_snd)))

end GS.Extensions
