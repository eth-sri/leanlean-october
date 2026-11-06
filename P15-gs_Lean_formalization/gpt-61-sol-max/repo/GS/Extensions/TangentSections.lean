
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv



/-!
# Product inputs for tangent-section constructions

These generic lemmas keep the manifold model abstract during elaboration.
They apply to both real and complex matrix orbits regarded as real manifolds.
-/

open scoped Manifold

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
  have hzero : ContMDiff (I.prod (𝓘(ℝ, V))) I.tangent ⊤
      (fun p : M × V => (⟨p.1, 0⟩ : TangentBundle I M)) :=
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_fst
  have hvector : ContMDiff (I.prod (𝓘(ℝ, V))) (𝓘(ℝ, V)).tangent ⊤
      (fun p : M × V => (⟨0, p.2⟩ : TangentBundle (𝓘(ℝ, V)) V)) := by
    have hp : ContMDiff (M' := ModelProd V V)
        (I.prod (𝓘(ℝ, V))) ((𝓘(ℝ, V)).prod (𝓘(ℝ, V))) ⊤
        (fun p : M × V => ((0, p.2) : ModelProd V V)) := contMDiff_const.prodMk_space contMDiff_snd
    exact (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, V))).comp hp
  exact (contMDiff_equivTangentBundleProd_symm
     (I' := 𝓘(ℝ, V))  (M' := V)).comp (hzero.prodMk hvector)

end GS.Extensions
