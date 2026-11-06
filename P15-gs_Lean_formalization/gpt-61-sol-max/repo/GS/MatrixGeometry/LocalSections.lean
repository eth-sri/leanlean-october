import GS.MatrixGeometry.Base

import GS.MatrixGeometry.OrbitAtlas
import GS.OverlapGeometry.ManifoldSmoothMaps



/-!
# Local smooth sections of the shared orbit map

Each translated slice yields an actual local choice of shared factors.  The
choice is smooth on its stated open neighbourhood and reconstructs every point
there.  No global section and no unique factorization are asserted.  In
particular, ambient-smooth orbit curves now admit local smooth factor lifts.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS.MatrixBase
open scoped Manifold
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  (right left : Pattern 𝕜 n) (P : KMat 𝕜 n)
local instance localSectionsNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _

variable (g : Factors right left)

variable (X : MatrixOrbit right left P)

/-- Total extension of a local section; its right-inverse identity is asserted
only on the open source of the translated slice. -/
def localFactors  (A : KMat 𝕜 n) : Factors right left :=
  factorLift g ((translatedOrbitSlice right left P g).coordinates A).val

/-- Every nearby matrix in the full shared orbit is reconstructed. -/
theorem localFactors_right_inverse 
     (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    orbitMapToOrbit right left P (localFactors right left P g X.val) = X := by
  apply Subtype.ext
  change orbitParam g P ((translatedOrbitSlice right left P g).coordinates X.val).val = X.val
  rw [orbitParam_eq_translate]
  exact congrArg Subtype.val ((translatedOrbitSlice right left P g).left_inverse X hX)

set_option backward.isDefEq.respectTransparency false
local instance : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P

/-- Smooth ambient formulas in local factors descend smoothly to the orbit. -/
theorem transported_contMDiff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : KMat 𝕜 n → E → F) (T : KMat 𝕜 n × (KMat 𝕜 n × E) → F)
    (hT : ContDiff ℝ ⊤ T)
    (he : ∀ (g : Factors right left) z,
      T (Factor.matrix g.1, (Factor.matrix g.2, z)) = f (g • P) z) :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, E)))
      (𝓘(ℝ, F)) ⊤ (fun p : MatrixOrbit right left P × E => f p.1.val p.2) := by
  intro p
  let g := preferredFactor P p.1
  have h₀ :=
    preferredOrbitSlice_covers right left P p.1
  have hv := (HorizontalModel right left P).subtypeL.contDiff.contDiffAt.comp p.1.val
    ((translatedOrbitSlice right left P g).coordinates_smooth p.1 h₀)
  have hLR := (((reconstruct_matrix_smooth g.1).contDiffAt.comp p.1.val
    (contDiffAt_fst.comp p.1.val hv)).prodMk
      ((reconstruct_matrix_smooth g.2).contDiffAt.comp p.1.val
        (contDiffAt_snd.comp p.1.val hv))).comp (p.1.val,p.2) contDiffAt_fst
  have hs := hT.contDiffAt.comp (p.1.val, p.2)
    (hLR.fst.prodMk (hLR.snd.prodMk contDiffAt_snd))
  have hi : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, E)))
      (𝓘(ℝ, KMat 𝕜 n × E)) ⊤
      (fun q : MatrixOrbit right left P × E => (q.1.val, q.2)) :=
    ((sharedOrbit_val_contMDiff right left P).comp contMDiff_fst).prodMk_space contMDiff_snd
  apply (ContDiffAt.comp_contMDiffAt
    (f := fun q : MatrixOrbit right left P × E => (q.1.val, q.2)) hs (hi p)).congr_of_eventuallyEq
  have hn := continuous_fst.continuousAt.eventually
    ((translatedOrbitSlice right left P g).open_source.mem_nhds h₀)
  filter_upwards [hn] with q hq
  dsimp only [Function.comp_apply]
  have hh := he (localFactors right left P g q.1.val) q.2
  rw [show localFactors right left P g q.1.val • P = q.1.val from
    congrArg Subtype.val (localFactors_right_inverse right left P g q.1 hq)] at hh
  simpa only [localFactors,factorLift,Submodule.subtypeL_apply] using hh.symm

end GS.MatrixGeometry
