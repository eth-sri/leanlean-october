module

public import GS.Shared.OrbitAtlas
public import GS.OverlapGeometry.ManifoldSmoothMaps

@[expose] public section


/-!
# Local smooth sections of the shared orbit map

Each translated slice yields an actual local choice of shared factors.  The
choice is smooth on its stated open neighbourhood and reconstructs every point
there.  No global section and no unique factorization are asserted.  In
particular, ambient-smooth orbit curves now admit local smooth factor lifts.
-/


noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (right left : Pattern 𝕜 n) (P : 𝕄)
local instance localSectionsNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _

section
variable (g : Factors right left) (A : 𝕄)
/-- Total extension of a local section; its right-inverse identity is asserted
only on the open source of the translated slice. -/
def localFactors : Factors right left :=
  factorLift g ((translatedOrbitSlice right left P g).coordinates A).val

theorem localFactors_orbit :
    orbitMapToOrbit right left P (localFactors right left P g A) =
      (translatedOrbitSlice right left P g).parametrization
        ((translatedOrbitSlice right left P g).coordinates A) := by
  apply Subtype.ext
  exact orbitParam_eq_translate g P _

end

section
variable (g : Factors right left) (X : MatrixOrbit right left P)
/-- Every nearby matrix in the full shared orbit is reconstructed. -/
theorem localFactors_right_inverse (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    orbitMapToOrbit right left P (localFactors right left P g X.val) = X := by
  rw [localFactors_orbit]
  exact (translatedOrbitSlice right left P g).left_inverse X hX

theorem localFactors_left_matrix_smooth_at (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    ContDiffAt ℝ ⊤ (fun A : 𝕄 => Factor.matrix (localFactors right left P g A).1) X.val := by
  have hc := (translatedOrbitSlice right left P g).coordinates_smooth X hX
  have hv := (HorizontalModel right left P).subtypeL.contDiff.contDiffAt.comp X.val hc
  have hl := contDiffAt_fst.comp X.val hv
  exact (reconstruct_matrix_smooth g.1).contDiffAt.comp X.val hl

theorem localFactors_right_matrix_smooth_at (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    ContDiffAt ℝ ⊤ (fun A : 𝕄 => Factor.matrix (localFactors right left P g A).2) X.val := by
  have hc := (translatedOrbitSlice right left P g).coordinates_smooth X hX
  have hv := (HorizontalModel right left P).subtypeL.contDiff.contDiffAt.comp X.val hc
  have hr := contDiffAt_snd.comp X.val hv
  exact (reconstruct_matrix_smooth g.2).contDiffAt.comp X.val hr

end

end GS.Shared
