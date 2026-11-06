module

public import GS.SharedGeometry.OrbitAtlas
public import GS.OverlapGeometry.ManifoldSmoothMaps

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Local smooth sections of the shared orbit map

Each translated slice yields an actual local choice of shared factors.  The
choice is smooth on its stated open neighbourhood and reconstructs every point
there.  No global section and no unique factorization are asserted.  In
particular, ambient-smooth orbit curves now admit local smooth factor lifts.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry GS.CayleyCharts Set Filter
open scoped Topology Manifold
namespace GS.SharedGeometry
variable {n : ℕ} (right left : Pattern n) (P : Mat n)

/-- Total extension of a local section; its right-inverse identity is asserted
only on the open source of the translated slice. -/
def localFactors (g : Factors right left) (A : Mat n) : Factors right left :=
  factorLift g ((translatedOrbitSlice right left P g).coordinates A).val

theorem localFactors_orbit (g : Factors right left) (A : Mat n) :
    orbitMapToOrbit right left P (localFactors right left P g A) =
      (translatedOrbitSlice right left P g).parametrization
        ((translatedOrbitSlice right left P g).coordinates A) := by
  apply Subtype.ext
  change orbitParam g P ((translatedOrbitSlice right left P g).coordinates A).val =
    g • orbitParam (1 : Factors right left) P
      ((translatedOrbitSlice right left P g).coordinates A).val
  exact orbitParam_eq_translate g P _

/-- Every nearby matrix in the full shared orbit is reconstructed. -/
theorem localFactors_right_inverse (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    orbitMapToOrbit right left P (localFactors right left P g X.val) = X := by
  rw [localFactors_orbit]
  exact (translatedOrbitSlice right left P g).left_inverse X hX

theorem localFactors_left_matrix_smooth_at (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    ContDiffAt ℝ ⊤ (fun A : Mat n => Factor.matrix (localFactors right left P g A).1) X.val := by
  have hc := (translatedOrbitSlice right left P g).coordinates_smooth X hX
  have hv := (HorizontalModel right left P).subtypeL.contDiff.contDiffAt.comp X.val hc
  have hl := contDiffAt_fst.comp X.val hv
  exact (reconstruct_matrix_smooth g.1).contDiffAt.comp X.val hl

theorem localFactors_right_matrix_smooth_at (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    ContDiffAt ℝ ⊤ (fun A : Mat n => Factor.matrix (localFactors right left P g A).2) X.val := by
  have hc := (translatedOrbitSlice right left P g).coordinates_smooth X hX
  have hv := (HorizontalModel right left P).subtypeL.contDiff.contDiffAt.comp X.val hc
  have hr := contDiffAt_snd.comp X.val hv
  exact (reconstruct_matrix_smooth g.2).contDiffAt.comp X.val hr

end GS.SharedGeometry
