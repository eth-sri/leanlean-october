/- Derived native reference-curvature blocks for the bounded fixed-frame gate.
D is the actual wedge plus KA commutator; no block identity is assumed. -/
module
public import Glennie.Native.CoordinateSimp

public import AlbertRecognition.FixedFrame.FrameCoordinates
public import AlbertRecognition.CubicOperators

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
set_option maxHeartbeats 2000000
open Glennie

private theorem octDot_zero_right (a : Octonion) : octDot a 0 = 0 := by
  simp [octDot_coordinates]
/-- The full native commutator is tracefree by the proved trace pairing law. -/
theorem trace_full_commutator (x y z : V) :
    Glennie.trace (jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
      jordan (y : Albert) (jordan (x : Albert) (z : Albert))) = 0 := by
  rw [trace_sub]
  change inner (x : Albert) (jordan (y : Albert) (z : Albert)) -
    inner (y : Albert) (jordan (x : Albert) (z : Albert)) = 0
  rw [← inner_jordan_associative, ← inner_jordan_associative,
    jordan_comm (y : Albert) (x : Albert)]
  simp

/-- Raising and projecting indices contributes the exact scalar metric term. -/
theorem KA_projected_composition (x y z : V) :
    KA x (KA y z) =
      project (jordan (x : Albert) (jordan (y : Albert) (z : Albert))) -
        gA y z • x := by
  simp only [KA_apply_apply]
  change project (jordan (x : Albert)
    (traceless (jordan (y : Albert) (z : Albert)))) = _
  rw [traceless, jordan_sub_right, jordan_smul_right, jordan_unit_right,
    map_sub, map_smul, project_V]
  rfl

/-- Exact unit/trace splitting identifies D with the full Jordan commutator.
This uses bilinearity and associative trace pairing, not a Jordan identity. -/
theorem D_apply_project_native (x y z : V) :
    D x y z = project
      (jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
        jordan (y : Albert) (jordan (x : Albert) (z : Albert))) := by
  unfold D q operatorComm
  rw [KB_referenceCubic]
  change gA y z • x - gA x z • y + (KA x (KA y z) - KA y (KA x z)) = _
  rw [map_sub, KA_projected_composition, KA_projected_composition]
  module

theorem D_apply_native (x y z : V) :
    (D x y z : Albert) =
      jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
        jordan (y : Albert) (jordan (x : Albert) (z : Albert)) := by
  rw [D_apply_project_native]
  change traceless _ = _
  rw [traceless, trace_full_commutator]
  simp

/- Native coordinate projections of additive negation. These are definitional
identities for the inspected coordinate transport on Albert. -/

def frameAction (a : Octonion) : V →ₗ[ℝ] V := D (h 1) (X12 a)

theorem frameAction_coordinates (a : Octonion) (x : V) :
    (frameAction a x : Albert) =
      ⟨0,-(3/2 : ℝ)*octDot a (x : Albert).o12,
        (3/2 : ℝ)*octDot a (x : Albert).o12,
        -(3/4 : ℝ) • octMul (x : Albert).o02 (octConj a),
        (3/4 : ℝ) • octMul (x : Albert).o01 a,
        ((3/4 : ℝ)*((x : Albert).d1-(x : Albert).d2)) • a⟩ := by
  rw [frameAction, D_apply_native]
  ext <;> simp [h, e, X12, albert_coords] <;> ring

theorem frameAction_h0 (a : Octonion) : frameAction a (h 0) = 0 := by
  apply Subtype.ext
  rw [frameAction_coordinates]
  apply Albert.ext <;>
    simp [h, e, octDot_zero_right, octMul_zero_left]

theorem frameAction_d (a : Octonion) :
    frameAction a frameD = (3/2 : ℝ) • X12 a := by
  apply Subtype.ext
  rw [frameAction_coordinates]
  apply Albert.ext <;>
    simp [frameD, X12, octDot_zero_right, octMul_zero_left] <;>
    ring

theorem frameAction_X12 (a z : Octonion) :
    frameAction a (X12 z) = (-(3/2 : ℝ)*octDot a z) • frameD := by
  apply Subtype.ext
  rw [frameAction_coordinates]
  apply Albert.ext <;>
    simp [X12, frameD, octMul_zero_left]

theorem frameAction_X01 (a u : Octonion) :
    frameAction a (X01 u) = (3/4 : ℝ) • X02 (octMul u a) := by
  apply Subtype.ext
  rw [frameAction_coordinates]
  apply Albert.ext <;>
    simp [X01, X02, octDot_zero_right, octMul_zero_left]

theorem frameAction_X02 (a v : Octonion) :
    frameAction a (X02 v) = -(3/4 : ℝ) • X01 (octMul v (octConj a)) := by
  apply Subtype.ext
  rw [frameAction_coordinates]
  apply Albert.ext <;>
    simp [X01, X02, octDot_zero_right, octMul_zero_left]

/-- The exact signed native 16D block, with its actual upper-slot embeddings. -/
theorem frameAction_spin (a : Octonion) (s : Spin) :
    frameAction a (frameSpin s) = (3/4 : ℝ) • frameSpin (spinJ a s) := by
  rcases s with ⟨u,v⟩
  rw [frameSpin_apply, map_add, frameAction_X01, frameAction_X02, spinJ_apply,
    frameSpin_apply]
  simp only [map_neg]
  module

end
end AlbertRecognition.FixedFrame
