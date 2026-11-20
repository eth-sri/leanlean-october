/- Derived native reference-curvature blocks for the bounded fixed-frame gate.
D is the actual wedge plus KA commutator; no block identity is assumed. -/
module

public import AlbertRecognition.CubicOperators

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie
set_option maxHeartbeats 2000000

/-- The full native commutator is tracefree by the proved trace pairing law. -/
theorem trace_full_commutator (x y z : V) :
    Glennie.trace (jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
      jordan (y : Albert) (jordan (x : Albert) (z : Albert))) = 0 := by
  rw [trace_sub]
  change inner (x : Albert) (jordan (y : Albert) (z : Albert)) -
    inner (y : Albert) (jordan (x : Albert) (z : Albert)) = 0
  simp [← inner_jordan_associative, jordan_comm (y : Albert) (x : Albert)]

/-- Raising and projecting indices contributes the exact scalar metric term. -/
theorem KA_projected_composition (x y z : V) :
    KA x (KA y z) =
      project (jordan (x : Albert) (jordan (y : Albert) (z : Albert))) -
        gA y z • x := by
  simp only [KA_apply, project_coe]
  rw [traceless, jordan_sub_right, jordan_smul_right, jordan_unit_right,
    map_sub, map_smul, project_V]
  rfl

/-- Exact unit/trace splitting identifies D with the full Jordan commutator.
This uses bilinearity and associative trace pairing, not a Jordan identity. -/
theorem D_apply_project_native (x y z : V) :
    D x y z = project
      (jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
        jordan (y : Albert) (jordan (x : Albert) (z : Albert))) := by
  change gA y z • x - gA x z • y + (KA x (KA y z) - KA y (KA x z)) = _
  grind [map_sub, KA_projected_composition]

theorem D_apply_native (x y z : V) :
    (D x y z : Albert) =
      jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
        jordan (y : Albert) (jordan (x : Albert) (z : Albert)) := by
  rw [D_apply_project_native]
  change traceless _ = _
  rw [traceless, trace_full_commutator]
  simp

local macro "frameCalc" : tactic => `(tactic| ext <;> simp [h,e,X12,unit,
  jordan_d0,jordan_d1,jordan_d2,jordan_o01,jordan_o02,jordan_o12,octDot_coordinates,octMul,octConj,Quaternion.re_mul,
  Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,smul_eq_mul] <;> ring)

def frameAction (a : Octonion) := D (h 1) (X12 a)
theorem frameAction_coordinates (a : Octonion) (x : V) :
    (frameAction a x : Albert) =
      ⟨0,-(3/2 : ℝ)*octDot a (x : Albert).o12,
        (3/2 : ℝ)*octDot a (x : Albert).o12,
        -(3/4 : ℝ) • octMul (x : Albert).o02 (octConj a),
        (3/4 : ℝ) • octMul (x : Albert).o01 a,
        ((3/4 : ℝ)*((x : Albert).d1-(x : Albert).d2)) • a⟩ := by
  rw [frameAction,D_apply_native]; frameCalc

theorem frameAction_h0 (a : Octonion) : frameAction a (h 0) = 0 := by
  apply Subtype.ext; rw [frameAction_coordinates]; frameCalc

theorem D_h0_h1_zero : D (h 0) (h 1) = 0 := by
  ext1 v; apply Subtype.ext; rw [D_apply_native]; frameCalc
theorem D_X12_h0_zero (a : Octonion) : D (X12 a) (h 0) = 0 := by
  ext1 v; apply Subtype.ext; rw [D_apply_native]; frameCalc
end
end AlbertRecognition.FixedFrame
