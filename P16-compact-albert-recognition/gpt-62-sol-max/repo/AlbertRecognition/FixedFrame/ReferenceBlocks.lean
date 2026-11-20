/- Derived native reference-curvature blocks for the bounded fixed-frame gate.
D is the actual wedge plus KA commutator; no block identity is assumed. -/
module

public import AlbertRecognition.CubicOperators
public import Glennie.Sector

@[expose] public section
namespace AlbertRecognition.FixedFrame
noncomputable section
open Glennie

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
        gA y z • x := by simp [KA_apply, project_coe, traceless, jordan_sub_right, jordan_smul_right, jordan_unit_right, map_sub, map_smul, project_V, gA, Glennie.inner]

/-- Exact unit/trace splitting identifies D with the full Jordan commutator.
This uses bilinearity and associative trace pairing, not a Jordan identity. -/
theorem D_apply_project_native (x y z : V) :
    D x y z = project
      (jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
        jordan (y : Albert) (jordan (x : Albert) (z : Albert))) := by grind [D, q, operatorComm, KB_referenceCubic, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, wedge_apply, KA_projected_composition, map_sub]

theorem D_apply_native (x y z : V) :
    (D x y z : Albert) =
      jordan (x : Albert) (jordan (y : Albert) (z : Albert)) -
        jordan (y : Albert) (jordan (x : Albert) (z : Albert)) := by
  rw [D_apply_project_native, project_coe, traceless, trace_full_commutator]
  simp

/- Native coordinate projections of additive negation. These are definitional
identities for the inspected coordinate transport on Albert. -/

/-- Finite slot12 multiplication, preserving each native binary product. -/
private theorem jordan_slot12 (a : Octonion) (x : Albert) :
    jordan (X12 a : Albert) x =
      ⟨0,octDot a x.o12,octDot a x.o12,
        (1/2 : ℝ) • octMul x.o02 (octConj a),
        (1/2 : ℝ) • octMul x.o01 a,((x.d1+x.d2)/2) • a⟩ := by
  apply Albert.ext
  all_goals simp [X12, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_zero_left, octMul_zero_left,
    octMul_zero_right, octConj_zero, smul_smul, div_eq_mul_inv]
  all_goals first | ring | (congr 1 <;> ring)

private theorem h1_diagonalAlbert : (h 1 : Albert) = diagonalAlbert 1 (-2) 1 := by
  apply Albert.ext <;> norm_num [h, e, unit, diagonalAlbert]

/-- The operator uses the zero-based h1, complementary to the distinguished h0. -/
def frameAction (a : Octonion) : V →ₗ[ℝ] V := D (h 1) (X12 a)

private theorem h0_diagonalAlbert : (h 0 : Albert) = diagonalAlbert (-2) 1 1 := by
  apply Albert.ext <;> norm_num [h, e, unit, diagonalAlbert]

/-- The distinguished diagonal commutes with the two complementary actions. -/
theorem D_h0_h1_zero : D (h 0) (h 1) = 0 := by
  ext x : 1
  apply Subtype.ext
  rw [D_apply_native, h0_diagonalAlbert, h1_diagonalAlbert]
  apply Albert.ext <;> norm_num [diagonal_jordan, smul_smul] 

theorem D_h0_X12_zero (a : Octonion) : D (h 0) (X12 a) = 0 := by
  ext x : 1
  apply Subtype.ext
  simp only [D_apply_native, h0_diagonalAlbert, diagonal_jordan, jordan_slot12]
  apply Albert.ext <;>
    norm_num [octDot_smul_right, octMul_neg_left, octMul_smul_left, smul_smul] 

theorem frameAction_apply (a : Octonion) (x : V) :
    (frameAction a x : Albert) = let v := (x : Albert)
      (3/4 : ℝ) • (⟨0, -2 * octDot a v.o12, 2 * octDot a v.o12,
        -octMul v.o02 (octConj a), octMul v.o01 a, (v.d1-v.d2) • a⟩ : Albert) := by
  simp only [frameAction, D_apply_native, h1_diagonalAlbert, diagonal_jordan, jordan_slot12]
  have hneg (x y : Octonion) : octDot x (-y) = -octDot x y := by
    simpa only [neg_one_smul, neg_one_mul] using octDot_smul_right (-1) x y
  apply Albert.ext <;> norm_num [octDot_smul_right, hneg, octMul_smul_left, octMul_neg_left, smul_smul] <;>
    first | (ring; done) | module


end
end AlbertRecognition.FixedFrame
