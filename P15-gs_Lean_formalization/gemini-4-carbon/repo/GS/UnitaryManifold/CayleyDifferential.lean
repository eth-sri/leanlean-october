module

public import GS.UnitaryManifold.CayleyCharts
public import GS.UnitaryManifold.MatrixCalculus

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix Filter
open scoped Topology
namespace GS.UnitaryManifold
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ} {block : Fin n → ℕ}

theorem chartInv_line_hasDerivAt_zero (Q : KBlockU 𝕂 block) (v : KModel 𝕂 block) :
    HasDerivAt (fun t : ℝ => chartInv Q (t • v)) ((-2 : ℝ) • (Q.val * v.val)) 0 := by
  let V := fderiv ℝ (chartInv Q) 0 v
  have hd : HasDerivAt (fun t : ℝ => chartInv Q (t • v)) V 0 :=
    (((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt).comp_hasDerivAt_of_eq 0
      (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)
  have hp : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin n) (Fin n) 𝕂) + t • v.val) v.val 0 := by
    simpa only [Pi.add_def, zero_add, id_eq, one_smul] using
      (hasDerivAt_const (0 : ℝ) (1 : Matrix (Fin n) (Fin n) 𝕂)).add ((hasDerivAt_id (0 : ℝ)).smul_const v.val)
  have hm : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin n) (Fin n) 𝕂) - t • v.val) (-v.val) 0 := by
    simpa only [Pi.sub_def, zero_sub, id_eq, one_smul] using
      (hasDerivAt_const (0 : ℝ) (1 : Matrix (Fin n) (Fin n) 𝕂)).sub ((hasDerivAt_id (0 : ℝ)).smul_const v.val)
  have hleft := hasDerivAt_matrix_mul hd hp
  have hright := hasDerivAt_matrix_mul (hasDerivAt_const (0 : ℝ) Q.val) hm
  have hid : (fun t : ℝ => chartInv Q (t • v) * (1 + t • v.val)) =
      (fun t : ℝ => Q.val * (1 - t • v.val)) := by
    funext t; change Q.val * cayley ((t • v).val) * (1 + (t • v).val) = _
    rw [Matrix.mul_assoc, cayley_mul _ (admissible_model (t • v))]; rfl
  rw [hid] at hleft
  have hv : V + Q.val * v.val = -(Q.val * v.val) := by
    simpa only [zero_smul, add_zero, sub_zero, chartInv_zero, Matrix.mul_one,
      Matrix.zero_mul, zero_add, Matrix.mul_neg] using hleft.unique hright
  have he : V = (-2 : ℝ) • (Q.val * v.val) := by
    rw [eq_sub_of_add_eq hv, neg_smul, two_smul]; abel
  rwa [he] at hd

end GS.UnitaryManifold
