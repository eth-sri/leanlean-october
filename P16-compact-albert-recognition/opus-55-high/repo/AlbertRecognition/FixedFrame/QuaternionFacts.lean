/- Finite quaternion coordinate lemmas for the compact native spin commutant.
No octonion associativity or classification theorem is used. -/
module

public import Glennie.Native

@[expose] public section

namespace AlbertRecognition.FixedFrame

open scoped Quaternion

def qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩
def qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
def qk : Quaternion ℝ := ⟨0, 0, 0, 1⟩

@[simp] theorem star_qi : star qi = -qi := by
  apply Quaternion.ext <;> simp [qi]
@[simp] theorem star_qj : star qj = -qj := by
  apply Quaternion.ext <;> simp [qj]
@[simp] theorem star_qk : star qk = -qk := by
  apply Quaternion.ext <;> simp [qk]
@[simp] theorem qi_mul_qj : qi * qj = qk := by
  apply Quaternion.ext <;> norm_num [qi, qj, qk]
@[simp] theorem qj_mul_qi : qj * qi = -qk := by
  apply Quaternion.ext <;> norm_num [qi, qj, qk]

/-- Characteristic zero, proved on the four actual quaternion coordinates. -/
theorem quat_neg_eq_self_zero (p : Quaternion ℝ) (hp : -p = p) : p = 0 := by
  have hr := congrArg QuaternionAlgebra.re hp
  have hi := congrArg QuaternionAlgebra.imI hp
  have hj := congrArg QuaternionAlgebra.imJ hp
  have hk := congrArg QuaternionAlgebra.imK hp
  simp at hr hi hj hk
  apply Quaternion.ext <;> simp <;> linarith

/-- Multiplication by the literal unit k is injective, without a division API. -/
theorem quat_right_k_zero (p : Quaternion ℝ) (hp : p * qk = 0) : p = 0 := by
  have hr := congrArg QuaternionAlgebra.re hp
  have hi := congrArg QuaternionAlgebra.imI hp
  have hj := congrArg QuaternionAlgebra.imJ hp
  have hk := congrArg QuaternionAlgebra.imK hp
  simp [qk] at hr hi hj hk
  apply Quaternion.ext <;> simp <;> linarith

/-- The common quaternion commutant of i and j is precisely the real line. -/
theorem quat_comm_i_j_real (p : Quaternion ℝ)
    (hi : qi * p = p * qi) (hj : qj * p = p * qj) :
    p = (p.re : Quaternion ℝ) := by
  have hiJ := congrArg QuaternionAlgebra.imJ hi
  have hiK := congrArg QuaternionAlgebra.imK hi
  have hjK := congrArg QuaternionAlgebra.imK hj
  simp [qi, qj] at hiJ hiK hjK
  apply Quaternion.ext <;> simp <;> linarith

/-- Simultaneously anticommuting with i,j,k forces all four coordinates to zero. -/
theorem quat_anticomm_i_j_k_zero (p : Quaternion ℝ)
    (hi : qi * p = -(p * qi)) (hj : qj * p = -(p * qj))
    (hk : qk * p = -(p * qk)) : p = 0 := by
  have hiR := congrArg QuaternionAlgebra.re hi
  have hiI := congrArg QuaternionAlgebra.imI hi
  have hjR := congrArg QuaternionAlgebra.re hj
  have hkR := congrArg QuaternionAlgebra.re hk
  simp [qi, qj, qk] at hiR hiI hjR hkR
  apply Quaternion.ext <;> simp <;> linarith

end AlbertRecognition.FixedFrame
