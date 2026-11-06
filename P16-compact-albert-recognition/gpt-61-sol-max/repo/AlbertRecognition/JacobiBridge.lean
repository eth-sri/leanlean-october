/- Universal Jacobi bridge for an unrestricted symmetric cubic.
The wedge cancellation is derived from the actual metric-raised KB, and the
concrete frame step uses native reference vanishing identities.  This is an
algebraic prerequisite, not the log-Hessian/Levi-Civita recognition endpoint. -/
module

public import AlbertRecognition.FixedFrame.BlockSeparation

@[expose] public section
namespace AlbertRecognition
section



@[simp] theorem operatorComm_zero_right (P : V →ₗ[ℝ] V) :
    operatorComm P 0 = 0 := by
  simp [operatorComm]

theorem operatorComm_add_right (P Q R : V →ₗ[ℝ] V) :
    operatorComm P (Q + R) = operatorComm P Q + operatorComm P R := by
  simp only [operatorComm, LinearMap.comp_add, LinearMap.add_comp]
  abel

theorem operatorComm_swap (P Q : V →ₗ[ℝ] V) :
    operatorComm P Q = -operatorComm Q P := by
  simp [operatorComm, neg_sub]

theorem wedge_swap (x y : V) : wedge x y = -wedge y x := by
  apply LinearMap.ext
  intro v
  change gA y v • x - gA x v • y = -(gA x v • y - gA y v • x)
  exact (neg_sub _ _).symm

/-- Total cubic symmetry cancels the entire wedge Jacobi term.  KB symmetry
and self-adjointness are the derived metric-dual identities, not hypotheses. -/
theorem A_wedge_eq_zero (B : SymmetricCubic) : A wedge B = 0 := by
  funext x y z
  apply LinearMap.ext
  intro v
  simp only [A, operatorComm_apply, wedge, LinearMap.add_apply,
    LinearMap.zero_apply, Pi.zero_apply, LinearMap.coe_mk, AddHom.coe_mk, map_sub, map_smul]
  simp_rw [← KB_selfadjoint, KB_comm]
  module

/-- The actual cyclic commutator is additive in its reference tensor. -/
theorem A_add_target (T U : V → V → (V →ₗ[ℝ] V)) (B : SymmetricCubic) :
    A (fun x y => T x y + U x y) B = A T B + A U B := by
  funext x y z
  simp only [A, operatorComm_add_right, Pi.add_apply]
  module

/-- Adding the wedge term does not change the Jacobi equation on any cubic. -/
theorem A_D_eq_A_q (B : SymmetricCubic) :
    A D B = A (q referenceCubic) B := by
  change A (fun x y => wedge x y + q referenceCubic x y) B = _
  rw [A_add_target, A_wedge_eq_zero, zero_add]

theorem D_swap (x y : V) : D y x = -D x y := by
  unfold D q
  rw [wedge_swap y x, operatorComm_swap (KB referenceCubic y) (KB referenceCubic x)]
  module

namespace FixedFrame

/-- The unrestricted unknown's h0 operator commutes with every actual native
frameAction.  The only input is the literal reference-q Jacobi kernel equation. -/
theorem h0_frame_commutes_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) (a : Glennie.Octonion) :
    operatorComm (KB B (h 0)) (frameAction a) = 0  := by
  rw [← A_D_eq_A_q] at hB
  have hzx : D (X12 a) (h 0) = 0 := by rw [D_swap, D_h0_X12_zero, neg_zero]
  have hcyclic := congrArg (fun F => F (h 0) (h 1) (X12 a)) hB
  simpa only [frameAction, A, hzx, D_h0_h1_zero, Pi.zero_apply, operatorComm_zero_right, zero_add, add_zero] using hcyclic

/-- Application form used by the subsequent native block-commutant argument. -/
theorem h0_frame_action_intertwines_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) (a : Glennie.Octonion) (v : V) :
    KB B (h 0) (frameAction a v) = frameAction a (KB B (h 0) v) := by
  have hcomm := congrArg (fun P : V →ₗ[ℝ] V => P v)
    (h0_frame_commutes_of_A_q_zero B hB a)
  change KB B (h 0) (frameAction a v) - frameAction a (KB B (h 0) v) = 0 at hcomm
  exact sub_eq_zero.mp hcomm

end FixedFrame
end
end AlbertRecognition
