/- Unrestricted native q-fiber recovery after the actual Albert kernel line.
no Euclidean coefficient identification is assumed here. -/
module

public import AlbertRecognition.FixedFrame.KernelLine
@[expose] public section
namespace AlbertRecognition
noncomputable section
open FixedFrame Glennie

/-- An explicit native witness for nonzero quadratic reference curvature. -/
theorem q_reference_h0_h1_h0 :
    q referenceCubic (h 0) (h 1) (h 0) = h 0 + (2 : ℝ) • h 1 := by
  have hzero : octNormSq 0 = 0 := (octNormSq_eq_zero 0).mpr rfl
  apply Subtype.ext
  apply Albert.ext <;> norm_num [q, KB_referenceCubic, operatorComm_apply, KA_apply,
    project_coe, traceless, trace, h, e, unit, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj, hzero]

theorem q_reference_ne_zero : q referenceCubic ≠ 0 := by
  intro hz
  have hv := congrArg (fun T : V → V → Module.End ℝ V => T (h 0) (h 1) (h 0)) hz
  rw [q_reference_h0_h1_h0] at hv
  change h 0 + (2 : ℝ) • h 1 = 0 at hv
  have hd := congrArg (fun x : V => (x : Albert).d1) hv
  norm_num [h, e, unit] at hd

/-- Universal Jacobi puts a curvature match on the reference cubic line;
its nonzero curvature fixes the square of the scale. -/
theorem q_fiber_reference (B : SymmetricCubic) (hq : q B = q referenceCubic) :
    ∃ b : ℝ, b * b = 1 ∧ B = scalarCubic b referenceCubic := by
  obtain ⟨b,rfl⟩ := reference_nativeKernelLine B (hq ▸ A_q_self B)
  have hs : (b * b) • q referenceCubic = (1 : ℝ) • q referenceCubic := by
    simpa [q_scalarCubic, pow_two] using hq
  exact ⟨b, smul_left_injective ℝ q_reference_ne_zero hs, rfl⟩

end
end AlbertRecognition
