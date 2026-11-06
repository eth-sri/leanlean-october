/- Unrestricted native q-fiber recovery after the actual Albert kernel line.
no Euclidean coefficient identification is assumed here. -/
module

public import AlbertRecognition.FixedFrame.KernelLine

@[expose] public section
namespace AlbertRecognition
section
open FixedFrame Glennie

theorem q_reference_ne_zero : q referenceCubic ≠ 0 := by
  intro hz
  have hv := congrArg (fun T : V → V → Module.End ℝ V => T (h 0) (h 1) (h 0)) hz
  simp only [q, KB_referenceCubic, operatorComm_apply,
    KA_h_cross 1 0 (by decide), KA_h_cross 0 1 (by decide),
    KA_h_self, map_add, map_smul] at hv
  have hd := congrArg (fun x : V => (x : Albert).d1) hv
  norm_num [h, e, unit] at hd

/-- Every competitor is constrained solely by equality of the actual native q.
Universal operator Jacobi supplies kernel membership; the true reference
kernel line and nonzero witness force the only possible scales to be ±1. -/
theorem q_fiber_reference (B : SymmetricCubic) (hq : q B = q referenceCubic) :
    B = referenceCubic ∨ B = scalarCubic (-1) referenceCubic := by
  have hB : A (q referenceCubic) B = 0 := by
    rw [← hq]
    exact A_q_self B
  obtain ⟨b,hb⟩ := common_scalar_on_reference_frames B hB
  have hK : KB B = b • KA := by
    apply ReferenceTransport.linear_ext_on_directions (KB B) (b • KA)
    intro i
    change KB B (automorphismV (ReferenceTransport.transporter i) (h 0)) =
      b • KA (automorphismV (ReferenceTransport.transporter i) (h 0))
    exact hb (ReferenceTransport.transporter i) 0
  have hb : B = scalarCubic b referenceCubic := by
    apply KB_injective
    rw [KB_scalarCubic, KB_referenceCubic]
    exact hK
  have hs : b^2 • q referenceCubic = (1 : ℝ) • q referenceCubic := by
    rw [one_smul, ← q_scalarCubic, ← hb]
    exact hq
  have hb2 := smul_left_injective ℝ q_reference_ne_zero hs
  rcases sq_eq_one_iff.mp hb2 with hb1 | hbm1
  · left
    rw [hb1, scalarCubic_one] at hb
    exact hb
  · right
    simpa only [hbm1] using hb

end
end AlbertRecognition
