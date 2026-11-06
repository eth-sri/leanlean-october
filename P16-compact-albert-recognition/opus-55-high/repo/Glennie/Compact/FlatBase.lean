/- The flat base, read through the dictionary, gives actual native frames
  P = projectorFrame x,  Q = projectorFrame y,  R = projectorFrame z,
with x = -witnessX, y = s * Y1, z = s * witnessZ and s = 1/sqrt 3. Here
witnessX and witnessZ are the literals of Native/Statements, and Y1
is the flat y at s = 1.
  * phi(P, Q, R) = -4/27. The first-frame reversal P' = projectorFrame witnessX
    (proved equal to reverseFrame P) has phi(P', Q, R) = +4/27.
  * Both triples have the uniform ledger (all 27 raw triple traces 1/9), by
    the `frame_equality`, and all 27 pair overlaps 1/3. So the two
    opposite-sign triples share the same complete 54-entry ledger.
The literal computation, phi(witnessX, Y1, witnessZ) = 4, follows the
Theorems/Witness.lean pattern. -/
module

public import Glennie.Compact.NativeDictionaryLiteral
public import Glennie.Theorems.ProjectorFrame
public import Glennie.Theorems.Frames
public import Glennie.Theorems.FrameEquality
public import Glennie.BasicLaws

@[expose] public section

namespace Glennie.Compact.FlatBase


noncomputable section

set_option maxHeartbeats 2000000

/-! ## The flat elements and their coordinates -/

/-- s = theta^-1 = 1/sqrt 3. -/
def flatScale : ℝ := 1 / Real.sqrt 3

theorem flatScale_sq : flatScale ^ 2 = 1 / 3 := by simp [flatScale]

/-- The flat x = diag(1, 0, -1). -/
def flatXN : Albert := ⟨1, 0, -1, 0, 0, 0⟩

/-- The flat y at s = 1. -/
def flatY1 : Albert := ⟨0, 0, 0, octScalar 1, -octI, octScalar 1⟩

theorem flatXN_eq : flatXN = (-1 : ℝ) • witnessX := by
  refine Albert.ext ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Albert.smul_d0]
    norm_num [flatXN, witnessX]
  · rw [Albert.smul_d1]
    norm_num [flatXN, witnessX]
  · aesop
  · rw [Albert.smul_o01]
    simp [flatXN, witnessX]
  · rw [Albert.smul_o02]
    simp [flatXN, witnessX]
  · rw [Albert.smul_o12]
    simp [flatXN, witnessX]

/-! ## Literal invariants (Witness.lean pattern) -/

theorem flat_traces :
    trace flatXN = 0 ∧ trace witnessX = 0 ∧ trace flatY1 = 0 ∧ trace witnessZ = 0 := by
  norm_num [trace, flatXN, witnessX, flatY1, witnessZ]

theorem flat_norms : inner flatXN flatXN = 2 ∧ inner witnessX witnessX = 2 ∧
    inner flatY1 flatY1 = 6 ∧ inner witnessZ witnessZ = 6 := by
  norm_num [inner_self_coordinates, flatXN, witnessX, flatY1, witnessZ, oct_simps, octI, octJL, octL, octK, quatI, quatJ, quatK]

theorem flat_cubic_norms : newtonCubicNorm flatXN = 0 ∧ newtonCubicNorm witnessX = 0 ∧
    newtonCubicNorm flatY1 = 0 ∧ newtonCubicNorm witnessZ = 0 := by
  norm_num [newtonCubicNorm_coordinates, flatXN, witnessX, flatY1, witnessZ, oct_simps, octI, octJL, octL, octK, quatI, quatJ, quatK, octRe]

/-- witnessX o Y1 (equal to the private witnessXY). -/
def flatBaseXY : Albert := ⟨0, 0, 0,
  ((⟨(-1/2 : ℝ), 0, 0, 0⟩ : Quaternion ℝ), 0), 0,
  ((⟨(1/2 : ℝ), 0, 0, 0⟩ : Quaternion ℝ), 0)⟩

/-- U witnessX (U Y1 witnessZ). -/
def flatBaseFirstU : Albert := ⟨0, 0, 0, 0,
  ((⟨0, 0, -1, 0⟩ : Quaternion ℝ), (⟨-1, 0, 0, -1⟩ : Quaternion ℝ)), 0⟩

/-- U Y1 (U witnessX witnessZ). -/
def flatBaseSecondU : Albert := ⟨0, 0, 0,
  (0, (⟨0, 1, 0, 0⟩ : Quaternion ℝ)),
  (0, (⟨-1, 0, 0, 0⟩ : Quaternion ℝ)),
  (0, (⟨0, -1, 0, 0⟩ : Quaternion ℝ))⟩

/-- U witnessZ (witnessX o Y1). -/
def flatBaseThirdU : Albert := ⟨0, 0, 0,
  ((⟨(1/2 : ℝ), 0, 0, 0⟩ : Quaternion ℝ), (⟨0, (-1/2 : ℝ), 0, 0⟩ : Quaternion ℝ)),
  ((⟨0, 0, (-1/2 : ℝ), 0⟩ : Quaternion ℝ), (⟨0, 0, 0, (-1/2 : ℝ)⟩ : Quaternion ℝ)),
  ((⟨(-1/2 : ℝ), 0, 0, 0⟩ : Quaternion ℝ), (⟨0, (1/2 : ℝ), 0, 0⟩ : Quaternion ℝ))⟩

theorem flat_xy : jordan witnessX flatY1 = flatBaseXY := by
  ext <;> norm_num [flatBaseXY, witnessX, flatY1, octI, quatI, oct_simps]

theorem flat_first_u : U witnessX (U flatY1 witnessZ) = flatBaseFirstU := by ext <;> norm_num [U, flatBaseFirstU, witnessX, flatY1, witnessZ, octI, octJ, octK, octL, octJL, quatI, quatJ, quatK, oct_simps, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]

theorem flat_second_u : U flatY1 (U witnessX witnessZ) = flatBaseSecondU := by
  ext <;> norm_num [U, flatBaseSecondU, witnessX, flatY1, witnessZ, octI, octJ, octK, octL, octJL, quatI, quatJ, quatK, oct_simps]

theorem flat_third_u : U witnessZ (jordan witnessX flatY1) = flatBaseThirdU := by
  rw [flat_xy]
  ext <;> norm_num [U, flatBaseXY, flatBaseThirdU, witnessZ, octJ, octK, octL, octJL, quatI, quatJ, quatK, oct_simps]

/-- The one new scalar: phi(witnessX, Y1, witnessZ) = 4. -/
theorem phi_witnessX_flatY1_witnessZ : phi witnessX flatY1 witnessZ = 4 := by
  rw [phi, flat_first_u, flat_second_u, flat_third_u]
  norm_num [inner_coordinates, octDot_coordinates, flatBaseFirstU, flatBaseSecondU,
    flatBaseThirdU]

/-! ## Frames, first-frame reversal and the shared complete ledger -/

/-- First-frame reversal of an ordered frame. -/
def reverseFrame (p : Fin 3 → Albert) : Fin 3 → Albert := ![p 2, p 1, p 0]

theorem reverseFrame_reverseFrame (p : Fin 3 → Albert) :
    reverseFrame (reverseFrame p) = p := by
  funext i
  fin_cases i <;> rfl

theorem projectorFrame_neg_one_smul (x : Albert) :
    projectorFrame ((-1 : ℝ) • x) = reverseFrame (projectorFrame x) := by
  have hxx : jordan ((-1 : ℝ) • x) ((-1 : ℝ) • x) = jordan x x := by simp
  funext i
  fin_cases i
  · show (1 / 2 : ℝ) • (jordan ((-1 : ℝ) • x) ((-1 : ℝ) • x) - (-1 : ℝ) • x) =
      (1 / 2 : ℝ) • (jordan x x + x)
    rw [hxx]
    module
  · show (1 : Albert) - jordan ((-1 : ℝ) • x) ((-1 : ℝ) • x) = 1 - jordan x x
    rw [hxx]
  · show (1 / 2 : ℝ) • (jordan ((-1 : ℝ) • x) ((-1 : ℝ) • x) + (-1 : ℝ) • x) =
      (1 / 2 : ℝ) • (jordan x x - x)
    rw [hxx]
    module

def flatFrameP : Fin 3 → Albert := projectorFrame flatXN
def flatFrameQ : Fin 3 → Albert := projectorFrame (flatScale • flatY1)
def flatFrameR : Fin 3 → Albert := projectorFrame (flatScale • witnessZ)
/-- The opposite-sign partner: first-frame reversal of flatFrameP. -/
def flatFramePRev : Fin 3 → Albert := projectorFrame witnessX

theorem flatFramePRev_eq_reverse : flatFramePRev = reverseFrame flatFrameP := by
  show projectorFrame witnessX = reverseFrame (projectorFrame flatXN)
  rw [flatXN_eq, projectorFrame_neg_one_smul, reverseFrame_reverseFrame]

theorem flatFrameP_frame : Frame flatFrameP :=
  projectorFrame_is_frame flatXN flat_traces.1 flat_norms.1 flat_cubic_norms.1

theorem flatFramePRev_frame : Frame flatFramePRev :=
  projectorFrame_is_frame witnessX flat_traces.2.1 flat_norms.2.1 flat_cubic_norms.2.1

theorem flatFrameQ_frame : Frame flatFrameQ := by
  apply projectorFrame_is_frame
  · rw [trace_smul, flat_traces.2.2.1, mul_zero]
  · rw [inner_smul_left, inner_smul_right, flat_norms.2.2.1]
    linear_combination 6 * flatScale_sq
  · rw [newtonCubicNorm_smul, flat_cubic_norms.2.2.1, mul_zero]

theorem flatFrameR_frame : Frame flatFrameR := by
  apply projectorFrame_is_frame
  · rw [trace_smul, flat_traces.2.2.2, mul_zero]
  · rw [inner_smul_left, inner_smul_right, flat_norms.2.2.2]
    linear_combination 6 * flatScale_sq
  · rw [newtonCubicNorm_smul, flat_cubic_norms.2.2.2, mul_zero]

theorem flatFrameP_encoder : encoder flatFrameP = flatXN := projectorFrame_encoder _
theorem flatFramePRev_encoder : encoder flatFramePRev = witnessX := projectorFrame_encoder _
theorem flatFrameQ_encoder : encoder flatFrameQ = flatScale • flatY1 := projectorFrame_encoder _
theorem flatFrameR_encoder : encoder flatFrameR = flatScale • witnessZ := projectorFrame_encoder _

theorem flat_phi :
    phi (encoder flatFrameP) (encoder flatFrameQ) (encoder flatFrameR) = -4 / 27 := by
  rw [flatFrameP_encoder, flatFrameQ_encoder, flatFrameR_encoder, flatXN_eq,
    phi_smul_first, phi_smul_second, phi_smul_third, phi_witnessX_flatY1_witnessZ]
  calc
    _ = -4 * (flatScale ^ 2) ^ 3 := by ring
    _ = -4 / 27 := by rw [flatScale_sq]; norm_num

theorem flatRev_phi :
    phi (encoder flatFramePRev) (encoder flatFrameQ) (encoder flatFrameR) = 4 / 27 := by
  rw [flatFramePRev_encoder, flatFrameQ_encoder, flatFrameR_encoder,
    phi_smul_second, phi_smul_third, phi_witnessX_flatY1_witnessZ]
  calc
    _ = 4 * (flatScale ^ 2) ^ 3 := by ring
    _ = 4 / 27 := by rw [flatScale_sq]; norm_num

/-- All 27 raw triple traces are 1/9, by the audited frame equality. -/
theorem flat_uniform : UniformLedger flatFrameP flatFrameQ flatFrameR :=
  (frame_equality flatFrameP flatFrameQ flatFrameR flatFrameP_frame flatFrameQ_frame
    flatFrameR_frame).mp (by rw [flat_phi, abs_of_neg (by norm_num)]; norm_num)

theorem flatRev_uniform : UniformLedger flatFramePRev flatFrameQ flatFrameR :=
  (frame_equality flatFramePRev flatFrameQ flatFrameR flatFramePRev_frame flatFrameQ_frame
    flatFrameR_frame).mp (by rw [flatRev_phi, abs_of_pos (by norm_num)])

/-- The three 9-entry pair-overlap blocks of a uniform frame triple are all 1/3. -/
theorem uniform_pair_blocks (p q r : Fin 3 → Albert) (hp : Frame p) (hq : Frame q)
    (hr : Frame r) (hu : UniformLedger p q r) (i j : Fin 3) :
    inner (p i) (q j) = 1 / 3 ∧ inner (q i) (r j) = 1 / 3 ∧ inner (r i) (p j) = 1 / 3 :=
  ⟨uniformLedger_pair_overlap p q r hr hu i j,
    uniformLedger_pair_overlap q r p hp (uniformLedger_cyclic p q r hu) i j,
    uniformLedger_pair_overlap r p q hq
      (uniformLedger_cyclic q r p (uniformLedger_cyclic p q r hu)) i j⟩

theorem flatFrameP_literal (i : Fin 3) :
    flatFrameP i =
      ![diagonalAlbert 0 0 1, diagonalAlbert 0 1 0,
        diagonalAlbert 1 0 0] i := by
  fin_cases i <;> ext <;>
    norm_num [flatFrameP, projectorFrame, flatXN, diagonalAlbert, oct_simps]

theorem flatFrameQ_literal (j : Fin 3) :
    flatFrameQ j =
      ![(⟨1 / 3, 1 / 3, 1 / 3,
          ((⟨-flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨1 / 6, flatScale / 2, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨-flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
        ⟨1 / 3, 1 / 3, 1 / 3,
          ((⟨0, 1 / 3, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨-1 / 3, 0, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨0, 1 / 3, 0, 0⟩ : Quaternion ℝ), 0)⟩,
        ⟨1 / 3, 1 / 3, 1 / 3,
          ((⟨flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨1 / 6, -flatScale / 2, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0)⟩] j := by
  fin_cases j <;> ext <;>
    simp [flatFrameQ, projectorFrame, flatY1, octI, quatI, oct_simps] <;>
    ring_nf <;> norm_num [flatScale_sq]

theorem flatFrameR_literal (k : Fin 3) :
    flatFrameR k =
      ![(⟨1 / 3, 1 / 3, 1 / 3,
          (0, (⟨0, 0, -flatScale / 2, 1 / 6⟩ : Quaternion ℝ)),
          (0, (⟨flatScale / 2, 1 / 6, 0, 0⟩ : Quaternion ℝ)),
          ((⟨0, 0, -1 / 6, flatScale / 2⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
        ⟨1 / 3, 1 / 3, 1 / 3,
          (0, (⟨0, 0, 0, -1 / 3⟩ : Quaternion ℝ)),
          (0, (⟨0, -1 / 3, 0, 0⟩ : Quaternion ℝ)),
          ((⟨0, 0, 1 / 3, 0⟩ : Quaternion ℝ), 0)⟩,
        ⟨1 / 3, 1 / 3, 1 / 3,
          (0, (⟨0, 0, flatScale / 2, 1 / 6⟩ : Quaternion ℝ)),
          (0, (⟨-flatScale / 2, 1 / 6, 0, 0⟩ : Quaternion ℝ)),
          ((⟨0, 0, -1 / 6, -flatScale / 2⟩ : Quaternion ℝ), 0)⟩] k := by
  fin_cases k <;> ext <;>
    simp [flatFrameR, projectorFrame, witnessZ, octJL, octL, octK, quatJ, quatK, oct_simps] <;>
    ring_nf <;> norm_num [flatScale_sq]

theorem flatScale_eq_sqrt3_div_three : flatScale = Real.sqrt 3 / 3 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := by simp
  dsimp [flatScale]
  apply (div_eq_div_iff hn (by norm_num : (3 : ℝ) ≠ 0)).2
  nlinarith 

end
end Glennie.Compact.FlatBase
