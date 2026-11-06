module

public import Glennie.Theorems.ProjectorFrame
public import Glennie.Theorems.Frames
public import Glennie.UnitShifts
public import Glennie.BasicLaws

@[expose] public section

namespace Glennie.Compact.FlatBase

noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

def flatScale : ℝ := 1 / Real.sqrt 3

theorem flatScale_sq : flatScale ^ 2 = 1 / 3 := by
  dsimp [flatScale]
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

def flatXN : Albert := ⟨1, 0, -1, 0, 0, 0⟩
def flatY1 : Albert := ⟨0, 0, 0, octScalar 1, -octI, octScalar 1⟩

theorem flatXN_eq : flatXN = (-1 : ℝ) • witnessX := by
  ext <;> simp only [Albert.smul_d0, Albert.smul_d1, Albert.smul_d2,
    Albert.smul_o01, Albert.smul_o02, Albert.smul_o12] <;>
    (try simp [flatXN, witnessX]) <;> norm_num [flatXN, witnessX]

theorem flat_traces :
    trace flatXN = 0 ∧ trace witnessX = 0 ∧ trace flatY1 = 0 ∧ trace witnessZ = 0 := by
  norm_num [trace, flatXN, witnessX, flatY1, witnessZ]

theorem flat_norms : inner flatXN flatXN = 2 ∧ inner witnessX witnessX = 2 ∧
    inner flatY1 flatY1 = 6 ∧ inner witnessZ witnessZ = 6 := by
  norm_num [inner_self_coordinates, flatXN, witnessX, flatY1, witnessZ, octNormSq,
    Quaternion.normSq_def', octScalar, octI, octJL, octL, octK, quatI, quatJ, quatK]

theorem flat_cubic_norms : newtonCubicNorm flatXN = 0 ∧ newtonCubicNorm witnessX = 0 ∧
    newtonCubicNorm flatY1 = 0 ∧ newtonCubicNorm witnessZ = 0 := by
  norm_num [newtonCubicNorm_coordinates, flatXN, witnessX, flatY1, witnessZ, octNormSq,
    Quaternion.normSq_def', octScalar, octI, octJL, octL, octK, quatI, quatJ, quatK,
    octMul, octConj, octRe, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]

theorem phi_witnessX_flatY1_witnessZ : phi witnessX flatY1 witnessZ = 4 := by
  rw [phi_of_diagonal_complex witnessX flatY1 witnessZ (by simp [IsDiagonal, witnessX])
    (by simp [InComplexSector, OctInComplex, flatY1, octScalar, octI, quatI])]
  simp [witnessX, flatY1, witnessZ, complexPart, hiddenMatrix, hiddenColumn,
    Matrix.det_fin_three, octScalar, octI, octJL, octL, octK, quatI, quatJ, quatK,
    Complex.mul_re, Complex.mul_im]
  norm_num

def flatFrameP : Fin 3 → Albert := projectorFrame flatXN
def flatFrameQ : Fin 3 → Albert := projectorFrame (flatScale • flatY1)
def flatFrameR : Fin 3 → Albert := projectorFrame (flatScale • witnessZ)

theorem flatFrameP_frame : Frame flatFrameP :=
  projectorFrame_is_frame flatXN flat_traces.1 flat_norms.1 flat_cubic_norms.1

theorem flatFrameQ_frame : Frame flatFrameQ :=
  projectorFrame_is_frame _ (by rw [trace_smul, flat_traces.2.2.1, mul_zero])
    (by rw [inner_smul_left, inner_smul_right, flat_norms.2.2.1]; linear_combination 6 * flatScale_sq)
    (by rw [newtonCubicNorm_smul, flat_cubic_norms.2.2.1, mul_zero])

theorem flatFrameR_frame : Frame flatFrameR :=
  projectorFrame_is_frame _ (by rw [trace_smul, flat_traces.2.2.2, mul_zero])
    (by rw [inner_smul_left, inner_smul_right, flat_norms.2.2.2]; linear_combination 6 * flatScale_sq)
    (by rw [newtonCubicNorm_smul, flat_cubic_norms.2.2.2, mul_zero])

theorem flatFrameP_encoder : encoder flatFrameP = flatXN := projectorFrame_encoder _
theorem flatFrameQ_encoder : encoder flatFrameQ = flatScale • flatY1 := projectorFrame_encoder _
theorem flatFrameR_encoder : encoder flatFrameR = flatScale • witnessZ := projectorFrame_encoder _

theorem flat_phi :
    phi (encoder flatFrameP) (encoder flatFrameQ) (encoder flatFrameR) = -4 / 27 := by
  rw [flatFrameP_encoder, flatFrameQ_encoder, flatFrameR_encoder, flatXN_eq,
    phi_smul_first, phi_smul_second, phi_smul_third, phi_witnessX_flatY1_witnessZ]
  calc
    _ = -4 * (flatScale ^ 2) ^ 3 := by ring
    _ = -4 / 27 := by rw [flatScale_sq]; norm_num

theorem flatScale_eq_sqrt3_div_three : flatScale = Real.sqrt 3 / 3 := by
  have hsq : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := fun h => by rw [h] at hsq; norm_num at hsq
  dsimp [flatScale]
  exact (div_eq_div_iff hn (by norm_num : (3 : ℝ) ≠ 0)).2 (by nlinarith [hsq])

theorem flatFrameP_literal (i : Fin 3) :
    flatFrameP i = ![diagonalAlbert 0 0 1, diagonalAlbert 0 1 0, diagonalAlbert 1 0 0] i := by
  fin_cases i <;> ext <;>
    norm_num [flatFrameP, projectorFrame, flatXN, diagonalAlbert,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

theorem flatFrameQ_literal (j : Fin 3) :
    flatFrameQ j =
      ![(⟨1 / 3, 1 / 3, 1 / 3,
          ((⟨-flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨1 / 6, flatScale / 2, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨-flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0)⟩ : Albert),
        ⟨1 / 3, 1 / 3, 1 / 3,
          ((⟨0, 1 / 3, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨-1 / 3, 0, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨0, 1 / 3, 0, 0⟩ : Quaternion ℝ), 0)⟩,
        ⟨1 / 3, 1 / 3, 1 / 3,
          ((⟨flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨1 / 6, -flatScale / 2, 0, 0⟩ : Quaternion ℝ), 0),
          ((⟨flatScale / 2, -1 / 6, 0, 0⟩ : Quaternion ℝ), 0)⟩] j := by
  fin_cases j <;> ext <;>
    simp [flatFrameQ, projectorFrame, flatY1, octI, quatI, octScalar,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring_nf <;> norm_num [flatScale_sq]

theorem flatFrameR_literal (k : Fin 3) :
    flatFrameR k =
      ![(⟨1 / 3, 1 / 3, 1 / 3,
          (0, (⟨0, 0, -flatScale / 2, 1 / 6⟩ : Quaternion ℝ)),
          (0, (⟨flatScale / 2, 1 / 6, 0, 0⟩ : Quaternion ℝ)),
          ((⟨0, 0, -1 / 6, flatScale / 2⟩ : Quaternion ℝ), 0)⟩ : Albert),
        ⟨1 / 3, 1 / 3, 1 / 3,
          (0, (⟨0, 0, 0, -1 / 3⟩ : Quaternion ℝ)),
          (0, (⟨0, -1 / 3, 0, 0⟩ : Quaternion ℝ)),
          ((⟨0, 0, 1 / 3, 0⟩ : Quaternion ℝ), 0)⟩,
        ⟨1 / 3, 1 / 3, 1 / 3,
          (0, (⟨0, 0, flatScale / 2, 1 / 6⟩ : Quaternion ℝ)),
          (0, (⟨-flatScale / 2, 1 / 6, 0, 0⟩ : Quaternion ℝ)),
          ((⟨0, 0, -1 / 6, -flatScale / 2⟩ : Quaternion ℝ), 0)⟩] k := by
  fin_cases k <;> ext <;>
    simp [flatFrameR, projectorFrame, witnessZ, octJL, octL, octK, quatJ, quatK,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring_nf <;> norm_num [flatScale_sq]

theorem flat_uniform : UniformLedger flatFrameP flatFrameQ flatFrameR := fun i j k => by
  change inner (jordan (flatFrameP i) (flatFrameQ j)) (flatFrameR k) = 1 / 9
  rw [inner_jordan_associative, flatFrameP_literal i, flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [diagonalAlbert, inner_coordinates, jordan_d0, jordan_d1, jordan_d2, octDot_coordinates]

theorem uniform_pair_blocks (p q r : Fin 3 → Albert) (hp : Frame p) (hq : Frame q)
    (hr : Frame r) (hu : UniformLedger p q r) (i j : Fin 3) :
    inner (p i) (q j) = 1 / 3 ∧ inner (q i) (r j) = 1 / 3 ∧ inner (r i) (p j) = 1 / 3 :=
  ⟨uniformLedger_pair_overlap p q r hr hu i j,
    uniformLedger_pair_overlap q r p hp (uniformLedger_cyclic p q r hu) i j,
    uniformLedger_pair_overlap r p q hq
      (uniformLedger_cyclic q r p (uniformLedger_cyclic p q r hu)) i j⟩

end
end Glennie.Compact.FlatBase
