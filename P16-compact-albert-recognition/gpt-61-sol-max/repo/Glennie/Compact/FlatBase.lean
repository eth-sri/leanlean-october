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
public import Mathlib.Tactic

public import Glennie.Native.CoordinateSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Aesop

public import Glennie.Compact.NativeDictionaryLiteral
public import Glennie.Theorems.ProjectorFrame
public import Glennie.Theorems.Frames
public import Glennie.UnitShifts
public import Glennie.Native.Statements
public import Glennie.BasicLaws

@[expose] public section

namespace Glennie.Compact.FlatBase

open Glennie.Compact.NativeDictionary

noncomputable section

def flatScale : ℝ := 1 / Real.sqrt 3

theorem flatScale_sq : flatScale ^ 2 = 1 / 3 := by simp_all [flatScale]

/-- The flat x = diag(1, 0, -1). -/
def flatXN : Albert := ⟨1, 0, -1, 0, 0, 0⟩

/-- The flat y at s = 1. -/
def flatY1 : Albert := ⟨0, 0, 0, octScalar 1, -octI, octScalar 1⟩

theorem flatXN_eq : flatXN = (-1 : ℝ) • witnessX := by
  ext <;> norm_num [flatXN, witnessX]

/-! ## Literal invariants (Witness.lean pattern) -/

theorem flat_traces :
    trace flatXN = 0 ∧ trace witnessX = 0 ∧ trace flatY1 = 0 ∧ trace witnessZ = 0 := by
  norm_num [trace, flatXN, witnessX, flatY1, witnessZ]

theorem flat_norms : inner flatXN flatXN = 2 ∧ inner witnessX witnessX = 2 ∧
    inner flatY1 flatY1 = 6 ∧ inner witnessZ witnessZ = 6 := by
  norm_num [inner_self_coordinates, flatXN, witnessX, flatY1, witnessZ, octNormSq,
    Quaternion.normSq_def', octScalar, octI, octJL, octL, octK, quatI, quatJ, quatK]

theorem flat_cubic_norms : newtonCubicNorm flatXN = 0 ∧ newtonCubicNorm witnessX = 0 ∧
    newtonCubicNorm flatY1 = 0 ∧ newtonCubicNorm witnessZ = 0 := by
  norm_num [albert_coords, newtonCubicNorm_coordinates, flatXN, witnessX, flatY1, witnessZ, octI, octJL, octL, octK, quatI, quatJ, quatK]

















/-- The one new scalar: phi(witnessX, Y1, witnessZ) = 4. -/
theorem phi_witnessX_flatY1_witnessZ : phi witnessX flatY1 witnessZ = 4 := by
  norm_num [phi, U, flatY1, witnessX, witnessZ, octI, octK, octL, octJL,
    quatI, quatJ, quatK, albert_coords, QuaternionAlgebra.re_ofNat,
    QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]

                                                                     

                                                
                                                                          

                                                        
                                           
          
                     

                                                  
                                                                         
                                                                    
                                                                                       
          
             
                                                                              
                                    
            
          
                                                                             
            
                                                                              
                                    
            
          

def flatFrameP : Fin 3 → Albert := projectorFrame flatXN
def flatFrameQ : Fin 3 → Albert := projectorFrame (flatScale • flatY1)
def flatFrameR : Fin 3 → Albert := projectorFrame (flatScale • witnessZ)
                                                                     
                                                             

                                                                                
                                                                     
                                                                        

theorem flatFrameP_frame : Frame flatFrameP :=
  projectorFrame_is_frame flatXN flat_traces.1 flat_norms.1 flat_cubic_norms.1

                                                    
                                                                                      

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
                                                                                            
theorem flatFrameQ_encoder : encoder flatFrameQ = flatScale • flatY1 := projectorFrame_encoder _
theorem flatFrameR_encoder : encoder flatFrameR = flatScale • witnessZ := projectorFrame_encoder _

theorem flat_phi :
    phi (encoder flatFrameP) (encoder flatFrameQ) (encoder flatFrameR) = -4 / 27 := by
  grind [flatFrameP_encoder, flatFrameQ_encoder, flatFrameR_encoder, flatXN_eq, phi_smul_first, phi_smul_second, phi_smul_third, phi_witnessX_flatY1_witnessZ, flatScale_sq]

                     
                                                                                        
                                                                    
                                                                  
      
                                          
                                                

theorem flatFrameP_literal (i : Fin 3) :
    flatFrameP i =
      ![diagonalAlbert 0 0 1, diagonalAlbert 0 1 0,
        diagonalAlbert 1 0 0] i := by
  fin_cases i <;> ext <;>
    norm_num [albert_coords, flatFrameP, projectorFrame, flatXN, diagonalAlbert]

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
    simp [albert_coords, flatFrameQ, projectorFrame, flatY1, octI, quatI] <;>
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
    simp [albert_coords, flatFrameR, projectorFrame, witnessZ, octJL, octL, octK, quatJ, quatK] <;>
    ring_nf <;> norm_num [flatScale_sq]

theorem flat_uniform : UniformLedger flatFrameP flatFrameQ flatFrameR := by
  intro i j k
  change inner (jordan (flatFrameP i) (flatFrameQ j)) (flatFrameR k) = 1 / 9
  rw [flatFrameP_literal, flatFrameQ_literal, flatFrameR_literal]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [albert_coords, diagonalAlbert]

                                                                                 
             
                               
             
                                                                
                            
                                                                
                            
                                                                
                            

/-- The three 9-entry pair-overlap blocks of a uniform frame triple are all 1/3. -/
theorem uniform_pair_blocks (p q r : Fin 3 → Albert) (hp : Frame p) (hq : Frame q)
    (hr : Frame r) (hu : UniformLedger p q r) (i j : Fin 3) :
    inner (p i) (q j) = 1 / 3 ∧ inner (q i) (r j) = 1 / 3 ∧ inner (r i) (p j) = 1 / 3 :=
  ⟨uniformLedger_pair_overlap p q r hr hu i j,
    uniformLedger_pair_overlap q r p hp (uniformLedger_cyclic p q r hu) i j,
    uniformLedger_pair_overlap r p q hq
      (uniformLedger_cyclic q r p (uniformLedger_cyclic p q r hu)) i j⟩

end
end Glennie.Compact.FlatBase
