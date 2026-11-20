/- Fixed compact complex-sector coordinates in the declared gauge.
The hidden columns are (-extract(o12), +extract(o02), -extract(o01)). -/
module
public import Glennie.Native.AlgebraLaws
public import Mathlib.Basic.Complex.Basic
@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

def complexPart (x : Octonion) : ℂ := ⟨x.1.re,x.1.imI⟩

def complexOct (z : ℂ) : Octonion := (⟨z.re,z.im,0,0⟩,0)

/-- The last imaginary coordinate has the sign i(jℓ)=−kℓ. -/
def hiddenColumn (x : Octonion) : Fin 3 → ℂ :=
  ![⟨x.1.imJ,x.1.imK⟩,⟨x.2.re,x.2.imI⟩,⟨x.2.imJ,-x.2.imK⟩]

def hiddenOct (v : Fin 3 → ℂ) : Octonion :=
  (⟨0,0,(v 0).re,(v 0).im⟩,⟨(v 1).re,(v 1).im,(v 2).re,-(v 2).im⟩)

def hiddenMatrix (z : Albert) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i => ![-hiddenColumn z.o12 i, hiddenColumn z.o02 i, -hiddenColumn z.o01 i]

def hiddenAlbert (M : Matrix (Fin 3) (Fin 3) ℂ) : Albert :=
  ⟨0,0,0,-hiddenOct (fun i => M i 2),hiddenOct (fun i => M i 1),
    -hiddenOct (fun i => M i 0)⟩

def complexProjection (z : Albert) : Albert :=
  ⟨z.d0,z.d1,z.d2,complexOct (complexPart z.o01),
    complexOct (complexPart z.o02),complexOct (complexPart z.o12)⟩

def diagonalAlbert (a b c : ℝ) : Albert := ⟨a,b,c,0,0,0⟩

def complexAlbert (a b c : ℝ) (u v w : ℂ) : Albert :=
  ⟨a,b,c,complexOct u,complexOct v,complexOct w⟩

theorem complex_hidden_decomposition (z : Albert) :
    complexProjection z + hiddenAlbert (hiddenMatrix z) = z := by
  apply Albert.ext
  all_goals simp [complexProjection, hiddenAlbert, hiddenMatrix, hiddenColumn,
    hiddenOct, complexPart, complexOct]

theorem complex_hidden_orthogonal (x : Albert) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    inner (complexProjection x) (hiddenAlbert M) = 0 := by
  simp [inner_coordinates, octDot_coordinates, complexProjection, hiddenAlbert,
    complexOct, hiddenOct]

def sectorColumnGram (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  M.conjTranspose * M

/-- A diagonal element scales the six Peirce blocks separately. -/
theorem diagonal_jordan (a b c : ℝ) (x : Albert) :
    jordan (diagonalAlbert a b c) x =
      ⟨a*x.d0,b*x.d1,c*x.d2,((a+b)/2) • x.o01,((a+c)/2) • x.o02,((b+c)/2) • x.o12⟩ := by
  apply Albert.ext <;> simp [diagonalAlbert, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_zero_left, octMul_zero_left,
    octMul_zero_right, octConj_zero, smul_smul] <;> congr 1 <;> ring

theorem U_diagonal (a b c : ℝ) (z : Albert) :
    U (diagonalAlbert a b c) z =
      ⟨a^2*z.d0,b^2*z.d1,c^2*z.d2,(a*b) • z.o01,
        (a*c) • z.o02,(b*c) • z.o12⟩ := by
  have h : jordan (diagonalAlbert a b c) (diagonalAlbert a b c) =
      diagonalAlbert (a*a) (b*b) (c*c) := by rw [diagonal_jordan]; simp [diagonalAlbert]
  rw [U, h]
  simp only [diagonal_jordan]
  apply Albert.ext <;> simp [smul_smul, ← sub_smul] <;> congr 1 <;> ring

end
end Glennie
