module

public import Glennie.Sector

public import Glennie.Theorems.CubicNorm

public import Glennie.Native.CubicIdentity
public import Glennie.BasicLaws
public import Glennie.Theorems.Frames
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FinCases
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

public import Glennie.Obligations

/- Resolution by arbitrary diagonal frame atoms, without a canonical permutation. -/

public section
namespace Glennie
noncomputable section

theorem diagonalAlbert_representation (x : Albert) (hx : IsDiagonal x) :
    x = diagonalAlbert x.d0 x.d1 x.d2 := by
  apply Albert.ext <;> simp [diagonalAlbert,hx.1,hx.2.1,hx.2.2]

theorem jordan_diagonalAlbert (a b c d e f : ℝ) :
    jordan (diagonalAlbert a b c) (diagonalAlbert d e f) =
      diagonalAlbert (a*d) (b*e) (c*f) := by
  ext <;> simp [diagonalAlbert,jordan_d0,jordan_d1,jordan_d2,
    jordan_o01,jordan_o02,jordan_o12,octDot_coordinates,octMul,octConj,
    octNormSq,Quaternion.normSq_def']

/-- Frame encoders diagonalize with zero determinant and fixed discriminant square. -/
theorem diagonal_frame_encoder_cubic_zero (p : Fin 3 → Albert) (hp : Frame p)
    (he : IsDiagonal (encoder p)) :
    (encoder p).d0*(encoder p).d1*(encoder p).d2 = 0 := by
  have h := frame_encoder_cubicNorm p hp
  rw [diagonalAlbert_representation (encoder p) he,newtonCubicNorm_coordinates] at h
  simp_all [diagonalAlbert, octNormSq, Quaternion.normSq_def', octMul, octConj, octRe]

end
end Glennie
