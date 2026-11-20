module
public import Glennie.Native.SectorAction
public import Glennie.Native.SectorArgumentAction
public import Glennie.Native.Quaternionic
public import Glennie.SectorFactorWeight

/-! For a complex pair, the cubic in the last argument has a visible term,
a term linear in the hidden Gram matrix, and a determinant term. Every Gram
matrix is the sum of the Grams of its rows. Each row alone fits in the special
quaternionic subalgebra, so both lower terms vanish there and hence everywhere. -/
@[expose] public section
namespace Glennie
noncomputable section
open SectorAction SectorArgumentAction SectorFactorWeight
private abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ
private abbrev H := sectorComplexMatrix
private abbrev m := hiddenMatrix
private def comm (D H K : M3) := D*H*K*H*D-H*D*K*D*H
private def mix (Q S K B G : M3) := (Q * gamma G B).trace +
  2 * (S.conjTranspose * G * ((K*B).trace • (1:M3)-K*B)).trace
private theorem mix_add (Q S K B G N : M3) : mix Q S K B (G+N) = mix Q S K B G + mix Q S K B N := by
  simp only [mix,gamma,Matrix.add_mul,Matrix.mul_add,Matrix.mul_sub,Matrix.trace_add,Matrix.trace_sub,
    mul_add,add_mul,smul_add,add_smul,sub_smul,smul_sub, Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]; ring

private def gram (M : M3) := M.conjTranspose * M
private def row (M : M3) (i : Fin 3) : M3 := fun j k => if j=0 then M i k else 0
private theorem grams (M : M3) : gram M = gram (row M 0) + gram (row M 1) + gram (row M 2) := by
  ext i j : 1; simp [gram,row,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_three]
private theorem cubic (M S B : M3) : ((M*S).conjTranspose * (sectorAdjointAdjugate M * B)).trace =
    star M.det * (S.conjTranspose*B).trace := by
  have h : M.conjTranspose * sectorAdjointAdjugate M = star M.det • (1:M3) := by
    simpa [sectorAdjointAdjugate] using congrArg Matrix.conjTranspose (Matrix.adjugate_mul M)
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,← Matrix.mul_assoc _ (sectorAdjointAdjugate M),h]; simp

private theorem split {x y : Albert} (hx : m x = 0) (hy : m y = 0) (z : Albert) :
    let Q := comm (H x) (H y) (H z); let S := adjugateCommutator (H x) (H y); let B := H (jordan x y)
    phi x y z = (Q * (H z*B*H z)).trace.re + (mix Q S (H z) B (gram (m z))).re +
      2*(star (m z).det * (S.conjTranspose*B).trace).re := by
  have hb : m (jordan x y) = 0 := by simp [m,hiddenMatrix_jordan,hx,hy,productHidden_complex_left]
  have c := complex_commutator x y z hx hy; have s := hidden_commutator x y z hx hy
  simp only [phi,inner_sector_model,c,s,complex_U_argument z _ hb,hidden_U_argument z _ hb,Matrix.mul_add,Matrix.trace_add,Complex.add_re,
    comm,adjugateCommutator,H,m,gram,mix,cubic]
  simp [Matrix.mul_assoc,Complex.mul_re]; ring

theorem phi_diagonal_complex_factor (a b c d e f : ℝ) (u v w : ℂ) (z : Albert) :
    phi (diagonalAlbert a b c) (complexAlbert d e f u v w) z =
      (2*(a-b)*(b-c)*(c-a)*(u*w*star v).im) * (hiddenMatrix z).det.im := by
  let x := diagonalAlbert a b c; let y := complexAlbert d e f u v w
  let K := H z; let M := m z; let B := H (jordan x y)
  let S := adjugateCommutator (H x) (H y); let Q := comm (H x) (H y) K
  let F := mix Q S K B
  have hx : m x = 0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [x,m,hiddenMatrix,hiddenColumn,diagonalAlbert] <;> rfl
  have hy : m y = 0 := hiddenMatrix_complexAlbert ((d,e,f),(u,v,w))
  let pureTerm := (Q * (K*B*K)).trace.re
  have test (N : M3) (i : Fin 3) : pureTerm + (F (gram (row N i))).re = 0 := by
    let q := sectorDecode K (row N i)
    have hq : q ∈ Quaternionic.space := by
      simp [q,Quaternionic.space,sectorDecode,complexAlbertLinear,complexAlbert,complexOct,hiddenAlbert,hiddenOct,row] <;> rfl
    have hz := Quaternionic.vanishes (x:=x) (y:=y) (by simp [x,Quaternionic.space,diagonalAlbert])
      (by simp [y,Quaternionic.space,complexAlbert,complexOct]) hq
    rw [split hx hy q] at hz
    have hd : (row N i).det = 0 := by simp [row,Matrix.det_fin_three]
    simpa only [q,H,m,sectorComplexMatrix_decode K _ (sectorComplexMatrix_isHermitian z),hiddenMatrix_decode,hd,star_zero,map_zero,zero_mul,Complex.zero_re,mul_zero,add_zero] using hz
  have zr : row 0 0 = 0 := by ext i j : 1; simp [row]
  have hp : pureTerm = 0 := by simpa [F,mix,gram,gamma,zr] using test 0 0
  have zero (i) : (F (gram (row M i))).re = 0 := by simpa [hp] using test M i
  have hf : (F (gram M)).re = 0 := by simpa only [grams M,F,mix_add,Complex.add_re] using show (F (gram (row M 0))).re + (F (gram (row M 1))).re + (F (gram (row M 2))).re = 0 by simp [zero]
  have hB : B = argumentMatrix (H x) (H y) := by simp [B,H,sectorComplexMatrix_jordan,hx,productComplex_complex_left,argumentMatrix]
  have hs : S.conjTranspose = -S := by simp [S,adjugateCommutator,(sectorComplexMatrix_isHermitian x).adjugate.eq,(sectorComplexMatrix_isHermitian y).adjugate.eq,neg_sub,H]
  have wt := adjugate_argument_trace a b c d e f u v w
  change (S*argumentMatrix (H x) (H y)).trace = _ at wt
  change phi x y z = _; rw [split hx hy z]; change pureTerm + (F (gram M)).re + 2*(star M.det * (S.conjTranspose*B).trace).re = _
  rw [hp,hf,hs,hB,Matrix.neg_mul,Matrix.trace_neg,wt]; simp [M,m,Complex.mul_re]; ring
end
end Glennie
