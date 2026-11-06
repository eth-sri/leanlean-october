/- Unrestricted native factor.
All intermediate conclusions are proved from named action, matrix and trace bodies;
no missing factor/cancellation field or hypothesis. -/
module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.NormNum
public import Aesop
public import Glennie.Native.SectorAction
public import Glennie.Native.SectorArgumentAction
public import Glennie.Theorems.SectorContraction
public import Glennie.Native.MixedComplexUnits
public import Glennie.SectorFactorWeight
public import Glennie.Native.SectorAssemblyBridges
public import Glennie.Native.SectorMixedTrace

@[expose] public section
namespace Glennie
section

theorem phi_diagonal_complex_factor (a b c d e f : ℝ) (u v w : ℂ) (z : Albert) :
    phi (diagonalAlbert a b c) (complexAlbert d e f u v w) z =
      (2*(a-b)*(b-c)*(c-a)*(u*w*star v).im) * (hiddenMatrix z).det.im := by
  let x := diagonalAlbert a b c
  let y := complexAlbert d e f u v w
  let D := sectorComplexMatrix x
  let H := sectorComplexMatrix y
  let K := sectorComplexMatrix z
  let M := hiddenMatrix z
  let B := sectorComplexMatrix (jordan x y)
  let G := M.conjTranspose*M
  let S := H.adjugate*D.adjugate-D.adjugate*H.adjugate
  let Q := D*H*K*H*D-H*D*K*D*H
  let t := (a-b)*(b-c)*(c-a)*(u*w*star v).im
  have hx : hiddenMatrix x = 0 := hiddenMatrix_complexAlbert ((a,b,c),(0,0,0))
  have hy : hiddenMatrix y = 0 := hiddenMatrix_complexAlbert ((d,e,f),(u,v,w))
  have hb : hiddenMatrix (jordan x y) = 0 := by
    rw [hiddenMatrix_jordan, hx, SectorAction.productHidden_complex_left, hy]
    simp
  have hB : B = (1/2:ℂ) • (D*H+H*D) := by
    dsimp only [B]
    rw [sectorComplexMatrix_jordan, hx, SectorAction.productComplex_complex_left]
  have hS : S.conjTranspose = -S :=
    SectorAssemblyBridges.adjugate_commutator_antiHermitian D H
      (sectorComplexMatrix_isHermitian x) (sectorComplexMatrix_isHermitian y)
  have hK : K.IsHermitian := sectorComplexMatrix_isHermitian z
  have hBH : B.IsHermitian := sectorComplexMatrix_isHermitian (jordan x y)
  have hCommC : sectorComplexMatrix (U x (U y z)-U y (U x z)) = Q :=
    SectorAction.complex_commutator x y z hx hy
  have hCommM : hiddenMatrix (U x (U y z)-U y (U x z)) = M*S :=
    SectorAction.hidden_commutator x y z hx hy
  have hUC : sectorComplexMatrix (U z (jordan x y)) =
      K*B*K+SectorArgumentAction.gamma G B :=
    SectorArgumentAction.complex_U_argument z (jordan x y) hb
  have hUH : hiddenMatrix (U z (jordan x y)) =
      M*((K*B).trace • (1:Matrix (Fin 3) (Fin 3) ℂ)-K*B)+
        sectorAdjointAdjugate M*B :=
    SectorArgumentAction.hidden_U_argument z (jordan x y) hb
  have hPure : (Q*(K*B*K)).trace.re = 0 := by
    rw [hB]
    exact congrArg Complex.re (SectorAssemblyBridges.pure_complex_trace D H K)
  have hMixedMatrix : SectorArgumentAction.gamma Q B = S*B*K-K*B*S := by
    rw [hB]
    simpa only [MixedComplexUnits.diagonalInput_native, MixedComplexUnits.complexCommutator,
      MixedComplexUnits.symmProduct, MixedComplexUnits.adjugateCommutator] using
      MixedComplexUnits.mixed_identity (a:ℂ) (b:ℂ) (c:ℂ) H K
  have hMixed : (Q*SectorArgumentAction.gamma G B).trace.re +
      2*((M*S).conjTranspose*
        (M*((K*B).trace • (1:Matrix (Fin 3) (Fin 3) ℂ)-K*B))).trace.re = 0 := by
    rw [SectorContraction.trace_polar_transfer Q G B, hMixedMatrix]
    exact SectorMixedTrace.mixed_trace_cancel M S K B hS hK hBH
  have hSB : (S*B).trace = (⟨0,-t⟩:ℂ) := by
    rw [hB]
    apply Complex.ext
    all_goals simp [S, D, H, x, y, t, sectorComplexMatrix,
      complexHermitianMatrix, complexCoordinatesLinear, diagonalAlbert,
      complexAlbert, complexOct, complexPart, Matrix.adjugate_fin_three,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_three,
      smul_eq_mul, Complex.mul_re, Complex.mul_im]
    all_goals ring
  have hCubic :
      2*((M*S).conjTranspose*(sectorAdjointAdjugate M*B)).trace.re =
        2*t*M.det.im := by
    rw [SectorContraction.hidden_cubic_real M S B hS, hSB]
    simp [Complex.mul_re]
    ring
  change phi x y z = (2*(a-b)*(b-c)*(c-a)*(u*w*star v).im) * M.det.im
  rw [phi, inner_sector_model, hCommC, hCommM, hUC, hUH]
  simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  simp only [t, Complex.star_def] at hCubic ⊢
  linarith only [hPure, hMixed, hCubic]

end
end Glennie
