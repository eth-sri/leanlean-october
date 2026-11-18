module
public import Glennie.Native.PairReduction
public import Glennie.SectorModel
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Module

@[expose] public section
namespace Glennie
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000
attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike

private abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℂ

private def tracePolar (G B : Mat3) : Mat3 :=
  G * B + B * G - B.trace • G - G.trace • B + (G.trace * B.trace - (G * B).trace) • (1 : Mat3)

private theorem polarAdjugate_eq_conjTranspose (M N : Mat3) :
    sectorPolarAdjugate M N = (tracePolar M N).conjTranspose := by
  have hg : tracePolar M N = (M + N).adjugate - M.adjugate - N.adjugate := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [tracePolar, Matrix.adjugate_fin_three, Matrix.mul_apply, Matrix.trace, Matrix.diag,
        Fin.sum_univ_three, smul_eq_mul] <;> ring
  rw [hg]; simp only [sectorPolarAdjugate, sectorAdjointAdjugate, Matrix.conjTranspose_sub]

private theorem complex_hidden_U_left (y z : Albert) (hy : hiddenMatrix y = 0) :
    sectorComplexMatrix (U y z) = sectorComplexMatrix y * sectorComplexMatrix z * sectorComplexMatrix y ∧
    hiddenMatrix (U y z) = hiddenMatrix z * (sectorComplexMatrix y).adjugate := by
  have hp0 (N : Mat3) : sectorPolarAdjugate 0 N = 0 := by simp [sectorPolarAdjugate, sectorAdjointAdjugate]
  have hs : hiddenMatrix (jordan y y) = 0 := by rw [hiddenMatrix_jordan, hy]; simp [sectorProductHidden, hp0]
  have hc (w : Albert) : sectorComplexMatrix (jordan y w) = (1 / 2 : ℂ) • (sectorComplexMatrix y * sectorComplexMatrix w + sectorComplexMatrix w * sectorComplexMatrix y) := by
    rw [sectorComplexMatrix_jordan, hy]; simp [sectorProductComplex]
  have hh (w : Albert) : hiddenMatrix (jordan y w) = (1 / 2 : ℂ) • (hiddenMatrix w * ((sectorComplexMatrix y).trace • (1 : Mat3) - sectorComplexMatrix y)) := by
    rw [hiddenMatrix_jordan, hy]; simp [sectorProductHidden, hp0]
  have hcs (w : Albert) : sectorComplexMatrix (jordan (jordan y y) w) = (1 / 2 : ℂ) • (sectorComplexMatrix (jordan y y) * sectorComplexMatrix w + sectorComplexMatrix w * sectorComplexMatrix (jordan y y)) := by
    rw [sectorComplexMatrix_jordan, hs]; simp [sectorProductComplex]
  have hhs (w : Albert) : hiddenMatrix (jordan (jordan y y) w) = (1 / 2 : ℂ) • (hiddenMatrix w * ((sectorComplexMatrix (jordan y y)).trace • (1 : Mat3) - sectorComplexMatrix (jordan y y))) := by
    rw [hiddenMatrix_jordan, hs]; simp [sectorProductHidden, hp0]
  constructor
  · change sectorComplexLinear ((2 : ℝ) • jordan y (jordan y z) - jordan (jordan y y) z) = _
    rw [map_sub, map_smul]; change (2 : ℝ) • sectorComplexMatrix (jordan y (jordan y z)) - sectorComplexMatrix (jordan (jordan y y) z) = _
    rw [hc, hc, hcs, hc]
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring
  · change sectorHiddenLinear ((2 : ℝ) • jordan y (jordan y z) - jordan (jordan y y) z) = _
    rw [map_sub, map_smul]; change (2 : ℝ) • hiddenMatrix (jordan y (jordan y z)) - hiddenMatrix (jordan (jordan y y) z) = _
    rw [hh, hh, hhs, hc]
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [Matrix.adjugate_fin_three, Matrix.mul_apply, Matrix.trace, Matrix.diag, Matrix.one_apply,
        Fin.sum_univ_three, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring

private theorem trace_re_coe {X : Mat3} (h : star X.trace = X.trace) : (X.trace.re : ℂ) = X.trace :=
  Complex.ext (by simp) (by have hi := congrArg Complex.im h; simp at hi ⊢; linarith)

private theorem complex_hidden_U_arg (z b : Albert) (hb : hiddenMatrix b = 0) :
    sectorComplexMatrix (U z b) = sectorComplexMatrix z * sectorComplexMatrix b * sectorComplexMatrix z +
      tracePolar ((hiddenMatrix z).conjTranspose * hiddenMatrix z) (sectorComplexMatrix b) ∧
    hiddenMatrix (U z b) = hiddenMatrix z * ((sectorComplexMatrix z * sectorComplexMatrix b).trace • (1 : Mat3) -
      sectorComplexMatrix z * sectorComplexMatrix b) + sectorAdjointAdjugate (hiddenMatrix z) * sectorComplexMatrix b := by
  let K := sectorComplexMatrix z; let M := hiddenMatrix z; let B := sectorComplexMatrix b
  let G := M.conjTranspose * M; let C := B.trace • (1 : Mat3) - B
  have hB : B.IsHermitian := sectorComplexMatrix_isHermitian b
  have hG : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hBtr : star B.trace = B.trace := by rw [← Matrix.trace_conjTranspose, hB.eq]
  have hC : C.conjTranspose = C := by simp [C, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hBtr, hB.eq]
  have hB_ct (i j : Fin 3) : star (B i j) = B j i := congrFun (congrFun hB j) i
  have hG_re : ((M.conjTranspose * M).trace.re : ℂ) = G.trace :=
    trace_re_coe (by rw [← Matrix.trace_conjTranspose, hG.eq])
  have hGC_re : ((M.conjTranspose * ((1 / 2 : ℂ) • (M * C))).trace.re : ℂ) = ((1 / 2 : ℂ) • (G * C)).trace := by
    rw [show M.conjTranspose * ((1 / 2 : ℂ) • (M * C)) = (1 / 2 : ℂ) • (G * C) by simp [G, Matrix.mul_assoc]]
    refine trace_re_coe ?_
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hC, hG.eq,
      Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_mul_comm]; norm_num
  have h2r (X : Mat3) : (2 : ℝ) • X = (2 : ℂ) • X := by ext i j; simp [Complex.real_smul]
  have hp0 (X : Mat3) : sectorPolarAdjugate X 0 = 0 := by simp [sectorPolarAdjugate, sectorAdjointAdjugate]
  have hcr (w : Albert) : sectorComplexMatrix (jordan w b) = (1 / 2 : ℂ) • (sectorComplexMatrix w * B + B * sectorComplexMatrix w) := by
    rw [sectorComplexMatrix_jordan, hb]; simp [sectorProductComplex, B]
  have hhr (w : Albert) : hiddenMatrix (jordan w b) = (1 / 2 : ℂ) • (hiddenMatrix w * C) := by
    rw [hiddenMatrix_jordan, hb]; simp [sectorProductHidden, hp0, C, B]
  constructor
  · change sectorComplexLinear ((2 : ℝ) • jordan z (jordan z b) - jordan (jordan z z) b) = K * B * K + tracePolar G B
    rw [map_sub, map_smul]; change (2 : ℝ) • sectorComplexMatrix (jordan z (jordan z b)) - sectorComplexMatrix (jordan (jordan z z) b) = _
    rw [h2r, sectorComplexMatrix_jordan, hcr, hhr, hcr, sectorComplexMatrix_jordan]
    dsimp only [sectorProductComplex]; change (2 : ℂ) • _ - _ = _; simp only [K, M] at hG_re hGC_re ⊢
    rw [hG_re, hGC_re,
      show ((1 / 2 : ℂ) • (M * C)).conjTranspose * M = (1 / 2 : ℂ) • (C * G) by simp [G, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hC, Matrix.mul_assoc],
      show M.conjTranspose * ((1 / 2 : ℂ) • (M * C)) = (1 / 2 : ℂ) • (G * C) by simp [G, Matrix.mul_assoc]]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [tracePolar, C, G, Matrix.mul_apply, Matrix.trace, Matrix.diag, Matrix.one_apply, Fin.sum_univ_three, smul_eq_mul] <;> ring
  · change sectorHiddenLinear ((2 : ℝ) • jordan z (jordan z b) - jordan (jordan z z) b) = M * ((K * B).trace • (1 : Mat3) - K * B) + sectorAdjointAdjugate M * B
    rw [map_sub, map_smul]; change (2 : ℝ) • hiddenMatrix (jordan z (jordan z b)) - hiddenMatrix (jordan (jordan z z) b) = _
    rw [h2r, hiddenMatrix_jordan, hcr, hhr, hhr, hiddenMatrix_jordan]
    dsimp only [sectorProductHidden]; simp only [K, M]
    rw [polarAdjugate_eq_conjTranspose, polarAdjugate_eq_conjTranspose]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [sectorAdjointAdjugate, tracePolar, C, Matrix.adjugate_fin_three, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag, Matrix.one_apply, Fin.sum_univ_three, smul_eq_mul, hB_ct] <;> ring

private theorem mixed_matrix_identity (a b c : ℂ) (H K : Mat3) :
    let D := Matrix.diagonal ![a, b, c]
    let B := (1 / 2 : ℂ) • (D * H + H * D)
    let S := H.adjugate * D.adjugate - D.adjugate * H.adjugate
    tracePolar (D * H * K * H * D - H * D * K * D * H) B = S * B * K - K * B * S := by
  have hd_adj : (Matrix.diagonal ![a, b, c]).adjugate = Matrix.diagonal ![b * c, a * c, a * b] := by
    rw [Matrix.adjugate_fin_three]; ext i j; fin_cases i <;> fin_cases j <;> simp
  change tracePolar _ _ = _
  ext r s; fin_cases r <;> fin_cases s <;> (
    simp only [tracePolar, hd_adj, Matrix.adjugate_fin_three]
    simp [Matrix.diagonal_apply, Matrix.mul_apply, Matrix.vecMul_apply_eq_sum,
      Matrix.trace, Matrix.diag, Fin.sum_univ_three, smul_eq_mul]; ring)

private theorem phi_diagonal_complex_factor (a b c d e f : ℝ) (u v w : ℂ) (z : Albert) :
    phi (diagonalAlbert a b c) (complexAlbert d e f u v w) z =
      (2 * (a - b) * (b - c) * (c - a) * (u * w * star v).im) * (hiddenMatrix z).det.im := by
  let x := diagonalAlbert a b c; let y := complexAlbert d e f u v w
  let D := sectorComplexMatrix x; let H := sectorComplexMatrix y
  let K := sectorComplexMatrix z; let M := hiddenMatrix z
  let B := sectorComplexMatrix (jordan x y); let G := M.conjTranspose * M
  let S := H.adjugate * D.adjugate - D.adjugate * H.adjugate
  let Q := D * H * K * H * D - H * D * K * D * H
  let t := (a - b) * (b - c) * (c - a) * (u * w * star v).im
  have hc0 : complexOct (0 : ℂ) = 0 := by ext <;> simp [complexOct]
  have hx : hiddenMatrix x = 0 := by simpa [x, complexAlbertLinear, complexAlbert, diagonalAlbert, hc0] using hiddenMatrix_complexAlbert ((a, b, c), (0, 0, 0))
  have hy : hiddenMatrix y = 0 := hiddenMatrix_complexAlbert ((d, e, f), (u, v, w))
  have hb : hiddenMatrix (jordan x y) = 0 := by
    rw [hiddenMatrix_jordan, hx, hy]; simp [sectorProductHidden, sectorPolarAdjugate, sectorAdjointAdjugate]
  have hB : B = (1 / 2 : ℂ) • (D * H + H * D) := by dsimp only [B, D, H]; rw [sectorComplexMatrix_jordan, hx]; simp [sectorProductComplex]
  have hS : S.conjTranspose = -S := by
    dsimp only [S, D, H]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      (sectorComplexMatrix_isHermitian y).adjugate.eq, (sectorComplexMatrix_isHermitian x).adjugate.eq, neg_sub]
  have hCommC : sectorComplexMatrix (U x (U y z) - U y (U x z)) = Q := by
    change sectorComplexLinear _ = _; rw [map_sub]
    change sectorComplexMatrix (U x (U y z)) - sectorComplexMatrix (U y (U x z)) = Q
    rw [(complex_hidden_U_left x _ hx).1, (complex_hidden_U_left y _ hy).1,
      (complex_hidden_U_left y _ hy).1, (complex_hidden_U_left x _ hx).1]
    simp only [Q, D, H, K, Matrix.mul_assoc]
  have hCommM : hiddenMatrix (U x (U y z) - U y (U x z)) = M * S := by
    change sectorHiddenLinear _ = _; rw [map_sub]
    change hiddenMatrix (U x (U y z)) - hiddenMatrix (U y (U x z)) = M * S
    rw [(complex_hidden_U_left x _ hx).2, (complex_hidden_U_left y _ hy).2,
      (complex_hidden_U_left y _ hy).2, (complex_hidden_U_left x _ hx).2]
    simp only [M, S, D, H, Matrix.mul_assoc, mul_sub]
  obtain ⟨hUC, hUH⟩ := complex_hidden_U_arg z (jordan x y) hb
  have hMetric : phi x y z = (Q * (K * B * K)).trace.re + (Q * tracePolar G B).trace.re +
      2 * ((M * S).conjTranspose * (M * ((K * B).trace • (1 : Mat3) - K * B))).trace.re +
      2 * ((M * S).conjTranspose * (sectorAdjointAdjugate M * B)).trace.re := by
    rw [phi, inner_sector_model, hCommC, hCommM, hUC, hUH]
    simp only [K, B, G, M, Matrix.mul_add, Matrix.trace_add, Complex.add_re]; ring
  have hPure : (Q * (K * B * K)).trace = 0 := by
    rw [hB, Matrix.mul_assoc K, show Q * (K * ((1 / 2 : ℂ) • (D * H + H * D) * K)) =
      (1 / 2 : ℂ) • ((D * H * K * (H * D * K) - H * D * K * (D * H * K)) * (D * H * K + H * D * K)) by
        simp only [Q, Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc],
      Matrix.trace_smul]
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add,
      show (D * H * K * (H * D * K) * (D * H * K)).trace = (H * D * K * (D * H * K) * (D * H * K)).trace by
        rw [Matrix.mul_assoc (D * H * K), Matrix.trace_mul_comm (D * H * K)],
      Matrix.trace_mul_cycle (D * H * K) (H * D * K) (H * D * K), smul_eq_mul]; ring
  have hTransfer : (Q * tracePolar G B).trace = (G * tracePolar Q B).trace := by
    simp only [tracePolar, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
      show (Q * (G * B)).trace = (G * (B * Q)).trace by rw [Matrix.trace_mul_cycle' Q G B, Matrix.trace_mul_cycle' B Q G],
      Matrix.trace_mul_cycle' Q B G, Matrix.trace_mul_comm Q G]; ring
  have hD_diag : D = Matrix.diagonal ![(a : ℂ), b, c] := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [D, x, sectorComplexMatrix, complexHermitianMatrix, complexCoordinatesLinear, diagonalAlbert, complexPart]
  have hMixed : (Q * tracePolar G B).trace.re +
      2 * ((M * S).conjTranspose * (M * ((K * B).trace • (1 : Mat3) - K * B))).trace.re = 0 := by
    rw [hTransfer, show tracePolar Q B = S * B * K - K * B * S by dsimp only [Q, S]; rw [hB, hD_diag]; exact mixed_matrix_identity a b c H K]
    have hG : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
    have hK := sectorComplexMatrix_isHermitian z
    have hBH := sectorComplexMatrix_isHermitian (jordan x y)
    have hSG_re : (S * G).trace.re = 0 := by
      have hs : star (S * G).trace = -(S * G).trace := by
        rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hG.eq, hS, Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_mul_comm]
      have hr := congrArg Complex.re hs; simp at hr; linarith
    have hKB_im : (K * B).trace.im = 0 := by
      have hs : star (K * B).trace = (K * B).trace := by
        rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hBH.eq, hK.eq, Matrix.trace_mul_comm]
      have hi := congrArg Complex.im hs; simp at hi; linarith
    have hexp : ((M * S).conjTranspose * (M * ((K * B).trace • (1 : Mat3) - K * B))).trace =
        -((K * B).trace * (S * G).trace) + (S * G * K * B).trace := by
      simp only [G, Matrix.conjTranspose_mul, hS, Matrix.mul_sub, Matrix.neg_mul,
        Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]; ring
    have hfour : star (S * G * K * B).trace = -(G * S * B * K).trace := by
      rw [← Matrix.trace_conjTranspose]; dsimp only [K, B]
      simp only [Matrix.conjTranspose_mul, hBH.eq, hK.eq, hG.eq, hS, Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_assoc]
      simpa only [Matrix.mul_assoc] using congrArg Neg.neg (Matrix.trace_mul_comm (B * K) (G * S))
    have hfour_re : (S * G * K * B).trace.re = -(G * S * B * K).trace.re := by simpa using congrArg Complex.re hfour
    have hcyc : (G * K * B * S).trace = (S * G * K * B).trace := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (G * K) B S
    have hgs : (G * (S * B * K - K * B * S)).trace.re = (G * S * B * K).trace.re - (S * G * K * B).trace.re := by
      rw [Matrix.mul_sub, Matrix.trace_sub]; simp only [Matrix.mul_assoc] at hcyc ⊢; rw [hcyc, Complex.sub_re]
    have hhr : ((M * S).conjTranspose * (M * ((K * B).trace • (1 : Mat3) - K * B))).trace.re = (S * G * K * B).trace.re := by
      rw [hexp]; simp [Complex.mul_re, hSG_re, hKB_im]
    rw [hgs, hhr]; linarith
  have hSB : (S * B).trace = (⟨0, -t⟩ : ℂ) := by
    have hDm : D = complexHermitianMatrix ((a, b, c), (0, 0, 0)) := by
      change complexHermitianMatrix (complexCoordinatesLinear (diagonalAlbert a b c)) = _
      simpa [complexAlbertLinear, complexAlbert, diagonalAlbert, hc0] using
        congrArg complexHermitianMatrix (complexCoordinates_albert ((a, b, c), (0, 0, 0)))
    have hHm : H = complexHermitianMatrix ((d, e, f), (u, v, w)) :=
      congrArg complexHermitianMatrix (complexCoordinates_albert ((d, e, f), (u, v, w)))
    dsimp only [S, t]; rw [hB, hDm, hHm]
    apply Complex.ext <;>
      simp [complexHermitianMatrix, Matrix.adjugate_fin_three, Matrix.trace, Matrix.diag,
        Matrix.mul_apply, Fin.sum_univ_three, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring
  have hCubic : 2 * ((M * S).conjTranspose * (sectorAdjointAdjugate M * B)).trace.re = 2 * t * M.det.im := by
    have hgram : M.conjTranspose * sectorAdjointAdjugate M = star M.det • (1 : Mat3) := by
      rw [show M.conjTranspose * sectorAdjointAdjugate M = (M.adjugate * M).conjTranspose by simp [sectorAdjointAdjugate, Matrix.conjTranspose_mul],
        Matrix.adjugate_mul]; simp
    have htr : ((M * S).conjTranspose * (sectorAdjointAdjugate M * B)).trace = star M.det * (S.conjTranspose * B).trace := by
      rw [show (M * S).conjTranspose * (sectorAdjointAdjugate M * B) = (S.conjTranspose * (M.conjTranspose * sectorAdjointAdjugate M)) * B by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc], hgram]; simp
    rw [htr, hS, Matrix.neg_mul, Matrix.trace_neg, hSB]; simp [Complex.mul_re]; ring
  rw [hMetric, show (Q * (K * B * K)).trace.re = 0 by rw [hPure]; rfl]
  linarith [hMixed, hCubic, show 2 * t * M.det.im = (2 * (a - b) * (b - c) * (c - a) * (u * w * star v).im) * M.det.im by dsimp [t]; ring]

theorem diagonalAlbert_eq (x : Albert) (hx : IsDiagonal x) :
    diagonalAlbert x.d0 x.d1 x.d2 = x := by
  apply Albert.ext <;> simp [diagonalAlbert, hx.1, hx.2.1, hx.2.2]

theorem complexAlbert_eq (x : Albert) (hx : InComplexSector x) :
    complexAlbert x.d0 x.d1 x.d2 (complexPart x.o01) (complexPart x.o02) (complexPart x.o12) = x :=
  complexProjection_eq_self x hx

theorem phi_of_diagonal_complex (x y z : Albert) (hx : IsDiagonal x) (hy : InComplexSector y) :
    phi x y z = (2 * (x.d0 - x.d1) * (x.d1 - x.d2) * (x.d2 - x.d0) *
      (complexPart y.o01 * complexPart y.o12 * star (complexPart y.o02)).im) *
      (hiddenMatrix z).det.im := by
  conv_lhs => rw [← diagonalAlbert_eq x hx, ← complexAlbert_eq y hy]
  exact phi_diagonal_complex_factor _ _ _ _ _ _ _ _ _ _

def hiddenMatrixLinear : Albert →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ := sectorHiddenLinear

theorem hiddenMatrix_eq_zero (x : Albert) (hx : InComplexSector x) : hiddenMatrix x = 0 := by
  rw [← show complexAlbertLinear (complexCoordinatesLinear x) = x from complexProjection_eq_self x hx]
  exact hiddenMatrix_complexAlbert _

theorem diagonal_inComplex (x : Albert) (hx : IsDiagonal x) : InComplexSector x := by
  rw [← diagonalAlbert_eq x hx]; simp [InComplexSector, OctInComplex, diagonalAlbert]

end
end Glennie

namespace Glennie.NativeGenerationEndpointR01
noncomputable section
open Glennie
open scoped BigOperators

private def E01 : Octonion →ₗ[ℝ] Albert :=
  { toFun q := ⟨0, 0, 0, q, 0, 0⟩, map_add' _ _ := by ext <;> simp, map_smul' _ _ := by ext <;> simp }
private def E02 : Octonion →ₗ[ℝ] Albert :=
  { toFun q := ⟨0, 0, 0, 0, q, 0⟩, map_add' _ _ := by ext <;> simp, map_smul' _ _ := by ext <;> simp }
private def E12 : Octonion →ₗ[ℝ] Albert :=
  { toFun q := ⟨0, 0, 0, 0, 0, q⟩, map_add' _ _ := by ext <;> simp, map_smul' _ _ := by ext <;> simp }

@[simp] private theorem octNormSq_zero' : octNormSq 0 = 0 := by norm_num [octNormSq, Quaternion.normSq_def']

private theorem cross01_12 (q r : Octonion) : (2 : ℝ) • jordan (E01 q) (E12 r) = E02 (octMul q r) := by
  ext <;> simp [E01, E02, E12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj] <;> ring

private theorem cross01_02 (q r : Octonion) : (2 : ℝ) • jordan (E01 q) (E02 r) = E12 (octMul (octConj q) r) := by
  ext <;> simp [E01, E02, E12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj] <;> ring

private theorem cross02_12 (q r : Octonion) : (2 : ℝ) • jordan (E02 q) (E12 r) = E01 (octMul q (octConj r)) := by
  ext <;> simp [E01, E02, E12, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj] <;> ring

private theorem complexOct_mul (u v : ℂ) : octMul (complexOct u) (complexOct v) = complexOct (u * v) := by
  ext <;> simp [complexOct, octMul, Complex.mul_re, Complex.mul_im] <;> ring

private theorem complexOct_conj (u : ℂ) : octConj (complexOct u) = complexOct (star u) := by
  ext <;> simp [complexOct, octConj, Complex.star_def]

private theorem complexOct_one : complexOct 1 = octScalar 1 := by ext <;> simp [complexOct, octScalar]
private theorem complexOct_zero : complexOct 0 = 0 := by ext <;> simp [complexOct]

private theorem peirce_extract (z : Albert) :
    (4 : ℝ) • jordan (diagonalAlbert 1 0 0) (jordan (diagonalAlbert 0 1 0) z) = E01 z.o01 ∧
    (4 : ℝ) • jordan (diagonalAlbert 1 0 0) (jordan (diagonalAlbert 0 0 1) z) = E02 z.o02 ∧
    (4 : ℝ) • jordan (diagonalAlbert 0 1 0) (jordan (diagonalAlbert 0 0 1) z) = E12 z.o12 := by
  refine ⟨?_, ?_, ?_⟩ <;> (
    apply Albert.ext <;> norm_num [E01, E02, E12, diagonalAlbert,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot, octRe, octMul, octConj, smul_smul]
    all_goals ext <;> norm_num)

private theorem complex_line_mem {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : Submodule ℝ V) (T : ℂ →ₗ[ℝ] V) (u v : ℂ)
    (hu : T u ∈ K) (hv : T v ∈ K) (hd : u.re * v.im - u.im * v.re ≠ 0) (z : ℂ) : T z ∈ K := by
  have he := congrArg T (show (u.re * v.im - u.im * v.re) • z =
      (z.re * v.im - z.im * v.re) • u + (u.re * z.im - u.im * z.re) • v by
    apply Complex.ext <;> simp <;> ring)
  simp only [map_smul, map_add] at he
  have hm : (u.re * v.im - u.im * v.re) • T z ∈ K := by rw [he]; exact K.add_mem (K.smul_mem _ hu) (K.smul_mem _ hv)
  simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul] using K.smul_mem (u.re * v.im - u.im * v.re)⁻¹ hm

private theorem complexSector_le_of_regular_triangle
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (a b c d e f : ℝ) (u v w : ℂ)
    (hx : diagonalAlbert a b c ∈ K) (hy : complexAlbert d e f u v w ∈ K)
    (hab : a - b ≠ 0) (hbc : b - c ≠ 0) (hca : c - a ≠ 0)
    (htriangle : (u * w * star v).im ≠ 0) : complexSector ≤ K := by
  have hlag (s t : ℝ) : diagonalAlbert ((a - s) * (a - t)) ((b - s) * (b - t)) ((c - s) * (c - t)) ∈ K := by
    rw [← show jordan (diagonalAlbert a b c) (diagonalAlbert a b c) - (s + t) • diagonalAlbert a b c + (s * t) • (1 : Albert) =
      diagonalAlbert ((a - s) * (a - t)) ((b - s) * (b - t)) ((c - s) * (c - t)) by
        ext <;> simp [diagonalAlbert, unit, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
          octDot, octRe, octMul, octConj] <;> ring]
    exact K.add_mem (K.sub_mem (hJ _ hx _ hx) (K.smul_mem _ hx)) (K.smul_mem _ h1)
  have hsm {r : ℝ} (hr : r ≠ 0) {p : Albert} (hp : r • p ∈ K) : p ∈ K := by
    simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using K.smul_mem r⁻¹ hp
  have he0 : diagonalAlbert 1 0 0 ∈ K := hsm (mul_ne_zero hab (sub_ne_zero.mpr (sub_ne_zero.mp hca).symm))
    (by convert hlag b c using 1; ext <;> simp [diagonalAlbert])
  have he1 : diagonalAlbert 0 1 0 ∈ K := hsm (mul_ne_zero (sub_ne_zero.mpr (sub_ne_zero.mp hab).symm) hbc)
    (by convert hlag a c using 1; ext <;> simp [diagonalAlbert])
  have he2 : diagonalAlbert 0 0 1 ∈ K := hsm (mul_ne_zero hca (sub_ne_zero.mpr (sub_ne_zero.mp hbc).symm))
    (by convert hlag a b using 1; ext <;> simp [diagonalAlbert])
  let cL : ℂ →ₗ[ℝ] Octonion :=
    { toFun := complexOct, map_add' _ _ := by ext <;> simp [complexOct], map_smul' _ _ := by ext <;> simp [complexOct, smul_eq_mul] }
  let S01 := E01.comp cL; let S02 := E02.comp cL; let S12 := E12.comp cL
  obtain ⟨hp01, hp02, hp12⟩ := peirce_extract (complexAlbert d e f u v w)
  have hu : S01 u ∈ K := by change E01 (complexOct u) ∈ K; rw [show complexOct u = (complexAlbert d e f u v w).o01 from rfl, ← hp01]; exact K.smul_mem 4 (hJ _ he0 _ (hJ _ he1 _ hy))
  have hv : S02 v ∈ K := by change E02 (complexOct v) ∈ K; rw [show complexOct v = (complexAlbert d e f u v w).o02 from rfl, ← hp02]; exact K.smul_mem 4 (hJ _ he0 _ (hJ _ he2 _ hy))
  have hw : S12 w ∈ K := by change E12 (complexOct w) ∈ K; rw [show complexOct w = (complexAlbert d e f u v w).o12 from rfl, ← hp12]; exact K.smul_mem 4 (hJ _ he1 _ (hJ _ he2 _ hy))
  have huv : S12 (star u * v) ∈ K := by change E12 (complexOct _) ∈ K; rw [← complexOct_mul, ← complexOct_conj, ← cross01_02]; exact K.smul_mem 2 (hJ _ hu _ hv)
  have huw : S02 (u * w) ∈ K := by change E02 (complexOct _) ∈ K; rw [← complexOct_mul, ← cross01_12]; exact K.smul_mem 2 (hJ _ hu _ hw)
  have hvw : S01 (v * star w) ∈ K := by change E01 (complexOct _) ∈ K; rw [← complexOct_mul, ← complexOct_conj, ← cross02_12]; exact K.smul_mem 2 (hJ _ hv _ hw)
  have h01 := complex_line_mem K S01 u (v * star w) hu hvw
    (by rw [show u.re * (v * star w).im - u.im * (v * star w).re = -(u * w * star v).im by simp [Complex.mul_re, Complex.mul_im]; ring]; exact neg_ne_zero.mpr htriangle)
  have h12 := complex_line_mem K S12 w (star u * v) hw huv
    (by rw [show w.re * (star u * v).im - w.im * (star u * v).re = -(u * w * star v).im by simp [Complex.mul_re, Complex.mul_im]; ring]; exact neg_ne_zero.mpr htriangle)
  have h02 := complex_line_mem K S02 v (u * w) hv huw
    (by rw [show v.re * (u * w).im - v.im * (u * w).re = (u * w * star v).im by simp [Complex.mul_re, Complex.mul_im]; ring]; exact htriangle)
  rintro _ ⟨q, rfl⟩
  rw [show complexAlbertLinear q = q.1.1 • diagonalAlbert 1 0 0 + q.1.2.1 • diagonalAlbert 0 1 0 +
      q.1.2.2 • diagonalAlbert 0 0 1 + S01 q.2.1 + S02 q.2.2.1 + S12 q.2.2.2 by
    ext <;> simp [complexAlbertLinear, complexAlbert, diagonalAlbert, S01, S02, S12, E01, E02, E12, cL]]
  exact K.add_mem (K.add_mem (K.add_mem (K.add_mem (K.add_mem
    (K.smul_mem _ he0) (K.smul_mem _ he1)) (K.smul_mem _ he2)) (h01 _)) (h02 _)) (h12 _)

theorem eq_top_of_phi_ne_zero
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hphi : phi x y z ≠ 0) : K = ⊤ := by
  obtain ⟨g, hxd, hyc⟩ := universal_pair_reduction x y
  let L : Submodule ℝ Albert := K.map g.equiv.toLinearMap
  have hLJ : ∀ p ∈ L, ∀ q ∈ L, jordan p q ∈ L := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩; exact ⟨jordan p q, hJ p hp q hq, g.map_jordan p q⟩
  set x' := g.equiv x; set y' := g.equiv y; set z' := g.equiv z
  have hz' : z' ∈ L := ⟨z, hz, rfl⟩
  have hphi' : phi x' y' z' ≠ 0 := g.phi_map x y z ▸ hphi
  have hF := phi_of_diagonal_complex x' y' z' hxd hyc
  have hC : complexSector ≤ L := complexSector_le_of_regular_triangle L ⟨1, h1, g.map_unit⟩ hLJ
    x'.d0 x'.d1 x'.d2 y'.d0 y'.d1 y'.d2
    (complexPart y'.o01) (complexPart y'.o02) (complexPart y'.o12)
    (by rw [diagonalAlbert_eq x' hxd]; exact ⟨x, hx, rfl⟩)
    (by rw [complexAlbert_eq y' hyc]; exact ⟨y, hy, rfl⟩)
    (fun h => hphi' (by rw [hF, h]; ring)) (fun h => hphi' (by rw [hF, h]; ring))
    (fun h => hphi' (by rw [hF, h]; ring)) (fun h => hphi' (by rw [hF, h]; ring))
  have hd : (hiddenMatrix z').det ≠ 0 := fun h => hphi' (by rw [hF, h]; simp)
  have hcA (a b c : ℝ) (u v w : ℂ) : complexAlbert a b c u v w ∈ L := hC ⟨((a, b, c), (u, v, w)), rfl⟩
  have he0 := hcA 1 0 0 0 0 0; have he1 := hcA 0 1 0 0 0 0; have he2 := hcA 0 0 1 0 0 0
  have hc01 (u : ℂ) : E01 (complexOct u) ∈ L := by simpa [E01, complexAlbert, complexOct_zero] using hcA 0 0 0 u 0 0
  have hc02 (u : ℂ) : E02 (complexOct u) ∈ L := by simpa [E02, complexAlbert, complexOct_zero] using hcA 0 0 0 0 u 0
  have hc12 (u : ℂ) : E12 (complexOct u) ∈ L := by simpa [E12, complexAlbert, complexOct_zero] using hcA 0 0 0 0 0 u
  obtain ⟨hp01, hp02, hp12⟩ := peirce_extract z'
  have hz01 : E01 z'.o01 ∈ L := by rw [← hp01]; exact L.smul_mem 4 (hLJ _ he0 _ (hLJ _ he1 _ hz'))
  have hz02 : E02 z'.o02 ∈ L := by rw [← hp02]; exact L.smul_mem 4 (hLJ _ he0 _ (hLJ _ he2 _ hz'))
  have hz12 : E12 z'.o12 ∈ L := by rw [← hp12]; exact L.smul_mem 4 (hLJ _ he1 _ (hLJ _ he2 _ hz'))
  let res (q : Octonion) : Octonion := q - complexOct (complexPart q)
  have he01_1 : E01 (octScalar 1) ∈ L := by simpa only [complexOct_one] using hc01 1
  have he12_1 : E12 (octScalar 1) ∈ L := by simpa only [complexOct_one] using hc12 1
  have hw (j : Fin 3) : E02 (hiddenOct (fun i => hiddenMatrix z' i j)) ∈ L := by
    fin_cases j <;> dsimp
    · rw [show hiddenOct (fun i => hiddenMatrix z' i 0) = -res z'.o12 by ext <;> simp [hiddenOct, hiddenMatrix, hiddenColumn, res, complexOct, complexPart], map_neg]
      have he := cross01_12 (octScalar 1) (res z'.o12); simp only [octMul_scalar_left, one_smul] at he
      rw [← he]; exact L.neg_mem (L.smul_mem 2 (hLJ _ he01_1 _ (by dsimp [res]; rw [map_sub]; exact L.sub_mem hz12 (hc12 _))))
    · rw [show hiddenOct (fun i => hiddenMatrix z' i 1) = res z'.o02 by ext <;> simp [hiddenOct, hiddenMatrix, hiddenColumn, res, complexOct, complexPart]]
      dsimp [res]; rw [map_sub]; exact L.sub_mem hz02 (hc02 _)
    · rw [show hiddenOct (fun i => hiddenMatrix z' i 2) = -res z'.o01 by ext <;> simp [hiddenOct, hiddenMatrix, hiddenColumn, res, complexOct, complexPart], map_neg]
      have he := cross01_12 (res z'.o01) (octScalar 1); simp only [octMul_scalar_right, one_smul] at he
      rw [← he]; exact L.neg_mem (L.smul_mem 2 (hLJ _ (by dsimp [res]; rw [map_sub]; exact L.sub_mem hz01 (hc01 _)) _ he12_1))
  have hi (j : Fin 3) : E02 (octMul (complexOct Complex.I) (hiddenOct (fun i => hiddenMatrix z' i j))) ∈ L := by
    rw [← show (4 : ℝ) • jordan (E01 (complexOct Complex.I)) (jordan (E01 (octScalar 1)) (E02 (hiddenOct fun i => hiddenMatrix z' i j))) =
      E02 (octMul (complexOct Complex.I) (hiddenOct fun i => hiddenMatrix z' i j)) by
        ext <;> simp [E01, E02, complexOct, octScalar, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
          octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, smul_eq_mul] <;> ring]
    exact L.smul_mem 4 (hLJ _ (hc01 Complex.I) _ (hLJ _ he01_1 _ (hw j)))
  have hall02 (q : Octonion) : E02 q ∈ L := by
    rw [← oct_complex_hidden_decomposition q, map_add]; refine L.add_mem (hc02 _) ?_
    set M := hiddenMatrix z'; let c := M⁻¹.mulVec (hiddenColumn q)
    have hc : M.mulVec c = hiddenColumn q := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hd), Matrix.one_mulVec]
    rw [← hc, show hiddenOct (M.mulVec c) = ∑ j : Fin 3,
      ((c j).re • hiddenOct (fun i => M i j) + (c j).im • octMul (complexOct Complex.I) (hiddenOct (fun i => M i j))) by
        ext <;> simp [hiddenOct, Matrix.mulVec, dotProduct, Fin.sum_univ_three, complexOct, octMul,
          Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring, map_sum]
    exact L.sum_mem fun j _ => by rw [map_add, map_smul, map_smul]; exact L.add_mem (L.smul_mem _ (hw j)) (L.smul_mem _ (hi j))
  have hall01 (q : Octonion) : E01 q ∈ L := by
    have he := cross02_12 q (octScalar 1); simp only [octConj_scalar, octMul_scalar_right, one_smul] at he
    rw [← he]; exact L.smul_mem 2 (hLJ _ (hall02 q) _ he12_1)
  have hall12 (q : Octonion) : E12 q ∈ L := by
    have he := cross01_02 (octScalar 1) q; simp only [octConj_scalar, octMul_scalar_left, one_smul] at he
    rw [← he]; exact L.smul_mem 2 (hLJ _ he01_1 _ (hall02 q))
  apply top_unique; intro t _
  have hgt : g.equiv t ∈ L := by
    rw [show g.equiv t = (g.equiv t).d0 • diagonalAlbert 1 0 0 + (g.equiv t).d1 • diagonalAlbert 0 1 0 +
      (g.equiv t).d2 • diagonalAlbert 0 0 1 + E01 (g.equiv t).o01 + E02 (g.equiv t).o02 + E12 (g.equiv t).o12 by
        ext <;> simp [diagonalAlbert, E01, E02, E12]]
    exact L.add_mem (L.add_mem (L.add_mem (L.add_mem (L.add_mem
      (L.smul_mem _ he0) (L.smul_mem _ he1)) (L.smul_mem _ he2)) (hall01 _)) (hall02 _)) (hall12 _)
  obtain ⟨s, hs, hse⟩ := hgt
  exact g.equiv.injective hse ▸ hs

end
end Glennie.NativeGenerationEndpointR01
