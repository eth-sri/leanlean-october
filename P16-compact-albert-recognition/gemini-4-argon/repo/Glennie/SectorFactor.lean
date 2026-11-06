module
public import Glennie.SectorModel
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Module

@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

private abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

private def gamma (G B : Mat) : Mat :=
  G*B+B*G-B.trace • G-G.trace • B+(G.trace*B.trace-(G*B).trace) • (1:Mat)

private theorem polarAdjugate_eq_gamma_conjTranspose (M N : Mat) :
    sectorPolarAdjugate M N = (gamma M N).conjTranspose := by
  have h : gamma M N = (M+N).adjugate-M.adjugate-N.adjugate := by
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp [gamma, Matrix.adjugate_fin_three, Matrix.mul_apply, Matrix.trace,
        Matrix.diag, Matrix.one_apply, Fin.sum_univ_three, smul_eq_mul]; ring)
  rw [h]; simp only [sectorPolarAdjugate, sectorAdjointAdjugate, Matrix.conjTranspose_sub]

private theorem polarAdjugate_zero_left (N : Mat) : sectorPolarAdjugate 0 N = 0 := by
  simp [sectorPolarAdjugate, sectorAdjointAdjugate, Matrix.adjugate_zero]

private theorem polarAdjugate_zero_right (M : Mat) : sectorPolarAdjugate M 0 = 0 := by
  simp [sectorPolarAdjugate, sectorAdjointAdjugate, Matrix.adjugate_zero]

private theorem productComplex_complex_left (H K M : Mat) :
    sectorProductComplex H 0 K M = (1/2:ℂ) • (H*K+K*H) := by
  simp [sectorProductComplex]

private theorem productHidden_complex_left (H K M : Mat) :
    sectorProductHidden H 0 K M = (1/2:ℂ) • (M*(H.trace • (1:Mat)-H)) := by
  simp [sectorProductHidden, polarAdjugate_zero_left]

private theorem productComplex_complex_right (K M B : Mat) :
    sectorProductComplex K M B 0 = (1/2:ℂ) • (K*B+B*K) := by
  simp [sectorProductComplex]

private theorem productHidden_complex_right (K M B : Mat) :
    sectorProductHidden K M B 0 = (1/2:ℂ) • (M*(B.trace • (1:Mat)-B)) := by
  simp [sectorProductHidden, polarAdjugate_zero_right]

private theorem complex_U (y z : Albert) (hy : hiddenMatrix y = 0) :
    sectorComplexMatrix (U y z) =
      sectorComplexMatrix y * sectorComplexMatrix z * sectorComplexMatrix y := by
  have hs : hiddenMatrix (jordan y y) = 0 := by
    rw [hiddenMatrix_jordan, hy, productHidden_complex_left]; simp
  change sectorComplexLinear ((2:ℝ) • jordan y (jordan y z) - jordan (jordan y y) z) = _
  rw [map_sub, map_smul]
  change (2:ℝ) • sectorComplexMatrix (jordan y (jordan y z)) -
    sectorComplexMatrix (jordan (jordan y y) z) = _
  simp only [hs, sectorComplexMatrix_jordan, hy, productComplex_complex_left]
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_three, Complex.real_smul, smul_eq_mul]; ring)

private theorem hidden_U (y z : Albert) (hy : hiddenMatrix y = 0) :
    hiddenMatrix (U y z) = hiddenMatrix z * (sectorComplexMatrix y).adjugate := by
  have hs : hiddenMatrix (jordan y y) = 0 := by
    rw [hiddenMatrix_jordan, hy, productHidden_complex_left]; simp
  change sectorHiddenLinear ((2:ℝ) • jordan y (jordan y z) - jordan (jordan y y) z) = _
  rw [map_sub, map_smul]
  change (2:ℝ) • hiddenMatrix (jordan y (jordan y z)) -
    hiddenMatrix (jordan (jordan y y) z) = _
  simp only [hs, hiddenMatrix_jordan, sectorComplexMatrix_jordan, hy,
    productHidden_complex_left, productComplex_complex_left]
  ext i j; fin_cases i <;> fin_cases j <;>
    (simp [Matrix.adjugate_fin_three, Matrix.mul_apply, Matrix.trace, Matrix.diag,
      Matrix.one_apply, Fin.sum_univ_three, Complex.real_smul, smul_eq_mul]; ring)

private theorem hermitian_mul_trace_im_zero {A B : Mat}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A * B).trace.im = 0 := by
  have hs : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hB.eq, hA.eq,
      Matrix.trace_mul_comm B A]
  have hi := congrArg Complex.im hs; simp at hi; linarith

private theorem hermitian_mul_trace_coe_re {A B : Mat}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : ((A * B).trace.re : ℂ) = (A * B).trace :=
  Complex.ext rfl (by simp [hermitian_mul_trace_im_zero hA hB])

private theorem hermitian_trace_coe_re {A : Mat} (hA : A.IsHermitian) :
    (A.trace.re : ℂ) = A.trace := by
  simpa using hermitian_mul_trace_coe_re hA Matrix.isHermitian_one

private theorem complex_U_argument (z b : Albert) (hb : hiddenMatrix b = 0) :
    sectorComplexMatrix (U z b) =
      sectorComplexMatrix z * sectorComplexMatrix b * sectorComplexMatrix z +
        gamma ((hiddenMatrix z).conjTranspose * hiddenMatrix z) (sectorComplexMatrix b) := by
  let K := sectorComplexMatrix z
  let M := hiddenMatrix z
  let B := sectorComplexMatrix b
  let G := M.conjTranspose * M
  have hB : B.IsHermitian := sectorComplexMatrix_isHermitian b
  have hG : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hBtr : star B.trace = B.trace := by rw [← Matrix.trace_conjTranspose, hB.eq]
  have h1 : sectorComplexMatrix (jordan z b) = (1/2:ℂ) • (K*B+B*K) := by
    rw [sectorComplexMatrix_jordan, hb, productComplex_complex_right]
  have h2 : hiddenMatrix (jordan z b) = (1/2:ℂ) • (M*(B.trace • (1:Mat)-B)) := by
    rw [hiddenMatrix_jordan, hb, productHidden_complex_right]
  have h3 : sectorComplexMatrix (jordan (jordan z z) b) =
      (1/2:ℂ) • (sectorComplexMatrix (jordan z z) * B + B * sectorComplexMatrix (jordan z z)) := by
    rw [sectorComplexMatrix_jordan, hb, productComplex_complex_right]
  have hM1 : M.conjTranspose * ((1/2:ℂ) • (M*(B.trace • (1:Mat)-B))) =
      (1/2:ℂ) • (B.trace • G - G*B) := by
    simp only [G, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  have hM2 : ((1/2:ℂ) • (M*(B.trace • (1:Mat)-B))).conjTranspose * M =
      (1/2:ℂ) • (B.trace • G - B*G) := by
    simp only [G, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hB.eq, hBtr,
      star_div₀, star_one, star_ofNat, Matrix.smul_mul, Matrix.sub_mul,
      Matrix.one_mul, Matrix.mul_assoc]
  have htr1 : (((1/2:ℂ) • (B.trace • G - G*B)).trace.re : ℂ) =
      (1/2:ℂ) * (G.trace * B.trace - (G*B).trace) := by
    have h := congrArg (fun c : ℂ => (c.re : ℂ))
      (show ((1/2:ℂ) • (B.trace • G - G*B)).trace =
        (1/2:ℂ) * (B.trace * G.trace - (G*B).trace) by
        simp [Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul])
    rw [h]
    have hre : (((1/2:ℂ) * (B.trace * G.trace - (G*B).trace)).re : ℂ) =
        (1/2:ℂ) * ((B.trace.re : ℂ) * (G.trace.re : ℂ) - ((G*B).trace.re : ℂ)) := by
      have hBi : B.trace.im = 0 := by simpa using hermitian_mul_trace_im_zero hB Matrix.isHermitian_one
      have hGi : G.trace.im = 0 := by simpa using hermitian_mul_trace_im_zero hG Matrix.isHermitian_one
      have hGBi : (G*B).trace.im = 0 := hermitian_mul_trace_im_zero hG hB
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hBi, hGi, hGBi] <;> ring
    rw [hre, hermitian_trace_coe_re hB, hermitian_trace_coe_re hG, hermitian_mul_trace_coe_re hG hB]
    ring
  change sectorComplexLinear ((2:ℝ) • jordan z (jordan z b) - jordan (jordan z z) b) =
    K*B*K + gamma G B
  rw [map_sub, map_smul]
  change (2:ℝ) • sectorComplexMatrix (jordan z (jordan z b)) -
    sectorComplexMatrix (jordan (jordan z z) b) = K*B*K + gamma G B
  rw [h3, sectorComplexMatrix_jordan z (jordan z b), h1, h2, sectorComplexMatrix_jordan z z]
  dsimp only [sectorProductComplex, gamma]
  change (2:ℝ) • ((1/2:ℂ) • (K * ((1/2:ℂ) • (K*B+B*K)) + ((1/2:ℂ) • (K*B+B*K)) * K -
      M.conjTranspose * ((1/2:ℂ) • (M*(B.trace • (1:Mat)-B))) -
      ((1/2:ℂ) • (M*(B.trace • (1:Mat)-B))).conjTranspose * M) +
      ((M.conjTranspose * ((1/2:ℂ) • (M*(B.trace • (1:Mat)-B)))).trace.re : ℂ) • (1:Mat)) -
    (1/2:ℂ) • (((1/2:ℂ) • (K*K+K*K-G-G) + (G.trace.re : ℂ) • (1:Mat)) * B +
      B * ((1/2:ℂ) • (K*K+K*K-G-G) + (G.trace.re : ℂ) • (1:Mat))) = _
  rw [hM1, hM2, htr1, hermitian_trace_coe_re hG]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc, Complex.real_smul, Complex.ofReal_ofNat, smul_eq_mul]
  ring

private theorem hidden_U_argument (z b : Albert) (hb : hiddenMatrix b = 0) :
    hiddenMatrix (U z b) =
      hiddenMatrix z *
        ((sectorComplexMatrix z * sectorComplexMatrix b).trace • (1:Mat) -
          sectorComplexMatrix z * sectorComplexMatrix b) +
      sectorAdjointAdjugate (hiddenMatrix z) * sectorComplexMatrix b := by
  let K := sectorComplexMatrix z
  let M := hiddenMatrix z
  let B := sectorComplexMatrix b
  have hB : B.IsHermitian := sectorComplexMatrix_isHermitian b
  have hBtr : star B.trace = B.trace := by rw [← Matrix.trace_conjTranspose, hB.eq]
  have h1 : sectorComplexMatrix (jordan z b) = (1/2:ℂ) • (K*B+B*K) := by
    rw [sectorComplexMatrix_jordan, hb, productComplex_complex_right]
  have h2 : hiddenMatrix (jordan z b) = (1/2:ℂ) • (M*(B.trace • (1:Mat)-B)) := by
    rw [hiddenMatrix_jordan, hb, productHidden_complex_right]
  have h3 : hiddenMatrix (jordan (jordan z z) b) =
      (1/2:ℂ) • (hiddenMatrix (jordan z z) * (B.trace • (1:Mat)-B)) := by
    rw [hiddenMatrix_jordan, hb, productHidden_complex_right]
  have h4 : hiddenMatrix (jordan z z) =
      M * (K.trace • (1:Mat) - K) + (1/2:ℂ) • sectorPolarAdjugate M M := by
    rw [hiddenMatrix_jordan]
    dsimp only [sectorProductHidden]
    ext i j; simp [smul_eq_mul]; ring
  have hKpart :
      M * (((1/2:ℂ) • (K*B+B*K)).trace • (1:Mat) - (1/2:ℂ) • (K*B+B*K)) +
        ((1/2:ℂ) • (M*(B.trace • (1:Mat)-B))) * (K.trace • (1:Mat)-K) -
        (1/2:ℂ) • (M * (K.trace • (1:Mat)-K) * (B.trace • (1:Mat)-B)) =
      M * ((K*B).trace • (1:Mat) - K*B) := by
    have htr : ((1/2:ℂ) • (K*B+B*K)).trace = (K*B).trace := by
      rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_mul_comm B K, smul_eq_mul]; ring
    rw [htr]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc, smul_eq_mul]
    ring
  have hMpart :
      sectorPolarAdjugate M ((1/2:ℂ) • (M*(B.trace • (1:Mat)-B))) -
        (1/4:ℂ) • (sectorPolarAdjugate M M * (B.trace • (1:Mat)-B)) =
      sectorAdjointAdjugate M * B := by
    apply Matrix.conjTranspose_inj.mp
    rw [polarAdjugate_eq_gamma_conjTranspose, polarAdjugate_eq_gamma_conjTranspose]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_one,
      Matrix.conjTranspose_conjTranspose, sectorAdjointAdjugate,
      hB.eq, hBtr, star_div₀, star_one, star_ofNat]
    ext i j; fin_cases i <;> fin_cases j <;>
      (simp [gamma, Matrix.adjugate_fin_three, Matrix.mul_apply,
        Matrix.trace, Matrix.diag, Matrix.one_apply, Fin.sum_univ_three, smul_eq_mul]; ring)
  change sectorHiddenLinear ((2:ℝ) • jordan z (jordan z b) - jordan (jordan z z) b) =
    M * ((K*B).trace • (1:Mat) - K*B) + sectorAdjointAdjugate M * B
  rw [map_sub, map_smul]
  change (2:ℝ) • hiddenMatrix (jordan z (jordan z b)) -
    hiddenMatrix (jordan (jordan z z) b) = _
  rw [h3, hiddenMatrix_jordan z (jordan z b), h1, h2, h4]
  dsimp only [sectorProductHidden]
  rw [← hMpart, ← hKpart]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.add_mul, Matrix.smul_mul, Complex.real_smul, Complex.ofReal_ofNat, smul_eq_mul]
  ring

private theorem trace_polar_transfer (C G B : Mat) :
    (C*gamma G B).trace = (G*gamma C B).trace := by
  have h1 : (C*(G*B)).trace = (G*(B*C)).trace := by
    rw [Matrix.trace_mul_cycle' C G B, Matrix.trace_mul_cycle' B C G]
  have h2 : (C*(B*G)).trace = (G*(C*B)).trace := Matrix.trace_mul_cycle' C B G
  have h3 : (C*G).trace = (G*C).trace := Matrix.trace_mul_comm C G
  simp only [gamma, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_assoc, h1, h2, h3]
  ring

private theorem mixed_identity (a b c : ℂ) (H K : Mat) :
    let D := Matrix.diagonal ![a,b,c]
    let B := (1/2:ℂ) • (D*H+H*D)
    let S := H.adjugate*D.adjugate-D.adjugate*H.adjugate
    gamma (D*H*K*H*D-H*D*K*D*H) B = S*B*K - K*B*S := by
  have hDa : (Matrix.diagonal ![a,b,c]).adjugate = Matrix.diagonal ![b*c,a*c,a*b] := by
    rw [Matrix.adjugate_fin_three]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  dsimp only
  rw [hDa]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [gamma, Matrix.adjugate_fin_three, Matrix.diagonal_apply, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Matrix.trace, Matrix.diag, Fin.sum_univ_three, smul_eq_mul]; ring)

private theorem mixed_trace_cancel (M S K B : Mat)
    (hS : S.conjTranspose = -S) (hK : K.IsHermitian) (hB : B.IsHermitian) :
    ((M.conjTranspose*M)*(S*B*K-K*B*S)).trace.re +
      2*((M*S).conjTranspose * (M*((K*B).trace • (1:Mat)-K*B))).trace.re = 0 := by
  let G : Mat := M.conjTranspose*M
  have hG : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hsg : (S*G).trace.re = 0 := by
    have hs : star (S*G).trace = -(S*G).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hG.eq, hS,
        Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_mul_comm G S]
    have hr := congrArg Complex.re hs; simp at hr; linarith
  have ht : (K*B).trace.im = 0 := hermitian_mul_trace_im_zero hK hB
  have hrev : (S*G*K*B).trace.re = -(G*S*B*K).trace.re := by
    have hs : star (S*G*K*B).trace = -(G*S*B*K).trace := by
      rw [← Matrix.trace_conjTranspose]
      simp only [Matrix.conjTranspose_mul, hB.eq, hK.eq, hG.eq, hS,
        Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_assoc]
      simpa only [Matrix.mul_assoc] using
        congrArg Neg.neg (Matrix.trace_mul_comm (B*K) (G*S))
    simpa using congrArg Complex.re hs
  have hexp : ((M*S).conjTranspose * (M*((K*B).trace • (1:Mat)-K*B))).trace =
      -((K*B).trace * (S*G).trace) + (S*G*K*B).trace := by
    dsimp [G]
    simp only [Matrix.conjTranspose_mul, hS, Matrix.mul_sub, Matrix.neg_mul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
      Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
    ring
  have hcyc : (G*K*B*S).trace = (S*G*K*B).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (G*K) B S
  have hc : (G*(S*B*K-K*B*S)).trace = (G*S*B*K).trace - (S*G*K*B).trace := by
    rw [Matrix.mul_sub, Matrix.trace_sub]; simp only [← Matrix.mul_assoc, hcyc]
  have hcr := congrArg Complex.re hc
  have hexpr := congrArg Complex.re hexp
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.mul_re, hsg, ht] at hcr hexpr
  change (G*(S*B*K-K*B*S)).trace.re +
    2*((M*S).conjTranspose * (M*((K*B).trace • (1:Mat)-K*B))).trace.re = 0
  linarith

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
  have hc0 : complexOct (0:ℂ) = (0:Octonion) := by
    apply Prod.ext <;> apply Quaternion.ext <;> simp [complexOct]
  have hx : hiddenMatrix x = 0 := by
    simpa [x, complexAlbertLinear, complexAlbert, diagonalAlbert, hc0] using
      hiddenMatrix_complexAlbert ((a,b,c),(0,0,0))
  have hy : hiddenMatrix y = 0 := hiddenMatrix_complexAlbert ((d,e,f),(u,v,w))
  have hb : hiddenMatrix (jordan x y) = 0 := by
    simp [hiddenMatrix_jordan, hx, hy, sectorProductHidden, polarAdjugate_zero_left]
  have hB : B = (1/2:ℂ) • (D*H+H*D) := by
    simp [B, D, H, sectorComplexMatrix_jordan, hx, sectorProductComplex]
  have hS : S.conjTranspose = -S := by
    dsimp only [S, D, H]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      (sectorComplexMatrix_isHermitian y).adjugate.eq,
      (sectorComplexMatrix_isHermitian x).adjugate.eq, neg_sub]
  have hCommC : sectorComplexMatrix (U x (U y z) - U y (U x z)) = Q := by
    change sectorComplexLinear (U x (U y z) - U y (U x z)) = Q
    rw [map_sub]
    change sectorComplexMatrix (U x (U y z)) - sectorComplexMatrix (U y (U x z)) = Q
    rw [complex_U x (U y z) hx, complex_U y z hy, complex_U y (U x z) hy, complex_U x z hx]
    simp only [Q, D, H, K, Matrix.mul_assoc]
  have hCommM : hiddenMatrix (U x (U y z) - U y (U x z)) = M*S := by
    change sectorHiddenLinear (U x (U y z) - U y (U x z)) = M*S
    rw [map_sub]
    change hiddenMatrix (U x (U y z)) - hiddenMatrix (U y (U x z)) = M*S
    rw [hidden_U x (U y z) hx, hidden_U y z hy, hidden_U y (U x z) hy, hidden_U x z hx]
    simp only [M, S, D, H, Matrix.mul_assoc, mul_sub]
  have hUC : sectorComplexMatrix (U z (jordan x y)) = K*B*K+gamma G B :=
    complex_U_argument z (jordan x y) hb
  have hUH : hiddenMatrix (U z (jordan x y)) =
      M*((K*B).trace • (1:Mat)-K*B)+sectorAdjointAdjugate M*B :=
    hidden_U_argument z (jordan x y) hb
  have hMetric : phi x y z =
      (Q*(K*B*K)).trace.re + (Q*gamma G B).trace.re +
      2*((M*S).conjTranspose*(M*((K*B).trace • (1:Mat)-K*B))).trace.re +
      2*((M*S).conjTranspose*(sectorAdjointAdjugate M*B)).trace.re := by
    rw [phi, inner_sector_model, hCommC, hCommM, hUC, hUH]
    simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]; ring
  have hPure : (Q*(K*B*K)).trace.re = 0 := by
    have h1 : (D*H*K*(H*D*K)*(D*H*K)).trace = (H*D*K*(D*H*K)*(D*H*K)).trace := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm (D*H*K) (H*D*K*(D*H*K))]
    have h2 : (D*H*K*(H*D*K)*(H*D*K)).trace = (H*D*K*(D*H*K)*(H*D*K)).trace :=
      Matrix.trace_mul_cycle (D*H*K) (H*D*K) (H*D*K)
    have h0 : (Q*(K*B*K)).trace = 0 := by
      calc (Q*(K*B*K)).trace
        _ = (1/2:ℂ) * ((D*H*K*(H*D*K) - H*D*K*(D*H*K)) * (D*H*K + H*D*K)).trace := by
          simp only [Q, hB, Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul,
            Matrix.mul_add, Matrix.add_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
        _ = 0 := by
          simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add, h1, h2]
          ring
    rw [h0, Complex.zero_re]
  have hDdiag : D = Matrix.diagonal ![(a:ℂ), (b:ℂ), (c:ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [D, x, sectorComplexMatrix, complexHermitianMatrix,
        complexCoordinatesLinear, diagonalAlbert, complexPart]
  have hMixedMatrix : gamma Q B = S*B*K-K*B*S := by
    dsimp only [Q, S]
    rw [hB, hDdiag]
    exact mixed_identity a b c H K
  have hMixed : (Q*gamma G B).trace.re +
      2*((M*S).conjTranspose*(M*((K*B).trace • (1:Mat)-K*B))).trace.re = 0 := by
    rw [trace_polar_transfer Q G B, hMixedMatrix]
    exact mixed_trace_cancel M S K B hS
      (sectorComplexMatrix_isHermitian z) (sectorComplexMatrix_isHermitian (jordan x y))
  have hH : H = complexHermitianMatrix ((d,e,f),(u,v,w)) := by
    change complexHermitianMatrix (complexCoordinatesLinear (complexAlbertLinear ((d,e,f),(u,v,w)))) = _
    rw [complexCoordinates_albert]
  have hD : D = complexHermitianMatrix ((a,b,c),(0,0,0)) := by
    simpa [D, x, complexAlbert, diagonalAlbert, hc0] using
      (by change complexHermitianMatrix (complexCoordinatesLinear (complexAlbertLinear ((a,b,c),(0,0,0)))) = _
          rw [complexCoordinates_albert] : sectorComplexMatrix (complexAlbert a b c 0 0 0) = _)
  have hSB : (S*B).trace = (⟨0,-t⟩:ℂ) := by
    dsimp only [S, t]
    rw [hB, hD, hH]
    apply Complex.ext <;>
      simp [complexHermitianMatrix, Matrix.adjugate_fin_three, Matrix.trace, Matrix.diag,
        Matrix.mul_apply, Fin.sum_univ_three, smul_eq_mul, Complex.mul_re, Complex.mul_im] <;> ring
  have hGram : M.conjTranspose * sectorAdjointAdjugate M = star M.det • (1 : Mat) := by
    calc M.conjTranspose * sectorAdjointAdjugate M
      _ = (M.adjugate*M).conjTranspose := by simp only [sectorAdjointAdjugate, Matrix.conjTranspose_mul]
      _ = (M.det • (1 : Mat)).conjTranspose := by rw [Matrix.adjugate_mul]
      _ = _ := by simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  have hCubic : 2*((M*S).conjTranspose*(sectorAdjointAdjugate M*B)).trace.re = 2*t*M.det.im := by
    have htr : ((M*S).conjTranspose*(sectorAdjointAdjugate M*B)).trace =
        star M.det*(S.conjTranspose*B).trace := by
      calc ((M*S).conjTranspose*(sectorAdjointAdjugate M*B)).trace
        _ = ((S.conjTranspose*(M.conjTranspose*sectorAdjointAdjugate M))*B).trace := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by
          rw [hGram]
          simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [htr, hS, Matrix.neg_mul, Matrix.trace_neg, hSB]
    simp [Complex.mul_re]; ring
  change phi x y z = (2*(a-b)*(b-c)*(c-a)*(u*w*star v).im)*M.det.im
  calc phi x y z
    _ = 2*t*M.det.im := by linarith [hMetric, hPure, hMixed, hCubic]
    _ = _ := by dsimp [t]; ring

end
end Glennie
