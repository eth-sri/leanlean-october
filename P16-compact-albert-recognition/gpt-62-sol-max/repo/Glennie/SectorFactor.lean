module
public import Glennie.SectorModel
public import Mathlib.Tactic.Module
public import Glennie.MatrixSimp
public import Glennie.Compact.CyclicTraceNullR01
@[expose] public section
namespace Glennie
noncomputable section
set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false

local notation "Mat" => SectorMatrix
local notation "C" => sectorComplexMatrix
local notation "H" => hiddenMatrix
local notation "Aadj" => sectorAdjointAdjugate
local notation "bar" => sectorComplement

attribute [sector_matrix] Matrix.mul_add Matrix.add_mul Matrix.mul_sub Matrix.sub_mul
  Matrix.mul_smul Matrix.smul_mul Matrix.mul_one Matrix.one_mul Matrix.trace_smul
  Matrix.trace_add Matrix.trace_sub Matrix.trace_neg Matrix.mul_neg Matrix.neg_mul
  Matrix.conjTranspose_mul Matrix.conjTranspose_smul Matrix.conjTranspose_sub
  smul_smul smul_eq_mul

private def polar (G B : Mat) : Mat := G*B+B*G-B.trace • G-G.trace • B+
  (G.trace*B.trace-(G*B).trace) • (1:Mat)

private theorem polar_adj (A B : Mat) : polar A B = (A+B).adjugate-A.adjugate-B.adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [polar, Matrix.adjugate_fin_three, Matrix.mul_apply,
    Matrix.trace, Matrix.diag, Fin.sum_univ_three, smul_eq_mul] <;> ring

private theorem polar_conj (A B : Mat) : sectorPolarAdjugate A B = (polar A B).conjTranspose := by
  simp only [polar_adj, sectorPolarAdjugate, sectorAdjointAdjugate, Matrix.conjTranspose_sub]

private theorem polar_self (M : Mat) : sectorPolarAdjugate M M = (2:ℂ) • Aadj M := by
  rw [sectorPolarAdjugate, ← two_smul ℂ M, sectorAdjointAdjugate, Matrix.adjugate_smul,
    Matrix.conjTranspose_smul]
  change star ((2:ℂ)^2) • Aadj M - Aadj M - Aadj M = _
  norm_num
  module

private def enc : Albert →ₗ[ℝ] Mat × Mat := sectorComplexLinear.prod sectorHiddenLinear
@[simp] private theorem enc_fst (x : Albert) : (enc x).1 = C x := rfl
@[simp] private theorem enc_snd (x : Albert) : (enc x).2 = H x := rfl
private def product (p q : Mat × Mat) : Mat × Mat :=
  (sectorProductComplex p.1 p.2 q.1 q.2, sectorProductHidden p.1 p.2 q.1 q.2)
private theorem enc_j (x y : Albert) : enc (jordan x y) = product (enc x) (enc y) :=
  Prod.ext (sectorComplexMatrix_jordan x y) (hiddenMatrix_jordan x y)
private def quad (p q : Mat × Mat) := (2:ℝ) • product p (product p q) - product (product p p) q
private theorem enc_u (x y : Albert) : enc (U x y) = quad (enc x) (enc y) := by
  simp only [U, quad, map_smul, map_sub, enc_j]

private theorem pure_products (K M B : Mat) :
    product (K,M) (B,0) = ((1/2:ℂ) • (K*B+B*K), (1/2:ℂ) • (M*(bar B))) ∧
    product (B,0) (K,M) = ((1/2:ℂ) • (B*K+K*B), (1/2:ℂ) • (M*(bar B))) := by
  constructor <;> simp [product, sectorProductComplex, sectorProductHidden, sectorPolarAdjugate,
    sectorAdjointAdjugate, Matrix.adjugate_zero]

private theorem U_left (x z : Albert) (hx : H x = 0) :
    enc (U x z) = (C x*(enc z).1*C x, (enc z).2*(C x).adjugate) := by
  rw [enc_u]
  change quad (C x,H x) (C z,H z) = _
  rw [hx]
  simp only [quad, (pure_products _ _ _).2, mul_zero, zero_mul, smul_zero]
  apply Prod.ext <;> apply Matrix.ext <;> intro i j
  all_goals fin_cases i <;> fin_cases j <;>
    simp [sectorComplement, Matrix.adjugate_fin_three, Matrix.mul_apply, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three, smul_eq_mul, Complex.real_smul] <;> ring

private theorem polar_one (X : Mat) : polar 1 X = bar X := by
  simp only [polar, sectorComplement, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat, Matrix.mul_one, Matrix.one_mul]
  module

private theorem polar_mul_left (X A B : Mat) : polar (X*A) (X*B) = polar A B * X.adjugate := by
  simp only [polar_adj, ← Matrix.mul_add, Matrix.adjugate_mul_distrib, Matrix.sub_mul]

private theorem mul_trace {A B : Mat} (ha : A.IsHermitian) (hb : B.IsHermitian) :
    star (A*B).trace = (A*B).trace := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, ha.eq, hb.eq, Matrix.trace_mul_comm]

private theorem bar_smul (t : ℂ) (X : Mat) : bar (t • X) = t • bar X := by
  simp only [sectorComplement, Matrix.trace_smul, smul_smul, smul_sub, smul_eq_mul]

private theorem quad_right (K M B : Mat) (hB : B.IsHermitian) :
    quad (K,M) (B,0) = (K*B*K + polar (M.conjTranspose*M) B,
      M*bar (K*B) + Aadj M*B) := by
  let G := M.conjTranspose*M
  let r : ℂ := 1/2
  let Q := r • (K*B+B*K)
  let N := r • (M*(bar B))
  have hr : star r = r := by norm_num [r]
  have hG : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self _
  have hL := sectorComplement_hermitian hB
  have hsquare : product (K,M) (K,M) = (K*K+bar G, M*bar K+Aadj M) := by
    refine Prod.ext (sectorProductComplex_square K M) ?_
    simp only [product, sectorProductHidden, Prod.fst, Prod.snd, polar_self]
    module
  have hAdj : sectorPolarAdjugate M N = r • (Aadj M * bar (bar B)) := by
    have h := polar_mul_left M 1 (r • bar B)
    rw [mul_one, Matrix.mul_smul, polar_one] at h
    change polar M N = _ at h
    rw [polar_conj, h, bar_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_smul, hr, (sectorComplement_hermitian hL).eq, Matrix.mul_smul]
    rfl
  have htr : ((M.conjTranspose*N).trace.re : ℂ) = (M.conjTranspose*N).trace := by
    apply Complex.conj_eq_iff_re.mp
    dsimp only [N]
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← Matrix.mul_assoc]
    change star (r * (G * bar B).trace) = _
    rw [star_mul, hr, mul_trace hG hL, mul_comm]
  rw [quad, (pure_products K M B).1, hsquare, (pure_products _ _ _).1]
  refine Prod.ext ?_ ?_
  · change (2:ℂ) • sectorProductComplex K M Q N - r • ((K*K+bar G)*B+B*(K*K+bar G)) = K*B*K + polar G B
    rw [sectorProductComplex, htr]
    simp only [sector_matrix, Q, N, hr, hL.eq, G]
    simp only [sector_matrix, r, polar, sectorComplement, Matrix.mul_assoc]
    module
  · change (2:ℂ) • sectorProductHidden K M Q N - r • ((M*bar K+Aadj M)*bar B) = _
    rw [sectorProductHidden, hAdj]
    simp only [sector_matrix, Q, N, r, bar_smul,
      sectorComplement, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat,
      Matrix.trace_mul_comm B K, Matrix.mul_assoc]
    module

private abbrev symmProd (A B : Mat) := (1/2:ℂ) • (A+B)
private abbrev skew (A B : Mat) := A.adjugate-B.adjugate
private abbrev comm (A B K : Mat) := A*K*B-B*K*A

private theorem comm_enc (x y z : Albert) (hx : H x = 0) (hy : H y = 0) :
    enc (U x (U y z) - U y (U x z)) =
      (comm (C x*C y) (C y*C x) (C z), H z*skew (C x*C y) (C y*C x)) := by
  simp only [map_sub, U_left x _ hx, U_left y _ hy, comm, skew, Prod.mk_sub_mk,
    Matrix.mul_assoc, Matrix.adjugate_mul_distrib, Matrix.mul_sub, enc_fst, enc_snd]

private theorem pure_trace (A D K : Mat) : (comm A D K * (K * symmProd A D * K)).trace = 0 := by
  simpa only [comm, symmProd, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Matrix.mul_assoc,
    smul_zero, Matrix.traceAddMonoidHom_apply, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_add] using
    congrArg ((1/2:ℂ) • ·) (Compact.CyclicTraceNullR01.cyclic_word_cancel
      (Matrix.traceAddMonoidHom (Fin 3) ℂ) Matrix.trace_mul_comm (A*K) (D*K))

/-- Polarize the product adjugates before expanding the commutator. -/
private theorem mixed_matrix (A D K : Mat) (hdet : A.det = D.det) :
    polar (comm A D K) (symmProd A D) = skew A D*symmProd A D*K-K*symmProd A D*skew A D := by
  have p1 (X : Mat) : polar X 1 = bar X := by
    simpa only [polar_adj, add_comm 1 X, sub_right_comm] using polar_one X
  have l (X Y : Mat) : polar (X*K*Y) X = bar (K*Y)*X.adjugate := by
    simpa only [Matrix.mul_one, p1, ← Matrix.mul_assoc] using polar_mul_left X (K*Y) 1
  have r (X Y : Mat) : polar (X*K*Y) Y = Y.adjugate*bar (X*K) := by
    have h : polar (X*K*Y) (1*Y) = Y.adjugate * polar (X*K) 1 := by
      simp only [polar_adj, ← Matrix.add_mul, Matrix.adjugate_mul_distrib, Matrix.mul_sub]
    simpa only [Matrix.one_mul, p1] using h
  have split (X Y U V : Mat) : polar (X-Y) (symmProd U V) =
      (1/2:ℂ) • (polar X U+polar X V-(polar Y U+polar Y V)) := by
    simp only [sector_matrix, polar, smul_add, smul_sub]
    module
  rw [comm, split, l A D, r A D, l D A, r D A]
  unfold skew
  simp only [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub]
  congr 1
  simp only [sector_matrix, sectorComplement, Matrix.trace_mul_comm K A, Matrix.trace_mul_comm K D, mul_assoc K A A.adjugate, mul_assoc K D D.adjugate, Matrix.mul_adjugate, Matrix.adjugate_mul, hdet, ← Matrix.mul_assoc]
  module

private theorem polar_transfer (Q G B : Mat) : (Q*polar G B).trace = (G*polar Q B).trace := by
  have h1 := Matrix.trace_mul_cycle' Q B G
  have h2 := (Matrix.trace_mul_cycle' G B Q).symm
  simp only [sector_matrix, polar, Matrix.mul_assoc, h1, h2, Matrix.trace_mul_comm Q G, Matrix.trace_mul_comm B G, Matrix.trace_mul_comm B Q]
  ring

private theorem trace_re_ct (A : Mat) : A.conjTranspose.trace.re = A.trace.re := by
  rw [Matrix.trace_conjTranspose]
  rfl

private theorem mixed_zero (M S K B : Mat) (hS : S.conjTranspose = -S)
    (hK : K.IsHermitian) (hB : B.IsHermitian) :
    ((M.conjTranspose*M)*(S*B*K-K*B*S)).trace.re +
      2*((M*S).conjTranspose*(M*bar (K*B))).trace.re = 0 := by
  let G := M.conjTranspose*M
  have hG : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hk := Complex.conj_eq_iff_im.mp (mul_trace hK hB)
  have hg : (S*G).trace.re = 0 := by
    have h := trace_re_ct (S*G)
    simp only [sector_matrix, hG.eq, hS, Complex.neg_re, Matrix.trace_mul_comm G S] at h
    linarith
  have hr : (G*(S*(B*K))).trace.re = -(S*(G*(K*B))).trace.re := by
    have hrot : (K*(B*(S*G))).trace = (S*(G*(K*B))).trace := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (K*B) (S*G)
    simpa only [sector_matrix, hK.eq, hB.eq, hS, hG.eq, Matrix.mul_assoc,
      hrot, Complex.neg_re] using (trace_re_ct (G*S*B*K)).symm
  have hc : (G*(K*(B*S))).trace = (S*(G*(K*B))).trace := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (G*K*B) S
  change (G*(S*B*K-K*B*S)).trace.re + _ = _
  rw [Matrix.conjTranspose_mul, hS, mul_assoc (-S) M.conjTranspose, ← mul_assoc M.conjTranspose M]
  change (G*(S*B*K-K*B*S)).trace.re + 2*(-S*(G*bar (K*B))).trace.re = _
  simp only [sector_matrix, sectorComplement, Matrix.mul_assoc,
    hc, Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.mul_re, hk,hg,hr]
  ring

private theorem complex_matrix (a b c : ℝ) (u v w : ℂ) :
    C (complexAlbert a b c u v w) = complexHermitianMatrix ((a,b,c),(u,v,w)) := by
  change complexHermitianMatrix (complexCoordinatesLinear (complexAlbertLinear ((a,b,c),(u,v,w)))) = _
  rw [complexCoordinates_albert]

private theorem diagonal_complex (a b c : ℝ) :
    diagonalAlbert a b c = complexAlbert a b c 0 0 0 := rfl

private theorem weight (a b c d e f : ℝ) (u v w : ℂ) :
    let D := C (diagonalAlbert a b c)
    let Y := C (complexAlbert d e f u v w)
    (skew (D*Y) (Y*D)*symmProd (D*Y) (Y*D)).trace =
      ⟨0,-(a-b)*(b-c)*(c-a)*(u*w*star v).im⟩ := by
  dsimp only
  rw [diagonal_complex, complex_matrix, complex_matrix]
  unfold skew
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
  apply Complex.ext
  all_goals simp [complexHermitianMatrix, Matrix.adjugate_fin_three, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_three, smul_eq_mul, Complex.mul_re, Complex.mul_im]
  all_goals ring

private theorem adj_contract (M S B : Mat) (hS : S.conjTranspose = -S) :
    ((M*S).conjTranspose * (Aadj M*B)).trace = -(star M.det * (S*B).trace) := by
  have h : M.conjTranspose * Aadj M = star M.det • (1:Mat) := by
    rw [sectorAdjointAdjugate, ← Matrix.conjTranspose_mul, Matrix.adjugate_mul,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  rw [Matrix.conjTranspose_mul, hS, mul_assoc, ← mul_assoc M.conjTranspose, h]
  simp [Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]

private def sectorPairing (p q : Mat × Mat) : ℝ :=
  (p.1*q.1).trace.re + 2*(p.2.conjTranspose*q.2).trace.re

private theorem enc_inner (x y : Albert) : inner x y = sectorPairing (enc x) (enc y) :=
  inner_sector_model x y

private theorem phi_pure (x y z : Albert) (hx : H x = 0) (hy : H y = 0) :
    phi x y z = -2 * (star (H z).det *
      (skew (C x*C y) (C y*C x) * symmProd (C x*C y) (C y*C x)).trace).re := by
  let A := C x*C y
  let D := C y*C x
  let K := C z
  let M := H z
  let B := symmProd A D
  let S := skew A D
  let Q := comm A D K
  have hJ : enc (jordan x y) = (B,0) := by
    rw [enc_j]
    change product (C x,H x) (C y,H y) = _
    rw [hx,hy,(pure_products _ _ _).2,zero_mul,smul_zero]
  have hS : S.conjTranspose = -S := by
    simp only [S,skew,A,D, Matrix.conjTranspose_sub, Matrix.adjugate_conjTranspose,
      Matrix.conjTranspose_mul, (sectorComplexMatrix_isHermitian x).eq,
      (sectorComplexMatrix_isHermitian y).eq, neg_sub]
  have hB : B.IsHermitian := (show C (jordan x y) = B from congrArg Prod.fst hJ) ▸ sectorComplexMatrix_isHermitian (jordan x y)
  have hp : (Q*(K*B*K)).trace = 0 := pure_trace A D K
  have hm : polar Q B = S*B*K-K*B*S :=
    mixed_matrix A D K (by simp only [A,D, Matrix.det_mul, mul_comm])
  have hz := mixed_zero M S K B hS (sectorComplexMatrix_isHermitian z) hB
  rw [phi, enc_inner, comm_enc x y z hx hy, enc_u, hJ]
  change sectorPairing (Q,M*S) (quad (K,M) (B,0)) = _
  rw [quad_right _ _ _ hB]
  simp only [sectorPairing, Prod.fst, Prod.snd, Matrix.mul_add, Matrix.trace_add, Complex.add_re,
    hp, Complex.zero_re, zero_add, polar_transfer Q (M.conjTranspose*M) B, hm,
    adj_contract M S B hS, Complex.neg_re]
  linear_combination hz

/-- The hidden determinant controls Phi when the first two arguments are complex. -/
theorem phi_diagonal_complex_factor (a b c d e f : ℝ) (u v w : ℂ) (z : Albert) :
    phi (diagonalAlbert a b c) (complexAlbert d e f u v w) z =
      (2*(a-b)*(b-c)*(c-a)*(u*w*star v).im) * (H z).det.im := by
  have hx : H (diagonalAlbert a b c) = 0 :=
    diagonal_complex a b c ▸ hiddenMatrix_complexAlbert ((a,b,c),(0,0,0))
  have hy : H (complexAlbert d e f u v w) = 0 := hiddenMatrix_complexAlbert ((d,e,f),(u,v,w))
  rw [phi_pure _ _ _ hx hy, weight]
  simp [Complex.mul_re]
  ring

end
end Glennie
