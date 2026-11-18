module
public import Glennie.Native.OrderedPositivePair
public import Glennie.UnitShifts
public import Glennie.Compact.FlowFamily
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

namespace Glennie.Compact.Affine20
abbrev Triple := Fin 3 → Fin 3 → Glennie.Albert
abbrev Ledger54 :=
  (Fin 3 → Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) ×
  (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ)
end Glennie.Compact.Affine20

namespace Glennie.Compact.PairNormNearby

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20 Glennie.NativeOrderedPositivePair

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike

private theorem fe_complex_cubic (d e f : ℝ) (u v w : ℂ) :
    newtonCubicNorm (complexAlbert d e f u v w) = d * e * f -
      d * Complex.normSq w - e * Complex.normSq v - f * Complex.normSq u +
      2 * (u * w * star v).re := by
  rw [newtonCubicNorm_coordinates]
  simp [complexAlbert, complexOct, octNormSq, Quaternion.normSq_def', octMul, octConj, octRe,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]; ring

private theorem fe_complex_square (d e f : ℝ) (u v w : ℂ) :
    jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w) =
      complexAlbert (d ^ 2 + Complex.normSq u + Complex.normSq v)
        (e ^ 2 + Complex.normSq u + Complex.normSq w)
        (f ^ 2 + Complex.normSq v + Complex.normSq w)
        (u * (d + e) + v * star w) (v * (d + f) + u * w) (w * (e + f) + star u * v) := by
  ext <;> simp [jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    complexAlbert, complexOct, octNormSq, Quaternion.normSq_def', octMul, octConj,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

private theorem hiddenAlbert_cubicNorm (M : Matrix (Fin 3) (Fin 3) ℂ) :
    newtonCubicNorm (hiddenAlbert M) = 2 * M.det.re := by
  rw [newtonCubicNorm_coordinates]
  simp [hiddenAlbert, hiddenOct, octMul, octConj, octRe, Matrix.det_fin_three, Complex.mul_re, Complex.mul_im]; ring

private theorem complexProjection_sub (x y : Albert) :
    complexProjection (x - y) = complexProjection x - complexProjection y :=
  (complexAlbertLinear.comp complexCoordinatesLinear).map_sub x y

private theorem complexProjection_add (x y : Albert) :
    complexProjection (x + y) = complexProjection x + complexProjection y :=
  (complexAlbertLinear.comp complexCoordinatesLinear).map_add x y

private theorem frame_in_complexSector (p : Fin 3 → Albert) (hp : Frame p)
    (he : InComplexSector (encoder p)) (i : Fin 3) : p i ∈ complexSector := by
  have he' := (complexSector_mem_iff _).mpr he
  have hs := (complexSector_mem_iff _).mpr (complexSector_jordan _ _ he he)
  fin_cases i <;> dsimp
  · rw [← frame_projector_first p hp]; exact complexSector.smul_mem _ (complexSector.sub_mem hs he')
  · rw [← frame_projector_middle p hp]; exact complexSector.sub_mem (by rw [complexSector_mem_iff]; simp [InComplexSector, OctInComplex, unit]) hs
  · rw [← frame_projector_last p hp]; exact complexSector.smul_mem _ (complexSector.add_mem hs he')

private theorem im_sq_eq_of_normSq_eq (z w : ℂ) (hn : Complex.normSq z = Complex.normSq w)
    (hr : z.re = w.re) : z.im ^ 2 = w.im ^ 2 := by
  rw [Complex.normSq_apply, Complex.normSq_apply, hr] at hn; nlinarith

private theorem two_by_two (A B C D X Y : ℝ)
    (h1 : A * X + B * Y = 0) (h2 : C * X + D * Y = 0) (hdet : A * D - B * C ≠ 0) : X = 0 ∧ Y = 0 :=
  ⟨(mul_eq_zero.mp (by linear_combination D * h1 - B * h2 : (A * D - B * C) * X = 0)).resolve_left hdet,
   (mul_eq_zero.mp (by linear_combination A * h2 - C * h1 : (A * D - B * C) * Y = 0)).resolve_left hdet⟩

private theorem normSq_det_eq_gram_det_re (M : Matrix (Fin 3) (Fin 3) ℂ) :
    Complex.normSq M.det = (M.conjTranspose * M).det.re := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose]; simp [Complex.mul_re, Complex.normSq_apply]

private theorem nondegenerate_core (a b D0 D1 D2 e0 e1 e2 v R Sg : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hD0 : |D0| < 1 / 25) (hD1 : |D1| < 1 / 25) (hD2 : |D2| < 1 / 25)
    (he0 : |e0 - 2 / 3| < 1 / 25) (he1 : |e1 - 2 / 3| < 1 / 25) (he2 : |e2 - 2 / 3| < 1 / 25)
    (hv0 : 0 ≤ v)
    (E0 : e0 = D0 ^ 2 + a ^ 2 + v) (E1 : e1 = D1 ^ 2 + a ^ 2 + b ^ 2) (E2 : e2 = D2 ^ 2 + v + b ^ 2)
    (C : 0 = D0 * D1 * D2 - D0 * b ^ 2 - D1 * v - D2 * a ^ 2 + 2 * (a * b * R))
    (hsplit : v = R ^ 2 + Sg ^ 2) :
    1 / 2 < a ∧ 1 / 2 < b ∧ Sg ≠ 0 := by
  obtain ⟨l0, r0⟩ := abs_lt.mp hD0; obtain ⟨l1, r1⟩ := abs_lt.mp hD1; obtain ⟨l2, r2⟩ := abs_lt.mp hD2
  obtain ⟨m0, n0⟩ := abs_lt.mp he0; obtain ⟨m1, n1⟩ := abs_lt.mp he1; obtain ⟨m2, n2⟩ := abs_lt.mp he2
  have q0 := sq_lt_sq' l0 r0; have q1 := sq_lt_sq' l1 r1; have q2 := sq_lt_sq' l2 r2
  have p0 := sq_nonneg D0; have p1 := sq_nonneg D1; have p2 := sq_nonneg D2
  have hasq : (1 : ℝ) / 4 < a ^ 2 := by linarith
  have hbsq : (1 : ℝ) / 4 < b ^ 2 := by linarith
  have halt : 1 / 2 < a := by nlinarith only [ha, hasq, sq_nonneg (a - 1 / 2)]
  have hblt : 1 / 2 < b := by nlinarith only [hb, hbsq, sq_nonneg (b - 1 / 2)]
  refine ⟨halt, hblt, fun h0 => ?_⟩
  have hab2 : (1 : ℝ) / 16 < (a * b) ^ 2 := by
    have hab : (1 : ℝ) / 4 < a * b := by nlinarith only [halt, hblt]
    nlinarith only [hab]
  have ap {x y bx by' : ℝ} (hx : |x| < bx) (hy : |y| < by') : |x * y| < bx * by' := by
    rw [abs_mul]; nlinarith only [hx, hy, abs_nonneg x, abs_nonneg y]
  obtain ⟨u1, u2⟩ := abs_lt.mp (ap hD0 (abs_lt.mpr ⟨by linarith, (by linarith : b ^ 2 < 1 / 2)⟩))
  obtain ⟨w1, w2⟩ := abs_lt.mp (ap hD1 (abs_lt.mpr ⟨by linarith, (by linarith : v < 1 / 2)⟩))
  obtain ⟨x1, x2⟩ := abs_lt.mp (ap hD2 (abs_lt.mpr ⟨by linarith, (by linarith : a ^ 2 < 1 / 2)⟩))
  obtain ⟨z1, z2⟩ := abs_lt.mp (ap (ap hD0 hD1) hD2)
  have hABR := sq_lt_sq' (by linarith : -(1 / 16 : ℝ) < a * b * R) (by linarith : a * b * R < 1 / 16)
  have hkey : R ^ 2 * (1 / 16) ≤ (a * b * R) ^ 2 := by
    simpa only [show R ^ 2 * (a * b) ^ 2 = (a * b * R) ^ 2 by ring] using mul_le_mul_of_nonneg_left hab2.le (sq_nonneg R)
  rw [h0] at hsplit; linarith

@[simp] private theorem octConj_zero : octConj (0 : Octonion) = 0 := by apply Prod.ext <;> simp [octConj]
@[simp] private theorem octMul_zero_left (y : Octonion) : octMul 0 y = 0 := by apply Prod.ext <;> simp [octMul]
@[simp] private theorem octMul_zero_right (x : Octonion) : octMul x 0 = 0 := by apply Prod.ext <;> simp [octMul]
@[simp] private theorem octNormSq_zero : octNormSq (0 : Octonion) = 0 := by norm_num [octNormSq, Quaternion.normSq_def']

private theorem frame_eq_of_encoder_eq (q s : Fin 3 → Albert) (hq : Frame q) (hs : Frame s)
    (m : CompactAutomorphism) (hEnc : m.equiv (encoder q) = encoder s) (i : Fin 3) :
    m.equiv (q i) = s i := by
  have hp (p : Fin 3 → Albert) (hp : Frame p) : p = projectorFrame (encoder p) := funext fun j => by
    fin_cases j
    · exact (frame_projector_first p hp).symm
    · exact (frame_projector_middle p hp).symm
    · exact (frame_projector_last p hp).symm
  rw [congrFun (hp q hq) i, compactAutomorphism_projectorFrame, hEnc, ← congrFun (hp s hs) i]

private theorem flatFrameP_eq :
    flatFrameP 0 = diagonalAlbert 0 0 1 ∧ flatFrameP 1 = diagonalAlbert 0 1 0 ∧ flatFrameP 2 = diagonalAlbert 1 0 0 := by
  have hj : jordan flatXN flatXN = diagonalAlbert 1 0 1 := by
    apply Albert.ext <;> simp [flatXN, diagonalAlbert, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12]
  exact ⟨by show (1 / 2 : ℝ) • (jordan flatXN flatXN - flatXN) = _; rw [hj]; ext <;> simp [diagonalAlbert, flatXN] <;> norm_num,
    by show (1 : Albert) - jordan flatXN flatXN = _; rw [hj]; ext <;> simp [diagonalAlbert] <;> norm_num,
    by show (1 / 2 : ℝ) • (jordan flatXN flatXN + flatXN) = _; rw [hj]; ext <;> simp [diagonalAlbert, flatXN] <;> norm_num⟩

private theorem inner_flatFrameP (x : Albert) :
    inner (flatFrameP 0) x = x.d2 ∧ inner (flatFrameP 1) x = x.d1 ∧ inner (flatFrameP 2) x = x.d0 := by
  have hid (a b c : ℝ) : inner (diagonalAlbert a b c) x = a * x.d0 + b * x.d1 + c * x.d2 := by
    simp [inner_coordinates, diagonalAlbert, octDot_coordinates]
  rw [flatFrameP_eq.1, flatFrameP_eq.2.1, flatFrameP_eq.2.2, hid, hid, hid]
  exact ⟨by ring, by ring, by ring⟩

private theorem flatFrameP_isDiagonal (i : Fin 3) : IsDiagonal (flatFrameP i) :=
  frame_projectors_diagonal flatFrameP flatFrameP_frame (by rw [flatFrameP_encoder]; simp [IsDiagonal, flatXN]) i

private theorem flatFrameP_inComplexSector (i : Fin 3) : InComplexSector (flatFrameP i) :=
  diagonal_inComplex _ (flatFrameP_isDiagonal i)

@[simp] private theorem complexPart_complexOct (z : ℂ) : complexPart (complexOct z) = z := Complex.ext rfl rfl
@[simp] private theorem complexPart_octScalar (a : ℝ) : complexPart (octScalar a) = (a : ℂ) := rfl

private theorem octInComplex_ext (x x' : Octonion) (hx : OctInComplex x) (hx' : OctInComplex x')
    (h : complexPart x = complexPart x') : x = x' := by
  refine Prod.ext ?_ (hx.2.2.trans hx'.2.2.symm)
  apply Quaternion.ext
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h
  · exact hx.1.trans hx'.1.symm
  · exact hx.2.1.trans hx'.2.1.symm

private theorem octDot_inComplex (x x' : Octonion) (hx : OctInComplex x) (hx' : OctInComplex x') :
    octDot x x' = (complexPart x).re * (complexPart x').re + (complexPart x).im * (complexPart x').im := by
  rw [octDot_coordinates]; simp [complexPart, hx.1, hx.2.1, hx.2.2, hx'.1, hx'.2.1, hx'.2.2]

private theorem real_real_conj (a b : ℝ) (z : ℂ) :
    ((a : ℂ) * (b : ℂ) * star z).re = a * b * z.re ∧ ((a : ℂ) * (b : ℂ) * star z).im = -(a * b * z.im) := by
  constructor <;> simp [Complex.mul_re, Complex.mul_im]

private theorem nearby_pair_normalization
    (p q p' q' : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hp' : Frame p') (hq' : Frame q')
    (hbox : ∀ i j : Fin 3, |inner (p i) (q j) - 1 / 3| < 1 / 50)
    (hEq : ∀ i j : Fin 3, inner (p i) (q j) = inner (p' i) (q' j)) :
    ∃ (g g' : CompactAutomorphism) (a b : ℝ),
      (∀ i : Fin 3, g.equiv (p i) = flatFrameP i) ∧
      (∀ i : Fin 3, g'.equiv (p' i) = flatFrameP i) ∧
      (∀ i : Fin 3, g.equiv (q i) = g'.equiv (q' i)) ∧
      InComplexSector (encoder fun i => g'.equiv (q' i)) ∧
      (encoder fun i => g'.equiv (q' i)).o01 = octScalar a ∧
      (encoder fun i => g'.equiv (q' i)).o12 = octScalar b ∧
      0 < a ∧ 0 < b ∧
      (complexPart (encoder fun i => g'.equiv (q' i)).o02).im ≠ 0 := by
  obtain ⟨g, a, b, ha, hb, hgp, h01g, h12g, hsecg⟩ := native_ordered_positive_pair p hp (encoder q)
  obtain ⟨g', a', b', ha', hb', hgp', h01g', h12g', hsecg'⟩ := native_ordered_positive_pair p' hp' (encoder q')
  set Q := fun i => g.equiv (q i); set Q' := fun i => g'.equiv (q' i)
  set y := encoder Q; set y' := encoder Q'
  have hQf : Frame Q := g.map_frame q hq; have hQf' : Frame Q' := g'.map_frame q' hq'
  have hyg : y = g.equiv (encoder q) := g.encoder_map q; have hyg' : y' = g'.equiv (encoder q') := g'.encoder_map q'
  have hcy : InComplexSector y := hyg ▸ hsecg; have hcy' : InComplexSector y' := hyg' ▸ hsecg'
  have hy01 : y.o01 = octScalar a := hyg ▸ h01g; have hy12 : y.o12 = octScalar b := hyg ▸ h12g
  have hy01' : y'.o01 = octScalar a' := hyg' ▸ h01g'; have hy12' : y'.o12 = octScalar b' := hyg' ▸ h12g'
  have hcoord (r : Fin 3 → Albert) (hP : ∀ i j, inner (flatFrameP i) (r j) = inner (p i) (q j)) (j : Fin 3) :
      (r j).d0 = inner (p 2) (q j) ∧ (r j).d1 = inner (p 1) (q j) ∧ (r j).d2 = inner (p 0) (q j) := by
    have hi := inner_flatFrameP (r j)
    exact ⟨hi.2.2.symm.trans (hP 2 j), hi.2.1.symm.trans (hP 1 j), hi.1.symm.trans (hP 0 j)⟩
  have hcQ := hcoord Q fun i j => by rw [← hgp i]; exact g.inner_map _ _
  have hcQ' := hcoord Q' fun i j => by rw [← hgp' i, g'.inner_map, ← hEq]
  have hd0 : y.d0 = y'.d0 := by show (Q 2).d0 - (Q 0).d0 = (Q' 2).d0 - (Q' 0).d0; rw [(hcQ 2).1, (hcQ 0).1, (hcQ' 2).1, (hcQ' 0).1]
  have hd1 : y.d1 = y'.d1 := by show (Q 2).d1 - (Q 0).d1 = (Q' 2).d1 - (Q' 0).d1; rw [(hcQ 2).2.1, (hcQ 0).2.1, (hcQ' 2).2.1, (hcQ' 0).2.1]
  have hd2 : y.d2 = y'.d2 := by show (Q 2).d2 - (Q 0).d2 = (Q' 2).d2 - (Q' 0).d2; rw [(hcQ 2).2.2, (hcQ 0).2.2, (hcQ' 2).2.2, (hcQ' 0).2.2]
  have hs0 : (jordan y y).d0 = (jordan y' y').d0 := by
    rw [frame_encoder_square Q hQf, frame_encoder_square Q' hQf']
    show (Q 2).d0 + (Q 0).d0 = (Q' 2).d0 + (Q' 0).d0; rw [(hcQ 2).1, (hcQ 0).1, (hcQ' 2).1, (hcQ' 0).1]
  have hs1 : (jordan y y).d1 = (jordan y' y').d1 := by
    rw [frame_encoder_square Q hQf, frame_encoder_square Q' hQf']
    show (Q 2).d1 + (Q 0).d1 = (Q' 2).d1 + (Q' 0).d1; rw [(hcQ 2).2.1, (hcQ 0).2.1, (hcQ' 2).2.1, (hcQ' 0).2.1]
  have hs2 : (jordan y y).d2 = (jordan y' y').d2 := by
    rw [frame_encoder_square Q hQf, frame_encoder_square Q' hQf']
    show (Q 2).d2 + (Q 0).d2 = (Q' 2).d2 + (Q' 0).d2; rw [(hcQ 2).2.2, (hcQ 0).2.2, (hcQ' 2).2.2, (hcQ' 0).2.2]
  have hcub : newtonCubicNorm y = 0 := frame_encoder_cubicNorm _ hQf
  have hcub' : newtonCubicNorm y' = 0 := frame_encoder_cubicNorm _ hQf'
  have hb_diff (i : Fin 3) : |inner (p i) (q 2) - inner (p i) (q 0)| < 1 / 25 ∧
      |(inner (p i) (q 2) + inner (p i) (q 0)) - 2 / 3| < 1 / 25 := by
    obtain ⟨l2, r2⟩ := abs_lt.mp (hbox i 2); obtain ⟨l0, r0⟩ := abs_lt.mp (hbox i 0)
    exact ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  have hsq_eq (w : Albert) (hw : InComplexSector w) :
      (jordan w w).d0 = w.d0 ^ 2 + Complex.normSq (complexPart w.o01) + Complex.normSq (complexPart w.o02) ∧
      (jordan w w).d1 = w.d1 ^ 2 + Complex.normSq (complexPart w.o01) + Complex.normSq (complexPart w.o12) ∧
      (jordan w w).d2 = w.d2 ^ 2 + Complex.normSq (complexPart w.o02) + Complex.normSq (complexPart w.o12) ∧
      newtonCubicNorm w = w.d0 * w.d1 * w.d2 - w.d0 * Complex.normSq (complexPart w.o12) -
        w.d1 * Complex.normSq (complexPart w.o02) - w.d2 * Complex.normSq (complexPart w.o01) +
        2 * (complexPart w.o01 * complexPart w.o12 * star (complexPart w.o02)).re := by
    have h1 := fe_complex_square w.d0 w.d1 w.d2 (complexPart w.o01) (complexPart w.o02) (complexPart w.o12)
    have h2 := fe_complex_cubic w.d0 w.d1 w.d2 (complexPart w.o01) (complexPart w.o02) (complexPart w.o12)
    rw [complexAlbert_eq w hw] at h1 h2
    exact ⟨congrArg Albert.d0 h1, congrArg Albert.d1 h1, congrArg Albert.d2 h1, h2⟩
  obtain ⟨E0, E1, E2, C⟩ := hsq_eq y hcy; obtain ⟨E0', E1', E2', C'⟩ := hsq_eq y' hcy'
  have hns_sc (r : ℝ) : Complex.normSq (complexPart (octScalar r)) = r ^ 2 := by rw [complexPart_octScalar, Complex.normSq_ofReal]; ring
  have hau : Complex.normSq (complexPart y.o01) = a ^ 2 := by rw [hy01, hns_sc]
  have hbw : Complex.normSq (complexPart y.o12) = b ^ 2 := by rw [hy12, hns_sc]
  have hau' : Complex.normSq (complexPart y'.o01) = a' ^ 2 := by rw [hy01', hns_sc]
  have hbw' : Complex.normSq (complexPart y'.o12) = b' ^ 2 := by rw [hy12', hns_sc]
  have htri_y : (complexPart y.o01 * complexPart y.o12 * star (complexPart y.o02)).re = a * b * (complexPart y.o02).re := by
    rw [hy01, hy12, complexPart_octScalar, complexPart_octScalar, (real_real_conj a b _).1]
  have htri_y' : (complexPart y'.o01 * complexPart y'.o12 * star (complexPart y'.o02)).re = a' * b' * (complexPart y'.o02).re := by
    rw [hy01', hy12', complexPart_octScalar, complexPart_octScalar, (real_real_conj a' b' _).1]
  obtain ⟨hapos, hbpos, hsigma⟩ := nondegenerate_core a b y.d0 y.d1 y.d2 (jordan y y).d0 (jordan y y).d1 (jordan y y).d2
    (Complex.normSq (complexPart y.o02)) (complexPart y.o02).re (complexPart y.o02).im ha hb
    (by show |(Q 2).d0 - (Q 0).d0| < _; rw [(hcQ 2).1, (hcQ 0).1]; exact (hb_diff 2).1)
    (by show |(Q 2).d1 - (Q 0).d1| < _; rw [(hcQ 2).2.1, (hcQ 0).2.1]; exact (hb_diff 1).1)
    (by show |(Q 2).d2 - (Q 0).d2| < _; rw [(hcQ 2).2.2, (hcQ 0).2.2]; exact (hb_diff 0).1)
    (by rw [frame_encoder_square Q hQf]; show |(Q 2).d0 + (Q 0).d0 - _| < _; rw [(hcQ 2).1, (hcQ 0).1]; exact (hb_diff 2).2)
    (by rw [frame_encoder_square Q hQf]; show |(Q 2).d1 + (Q 0).d1 - _| < _; rw [(hcQ 2).2.1, (hcQ 0).2.1]; exact (hb_diff 1).2)
    (by rw [frame_encoder_square Q hQf]; show |(Q 2).d2 + (Q 0).d2 - _| < _; rw [(hcQ 2).2.2, (hcQ 0).2.2]; exact (hb_diff 0).2)
    (Complex.normSq_nonneg _) (by rwa [hau] at E0) (by rwa [hau, hbw] at E1) (by rwa [hbw] at E2)
    (by rw [hcub, hau, hbw, htri_y] at C; exact C) (by rw [Complex.normSq_apply]; ring)
  rw [hd0, hs0] at E0; rw [hd1, hs1] at E1; rw [hd2, hs2] at E2; rw [hcub] at C; rw [hcub'] at C'
  have hn01 : Complex.normSq (complexPart y.o01) = Complex.normSq (complexPart y'.o01) := by linarith
  have hn02 : Complex.normSq (complexPart y.o02) = Complex.normSq (complexPart y'.o02) := by linarith
  have hn12 : Complex.normSq (complexPart y.o12) = Complex.normSq (complexPart y'.o12) := by linarith
  have haa : a = a' := by rw [hau, hau'] at hn01; nlinarith
  have hbb : b = b' := by rw [hbw, hbw'] at hn12; nlinarith
  have hre : (complexPart y.o02).re = (complexPart y'.o02).re := by
    have hc : a * b * (complexPart y.o02).re = a * b * (complexPart y'.o02).re := by
      rw [hd0, hd1, hd2, hn01, hn02, hn12, htri_y] at C; rw [htri_y', ← haa, ← hbb] at C'; linarith
    exact mul_left_cancel₀ (mul_ne_zero (by linarith) (by linarith)) hc
  have himsq := im_sq_eq_of_normSq_eq _ _ hn02 hre
  have hsigma' : (complexPart y'.o02).im ≠ 0 := fun hz => hsigma (by nlinarith [show (complexPart y.o02).im ^ 2 = 0 by rw [himsq, hz, sq, mul_zero]])
  have hrel : ∃ m : CompactAutomorphism, (∀ i, m.equiv (flatFrameP i) = flatFrameP i) ∧ m.equiv y = y' := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp himsq with him | him
    · exact ⟨.refl, fun _ => rfl, show y = y' from Albert.ext hd0 hd1 hd2 (by rw [hy01, hy01', haa])
        (octInComplex_ext _ _ hcy.2.1 hcy'.2.1 (Complex.ext hre him)) (by rw [hy12, hy12', hbb])⟩
    · have hni : -octI = ((⟨0, -1, 0, 0⟩ : Quaternion ℝ), (0 : Quaternion ℝ)) := by ext <;> simp [octI, quatI]
      obtain ⟨k, hk, hkI⟩ := exists_octAutomorphism_to_i (-octI)
        (by rw [hni]; rfl) (by rw [hni]; norm_num [octNormSq, Quaternion.normSq_def'])
      have hkIneg : k.A octI = -octI := by
        have h : k.A ((-1 : ℝ) • octI) = octI := by rw [neg_one_smul]; exact hkI
        rw [LinearEquiv.map_smul, neg_one_smul] at h; simpa using congrArg Neg.neg h
      have hconj (x : Octonion) (hx : OctInComplex x) : OctInComplex (k.A x) ∧ complexPart (k.A x) = star (complexPart x) := by
        have hdec : x = octScalar (complexPart x).re + (complexPart x).im • octI := by
          ext <;> simp [octScalar, octI, quatI, complexPart, hx.1, hx.2.1, hx.2.2]
        have hkA : k.A x = octScalar (complexPart x).re - (complexPart x).im • octI := by
          conv_lhs => rw [hdec]; rw [map_add, map_smul, diagonalOctTriple_scalar k hk, hkIneg, smul_neg, ← sub_eq_add_neg]
        rw [hkA]; exact ⟨by simp [OctInComplex, octScalar, octI, quatI], by apply Complex.ext <;> simp [complexPart, octScalar, octI, quatI]⟩
      refine ⟨k.compactAutomorphism, frame_eq_of_encoder_eq flatFrameP flatFrameP flatFrameP_frame flatFrameP_frame
        k.compactAutomorphism (by rw [flatFrameP_encoder]; change (⟨_, _, _, k.A _, k.C _, k.B _⟩ : Albert) = flatXN; simp [flatXN]),
        Albert.ext hd0 hd1 hd2 ?_ ?_ ?_⟩
      · exact octInComplex_ext _ _ (hconj y.o01 hcy.1).1 hcy'.1 (by change complexPart (k.A y.o01) = _; rw [(hconj y.o01 hcy.1).2, hy01, hy01', haa]; simp)
      · have hc02 : (k.compactAutomorphism.equiv y).o02 = k.A y.o02 := hk.2.1 _
        exact octInComplex_ext _ _ (hc02 ▸ (hconj y.o02 hcy.2.1).1) hcy'.2.1 (by rw [hc02, (hconj y.o02 hcy.2.1).2]; exact Complex.ext hre (by simp [him]))
      · have hb12 : (k.compactAutomorphism.equiv y).o12 = k.A y.o12 := hk.1 _
        exact octInComplex_ext _ _ (hb12 ▸ (hconj y.o12 hcy.2.2).1) hcy'.2.2 (by rw [hb12, (hconj y.o12 hcy.2.2).2, hy12, hy12', hbb]; simp)
  obtain ⟨m, hmP, hmy⟩ := hrel
  exact ⟨m.comp g, g', a', b', fun i => by rw [CompactAutomorphism.comp_apply, hgp, hmP], hgp',
    frame_eq_of_encoder_eq q Q' hq hQf' (m.comp g) (by rw [CompactAutomorphism.comp_apply, ← hyg, hmy]),
    hcy', hy01', hy12', by linarith, by linarith, hsigma'⟩

private theorem inner_sector_complexProjection (v W : Albert) (hv : InComplexSector v) :
    inner v W = inner v (complexProjection W) := by
  conv_lhs => rw [← complex_hidden_decomposition W]
  rw [inner_add_right, ← complexProjection_eq_self v hv, complex_hidden_orthogonal, complexProjection_eq_self v hv, add_zero]

private theorem slot_pairings_zero (z E : Albert)
    (hE0 : E.d0 = 0) (hE1 : E.d1 = 0) (hE2 : E.d2 = 0)
    (h : ∀ i : Fin 3, inner (jordan (flatFrameP i) z) E = 0) :
    octDot z.o01 E.o01 = 0 ∧ octDot z.o02 E.o02 = 0 ∧ octDot z.o12 E.o12 = 0 := by
  have hdj (x : Albert) (hx : IsDiagonal x) :
      inner (jordan x z) E = (x.d0 + x.d1) * octDot z.o01 E.o01 + (x.d0 + x.d2) * octDot z.o02 E.o02 +
        (x.d1 + x.d2) * octDot z.o12 E.o12 := by
    rw [inner_coordinates, hE0, hE1, hE2, jordan_o01, jordan_o02, jordan_o12, hx.1, hx.2.1, hx.2.2]
    simp [octDot_smul_left]; ring
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  rw [hdj _ (flatFrameP_isDiagonal 0), flatFrameP_eq.1] at h0
  rw [hdj _ (flatFrameP_isDiagonal 1), flatFrameP_eq.2.1] at h1
  rw [hdj _ (flatFrameP_isDiagonal 2), flatFrameP_eq.2.2] at h2
  simp only [diagonalAlbert] at h0 h1 h2
  exact ⟨by linarith, by linarith, by linarith⟩

private theorem sector_slot_recovery (y E : Albert) (a b : ℝ)
    (hcy : InComplexSector y) (hcE : InComplexSector E)
    (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b)
    (hapos : 0 < a) (hbpos : 0 < b) (hsigma : (complexPart y.o02).im ≠ 0)
    (hE0 : E.d0 = 0) (hE1 : E.d1 = 0) (hE2 : E.d2 = 0)
    (p1 : octDot y.o01 E.o01 = 0) (p2 : octDot y.o02 E.o02 = 0) (p3 : octDot y.o12 E.o12 = 0)
    (q1 : octDot (jordan y y).o01 E.o01 = 0) (q2 : octDot (jordan y y).o02 E.o02 = 0)
    (q3 : octDot (jordan y y).o12 E.o12 = 0) :
    E = 0 := by
  have hcsq : InComplexSector (jordan y y) := complexSector_jordan y y hcy hcy
  have hsq := fe_complex_square y.d0 y.d1 y.d2 (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  rw [complexAlbert_eq y hcy, h01, h12, complexPart_octScalar, complexPart_octScalar] at hsq
  have s01 : complexPart (jordan y y).o01 = (a : ℂ) * (y.d0 + y.d1) + complexPart y.o02 * star (b : ℂ) := by
    simpa [complexAlbert] using congrArg (fun x : Albert => complexPart x.o01) hsq
  have s02 : complexPart (jordan y y).o02 = complexPart y.o02 * (y.d0 + y.d2) + (a : ℂ) * (b : ℂ) := by
    simpa [complexAlbert] using congrArg (fun x : Albert => complexPart x.o02) hsq
  have s12 : complexPart (jordan y y).o12 = (b : ℂ) * (y.d1 + y.d2) + star (a : ℂ) * complexPart y.o02 := by
    simpa [complexAlbert] using congrArg (fun x : Albert => complexPart x.o12) hsq
  rw [octDot_inComplex y.o01 E.o01 hcy.1 hcE.1, h01, complexPart_octScalar, Complex.ofReal_re, Complex.ofReal_im] at p1
  rw [octDot_inComplex (jordan y y).o01 E.o01 hcsq.1 hcE.1, s01] at q1
  rw [octDot_inComplex y.o02 E.o02 hcy.2.1 hcE.2.1] at p2
  rw [octDot_inComplex (jordan y y).o02 E.o02 hcsq.2.1 hcE.2.1, s02] at q2
  rw [octDot_inComplex y.o12 E.o12 hcy.2.2 hcE.2.2, h12, complexPart_octScalar, Complex.ofReal_re, Complex.ofReal_im] at p3
  rw [octDot_inComplex (jordan y y).o12 E.o12 hcsq.2.2 hcE.2.2, s12] at q3
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im] at q1 q2 q3
  obtain ⟨r01, i01⟩ := two_by_two a 0 (a * (y.d0 + y.d1) + (complexPart y.o02).re * b) ((complexPart y.o02).im * b)
    (complexPart E.o01).re (complexPart E.o01).im p1 (by linarith) (by simp [hapos.ne', hbpos.ne', hsigma])
  obtain ⟨r02, i02⟩ := two_by_two (complexPart y.o02).re (complexPart y.o02).im
    ((complexPart y.o02).re * (y.d0 + y.d2) + a * b) ((complexPart y.o02).im * (y.d0 + y.d2))
    (complexPart E.o02).re (complexPart E.o02).im p2 (by linarith)
    (by rw [show (complexPart y.o02).re * ((complexPart y.o02).im * (y.d0 + y.d2)) -
      (complexPart y.o02).im * ((complexPart y.o02).re * (y.d0 + y.d2) + a * b) =
      -((complexPart y.o02).im * (a * b)) by ring]; simp [hsigma, hapos.ne', hbpos.ne'])
  obtain ⟨r12, i12⟩ := two_by_two b 0 (b * (y.d1 + y.d2) + a * (complexPart y.o02).re) (a * (complexPart y.o02).im)
    (complexPart E.o12).re (complexPart E.o12).im p3 (by linarith) (by simp [hapos.ne', hbpos.ne', hsigma])
  have hz0 (w : Octonion) (hw : OctInComplex w) (hr : (complexPart w).re = 0) (hi : (complexPart w).im = 0) : w = 0 :=
    octInComplex_ext w 0 hw ⟨rfl, rfl, rfl⟩ (Complex.ext hr hi)
  exact Albert.ext hE0 hE1 hE2 (hz0 _ hcE.1 r01 i01) (hz0 _ hcE.2.1 r02 i02) (hz0 _ hcE.2.2 r12 i12)

private theorem inner_sector_hiddenAlbert (v : Albert) (hv : InComplexSector v)
    (M : Matrix (Fin 3) (Fin 3) ℂ) : inner v (hiddenAlbert M) = 0 := by
  rw [← complexProjection_eq_self v hv]; exact complex_hidden_orthogonal v M

private theorem gram_and_det_re_eq (z z' : Albert)
    (hS : complexProjection z = complexProjection z')
    (hT : complexProjection (jordan z z) = complexProjection (jordan z' z'))
    (hcub : newtonCubicNorm z = newtonCubicNorm z') :
    sectorColumnGram (hiddenMatrix z) = sectorColumnGram (hiddenMatrix z') ∧
      (hiddenMatrix z).det.re = (hiddenMatrix z').det.re := by
  have hperp (w : Albert) (M : Matrix (Fin 3) (Fin 3) ℂ) :
      complexProjection (jordan (complexProjection w) (hiddenAlbert M)) = 0 :=
    complexProjection_zero_of_perp _ fun v hv => by
      rw [← inner_jordan_associative]
      exact inner_sector_hiddenAlbert _ (complexSector_jordan _ _ ((complexSector_mem_iff v).mp hv)
        ((complexSector_mem_iff _).mp (complexProjection_mem w))) M
  have hsplit_sq (w : Albert) : complexProjection (jordan w w) =
      jordan (complexProjection w) (complexProjection w) +
        complexProjection (jordan (hiddenAlbert (hiddenMatrix w)) (hiddenAlbert (hiddenMatrix w))) := by
    have hs := (complexSector_mem_iff _).mp (complexProjection_mem w)
    conv_lhs => rw [← complex_hidden_decomposition w]
    rw [jordan_add_left, jordan_add_right, jordan_add_right, jordan_comm (hiddenAlbert _),
      complexProjection_add, complexProjection_add, complexProjection_add,
      complexProjection_eq_self _ (complexSector_jordan _ _ hs hs), hperp, add_zero, zero_add]
  have hcore : complexProjection (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z))) =
      complexProjection (jordan (hiddenAlbert (hiddenMatrix z')) (hiddenAlbert (hiddenMatrix z'))) := by
    have e1 := hsplit_sq z; have e2 := hsplit_sq z'; rw [hS, hT] at e1; exact add_left_cancel (e1.symm.trans e2)
  rw [hidden_square_complexProjection, hidden_square_complexProjection] at hcore
  have hherm (w : Albert) : (sectorColumnGram (hiddenMatrix w)).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self _
  have hS0 := congrArg Albert.d0 hcore; have hS1 := congrArg Albert.d1 hcore; have hS2 := congrArg Albert.d2 hcore
  simp only [complexAlbert] at hS0 hS1 hS2
  have hg01 : sectorColumnGram (hiddenMatrix z) 0 1 = sectorColumnGram (hiddenMatrix z') 0 1 :=
    neg_inj.mp (by simpa [complexAlbert] using congrArg (fun x : Albert => complexPart x.o01) hcore)
  have hg02 : sectorColumnGram (hiddenMatrix z) 0 2 = sectorColumnGram (hiddenMatrix z') 0 2 :=
    neg_inj.mp (by simpa [complexAlbert] using congrArg (fun x : Albert => complexPart x.o02) hcore)
  have hg12 : sectorColumnGram (hiddenMatrix z) 1 2 = sectorColumnGram (hiddenMatrix z') 1 2 :=
    neg_inj.mp (by simpa [complexAlbert] using congrArg (fun x : Albert => complexPart x.o12) hcore)
  have hFroD (M : Matrix (Fin 3) (Fin 3) ℂ) :
      (sectorColumnGram M 0 0).re + (sectorColumnGram M 1 1).re + (sectorColumnGram M 2 2).re = sectorFrobeniusSq M := by
    simp [sectorColumnGram, sectorFrobeniusSq, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re]; ring
  have hFro : sectorFrobeniusSq (hiddenMatrix z) = sectorFrobeniusSq (hiddenMatrix z') := by
    linarith [hFroD (hiddenMatrix z), hFroD (hiddenMatrix z')]
  have hdIm (w : Albert) (i : Fin 3) : (sectorColumnGram (hiddenMatrix w) i i).im = 0 := by
    have hi := congrArg Complex.im ((hherm w).apply i i); simp at hi; linarith
  have hGram : sectorColumnGram (hiddenMatrix z) = sectorColumnGram (hiddenMatrix z') := by
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp
    · exact Complex.ext (by linarith) (by rw [hdIm, hdIm])
    · exact hg01
    · exact hg02
    · rw [← (hherm z).apply 1 0, ← (hherm z').apply 1 0, hg01]
    · exact Complex.ext (by linarith) (by rw [hdIm, hdIm])
    · exact hg12
    · rw [← (hherm z).apply 2 0, ← (hherm z').apply 2 0, hg02]
    · rw [← (hherm z).apply 2 1, ← (hherm z').apply 2 1, hg12]
    · exact Complex.ext (by linarith) (by rw [hdIm, hdIm])
  have hcub_split (w : Albert) : newtonCubicNorm w =
      ((trace (complexProjection w)) ^ 3 - 3 * trace (complexProjection w) * trace (complexProjection (jordan w w)) +
        2 * (3 * inner (complexProjection w) (complexProjection (jordan w w)) -
          2 * inner (complexProjection w) (jordan (complexProjection w) (complexProjection w)) +
          6 * (hiddenMatrix w).det.re)) / 6 := by
    set S := complexProjection w; set H := hiddenAlbert (hiddenMatrix w)
    have hdec : S + H = w := complex_hidden_decomposition w
    have hs : InComplexSector S := (complexSector_mem_iff _).mp (complexProjection_mem w)
    have hss := complexSector_jordan _ _ hs hs
    have htr (u : Albert) : trace u = trace (complexProjection u) := by
      conv_lhs => rw [← complex_hidden_decomposition u]
      rw [trace_add, show trace (hiddenAlbert (hiddenMatrix u)) = 0 by simp [hiddenAlbert, trace], add_zero]
    have hc1 : inner S (jordan S H) = 0 := by rw [← inner_jordan_associative]; exact inner_sector_hiddenAlbert _ hss _
    have hc2 : inner H (jordan S S) = 0 := by rw [inner_comm]; exact inner_sector_hiddenAlbert _ hss _
    have hc3 : inner H (jordan S H) = inner S (jordan H H) := by rw [inner_comm H, inner_jordan_associative]
    have hcubeH : inner H (jordan H H) = 6 * (hiddenMatrix w).det.re := by
      have hn := hiddenAlbert_cubicNorm (hiddenMatrix w)
      rw [newtonCubicNorm, show trace H = 0 by simp [H, hiddenAlbert, trace]] at hn
      norm_num at hn; change trace (jordan H (jordan H H)) = _; linarith
    have hsq_exp : jordan (S + H) (S + H) = jordan S S + jordan S H + (jordan S H + jordan H H) := by
      rw [jordan_add_left, jordan_add_right, jordan_add_right, jordan_comm H S]
    have hmix : inner S (jordan w w) = inner S (jordan S S) + inner S (jordan H H) := by
      rw [← hdec, hsq_exp]; simp only [inner_add_right, hc1]; ring
    have hcub3 : trace (jordan w (jordan w w)) = inner S (jordan S S) + 3 * inner S (jordan H H) + 6 * (hiddenMatrix w).det.re := by
      change inner w (jordan w w) = _; conv_lhs => rw [← hdec]
      rw [hsq_exp]; simp only [inner_add_left, inner_add_right, hc1, hc2, hc3, hcubeH]; ring
    rw [newtonCubicNorm, htr w, htr (jordan w w), hcub3, ← inner_sector_complexProjection S (jordan w w) hs, hmix]; ring
  rw [hcub_split z, hcub_split z', hS, hT] at hcub
  exact ⟨hGram, by linarith⟩

private theorem su3_transport_general (M N : Matrix (Fin 3) (Fin 3) ℂ)
    (hG : sectorColumnGram M = sectorColumnGram N)
    (hUnit : IsUnit (sectorColumnGram M).det) (hdet : N.det = M.det) :
    ∃ s : SectorUnitary, (s : SectorMatrix).det = 1 ∧ (s : SectorMatrix) * M = N := by
  let A := (sectorColumnGram M)⁻¹ * M.conjTranspose
  have hAM : A * M = 1 := by dsimp [A]; rw [Matrix.mul_assoc, show M.conjTranspose * M = sectorColumnGram M from rfl, Matrix.nonsing_inv_mul _ hUnit]
  have hMA : M * A = 1 := mul_eq_one_comm.mp hAM
  have hU : (N * A).conjTranspose * (N * A) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc N.conjTranspose N A, ← Matrix.mul_assoc,
      show A.conjTranspose * (N.conjTranspose * N) * A = (M * A).conjTranspose * (M * A) by
        rw [show N.conjTranspose * N = sectorColumnGram N from rfl, ← hG, show sectorColumnGram M = M.conjTranspose * M from rfl]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc],
      hMA, Matrix.conjTranspose_one, Matrix.one_mul]
  exact ⟨⟨N * A, Matrix.mem_unitaryGroup_iff'.mpr hU⟩,
    by change (N * A).det = 1; rw [Matrix.det_mul, hdet, ← Matrix.det_mul, hMA, Matrix.det_one],
    by change N * A * M = N; rw [Matrix.mul_assoc, hAM, Matrix.mul_one]⟩

abbrev led54 (T : Triple) : Ledger54 :=
  (ledger (T 0) (T 1) (T 2), fun i j => inner (T 0 i) (T 1 j),
    fun j k => inner (T 1 j) (T 2 k), fun k i => inner (T 2 k) (T 0 i))

abbrev phiT (T : Triple) : ℝ := phi (encoder (T 0)) (encoder (T 1)) (encoder (T 2))

theorem nearby_core (T S : Triple)
    (hT : ∀ a : Fin 3, Frame (T a)) (hS : ∀ a : Fin 3, Frame (S a))
    (hbox : ∀ i j : Fin 3, |(led54 T).2.1 i j - 1 / 3| < (1 : ℝ) / 50)
    (hL : led54 T = led54 S) (hTne : phiT T ≠ 0) :
    phiT T ^ 2 = phiT S ^ 2 ∧
      (phiT T = phiT S → ∃ k : CompactAutomorphism, (fun a i => k.equiv (S a i)) = T) := by
  obtain ⟨g, g', a, b, hgp, hgp', hqq, hcy, h01, h12, hapos, hbpos, hsig⟩ :=
    nearby_pair_normalization (T 0) (T 1) (S 0) (S 1) (hT 0) (hT 1) (hS 0) (hS 1) hbox
      fun i j => congrArg (fun L : Ledger54 => L.2.1 i j) hL
  set Q := fun i => g'.equiv (S 1 i)
  have hQsame : (fun i => g.equiv (T 1 i)) = Q := funext hqq
  have hQframe : Frame Q := g'.map_frame (S 1) (hS 1)
  have hrTf : Frame (fun k => g.equiv (T 2 k)) := g.map_frame (T 2) (hT 2)
  have hrSf : Frame (fun k => g'.equiv (S 2 k)) := g'.map_frame (S 2) (hS 2)
  have hQsec (j : Fin 3) : InComplexSector (Q j) := (complexSector_mem_iff _).mp (frame_in_complexSector _ hQframe hcy j)
  have hatom (k : Fin 3) : complexProjection (g.equiv (T 2 k)) = complexProjection (g'.equiv (S 2 k)) := by
    set E := complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))
    have hEsec : InComplexSector E := (complexSector_mem_iff _).mp (complexProjection_mem _)
    have hR (i : Fin 3) : inner (flatFrameP i) E = 0 := by
      rw [← inner_sector_complexProjection _ _ (flatFrameP_inComplexSector i), inner_sub_right,
        show inner (flatFrameP i) (g.equiv (T 2 k)) = inner (T 0 i) (T 2 k) by rw [← hgp i]; exact g.inner_map _ _,
        show inner (flatFrameP i) (g'.equiv (S 2 k)) = inner (S 0 i) (S 2 k) by rw [← hgp' i]; exact g'.inner_map _ _,
        inner_comm (T 0 i), inner_comm (S 0 i),
        show inner (T 2 k) (T 0 i) = inner (S 2 k) (S 0 i) from congrArg (fun L : Ledger54 => L.2.2.2 k i) hL, sub_self]
    have hE0 : E.d0 = 0 := (inner_flatFrameP E).2.2 ▸ hR 2
    have hE1 : E.d1 = 0 := (inner_flatFrameP E).2.1 ▸ hR 1
    have hE2 : E.d2 = 0 := (inner_flatFrameP E).1 ▸ hR 0
    have hCE (i j : Fin 3) : inner (jordan (flatFrameP i) (Q j)) E = 0 := by
      rw [← inner_sector_complexProjection _ _ (complexSector_jordan _ _ (flatFrameP_inComplexSector i) (hQsec j)), inner_sub_right,
        show inner (jordan (flatFrameP i) (Q j)) (g.equiv (T 2 k)) = (led54 T).1 i j k by
          rw [← hQsame, ← hgp i]; show inner (jordan (g.equiv _) (g.equiv _)) _ = _; rw [← g.map_jordan, g.inner_map]; rfl,
        show inner (jordan (flatFrameP i) (Q j)) (g'.equiv (S 2 k)) = (led54 S).1 i j k by
          rw [← hgp' i]; show inner (jordan (g'.equiv _) (g'.equiv _)) _ = _; rw [← g'.map_jordan, g'.inner_map]; rfl,
        hL, sub_self]
    obtain ⟨p1, p2, p3⟩ := slot_pairings_zero (encoder Q) E hE0 hE1 hE2 fun i => by
      show inner (jordan _ (Q 2 - Q 0)) E = 0; rw [jordan_sub_right, inner_sub_left, hCE, hCE, sub_self]
    obtain ⟨q1, q2, q3⟩ := slot_pairings_zero (jordan (encoder Q) (encoder Q)) E hE0 hE1 hE2 fun i => by
      rw [frame_encoder_square _ hQframe, jordan_add_right, inner_add_left, hCE, hCE, add_zero]
    exact sub_eq_zero.mp (complexProjection_sub _ _ ▸
      sector_slot_recovery (encoder Q) E a b hcy hEsec h01 h12 hapos hbpos hsig hE0 hE1 hE2 p1 p2 p3 q1 q2 q3)
  set zT := encoder fun k => g.equiv (T 2 k)
  set zS := encoder fun k => g'.equiv (S 2 k)
  have hSigma : complexProjection zT = complexProjection zS := by
    show complexProjection (g.equiv (T 2 2) - g.equiv (T 2 0)) = complexProjection (g'.equiv (S 2 2) - g'.equiv (S 2 0))
    rw [complexProjection_sub, complexProjection_sub, hatom 2, hatom 0]
  have hTheta : complexProjection (jordan zT zT) = complexProjection (jordan zS zS) := by
    rw [frame_encoder_square _ hrTf, frame_encoder_square _ hrSf, complexProjection_add, complexProjection_add, hatom 2, hatom 0]
  obtain ⟨hGram, hdetre⟩ := gram_and_det_re_eq zT zS hSigma hTheta
    (by rw [frame_encoder_cubicNorm _ hrTf, frame_encoder_cubicNorm _ hrSf])
  have hdetim := im_sq_eq_of_normSq_eq _ _ (by
    rw [normSq_det_eq_gram_det_re, normSq_det_eq_gram_det_re]; exact congrArg (fun G => G.det.re) hGram) hdetre
  have hphi_norm (X : Triple) (m : CompactAutomorphism)
      (h0 : ∀ i, m.equiv (X 0 i) = flatFrameP i) (h1 : (fun i => m.equiv (X 1 i)) = Q) :
      phiT X = 4 * a * b * (complexPart (encoder Q).o02).im *
        (hiddenMatrix (encoder fun k => m.equiv (X 2 k))).det.im := by
    dsimp only [phiT]
    rw [← m.phi_map, ← m.encoder_map (X 0), ← m.encoder_map (X 1), ← m.encoder_map (X 2),
      congrArg encoder (funext h0), flatFrameP_encoder, h1,
      phi_of_diagonal_complex flatXN (encoder Q) _ ⟨rfl, rfl, rfl⟩ hcy,
      h01, h12, complexPart_octScalar, complexPart_octScalar, (real_real_conj a b _).2]
    dsimp [flatXN]; ring
  have hphiT := hphi_norm T g hgp hQsame
  have hphiS := hphi_norm S g' hgp' rfl
  refine ⟨by rw [hphiT, hphiS, mul_pow, hdetim, ← mul_pow], fun hsame => ?_⟩
  rw [hphiT, hphiS] at hsame
  have hdeteq : (hiddenMatrix zT).det = (hiddenMatrix zS).det :=
    Complex.ext hdetre (mul_left_cancel₀ (by simp [hapos.ne', hbpos.ne', hsig]) hsame)
  have hdetne : (hiddenMatrix zT).det ≠ 0 := fun hz => hTne (by rw [hphiT, hz]; simp)
  have hUnit : IsUnit (sectorColumnGram (hiddenMatrix zT)).det := isUnit_iff_ne_zero.mpr fun hz =>
    hdetne (Complex.normSq_eq_zero.mp (by rw [normSq_det_eq_gram_det_re]; change (sectorColumnGram _).det.re = 0; rw [hz]; rfl))
  obtain ⟨s, hs, hsM⟩ := su3_transport_general _ _ hGram hUnit hdeteq.symm
  have hatoms : ∀ k, (sectorLeftSU3Automorphism s hs).equiv (g.equiv (T 2 k)) = g'.equiv (S 2 k) :=
    frame_eq_of_encoder_eq _ _ hrTf hrSf (sectorLeftSU3Automorphism s hs)
      (by change complexProjection zT + hiddenAlbert ((s : SectorMatrix) * hiddenMatrix zT) = zS
          rw [hsM, hSigma, complex_hidden_decomposition])
  let K := g'.symm.comp ((sectorLeftSU3Automorphism s hs).comp g)
  have hKT (c i : Fin 3) : K.equiv (T c i) = S c i := by
    show g'.equiv.symm ((sectorLeftSU3Automorphism s hs).equiv (g.equiv (T c i))) = S c i
    fin_cases c <;> dsimp
    · rw [hgp i, sectorLeftSU3_fixes_complex s hs _ (flatFrameP_inComplexSector i), ← hgp' i, g'.equiv.symm_apply_apply]
    · rw [hqq i, sectorLeftSU3_fixes_complex s hs _ (hQsec i), g'.equiv.symm_apply_apply]
    · rw [hatoms i, g'.equiv.symm_apply_apply]
  exact ⟨K.symm, funext fun c => funext fun i => by show K.equiv.symm (S c i) = T c i; rw [← hKT c i, K.equiv.symm_apply_apply]⟩

end

section Rank20
open Glennie.Compact.FlowFamily Glennie.Compact.NativeDictionary Glennie.Compact.NativeWordTableR01
open scoped BigOperators Matrix

private def phiP : Z3 →+* ZMod 13 := Zsqrtd.lift ⟨4, by decide⟩

private def extDecodeG {R : Type*} [CommRing R] (a : Fin 27 → R) : AlbertG R :=
  let b (i : Fin 26) : R := a i.succ
  addG (smulG (a 0) unitG)
    ⟨b 0 + b 1, -b 0 + b 1, -2 * b 1,
      (⟨b 2, b 3, -b 12, -b 13⟩, ⟨-b 18, -b 19, -b 24, b 25⟩),
      (⟨b 4, b 5, b 10, b 11⟩, ⟨b 16, b 17, b 22, -b 23⟩),
      (⟨b 6, b 7, -b 8, -b 9⟩, ⟨-b 14, -b 15, -b 20, b 21⟩)⟩

private def extUnitG {R : Type*} [CommRing R] (m k : Fin 27) : R := cond (k.1 == m.1) 1 0

private def dir4G {R : Type*} [CommRing R] (n : Fin 20) (x : AlbertG R) : AlbertG R :=
  let t := extDecodeG (extUnitG (R := R) 1)
  let b := extDecodeG (extUnitG (R := R) (partnerIndex n))
  subG (jordan2G t (jordan2G b x)) (jordan2G b (jordan2G t x))

private def jacEntryG {R : Type*} [CommRing R] (s3 : R) (r n : Fin 20) : R :=
  let idx := rowIndex r
  if contextIndex n = 0 then
    innerG (dir4G n (flatTriple36 s3 0 idx.1)) (jordan2G (flatTriple36 s3 1 idx.2.1) (flatTriple36 s3 2 idx.2.2))
  else
    innerG (dir4G n (flatTriple36 s3 1 idx.2.1)) (jordan2G (flatTriple36 s3 0 idx.1) (flatTriple36 s3 2 idx.2.2))

private theorem map_jacEntryG {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s3 : R) (r n : Fin 20) :
    f (jacEntryG s3 r n) = jacEntryG (f s3) r n := by
  have hext (a : Fin 27 → R) : mapAG f (extDecodeG a) = extDecodeG (f ∘ a) := by
    ext <;> simp [extDecodeG, mapAG, mapOG, mapQG, addG, smulG, unitG, oAdd, oSmul, oZero, qAdd, qSmul, qZero, map_ofNat]
  have hunit (m : Fin 27) : f ∘ extUnitG m = extUnitG m := by funext k; dsimp [extUnitG]; cases k.1 == m.1 <;> simp
  have hd (x : AlbertG R) : mapAG f (dir4G n x) = dir4G n (mapAG f x) := by
    simp only [dir4G, mapAG_sub, mapAG_jordan2, hext, hunit]
  unfold jacEntryG; split_ifs <;> simp only [mapAG_inner, hd, mapAG_jordan2, mapAG_flatTriple36]

private def qrFast : List (List (AlbertG ℤ)) :=
  (List.finRange 3).map fun j => (List.finRange 3).map fun l => jordan2G (flatTriple36 (4 : ℤ) 1 j) (flatTriple36 (4 : ℤ) 2 l)
private def prFast : List (List (AlbertG ℤ)) :=
  (List.finRange 3).map fun i => (List.finRange 3).map fun l => jordan2G (flatTriple36 (4 : ℤ) 0 i) (flatTriple36 (4 : ℤ) 2 l)
private def dirFast : List (List (AlbertG ℤ)) :=
  (List.finRange 20).map fun n => (List.finRange 3).map fun i => dir4G n (flatTriple36 (4 : ℤ) (contextIndex n) i)

private def jacFast (r n : Fin 20) : ℤ :=
  let idx := rowIndex r
  if contextIndex n = 0 then
    innerG ((dirFast.getD n.1 []).getD idx.1.1 zeroG) ((qrFast.getD idx.2.1.1 []).getD idx.2.2.1 zeroG)
  else
    innerG ((dirFast.getD n.1 []).getD idx.2.1.1 zeroG) ((prFast.getD idx.1.1 []).getD idx.2.2.1 zeroG)

private instance : Fact (1 < 13) := ⟨by decide⟩

private def jacMatZ3 : Matrix (Fin 20) (Fin 20) Z3 := Matrix.of (jacEntryG Zsqrtd.sqrtd)

private theorem det_jacMatZ3_ne_zero : jacMatZ3.det ≠ 0 := by
  refine det_ne_zero_of_checkMatInvInt phiP jacMatZ3 jacFast (fun r n => ?_) (by decide +kernel)
  have hctx : contextIndex n = 0 ∨ contextIndex n = 1 := by fin_cases n <;> first | exact Or.inl rfl | exact Or.inr rfl
  have hfast : jacFast r n = jacEntryG (4 : ℤ) r n := by
    rcases hctx with hc | hc <;> simp [jacFast, jacEntryG, hc, dirFast, qrFast, prFast, List.getD_eq_getElem?_getD,
      n.2, (rowIndex r).1.2, (rowIndex r).2.1.2, (rowIndex r).2.2.2]
  rw [jacMatZ3, Matrix.of_apply, hfast]
  have h1 := map_jacEntryG phiP Zsqrtd.sqrtd r n
  rw [show phiP Zsqrtd.sqrtd = 4 by simp [phiP]] at h1
  exact h1.trans (map_jacEntryG (Int.castRingHom (ZMod 13)) (4 : ℤ) r n).symm

noncomputable section

theorem native_rank20_strict_with_inverse :
    ∃ e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ),
      (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR] := by
  have hext (m : Fin 27) : toRealAlbert (extDecodeG (extUnitG m)) = extDecode (extUnit m) := by
    rw [show (extUnitG m : Fin 27 → ℝ) = extUnit m by
      funext k; by_cases h : k = m
      · subst h; simp [extUnitG, extUnit]
      · simp [extUnitG, extUnit, h, beq_false_of_ne (Fin.val_ne_of_ne h)]]
    ext <;> rfl
  have hdir (k : Fin 20) (x : AlbertG ℝ) : toRealAlbert (dir4G k x) = (4 : ℝ) • direction k (toRealAlbert x) := by
    simp only [dir4G, direction, Glennie.Compact.innerDerLinear_apply, Glennie.Compact.innerDer,
      toRealAlbert_sub, toRealAlbert_jordan2, hext, jordan_smul_right, smul_sub, smul_smul]; norm_num
  have hj0 (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20) (h : contextIndex n = 0) :
      jacobianEntry T r n = Glennie.inner (direction n (T 0 (rowIndex r).1)) (jordan (T 1 (rowIndex r).2.1) (T 2 (rowIndex r).2.2)) := by
    simp only [jacobianEntry, atomTangent, h, (by decide : (1 : Fin 3) ≠ 0), (by decide : (2 : Fin 3) ≠ 0),
      ↓reduceIte, jordan_zero_left, jordan_zero_right, add_zero]
    exact inner_jordan_associative _ _ _
  have hj1 (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20) (h : contextIndex n = 1) :
      jacobianEntry T r n = Glennie.inner (direction n (T 1 (rowIndex r).2.1)) (jordan (T 0 (rowIndex r).1) (T 2 (rowIndex r).2.2)) := by
    simp only [jacobianEntry, atomTangent, h, (by decide : (0 : Fin 3) ≠ 1), (by decide : (2 : Fin 3) ≠ 1),
      ↓reduceIte, jordan_zero_left, jordan_zero_right, add_zero, zero_add]
    rw [jordan_comm (T 0 _)]; exact inner_jordan_associative _ _ _
  have hreal (r n : Fin 20) : jacEntryG (Real.sqrt 3) r n = 373248 * jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r n := by
    have hctx : contextIndex n = 0 ∨ contextIndex n = 1 := by fin_cases n <;> first | exact Or.inl rfl | exact Or.inr rfl
    rcases hctx with hc0 | hc1
    · rw [hj0 _ r n hc0]; simp only [jacEntryG, hc0, ↓reduceIte, toRealAlbert_inner, hdir, toRealAlbert_jordan2,
        toRealAlbert_flatTriple36, map_smul, jordan_smul_left, jordan_smul_right, Glennie.inner_smul_left, Glennie.inner_smul_right, smul_smul]; ring
    · rw [hj1 _ r n hc1]; simp only [jacEntryG, show contextIndex n ≠ 0 by rw [hc1]; decide, ↓reduceIte, toRealAlbert_inner, hdir, toRealAlbert_jordan2,
        toRealAlbert_flatTriple36, map_smul, jordan_smul_left, jordan_smul_right, Glennie.inner_smul_left, Glennie.inner_smul_right, smul_smul]; ring
  have hmat : Matrix.of (jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR]) = (373248 : ℝ)⁻¹ • jacMatZ3.map liftR := by
    ext r n; have hm := map_jacEntryG liftR Zsqrtd.sqrtd r n
    rw [show liftR Zsqrtd.sqrtd = Real.sqrt 3 by simp [liftR], hreal] at hm
    simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, jacMatZ3, hm, smul_eq_mul]; ring
  have hdetM : (Matrix.of (jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR])).det ≠ 0 := by
    rw [hmat, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) fun h => det_jacMatZ3_ne_zero (liftR_injective (h.trans (map_zero liftR).symm))
  have htoM : LinearMap.toMatrix' (rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR] : (Fin 20 → ℝ) →ₗ[ℝ] (Fin 20 → ℝ)) =
      Matrix.of (jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR]) := by
    ext r n; rw [LinearMap.toMatrix'_apply, Matrix.of_apply, ContinuousLinearMap.coe_coe, rowLedgerDeriv_single]
  have hdet : (rowLedgerDeriv ![flatFrameP, flatFrameQ, flatFrameR]).det ≠ 0 :=
    fun h0 => hdetM (by rwa [← htoM, LinearMap.det_toMatrix'])
  exact ⟨(rowLedgerDeriv _).toContinuousLinearEquivOfDetNeZero hdet,
    (rowLedgerDeriv _).coe_toContinuousLinearEquivOfDetNeZero hdet⟩

end
end Rank20
end Glennie.Compact.PairNormNearby
