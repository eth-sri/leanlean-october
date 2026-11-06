module
public import Glennie.Compact.NativeFlatSections
public import Glennie.Compact.FlatOrbit
public import Glennie.Compact.LocalContrast
public import Glennie.Compact.NativeQFamilyLedger
public import Glennie.Native.OrderedPositivePair
public import Glennie.Native.SectorLeftAction
public import Glennie.UnitShifts

@[expose] public section
namespace Glennie.Compact.NearbyOrbits
open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FrameTopology Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections
noncomputable section
set_option autoImplicit false

theorem ledger54_eq_decode20 {T : Triple} (hT : ∀ a : Fin 3, Glennie.Frame (T a))
    {b : Fin 20 → ℝ} (hb : encode20 (ledger54 T) = b) :
    ledger54 T = decode20 b := by
  subst hb; exact (decode_encode_frames T hT).symm

def fibre54 (b : Fin 20 → ℝ) : Set Triple :=
  {T : Triple | (∀ a : Fin 3, Glennie.Frame (T a)) ∧ ledger54 T = decode20 b}

def fibre20 (b : Fin 20 → ℝ) : Set Triple :=
  {T : Triple | (∀ a : Fin 3, Glennie.Frame (T a)) ∧ encode20 (ledger54 T) = b}

theorem fibre20_subset_fibre54 (b : Fin 20 → ℝ) : fibre20 b ⊆ fibre54 b :=
  fun _ ⟨hT, hb⟩ => ⟨hT, ledger54_eq_decode20 hT hb⟩

theorem fibre54_subset_fibre20 {b : Fin 20 → ℝ} {S : Triple}
    (hS : S ∈ fibre54 b) (hSb : encode20 (ledger54 S) = b) :
    fibre54 b ⊆ fibre20 b :=
  fun _ ⟨hT, hTb⟩ => ⟨hT, by rw [hTb, ← hS.2, hSb]⟩

theorem phiOf_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple) :
    phiOf (mapAtoms g T) = phiOf T := phi_mapAtoms g T

theorem phiOf_eq_of_mem_autOrbit {S T : Triple} (h : T ∈ autOrbit S) :
    phiOf T = phiOf S := phi_eq_of_mem_autOrbit h

end
end Glennie.Compact.NearbyOrbits

namespace Glennie.Compact.NearbyOrbitsClosed
open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FrameTopology Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections Glennie.Compact.NearbyOrbits
open Glennie.Compact.NativeQFamilyLedger Glennie.Compact.LocalContrast
open Glennie.NativeOrderedPositivePair

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem nonneg_sq_eq_of_sq_eq (a a' : ℝ) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (h : a ^ 2 = a' ^ 2) : a = a' := by nlinarith

theorem half_lt_of_sq (a : ℝ) (ha : 0 ≤ a) (h : 1 / 4 < a ^ 2) : 1 / 2 < a := by nlinarith

theorem ne_zero_of_sq_eq_of_ne_zero (x x' : ℝ) (h : x ^ 2 = x' ^ 2) (hx : x ≠ 0) : x' ≠ 0 :=
  fun hz => hx (by nlinarith)

theorem mul_lt_mul_nonneg (x bx y by' : ℝ)
    (hx0 : 0 ≤ x) (hx : x < bx) (hy0 : 0 ≤ y) (hy : y < by') : x * y < bx * by' := by nlinarith

theorem abs_prod_lt (x y bx by' : ℝ) (hx : |x| < bx) (hy : |y| < by') :
    |x * y| < bx * by' := by
  rw [abs_mul]; exact mul_lt_mul_nonneg |x| bx |y| by' (abs_nonneg x) hx (abs_nonneg y) hy

theorem abs_prod_nonneg_lt (x y bx by' : ℝ) (hx : |x| < bx) (hy0 : 0 ≤ y) (hy : y < by') :
    |x * y| < bx * by' := by
  rw [abs_mul, abs_of_nonneg hy0]; exact mul_lt_mul_nonneg |x| bx y by' (abs_nonneg x) hx hy0 hy

theorem mul_sq_eq_of_sq_eq (K X Y : ℝ) (h : X ^ 2 = Y ^ 2) : (K * X) ^ 2 = (K * Y) ^ 2 := by
  linear_combination K ^ 2 * h

theorem im_sq_eq_of_normSq_eq (z w : ℂ) (hn : Complex.normSq z = Complex.normSq w)
    (hr : z.re = w.re) : z.im ^ 2 = w.im ^ 2 := by
  rw [Complex.normSq_apply, Complex.normSq_apply, hr] at hn; linear_combination hn

theorem two_by_two (A B C D X Y : ℝ)
    (h1 : A * X + B * Y = 0) (h2 : C * X + D * Y = 0)
    (hdet : A * D - B * C ≠ 0) : X = 0 ∧ Y = 0 :=
  ⟨mul_left_cancel₀ hdet (by linear_combination D * h1 - B * h2),
   mul_left_cancel₀ hdet (by linear_combination A * h2 - C * h1)⟩

theorem normSq_det_eq_gram_det_re (M : Matrix (Fin 3) (Fin 3) ℂ) :
    Complex.normSq M.det = (M.conjTranspose * M).det.re := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose]
  simp [Complex.mul_re, Complex.normSq_apply]

theorem nondegenerate_core (a b D0 D1 D2 e0 e1 e2 v R Sg : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hD0 : |D0| < 1 / 25) (hD1 : |D1| < 1 / 25) (hD2 : |D2| < 1 / 25)
    (he0 : |e0 - 2 / 3| < 1 / 25) (he1 : |e1 - 2 / 3| < 1 / 25) (he2 : |e2 - 2 / 3| < 1 / 25)
    (hv0 : 0 ≤ v)
    (E0 : e0 = D0 ^ 2 + a ^ 2 + v)
    (E1 : e1 = D1 ^ 2 + a ^ 2 + b ^ 2)
    (E2 : e2 = D2 ^ 2 + v + b ^ 2)
    (C : 0 = D0 * D1 * D2 - D0 * b ^ 2 - D1 * v - D2 * a ^ 2 + 2 * (a * b * R))
    (hsplit : v = R ^ 2 + Sg ^ 2) :
    1 / 2 < a ∧ 1 / 2 < b ∧ Sg ≠ 0 := by
  obtain ⟨l0, r0⟩ := abs_lt.mp hD0; obtain ⟨l1, r1⟩ := abs_lt.mp hD1; obtain ⟨l2, r2⟩ := abs_lt.mp hD2
  obtain ⟨m0, n0⟩ := abs_lt.mp he0; obtain ⟨m1, n1⟩ := abs_lt.mp he1; obtain ⟨m2, n2⟩ := abs_lt.mp he2
  have q0 : D0 ^ 2 < (1 / 25 : ℝ) ^ 2 := sq_lt_sq' l0 r0
  have q1 : D1 ^ 2 < (1 / 25 : ℝ) ^ 2 := sq_lt_sq' l1 r1
  have q2 : D2 ^ 2 < (1 / 25 : ℝ) ^ 2 := sq_lt_sq' l2 r2
  have p0 := sq_nonneg D0; have p1 := sq_nonneg D1; have p2 := sq_nonneg D2
  have hasq : (1 : ℝ) / 4 < a ^ 2 := by linarith
  have hasq' : a ^ 2 < (1 : ℝ) / 2 := by linarith
  have hbsq : (1 : ℝ) / 4 < b ^ 2 := by linarith
  have hbsq' : b ^ 2 < (1 : ℝ) / 2 := by linarith
  have hvlb : (1 : ℝ) / 4 < v := by linarith
  have hvub : v < (1 : ℝ) / 2 := by linarith
  have halt := half_lt_of_sq a ha hasq
  have hblt := half_lt_of_sq b hb hbsq
  refine ⟨halt, hblt, ?_⟩
  have hab : (1 : ℝ) / 4 < a * b := by
    linarith [mul_lt_mul_nonneg (1 / 2) a (1 / 2) b (by norm_num) halt (by norm_num) hblt]
  obtain ⟨u1, u2⟩ := abs_lt.mp (abs_prod_nonneg_lt D0 (b ^ 2) (1 / 25) (1 / 2) hD0 (sq_nonneg b) hbsq')
  obtain ⟨w1, w2⟩ := abs_lt.mp (abs_prod_nonneg_lt D1 v (1 / 25) (1 / 2) hD1 hv0 hvub)
  obtain ⟨x1, x2⟩ := abs_lt.mp (abs_prod_nonneg_lt D2 (a ^ 2) (1 / 25) (1 / 2) hD2 (sq_nonneg a) hasq')
  obtain ⟨z1, z2⟩ := abs_lt.mp (abs_prod_lt (D0 * D1) D2 ((1 / 25) * (1 / 25)) (1 / 25)
    (abs_prod_lt D0 D1 (1 / 25) (1 / 25) hD0 hD1) hD2)
  have hABsq : (1 : ℝ) / 16 < (a * b) ^ 2 := by
    have h := mul_lt_mul_nonneg (1 / 4) (a * b) (1 / 4) (a * b) (by norm_num) hab (by norm_num) hab
    linarith [show (a * b) * (a * b) = (a * b) ^ 2 by ring]
  have hb2 : (a * b * R) ^ 2 < ((1 : ℝ) / 16) ^ 2 := sq_lt_sq' (by linarith) (by linarith)
  have hkey : R ^ 2 * (1 / 16) ≤ (a * b * R) ^ 2 := by
    calc R ^ 2 * (1 / 16) ≤ R ^ 2 * (a * b) ^ 2 := mul_le_mul_of_nonneg_left hABsq.le (sq_nonneg R)
      _ = (a * b * R) ^ 2 := by ring
  have hSg : (0 : ℝ) < Sg ^ 2 := by linarith
  rintro rfl; norm_num at hSg

theorem octConj_zero : octConj (0 : Octonion) = 0 := by apply Prod.ext <;> simp [octConj]
theorem octMul_zero_left (y : Octonion) : octMul 0 y = 0 := by apply Prod.ext <;> simp [octMul]
theorem octMul_zero_right (x : Octonion) : octMul x 0 = 0 := by apply Prod.ext <;> simp [octMul]

theorem frame_as_projector (p : Fin 3 → Albert) (hp : Frame p) :
    p = projectorFrame (encoder p) := by
  funext i; fin_cases i
  · exact (frame_projector_first p hp).symm
  · exact (frame_projector_middle p hp).symm
  · exact (frame_projector_last p hp).symm

theorem frame_eq_of_encoder_eq (q s : Fin 3 → Albert) (hq : Frame q) (hs : Frame s)
    (m : CompactAutomorphism) (hEnc : m.equiv (encoder q) = encoder s) (i : Fin 3) :
    m.equiv (q i) = s i := by
  rw [congrFun (frame_as_projector q hq) i, compactAutomorphism_projectorFrame, hEnc,
    ← congrFun (frame_as_projector s hs) i]

theorem jordan_flatXN : jordan flatXN flatXN = diagonalAlbert 1 0 1 := by
  ext <;> simp [flatXN, diagonalAlbert, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octNormSq, Quaternion.normSq_def',
    octConj_zero, octMul_zero_right]

theorem inner_diagonalAlbert (a b c : ℝ) (x : Albert) :
    inner (diagonalAlbert a b c) x = a * x.d0 + b * x.d1 + c * x.d2 := by
  simp [inner_coordinates, diagonalAlbert, octDot_coordinates]

theorem flatFrameP_zero_eq : flatFrameP 0 = diagonalAlbert 0 0 1 := by
  change (1 / 2 : ℝ) • (jordan flatXN flatXN - flatXN) = _; rw [jordan_flatXN]
  ext <;> (simp [diagonalAlbert, flatXN]; try norm_num)

theorem flatFrameP_one_eq : flatFrameP 1 = diagonalAlbert 0 1 0 := by
  change (1 : Albert) - jordan flatXN flatXN = _; rw [jordan_flatXN]
  ext <;> simp [diagonalAlbert]

theorem flatFrameP_two_eq : flatFrameP 2 = diagonalAlbert 1 0 0 := by
  change (1 / 2 : ℝ) • (jordan flatXN flatXN + flatXN) = _; rw [jordan_flatXN]
  ext <;> (simp [diagonalAlbert, flatXN]; try norm_num)

theorem inner_flatFrameP_zero (x : Albert) : inner (flatFrameP 0) x = x.d2 := by
  rw [flatFrameP_zero_eq, inner_diagonalAlbert]; ring
theorem inner_flatFrameP_one (x : Albert) : inner (flatFrameP 1) x = x.d1 := by
  rw [flatFrameP_one_eq, inner_diagonalAlbert]; ring
theorem inner_flatFrameP_two (x : Albert) : inner (flatFrameP 2) x = x.d0 := by
  rw [flatFrameP_two_eq, inner_diagonalAlbert]; ring

theorem flatFrameP_isDiagonal (i : Fin 3) : IsDiagonal (flatFrameP i) :=
  frame_projectors_diagonal flatFrameP flatFrameP_frame
    (by rw [flatFrameP_encoder]; simp [IsDiagonal, flatXN]) i

theorem flatFrameP_inComplexSector (i : Fin 3) : InComplexSector (flatFrameP i) :=
  diagonal_inComplex _ (flatFrameP_isDiagonal i)

theorem normalised_diag_data (q : Fin 3 → Albert) (hq : Frame q) (P : Fin 3 → Fin 3 → ℝ)
    (hPQ : ∀ i j : Fin 3, inner (flatFrameP i) (q j) = P i j) :
    (encoder q).d0 = P 2 2 - P 2 0 ∧ (encoder q).d1 = P 1 2 - P 1 0 ∧
      (encoder q).d2 = P 0 2 - P 0 0 ∧
      (jordan (encoder q) (encoder q)).d0 = P 2 2 + P 2 0 ∧
      (jordan (encoder q) (encoder q)).d1 = P 1 2 + P 1 0 ∧
      (jordan (encoder q) (encoder q)).d2 = P 0 2 + P 0 0 := by
  rw [frame_encoder_square q hq]
  simp only [encoder, Albert.sub_d0, Albert.sub_d1, Albert.sub_d2,
    Albert.add_d0, Albert.add_d1, Albert.add_d2]
  simp only [← inner_flatFrameP_two, ← inner_flatFrameP_one, ← inner_flatFrameP_zero, hPQ,
    and_self]

theorem fe_complex_square_o01 (d e f : ℝ) (u v w : ℂ) :
    complexPart (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).o01 =
      u * (d + e) + v * star w := by
  apply Complex.ext <;> simp [jordan_o01, complexAlbert, complexOct, complexPart, octMul, octConj,
    Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

theorem fe_complex_square_o02 (d e f : ℝ) (u v w : ℂ) :
    complexPart (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).o02 =
      v * (d + f) + u * w := by
  apply Complex.ext <;> simp [jordan_o02, complexAlbert, complexOct, complexPart, octMul,
    Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

theorem fe_complex_square_o12 (d e f : ℝ) (u v w : ℂ) :
    complexPart (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).o12 =
      w * (e + f) + star u * v := by
  apply Complex.ext <;> simp [jordan_o12, complexAlbert, complexOct, complexPart, octMul, octConj,
    Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

theorem complexPart_complexAlbert_o01 (a b c : ℝ) (u v w : ℂ) :
    complexPart (complexAlbert a b c u v w).o01 = u := by apply Complex.ext <;> rfl
theorem complexPart_complexAlbert_o02 (a b c : ℝ) (u v w : ℂ) :
    complexPart (complexAlbert a b c u v w).o02 = v := by apply Complex.ext <;> rfl
theorem complexPart_complexAlbert_o12 (a b c : ℝ) (u v w : ℂ) :
    complexPart (complexAlbert a b c u v w).o12 = w := by apply Complex.ext <;> rfl

theorem complexPart_octScalar (a : ℝ) : complexPart (octScalar a) = (a : ℂ) := rfl

theorem normSq_complexPart_octScalar (a : ℝ) :
    Complex.normSq (complexPart (octScalar a)) = a ^ 2 := by
  rw [complexPart_octScalar, Complex.normSq_ofReal]; ring

theorem octInComplex_ext (x x' : Octonion) (hx : OctInComplex x) (hx' : OctInComplex x')
    (h : complexPart x = complexPart x') : x = x' :=
  Prod.ext (Quaternion.ext x.1 x'.1 (congrArg Complex.re h) (congrArg Complex.im h)
    (hx.1.trans hx'.1.symm) (hx.2.1.trans hx'.2.1.symm)) (hx.2.2.trans hx'.2.2.symm)

theorem octInComplex_eq_zero (x : Octonion) (hx : OctInComplex x)
    (hre : (complexPart x).re = 0) (him : (complexPart x).im = 0) : x = 0 :=
  octInComplex_ext x 0 hx ⟨rfl, rfl, rfl⟩ (Complex.ext hre him)

theorem octInComplex_decomp (x : Octonion) (hx : OctInComplex x) :
    x = octScalar (complexPart x).re + (complexPart x).im • octI := by
  obtain ⟨hj, hk, hz⟩ := hx
  apply Prod.ext
  · apply Quaternion.ext <;> simp [octScalar, octI, quatI, complexPart, hj, hk]
  · simp [octScalar, octI, quatI, hz]

theorem octDot_inComplex (x x' : Octonion) (hx : OctInComplex x) (hx' : OctInComplex x') :
    octDot x x' = (complexPart x).re * (complexPart x').re +
      (complexPart x).im * (complexPart x').im := by
  obtain ⟨hj, hk, hz⟩ := hx; obtain ⟨hj', hk', hz'⟩ := hx'
  simp [octDot_coordinates, complexPart, hj, hk, hz, hj', hk', hz']

theorem real_real_conj_re (a b : ℝ) (z : ℂ) :
    ((a : ℂ) * (b : ℂ) * star z).re = a * b * z.re := by
  simp [Complex.mul_re, Complex.mul_im]

theorem real_real_conj_im (a b : ℝ) (z : ℂ) :
    ((a : ℂ) * (b : ℂ) * star z).im = -(a * b * z.im) := by
  simp [Complex.mul_re, Complex.mul_im]

theorem slot_data_eq_of_diag_eq (y y' : Albert)
    (hc : InComplexSector y) (hc' : InComplexSector y')
    (hd0 : y.d0 = y'.d0) (hd1 : y.d1 = y'.d1) (hd2 : y.d2 = y'.d2)
    (hs0 : (jordan y y).d0 = (jordan y' y').d0)
    (hs1 : (jordan y y).d1 = (jordan y' y').d1)
    (hs2 : (jordan y y).d2 = (jordan y' y').d2)
    (hcub : newtonCubicNorm y = newtonCubicNorm y') :
    Complex.normSq (complexPart y.o01) = Complex.normSq (complexPart y'.o01) ∧
      Complex.normSq (complexPart y.o02) = Complex.normSq (complexPart y'.o02) ∧
      Complex.normSq (complexPart y.o12) = Complex.normSq (complexPart y'.o12) ∧
      (complexPart y.o01 * complexPart y.o12 * star (complexPart y.o02)).re =
        (complexPart y'.o01 * complexPart y'.o12 * star (complexPart y'.o02)).re := by
  have E0 := fe_complex_square_d0 y.d0 y.d1 y.d2 (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have E1 := fe_complex_square_d1 y.d0 y.d1 y.d2 (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have E2 := fe_complex_square_d2 y.d0 y.d1 y.d2 (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have C := fe_complex_cubic y.d0 y.d1 y.d2 (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have E0' := fe_complex_square_d0 y'.d0 y'.d1 y'.d2 (complexPart y'.o01) (complexPart y'.o02) (complexPart y'.o12)
  have E1' := fe_complex_square_d1 y'.d0 y'.d1 y'.d2 (complexPart y'.o01) (complexPart y'.o02) (complexPart y'.o12)
  have E2' := fe_complex_square_d2 y'.d0 y'.d1 y'.d2 (complexPart y'.o01) (complexPart y'.o02) (complexPart y'.o12)
  have C' := fe_complex_cubic y'.d0 y'.d1 y'.d2 (complexPart y'.o01) (complexPart y'.o02) (complexPart y'.o12)
  rw [complexAlbert_eq y hc] at E0 E1 E2 C
  rw [complexAlbert_eq y' hc'] at E0' E1' E2' C'
  rw [hd0, hs0] at E0; rw [hd1, hs1] at E1; rw [hd2, hs2] at E2
  rw [hd0, hd1, hd2, hcub] at C
  have h01 : Complex.normSq (complexPart y.o01) = Complex.normSq (complexPart y'.o01) := by linarith
  have h02 : Complex.normSq (complexPart y.o02) = Complex.normSq (complexPart y'.o02) := by linarith
  have h12 : Complex.normSq (complexPart y.o12) = Complex.normSq (complexPart y'.o12) := by linarith
  exact ⟨h01, h02, h12, by rw [h01, h02, h12] at C; linarith⟩

theorem slot_nondegenerate (y : Albert) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : InComplexSector y)
    (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b)
    (hcub : newtonCubicNorm y = 0)
    (hc0 : |y.d0| < 1 / 25) (hc1 : |y.d1| < 1 / 25) (hc2 : |y.d2| < 1 / 25)
    (he0 : |(jordan y y).d0 - 2 / 3| < 1 / 25)
    (he1 : |(jordan y y).d1 - 2 / 3| < 1 / 25)
    (he2 : |(jordan y y).d2 - 2 / 3| < 1 / 25) :
    1 / 2 < a ∧ 1 / 2 < b ∧ (complexPart y.o02).im ≠ 0 := by
  have E0 := fe_complex_square_d0 y.d0 y.d1 y.d2 (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have E1 := fe_complex_square_d1 y.d0 y.d1 y.d2 (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have E2 := fe_complex_square_d2 y.d0 y.d1 y.d2 (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have C := fe_complex_cubic y.d0 y.d1 y.d2 (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  rw [complexAlbert_eq y hc] at E0 E1 E2 C
  have hau : Complex.normSq (complexPart y.o01) = a ^ 2 := by rw [h01, normSq_complexPart_octScalar]
  have hbw : Complex.normSq (complexPart y.o12) = b ^ 2 := by rw [h12, normSq_complexPart_octScalar]
  have htriangle : (complexPart y.o01 * complexPart y.o12 * star (complexPart y.o02)).re =
      a * b * (complexPart y.o02).re := by
    rw [h01, h12, complexPart_octScalar, complexPart_octScalar, real_real_conj_re]
  rw [hau] at E0; rw [hau, hbw] at E1; rw [hbw] at E2
  rw [hcub, hau, hbw, htriangle] at C
  exact nondegenerate_core a b y.d0 y.d1 y.d2
    (jordan y y).d0 (jordan y y).d1 (jordan y y).d2
    (Complex.normSq (complexPart y.o02)) (complexPart y.o02).re (complexPart y.o02).im
    ha hb hc0 hc1 hc2 he0 he1 he2 (Complex.normSq_nonneg _) E0 E1 E2 C
    (by rw [Complex.normSq_apply]; ring)

theorem octInComplex_conj_slot (k : OctRelatedTriple) (hk : DiagonalOctTriple k)
    (hkI : k.A octI = -octI) (x : Octonion) (hx : OctInComplex x) :
    OctInComplex (k.A x) ∧ complexPart (k.A x) = star (complexPart x) := by
  have hd : k.A x = octScalar (complexPart x).re - (complexPart x).im • octI := by
    conv_lhs => rw [octInComplex_decomp x hx]
    rw [map_add, map_smul, diagonalOctTriple_scalar k hk, hkI, smul_neg, ← sub_eq_add_neg]
  rw [hd]
  refine ⟨⟨by simp [octScalar, octI, quatI], by simp [octScalar, octI, quatI],
    by simp [octScalar, octI, quatI]⟩, ?_⟩
  apply Complex.ext <;> simp [complexPart, octScalar, octI, quatI]

theorem exists_slot_conjugator :
    ∃ m : CompactAutomorphism,
      (∀ i : Fin 3, m.equiv (flatFrameP i) = flatFrameP i) ∧
      (∀ y : Albert, InComplexSector y →
        (m.equiv y).d0 = y.d0 ∧ (m.equiv y).d1 = y.d1 ∧ (m.equiv y).d2 = y.d2 ∧
        complexPart (m.equiv y).o01 = star (complexPart y.o01) ∧
        complexPart (m.equiv y).o02 = star (complexPart y.o02) ∧
        complexPart (m.equiv y).o12 = star (complexPart y.o12) ∧
        InComplexSector (m.equiv y)) := by
  have hneg : -octI = ((⟨0, -1, 0, 0⟩ : Quaternion ℝ), (0 : Quaternion ℝ)) := by
    apply Prod.ext <;> apply Quaternion.ext <;> simp [octI, quatI]
  obtain ⟨k, hk, hkI⟩ := exists_octAutomorphism_to_i (-octI)
    (by rw [hneg]; rfl) (by rw [hneg]; norm_num [octNormSq, Quaternion.normSq_def'])
  have hkIneg : k.A octI = -octI := by
    have h : k.A ((-1 : ℝ) • octI) = octI := by rw [neg_one_smul]; exact hkI
    rw [LinearEquiv.map_smul, neg_one_smul] at h
    simpa only [neg_neg] using congrArg Neg.neg h
  refine ⟨k.compactAutomorphism, fun i => frame_eq_of_encoder_eq flatFrameP flatFrameP
    flatFrameP_frame flatFrameP_frame k.compactAutomorphism
    (by rw [flatFrameP_encoder]; change (⟨flatXN.d0, flatXN.d1, flatXN.d2, _, _, _⟩ : Albert) = _; simp [flatXN, map_zero]) i,
    fun y hy => ?_⟩
  have hA01 := octInComplex_conj_slot k hk hkIneg y.o01 hy.1
  have hC02 := octInComplex_conj_slot k hk hkIneg y.o02 hy.2.1
  have hB12 := octInComplex_conj_slot k hk hkIneg y.o12 hy.2.2
  have hs01 : (k.compactAutomorphism.equiv y).o01 = k.A y.o01 := rfl
  have hs02 : (k.compactAutomorphism.equiv y).o02 = k.A y.o02 := by change k.C y.o02 = _; rw [hk.2.1]
  have hs12 : (k.compactAutomorphism.equiv y).o12 = k.A y.o12 := by change k.B y.o12 = _; rw [hk.1]
  exact ⟨rfl, rfl, rfl, hs01 ▸ hA01.2, hs02 ▸ hC02.2, hs12 ▸ hB12.2,
    hs01 ▸ hA01.1, hs02 ▸ hC02.1, hs12 ▸ hB12.1⟩

theorem pair_normal_form_rel (y y' : Albert) (a b a' b' : ℝ)
    (hc : InComplexSector y) (hc' : InComplexSector y')
    (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b)
    (h01' : y'.o01 = octScalar a') (h12' : y'.o12 = octScalar b')
    (hd0 : y.d0 = y'.d0) (hd1 : y.d1 = y'.d1) (hd2 : y.d2 = y'.d2)
    (haa : a = a') (hbb : b = b')
    (hre : (complexPart y.o02).re = (complexPart y'.o02).re)
    (himsq : (complexPart y.o02).im ^ 2 = (complexPart y'.o02).im ^ 2) :
    ∃ m : CompactAutomorphism,
      (∀ i : Fin 3, m.equiv (flatFrameP i) = flatFrameP i) ∧ m.equiv y = y' := by
  have hy01 : y.o01 = y'.o01 := by rw [h01, h01', haa]
  have hy12 : y.o12 = y'.o12 := by rw [h12, h12', hbb]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp himsq with him | him
  · exact ⟨CompactAutomorphism.refl, fun _ => rfl,
      Albert.ext hd0 hd1 hd2 hy01 (octInComplex_ext y.o02 y'.o02 hc.2.1 hc'.2.1 (Complex.ext hre him)) hy12⟩
  · obtain ⟨m, hmP, hmslots⟩ := exists_slot_conjugator
    obtain ⟨e0, e1, e2, c01, c02, c12, hsec⟩ := hmslots y hc
    refine ⟨m, hmP, Albert.ext (e0.trans hd0) (e1.trans hd1) (e2.trans hd2) ?_ ?_ ?_⟩
    · refine octInComplex_ext _ _ hsec.1 hc'.1 ?_
      rw [c01, h01, h01', complexPart_octScalar, complexPart_octScalar, haa]
      exact Complex.conj_ofReal a'
    · refine octInComplex_ext _ _ hsec.2.1 hc'.2.1 ?_
      rw [c02]; exact Complex.ext hre (by change -(complexPart y.o02).im = _; linarith)
    · refine octInComplex_ext _ _ hsec.2.2 hc'.2.2 ?_
      rw [c12, h12, h12', complexPart_octScalar, complexPart_octScalar, hbb]
      exact Complex.conj_ofReal b'

theorem nearby_pair_normalization
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
  have hQframe : Frame (fun i => g.equiv (q i)) := g.map_frame q hq
  have hQframe' : Frame (fun i => g'.equiv (q' i)) := g'.map_frame q' hq'
  have hyg : (encoder fun i => g.equiv (q i)) = g.equiv (encoder q) := g.encoder_map q
  have hyg' : (encoder fun i => g'.equiv (q' i)) = g'.equiv (encoder q') := g'.encoder_map q'
  have hcy : InComplexSector (encoder fun i => g.equiv (q i)) := hyg ▸ hsecg
  have hcy' : InComplexSector (encoder fun i => g'.equiv (q' i)) := hyg' ▸ hsecg'
  have hy01 : (encoder fun i => g.equiv (q i)).o01 = octScalar a := by rw [hyg]; exact h01g
  have hy12 : (encoder fun i => g.equiv (q i)).o12 = octScalar b := by rw [hyg]; exact h12g
  have hy01' : (encoder fun i => g'.equiv (q' i)).o01 = octScalar a' := by rw [hyg']; exact h01g'
  have hy12' : (encoder fun i => g'.equiv (q' i)).o12 = octScalar b' := by rw [hyg']; exact h12g'
  obtain ⟨d0, d1, d2, e0, e1, e2⟩ := normalised_diag_data (fun i => g.equiv (q i)) hQframe
    (fun i j => inner (p i) (q j)) (fun i j => by rw [← hgp i]; exact g.inner_map (p i) (q j))
  obtain ⟨d0', d1', d2', e0', e1', e2'⟩ := normalised_diag_data (fun i => g'.equiv (q' i)) hQframe'
    (fun i j => inner (p i) (q j)) (fun i j => by rw [← hgp' i, g'.inner_map, hEq])
  have hd0 := d0.trans d0'.symm; have hd1 := d1.trans d1'.symm; have hd2 := d2.trans d2'.symm
  have hs0 := e0.trans e0'.symm; have hs1 := e1.trans e1'.symm; have hs2 := e2.trans e2'.symm
  have hcub := frame_encoder_cubicNorm _ hQframe
  have hcub' := frame_encoder_cubicNorm _ hQframe'
  have habs (i j : Fin 3) := abs_lt.mp (hbox i j)
  obtain ⟨hapos, hbpos, hsigma⟩ := slot_nondegenerate (encoder fun i => g.equiv (q i)) a b ha hb hcy hy01 hy12 hcub
    (by rw [d0, abs_lt]; constructor <;> linarith [(habs 2 2).1, (habs 2 2).2, (habs 2 0).1, (habs 2 0).2])
    (by rw [d1, abs_lt]; constructor <;> linarith [(habs 1 2).1, (habs 1 2).2, (habs 1 0).1, (habs 1 0).2])
    (by rw [d2, abs_lt]; constructor <;> linarith [(habs 0 2).1, (habs 0 2).2, (habs 0 0).1, (habs 0 0).2])
    (by rw [e0, abs_lt]; constructor <;> linarith [(habs 2 2).1, (habs 2 2).2, (habs 2 0).1, (habs 2 0).2])
    (by rw [e1, abs_lt]; constructor <;> linarith [(habs 1 2).1, (habs 1 2).2, (habs 1 0).1, (habs 1 0).2])
    (by rw [e2, abs_lt]; constructor <;> linarith [(habs 0 2).1, (habs 0 2).2, (habs 0 0).1, (habs 0 0).2])
  obtain ⟨hn01, hn02, hn12, htri⟩ :=
    slot_data_eq_of_diag_eq _ _ hcy hcy' hd0 hd1 hd2 hs0 hs1 hs2 (hcub.trans hcub'.symm)
  have haa : a = a' := nonneg_sq_eq_of_sq_eq a a' ha ha'
    (by simpa only [hy01, hy01', normSq_complexPart_octScalar] using hn01)
  have hbb : b = b' := nonneg_sq_eq_of_sq_eq b b' hb hb'
    (by simpa only [hy12, hy12', normSq_complexPart_octScalar] using hn12)
  have hre : (complexPart (encoder fun i => g.equiv (q i)).o02).re =
      (complexPart (encoder fun i => g'.equiv (q' i)).o02).re := by
    rw [hy01, hy12, hy01', hy12', complexPart_octScalar, complexPart_octScalar,
      complexPart_octScalar, complexPart_octScalar, real_real_conj_re,
      real_real_conj_re, ← haa, ← hbb] at htri
    exact mul_left_cancel₀ (ne_of_gt (mul_pos (by linarith) (by linarith))) htri
  have himsq := im_sq_eq_of_normSq_eq _ _ hn02 hre
  obtain ⟨m, hmP, hmy⟩ := pair_normal_form_rel _ _ a b a' b' hcy hcy' hy01 hy12 hy01' hy12'
    hd0 hd1 hd2 haa hbb hre himsq
  refine ⟨m.comp g, g', a', b', fun i => (congrArg m.equiv (hgp i)).trans (hmP i), hgp',
    fun i => frame_eq_of_encoder_eq q (fun i => g'.equiv (q' i)) hq hQframe' (m.comp g)
      (by rw [CompactAutomorphism.comp_apply, ← hyg, hmy]) i,
    hcy', hy01', hy12', by linarith, by linarith,
    ne_zero_of_sq_eq_of_ne_zero _ _ himsq hsigma⟩

theorem inner_sector_complexProjection (v W : Albert) (hv : InComplexSector v) :
    inner v W = inner v (complexProjection W) := by
  conv_lhs => rw [← complex_hidden_decomposition W]
  rw [inner_add_right, ← complexProjection_eq_self v hv, complex_hidden_orthogonal, add_zero]

theorem inner_diag_jordan_slots (x z E : Albert) (hxd : IsDiagonal x)
    (hE0 : E.d0 = 0) (hE1 : E.d1 = 0) (hE2 : E.d2 = 0) :
    inner (jordan x z) E =
      (x.d0 + x.d1) * octDot z.o01 E.o01 + (x.d0 + x.d2) * octDot z.o02 E.o02 +
        (x.d1 + x.d2) * octDot z.o12 E.o12 := by
  obtain ⟨hx01, hx02, hx12⟩ := hxd
  have s01 : (jordan x z).o01 = (1 / 2 : ℝ) • ((x.d0 + x.d1) • z.o01) := by
    rw [jordan_o01, hx01, hx02, hx12]; simp [octConj_zero, octMul_zero_left, octMul_zero_right]
  have s02 : (jordan x z).o02 = (1 / 2 : ℝ) • ((x.d0 + x.d2) • z.o02) := by
    rw [jordan_o02, hx01, hx02, hx12]; simp [octMul_zero_left, octMul_zero_right]
  have s12 : (jordan x z).o12 = (1 / 2 : ℝ) • ((x.d1 + x.d2) • z.o12) := by
    rw [jordan_o12, hx01, hx02, hx12]; simp [octConj_zero, octMul_zero_left, octMul_zero_right]
  rw [inner_coordinates, hE0, hE1, hE2, s01, s02, s12]
  simp only [octDot_smul_left]; ring

theorem slot_pairings_zero (z E : Albert)
    (hE0 : E.d0 = 0) (hE1 : E.d1 = 0) (hE2 : E.d2 = 0)
    (h0 : inner (jordan (flatFrameP 0) z) E = 0)
    (h1 : inner (jordan (flatFrameP 1) z) E = 0)
    (h2 : inner (jordan (flatFrameP 2) z) E = 0) :
    octDot z.o01 E.o01 = 0 ∧ octDot z.o02 E.o02 = 0 ∧ octDot z.o12 E.o12 = 0 := by
  rw [inner_diag_jordan_slots _ z E (flatFrameP_isDiagonal 0) hE0 hE1 hE2, flatFrameP_zero_eq] at h0
  rw [inner_diag_jordan_slots _ z E (flatFrameP_isDiagonal 1) hE0 hE1 hE2, flatFrameP_one_eq] at h1
  rw [inner_diag_jordan_slots _ z E (flatFrameP_isDiagonal 2) hE0 hE1 hE2, flatFrameP_two_eq] at h2
  simp only [diagonalAlbert] at h0 h1 h2
  exact ⟨by linarith, by linarith, by linarith⟩

theorem sector_slot_recovery (y E : Albert) (a b : ℝ)
    (hcy : InComplexSector y) (hcE : InComplexSector E)
    (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b)
    (hapos : 0 < a) (hbpos : 0 < b)
    (hsigma : (complexPart y.o02).im ≠ 0)
    (hE0 : E.d0 = 0) (hE1 : E.d1 = 0) (hE2 : E.d2 = 0)
    (p1 : octDot y.o01 E.o01 = 0) (p2 : octDot y.o02 E.o02 = 0)
    (p3 : octDot y.o12 E.o12 = 0)
    (q1 : octDot (jordan y y).o01 E.o01 = 0) (q2 : octDot (jordan y y).o02 E.o02 = 0)
    (q3 : octDot (jordan y y).o12 E.o12 = 0) :
    E = 0 := by
  have hcsq : InComplexSector (jordan y y) := complexSector_jordan y y hcy hcy
  have hua : complexPart y.o01 = (a : ℂ) := by rw [h01, complexPart_octScalar]
  have hwb : complexPart y.o12 = (b : ℂ) := by rw [h12, complexPart_octScalar]
  have S01 := fe_complex_square_o01 y.d0 y.d1 y.d2 (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have S02 := fe_complex_square_o02 y.d0 y.d1 y.d2 (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  have S12 := fe_complex_square_o12 y.d0 y.d1 y.d2 (complexPart y.o01) (complexPart y.o02) (complexPart y.o12)
  rw [complexAlbert_eq y hcy, hua, hwb] at S01 S02 S12
  rw [octDot_inComplex y.o01 E.o01 hcy.1 hcE.1, hua] at p1
  rw [octDot_inComplex (jordan y y).o01 E.o01 hcsq.1 hcE.1, S01] at q1
  rw [octDot_inComplex y.o02 E.o02 hcy.2.1 hcE.2.1] at p2
  rw [octDot_inComplex (jordan y y).o02 E.o02 hcsq.2.1 hcE.2.1, S02] at q2
  rw [octDot_inComplex y.o12 E.o12 hcy.2.2 hcE.2.2, hwb] at p3
  rw [octDot_inComplex (jordan y y).o12 E.o12 hcsq.2.2 hcE.2.2, S12] at q3
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im] at p1 p3 q1 q2 q3
  have hne : a * b * (complexPart y.o02).im ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_of_gt hapos) (ne_of_gt hbpos)) hsigma
  obtain ⟨r01, i01⟩ := two_by_two a 0 (a * (y.d0 + y.d1) + b * (complexPart y.o02).re)
    (b * (complexPart y.o02).im) (complexPart E.o01).re (complexPart E.o01).im
    (by linear_combination p1) (by linear_combination q1)
    (fun h => hne (by linear_combination h))
  obtain ⟨r02, i02⟩ := two_by_two (complexPart y.o02).re (complexPart y.o02).im
    ((complexPart y.o02).re * (y.d0 + y.d2) + a * b) ((complexPart y.o02).im * (y.d0 + y.d2))
    (complexPart E.o02).re (complexPart E.o02).im
    (by linear_combination p2) (by linear_combination q2)
    (fun h => hne (by linear_combination -h))
  obtain ⟨r12, i12⟩ := two_by_two b 0 (b * (y.d1 + y.d2) + a * (complexPart y.o02).re)
    (a * (complexPart y.o02).im) (complexPart E.o12).re (complexPart E.o12).im
    (by linear_combination p3) (by linear_combination q3)
    (fun h => hne (by linear_combination h))
  exact Albert.ext hE0 hE1 hE2
    (octInComplex_eq_zero E.o01 hcE.1 r01 i01)
    (octInComplex_eq_zero E.o02 hcE.2.1 r02 i02)
    (octInComplex_eq_zero E.o12 hcE.2.2 r12 i12)

theorem inner_sector_hiddenAlbert (v : Albert) (hv : InComplexSector v)
    (M : Matrix (Fin 3) (Fin 3) ℂ) : inner v (hiddenAlbert M) = 0 := by
  rw [← complexProjection_eq_self v hv]
  exact complex_hidden_orthogonal v M

theorem sector_hidden_cross_perp (x : Albert) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    complexProjection (jordan (complexProjection x) (hiddenAlbert M)) = 0 := by
  refine complexProjection_zero_of_perp _ fun v hv => ?_
  rw [← inner_jordan_associative]
  exact inner_sector_hiddenAlbert _ (complexSector_jordan _ _
    ((complexSector_mem_iff v).mp hv) ((complexSector_mem_iff _).mp (complexProjection_mem x))) M

theorem jordan_add_self_split (S H : Albert) :
    jordan (S + H) (S + H) = jordan S S + jordan S H + (jordan S H + jordan H H) := by
  rw [jordan_add_left, jordan_add_right, jordan_add_right, jordan_comm H S]

theorem complexProjection_square_split (z : Albert) :
    complexProjection (jordan z z) =
      jordan (complexProjection z) (complexProjection z) +
        complexProjection (jordan (hiddenAlbert (hiddenMatrix z))
          (hiddenAlbert (hiddenMatrix z))) := by
  have hsec : InComplexSector (complexProjection z) :=
    (complexSector_mem_iff _).mp (complexProjection_mem z)
  have hcross : complexProjection
      (jordan (hiddenAlbert (hiddenMatrix z)) (complexProjection z)) = 0 := by
    rw [jordan_comm]; exact sector_hidden_cross_perp z (hiddenMatrix z)
  conv_lhs => rw [← complex_hidden_decomposition z]
  rw [jordan_add_left, jordan_add_right, jordan_add_right,
    complexProjection_add, complexProjection_add, complexProjection_add,
    complexProjection_eq_self _ (complexSector_jordan _ _ hsec hsec),
    sector_hidden_cross_perp z (hiddenMatrix z), hcross, add_zero, zero_add]

theorem gram_eq_of_sector_data (z z' : Albert)
    (hS : complexProjection z = complexProjection z')
    (hT : complexProjection (jordan z z) = complexProjection (jordan z' z')) :
    sectorColumnGram (hiddenMatrix z) = sectorColumnGram (hiddenMatrix z') := by
  have hcore : complexProjection (jordan (hiddenAlbert (hiddenMatrix z))
        (hiddenAlbert (hiddenMatrix z))) =
      complexProjection (jordan (hiddenAlbert (hiddenMatrix z'))
        (hiddenAlbert (hiddenMatrix z'))) := by
    have h := complexProjection_square_split z
    have h' := complexProjection_square_split z'
    rw [hS, hT] at h
    exact add_left_cancel (h.symm.trans h')
  rw [hidden_square_complexProjection, hidden_square_complexProjection] at hcore
  have hherm : (sectorColumnGram (hiddenMatrix z)).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self (hiddenMatrix z)
  have hherm' : (sectorColumnGram (hiddenMatrix z')).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self (hiddenMatrix z')
  have hS0 := congrArg Albert.d0 hcore
  have hS1 := congrArg Albert.d1 hcore
  have hS2 := congrArg Albert.d2 hcore
  simp only [complexAlbert] at hS0 hS1 hS2
  have hg01 : sectorColumnGram (hiddenMatrix z) 0 1 = sectorColumnGram (hiddenMatrix z') 0 1 :=
    neg_inj.mp (by simpa only [complexPart_complexAlbert_o01] using congrArg (fun x => complexPart x.o01) hcore)
  have hg02 : sectorColumnGram (hiddenMatrix z) 0 2 = sectorColumnGram (hiddenMatrix z') 0 2 :=
    neg_inj.mp (by simpa only [complexPart_complexAlbert_o02] using congrArg (fun x => complexPart x.o02) hcore)
  have hg12 : sectorColumnGram (hiddenMatrix z) 1 2 = sectorColumnGram (hiddenMatrix z') 1 2 :=
    neg_inj.mp (by simpa only [complexPart_complexAlbert_o12] using congrArg (fun x => complexPart x.o12) hcore)
  have hFroDiag (M : Matrix (Fin 3) (Fin 3) ℂ) :
      (sectorColumnGram M 0 0).re + (sectorColumnGram M 1 1).re +
        (sectorColumnGram M 2 2).re = sectorFrobeniusSq M := by
    simp [sectorColumnGram, sectorFrobeniusSq, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]; ring
  have hFro : sectorFrobeniusSq (hiddenMatrix z) = sectorFrobeniusSq (hiddenMatrix z') := by
    linarith [hS0, hS1, hS2, hFroDiag (hiddenMatrix z), hFroDiag (hiddenMatrix z')]
  have hdiagIm (M : Matrix (Fin 3) (Fin 3) ℂ) (hM : (sectorColumnGram M).IsHermitian) (i : Fin 3) :
      (sectorColumnGram M i i).im = 0 := by
    have h := congrArg Complex.im (hM.apply i i)
    simp only [Complex.star_def, Complex.conj_im] at h; linarith
  have hd0 : sectorColumnGram (hiddenMatrix z) 0 0 = sectorColumnGram (hiddenMatrix z') 0 0 :=
    Complex.ext (by linarith) (by rw [hdiagIm _ hherm 0, hdiagIm _ hherm' 0])
  have hd1 : sectorColumnGram (hiddenMatrix z) 1 1 = sectorColumnGram (hiddenMatrix z') 1 1 :=
    Complex.ext (by linarith) (by rw [hdiagIm _ hherm 1, hdiagIm _ hherm' 1])
  have hd2 : sectorColumnGram (hiddenMatrix z) 2 2 = sectorColumnGram (hiddenMatrix z') 2 2 :=
    Complex.ext (by linarith) (by rw [hdiagIm _ hherm 2, hdiagIm _ hherm' 2])
  ext i j
  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl
  · exact hd0
  · exact hg01
  · exact hg02
  · rw [← hherm.apply 1 0, ← hherm'.apply 1 0, hg01]
  · exact hd1
  · exact hg12
  · rw [← hherm.apply 2 0, ← hherm'.apply 2 0, hg02]
  · rw [← hherm.apply 2 1, ← hherm'.apply 2 1, hg12]
  · exact hd2

theorem cubic_trace_split (S H : Albert)
    (hc1 : inner S (jordan S H) = 0)
    (hc2 : inner H (jordan S S) = 0)
    (hc3 : inner H (jordan S H) = inner S (jordan H H)) :
    inner (S + H) (jordan (S + H) (S + H)) =
      inner S (jordan S S) + 3 * inner S (jordan H H) + inner H (jordan H H) := by
  rw [jordan_add_self_split]
  simp only [inner_add_left, inner_add_right, hc1, hc2, hc3]; ring

theorem newtonCubicNorm_sector_split (z : Albert) :
    newtonCubicNorm z =
      ((trace (complexProjection z)) ^ 3
        - 3 * trace (complexProjection z) * trace (complexProjection (jordan z z))
        + 2 * (3 * inner (complexProjection z) (complexProjection (jordan z z))
              - 2 * inner (complexProjection z)
                  (jordan (complexProjection z) (complexProjection z))
              + 6 * (hiddenMatrix z).det.re)) / 6 := by
  have hdec := complex_hidden_decomposition z
  have hsec : InComplexSector (complexProjection z) :=
    (complexSector_mem_iff _).mp (complexProjection_mem z)
  have hHtr (w : Albert) : trace (hiddenAlbert (hiddenMatrix w)) = 0 := by simp [hiddenAlbert, trace]
  have hc1 : inner (complexProjection z)
      (jordan (complexProjection z) (hiddenAlbert (hiddenMatrix z))) = 0 := by
    rw [← inner_jordan_associative]
    exact inner_sector_hiddenAlbert _ (complexSector_jordan _ _ hsec hsec) (hiddenMatrix z)
  have hc2 : inner (hiddenAlbert (hiddenMatrix z))
      (jordan (complexProjection z) (complexProjection z)) = 0 := by
    rw [inner_comm]
    exact inner_sector_hiddenAlbert _ (complexSector_jordan _ _ hsec hsec) (hiddenMatrix z)
  have hc3 : inner (hiddenAlbert (hiddenMatrix z))
      (jordan (complexProjection z) (hiddenAlbert (hiddenMatrix z))) =
      inner (complexProjection z)
        (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z))) := by
    rw [inner_comm (hiddenAlbert (hiddenMatrix z)), inner_jordan_associative]
  have ht (w : Albert) : trace w = trace (complexProjection w) := by
    have h := trace_add (complexProjection w) (hiddenAlbert (hiddenMatrix w))
    rw [complex_hidden_decomposition w, hHtr, add_zero] at h; exact h
  have hcube : inner (hiddenAlbert (hiddenMatrix z))
      (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z))) =
      6 * (hiddenMatrix z).det.re := by
    have h := hiddenAlbert_cubicNorm (hiddenMatrix z)
    rw [newtonCubicNorm, hHtr] at h
    linarith [show trace (jordan (hiddenAlbert (hiddenMatrix z))
      (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z)))) =
      inner (hiddenAlbert (hiddenMatrix z))
        (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z))) from rfl]
  have hmix : inner (complexProjection z)
      (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z))) =
      inner (complexProjection z) (complexProjection (jordan z z)) -
        inner (complexProjection z) (jordan (complexProjection z) (complexProjection z)) := by
    have hexp : inner (complexProjection z)
        (jordan (complexProjection z + hiddenAlbert (hiddenMatrix z))
          (complexProjection z + hiddenAlbert (hiddenMatrix z))) =
        inner (complexProjection z) (jordan (complexProjection z) (complexProjection z)) +
          inner (complexProjection z)
            (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z))) := by
      rw [jordan_add_self_split]; simp only [inner_add_right, hc1]; ring
    rw [hdec, inner_sector_complexProjection _ _ hsec] at hexp; linarith
  have hcubic : trace (jordan z (jordan z z)) =
      inner (complexProjection z) (jordan (complexProjection z) (complexProjection z)) +
        3 * inner (complexProjection z)
          (jordan (hiddenAlbert (hiddenMatrix z)) (hiddenAlbert (hiddenMatrix z))) +
        6 * (hiddenMatrix z).det.re := by
    have h := cubic_trace_split (complexProjection z) (hiddenAlbert (hiddenMatrix z)) hc1 hc2 hc3
    rw [hdec, hcube] at h; exact h
  rw [newtonCubicNorm, ht z, ht (jordan z z), hcubic, hmix]; ring

theorem det_re_eq_of_sector_data (z z' : Albert)
    (hS : complexProjection z = complexProjection z')
    (hT : complexProjection (jordan z z) = complexProjection (jordan z' z'))
    (hcub : newtonCubicNorm z = newtonCubicNorm z') :
    (hiddenMatrix z).det.re = (hiddenMatrix z').det.re := by
  rw [newtonCubicNorm_sector_split z, newtonCubicNorm_sector_split z', hS, hT] at hcub
  linarith [hcub]

theorem su3_transport_general (M N : Matrix (Fin 3) (Fin 3) ℂ)
    (hG : sectorColumnGram M = sectorColumnGram N)
    (hUnit : IsUnit (sectorColumnGram M).det)
    (hdet : N.det = M.det) :
    ∃ s : SectorUnitary, (s : SectorMatrix).det = 1 ∧ (s : SectorMatrix) * M = N := by
  have hGdef (X : Matrix (Fin 3) (Fin 3) ℂ) : sectorColumnGram X = X.conjTranspose * X := rfl
  have hAM : ((sectorColumnGram M)⁻¹ * M.conjTranspose) * M = 1 := by
    rw [Matrix.mul_assoc, ← hGdef M, Matrix.nonsing_inv_mul _ hUnit]
  have hMA : M * ((sectorColumnGram M)⁻¹ * M.conjTranspose) = 1 := mul_eq_one_comm.mp hAM
  have hUnitary :
      (N * ((sectorColumnGram M)⁻¹ * M.conjTranspose)).conjTranspose *
        (N * ((sectorColumnGram M)⁻¹ * M.conjTranspose)) = 1 := by
    have hstep :
        ((sectorColumnGram M)⁻¹ * M.conjTranspose).conjTranspose * (N.conjTranspose * N) *
            ((sectorColumnGram M)⁻¹ * M.conjTranspose) =
          (M * ((sectorColumnGram M)⁻¹ * M.conjTranspose)).conjTranspose *
            (M * ((sectorColumnGram M)⁻¹ * M.conjTranspose)) := by
      rw [← hGdef N, ← hG, hGdef M]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc N.conjTranspose N ((sectorColumnGram M)⁻¹ * M.conjTranspose),
      ← Matrix.mul_assoc, hstep, hMA, Matrix.conjTranspose_one, Matrix.one_mul]
  refine ⟨⟨N * ((sectorColumnGram M)⁻¹ * M.conjTranspose),
    Matrix.mem_unitaryGroup_iff'.mpr hUnitary⟩, ?_, ?_⟩
  · change (N * ((sectorColumnGram M)⁻¹ * M.conjTranspose)).det = 1
    rw [Matrix.det_mul, hdet, ← Matrix.det_mul, hMA, Matrix.det_one]
  · change N * ((sectorColumnGram M)⁻¹ * M.conjTranspose) * M = N
    rw [Matrix.mul_assoc, hAM, Matrix.mul_one]

theorem su3_maps_hiddenAlbert (s : SectorUnitary) (hs : (s : SectorMatrix).det = 1)
    (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (sectorLeftSU3Automorphism s hs).equiv (hiddenAlbert M) =
      hiddenAlbert ((s : SectorMatrix) * M) := by
  have hc : complexProjection
      ((sectorLeftSU3Automorphism s hs).equiv (hiddenAlbert M)) = 0 := by
    refine complexProjection_zero_of_perp _ fun v hv => ?_
    have hvs : InComplexSector v := (complexSector_mem_iff v).mp hv
    rw [← sectorLeftSU3_fixes_complex s hs v hvs,
      (sectorLeftSU3Automorphism s hs).inner_map v (hiddenAlbert M)]
    exact inner_sector_hiddenAlbert v hvs M
  have hm : hiddenMatrix ((sectorLeftSU3Automorphism s hs).equiv (hiddenAlbert M)) =
      (s : SectorMatrix) * M := by
    rw [sectorLeftSU3_hidden s hs, hiddenMatrix_hiddenAlbert]
  have hd := complex_hidden_decomposition
    ((sectorLeftSU3Automorphism s hs).equiv (hiddenAlbert M))
  rw [hc, hm, zero_add] at hd
  exact hd.symm

theorem su3_maps_sector_hidden (s : SectorUnitary) (hs : (s : SectorMatrix).det = 1)
    (z : Albert) :
    (sectorLeftSU3Automorphism s hs).equiv z =
      complexProjection z + hiddenAlbert ((s : SectorMatrix) * hiddenMatrix z) := by
  conv_lhs => rw [← complex_hidden_decomposition z]
  rw [map_add, sectorLeftSU3_fixes_complex s hs _ ((complexSector_mem_iff _).mp (complexProjection_mem z)),
    su3_maps_hiddenAlbert s hs (hiddenMatrix z)]

theorem phi_normalized (y z : Albert) (a b : ℝ)
    (hcy : InComplexSector y) (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b) :
    phi flatXN y z =
      4 * a * b * (complexPart y.o02).im * (hiddenMatrix z).det.im := by
  rw [phi_of_diagonal_complex flatXN y z (by simp [IsDiagonal, flatXN]) hcy]
  change 2 * (1 - 0) * (0 - -1) * (-1 - 1) * _ * _ = _
  rw [h01, h12, complexPart_octScalar, complexPart_octScalar, real_real_conj_im]; ring

def PBox : Set Triple :=
  {T : Triple | ∀ i j : Fin 3, |(ledger54 T).2.1 i j - 1 / 3| < 1 / 50}

theorem isOpen_PBox : IsOpen PBox := by
  have hset : PBox = ⋂ r : Fin 3 × Fin 3,
      {T : Triple | |(ledger54 T).2.1 r.1 r.2 - 1 / 3| < 1 / 50} := by
    ext T; simp only [PBox, Set.mem_ofPred_eq, Set.mem_iInter, Prod.forall]
  rw [hset]
  refine isOpen_iInter_of_finite fun r => ?_
  have h2 : Continuous fun L : Ledger54 => L.2.1 r.1 r.2 := by fun_prop
  exact isOpen_lt (((h2.comp continuous_ledger54).sub continuous_const).abs) continuous_const

theorem nearby_core (T S : Triple)
    (hT : ∀ a : Fin 3, Frame (T a)) (hS : ∀ a : Fin 3, Frame (S a))
    (hbox : T ∈ PBox) (hL : ledger54 T = ledger54 S) (hTne : phiOf T ≠ 0) :
    phiOf T ^ 2 = phiOf S ^ 2 ∧
      (phiOf T = phiOf S → ∃ k : CompactAutomorphism, mapAtoms k S = T) := by
  obtain ⟨g, g', a, b, hgp, hgp', hqq, hcy, h01, h12, hapos, hbpos, hsig⟩ :=
    nearby_pair_normalization (T 0) (T 1) (S 0) (S 1) (hT 0) (hT 1) (hS 0) (hS 1) hbox
      (fun i j => congrArg (fun L : Ledger54 => L.2.1 i j) hL)
  have hQsame : (fun i => g.equiv (T 1 i)) = fun i => g'.equiv (S 1 i) := funext hqq
  have hQframe : Frame (fun i => g'.equiv (S 1 i)) := g'.map_frame (S 1) (hS 1)
  have hrTframe : Frame (fun k => g.equiv (T 2 k)) := g.map_frame (T 2) (hT 2)
  have hrSframe : Frame (fun k => g'.equiv (S 2 k)) := g'.map_frame (S 2) (hS 2)
  have hQsec : ∀ j : Fin 3, InComplexSector ((fun i => g'.equiv (S 1 i)) j) := fun j =>
    (complexSector_mem_iff _).mp (frame_in_complexSector _ hQframe hcy j)
  have hatom (k : Fin 3) :
      complexProjection (g.equiv (T 2 k)) = complexProjection (g'.equiv (S 2 k)) := by
    have hEsec : InComplexSector (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))) :=
      (complexSector_mem_iff _).mp (complexProjection_mem _)
    have hR (i : Fin 3) :
        inner (flatFrameP i) (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))) = 0 := by
      have e1 : inner (flatFrameP i) (g.equiv (T 2 k)) = inner (T 0 i) (T 2 k) := by
        rw [← hgp i]; exact g.inner_map _ _
      have e2 : inner (flatFrameP i) (g'.equiv (S 2 k)) = inner (S 0 i) (S 2 k) := by
        rw [← hgp' i]; exact g'.inner_map _ _
      have hRL : inner (T 2 k) (T 0 i) = inner (S 2 k) (S 0 i) :=
        congrArg (fun L : Ledger54 => L.2.2.2 k i) hL
      rw [← inner_sector_complexProjection _ _ (flatFrameP_inComplexSector i),
        inner_sub_right, e1, e2, inner_comm (T 0 i), inner_comm (S 0 i), hRL, sub_self]
    have hE0 : (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))).d0 = 0 := by
      simpa only [inner_flatFrameP_two] using hR 2
    have hE1 : (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))).d1 = 0 := by
      simpa only [inner_flatFrameP_one] using hR 1
    have hE2 : (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))).d2 = 0 := by
      simpa only [inner_flatFrameP_zero] using hR 0
    have hCE (i j : Fin 3) :
        inner (jordan (flatFrameP i) ((fun i => g'.equiv (S 1 i)) j))
          (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))) = 0 := by
      rw [← inner_sector_complexProjection _ _
        (complexSector_jordan _ _ (flatFrameP_inComplexSector i) (hQsec j)), inner_sub_right]
      have hCL : ledger (T 0) (T 1) (T 2) i j k = ledger (S 0) (S 1) (S 2) i j k :=
        congrArg (fun L : Ledger54 => L.1 i j k) hL
      have e1 : inner (jordan (flatFrameP i) ((fun i => g'.equiv (S 1 i)) j)) (g.equiv (T 2 k)) =
          ledger (T 0) (T 1) (T 2) i j k := by
        rw [← hQsame, ← hgp i]
        change inner (jordan (g.equiv (T 0 i)) (g.equiv (T 1 j))) (g.equiv (T 2 k)) = _
        rw [← g.map_jordan, g.inner_map]; rfl
      have e2 : inner (jordan (flatFrameP i) ((fun i => g'.equiv (S 1 i)) j)) (g'.equiv (S 2 k)) =
          ledger (S 0) (S 1) (S 2) i j k := by
        rw [← hgp' i]
        change inner (jordan (g'.equiv (S 0 i)) (g'.equiv (S 1 j))) (g'.equiv (S 2 k)) = _
        rw [← g'.map_jordan, g'.inner_map]; rfl
      rw [e1, e2, hCL, sub_self]
    have hyc (i : Fin 3) :
        inner (jordan (flatFrameP i) (encoder fun i => g'.equiv (S 1 i)))
          (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))) = 0 := by
      change inner (jordan (flatFrameP i) (g'.equiv (S 1 2) - g'.equiv (S 1 0))) _ = 0
      rw [jordan_sub_right, inner_sub_left, hCE i 2, hCE i 0, sub_self]
    have hsqc (i : Fin 3) :
        inner (jordan (flatFrameP i) (jordan (encoder fun i => g'.equiv (S 1 i))
          (encoder fun i => g'.equiv (S 1 i))))
          (complexProjection (g.equiv (T 2 k) - g'.equiv (S 2 k))) = 0 := by
      rw [frame_encoder_square _ hQframe, jordan_add_right, inner_add_left, hCE i 2, hCE i 0, add_zero]
    obtain ⟨p1, p2, p3⟩ := slot_pairings_zero _ _ hE0 hE1 hE2 (hyc 0) (hyc 1) (hyc 2)
    obtain ⟨q1, q2, q3⟩ := slot_pairings_zero _ _ hE0 hE1 hE2 (hsqc 0) (hsqc 1) (hsqc 2)
    have hzero := sector_slot_recovery _ _ a b hcy hEsec h01 h12 hapos hbpos hsig hE0 hE1 hE2 p1 p2 p3 q1 q2 q3
    rw [complexProjection_sub] at hzero
    exact sub_eq_zero.mp hzero
  have hSigma : complexProjection (encoder fun k => g.equiv (T 2 k)) =
      complexProjection (encoder fun k => g'.equiv (S 2 k)) := by
    change complexProjection (g.equiv (T 2 2) - g.equiv (T 2 0)) =
      complexProjection (g'.equiv (S 2 2) - g'.equiv (S 2 0))
    rw [complexProjection_sub, complexProjection_sub, hatom 2, hatom 0]
  have hTheta : complexProjection (jordan (encoder fun k => g.equiv (T 2 k))
        (encoder fun k => g.equiv (T 2 k))) =
      complexProjection (jordan (encoder fun k => g'.equiv (S 2 k))
        (encoder fun k => g'.equiv (S 2 k))) := by
    rw [frame_encoder_square _ hrTframe, frame_encoder_square _ hrSframe,
      complexProjection_add, complexProjection_add, hatom 2, hatom 0]
  have hGram := gram_eq_of_sector_data _ _ hSigma hTheta
  have hdetre := det_re_eq_of_sector_data _ _ hSigma hTheta
    (by rw [frame_encoder_cubicNorm _ hrTframe, frame_encoder_cubicNorm _ hrSframe])
  have hnorm : Complex.normSq (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det =
      Complex.normSq (hiddenMatrix (encoder fun k => g'.equiv (S 2 k))).det := by
    rw [normSq_det_eq_gram_det_re, normSq_det_eq_gram_det_re]
    exact congrArg (fun G : Matrix (Fin 3) (Fin 3) ℂ => G.det.re) hGram
  have hdetim := im_sq_eq_of_normSq_eq _ _ hnorm hdetre
  have hcoef : 4 * a * b * (complexPart (encoder fun i => g'.equiv (S 1 i)).o02).im ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hapos)) (ne_of_gt hbpos)) hsig
  have hphiT : phiOf T = 4 * a * b *
      (complexPart (encoder fun i => g'.equiv (S 1 i)).o02).im *
      (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det.im := by
    rw [phiOf_apply, ← g.phi_map, ← g.encoder_map (T 0), ← g.encoder_map (T 1),
      ← g.encoder_map (T 2), congrArg encoder (funext hgp), flatFrameP_encoder, hQsame,
      phi_normalized _ _ a b hcy h01 h12]
  have hphiS : phiOf S = 4 * a * b *
      (complexPart (encoder fun i => g'.equiv (S 1 i)).o02).im *
      (hiddenMatrix (encoder fun k => g'.equiv (S 2 k))).det.im := by
    rw [phiOf_apply, ← g'.phi_map, ← g'.encoder_map (S 0), ← g'.encoder_map (S 1),
      ← g'.encoder_map (S 2), congrArg encoder (funext hgp'), flatFrameP_encoder,
      phi_normalized _ _ a b hcy h01 h12]
  refine ⟨by rw [hphiT, hphiS]; exact mul_sq_eq_of_sq_eq _ _ _ hdetim, fun hsame => ?_⟩
  rw [hphiT, hphiS] at hsame
  have hdeteq : (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det =
      (hiddenMatrix (encoder fun k => g'.equiv (S 2 k))).det :=
    Complex.ext hdetre (mul_left_cancel₀ hcoef hsame)
  have hdetne : (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det ≠ 0 := fun h =>
    hTne (by rw [hphiT, show (hiddenMatrix (encoder fun k => g.equiv (T 2 k))).det.im = 0 by rw [h]; rfl, mul_zero])
  have hUnit : IsUnit (sectorColumnGram (hiddenMatrix (encoder fun k => g.equiv (T 2 k)))).det := by
    refine isUnit_iff_ne_zero.mpr fun hz => hdetne (Complex.normSq_eq_zero.mp ?_)
    rw [normSq_det_eq_gram_det_re]
    change (sectorColumnGram _).det.re = 0
    rw [hz]; rfl
  obtain ⟨s, hs, hsM⟩ := su3_transport_general _ _ hGram hUnit hdeteq.symm
  have hatoms : ∀ k : Fin 3,
      (sectorLeftSU3Automorphism s hs).equiv (g.equiv (T 2 k)) = g'.equiv (S 2 k) :=
    frame_eq_of_encoder_eq _ _ hrTframe hrSframe (sectorLeftSU3Automorphism s hs)
      (by rw [su3_maps_sector_hidden s hs, hsM, hSigma, complex_hidden_decomposition])
  have hKT (c i : Fin 3) :
      (g'.symm.comp ((sectorLeftSU3Automorphism s hs).comp g)).equiv (T c i) = S c i := by
    rw [CompactAutomorphism.comp_apply]
    rcases fin3_cases c with rfl | rfl | rfl
    · rw [CompactAutomorphism.comp_apply, hgp i,
        sectorLeftSU3_fixes_complex s hs _ (flatFrameP_inComplexSector i), ← hgp' i]
      exact g'.equiv.symm_apply_apply _
    · rw [CompactAutomorphism.comp_apply, hqq i,
        sectorLeftSU3_fixes_complex s hs _ (hQsec i)]
      exact g'.equiv.symm_apply_apply _
    · rw [CompactAutomorphism.comp_apply, hatoms i]
      exact g'.equiv.symm_apply_apply _
  refine ⟨(g'.symm.comp ((sectorLeftSU3Automorphism s hs).comp g)).symm, ?_⟩
  funext c i
  exact (congrArg _ (hKT c i).symm).trans
    ((g'.symm.comp ((sectorLeftSU3Automorphism s hs).comp g)).equiv.symm_apply_apply (T c i))

theorem flatBaseTriple_mem_PBox : flatBaseTriple ∈ PBox := fun i j => by
  have h : (ledger54 flatBaseTriple).2.1 i j = 1 / 3 :=
    uniformLedger_pair_overlap flatFrameP flatFrameQ flatFrameR flatFrameR_frame flat_uniform i j
  rw [h]; norm_num

private def LBox : Set Ledger54 :=
  {L : Ledger54 | ∀ i j : Fin 3, |L.2.1 i j - 1 / 3| < 1 / 50}

private theorem isOpen_LBox : IsOpen LBox := by
  have hset : LBox = ⋂ r : Fin 3 × Fin 3, {L : Ledger54 | |L.2.1 r.1 r.2 - 1 / 3| < 1 / 50} := by
    ext L; simp only [LBox, Set.mem_ofPred_eq, Set.mem_iInter, Prod.forall]
  rw [hset]
  refine isOpen_iInter_of_finite fun r => ?_
  have hc : Continuous (fun L : Ledger54 => L.2.1 r.1 r.2) := by fun_prop
  exact isOpen_lt ((hc.sub continuous_const).abs) continuous_const

private theorem abs_eq_of_sq_eq {x y : ℝ} (h : x ^ 2 = y ^ 2) : |x| = |y| :=
  nonneg_sq_eq_of_sq_eq |x| |y| (abs_nonneg x) (abs_nonneg y) (by simpa only [sq_abs] using h)

private theorem same_sign_rigidity {T S : Triple}
    (hT : ∀ a : Fin 3, Glennie.Frame (T a)) (hS : ∀ a : Fin 3, Glennie.Frame (S a))
    (hbox : T ∈ PBox) (hL : ledger54 T = ledger54 S)
    (hsign : (phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) :
    ∃ k : Glennie.CompactAutomorphism, mapAtoms k S = T := by
  have hTne : phiOf T ≠ 0 := by rcases hsign with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  obtain ⟨hsq, himp⟩ := nearby_core T S hT hS hbox hL hTne
  have hprod : (phiOf T - phiOf S) * (phiOf T + phiOf S) = 0 := by linarith [hsq]
  refine himp ?_
  rcases mul_eq_zero.mp hprod with h | h <;> rcases hsign with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

theorem nearby_sign_rigidity_unconditional :
    ∃ V : Set Ledger54, IsOpen V ∧ ledger54 flatBaseTriple ∈ V ∧
      ∀ T S : Triple, (∀ a : Fin 3, Glennie.Frame (T a)) →
        (∀ a : Fin 3, Glennie.Frame (S a)) → ledger54 T ∈ V →
        ledger54 T = ledger54 S →
        ((phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) →
        ∃ k : Glennie.CompactAutomorphism, mapAtoms k S = T :=
  ⟨LBox, isOpen_LBox, flatBaseTriple_mem_PBox,
    fun _ _ hT hS hTV hL hsign => same_sign_rigidity hT hS hTV hL hsign⟩

theorem nearby_fibres_two_orbits_unconditional :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧
      encode20 (ledger54 Glennie.Compact.Sections.flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Glennie.Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Glennie.Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (ledger54 (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (ledger54 (secNeg b)) = b) ∧
        (∀ b ∈ V, ledger54 (secPos b) = decode20 b) ∧
        (∀ b ∈ V, ledger54 (secNeg b) = decode20 b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) ∧
        (∀ b ∈ V, fibre54 b = autOrbit (secNeg b) ∪ autOrbit (secPos b)) ∧
        (∀ b ∈ V, Disjoint (autOrbit (secNeg b)) (autOrbit (secPos b))) ∧
        (∀ b ∈ V, fibre20 b = fibre54 b) := by
  obtain ⟨V0, hV0, hbase, secPos, secNeg, hcP, hcN, hfP, hfN, heP, heN, hlP, hlN, hpP, hpN⟩ :=
    Glennie.Compact.NativeFlatSections.native_flat_two_sections_full54
  have hbP : secPos (encode20 (ledger54 Glennie.Compact.Sections.flatBase)) ∈ PBox := by
    change ledger54 (secPos _) ∈ LBox
    rw [hlP _ hbase, decode_encode_frames _ flatBase_frames]
    exact flatBaseTriple_mem_PBox
  refine ⟨V0 ∩ secPos ⁻¹' PBox, hcP.isOpen_inter_preimage hV0 isOpen_PBox, ⟨hbase, hbP⟩,
    secPos, secNeg,
    hcP.mono Set.inter_subset_left, hcN.mono Set.inter_subset_left,
    (fun b hb => hfP b hb.1), (fun b hb => hfN b hb.1),
    (fun b hb => heP b hb.1), (fun b hb => heN b hb.1),
    (fun b hb => hlP b hb.1), (fun b hb => hlN b hb.1),
    (fun b hb => hpP b hb.1), (fun b hb => hpN b hb.1), ?_, ?_, ?_⟩
  · intro b hb
    have hb0 : b ∈ V0 := hb.1
    refine Set.Subset.antisymm ?_ ?_
    · rintro T ⟨hT, hTL⟩
      have hLP : ledger54 (secPos b) = ledger54 T := (hlP b hb0).trans hTL.symm
      have hLN : ledger54 (secNeg b) = ledger54 T := (hlN b hb0).trans hTL.symm
      obtain ⟨hsq, _⟩ := nearby_core (secPos b) T (hfP b hb0) hT hb.2 hLP (ne_of_gt (hpP b hb0))
      have hTP : T ∈ PBox := by change ledger54 T ∈ LBox; rw [← hLP]; exact hb.2
      rcases lt_trichotomy (phiOf T) 0 with hneg | hzero | hpos
      · exact Or.inl (same_sign_rigidity hT (hfN b hb0) hTP hLN.symm (Or.inl ⟨hneg, hpN b hb0⟩))
      · exfalso; have := hpP b hb0; nlinarith [hsq, hzero]
      · exact Or.inr (same_sign_rigidity hT (hfP b hb0) hTP hLP.symm (Or.inr ⟨hpos, hpP b hb0⟩))
    · rintro T (⟨g, rfl⟩ | ⟨g, rfl⟩)
      · exact ⟨fun a => frame_mapAtoms g (secNeg b) (hfN b hb0) a, by rw [ledger54_map, hlN b hb0]⟩
      · exact ⟨fun a => frame_mapAtoms g (secPos b) (hfP b hb0) a, by rw [ledger54_map, hlP b hb0]⟩
  · intro b hb
    rw [Set.disjoint_left]
    intro T hTN hTP
    linarith [phiOf_eq_of_mem_autOrbit hTN, phiOf_eq_of_mem_autOrbit hTP, hpN b hb.1, hpP b hb.1]
  · intro b hb
    exact Set.Subset.antisymm (fibre20_subset_fibre54 b)
      (fibre54_subset_fibre20 ⟨hfN b hb.1, hlN b hb.1⟩ (heN b hb.1))

theorem continuous_encode20 : Continuous (encode20 : Ledger54 → Fin 20 → ℝ) := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> dsimp [encode20, Glennie.Compact.Affine20.centred] <;> fun_prop

theorem phi_bounded_away_near_flat :
    ∃ V : Set Ledger54, IsOpen V ∧ ledger54 flatBaseTriple ∈ V ∧
      ∀ T : Triple, (∀ a : Fin 3, Glennie.Frame (T a)) → ledger54 T ∈ V →
        1 / 27 < |phiOf T| := by
  obtain ⟨V0, hV0, hbase, secPos, _, hcP, _, hfP, _, _, _, hlP, _, hpP, _⟩ :=
    Glennie.Compact.NativeFlatSections.native_flat_two_sections_full54
  let b0 := encode20 (ledger54 flatBaseTriple)
  have hbL : ledger54 (secPos b0) = ledger54 flatBaseTriple :=
    (hlP b0 hbase).trans (decode_encode_frames _ flatBase_frames)
  have hbP : secPos b0 ∈ PBox := by change ledger54 (secPos b0) ∈ LBox; rw [hbL]; exact flatBaseTriple_mem_PBox
  have hbPhi : 1 / 27 < |phiOf (secPos b0)| := by
    have hsq := (nearby_core (secPos b0) flatBaseTriple (hfP b0 hbase) flatBase_frames hbP hbL (ne_of_gt (hpP b0 hbase))).1
    rw [abs_eq_of_sq_eq hsq, phiOf_apply, show Glennie.phi (Glennie.encoder (flatBaseTriple 0))
      (Glennie.encoder (flatBaseTriple 1)) (Glennie.encoder (flatBaseTriple 2)) = -4 / 27 from flat_phi]
    norm_num
  let M : Set Triple := PBox ∩ {T | 1 / 27 < |phiOf T|}
  have hM : IsOpen M := isOpen_PBox.inter (isOpen_lt continuous_const continuous_phiOf.abs)
  refine ⟨encode20 ⁻¹' (V0 ∩ secPos ⁻¹' M),
    (hcP.isOpen_inter_preimage hV0 hM).preimage continuous_encode20, ⟨hbase, hbP, hbPhi⟩, ?_⟩
  intro T hT hTV
  let b := encode20 (ledger54 T)
  have hLP : ledger54 (secPos b) = ledger54 T :=
    (hlP b hTV.1).trans (decode_encode_frames T hT)
  have hsq := (nearby_core (secPos b) T (hfP b hTV.1) hT hTV.2.1 hLP (ne_of_gt (hpP b hTV.1))).1
  rw [← abs_eq_of_sq_eq hsq]
  exact hTV.2.2

def SameScoreSign (T S : Triple) : Prop :=
  (score T < 0 ∧ score S < 0) ∨ (0 < score T ∧ 0 < score S)

theorem nearby_q26_score_complete :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧
      encode20 (ledger54 flatBase) ∈ V ∧
      ∀ T S : Triple, (∀ a, Frame (T a)) → (∀ a, Frame (S a)) →
        encode20 (ledger54 T) ∈ V →
        score T ≠ 0 ∧
        ((∃ k : CompactAutomorphism, mapAtoms k S = T) ↔
          q26 T = q26 S ∧ SameScoreSign T S) := by
  obtain ⟨V, hVopen, hbase, secPos, secNeg, _, _, _, _, _, _, _, _, hpP, hpN, hcover, _, h20⟩ :=
    nearby_fibres_two_orbits_unconditional
  refine ⟨V, hVopen, hbase, fun T S hT hS hb => ?_⟩
  let b := encode20 (ledger54 T)
  have hTorbit : T ∈ autOrbit (secNeg b) ∨ T ∈ autOrbit (secPos b) := by
    change T ∈ autOrbit (secNeg b) ∪ autOrbit (secPos b)
    rw [← hcover b hb, ← h20 b hb]; exact ⟨hT, rfl⟩
  have hsN (X : Triple) (hX : X ∈ autOrbit (secNeg b)) : score X < 0 := by
    rw [score_eq_two_phi, phiOf_eq_of_mem_autOrbit hX]; linarith [hpN b hb]
  have hsP (X : Triple) (hX : X ∈ autOrbit (secPos b)) : 0 < score X := by
    rw [score_eq_two_phi, phiOf_eq_of_mem_autOrbit hX]; linarith [hpP b hb]
  have hscoreT : score T ≠ 0 := by
    rcases hTorbit with hN | hP
    · exact ne_of_lt (hsN T hN)
    · exact ne_of_gt (hsP T hP)
  refine ⟨hscoreT, ⟨?_, ?_⟩⟩
  · rintro ⟨k, hk⟩
    have hq : q26 T = q26 S := (q26_eq_iff_ledger54_eq T S hT hS).mpr (by rw [← hk, ledger54_map])
    have hscore : score T = score S := by
      rw [score_eq_two_phi, score_eq_two_phi, phiOf_eq_of_mem_autOrbit ⟨k, hk⟩]
    refine ⟨hq, ?_⟩
    rcases lt_trichotomy (score T) 0 with hN | hZ | hP
    · exact Or.inl ⟨hN, hscore ▸ hN⟩
    · exact False.elim (hscoreT hZ)
    · exact Or.inr ⟨hP, hscore ▸ hP⟩
  · rintro ⟨hq, hsign⟩
    have hL : ledger54 T = ledger54 S := (q26_eq_iff_ledger54_eq T S hT hS).mp hq
    have hSorbit : S ∈ autOrbit (secNeg b) ∨ S ∈ autOrbit (secPos b) := by
      change S ∈ autOrbit (secNeg b) ∪ autOrbit (secPos b)
      rw [← hcover b hb, ← h20 b hb]; exact ⟨hS, hL.symm ▸ rfl⟩
    rcases hTorbit with hTN | hTP <;> rcases hSorbit with hSN | hSP
    · change T ∈ autOrbit S; rw [autOrbit_eq_of_mem hSN]; exact hTN
    · rcases hsign with ⟨_, h⟩ | ⟨h, _⟩ <;> linarith [hsN T hTN, hsP S hSP]
    · rcases hsign with ⟨h, _⟩ | ⟨_, h⟩ <;> linarith [hsP T hTP, hsN S hSN]
    · change T ∈ autOrbit S; rw [autOrbit_eq_of_mem hSP]; exact hTP

end
end Glennie.Compact.NearbyOrbitsClosed
