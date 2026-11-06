module

public import Glennie.Native.PairReduction
public import Glennie.Native.RealConjugation
public import Glennie.Native.SectorLeftAction
public import Glennie.Compact.FlatBase

@[expose] public section
namespace Glennie
noncomputable section
set_option maxHeartbeats 2000000

theorem diagonalAlbert_representation (x : Albert) (hx : IsDiagonal x) :
    x = diagonalAlbert x.d0 x.d1 x.d2 := by
  apply Albert.ext <;> simp [diagonalAlbert, hx.1, hx.2.1, hx.2.2]

theorem jordan_diagonalAlbert (a b c d e f : ℝ) :
    jordan (diagonalAlbert a b c) (diagonalAlbert d e f) =
      diagonalAlbert (a * d) (b * e) (c * f) := by
  ext <;> simp [diagonalAlbert, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octMul, octConj,
    octNormSq, Quaternion.normSq_def']

theorem frame_projectors_diagonal (p : Fin 3 → Albert) (hp : Frame p)
    (he : IsDiagonal (encoder p)) (i : Fin 3) : IsDiagonal (p i) := by
  have hs : IsDiagonal (jordan (encoder p) (encoder p)) := by
    rw [diagonalAlbert_representation (encoder p) he, jordan_diagonalAlbert]
    simp [IsDiagonal, diagonalAlbert]
  fin_cases i <;> dsimp
  · rw [← frame_projector_first p hp]
    simp [IsDiagonal, hs.1, hs.2.1, hs.2.2, he.1, he.2.1, he.2.2]
  · rw [← frame_projector_middle p hp]
    simp [IsDiagonal, hs.1, hs.2.1, hs.2.2, unit, octScalar]
  · rw [← frame_projector_last p hp]
    simp [IsDiagonal, hs.1, hs.2.1, hs.2.2, he.1, he.2.1, he.2.2]

theorem diagonal_frame_encoder_cubic_zero (p : Fin 3 → Albert) (hp : Frame p)
    (he : IsDiagonal (encoder p)) :
    (encoder p).d0 * (encoder p).d1 * (encoder p).d2 = 0 := by
  have h := frame_encoder_cubicNorm p hp
  rw [diagonalAlbert_representation (encoder p) he, newtonCubicNorm_coordinates] at h
  simpa [diagonalAlbert, octNormSq, Quaternion.normSq_def', octMul, octConj, octRe] using h

theorem complexProjection_sub (x y : Albert) :
    complexProjection (x - y) = complexProjection x - complexProjection y := by
  ext <;> simp [complexProjection, complexOct, complexPart]

theorem complexProjection_add (x y : Albert) :
    complexProjection (x + y) = complexProjection x + complexProjection y := by
  ext <;> simp [complexProjection, complexOct, complexPart]

theorem frame_in_complexSector (p : Fin 3 → Albert) (hp : Frame p)
    (he : InComplexSector (encoder p)) (i : Fin 3) : p i ∈ complexSector := by
  have he' : encoder p ∈ complexSector := (complexSector_mem_iff _).mpr he
  have hs : jordan (encoder p) (encoder p) ∈ complexSector :=
    (complexSector_mem_iff _).mpr (complexSector_jordan _ _ he he)
  have hu : (1 : Albert) ∈ complexSector := by
    rw [complexSector_mem_iff]
    simp [InComplexSector, OctInComplex, unit, octScalar]
  fin_cases i <;> dsimp
  · rw [← frame_projector_first p hp]
    exact complexSector.smul_mem _ (complexSector.sub_mem hs he')
  · rw [← frame_projector_middle p hp]
    exact complexSector.sub_mem hu hs
  · rw [← frame_projector_last p hp]
    exact complexSector.smul_mem _ (complexSector.add_mem hs he')

theorem hiddenAlbert_cubicNorm (M : Matrix (Fin 3) (Fin 3) ℂ) :
    newtonCubicNorm (hiddenAlbert M) = 2 * M.det.re := by
  rw [newtonCubicNorm_coordinates]
  simp [hiddenAlbert, hiddenOct, octMul, octConj, octRe,
    Matrix.det_fin_three, Complex.mul_re, Complex.mul_im,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul]
  ring

theorem fe_complex_cubic (d e f : ℝ) (u v w : ℂ) :
    newtonCubicNorm (complexAlbert d e f u v w) = d * e * f -
      d * Complex.normSq w - e * Complex.normSq v - f * Complex.normSq u +
      2 * (u * w * star v).re := by
  rw [newtonCubicNorm_coordinates]
  simp [complexAlbert, complexOct, octNormSq, Quaternion.normSq_def', octMul, octConj, octRe,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem fe_complex_square_d0 (d e f : ℝ) (u v w : ℂ) :
    (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).d0 =
      d ^ 2 + Complex.normSq u + Complex.normSq v := by
  simp [jordan_d0, complexAlbert, complexOct, octDot_coordinates, octNormSq,
    Quaternion.normSq_def', Complex.normSq_apply]; ring

theorem fe_complex_square_d1 (d e f : ℝ) (u v w : ℂ) :
    (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).d1 =
      e ^ 2 + Complex.normSq u + Complex.normSq w := by
  simp [jordan_d1, complexAlbert, complexOct, octDot_coordinates, octNormSq,
    Quaternion.normSq_def', Complex.normSq_apply]; ring

theorem fe_complex_square_d2 (d e f : ℝ) (u v w : ℂ) :
    (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).d2 =
      f ^ 2 + Complex.normSq v + Complex.normSq w := by
  simp [jordan_d2, complexAlbert, complexOct, octDot_coordinates, octNormSq,
    Quaternion.normSq_def', Complex.normSq_apply]; ring

end
end Glennie

namespace Glennie.NativeOrderedPositivePair
open Glennie Glennie.Compact.FlatBase
noncomputable section
set_option autoImplicit false

private theorem six_diagonal_patterns (a b c : ℝ)
    (ht : a + b + c = 0) (hn : a^2 + b^2 + c^2 = 2) (hc : a*b*c = 0) :
    (a = 1 ∧ b = 0 ∧ c = -1) ∨
    (a = 1 ∧ b = -1 ∧ c = 0) ∨
    (a = 0 ∧ b = 1 ∧ c = -1) ∨
    (a = -1 ∧ b = 1 ∧ c = 0) ∨
    (a = -1 ∧ b = 0 ∧ c = 1) ∨
    (a = 0 ∧ b = -1 ∧ c = 1) := by
  have hz : a = 0 ∨ b = 0 ∨ c = 0 := by
    rcases mul_eq_zero.mp hc with hab | hc
    · exact (mul_eq_zero.mp hab).imp id Or.inl
    · exact Or.inr (Or.inr hc)
  rcases hz with rfl | rfl | rfl
  · have hc' : c = -b := by linarith
    rw [hc'] at hn
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show b^2 = (1 : ℝ)^2 by nlinarith) with rfl | rfl <;> simp [hc']
  · have hc' : c = -a := by linarith
    rw [hc'] at hn
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show a^2 = (1 : ℝ)^2 by nlinarith) with rfl | rfl <;> simp [hc']
  · have hb' : b = -a := by linarith
    rw [hb'] at hn
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show a^2 = (1 : ℝ)^2 by nlinarith) with rfl | rfl <;> simp [hb']

private theorem swap01_diagonal (a b c : ℝ) :
    realSwap01Automorphism.equiv (diagonalAlbert a b c) = diagonalAlbert b a c := by
  change realConjugateAlbert realSwap01 (diagonalAlbert a b c) = _
  rw [realSwap01_coordinates]
  simp [diagonalAlbert, octConj]

private theorem swap02_diagonal (a b c : ℝ) :
    realSwap02Automorphism.equiv (diagonalAlbert a b c) = diagonalAlbert c b a := by
  change realConjugateAlbert realSwap02 (diagonalAlbert a b c) = _
  rw [realSwap02_coordinates]
  simp [diagonalAlbert, octConj]

private theorem ordered_diagonal (x : Albert) (hx : IsDiagonal x)
    (ht : trace x = 0) (hn : inner x x = 2) (hc : x.d0*x.d1*x.d2 = 0) :
    ∃ g : CompactAutomorphism, g.equiv x = flatXN := by
  have hn' : x.d0^2 + x.d1^2 + x.d2^2 = 2 := by
    rw [inner_self_coordinates] at hn
    simp only [hx.1, hx.2.1, hx.2.2] at hn
    norm_num [octNormSq, Quaternion.normSq_def'] at hn
    exact hn
  have hrep := diagonalAlbert_representation x hx
  let A := realSwap01Automorphism
  let B := realSwap02Automorphism
  let C := A.comp (B.comp A)
  have hC (a b c : ℝ) : C.equiv (diagonalAlbert a b c) = diagonalAlbert a c b := by
    dsimp only [C, A, B]
    rw [CompactAutomorphism.comp_apply, CompactAutomorphism.comp_apply,
      swap01_diagonal, swap02_diagonal, swap01_diagonal]
  rcases six_diagonal_patterns x.d0 x.d1 x.d2 ht hn' hc with
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact ⟨CompactAutomorphism.refl, by change x = flatXN; rw [hrep, h0, h1, h2]; rfl⟩
  · exact ⟨C, by rw [hrep, hC, h0, h1, h2]; rfl⟩
  · exact ⟨A, by change A.equiv x = _; rw [hrep, swap01_diagonal, h0, h1, h2]; rfl⟩
  · exact ⟨C.comp A, by change C.equiv (A.equiv x) = _; rw [hrep, swap01_diagonal, hC, h0, h1, h2]; rfl⟩
  · exact ⟨B, by change B.equiv x = _; rw [hrep, swap02_diagonal, h0, h1, h2]; rfl⟩
  · exact ⟨C.comp B, by change C.equiv (B.equiv x) = _; rw [hrep, swap02_diagonal, hC, h0, h1, h2]; rfl⟩

private theorem frame_as_projector (p : Fin 3 → Albert) (hp : Frame p) :
    p = projectorFrame (encoder p) := by
  funext i; fin_cases i
  · exact (frame_projector_first p hp).symm
  · exact (frame_projector_middle p hp).symm
  · exact (frame_projector_last p hp).symm

/-- A genuine native frame is carried to the ORIGINAL ordered first frame. -/
theorem native_ordered_frame (p : Fin 3 → Albert) (hp : Frame p) :
    ∃ g : CompactAutomorphism, g.equiv (encoder p) = flatXN ∧
      ∀ i : Fin 3, g.equiv (p i) = flatFrameP i := by
  obtain ⟨d, hd⟩ := native_diagonalization (encoder p)
  let p' := fun i => d.equiv (p i)
  have hp' : Frame p' := d.map_frame p hp
  have he : IsDiagonal (encoder p') := by rw [d.encoder_map]; exact hd
  obtain ⟨u, hu⟩ := ordered_diagonal (encoder p') he
    (frame_encoder_trace p' hp') (frame_encoder_norm p' hp')
    (diagonal_frame_encoder_cubic_zero p' hp' he)
  let g := u.comp d
  have hg : g.equiv (encoder p) = flatXN := by
    change u.equiv (d.equiv (encoder p)) = flatXN; rw [← d.encoder_map]; exact hu
  exact ⟨g, hg, fun i => by rw [frame_as_projector p hp, compactAutomorphism_projectorFrame, hg]; rfl⟩

private theorem relatedTriple_flatXN (t : OctRelatedTriple) :
    t.compactAutomorphism.equiv flatXN = flatXN := by
  change (⟨flatXN.d0, flatXN.d1, flatXN.d2,
    t.A flatXN.o01, t.C flatXN.o02, t.B flatXN.o12⟩ : Albert) = flatXN
  simp [flatXN, map_zero]

/-- Retain the nonnegative real 01/12 slots actually constructed by PairReduction. -/
theorem native_ordered_positive_pair (p : Fin 3 → Albert) (hp : Frame p) (y : Albert) :
    ∃ g : CompactAutomorphism, ∃ a b : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧
      (∀ i : Fin 3, g.equiv (p i) = flatFrameP i) ∧
      (g.equiv y).o01 = octScalar a ∧ (g.equiv y).o12 = octScalar b ∧
      InComplexSector (g.equiv y) := by
  obtain ⟨d, hd, _⟩ := native_ordered_frame p hp
  let z := d.equiv y
  obtain ⟨t, a, b, ha, hb, h01, h12⟩ := octTwoSlotsReal z.o01 z.o12
  obtain ⟨k, hk, h02⟩ := exists_octAutomorphism_to_complex (t.C z.o02)
  let g := k.compactAutomorphism.comp (t.compactAutomorphism.comp d)
  have hgX : g.equiv (encoder p) = flatXN := by
    change k.compactAutomorphism.equiv
      (t.compactAutomorphism.equiv (d.equiv (encoder p))) = flatXN
    rw [hd, relatedTriple_flatXN, relatedTriple_flatXN]
  refine ⟨g, a, b, ha, hb,
    fun i => by rw [frame_as_projector p hp, compactAutomorphism_projectorFrame, hgX]; rfl,
    ?_, ?_, ?_⟩
  · change k.A (t.A z.o01) = octScalar a
    rw [h01, diagonalOctTriple_scalar k hk a]
  · change k.B (t.B z.o12) = octScalar b
    rw [h12, hk.1, diagonalOctTriple_scalar k hk b]
  · change OctInComplex (k.A (t.A z.o01)) ∧
      OctInComplex (k.C (t.C z.o02)) ∧ OctInComplex (k.B (t.B z.o12))
    rw [h01, h12, diagonalOctTriple_scalar k hk a, hk.1,
      diagonalOctTriple_scalar k hk b]
    exact ⟨octInComplex_scalar a, h02, octInComplex_scalar b⟩

end
end Glennie.NativeOrderedPositivePair
