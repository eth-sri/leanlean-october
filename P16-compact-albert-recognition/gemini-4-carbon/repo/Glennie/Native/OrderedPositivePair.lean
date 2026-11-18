module
public import Glennie.SectorModel
public import Glennie.Automorphism
public import Glennie.Theorems.Frames
public import Glennie.Native.PairReduction
public import Glennie.Compact.NativeWordTableBasisR01
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section
namespace Glennie
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike

abbrev SectorMatrix := Matrix (Fin 3) (Fin 3) ℂ
abbrev SectorUnitary := Matrix.unitaryGroup (Fin 3) ℂ

private theorem su_l (s : SectorUnitary) : (s : SectorMatrix).conjTranspose * (s : SectorMatrix) = 1 := s.2.1
private theorem su_r (s : SectorUnitary) : (s : SectorMatrix) * (s : SectorMatrix).conjTranspose = 1 := s.2.2

def leftMulEquiv (s : SectorUnitary) : SectorMatrix ≃ₗ[ℝ] SectorMatrix where
  toFun M := (s : SectorMatrix) * M
  invFun M := (s : SectorMatrix).conjTranspose * M
  left_inv M := by change (s : SectorMatrix).conjTranspose * ((s : SectorMatrix) * M) = M; rw [← Matrix.mul_assoc, su_l, Matrix.one_mul]
  right_inv M := by change (s : SectorMatrix) * ((s : SectorMatrix).conjTranspose * M) = M; rw [← Matrix.mul_assoc, su_r, Matrix.one_mul]
  map_add' := Matrix.mul_add _
  map_smul' _ _ := by simp only [Matrix.mul_smul, RingHom.id_apply]

def sectorLeftEquiv (s : SectorUnitary) : Albert ≃ₗ[ℝ] Albert :=
  compactSectorEquiv.trans (((LinearEquiv.refl ℝ ComplexHermitianCoordinates).prodCongr (leftMulEquiv s)).trans compactSectorEquiv.symm)

private theorem sectorLeftEquiv_eq (s : SectorUnitary) (x : Albert) :
    sectorLeftEquiv s x = sectorDecode (sectorComplexMatrix x) ((s : SectorMatrix) * hiddenMatrix x) := by
  change complexAlbertLinear (complexCoordinatesLinear x) + hiddenAlbert ((s : SectorMatrix) * hiddenMatrix x) = _
  simp only [sectorDecode, sectorComplexMatrix, matrixComplexCoordinates_inverse]

private theorem sectorLeftEquiv_complex (s : SectorUnitary) (x : Albert) :
    sectorComplexMatrix (sectorLeftEquiv s x) = sectorComplexMatrix x := by
  rw [sectorLeftEquiv_eq]; exact sectorComplexMatrix_decode _ _ (sectorComplexMatrix_isHermitian x)

private theorem sectorLeftEquiv_hidden (s : SectorUnitary) (x : Albert) :
    hiddenMatrix (sectorLeftEquiv s x) = (s : SectorMatrix) * hiddenMatrix x := by
  rw [sectorLeftEquiv_eq, hiddenMatrix_decode]

def sectorLeftSU3Automorphism (s : SectorUnitary) (hs : (s : SectorMatrix).det = 1) : CompactAutomorphism where
  equiv := sectorLeftEquiv s
  map_jordan x y := by
    have hadj : sectorAdjointAdjugate (s : SectorMatrix) = s := by
      have h := congrArg ((s : SectorMatrix).conjTranspose * ·) (Matrix.mul_adjugate (s : SectorMatrix))
      have ha : (s : SectorMatrix).adjugate = (s : SectorMatrix).conjTranspose := by
        simpa only [← Matrix.mul_assoc, su_l, Matrix.one_mul, hs, one_smul, Matrix.mul_one] using h
      simp only [sectorAdjointAdjugate, ha, Matrix.conjTranspose_conjTranspose]
    have hgram (M N : SectorMatrix) : ((s : SectorMatrix) * M).conjTranspose * ((s : SectorMatrix) * N) = M.conjTranspose * N := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (s : SectorMatrix).conjTranspose, su_l, Matrix.one_mul]
    have hpol (M N : SectorMatrix) : sectorPolarAdjugate ((s : SectorMatrix) * M) ((s : SectorMatrix) * N) =
        (s : SectorMatrix) * sectorPolarAdjugate M N := by
      have hmul (A B : SectorMatrix) : sectorAdjointAdjugate (A * B) = sectorAdjointAdjugate A * sectorAdjointAdjugate B := by
        simp only [sectorAdjointAdjugate, Matrix.adjugate_mul_distrib, Matrix.conjTranspose_mul]
      rw [sectorPolarAdjugate, ← Matrix.mul_add]
      simp only [hmul, hadj, sectorPolarAdjugate, Matrix.mul_sub]
    rw [← sectorDecode_encode (sectorLeftEquiv s (jordan x y)), ← sectorDecode_encode (jordan (sectorLeftEquiv s x) (sectorLeftEquiv s y))]
    congr 1
    · simp only [sectorLeftEquiv_complex, sectorComplexMatrix_jordan, sectorLeftEquiv_hidden, sectorProductComplex, hgram]
    · simp only [sectorLeftEquiv_hidden, hiddenMatrix_jordan, sectorLeftEquiv_complex, sectorProductHidden, hpol,
        Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc]
  map_trace x := by
    have h := congrArg Matrix.trace (sectorLeftEquiv_complex s x)
    simp only [trace_sectorComplexMatrix] at h; exact_mod_cast h

theorem sectorLeftSU3_hidden (s : SectorUnitary) (hs : (s : SectorMatrix).det = 1) (x : Albert) :
    hiddenMatrix ((sectorLeftSU3Automorphism s hs).equiv x) = (s : SectorMatrix) * hiddenMatrix x :=
  sectorLeftEquiv_hidden s x

theorem sectorLeftSU3_fixes_complex (s : SectorUnitary) (hs : (s : SectorMatrix).det = 1)
    (x : Albert) (hx : InComplexSector x) : (sectorLeftSU3Automorphism s hs).equiv x = x := by
  have hz : hiddenMatrix x = 0 := by
    rw [← show complexAlbertLinear (complexCoordinatesLinear x) = x from complexProjection_eq_self x hx]
    exact hiddenMatrix_complexAlbert _
  rw [← sectorDecode_encode ((sectorLeftSU3Automorphism s hs).equiv x), sectorLeftSU3_hidden, hz, Matrix.mul_zero]
  exact (congrArg (sectorDecode · 0) (sectorLeftEquiv_complex s x)).trans (hz ▸ sectorDecode_encode x)

theorem compactAutomorphism_projectorFrame (g : CompactAutomorphism) (x : Albert) (i : Fin 3) :
    g.equiv (projectorFrame x i) = projectorFrame (g.equiv x) i := by
  fin_cases i
  · change g.equiv ((1 / 2 : ℝ) • (jordan x x - x)) = (1 / 2 : ℝ) • (jordan (g.equiv x) (g.equiv x) - g.equiv x)
    rw [map_smul, map_sub, g.map_jordan]
  · change g.equiv (1 - jordan x x) = 1 - jordan (g.equiv x) (g.equiv x)
    rw [map_sub, g.map_unit, g.map_jordan]
  · change g.equiv ((1 / 2 : ℝ) • (jordan x x + x)) = (1 / 2 : ℝ) • (jordan (g.equiv x) (g.equiv x) + g.equiv x)
    rw [map_smul, map_add, g.map_jordan]

theorem diagonalAlbert_representation (x : Albert) (hx : IsDiagonal x) :
    x = diagonalAlbert x.d0 x.d1 x.d2 := by
  apply Albert.ext <;> simp [diagonalAlbert, hx.1, hx.2.1, hx.2.2]

theorem frame_projectors_diagonal (p : Fin 3 → Albert) (hp : Frame p)
    (he : IsDiagonal (encoder p)) (i : Fin 3) : IsDiagonal (p i) := by
  have hs : IsDiagonal (jordan (encoder p) (encoder p)) := by
    rw [diagonalAlbert_representation (encoder p) he]
    simp [IsDiagonal, diagonalAlbert, jordan_o01, jordan_o02, jordan_o12, octMul, octConj]
  fin_cases i <;> dsimp
  · rw [← frame_projector_first p hp]; simp [IsDiagonal, hs.1, hs.2.1, hs.2.2, he.1, he.2.1, he.2.2]
  · rw [← frame_projector_middle p hp]; simp [IsDiagonal, hs.1, hs.2.1, hs.2.2, unit, octScalar]
  · rw [← frame_projector_last p hp]; simp [IsDiagonal, hs.1, hs.2.1, hs.2.2, he.1, he.2.1, he.2.2]

end
end Glennie

namespace Glennie.NativeOrderedPositivePair
open Glennie Glennie.Compact.FlatBase
noncomputable section
set_option autoImplicit false

private theorem ordered_diagonal (x : Albert) (hx : IsDiagonal x)
    (ht : trace x = 0) (hn : inner x x = 2) (hc : newtonCubicNorm x = 0) :
    ∃ g : CompactAutomorphism, g.equiv x = flatXN := by
  have hn' : x.d0 ^ 2 + x.d1 ^ 2 + x.d2 ^ 2 = 2 := by
    rw [inner_self_coordinates] at hn; simpa [hx.1, hx.2.1, hx.2.2, octNormSq, Quaternion.normSq_def'] using hn
  have hc' : x.d0 * x.d1 * x.d2 = 0 := by
    rw [diagonalAlbert_representation x hx, newtonCubicNorm_coordinates] at hc
    simpa [diagonalAlbert, octNormSq, Quaternion.normSq_def', octMul, octConj, octRe] using hc
  have hrep := diagonalAlbert_representation x hx
  let A := realSwap01Automorphism; let B := realSwap02Automorphism; let C := A.comp (B.comp A)
  have hA (a b c : ℝ) : A.equiv (diagonalAlbert a b c) = diagonalAlbert b a c := by
    apply Albert.ext <;> simp [A, realSwap01Automorphism, diagonalAlbert, octConj]
  have hB (a b c : ℝ) : B.equiv (diagonalAlbert a b c) = diagonalAlbert c b a := by
    apply Albert.ext <;> simp [B, realSwap02Automorphism, diagonalAlbert, octConj]
  have hC (a b c : ℝ) : C.equiv (diagonalAlbert a b c) = diagonalAlbert a c b := by
    simp only [C, CompactAutomorphism.comp_apply, hA, hB]
  change x.d0 + x.d1 + x.d2 = 0 at ht
  rcases mul_eq_zero.mp hc' with hab | h2
  · rcases mul_eq_zero.mp hab with h0 | h1
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show x.d1 ^ 2 = 1 ^ 2 by rw [show x.d2 = -x.d1 by linarith, h0] at hn'; nlinarith) with hb1 | hb1
      · exact ⟨A, by rw [hrep, hA, h0, hb1, show x.d2 = -1 by linarith]; rfl⟩
      · exact ⟨C.comp B, by change C.equiv (B.equiv x) = _; rw [hrep, hB, hC, h0, hb1, show x.d2 = 1 by linarith]; rfl⟩
    · rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show x.d0 ^ 2 = 1 ^ 2 by rw [show x.d2 = -x.d0 by linarith, h1] at hn'; nlinarith) with ha1 | ha1
      · exact ⟨.refl, by change x = flatXN; rw [hrep, ha1, h1, show x.d2 = -1 by linarith]; rfl⟩
      · exact ⟨B, by rw [hrep, hB, ha1, h1, show x.d2 = 1 by linarith]; rfl⟩
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show x.d0 ^ 2 = 1 ^ 2 by rw [show x.d1 = -x.d0 by linarith, h2] at hn'; nlinarith) with ha1 | ha1
    · exact ⟨C, by rw [hrep, hC, ha1, show x.d1 = -1 by linarith, h2]; rfl⟩
    · exact ⟨C.comp A, by change C.equiv (A.equiv x) = _; rw [hrep, hA, hC, ha1, show x.d1 = 1 by linarith, h2]; rfl⟩

theorem native_ordered_positive_pair (p : Fin 3 → Albert) (hp : Frame p) (y : Albert) :
    ∃ g : CompactAutomorphism, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      (∀ i : Fin 3, g.equiv (p i) = flatFrameP i) ∧
      (g.equiv y).o01 = octScalar a ∧ (g.equiv y).o12 = octScalar b ∧
      InComplexSector (g.equiv y) := by
  obtain ⟨d0, hd0⟩ := native_diagonalization (encoder p)
  have hp' : Frame (fun i => d0.equiv (p i)) := d0.map_frame p hp
  obtain ⟨u, hu⟩ := ordered_diagonal _ (by rw [d0.encoder_map]; exact hd0)
    (frame_encoder_trace _ hp') (frame_encoder_norm _ hp') (frame_encoder_cubicNorm _ hp')
  let d := u.comp d0
  have hd : d.equiv (encoder p) = flatXN := by change u.equiv (d0.equiv (encoder p)) = _; rwa [← d0.encoder_map]
  obtain ⟨t, a, b, ha, hb, h01, h12⟩ := octTwoSlotsReal (d.equiv y).o01 (d.equiv y).o12
  obtain ⟨k, hk, h02⟩ := exists_octAutomorphism_to_complex (t.C (d.equiv y).o02)
  let g := k.compactAutomorphism.comp (t.compactAutomorphism.comp d)
  have hrel (s : OctRelatedTriple) : s.compactAutomorphism.equiv flatXN = flatXN := by
    change (⟨flatXN.d0, flatXN.d1, flatXN.d2, s.A flatXN.o01, s.C flatXN.o02, s.B flatXN.o12⟩ : Albert) = flatXN
    simp [flatXN, map_zero]
  have hgX : g.equiv (encoder p) = flatXN := by
    change k.compactAutomorphism.equiv (t.compactAutomorphism.equiv (d.equiv (encoder p))) = flatXN
    rw [hd, hrel, hrel]
  refine ⟨g, a, b, ha, hb, fun i => ?_, ?_, ?_, ?_⟩
  · have hfp : p i = projectorFrame (encoder p) i := by
      fin_cases i
      · exact (frame_projector_first p hp).symm
      · exact (frame_projector_middle p hp).symm
      · exact (frame_projector_last p hp).symm
    rw [hfp, compactAutomorphism_projectorFrame, hgX]; rfl
  · change k.A (t.A (d.equiv y).o01) = octScalar a; rw [h01, diagonalOctTriple_scalar k hk a]
  · change k.B (t.B (d.equiv y).o12) = octScalar b; rw [h12, hk.1, diagonalOctTriple_scalar k hk b]
  · change OctInComplex (k.A (t.A (d.equiv y).o01)) ∧ OctInComplex (k.C (t.C (d.equiv y).o02)) ∧ OctInComplex (k.B (t.B (d.equiv y).o12))
    rw [h01, h12, diagonalOctTriple_scalar k hk a, hk.1, diagonalOctTriple_scalar k hk b]
    exact ⟨octInComplex_scalar a, h02, octInComplex_scalar b⟩

end
end Glennie.NativeOrderedPositivePair
