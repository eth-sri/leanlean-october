module

public import Glennie.SectorModel
public import Glennie.Automorphism
public import Glennie.SectorFactor
public import Glennie.Theorems.ProjectorFrame
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

namespace Glennie
noncomputable section

set_option autoImplicit false

abbrev SectorMatrix := Matrix (Fin 3) (Fin 3) ℂ
abbrev SectorUnitary := Matrix.unitaryGroup (Fin 3) ℂ

theorem sectorAdjointAdjugate_mul (M N : SectorMatrix) :
    sectorAdjointAdjugate (M * N) = sectorAdjointAdjugate M * sectorAdjointAdjugate N := by
  simp only [sectorAdjointAdjugate, Matrix.adjugate_mul_distrib, Matrix.conjTranspose_mul]

theorem hiddenMatrix_of_inComplex (x : Albert) (hx : InComplexSector x) : hiddenMatrix x = 0 := by
  have h : complexAlbertLinear (complexCoordinatesLinear x) = x := complexProjection_eq_self x hx
  rw [← h]
  exact hiddenMatrix_complexAlbert _

/-- Real left multiplication by an actual unitary matrix, with its explicit inverse.
Exposed because it is data in the exported automorphism constructor. -/
def leftMulEquiv (s : SectorUnitary) : SectorMatrix ≃ₗ[ℝ] SectorMatrix where
  toFun M := (s : SectorMatrix) * M
  invFun M := (s : SectorMatrix).conjTranspose * M
  left_inv M := by
    change (s : SectorMatrix).conjTranspose * ((s : SectorMatrix) * M) = M
    have h : (s : SectorMatrix).conjTranspose * (s : SectorMatrix) = 1 := s.property.1
    rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  right_inv M := by
    change (s : SectorMatrix) * ((s : SectorMatrix).conjTranspose * M) = M
    have h : (s : SectorMatrix) * (s : SectorMatrix).conjTranspose = 1 := s.property.2
    rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  map_add' M N := Matrix.mul_add _ _ _
  map_smul' r M := by simp only [Matrix.mul_smul, RingHom.id_apply]

/-- Conjugate that real equivalence through the actual native sector coordinates. -/
def sectorLeftEquiv (s : SectorUnitary) : Albert ≃ₗ[ℝ] Albert :=
  compactSectorEquiv.trans
    (((LinearEquiv.refl ℝ ComplexHermitianCoordinates).prodCongr (leftMulEquiv s)).trans
      compactSectorEquiv.symm)

private theorem sectorLeftEquiv_apply (s : SectorUnitary) (x : Albert) :
    sectorLeftEquiv s x =
      sectorDecode (sectorComplexMatrix x) ((s : SectorMatrix) * hiddenMatrix x) := by
  change complexAlbertLinear (complexCoordinatesLinear x) +
      hiddenAlbert ((s : SectorMatrix) * hiddenMatrix x) = _
  simp only [sectorDecode, sectorComplexMatrix, matrixComplexCoordinates_inverse]

private theorem sectorLeftEquiv_complex (s : SectorUnitary) (x : Albert) :
    sectorComplexMatrix (sectorLeftEquiv s x) = sectorComplexMatrix x := by
  rw [sectorLeftEquiv_apply]
  exact sectorComplexMatrix_decode _ _ (sectorComplexMatrix_isHermitian x)

private theorem sectorLeftEquiv_hidden (s : SectorUnitary) (x : Albert) :
    hiddenMatrix (sectorLeftEquiv s x) = (s : SectorMatrix) * hiddenMatrix x := by
  rw [sectorLeftEquiv_apply, hiddenMatrix_decode]

private theorem left_gram (s : SectorUnitary) (M N : SectorMatrix) :
    ((s : SectorMatrix) * M).conjTranspose * ((s : SectorMatrix) * N) =
      M.conjTranspose * N := by
  have h : (s : SectorMatrix).conjTranspose * (s : SectorMatrix) = 1 := s.property.1
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (s : SectorMatrix).conjTranspose,
    h, Matrix.one_mul]

private theorem adjointAdjugate_left_unitary (s : SectorUnitary)
    (hs : (s : SectorMatrix).det = 1) : sectorAdjointAdjugate (s : SectorMatrix) = s := by
  have h := congrArg (fun A : SectorMatrix => (s : SectorMatrix).conjTranspose * A)
    (Matrix.mul_adjugate (s : SectorMatrix))
  have hl : (s : SectorMatrix).conjTranspose * (s : SectorMatrix) = 1 := s.property.1
  have ha : (s : SectorMatrix).adjugate = (s : SectorMatrix).conjTranspose := by
    simpa only [← Matrix.mul_assoc, hl, Matrix.one_mul, hs, one_smul, Matrix.mul_one] using h
  simp only [sectorAdjointAdjugate, ha, Matrix.conjTranspose_conjTranspose]

private theorem polarAdjugate_left (s : SectorUnitary)
    (hs : (s : SectorMatrix).det = 1) (M N : SectorMatrix) :
    sectorPolarAdjugate ((s : SectorMatrix) * M) ((s : SectorMatrix) * N) =
      (s : SectorMatrix) * sectorPolarAdjugate M N := by
  rw [sectorPolarAdjugate, ← Matrix.mul_add]
  simp only [sectorAdjointAdjugate_mul, adjointAdjugate_left_unitary s hs,
    sectorPolarAdjugate, Matrix.mul_sub]

private theorem productComplex_left (s : SectorUnitary) (H M K N : SectorMatrix) :
    sectorProductComplex H ((s : SectorMatrix) * M) K ((s : SectorMatrix) * N) =
      sectorProductComplex H M K N := by
  simp only [sectorProductComplex, left_gram]

private theorem productHidden_left (s : SectorUnitary)
    (hs : (s : SectorMatrix).det = 1) (H M K N : SectorMatrix) :
    sectorProductHidden H ((s : SectorMatrix) * M) K ((s : SectorMatrix) * N) =
      (s : SectorMatrix) * sectorProductHidden H M K N := by
  simp only [sectorProductHidden, polarAdjugate_left s hs,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc]

private theorem native_sector_ext (x y : Albert)
    (hH : sectorComplexMatrix x = sectorComplexMatrix y)
    (hM : hiddenMatrix x = hiddenMatrix y) : x = y := by
  calc
    x = sectorDecode (sectorComplexMatrix x) (hiddenMatrix x) := (sectorDecode_encode x).symm
    _ = sectorDecode (sectorComplexMatrix y) (hiddenMatrix y) := by rw [hH, hM]
    _ = y := sectorDecode_encode y

theorem sectorLeftEquiv_jordan (s : SectorUnitary)
    (hs : (s : SectorMatrix).det = 1) (x y : Albert) :
    sectorLeftEquiv s (jordan x y) = jordan (sectorLeftEquiv s x) (sectorLeftEquiv s y) := by
  apply native_sector_ext
  · simp only [sectorLeftEquiv_complex, sectorComplexMatrix_jordan,
      sectorLeftEquiv_hidden, productComplex_left]
  · simp only [sectorLeftEquiv_hidden, hiddenMatrix_jordan,
      sectorLeftEquiv_complex, productHidden_left s hs]

theorem sectorLeftEquiv_trace (s : SectorUnitary) (x : Albert) :
    trace (sectorLeftEquiv s x) = trace x := by
  have h := congrArg (fun H : SectorMatrix => H.trace) (sectorLeftEquiv_complex s x)
  simp only [trace_sectorComplexMatrix] at h
  exact_mod_cast h

/-- The actual native left SU3 action fixes the visible sector and multiplies
the hidden matrix on the left. -/
def sectorLeftSU3Automorphism (s : SectorUnitary)
    (hs : (s : SectorMatrix).det = 1) : CompactAutomorphism where
  equiv := sectorLeftEquiv s
  map_jordan := sectorLeftEquiv_jordan s hs
  map_trace := sectorLeftEquiv_trace s

theorem sectorLeftSU3_complex (s : SectorUnitary) (hs : (s : SectorMatrix).det = 1)
    (x : Albert) :
    sectorComplexMatrix ((sectorLeftSU3Automorphism s hs).equiv x) = sectorComplexMatrix x :=
  sectorLeftEquiv_complex s x

theorem sectorLeftSU3_hidden (s : SectorUnitary) (hs : (s : SectorMatrix).det = 1)
    (x : Albert) :
    hiddenMatrix ((sectorLeftSU3Automorphism s hs).equiv x) = (s : SectorMatrix) * hiddenMatrix x :=
  sectorLeftEquiv_hidden s x

theorem sectorLeftSU3_fixes_complex (s : SectorUnitary) (hs : (s : SectorMatrix).det = 1)
    (x : Albert) (hx : InComplexSector x) : (sectorLeftSU3Automorphism s hs).equiv x = x := by
  apply native_sector_ext
  · exact sectorLeftSU3_complex s hs x
  · rw [sectorLeftSU3_hidden, hiddenMatrix_of_inComplex x hx, Matrix.mul_zero]

/-- Every actual product automorphism commutes with the ordered projector
polynomials, with no spectral, frame, or relabel hypothesis. -/
theorem compactAutomorphism_projectorFrame (g : CompactAutomorphism) (x : Albert) (i : Fin 3) :
    g.equiv (projectorFrame x i) = projectorFrame (g.equiv x) i := by
  fin_cases i
  · change g.equiv ((1 / 2 : ℝ) • (jordan x x - x)) =
      (1 / 2 : ℝ) • (jordan (g.equiv x) (g.equiv x) - g.equiv x)
    rw [map_smul, map_sub, g.map_jordan]
  · change g.equiv (1 - jordan x x) = 1 - jordan (g.equiv x) (g.equiv x)
    rw [map_sub, g.map_unit, g.map_jordan]
  · change g.equiv ((1 / 2 : ℝ) • (jordan x x + x)) =
      (1 / 2 : ℝ) • (jordan (g.equiv x) (g.equiv x) + g.equiv x)
    rw [map_smul, map_add, g.map_jordan]

end
end Glennie
