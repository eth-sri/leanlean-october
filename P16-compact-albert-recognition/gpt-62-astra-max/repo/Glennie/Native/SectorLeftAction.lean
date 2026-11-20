module

public import Glennie.Theorems.SectorTransport
public import Glennie.Theorems.ProjectorFrame

@[expose] public section

namespace Glennie
noncomputable section

set_option autoImplicit false

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
      sectorDecode (sectorComplexMatrix x) ((s : SectorMatrix) * hiddenMatrix x) := rfl

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
  calc
    _ = M.conjTranspose * (((s : SectorMatrix).conjTranspose * (s : SectorMatrix)) * N) := by
      simp [Matrix.mul_assoc]
    _ = M.conjTranspose * N := by
      have h : (s : SectorMatrix).conjTranspose * (s : SectorMatrix) = 1 := s.property.1
      simp_all

private theorem adjointAdjugate_left_unitary (s : SectorUnitary)
    (hs : (s : SectorMatrix).det = 1) : sectorAdjointAdjugate (s : SectorMatrix) = s := by
  have hds : ((star s : SectorUnitary) : SectorMatrix).det = 1 := by
    change (s : SectorMatrix).conjTranspose.det = 1
    simp_all
  have h := sectorAdjointAdjugate_unitary (star s) hds
  change sectorAdjointAdjugate ((s : SectorMatrix).conjTranspose.conjTranspose) =
    (s : SectorMatrix).conjTranspose.conjTranspose at h
  simp_all

private theorem polarAdjugate_left (s : SectorUnitary)
    (hs : (s : SectorMatrix).det = 1) (M N : SectorMatrix) :
    sectorPolarAdjugate ((s : SectorMatrix) * M) ((s : SectorMatrix) * N) =
      (s : SectorMatrix) * sectorPolarAdjugate M N := by
  simp [sectorPolarAdjugate, ← Matrix.mul_add, sectorAdjointAdjugate_mul, adjointAdjugate_left_unitary s hs, Matrix.mul_sub]

private theorem productComplex_left (s : SectorUnitary) (H M K N : SectorMatrix) :
    sectorProductComplex H ((s : SectorMatrix) * M) K ((s : SectorMatrix) * N) =
      sectorProductComplex H M K N := by
  grind [sectorProductComplex, left_gram]

private theorem productHidden_left (s : SectorUnitary)
    (hs : (s : SectorMatrix).det = 1) (H M K N : SectorMatrix) :
    sectorProductHidden H ((s : SectorMatrix) * M) K ((s : SectorMatrix) * N) =
      (s : SectorMatrix) * sectorProductHidden H M K N := by
  simp_all [sectorProductHidden, polarAdjugate_left, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc]

private theorem native_sector_ext (x y : Albert)
    (hH : sectorComplexMatrix x = sectorComplexMatrix y)
    (hM : hiddenMatrix x = hiddenMatrix y) : x = y := by
  grind [sectorComplexMatrix, hiddenMatrix, sectorDecode, sectorDecode_encode]

theorem sectorLeftEquiv_jordan (s : SectorUnitary)
    (hs : (s : SectorMatrix).det = 1) (x y : Albert) :
    sectorLeftEquiv s (jordan x y) = jordan (sectorLeftEquiv s x) (sectorLeftEquiv s y) := by
  grind [sectorLeftEquiv, jordan, native_sector_ext, sectorLeftEquiv_complex, sectorComplexMatrix_jordan, sectorLeftEquiv_hidden, productComplex_left, hiddenMatrix_jordan, productHidden_left]

theorem sectorLeftEquiv_trace (s : SectorUnitary) (x : Albert) :
    trace (sectorLeftEquiv s x) = trace x := by
  have h := congrArg (fun H : SectorMatrix => H.trace) (sectorLeftEquiv_complex s x)
  simp_all [trace_sectorComplexMatrix]

/-- The actual native left SU3 action fixes the visible sector and multiplies
the hidden matrix on the left. Unitarity and determinant one are the only caller
restrictions; product and trace preservation are proved, including singular
hidden matrices, with the original HALF and positive adjoint-adjugate product. -/
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
  grind [native_sector_ext, sectorLeftSU3_complex, sectorLeftSU3_hidden, hiddenMatrix_of_inComplex]

end
end Glennie
