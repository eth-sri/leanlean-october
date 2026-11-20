module

public import Glennie.Theorems.SectorTransport
public import Glennie.Theorems.ProjectorFrame
@[expose] public section

namespace Glennie
noncomputable section

set_option autoImplicit false

/-- Transport unitary left multiplication through the native sector coordinates. -/
def sectorLeftEquiv (s : SectorUnitary) : Albert ≃ₗ[ℝ] Albert :=
  (compactSectorEquiv.trans ((LinearEquiv.refl ℝ _).prodCongr
    (Units.mulLeftLinearEquiv ℝ SectorMatrix (Unitary.toUnits s)))).trans compactSectorEquiv.symm

private theorem sectorLeftEquiv_coords (s : SectorUnitary) (x : Albert) :
    compactSectorEquiv (sectorLeftEquiv s x) = (complexCoordinatesLinear x, (s : SectorMatrix) * hiddenMatrix x) :=
  compactSectorEquiv.apply_symm_apply _

private theorem sectorLeftEquiv_complex (s : SectorUnitary) (x : Albert) :
    sectorComplexMatrix (sectorLeftEquiv s x) = sectorComplexMatrix x :=
  congrArg (complexHermitianMatrix ∘ Prod.fst) (sectorLeftEquiv_coords s x)

private theorem sectorLeftEquiv_hidden (s : SectorUnitary) (x : Albert) :
    hiddenMatrix (sectorLeftEquiv s x) = (s : SectorMatrix) * hiddenMatrix x :=
  congrArg Prod.snd (sectorLeftEquiv_coords s x)

private theorem left_gram (s : SectorUnitary) (M N : SectorMatrix) :
    ((s : SectorMatrix) * M).conjTranspose * ((s : SectorMatrix) * N) =
      M.conjTranspose * N := by
  have h : (s : SectorMatrix).conjTranspose * (s : SectorMatrix) = 1 := s.property.1
  simp only [Matrix.conjTranspose_mul, mul_assoc]
  rw [← mul_assoc _ (s : SectorMatrix), h, one_mul]

private theorem polarAdjugate_left (s : SectorUnitary)
    (hs : (s : SectorMatrix).det = 1) (M N : SectorMatrix) :
    sectorPolarAdjugate ((s : SectorMatrix) * M) ((s : SectorMatrix) * N) =
      (s : SectorMatrix) * sectorPolarAdjugate M N := by
  rw [sectorPolarAdjugate, ← Matrix.mul_add]
  simp only [sectorAdjointAdjugate_mul, sectorAdjointAdjugate_unitary s hs,
    sectorPolarAdjugate, Matrix.mul_sub]

/-- The determinant-one unitary left action is a native automorphism. -/
def sectorLeftSU3Automorphism (s : SectorUnitary)
    (hs : (s : SectorMatrix).det = 1) : CompactAutomorphism where
  equiv := sectorLeftEquiv s
  map_jordan x y := by
    apply sector_ext
    · simp only [sectorLeftEquiv_complex, sectorComplexMatrix_jordan,
        sectorLeftEquiv_hidden, sectorProductComplex, left_gram]
    · simp [sectorLeftEquiv_hidden, hiddenMatrix_jordan, sectorLeftEquiv_complex,
        sectorProductHidden, polarAdjugate_left s hs, Matrix.mul_add, mul_assoc]
  map_trace x := by
    simpa only [trace_sectorComplexMatrix, Complex.ofReal_re] using
      congrArg (fun H : SectorMatrix => H.trace.re) (sectorLeftEquiv_complex s x)

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
  apply sector_ext
  · exact sectorLeftSU3_complex s hs x
  · rw [sectorLeftSU3_hidden, hiddenMatrix_of_inComplex x hx, Matrix.mul_zero]

end
end Glennie
