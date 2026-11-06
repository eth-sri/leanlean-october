/- Actual determinant-one unitary transport of the compact native sector.
The action is (H,M) ↦ (g H g†, M g†). Every adjugate identity below
is polynomial; singular hidden matrices are included. -/
module
public import Glennie.SectorModel
public import Glennie.Automorphism
public import Glennie.SectorFactor
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section
namespace Glennie

abbrev SectorMatrix := Matrix (Fin 3) (Fin 3) ℂ
abbrev SectorUnitary := Matrix.unitaryGroup (Fin 3) ℂ


def sectorConjugation (g : SectorUnitary) (H : SectorMatrix) : SectorMatrix :=
  (g : SectorMatrix) * H * (g : SectorMatrix).conjTranspose

theorem su_right (g : SectorUnitary) :
    (g : SectorMatrix) * (g : SectorMatrix).conjTranspose = 1 := g.property.2


theorem sectorConjugation_hermitian (g : SectorUnitary) (H : SectorMatrix)
    (hH : H.IsHermitian) : (sectorConjugation g H).IsHermitian := by
  change (sectorConjugation g H).conjTranspose=sectorConjugation g H
  simp [sectorConjugation, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]

theorem sectorAdjointAdjugate_mul (M N : SectorMatrix) :
    sectorAdjointAdjugate (M*N)=sectorAdjointAdjugate M*sectorAdjointAdjugate N := by simp [sectorAdjointAdjugate, Matrix.adjugate_mul_distrib, Matrix.conjTranspose_mul]

theorem sectorAdjointAdjugate_unitary (g : SectorUnitary)
    (hd : (g : SectorMatrix).det=1) :
    sectorAdjointAdjugate (g : SectorMatrix).conjTranspose=(g : SectorMatrix).conjTranspose := by
  have hdt : (g : SectorMatrix).conjTranspose.det=1 := by simp_all
  have h := congrArg (fun A => (g : SectorMatrix)*A)
    (Matrix.mul_adjugate (g : SectorMatrix).conjTranspose)
  have ha : (g : SectorMatrix).conjTranspose.adjugate=(g : SectorMatrix) := by
    simpa [← Matrix.mul_assoc,su_right,Matrix.one_mul,hdt,one_smul,Matrix.mul_one] using h
  simp [sectorAdjointAdjugate,ha]

def sectorUnitaryAction (g : SectorUnitary) (x : Albert) : Albert :=
  sectorDecode (sectorConjugation g (sectorComplexMatrix x))
    (hiddenMatrix x*(g : SectorMatrix).conjTranspose)

@[simp] theorem sectorUnitaryAction_complex (g : SectorUnitary) (x : Albert) :
    sectorComplexMatrix (sectorUnitaryAction g x)=sectorConjugation g (sectorComplexMatrix x) :=
  sectorComplexMatrix_decode _ _ (sectorConjugation_hermitian g _ (sectorComplexMatrix_isHermitian x))
@[simp] theorem sectorUnitaryAction_hidden (g : SectorUnitary) (x : Albert) :
    hiddenMatrix (sectorUnitaryAction g x)=hiddenMatrix x*(g : SectorMatrix).conjTranspose :=
  hiddenMatrix_decode _ _

/-- Literal compact-sector inputs have no hidden coordinate, in the actual
sector equivalence rather than an assumed model conversion. -/
theorem hiddenMatrix_of_inComplex (x : Albert) (hx : InComplexSector x) : hiddenMatrix x=0 := by
  have h : complexAlbertLinear (complexCoordinatesLinear x)=x := complexProjection_eq_self x hx
  rw [← h]
  exact hiddenMatrix_complexAlbert _

end Glennie
