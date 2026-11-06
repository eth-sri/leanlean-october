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
noncomputable section

abbrev SectorMatrix := Matrix (Fin 3) (Fin 3) ℂ
abbrev SectorUnitary := Matrix.unitaryGroup (Fin 3) ℂ

private theorem su_right (g : SectorUnitary) :
    (g : SectorMatrix) * (g : SectorMatrix).conjTranspose = 1 := g.property.2

theorem sectorAdjointAdjugate_mul (M N : SectorMatrix) :
    sectorAdjointAdjugate (M*N)=sectorAdjointAdjugate M*sectorAdjointAdjugate N := by
  simp only [sectorAdjointAdjugate, Matrix.adjugate_mul_distrib, Matrix.conjTranspose_mul]

theorem sectorAdjointAdjugate_unitary (g : SectorUnitary)
    (hd : (g : SectorMatrix).det=1) :
    sectorAdjointAdjugate (g : SectorMatrix).conjTranspose=(g : SectorMatrix).conjTranspose := by
  have hdt : (g : SectorMatrix).conjTranspose.det=1 := by
    rw [Matrix.det_conjTranspose,hd]
    simp
  have h := congrArg (fun A : SectorMatrix => (g : SectorMatrix)*A)
    (Matrix.mul_adjugate (g : SectorMatrix).conjTranspose)
  have ha : (g : SectorMatrix).conjTranspose.adjugate=(g : SectorMatrix) := by
    simpa only [← Matrix.mul_assoc,su_right,Matrix.one_mul,hdt,one_smul,Matrix.mul_one] using h
  simp only [sectorAdjointAdjugate,ha]

/-- Literal compact-sector inputs have no hidden coordinate, in the actual
sector equivalence rather than an assumed model conversion. -/
theorem hiddenMatrix_of_inComplex (x : Albert) (hx : InComplexSector x) : hiddenMatrix x=0 := by
  have h : complexAlbertLinear (complexCoordinatesLinear x)=x := complexProjection_eq_self x hx
  rw [← h]
  exact hiddenMatrix_complexAlbert _

end
end Glennie
