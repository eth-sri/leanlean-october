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

abbrev SectorUnitary := Matrix.unitaryGroup (Fin 3) ℂ

set_option maxHeartbeats 2000000

theorem sectorAdjointAdjugate_mul (M N : SectorMatrix) :
    sectorAdjointAdjugate (M*N)=sectorAdjointAdjugate M*sectorAdjointAdjugate N := by
  simp only [sectorAdjointAdjugate, Matrix.adjugate_mul_distrib, Matrix.conjTranspose_mul]

theorem sectorAdjointAdjugate_unitary (g : SectorUnitary)
    (hd : (g : SectorMatrix).det = 1) : sectorAdjointAdjugate (g : SectorMatrix) = g := by
  have hg : (g : SectorMatrix).conjTranspose * (g : SectorMatrix) = 1 := g.property.1
  have h := congrArg ((g : SectorMatrix).conjTranspose * ·) (Matrix.mul_adjugate (g : SectorMatrix))
  simp only [hd, one_smul, ← mul_assoc, hg, one_mul] at h
  simp [sectorAdjointAdjugate, h]

end
end Glennie
