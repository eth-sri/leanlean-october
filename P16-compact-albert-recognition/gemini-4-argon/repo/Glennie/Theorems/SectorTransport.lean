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

set_option maxHeartbeats 2000000

def sectorConjugation (g : SectorUnitary) (H : SectorMatrix) : SectorMatrix :=
  (g : SectorMatrix) * H * (g : SectorMatrix).conjTranspose

private theorem su_left (g : SectorUnitary) :
    (g : SectorMatrix).conjTranspose * (g : SectorMatrix) = 1 := g.property.1
private theorem su_right (g : SectorUnitary) :
    (g : SectorMatrix) * (g : SectorMatrix).conjTranspose = 1 := g.property.2
private theorem su_cancel (g : SectorUnitary) (H : SectorMatrix) :
    (g : SectorMatrix).conjTranspose * ((g : SectorMatrix) * H) = H := by
  rw [← Matrix.mul_assoc, su_left, Matrix.one_mul]

@[simp] theorem sectorConjugation_add (g : SectorUnitary) (H K : SectorMatrix) :
    sectorConjugation g (H+K)=sectorConjugation g H+sectorConjugation g K := by
  simp [sectorConjugation, Matrix.mul_add, Matrix.add_mul]
@[simp] theorem sectorConjugation_sub (g : SectorUnitary) (H K : SectorMatrix) :
    sectorConjugation g (H-K)=sectorConjugation g H-sectorConjugation g K := by
  simp [sectorConjugation, Matrix.mul_sub, Matrix.sub_mul]
@[simp] theorem sectorConjugation_smul (g : SectorUnitary) (a : ℂ) (H : SectorMatrix) :
    sectorConjugation g (a • H)=a • sectorConjugation g H := by
  simp [sectorConjugation, Matrix.mul_smul, Matrix.smul_mul]
@[simp] theorem sectorConjugation_real_smul (g : SectorUnitary) (a : ℝ) (H : SectorMatrix) :
    sectorConjugation g (a • H)=a • sectorConjugation g H := by
  simp [sectorConjugation, Matrix.mul_smul, Matrix.smul_mul]
@[simp] theorem sectorConjugation_one (g : SectorUnitary) : sectorConjugation g 1=1 := by
  simp only [sectorConjugation, Matrix.mul_one, su_right]
@[simp] theorem sectorConjugation_mul (g : SectorUnitary) (H K : SectorMatrix) :
    sectorConjugation g (H*K)=sectorConjugation g H*sectorConjugation g K := by
  simp only [sectorConjugation, Matrix.mul_assoc, su_cancel]
@[simp] theorem sectorConjugation_trace (g : SectorUnitary) (H : SectorMatrix) :
    (sectorConjugation g H).trace=H.trace := by
  rw [sectorConjugation, Matrix.trace_mul_cycle, su_left, Matrix.one_mul]

theorem sectorConjugation_hermitian (g : SectorUnitary) (H : SectorMatrix)
    (hH : H.IsHermitian) : (sectorConjugation g H).IsHermitian := by
  change (sectorConjugation g H).conjTranspose=sectorConjugation g H
  simp only [sectorConjugation, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]

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

def sectorUnitaryAction (g : SectorUnitary) (x : Albert) : Albert :=
  sectorDecode (sectorConjugation g (sectorComplexMatrix x))
    (hiddenMatrix x*(g : SectorMatrix).conjTranspose)

@[simp] theorem sectorUnitaryAction_complex (g : SectorUnitary) (x : Albert) :
    sectorComplexMatrix (sectorUnitaryAction g x)=sectorConjugation g (sectorComplexMatrix x) :=
  sectorComplexMatrix_decode _ _ (sectorConjugation_hermitian g _ (sectorComplexMatrix_isHermitian x))
@[simp] theorem sectorUnitaryAction_hidden (g : SectorUnitary) (x : Albert) :
    hiddenMatrix (sectorUnitaryAction g x)=hiddenMatrix x*(g : SectorMatrix).conjTranspose :=
  hiddenMatrix_decode _ _

private theorem sector_native_ext (x y : Albert)
    (hH : sectorComplexMatrix x=sectorComplexMatrix y) (hM : hiddenMatrix x=hiddenMatrix y) : x=y := by
  calc
    x = sectorDecode (sectorComplexMatrix x) (hiddenMatrix x) := (sectorDecode_encode x).symm
    _ = sectorDecode (sectorComplexMatrix y) (hiddenMatrix y) := by rw [hH,hM]
    _ = y := sectorDecode_encode y

@[simp] theorem sectorUnitaryAction_inverse (g : SectorUnitary) (x : Albert) :
    sectorUnitaryAction (star g) (sectorUnitaryAction g x)=x := by
  have hs : ((star g : SectorUnitary) : SectorMatrix)=(g : SectorMatrix).conjTranspose := rfl
  apply sector_native_ext
  · simp only [sectorUnitaryAction_complex,sectorConjugation]
    simp only [hs,Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc,su_cancel,su_left,Matrix.mul_one]
  · simp only [sectorUnitaryAction_hidden]
    simp only [hs,Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mul_assoc,su_left,Matrix.mul_one]

/-- Literal compact-sector inputs have no hidden coordinate, in the actual
sector equivalence rather than an assumed model conversion. -/
theorem hiddenMatrix_of_inComplex (x : Albert) (hx : InComplexSector x) : hiddenMatrix x=0 := by
  have h : complexAlbertLinear (complexCoordinatesLinear x)=x := complexProjection_eq_self x hx
  rw [← h]
  exact hiddenMatrix_complexAlbert _

end
end Glennie
