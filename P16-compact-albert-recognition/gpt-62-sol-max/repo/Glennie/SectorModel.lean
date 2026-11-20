/- The full real-linear compact sector model and its native matrix semantics.
The complex Hermitian coordinate type stores three real diagonal entries and
three complex upper entries; it is not the split Albert model. -/
module
public import Glennie.SectorSubspace
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Tactic.Module
@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

abbrev SectorMatrix := Matrix (Fin 3) (Fin 3) ℂ

abbrev ComplexHermitianCoordinates := ComplexCoordinates

def complexHermitianMatrix (q : ComplexHermitianCoordinates) : SectorMatrix :=
  !![(q.1.1:ℂ),q.2.1,q.2.2.1;
     star q.2.1,(q.1.2.1:ℂ),q.2.2.2;
     star q.2.2.1,star q.2.2.2,(q.1.2.2:ℂ)]

def matrixComplexCoordinates (H : SectorMatrix) : ComplexHermitianCoordinates :=
  (((H 0 0).re,(H 1 1).re,(H 2 2).re),(H 0 1,H 0 2,H 1 2))

theorem complexHermitianMatrix_isHermitian (q : ComplexHermitianCoordinates) :
    (complexHermitianMatrix q).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexHermitianMatrix, Matrix.conjTranspose_apply]

theorem matrixComplexCoordinates_inverse (q : ComplexHermitianCoordinates) :
    matrixComplexCoordinates (complexHermitianMatrix q) = q := rfl

theorem complexHermitianMatrix_inverse (H : SectorMatrix)
    (hH : H.IsHermitian) : complexHermitianMatrix (matrixComplexCoordinates H)=H := by
  have hs (i j : Fin 3) : star (H j i)=H i j := congrFun (congrFun hH i) j
  have hd (i : Fin 3) : ((H i i).re:ℂ)=H i i := by
    apply Complex.ext
    · simp
    · have h := congrArg Complex.im (hs i i)
      simp at h ⊢
      linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexHermitianMatrix,matrixComplexCoordinates,hd,hs]

def sectorHiddenLinear : Albert →ₗ[ℝ] SectorMatrix where
  toFun := hiddenMatrix
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [hiddenMatrix,hiddenColumn]
    all_goals ring
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [hiddenMatrix,hiddenColumn,smul_eq_mul,Complex.mul_re,Complex.mul_im]

theorem hiddenMatrix_hiddenAlbert (M : SectorMatrix) :
    hiddenMatrix (hiddenAlbert M)=M := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [hiddenMatrix,hiddenAlbert,hiddenColumn,hiddenOct]

theorem hiddenMatrix_complexAlbert (q : ComplexCoordinates) :
    hiddenMatrix (complexAlbertLinear q)=0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [hiddenMatrix,complexAlbertLinear,complexAlbert,hiddenColumn,complexOct]

theorem hiddenMatrix_of_inComplex (x : Albert) (hx : InComplexSector x) : hiddenMatrix x = 0 := by
  rw [← complexProjection_eq_self x hx]
  exact hiddenMatrix_complexAlbert (complexCoordinatesLinear x)

theorem complexCoordinates_hiddenAlbert (M : SectorMatrix) :
    complexCoordinatesLinear (hiddenAlbert M)=0 := by
  simp [complexCoordinatesLinear,hiddenAlbert,complexPart,hiddenOct,Complex.ext_iff]

/-- The actual full real-linear sector equivalence. -/
def compactSectorEquiv : Albert ≃ₗ[ℝ]
    ComplexHermitianCoordinates × SectorMatrix where
  toFun x := (complexCoordinatesLinear x,sectorHiddenLinear x)
  invFun p := complexAlbertLinear p.1+hiddenAlbert p.2
  left_inv := complex_hidden_decomposition
  right_inv p := by
    apply Prod.ext
    · change complexCoordinatesLinear (complexAlbertLinear p.1+hiddenAlbert p.2)=p.1
      rw [map_add,complexCoordinates_albert,complexCoordinates_hiddenAlbert,add_zero]
    · change sectorHiddenLinear (complexAlbertLinear p.1+hiddenAlbert p.2)=p.2
      rw [map_add]
      change hiddenMatrix (complexAlbertLinear p.1)+hiddenMatrix (hiddenAlbert p.2)=p.2
      rw [hiddenMatrix_complexAlbert,hiddenMatrix_hiddenAlbert,zero_add]
  map_add' x y := by simp only [map_add,Prod.mk_add_mk]
  map_smul' r x := by simp only [map_smul,Prod.smul_mk,RingHom.id_apply]

def sectorComplexMatrix (x : Albert) : SectorMatrix :=
  complexHermitianMatrix (complexCoordinatesLinear x)

theorem sectorComplexMatrix_isHermitian (x : Albert) :
    (sectorComplexMatrix x).IsHermitian :=
  complexHermitianMatrix_isHermitian (complexCoordinatesLinear x)

theorem sector_ext {x y : Albert} (hC : sectorComplexMatrix x = sectorComplexMatrix y)
    (hH : hiddenMatrix x = hiddenMatrix y) : x = y := by
  apply compactSectorEquiv.injective
  refine Prod.ext ?_ hH
  change complexCoordinatesLinear x = complexCoordinatesLinear y
  simpa only [sectorComplexMatrix, matrixComplexCoordinates_inverse] using congrArg matrixComplexCoordinates hC

def sectorAdjointAdjugate (M : SectorMatrix) := M.adjugate.conjTranspose

def sectorPolarAdjugate (M N : SectorMatrix) :=
  sectorAdjointAdjugate (M+N)-sectorAdjointAdjugate M-sectorAdjointAdjugate N

def sectorProductComplex (H M K N : SectorMatrix) :=
  (1/2:ℂ) • (H*K+K*H-M.conjTranspose*N-N.conjTranspose*M)+
    ((M.conjTranspose*N).trace.re:ℂ) • (1 : SectorMatrix)

def sectorComplement (B : SectorMatrix) : SectorMatrix := B.trace • 1 - B

theorem sectorHermitian_trace {B : SectorMatrix} (h : B.IsHermitian) : star B.trace = B.trace := by
  rw [← Matrix.trace_conjTranspose, h.eq]

theorem sectorComplement_hermitian {B : SectorMatrix} (h : B.IsHermitian) :
    (sectorComplement B).IsHermitian := by
  show (sectorComplement B).conjTranspose = sectorComplement B
  simp [sectorComplement, Matrix.conjTranspose_smul, h.eq, sectorHermitian_trace h]

@[simp] theorem trace_sectorComplement (B : SectorMatrix) : (sectorComplement B).trace = 2*B.trace := by
  simp [sectorComplement, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  ring

theorem sectorComplement_injective : Function.Injective sectorComplement := by
  intro A B h
  have ht := congrArg Matrix.trace h
  simp only [trace_sectorComplement, mul_right_inj' (two_ne_zero : (2 : ℂ) ≠ 0)] at ht
  simpa [sectorComplement, ht] using h

theorem sectorProductComplex_square (K M : SectorMatrix) :
    sectorProductComplex K M K M = K*K + sectorComplement (M.conjTranspose*M) := by
  rw [sectorProductComplex, Complex.conj_eq_iff_re.mp
    (sectorHermitian_trace (Matrix.isHermitian_conjTranspose_mul_self M)), sectorComplement]
  module

def sectorProductHidden (H M K N : SectorMatrix) :=
  (1/2:ℂ) • (M*sectorComplement K + N*sectorComplement H + sectorPolarAdjugate M N)

/-- The complex component of the complete bilinear product, in the
column gauge. Both arguments range over all 27 real coordinates. -/
theorem sectorComplexMatrix_jordan (x y : Albert) :
    sectorComplexMatrix (jordan x y) =
      sectorProductComplex (sectorComplexMatrix x) (hiddenMatrix x)
        (sectorComplexMatrix y) (hiddenMatrix y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals simp [sectorComplexMatrix, complexHermitianMatrix, complexCoordinatesLinear, complexPart,
    hiddenMatrix, hiddenColumn, sectorProductComplex, jordan_coord, oct_coord, smul_eq_mul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag, 
    Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  all_goals ring

/-- The hidden component includes the full polarized adjoint-adjugate term.
This polynomial identity also covers singular hidden matrices. -/
theorem hiddenMatrix_jordan (x y : Albert) :
    hiddenMatrix (jordan x y) =
      sectorProductHidden (sectorComplexMatrix x) (hiddenMatrix x)
        (sectorComplexMatrix y) (hiddenMatrix y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals simp [hiddenMatrix, hiddenColumn, sectorComplexMatrix, complexHermitianMatrix,
    complexCoordinatesLinear, complexPart, sectorProductHidden, sectorComplement, sectorPolarAdjugate,
    sectorAdjointAdjugate, jordan_o01, jordan_o02, jordan_o12, oct_coord, smul_eq_mul,
    Matrix.adjugate_fin_three, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace,
    Matrix.diag, Matrix.one_apply, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  all_goals ring

/-- Raw trace normalization T(1)=3 is preserved by the complex matrix component. -/
theorem trace_sectorComplexMatrix (x : Albert) :
    (sectorComplexMatrix x).trace = (trace x : ℂ) := by
  simp [sectorComplexMatrix, complexHermitianMatrix, complexCoordinatesLinear,
    Matrix.trace, Matrix.diag, Fin.sum_univ_three, trace]

/-- The full positive compact metric, with the required factor two on hidden
matrix coordinates. No normalized trace is substituted. -/
theorem inner_sector_model (x y : Albert) :
    inner x y = ((sectorComplexMatrix x * sectorComplexMatrix y).trace).re +
      2 * (((hiddenMatrix x).conjTranspose * hiddenMatrix y).trace).re := by
  simp [inner_coordinates, octDot_coordinates, sectorComplexMatrix,
    complexHermitianMatrix, complexCoordinatesLinear, complexPart,
    hiddenMatrix, hiddenColumn, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
    Complex.mul_re]
  ring

def sectorComplexLinear : Albert →ₗ[ℝ] SectorMatrix where
  toFun := sectorComplexMatrix
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [sectorComplexMatrix, complexHermitianMatrix,
        complexCoordinatesLinear, complexPart]
    all_goals ring
  map_smul' r x := by
    simp [sectorComplexMatrix, complexHermitianMatrix, complexCoordinatesLinear, complexPart,
      smul_eq_mul]

@[simp] theorem sectorComplexLinear_apply (x : Albert) :
    sectorComplexLinear x = sectorComplexMatrix x := rfl

end
end Glennie
