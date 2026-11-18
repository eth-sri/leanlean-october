module
public import Glennie.Hilbert
public import Glennie.Obligations
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section
namespace Glennie
noncomputable section

set_option maxHeartbeats 2000000

def complexPart (x : Octonion) : ℂ := ⟨x.1.re, x.1.imI⟩
def complexOct (z : ℂ) : Octonion := (⟨z.re, z.im, 0, 0⟩, 0)

def hiddenColumn (x : Octonion) : Fin 3 → ℂ :=
  ![⟨x.1.imJ, x.1.imK⟩, ⟨x.2.re, x.2.imI⟩, ⟨x.2.imJ, -x.2.imK⟩]

def hiddenOct (v : Fin 3 → ℂ) : Octonion :=
  (⟨0, 0, (v 0).re, (v 0).im⟩, ⟨(v 1).re, (v 1).im, (v 2).re, -(v 2).im⟩)

def hiddenMatrix (z : Albert) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i => ![-hiddenColumn z.o12 i, hiddenColumn z.o02 i, -hiddenColumn z.o01 i]

def hiddenAlbert (M : Matrix (Fin 3) (Fin 3) ℂ) : Albert :=
  ⟨0, 0, 0, -hiddenOct (fun i => M i 2), hiddenOct (fun i => M i 1), -hiddenOct (fun i => M i 0)⟩

def complexProjection (z : Albert) : Albert :=
  ⟨z.d0, z.d1, z.d2, complexOct (complexPart z.o01), complexOct (complexPart z.o02), complexOct (complexPart z.o12)⟩

def diagonalAlbert (a b c : ℝ) : Albert := ⟨a, b, c, 0, 0, 0⟩
def complexAlbert (a b c : ℝ) (u v w : ℂ) : Albert := ⟨a, b, c, complexOct u, complexOct v, complexOct w⟩

theorem oct_complex_hidden_decomposition (x : Octonion) :
    complexOct (complexPart x) + hiddenOct (hiddenColumn x) = x := by
  ext <;> simp [complexOct, complexPart, hiddenOct, hiddenColumn]

theorem complex_hidden_decomposition (z : Albert) :
    complexProjection z + hiddenAlbert (hiddenMatrix z) = z := by
  ext <;> simp [complexProjection, hiddenAlbert, hiddenMatrix, hiddenColumn, hiddenOct, complexPart, complexOct]

theorem complex_hidden_orthogonal (x : Albert) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    inner (complexProjection x) (hiddenAlbert M) = 0 := by
  simp [inner_coordinates, octDot_coordinates, complexProjection, hiddenAlbert, complexOct, hiddenOct]

def sectorColumnGram (M : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ := M.conjTranspose * M
def sectorFrobeniusSq (M : Matrix (Fin 3) (Fin 3) ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (M i j)

theorem hidden_square_complexProjection (M : Matrix (Fin 3) (Fin 3) ℂ) :
    complexProjection (jordan (hiddenAlbert M) (hiddenAlbert M)) =
      complexAlbert (sectorFrobeniusSq M - (sectorColumnGram M 0 0).re)
        (sectorFrobeniusSq M - (sectorColumnGram M 1 1).re)
        (sectorFrobeniusSq M - (sectorColumnGram M 2 2).re)
        (-sectorColumnGram M 0 1) (-sectorColumnGram M 0 2) (-sectorColumnGram M 1 2) := by
  ext <;> simp [complexProjection, complexAlbert, complexOct, complexPart, hiddenAlbert, hiddenOct,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octNormSq,
    Quaternion.normSq_def', octMul, octConj, smul_eq_mul, sectorColumnGram, sectorFrobeniusSq, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

theorem U_diagonal (a b c : ℝ) (z : Albert) :
    U (diagonalAlbert a b c) z =
      ⟨a ^ 2 * z.d0, b ^ 2 * z.d1, c ^ 2 * z.d2, (a * b) • z.o01, (a * c) • z.o02, (b * c) • z.o12⟩ := by
  ext <;> simp [U, diagonalAlbert, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_coordinates, octMul, octConj, octNormSq, Quaternion.normSq_def', smul_smul, smul_eq_mul] <;> ring

abbrev ComplexCoordinates := (ℝ × ℝ × ℝ) × (ℂ × ℂ × ℂ)

def complexAlbertLinear : ComplexCoordinates →ₗ[ℝ] Albert where
  toFun q := complexAlbert q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2.1 q.2.2.2
  map_add' _ _ := by ext <;> simp [complexAlbert, complexOct]
  map_smul' _ _ := by ext <;> simp [complexAlbert, complexOct, smul_eq_mul]

def complexCoordinatesLinear : Albert →ₗ[ℝ] ComplexCoordinates where
  toFun x := ((x.d0, x.d1, x.d2), (complexPart x.o01, complexPart x.o02, complexPart x.o12))
  map_add' _ _ := by ext <;> simp [complexPart] <;> apply Complex.ext <;> simp
  map_smul' _ _ := by ext <;> simp [complexPart, smul_eq_mul] <;> apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem complexCoordinates_albert (q : ComplexCoordinates) : complexCoordinatesLinear (complexAlbertLinear q) = q := rfl
theorem complexAlbert_coordinates (x : Albert) : complexAlbertLinear (complexCoordinatesLinear x) = complexProjection x := rfl

def complexSector : Submodule ℝ Albert := LinearMap.range complexAlbertLinear

theorem complexProjection_mem (x : Albert) : complexProjection x ∈ complexSector :=
  ⟨complexCoordinatesLinear x, complexAlbert_coordinates x⟩

theorem complexProjection_eq_self (x : Albert) (hx : InComplexSector x) : complexProjection x = x := by
  rcases hx with ⟨⟨h01j, h01k, h01s⟩, ⟨h02j, h02k, h02s⟩, ⟨h12j, h12k, h12s⟩⟩
  ext <;> simp [complexProjection, complexPart, complexOct, h01j, h01k, h01s, h02j, h02k, h02s, h12j, h12k, h12s]

theorem complexSector_mem_iff (x : Albert) : x ∈ complexSector ↔ InComplexSector x :=
  ⟨fun ⟨_, hq⟩ => hq ▸ by simp [complexAlbertLinear, complexAlbert, complexOct, InComplexSector, OctInComplex],
   fun hx => complexProjection_eq_self x hx ▸ complexProjection_mem x⟩

theorem complexSector_jordan (x y : Albert) (hx : InComplexSector x) (hy : InComplexSector y) :
    InComplexSector (jordan x y) := by
  rw [← complexProjection_eq_self x hx, ← complexProjection_eq_self y hy]
  simp [InComplexSector, OctInComplex, complexProjection, complexPart, complexOct, jordan_o01, jordan_o02, jordan_o12, octMul, octConj]

theorem complexProjection_zero_of_perp (z : Albert) (hz : ∀ v ∈ complexSector, inner v z = 0) :
    complexProjection z = 0 := by
  apply (inner_self_eq_zero _).mp
  have hp : inner (complexProjection z) z = inner (complexProjection z) (complexProjection z) := by
    calc inner (complexProjection z) z
        = inner (complexProjection z) (complexProjection z + hiddenAlbert (hiddenMatrix z)) :=
            congrArg (inner _) (complex_hidden_decomposition z).symm
      _ = _ := by rw [inner_add_right, complex_hidden_orthogonal, add_zero]
  exact hp.symm.trans (hz _ (complexProjection_mem z))

abbrev ComplexHermitianCoordinates := ComplexCoordinates

def complexHermitianMatrix (q : ComplexHermitianCoordinates) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(q.1.1 : ℂ), q.2.1, q.2.2.1;
     star q.2.1, (q.1.2.1 : ℂ), q.2.2.2;
     star q.2.2.1, star q.2.2.2, (q.1.2.2 : ℂ)]

def matrixComplexCoordinates (H : Matrix (Fin 3) (Fin 3) ℂ) : ComplexHermitianCoordinates :=
  (((H 0 0).re, (H 1 1).re, (H 2 2).re), (H 0 1, H 0 2, H 1 2))

theorem complexHermitianMatrix_isHermitian (q : ComplexHermitianCoordinates) :
    (complexHermitianMatrix q).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexHermitianMatrix, Matrix.conjTranspose_apply]

theorem matrixComplexCoordinates_inverse (q : ComplexHermitianCoordinates) :
    matrixComplexCoordinates (complexHermitianMatrix q) = q := by
  rcases q with ⟨⟨a, b, c⟩, ⟨u, v, w⟩⟩; simp [matrixComplexCoordinates, complexHermitianMatrix]

theorem complexHermitianMatrix_inverse (H : Matrix (Fin 3) (Fin 3) ℂ) (hH : H.IsHermitian) :
    complexHermitianMatrix (matrixComplexCoordinates H) = H := by
  have hs (i j : Fin 3) : star (H j i) = H i j := congrFun (congrFun hH i) j
  have hd (i : Fin 3) : ((H i i).re : ℂ) = H i i :=
    Complex.ext (by simp) (by have h := congrArg Complex.im (hs i i); simp at h ⊢; linarith)
  ext i j; fin_cases i <;> fin_cases j <;> simp [complexHermitianMatrix, matrixComplexCoordinates, hd, hs]

def sectorHiddenLinear : Albert →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun := hiddenMatrix
  map_add' _ _ := by ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [hiddenMatrix, hiddenColumn] <;> ring
  map_smul' _ _ := by ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [hiddenMatrix, hiddenColumn, smul_eq_mul, Complex.mul_re, Complex.mul_im]

theorem hiddenMatrix_hiddenAlbert (M : Matrix (Fin 3) (Fin 3) ℂ) : hiddenMatrix (hiddenAlbert M) = M := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [hiddenMatrix, hiddenAlbert, hiddenColumn, hiddenOct]

theorem hiddenMatrix_complexAlbert (q : ComplexCoordinates) : hiddenMatrix (complexAlbertLinear q) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [hiddenMatrix, complexAlbertLinear, complexAlbert, hiddenColumn, complexOct]

theorem complexCoordinates_hiddenAlbert (M : Matrix (Fin 3) (Fin 3) ℂ) :
    complexCoordinatesLinear (hiddenAlbert M) = 0 := by
  simp [complexCoordinatesLinear, hiddenAlbert, complexPart, hiddenOct, Complex.ext_iff]

def compactSectorEquiv : Albert ≃ₗ[ℝ] ComplexHermitianCoordinates × Matrix (Fin 3) (Fin 3) ℂ where
  toFun x := (complexCoordinatesLinear x, sectorHiddenLinear x)
  invFun p := complexAlbertLinear p.1 + hiddenAlbert p.2
  left_inv := complex_hidden_decomposition
  right_inv p := Prod.ext
    (by change complexCoordinatesLinear (complexAlbertLinear p.1 + hiddenAlbert p.2) = p.1
        rw [map_add, complexCoordinates_albert, complexCoordinates_hiddenAlbert, add_zero])
    (by change sectorHiddenLinear (complexAlbertLinear p.1 + hiddenAlbert p.2) = p.2
        rw [map_add]
        change hiddenMatrix (complexAlbertLinear p.1) + hiddenMatrix (hiddenAlbert p.2) = p.2
        rw [hiddenMatrix_complexAlbert, hiddenMatrix_hiddenAlbert, zero_add])
  map_add' _ _ := by simp only [map_add, Prod.mk_add_mk]
  map_smul' _ _ := by simp only [map_smul, Prod.smul_mk, RingHom.id_apply]

def sectorComplexMatrix (x : Albert) : Matrix (Fin 3) (Fin 3) ℂ :=
  complexHermitianMatrix (complexCoordinatesLinear x)

theorem sectorComplexMatrix_isHermitian (x : Albert) : (sectorComplexMatrix x).IsHermitian :=
  complexHermitianMatrix_isHermitian _

def sectorDecode (H M : Matrix (Fin 3) (Fin 3) ℂ) : Albert :=
  complexAlbertLinear (matrixComplexCoordinates H) + hiddenAlbert M

def sectorAdjointAdjugate (M : Matrix (Fin 3) (Fin 3) ℂ) := M.adjugate.conjTranspose
def sectorPolarAdjugate (M N : Matrix (Fin 3) (Fin 3) ℂ) :=
  sectorAdjointAdjugate (M + N) - sectorAdjointAdjugate M - sectorAdjointAdjugate N

def sectorProductComplex (H M K N : Matrix (Fin 3) (Fin 3) ℂ) :=
  (1 / 2 : ℂ) • (H * K + K * H - M.conjTranspose * N - N.conjTranspose * M) +
    ((M.conjTranspose * N).trace.re : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)

def sectorProductHidden (H M K N : Matrix (Fin 3) (Fin 3) ℂ) :=
  (1 / 2 : ℂ) • (M * (K.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) - K) +
    N * (H.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) - H) + sectorPolarAdjugate M N)

theorem sectorComplexMatrix_jordan (x y : Albert) :
    sectorComplexMatrix (jordan x y) =
      sectorProductComplex (sectorComplexMatrix x) (hiddenMatrix x) (sectorComplexMatrix y) (hiddenMatrix y) := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [sectorComplexMatrix, complexHermitianMatrix, complexCoordinatesLinear, complexPart, hiddenMatrix, hiddenColumn,
      sectorProductComplex, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, octDot_coordinates,
      octMul, octConj, smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three, Complex.mul_re, Complex.mul_im] <;> ring

theorem hiddenMatrix_jordan (x y : Albert) :
    hiddenMatrix (jordan x y) =
      sectorProductHidden (sectorComplexMatrix x) (hiddenMatrix x) (sectorComplexMatrix y) (hiddenMatrix y) := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [hiddenMatrix, hiddenColumn, sectorComplexMatrix, complexHermitianMatrix, complexCoordinatesLinear, complexPart,
      sectorProductHidden, sectorPolarAdjugate, sectorAdjointAdjugate, jordan_o01, jordan_o02, jordan_o12, octMul, octConj,
      smul_eq_mul, Matrix.adjugate_fin_three, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag,
      Matrix.one_apply, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im] <;> ring

theorem trace_sectorComplexMatrix (x : Albert) : (sectorComplexMatrix x).trace = (trace x : ℂ) := by
  simp [sectorComplexMatrix, complexHermitianMatrix, complexCoordinatesLinear, Matrix.trace, Matrix.diag, Fin.sum_univ_three, trace]

theorem inner_sector_model (x y : Albert) :
    inner x y = ((sectorComplexMatrix x * sectorComplexMatrix y).trace).re +
      2 * (((hiddenMatrix x).conjTranspose * hiddenMatrix y).trace).re := by
  simp [inner_coordinates, octDot_coordinates, sectorComplexMatrix, complexHermitianMatrix, complexCoordinatesLinear,
    complexPart, hiddenMatrix, hiddenColumn, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_three, Complex.mul_re]; ring

@[simp] theorem sectorDecode_encode (x : Albert) : sectorDecode (sectorComplexMatrix x) (hiddenMatrix x) = x := by
  unfold sectorDecode sectorComplexMatrix
  rw [matrixComplexCoordinates_inverse]; exact complex_hidden_decomposition x

theorem sectorComplexMatrix_decode (H M : Matrix (Fin 3) (Fin 3) ℂ) (hH : H.IsHermitian) :
    sectorComplexMatrix (sectorDecode H M) = H := by
  simp only [sectorDecode, sectorComplexMatrix, map_add, complexCoordinates_albert, complexCoordinates_hiddenAlbert, add_zero]
  exact complexHermitianMatrix_inverse H hH

theorem hiddenMatrix_decode (H M : Matrix (Fin 3) (Fin 3) ℂ) : hiddenMatrix (sectorDecode H M) = M := by
  change sectorHiddenLinear (complexAlbertLinear (matrixComplexCoordinates H) + hiddenAlbert M) = M
  rw [map_add]
  change hiddenMatrix (complexAlbertLinear (matrixComplexCoordinates H)) + hiddenMatrix (hiddenAlbert M) = M
  rw [hiddenMatrix_complexAlbert, hiddenMatrix_hiddenAlbert, zero_add]

def sectorComplexLinear : Albert →ₗ[ℝ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun := sectorComplexMatrix
  map_add' _ _ := by ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [sectorComplexMatrix, complexHermitianMatrix, complexCoordinatesLinear, complexPart] <;> ring
  map_smul' _ _ := by ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [sectorComplexMatrix, complexHermitianMatrix, complexCoordinatesLinear, complexPart, smul_eq_mul, Complex.mul_re, Complex.mul_im]

end
end Glennie
