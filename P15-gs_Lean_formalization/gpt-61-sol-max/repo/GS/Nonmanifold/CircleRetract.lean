
import GS.Nonmanifold.RankOneGeometry
open GS.MatrixBase



/-!
# A polynomial circle retract of the rank-one link

For W of size 2 x (d+2), rank <= 1 and Frobenius radius one, put G=W W^T.
The map W |-> (G00-G11, 2 G01) takes values in the unit circle.
Its section is [(I+T(v))/2 | 0]. The section is globally continuous; no
continuous choice of a sign for a rank-one factor is needed.

This proves a genuine topological retract, not yet the nontriviality of
singular homology or the local homology obstruction at the cone vertex.
-/
open Matrix
namespace GS.Nonmanifold

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def rowGram (W : Matrix (Fin 2) κ ℝ) : Mat 2 :=
  fun i j => ∑ k, W i k * W j k

variable (d : ℕ)

variable (A : Mat 2)



def circleCoordinate (W : Matrix (Fin 2) κ ℝ) : CircleVector :=
  ![rowGram W 0 0 - rowGram W 1 1, 2 * rowGram W 0 1]

theorem continuous_circleCoordinate :
    Continuous (circleCoordinate : Matrix (Fin 2) κ ℝ → CircleVector) := by fun_prop [circleCoordinate, rowGram]

/-- Append zero columns, using d+2 rather than a dimension cast. -/
def padTwo   : Matrix (Fin 2) (Fin (d+2)) ℝ :=
  fun i => Fin.cases (A i 0) (Fin.cases (A i 1) (fun _ : Fin d => 0))

theorem padTwo_frobSq   :
    cFrobSq (padTwo d A) = cFrobSq A := by
  simp [cFrobSq, cFrobInner, padTwo, Fin.sum_univ_succ]

theorem padTwo_rowGram   :
    rowGram (padTwo d A) = A * Aᵀ := by ext <;> simp_all [padTwo,rowGram,Fin.sum_univ_succ,Matrix.mul_apply,Matrix.transpose_apply]

theorem padTwo_rank_le_one  {A : Mat 2} (hA : A.rank ≤ 1) :
    (padTwo d A).rank ≤ 1 := by
  have he : padTwo d A = A * padTwo d 1 := by
    ext i j
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
      simp [padTwo,Matrix.mul_apply,Fin.sum_univ_two]
    change A i 1 = A i 0 * 0 + A i 1 * 1
    ring
  rw [he]
  exact (Matrix.rank_mul_le_left _ _).trans hA

end GS.Nonmanifold
