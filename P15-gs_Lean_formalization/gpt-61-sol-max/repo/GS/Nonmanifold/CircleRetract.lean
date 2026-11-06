module

public import GS.Nonmanifold.RankOneGeometry

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A polynomial circle retract of the rank-one link

For W of size 2 x (d+2), rank <= 1 and Frobenius radius one, put G=W W^T.
The map W |-> (G00-G11, 2 G01) takes values in the unit circle.
Its section is [(I+T(v))/2 | 0]. The section is globally continuous; no
continuous choice of a sign for a rank-one factor is needed.

This proves a genuine topological retract, not yet the nontriviality of
singular homology or the local homology obstruction at the cone vertex.
-/
noncomputable section
open Matrix GS GS.Extensions GS.GlobalGeometry
open scoped BigOperators
namespace GS.Nonmanifold

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def rowGram (W : Matrix (Fin 2) κ ℝ) : Mat 2 :=
  fun i j => ∑ k, W i k * W j k

theorem rowGram_outer (u : CircleVector) (z : κ → ℝ) (i j : Fin 2) :
    rowGram (outer u z) i j = (u i * u j) * ∑ k, z k^2 := by
  simp only [rowGram, outer, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

def circleCoordinate (W : Matrix (Fin 2) κ ℝ) : CircleVector :=
  ![rowGram W 0 0 - rowGram W 1 1, 2 * rowGram W 0 1]

theorem continuous_circleCoordinate :
    Continuous (circleCoordinate : Matrix (Fin 2) κ ℝ → CircleVector) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [circleCoordinate, rowGram] <;> fun_prop

/-- Append zero columns, using d+2 rather than a dimension cast. -/
def padTwo (d : ℕ) (A : Mat 2) : Matrix (Fin 2) (Fin (d+2)) ℝ :=
  fun i => Fin.cases (A i 0) (Fin.cases (A i 1) (fun _ : Fin d => 0))

theorem padTwo_frobSq (d : ℕ) (A : Mat 2) :
    frobSq (padTwo d A) = frobSq A := by
  simp [frobSq, frobInner, padTwo, Fin.sum_univ_succ, Fin.sum_univ_two]

theorem padTwo_rowGram (d : ℕ) (A : Mat 2) :
    rowGram (padTwo d A) = A * Aᵀ := by
  ext i j
  simp [rowGram, padTwo, Matrix.mul_apply, Fin.sum_univ_succ,
    Fin.sum_univ_two, Matrix.transpose_apply]

theorem padTwo_rank_le_one (d : ℕ) {A : Mat 2} (hA : A.rank ≤ 1) :
    (padTwo d A).rank ≤ 1 := by
  apply rank_le_one_of_two_column_minors
  intro j k
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  · refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
    · simp [padTwo]
    · change A 0 0 * A 1 1 = A 0 1 * A 1 0
      exact rank_le_one_two_column_minor A hA 0 1
    · simp [padTwo]
  · refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
    · change A 0 1 * A 1 0 = A 0 0 * A 1 1
      exact rank_le_one_two_column_minor A hA 1 0
    · simp [padTwo]
    · simp [padTwo]
  · simp [padTwo]

end GS.Nonmanifold
