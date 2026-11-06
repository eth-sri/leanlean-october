module

public import GS.Nonmanifold.RankOneGeometry

@[expose] public section


/-!
# Removing the redundant coordinates from the manuscript's row-skew cone

The actual g(K) has two rows indexed by q x q matrix entries, each a skew
matrix. This file constructs the coordinate homeomorphism to two rows indexed
only by strict-upper-triangular entries. Rank-at-most-one is preserved both
ways. This is a homeomorphism, NOT an assertion that unweighted upper entries
preserve the Frobenius norm. Closed Frobenius balls become the corresponding
ellipsoidal constraints until a separately proved normalization is applied.
-/
noncomputable section
open Matrix GS GS.Extensions GS.GlobalGeometry
namespace GS.Nonmanifold

/-- Independent coordinates of a real skew q x q matrix. -/
abbrev UpperIndex (q : ℕ) := {ij : Fin q × Fin q // ij.1 < ij.2}

def packSkew {q : ℕ} (A : Mat q) : UpperIndex q → ℝ :=
  fun ij => A ij.val.1 ij.val.2

section
variable {q : ℕ} (x : UpperIndex q → ℝ)
def unpackSkew : Mat q := fun i j =>
  if h : i < j then x ⟨(i,j),h⟩
  else if h : j < i then -x ⟨(j,i),h⟩ else 0

theorem unpackSkew_isSkew :
    IsSkew (unpackSkew x) := by
  ext i j
  simp only [unpackSkew, transpose_apply, Matrix.neg_apply]
  split_ifs <;> grind

theorem pack_unpackSkew :
    packSkew (unpackSkew x) = x := by
  funext ij
  simp [packSkew, unpackSkew, ij.property]

end

section
variable {q : ℕ}
theorem unpack_packSkew {A : Mat q} (hA : IsSkew A) :
    unpackSkew (packSkew A) = A := by
  ext i j
  have := congrFun₂ hA i j
  have := congrFun₂ hA i i
  simp only [unpackSkew, packSkew, transpose_apply, Matrix.neg_apply] at *
  split_ifs <;> grind

theorem unpackSkew_smul (t : ℝ) (x : UpperIndex q → ℝ) :
    unpackSkew (t • x) = t • unpackSkew x := by
  ext i j
  by_cases hij : i < j <;> by_cases hji : j < i <;>
    simp [unpackSkew, hij, hji]

end

theorem continuous_unpackSkew (q : ℕ) : Continuous (@unpackSkew q) :=
  continuous_pi fun i => continuous_pi fun j => by
  by_cases hij : i < j <;> by_cases hji : j < i <;>
    simp [unpackSkew, hij, hji] <;> fun_prop

def packRows (W : Matrix (Fin 2) (Fin q × Fin q) ℝ) :
    Matrix (Fin 2) (UpperIndex q) ℝ := fun r ij => W r ij.val

section
variable {q : ℕ} (Z : Matrix (Fin 2) (UpperIndex q) ℝ)
def unpackRows :
    Matrix (Fin 2) (Fin q × Fin q) ℝ := fun r ij => unpackSkew (Z r) ij.1 ij.2

theorem pack_unpackRows :
    packRows (unpackRows Z) = Z :=
  funext fun r => pack_unpackSkew (Z r)

end

section
variable {q : ℕ}
theorem unpack_packRows (W : Matrix (Fin 2) (Fin q × Fin q) ℝ)
    (hW : ∀ r, IsSkew (fun i j => W r (i,j))) :
    unpackRows (packRows W) = W := by
  ext r ij
  exact congrFun₂ (unpack_packSkew (hW r)) ij.1 ij.2

theorem unpackRows_isSkew (Z : Matrix (Fin 2) (UpperIndex q) ℝ) (r : Fin 2) :
    IsSkew (fun i j => unpackRows Z r (i,j)) := unpackSkew_isSkew (Z r)

theorem packRows_rank_le_one (W : Matrix (Fin 2) (Fin q × Fin q) ℝ)
    (hW : W.rank ≤ 1) : (packRows W).rank ≤ 1 := by
  apply rank_le_one_of_two_column_minors
  intro j k
  exact rank_le_one_minor W hW 0 1 j.val k.val

theorem unpackRows_outer (u : CircleVector) (z : UpperIndex q → ℝ) :
    unpackRows (outer u z) = outer u (fun ij => unpackSkew z ij.1 ij.2) := by
  ext r ij
  have := congrFun₂ (unpackSkew_smul (u r) z) ij.1 ij.2
  aesop

theorem unpackRows_rank_le_one (Z : Matrix (Fin 2) (UpperIndex q) ℝ)
    (hZ : Z.rank ≤ 1) : (unpackRows Z).rank ≤ 1 := by
  obtain ⟨u,hu,z,he⟩ := exists_unit_outer_of_rank_le_one Z hZ
  rw [← he, unpackRows_outer]
  exact rank_outer_le_one _ _

end

section
variable (q : ℕ)
theorem continuous_unpackRows : Continuous (@unpackRows q) := by
  have := continuous_unpackSkew q
  unfold unpackRows
  fun_prop

/-- Three independent skew coordinates, available for every q >= 3. -/
def threeUpperIndices (hq : 3 ≤ q) : Fin 3 → UpperIndex q :=
  ![⟨(⟨0,by omega⟩,⟨1,by omega⟩), Nat.zero_lt_succ 0⟩,
    ⟨(⟨0,by omega⟩,⟨2,by omega⟩), Nat.zero_lt_succ 1⟩,
    ⟨(⟨1,by omega⟩,⟨2,by omega⟩), Nat.lt_succ_self 1⟩]

theorem three_le_card_upperIndex (hq : 3 ≤ q) :
    3 ≤ Fintype.card (UpperIndex q) := by
  simpa using Fintype.card_le_of_injective (threeUpperIndices q hq) fun i j h => by
    fin_cases i <;> fin_cases j <;> simp_all [threeUpperIndices]

end

end GS.Nonmanifold
