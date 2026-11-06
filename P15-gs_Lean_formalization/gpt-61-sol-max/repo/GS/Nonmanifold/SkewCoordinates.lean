import Mathlib.Tactic

import GS.Nonmanifold.RankOneGeometry




/-!
# Removing the redundant coordinates from the manuscript's row-skew cone

The actual g(K) has two rows indexed by q x q matrix entries, each a skew
matrix. This file constructs the coordinate homeomorphism to two rows indexed
only by strict-upper-triangular entries. Rank-at-most-one is preserved both
ways. This is a homeomorphism, NOT an assertion that unweighted upper entries
preserve the Frobenius norm. Closed Frobenius balls become the corresponding
ellipsoidal constraints until a separately proved normalization is applied.
-/
namespace GS.Nonmanifold

/-- Independent coordinates of a real skew q x q matrix. -/
abbrev UpperIndex (q : ℕ) := {ij : Fin q × Fin q // ij.1 < ij.2}

def packSkew (A : Mat q) : UpperIndex q → ℝ :=
  fun ij => A ij.val.1 ij.val.2

def unpackSkew (x : UpperIndex q → ℝ) := fun i j =>
  if h : i < j then x ⟨(i,j),h⟩
  else if h : j < i then -x ⟨(j,i),h⟩ else 0

theorem unpackSkew_isSkew (x : UpperIndex q → ℝ) :
    IsSkew (unpackSkew x) := by
  ext i j
  change unpackSkew x j i = -unpackSkew x i j
  by_cases hij : i < j <;> by_cases hji : j < i <;>
    simp [unpackSkew,hij,hji] <;> omega

theorem pack_unpackSkew (x : UpperIndex q → ℝ) :
    packSkew (unpackSkew x) = x := by grind [packSkew,unpackSkew]

theorem unpack_packSkew {A : Mat q} (hA : IsSkew A) :
    unpackSkew (packSkew A) = A := by
  ext i j
  have he := congrFun (congrFun hA i) j
  change A j i = -A i j at he
  by_cases hij : i < j
  · simp_all [packSkew,unpackSkew]
  · by_cases hji : j < i
    · simp_all [packSkew,unpackSkew]
    · have h := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      have hd : A i i = 0 := by grind
      simp [unpackSkew, packSkew, hd]



theorem continuous_unpackSkew (q : ℕ) : Continuous (@unpackSkew q) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i < j <;> by_cases hji : j < i <;>
    simp [unpackSkew, hij, hji] <;> fun_prop

def packRows (W : Matrix (Fin 2) (Fin q × Fin q) ℝ) :
    Matrix (Fin 2) (UpperIndex q) ℝ := fun r ij => W r ij.val

def unpackRows (Z : Matrix (Fin 2) (UpperIndex q) ℝ) :
    Matrix (Fin 2) (Fin q × Fin q) ℝ := fun r ij => unpackSkew (Z r) ij.1 ij.2

theorem pack_unpackRows (Z : Matrix (Fin 2) (UpperIndex q) ℝ) :
    packRows (unpackRows Z) = Z := by
  funext r
  exact pack_unpackSkew (Z r)











theorem continuous_unpackRows (q : ℕ) : Continuous (@unpackRows q) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro ij
  exact (continuous_apply ij.2).comp ((continuous_apply ij.1).comp
    ((continuous_unpackSkew q).comp (continuous_apply r)))

/-- Three independent skew coordinates, available for every q >= 3. -/
def threeUpperIndices (q : ℕ) (hq : 3 ≤ q) : Fin 3 → UpperIndex q :=
  ![⟨(⟨0,by omega⟩,⟨1,by omega⟩), Nat.zero_lt_succ 0⟩,
    ⟨(⟨0,by omega⟩,⟨2,by omega⟩), Nat.zero_lt_succ 1⟩,
    ⟨(⟨1,by omega⟩,⟨2,by omega⟩), Nat.lt_succ_self 1⟩]

theorem threeUpperIndices_injective (q : ℕ) (hq : 3 ≤ q) :
    Function.Injective (threeUpperIndices q hq) := by
  intro i j h
  fin_cases i,j <;> simp_all [threeUpperIndices]

theorem three_le_card_upperIndex (q : ℕ) (hq : 3 ≤ q) :
    3 ≤ Fintype.card (UpperIndex q) := by
  have h := Fintype.card_le_of_injective _ (threeUpperIndices_injective q hq)
  simpa using h

end GS.Nonmanifold
