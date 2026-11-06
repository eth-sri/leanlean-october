module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import GS.CompactFibres
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Fibres
public import GS.Frobenius
public import GS.GlobalGeometry.OriginalGImage
public import GS.Nonmanifold.RankOneGeometry
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

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
open scoped BigOperators
namespace GS.Nonmanifold

/-- Independent coordinates of a real skew q x q matrix. -/
abbrev UpperIndex (q : ℕ) := {ij : Fin q × Fin q // ij.1 < ij.2}

def packSkew {q : ℕ} (A : Mat q) : UpperIndex q → ℝ :=
  fun ij => A ij.val.1 ij.val.2

def unpackSkew {q : ℕ} (x : UpperIndex q → ℝ) : Mat q := fun i j =>
  if h : i < j then x ⟨(i,j),h⟩
  else if h : j < i then -x ⟨(j,i),h⟩ else 0

theorem unpackSkew_isSkew {q : ℕ} (x : UpperIndex q → ℝ) :
    IsSkew (unpackSkew x) := by
  ext i j
  change unpackSkew x j i = -unpackSkew x i j
  by_cases hij : i < j
  · have hji : ¬ j < i := not_lt.mpr (le_of_lt hij)
    simp [unpackSkew, hij, hji]
  · by_cases hji : j < i
    · simp [unpackSkew, hij, hji]
    · simp [unpackSkew, hij, hji]

theorem pack_unpackSkew {q : ℕ} (x : UpperIndex q → ℝ) :
    packSkew (unpackSkew x) = x := by
  funext ij
  simp [packSkew, unpackSkew, ij.property]

theorem unpack_packSkew {q : ℕ} {A : Mat q} (hA : IsSkew A) :
    unpackSkew (packSkew A) = A := by
  ext i j
  have he := congrFun (congrFun hA i) j
  change A j i = -A i j at he
  by_cases hij : i < j
  · simp [unpackSkew, packSkew, hij]
  · by_cases hji : j < i
    · simp [unpackSkew, packSkew, hij, hji, he]
    · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      have hd : A i i = 0 := by linarith [he]
      simp [unpackSkew, packSkew, hd]

theorem unpackSkew_smul {q : ℕ} (t : ℝ) (x : UpperIndex q → ℝ) :
    unpackSkew (t • x) = t • unpackSkew x := by
  ext i j
  by_cases hij : i < j <;> by_cases hji : j < i <;>
    simp [unpackSkew, hij, hji]

theorem continuous_unpackSkew (q : ℕ) : Continuous (@unpackSkew q) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : i < j <;> by_cases hji : j < i <;>
    simp [unpackSkew, hij, hji] <;> fun_prop

def packRows {q : ℕ} (W : Matrix (Fin 2) (Fin q × Fin q) ℝ) :
    Matrix (Fin 2) (UpperIndex q) ℝ := fun r ij => W r ij.val

def unpackRows {q : ℕ} (Z : Matrix (Fin 2) (UpperIndex q) ℝ) :
    Matrix (Fin 2) (Fin q × Fin q) ℝ := fun r ij => unpackSkew (Z r) ij.1 ij.2

theorem pack_unpackRows {q : ℕ} (Z : Matrix (Fin 2) (UpperIndex q) ℝ) :
    packRows (unpackRows Z) = Z := by
  funext r
  exact pack_unpackSkew (Z r)

theorem unpack_packRows {q : ℕ} (W : Matrix (Fin 2) (Fin q × Fin q) ℝ)
    (hW : ∀ r, IsSkew (fun i j => W r (i,j))) :
    unpackRows (packRows W) = W := by
  ext r ij
  exact congrFun (congrFun (unpack_packSkew (hW r)) ij.1) ij.2

theorem unpackRows_isSkew {q : ℕ} (Z : Matrix (Fin 2) (UpperIndex q) ℝ) (r : Fin 2) :
    IsSkew (fun i j => unpackRows Z r (i,j)) := unpackSkew_isSkew (Z r)

theorem packRows_rank_le_one {q : ℕ} (W : Matrix (Fin 2) (Fin q × Fin q) ℝ)
    (hW : W.rank ≤ 1) : (packRows W).rank ≤ 1 := by
  apply rank_le_one_of_two_column_minors
  intro j k
  exact rank_le_one_two_column_minor W hW j.val k.val

theorem unpackRows_outer {q : ℕ} (u : CircleVector) (z : UpperIndex q → ℝ) :
    unpackRows (outer u z) = outer u (fun ij => unpackSkew z ij.1 ij.2) := by
  ext r ij
  have he := congrFun (congrFun (unpackSkew_smul (u r) z) ij.1) ij.2
  exact he

theorem unpackRows_rank_le_one {q : ℕ} (Z : Matrix (Fin 2) (UpperIndex q) ℝ)
    (hZ : Z.rank ≤ 1) : (unpackRows Z).rank ≤ 1 := by
  obtain ⟨u,hu,z,he⟩ := exists_unit_outer_of_rank_le_one Z hZ
  rw [← he, unpackRows_outer]
  exact rank_outer_le_one _ _

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
  have he := congrArg (fun x : UpperIndex q => (x.val.1.val,x.val.2.val)) h
  fin_cases i <;> fin_cases j <;> simp_all [threeUpperIndices]

theorem three_le_card_upperIndex (q : ℕ) (hq : 3 ≤ q) :
    3 ≤ Fintype.card (UpperIndex q) := by
  have h := Fintype.card_le_of_injective _ (threeUpperIndices_injective q hq)
  simpa using h

end GS.Nonmanifold
