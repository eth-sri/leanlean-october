import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Set.Finite.Lattice


/-! Compact subsets of an original classical Hausdorff CW complex meet only
finitely many original open cells. The proof uses the actual weak topology
and closure-finiteness axioms. Pending Lean verification. -/

open Topology

namespace FiniteChains.ClassicalCW

variable {X : Type} [TopologicalSpace X] [T2Space X]
  [CWComplex (Set.univ : Set X)]

/-- At most one selected point lies in each original open cell. -/
def CellSeparated (S : Set X) :=
  ∀ n (j : RelCWComplex.cell (Set.univ : Set X) n),
    (S ∩ RelCWComplex.openCell n j).Subsingleton

omit [T2Space X] in
theorem CellSeparated.mono {S T : Set X} (hS : CellSeparated S) (hTS : T ⊆ S) :
    CellSeparated T := by
  intro n j x hx y hy
  aesop

omit [T2Space X] in
theorem CellSeparated.finite_inter_closedCell {S : Set X} (hS : CellSeparated S)
    (n : ℕ) (j : RelCWComplex.cell (Set.univ : Set X) n) :
    (S ∩ RelCWComplex.closedCell n j).Finite := by
  obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_openCell (C := (Set.univ : Set X)) n j
  have hf : (⋃ m : Fin n, ⋃ k ∈ I m.val, S ∩ RelCWComplex.openCell m.val k).Finite := by
    apply Set.finite_iUnion
    intro m
    exact (I m.val).finite_toSet.biUnion (fun k _ => (hS m.val k).finite)
  have hfront : (S ∩ RelCWComplex.cellFrontier n j).Finite := by
    apply hf.subset
    intro x hx
    obtain ⟨m, hm, k, hk, hcell⟩ := by
      simpa [Set.mem_iUnion] using hI hx.2
    exact Set.mem_iUnion.mpr ⟨⟨m, hm⟩,
      by aesop⟩
  rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell, Set.inter_union_distrib_left]
  exact hfront.union (hS n j).finite

theorem CellSeparated.isClosed {S : Set X} (hS : CellSeparated S) : IsClosed S := by
  apply (CWComplex.closed _ S (Set.subset_univ _)).mpr
  intro n j
  exact (hS.finite_inter_closedCell n j).isClosed

theorem CellSeparated.isDiscrete {S : Set X} (hS : CellSeparated S) : IsDiscrete S := by
  constructor
  apply discreteTopology_iff_forall_isClosed.mpr
  intro T
  have hT : CellSeparated (Subtype.val '' T) := hS.mono (by
    simp)
  have hc := hT.isClosed.preimage (continuous_subtype_val : Continuous (Subtype.val : S → X))
  simp_all

theorem CellSeparated.finite_of_subset_compact {S K : Set X} (hS : CellSeparated S)
    (hK : IsCompact K) (hSK : S ⊆ K) : S.Finite :=
  (hK.of_isClosed_subset hS.isClosed hSK).finite hS.isDiscrete

def touchedCells (K : Set X) : Set (Σ n, RelCWComplex.cell (Set.univ : Set X) n) :=
  {c | (K ∩ RelCWComplex.openCell c.1 c.2).Nonempty}

/-- Compactness plus the actual CW weak topology rules out meeting
infinitely many different open cells. -/
theorem IsCompact.finite_touchedCells {K : Set X} (hK : IsCompact K) :
    (touchedCells K).Finite := by
  let p : touchedCells K → X := fun c => Classical.choose c.property
  have heq {n m : ℕ} {i : RelCWComplex.cell Set.univ n}
      {j : RelCWComplex.cell Set.univ m} {x : X}
      (hi : x ∈ RelCWComplex.openCell n i) (hj : x ∈ RelCWComplex.openCell m j) :
      (⟨n, i⟩ : Σ n, RelCWComplex.cell (Set.univ : Set X) n) = ⟨m, j⟩ := by
    apply RelCWComplex.eq_of_not_disjoint_openCell
    grind
  have hinj : p.Injective := by
    intro c d h
    grind
  have hs : CellSeparated (Set.range p) := by
    intro n j x hx y hy
    grind
  have hpK : Set.range p ⊆ K := by
    grind
  have hf := hs.finite_of_subset_compact hK hpK
  letI : Finite (touchedCells K) := (Set.finite_range_iff hinj).mp hf
  exact Set.toFinite _

/-- A compact subset of a lower skeleton has genuine finite support by
cells of strictly lower dimension. -/
theorem IsCompact.finite_lower_support (hK : IsCompact K) (d : ℕ)
    (hKd : K ⊆ CWComplex.skeletonLT (Set.univ : Set X) (d : ℕ∞)) :
    ∃ I : ∀ m, Finset (RelCWComplex.cell (Set.univ : Set X) m),
      K ⊆ ⋃ (m < d) (j ∈ I m), RelCWComplex.closedCell m j := by
  have hT := IsCompact.finite_touchedCells hK
  have hI (m : ℕ) : ((Sigma.mk m) ⁻¹' touchedCells K).Finite :=
    Set.Finite.preimage (by simp) hT
  let I := fun m => (hI m).toFinset
  refine ⟨I, ?_⟩
  intro x hx
  have hxall : x ∈ ⋃ m, ⋃ j : RelCWComplex.cell Set.univ m,
      RelCWComplex.openCell m j := by rw [CWComplex.iUnion_openCell_eq_complex]; trivial
  obtain ⟨m, j, hj⟩ := by simpa [Set.mem_iUnion] using hxall
  have hmd : m < d := by
    by_contra h
    have hdm : (d : ℕ∞) ≤ m := by exact_mod_cast Nat.le_of_not_gt h
    exact Set.disjoint_left.mp (CWComplex.disjoint_skeletonLT_openCell (C := Set.univ)
      (j := j) hdm) (hKd hx) hj
  simp [Set.mem_iUnion]
  refine ⟨m, hmd, j, ?_, RelCWComplex.openCell_subset_closedCell m j hj⟩
  exact (Set.Finite.mem_toFinset _).mpr (by tauto)
