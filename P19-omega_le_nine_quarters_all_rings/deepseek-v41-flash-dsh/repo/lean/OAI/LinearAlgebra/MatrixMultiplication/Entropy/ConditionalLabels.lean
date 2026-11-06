module

public import OAI.LinearAlgebra.MatrixMultiplication.Separation.AuxiliarySeparation
public import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexHierarchyEntropy

public section

@[expose] section

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/


namespace MatrixMultiplication

open MatrixMultiplication.Foundation Filter
open scoped Topology BigOperators Classical

inductive ReaderPair where
  | xy | xz | yz
  deriving DecidableEq

protected abbrev ReaderPair.enumList : List ReaderPair := [.xy, .xz, .yz]

protected theorem ReaderPair.enumList_getElem?_ctorIdx_eq (x : ReaderPair) :
    ReaderPair.enumList[ReaderPair.ctorIdx x]? = some x := by
  cases x <;> rfl

protected theorem ReaderPair.enumList_nodup : ReaderPair.enumList.Nodup := by
  apply List.Nodup.of_map ReaderPair.ctorIdx
  have h : List.map ReaderPair.ctorIdx ReaderPair.enumList = List.range 3 := rfl
  exact h ▸ List.nodup_range

instance : Fintype ReaderPair where
  elems := Finset.mk ReaderPair.enumList (Multiset.coe_nodup.mpr ReaderPair.enumList_nodup)
  complete := by
    intro x
    rw [Finset.mem_mk, Multiset.mem_coe, List.mem_iff_getElem?]
    exact ⟨ReaderPair.ctorIdx x, ReaderPair.enumList_getElem?_ctorIdx_eq x⟩

namespace ConditionalLabels

universe u v

section SourceHierarchy

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

open StageHierarchyResources

end SourceHierarchy
end ConditionalLabels
end MatrixMultiplication


end OAI
