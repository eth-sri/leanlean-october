import RequestProject.ClassicalCWChainPresentation
import RequestProject.ClassicalChartedGraphComparison
import RequestProject.Tac


/-! Prescribed original graph words are retained at stage zero. The
remaining cells still obtain actual words and homotopies from the graph
approximation theorem. Unverified source. -/

noncomputable section
bwd

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel
open Set Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C)

def seededChoices
    (W : ∀ _j,
      BoundaryWords (skeletonAttachingMap (C 0 : Set K) 1))
    (hW : ∀ j, (subcomplexCellBoundary (C 0) j).Homotopic (W j).boundaryMap) : Choices C where
  cellWord i j := if hi : i = 0 then by subst i; exact W j
    else Classical.choose (subcomplexCellBoundary_word_exists (C i) j)
  cellWord_spec i j := by
    split_ifs with hi
    · aesop
    grind

theorem seededChoices_zero
    W
    hW
    j :
    Choices.cellWord (self := seededChoices K C W hW) 0 j = W j := by
  rfl

theorem word_zero [Choices C] j :
    word C hC 0 j = Choices.cellWord 0 j := by
  have hh (a : Fin (n + 1)) (ha : a ≤ 0) (hj : j.val ∈ (C a).I 2) :
      (Choices.cellWord a ⟨j.val, hj⟩).map (subcomplexGraphInclusion (hC ha)) =
        Choices.cellWord 0 j := by
    have hz : a = 0 := by simp_all
    subst a
    have he : subcomplexGraphInclusion (hC ha) = Comb.Hom.id _ := by
      apply Comb.Hom.ext'
      · rfl
      · rfl
      · funext f
        exact f.elim
    rw [he]
    cases Choices.cellWord 0 j
    simp [BoundaryWords.map, Comb.Hom.id, Comb.mapPath]
  exact hh _
    (birth_le C _ 0 j.property) _

def seededTreeChoice (T : Comb.SpanningTree (subcomplexGraph (C 0))) : TreeChoice K C := ⟨some T⟩

end FiniteChains.ClassicalCW.ChainWords

namespace FiniteChains.ClassicalCW
open ClassicalGraphModel Comb Topology
open scoped Classical
variable (K : Whitehead.TwoComplex) (T : SpanningTree (originalGraph K))

abbrev FixedGen := T.NonTree ⊕ PUnit.{1}
abbrev FixedRel := RelCWComplex.cell (Set.univ : Set K) 2 ⊕ PUnit.{1}

def fixedRelators : FixedRel K → FreeGroup (FixedGen K T)
  | .inl j => FreeGroup.map Sum.inl (SpanningTree.pathWord T (fixedGraphWord K j).loopWord)
  | .inr _ => FreeGroup.of (Sum.inr PUnit.unit)
