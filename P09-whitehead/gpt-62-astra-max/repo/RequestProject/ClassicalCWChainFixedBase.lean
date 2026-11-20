module

public import RequestProject.ClassicalCWChainSeeded

@[expose] public section

/-! Rebasing the constructed chain on prescribed original words and a
prescribed original tree. The base maps are genuine injective maps of
generators and two-cell labels, and their relator equation is proved.
Unverified source. -/

noncomputable section

namespace FiniteChains.ClassicalCW.ChainWords
open ClassicalSkeletonAttachment ClassicalGraphModel RelativeAttachment PresModel Comb
open Set Topology
open scoped Classical
variable (D K : Whitehead.TwoComplex) {n : ℕ}
  (C : Fin (n + 1) → CWComplex.Subcomplex (Set.univ : Set K))
  (hC : Monotone C) (hconn : ∀ i, ConnectedSpace (C i : Set K))
  [Choices C] [TreeChoice K C]
  (T : SpanningTree (originalGraph D))
  (g : Hom (originalGraph D) (subcomplexGraph (C 0)))
  (hg : Function.Injective g.onE)
  (c : RelCWComplex.cell (Set.univ : Set D) 2 ↪ RelCWComplex.cell (C 0 : Set K) 2)
  (hw : ∀ j, Choices.cellWord 0 (c j) = (fixedGraphWord D j).map g)
  (ht : ∀ a, (chainTree K C hC hconn 0).isTree (g.onE a) ↔ T.isTree a)

def fixedBaseGen : FixedGen D T ↪ CanonicalGen K C hC hconn 0 :=
  StabilizedDiskPresentation.withDummy
    ⟨SpanningTree.nonTreeIncl ht, SpanningTree.nonTreeIncl_injective ht hg⟩

def fixedBaseCell : FixedRel D ↪ CanonicalRel K C 0 :=
  StabilizedDiskPresentation.withDummy c

include hw in
theorem fixedBase_relators (j : FixedRel D) :
    canonicalRelators K C hC hconn 0 (fixedBaseCell D K C c j) =
      FreeGroup.map (fixedBaseGen D K C hC hconn T g hg ht) (fixedRelators D T j) := by
  cases j with
  | inl j =>
      letI := subcomplexZeroSkeleton_discrete (C 0)
      change FreeGroup.map Sum.inl (FreeGroup.mk
        (((word C hC 0 (c j)).eraseTree (skeletonAttachingMap (C 0 : Set K) 1)
          (chainTree K C hC hconn 0)).loopWord)) = _
      erw [BoundaryWords.eraseTree_mk, word_zero, hw, BoundaryWords.loopWord_map,
        SpanningTree.pathWord_mapPath ht]
      erw [FreeGroup.map.comp, FreeGroup.map.comp]; rfl
  | inr u =>
      rfl

variable (hkill : ∀ i : Fin n, Whitehead.KillsPi2 (⟨Set.inclusion (hC (show i.castSucc ≤ i.succ from Nat.le_succ i.val)), continuous_inclusion _⟩ : C((C i.castSucc : Set K), (C i.succ : Set K))))

def fixedPresChainFS :
    PresChainFS (fixedRelators D T) n where
  gen r := CanonicalGen K C hC hconn (boundedStage n r)
  cell r := CanonicalRel K C (boundedStage n r)
  decGen _ := inferInstance
  rel r := canonicalRelators K C hC hconn (boundedStage n r)
  genIncl r := canonicalGenInclusion K C hC hconn (boundedStage_monotone n (Nat.le_succ r))
  cellIncl r := canonicalCellInclusion K C hC (boundedStage_monotone n (Nat.le_succ r))
  rel_incl r := canonicalRelators_natural K C hC hconn (boundedStage_monotone n (Nat.le_succ r))
  baseGen := fixedBaseGen D K C hC hconn T g hg ht
  baseCell := fixedBaseCell D K C c
  rel_base := fixedBase_relators D K C hC hconn T g hg c hw ht
  zero_pi2 r hr := by
    let h := boundedStage_monotone n (Nat.le_succ r)
    apply (zeroPi2_presInclHom_iff (ρ := canonicalRelators K C hC hconn (boundedStage n r)) (σ := canonicalRelators K C hC hconn (boundedStage n (r + 1))) (canonicalGenInclusion K C hC hconn h)
      (canonicalGenInclusion K C hC hconn h).injective (canonicalCellInclusion K C hC h)
      (canonicalRelators_natural K C hC hconn h)).mp
    apply canonicalInclusion_zeroPi2
    let i : Fin n := ⟨r, hr⟩
    have step (a b : Fin (n+1)) (hab : a ≤ b) (ha : a = i.castSucc) (hb : b = i.succ) :
        Whitehead.KillsPi2 (⟨Set.inclusion (hC hab), continuous_inclusion _⟩ : C((C a : Set K), (C b : Set K))) := by
      subst a b
      exact hkill i
    exact step _ _ h (Fin.ext (Nat.min_eq_left hr.le)) (Fin.ext (Nat.min_eq_left hr))

end FiniteChains.ClassicalCW.ChainWords
