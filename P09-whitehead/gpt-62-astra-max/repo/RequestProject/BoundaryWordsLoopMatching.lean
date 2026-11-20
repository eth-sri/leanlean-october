module


public import RequestProject.ClassicalGraphBoundaryWords
public import RequestProject.ContinuousEdgeWordHomotopies
public import RequestProject.SquareBoundaryLoopQuotient

@[expose] public section

/-! The actual four-side attaching map is homotopic to the descended
continuous realization of its based edge word. This retains a homotopy
of circle maps, not merely equality in the fundamental group. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.ClassicalGraphModel.BoundaryWords
open RelativeAttachment ContinuousEdgeWords
open scoped Classical unitInterval

variable {V J : Type} [TopologicalSpace V]
    {r : BoundaryFamily J (Fin 1 → ℝ) → V} (W : BoundaryWords r)

theorem corner01Eq : squareSideMap (0, false) 1 = squareSideMap (1, true) 0 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner11Eq : squareSideMap (1, true) 1 = squareSideMap (0, true) 1 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner10Eq : squareSideMap (0, true) 0 = squareSideMap (1, false) 1 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner00Eq : squareSideMap (1, false) 0 = squareSideMap (0, false) 0 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem realize_cast_eq {V E X : Type} [TopologicalSpace X]
    (src tgt : E → V) (v : V → X) (edge : ∀ e, Path _ (v _))
    (l : List _) {a b a' b' : V}
    (hl : Comb.IsPath src tgt l a b) (hl' : Comb.IsPath src tgt l a' b')
    (ha : a' = a) (hb : b' = b) :
    (realize src tgt v edge l hl).cast (congrArg v ha) (congrArg v hb) =
      realize src tgt v edge l hl' := by
  aesop

def loopRealization :
    Path (old r (boundaryFamilyInclusion J _) (W.vertex squareCorner00))
      (old r _ (W.vertex squareCorner00)) :=
  realize _ _ _
    (graphEdgePath r) W.loopWord W.loopWord_isPath

theorem corner_value (s : SquareSide) (t : I) (ht : t = 0 ∨ t = 1) :
    W.squareMap (squareSideMap s t) =
      old r _ (W.vertex (squareSideMap s t)) :=
  (W.squareMap_side s t).trans (W.sidePath_endpoint s t ht)

def baseEquality : old r _ (W.vertex squareCorner00) =
    W.squareMap squareCorner00 := (corner_value W _ 0 (Or.inl rfl)).symm

def basedTraversal :=
  (squareBoundaryTraversal.map W.squareMap.continuous).cast W.baseEquality W.baseEquality

theorem basedTraversal_homotopic_loopRealization : W.basedTraversal.Homotopic W.loopRealization := by
  let vG := old r (boundaryFamilyInclusion J (Fin 1 → ℝ))
  have e₀ := W.baseEquality
  have e₁ :=
    (corner_value W (0, false) 1 (Or.inr rfl)).symm
  have e₂ :=
    (corner_value W (0, true) 1 (Or.inr rfl)).symm
  have e₃ :=
    (corner_value W (0, true) 0 (Or.inl rfl)).symm
  let D₀ := (squareTraversalLeft.map W.squareMap.continuous).cast e₀ e₁
  let D₁ := (squareTraversalTop.map W.squareMap.continuous).cast e₁ e₂
  let D₂ := (squareTraversalRight.map W.squareMap.continuous).cast e₂ e₃
  let D₃ := (squareTraversalBottom.map W.squareMap.continuous).cast e₃ e₀
  have ht : W.basedTraversal = (D₀.trans D₁).trans (D₂.trans D₃) := by
    unfold basedTraversal squareBoundaryTraversal
    aesop
  let l₀ := W.word (0, false)
  let l₁ := W.word (1, true)
  let l₂ := Comb.revPath (X := graphCx r) (W.word (0, true))
  let l₃ := Comb.revPath (X := graphCx r) (W.word (1, false))
  have hw₀ := W.isPath (0, false)
  have hw₁ : Comb.IsPath (graphSrc r) (graphTgt r) l₁ (W.vertex squareCorner01) (W.vertex squareCorner11) := by
    have hh := W.isPath (1, true)
    rw [← corner01Eq, corner11Eq] at hh
    exact hh
  have hw₂ :=
    Comb.isPath_revPath (X := graphCx r) (W.isPath (0, true))
  have hw₃ : Comb.IsPath (graphSrc r) (graphTgt r) l₃ (W.vertex squareCorner10) (W.vertex squareCorner00) := by
    have hh := Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false))
    rw [← corner10Eq, corner00Eq] at hh
    exact hh
  let R₀ := realize _ _ vG (graphEdgePath r) l₀ hw₀
  let R₁ := realize _ _ vG (graphEdgePath r) l₁ hw₁
  let R₂ := realize _ _ vG (graphEdgePath r) l₂ hw₂
  let R₃ := realize _ _ vG (graphEdgePath r) l₃ hw₃
  have H₀ : D₀.Homotopic R₀ := by
    have he : D₀ = R₀ := by
      apply Path.ext
      funext t
      apply W.squareMap_side
    aesop
  have H₁ : D₁.Homotopic R₁ := by
    have ha := congrArg W.vertex corner01Eq
    have hb := congrArg W.vertex corner11Eq.symm
    have hd : D₁ = (W.sidePath _).cast (congrArg vG ha) (congrArg vG hb) := by
      apply Path.ext
      funext t
      apply W.squareMap_side
    have he := hd.trans (realize_cast_eq (graphSrc r) (graphTgt r) vG
      (graphEdgePath r) l₁ (W.isPath (1, true)) hw₁ ha hb)
    aesop
  have H₂ : D₂.Homotopic R₂ := by
    have hd : D₂ = (W.sidePath _).symm := by
      apply Path.ext
      funext t
      apply W.squareMap_side
    rw [hd]
    exact realize_revPath (K := graphCx r) vG _
      _ _
  have H₃ : D₃.Homotopic R₃ := by
    have ha := congrArg W.vertex corner10Eq
    have hb := congrArg W.vertex corner00Eq.symm
    have hd : (W.sidePath _).symm.cast (congrArg vG ha) (congrArg vG hb) = D₃ := by
      apply Path.ext
      funext t
      exact (W.squareMap_side _ _).symm
    have HH := (realize_revPath (K := graphCx r) vG (graphEdgePath r)
      _ (W.isPath (1, false))).pathCast (congrArg vG ha) (congrArg vG hb)
    have hr : (realize _ _ vG (graphEdgePath r) l₃
        (Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false)))).cast
          _ _ = R₃ :=
      realize_cast_eq _ _ vG _ l₃ _ hw₃ ha hb
    change ((W.sidePath _).symm.cast _ _).Homotopic
      ((realize (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₃
        (Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false)))).cast
          (congrArg vG ha) (congrArg vG hb)) at HH
    simp_all
  have Hs : W.basedTraversal.Homotopic ((R₀.trans R₁).trans (R₂.trans R₃)) := by
    rw [ht]
    exact (H₀.hcomp H₁).hcomp (H₂.hcomp H₃)
  have Happend := realize_append _ _ vG (graphEdgePath r)
    _ _ (hw₀.append hw₁) (hw₂.append hw₃)
  have Hall := Hs.trans (((realize_append (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₀ l₁ hw₀ hw₁).hcomp (realize_append (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₂ l₃ hw₂ hw₃)).trans Happend)
  simpa only [loopRealization, loopWord, l₀, l₁, l₂, l₃, List.append_eq, List.append_assoc] using Hall

theorem squareLoopDesc_basedTraversal : squareLoopDesc W.basedTraversal = W.squareMap := by
  have hc : squareLoopDesc W.basedTraversal =
      squareLoopDesc (squareBoundaryTraversal.map W.squareMap.continuous) := by
    solve_by_elim
  exact hc.trans (squareLoopDesc_map W.squareMap)

def loopBoundaryMap :=
  (squareLoopDesc W.loopRealization).comp unitBoundarySquareHomeomorph.toContinuousMap

theorem boundaryMap_homotopic_loopBoundaryMap : W.boundaryMap.Homotopic W.loopBoundaryMap := by
  have H := squareLoopDesc_homotopic W.basedTraversal_homotopic_loopRealization
  rw [W.squareLoopDesc_basedTraversal] at H
  exact H.comp (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap)

theorem boundaryMap_homotopic_word : W.boundaryMap.Homotopic
    ((squareLoopDesc (realize (graphSrc r) (graphTgt r)
      (old r (boundaryFamilyInclusion J _)) (graphEdgePath r)
      W.loopWord W.loopWord_isPath)).comp unitBoundarySquareHomeomorph.toContinuousMap) :=
  W.boundaryMap_homotopic_loopBoundaryMap

end FiniteChains.ClassicalGraphModel.BoundaryWords
