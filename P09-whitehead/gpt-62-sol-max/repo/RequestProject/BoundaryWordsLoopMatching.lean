module

public import RequestProject.HomeomorphContinuousMap
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

def loopRealization :
    Path (old r (boundaryFamilyInclusion J _) (W.vertex squareCorner00))
      (old r (boundaryFamilyInclusion J _) (W.vertex squareCorner00)) :=
  realize (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J _))
    (graphEdgePath r) W.loopWord W.loopWord_isPath

theorem corner_value (s : SquareSide) (t : I) (ht : t = 0 ∨ t = 1) :
    W.squareMap (squareSideMap s t) =
      old r (boundaryFamilyInclusion J _) (W.vertex (squareSideMap s t)) :=
  (W.squareMap_side s t).trans (W.sidePath_endpoint s t ht)

def baseEquality : old r (boundaryFamilyInclusion J _) (W.vertex squareCorner00) =
    W.squareMap squareCorner00 := (corner_value W (0, false) 0 (Or.inl rfl)).symm

def basedTraversal :
    Path (old r (boundaryFamilyInclusion J _) (W.vertex squareCorner00))
      (old r (boundaryFamilyInclusion J _) (W.vertex squareCorner00)) :=
  (squareBoundaryTraversal.map W.squareMap.continuous).cast W.baseEquality W.baseEquality

theorem basedTraversal_homotopic_loopRealization : W.basedTraversal.Homotopic W.loopRealization := by
  let vG := old r (boundaryFamilyInclusion J (Fin 1 → ℝ))
  let a₀ := W.vertex squareCorner00
  let a₁ := W.vertex squareCorner01
  let a₂ := W.vertex squareCorner11
  let a₃ := W.vertex squareCorner10
  have e₀  := W.baseEquality
  have e₁  :=
    (corner_value W (0, false) 1 (Or.inr rfl)).symm
  have e₂  :=
    (corner_value W (0, true) 1 (Or.inr rfl)).symm
  have e₃  :=
    (corner_value W (0, true) 0 (Or.inl rfl)).symm
  let D₀ := (squareTraversalLeft.map W.squareMap.continuous).cast e₀ e₁
  let D₁ := (squareTraversalTop.map W.squareMap.continuous).cast e₁ e₂
  let D₂ := (squareTraversalRight.map W.squareMap.continuous).cast e₂ e₃
  let D₃ := (squareTraversalBottom.map W.squareMap.continuous).cast e₃ e₀
  have ht : W.basedTraversal = (D₀.trans D₁).trans (D₂.trans D₃) := by
    unfold basedTraversal squareBoundaryTraversal
    rw [Path.map_trans, Path.map_trans, Path.map_trans]
    rfl
  let l₀ := W.word (0, false)
  let l₁ := W.word (1, true)
  let l₂ := Comb.revPath (X := graphCx r) (W.word (0, true))
  let l₃ := Comb.revPath (X := graphCx r) (W.word (1, false))
  have hw₀  := W.isPath (0, false)
  have hw₁ : Comb.IsPath (graphSrc r) (graphTgt r) l₁ a₁ a₂ := by
    have hh := W.isPath (1, true)
    rw [← corner01Eq, corner11Eq] at hh
    exact hh
  have hw₂  :=
    Comb.isPath_revPath (X := graphCx r) (W.isPath (0, true))
  have hw₃ : Comb.IsPath (graphSrc r) (graphTgt r) l₃ a₃ a₀ := by
    have hh := Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false))
    rw [← corner10Eq, corner00Eq] at hh
    exact hh
  have hside (s : SquareSide) (rev : Bool) {a b : V}
      (h : Comb.IsPath (graphSrc r) (graphTgt r)
        (if rev then Comb.revPath (X := graphCx r) (W.word s) else W.word s) a b)
      (ha : a = W.vertex (squareSideMap s (if rev then 1 else 0)))
      (hb : b = W.vertex (squareSideMap s (if rev then 0 else 1)))
      (D : Path (vG a) (vG b))
      (hD : ∀ t : I, D t = W.squareMap (squareSideMap s (if rev then unitInterval.symm t else t))) :
      D.Homotopic (realize (graphSrc r) (graphTgt r) vG (graphEdgePath r) _ h) := by
    subst a b
    cases rev
    · have he : D = W.sidePath s := Path.ext (funext fun t => (hD t).trans (W.squareMap_side s t))
      rw [he]
      exact Path.Homotopic.refl _
    · have he : D = (W.sidePath s).symm := Path.ext (funext fun t =>
        (hD t).trans (W.squareMap_side s (unitInterval.symm t)))
      rw [he]
      exact realize_revPath (K := graphCx r) vG (graphEdgePath r) (W.word s) (W.isPath s)
  have H₀ := hside (0, false) false hw₀ rfl rfl D₀ (fun _ => rfl)
  have H₁ := hside (1, true) false hw₁ (congrArg W.vertex corner01Eq)
    (congrArg W.vertex corner11Eq.symm) D₁ (fun _ => rfl)
  have H₂ := hside (0, true) true hw₂ rfl rfl D₂ (fun _ => rfl)
  have H₃ := hside (1, false) true hw₃ (congrArg W.vertex corner10Eq)
    (congrArg W.vertex corner00Eq.symm) D₃ (fun _ => rfl)
  have Hleft := realize_append (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₀ l₁ hw₀ hw₁
  have Hright := realize_append (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₂ l₃ hw₂ hw₃
  have Happend := realize_append (graphSrc r) (graphTgt r) vG (graphEdgePath r)
    (l₀ ++ l₁) (l₂ ++ l₃) (hw₀.append hw₁) (hw₂.append hw₃)
  rw [ht]
  have Hall := ((H₀.hcomp H₁).hcomp (H₂.hcomp H₃)).trans ((Hleft.hcomp Hright).trans Happend)
  simpa only [loopRealization, loopWord, l₀, l₁, l₂, l₃, List.append_eq, List.append_assoc] using Hall

theorem squareLoopDesc_basedTraversal : squareLoopDesc W.basedTraversal = W.squareMap := by
  have hc : squareLoopDesc W.basedTraversal =
      squareLoopDesc (squareBoundaryTraversal.map W.squareMap.continuous) := by
    tauto
  exact hc.trans (squareLoopDesc_map W.squareMap)

def loopBoundaryMap : C(UnitBoundary (Fin 2 → ℝ), DiskAttachment r) :=
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
