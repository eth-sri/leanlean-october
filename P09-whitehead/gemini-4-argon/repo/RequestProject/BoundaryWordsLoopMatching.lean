module

public import RequestProject.HomeomorphContinuousMap
public import RequestProject.ClassicalGraphBoundaryWords
public import RequestProject.ContinuousEdgeWordHomotopies
public import RequestProject.SquareBoundaryLoopQuotient

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.ClassicalGraphModel.BoundaryWords
open RelativeAttachment ContinuousEdgeWords
open scoped Classical unitInterval

variable {V J : Type} [TopologicalSpace V]
    {r : BoundaryFamily J (Fin 1 → ℝ) → V} (W : BoundaryWords r)

theorem boundaryMap_homotopic_word : W.boundaryMap.Homotopic
    ((squareLoopDesc (realize (graphSrc r) (graphTgt r)
      (old r (boundaryFamilyInclusion J _)) (graphEdgePath r)
      W.loopWord W.loopWord_isPath)).comp unitBoundarySquareHomeomorph.toContinuousMap) := by
  have c01 : squareSideMap (0, false) 1 = squareSideMap (1, true) 0 :=
    Subtype.ext (funext fun i => by fin_cases i <;> rfl)
  have c11 : squareSideMap (1, true) 1 = squareSideMap (0, true) 1 :=
    Subtype.ext (funext fun i => by fin_cases i <;> rfl)
  have c10 : squareSideMap (0, true) 0 = squareSideMap (1, false) 1 :=
    Subtype.ext (funext fun i => by fin_cases i <;> rfl)
  have c00 : squareSideMap (1, false) 0 = squareSideMap (0, false) 0 :=
    Subtype.ext (funext fun i => by fin_cases i <;> rfl)
  have rcast (l : List (J × Bool)) {a b a' b' : V}
      (hl : Comb.IsPath (graphSrc r) (graphTgt r) l a b)
      (hl' : Comb.IsPath (graphSrc r) (graphTgt r) l a' b')
      (ha : a' = a) (hb : b' = b) :
      (realize (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J _))
        (graphEdgePath r) l hl).cast
        (congrArg (old r (boundaryFamilyInclusion J _)) ha)
        (congrArg (old r (boundaryFamilyInclusion J _)) hb) =
        realize (graphSrc r) (graphTgt r) (old r (boundaryFamilyInclusion J _))
          (graphEdgePath r) l hl' := by cases ha; cases hb; rfl
  let vG := old r (boundaryFamilyInclusion J (Fin 1 → ℝ))
  have cval (s : SquareSide) (t : I) (ht : t = 0 ∨ t = 1) :
      W.squareMap (squareSideMap s t) = vG (W.vertex (squareSideMap s t)) :=
    (W.squareMap_side s t).trans (W.sidePath_endpoint s t ht)
  let a₀ := W.vertex squareCorner00
  let a₁ := W.vertex squareCorner01
  let a₂ := W.vertex squareCorner11
  let a₃ := W.vertex squareCorner10
  have e₀ : vG a₀ = W.squareMap squareCorner00 := (cval (0, false) 0 (.inl rfl)).symm
  have e₁ : vG a₁ = W.squareMap squareCorner01 := (cval (0, false) 1 (.inr rfl)).symm
  have e₂ : vG a₂ = W.squareMap squareCorner11 := (cval (0, true) 1 (.inr rfl)).symm
  have e₃ : vG a₃ = W.squareMap squareCorner10 := (cval (0, true) 0 (.inl rfl)).symm
  let D₀ := (squareTraversalLeft.map W.squareMap.continuous).cast e₀ e₁
  let D₁ := (squareTraversalTop.map W.squareMap.continuous).cast e₁ e₂
  let D₂ := (squareTraversalRight.map W.squareMap.continuous).cast e₂ e₃
  let D₃ := (squareTraversalBottom.map W.squareMap.continuous).cast e₃ e₀
  let bt : Path (vG a₀) (vG a₀) := (squareBoundaryTraversal.map W.squareMap.continuous).cast e₀ e₀
  have ht : bt = (D₀.trans D₁).trans (D₂.trans D₃) := by
    dsimp [bt, squareBoundaryTraversal]
    rw [Path.map_trans, Path.map_trans, Path.map_trans]; rfl
  let l₀ := W.word (0, false)
  let l₁ := W.word (1, true)
  let l₂ := Comb.revPath (X := graphCx r) (W.word (0, true))
  let l₃ := Comb.revPath (X := graphCx r) (W.word (1, false))
  have hw₀ : Comb.IsPath (graphSrc r) (graphTgt r) l₀ a₀ a₁ := W.isPath (0, false)
  have hw₁ : Comb.IsPath (graphSrc r) (graphTgt r) l₁ a₁ a₂ := by
    have hh := W.isPath (1, true); rwa [← c01, c11] at hh
  have hw₂ : Comb.IsPath (graphSrc r) (graphTgt r) l₂ a₂ a₃ :=
    Comb.isPath_revPath (X := graphCx r) (W.isPath (0, true))
  have hw₃ : Comb.IsPath (graphSrc r) (graphTgt r) l₃ a₃ a₀ := by
    have hh := Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false)); rwa [← c10, c00] at hh
  let R₀ := realize (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₀ hw₀
  let R₁ := realize (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₁ hw₁
  let R₂ := realize (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₂ hw₂
  let R₃ := realize (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₃ hw₃
  have H₀ : D₀.Homotopic R₀ := by
    rw [show D₀ = R₀ from Path.ext (funext (W.squareMap_side (0, false)))]
  have H₁ : D₁.Homotopic R₁ := by
    have ha : a₁ = W.vertex (squareSideMap (1, true) 0) := congrArg W.vertex c01
    have hb : a₂ = W.vertex (squareSideMap (1, true) 1) := congrArg W.vertex c11.symm
    have he : D₁ = R₁ := (Path.ext (funext (W.squareMap_side (1, true))) :
      D₁ = (W.sidePath (1, true)).cast (congrArg vG ha) (congrArg vG hb)).trans
      (rcast l₁ (W.isPath (1, true)) hw₁ ha hb)
    rw [he]
  have H₂ : D₂.Homotopic R₂ := by
    rw [show D₂ = (W.sidePath (0, true)).symm from
      Path.ext (funext fun t => W.squareMap_side (0, true) (unitInterval.symm t))]
    exact realize_revPath (K := graphCx r) vG (graphEdgePath r) (W.word (0, true)) (W.isPath (0, true))
  have H₃ : D₃.Homotopic R₃ := by
    have ha : a₃ = W.vertex (squareSideMap (1, false) 1) := congrArg W.vertex c10
    have hb : a₀ = W.vertex (squareSideMap (1, false) 0) := congrArg W.vertex c00.symm
    have hd : (W.sidePath (1, false)).symm.cast (congrArg vG ha) (congrArg vG hb) = D₃ :=
      Path.ext (funext fun t => (W.squareMap_side (1, false) (unitInterval.symm t)).symm)
    have HH := (realize_revPath (K := graphCx r) vG (graphEdgePath r)
      (W.word (1, false)) (W.isPath (1, false))).pathCast (congrArg vG ha) (congrArg vG hb)
    have hr := rcast l₃ (Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false))) hw₃ ha hb
    change ((W.sidePath (1, false)).symm.cast (congrArg vG ha) (congrArg vG hb)).Homotopic
      ((realize (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₃
        (Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false)))).cast
          (congrArg vG ha) (congrArg vG hb)) at HH
    rwa [hd, hr] at HH
  have Hall : bt.Homotopic (realize (graphSrc r) (graphTgt r) vG (graphEdgePath r)
      W.loopWord W.loopWord_isPath) := by
    simpa only [loopWord, l₀, l₁, l₂, l₃, List.append_eq, List.append_assoc] using
      (by rw [ht]; exact (H₀.hcomp H₁).hcomp (H₂.hcomp H₃) :
        bt.Homotopic ((R₀.trans R₁).trans (R₂.trans R₃))).trans
      (((realize_append (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₀ l₁ hw₀ hw₁).hcomp
        (realize_append (graphSrc r) (graphTgt r) vG (graphEdgePath r) l₂ l₃ hw₂ hw₃)).trans
        (realize_append (graphSrc r) (graphTgt r) vG (graphEdgePath r)
          (l₀ ++ l₁) (l₂ ++ l₃) (hw₀.append hw₁) (hw₂.append hw₃)))
  have H := squareLoopDesc_homotopic Hall
  rw [(ContinuousMap.ext fun _ => rfl :
    squareLoopDesc bt = squareLoopDesc (squareBoundaryTraversal.map W.squareMap.continuous)).trans
    (squareLoopDesc_map W.squareMap)] at H
  exact H.comp (ContinuousMap.Homotopic.refl unitBoundarySquareHomeomorph.toContinuousMap)

end FiniteChains.ClassicalGraphModel.BoundaryWords
