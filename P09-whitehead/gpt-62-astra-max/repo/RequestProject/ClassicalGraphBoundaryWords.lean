module


public import RequestProject.ClassicalGraphPathStraightening
public import RequestProject.IntervalEndpointHomotopyExtension


@[expose] public section

/-! Genuine attaching-circle maps into a graph can be replaced by finite
words in its actual edges, through homotopies entirely in that graph. Four
side words retain their exact parametrized attaching map. Pending Lean
verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment ContinuousEdgeWords

variable {V J : Type} [TopologicalSpace V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V)

/-- Finite words on the four sides, with their exact corner incidences. -/
structure BoundaryWords where
  vertex : SquareBoundary → V
  word : SquareSide → List _
  isPath : ∀ s, Comb.IsPath (graphSrc r) (graphTgt r) (word s)
    (vertex (squareSideMap s 0)) (vertex (squareSideMap s 1))

namespace BoundaryWords

variable {r} (W : BoundaryWords r)

variable (s : SquareSide)

def sidePath :=
  realize _ _ _
    (graphEdgePath r) _ (W.isPath s)

theorem sidePath_endpoint (t : I) (ht : t = 0 ∨ t = 1) :
    W.sidePath s t = old r _
      (W.vertex (squareSideMap s t)) := by
  rcases ht with rfl | rfl
  · exact (W.sidePath s).source
  · simp

def squareMap :=
  squareBoundaryPasting _
    (fun z => old r _ _)
    W.sidePath_endpoint

@[simp] theorem squareMap_side (s : SquareSide) (t : I) :
    W.squareMap (squareSideMap s t) = W.sidePath s t :=
  squareBoundaryPasting_side _ _ _ s t

def boundaryMap :=
  W.squareMap.comp unitBoundarySquareHomeomorph.toContinuousMap

/-- The based combinatorial word obtained by travelling around the four
sides, reversing the two sides whose coordinate direction opposes travel. -/
def loopWord :=
  List.append
    (List.append (α := J × Bool)
      (List.append (W.word (0, false)) (W.word (1, true)))
      (Comb.revPath (X := graphCx r) (W.word (0, true))))
    (Comb.revPath (X := graphCx r) (W.word (1, false)))

theorem corner01 : squareSideMap (0, false) 1 = squareSideMap (1, true) 0 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner11 : squareSideMap (1, true) 1 = squareSideMap (0, true) 1 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner10 : squareSideMap (0, true) 0 = squareSideMap (1, false) 1 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

theorem corner00 : squareSideMap (1, false) 0 = squareSideMap (0, false) 0 := by
  apply Subtype.ext
  funext i
  fin_cases i <;> rfl

omit [TopologicalSpace V] in
theorem loopWord_isPath : Comb.IsPath (graphSrc r) (graphTgt r) W.loopWord
    (W.vertex (squareSideMap (0, false) 0)) (W.vertex (squareSideMap (0, false) 0)) := by
  have h₁ := W.isPath (1, true)
  have h₂ := Comb.isPath_revPath (X := graphCx r) (W.isPath (0, true))
  have h₃ := Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false))
  rw [← corner01] at h₁
  rw [← corner11] at h₂
  rw [← corner10, corner00] at h₃
  exact (((W.isPath _).append h₁).append h₂).append h₃

end BoundaryWords

variable [DiscreteTopology V] (hr : Continuous r)
include hr

/-- The endpoint motions and edge-word homotopies descend through the
actual four-side quotient. No cellular approximation premise is assumed. -/
theorem squareMap_homotopic_boundaryWords
    (f : C(SquareBoundary, DiskAttachment r)) :
    ∃ W : BoundaryWords r, f.Homotopic W.squareMap := by
  let v := fun z => graphSnap r (f z)
  let p (z : SquareBoundary) := graphConnector r (f z)
  let E (s : SquareSide) := intervalEndpointExtension (f.comp (squareSideMap s))
    (p (squareSideMap s 0)) (p (squareSideMap s 1))
  have hE : ∀ s τ t, t = 0 ∨ t = 1 →
      (E s).map (τ, t) = p (squareSideMap s t) τ := by
    intro s τ t ht
    rcases ht with rfl | rfl
    · exact (E s).side_zero τ
    · exact (E s).side_one τ
  let G := squareBoundaryHomotopyPasting _ (fun τ z => p z τ) hE
  let f₁ :=
    G.comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  let H₀ : f.Homotopy f₁ := {
    toContinuousMap := G
    map_zero_left := by
      intro z
      obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
      change G (0, squareSideMap s t) = f _
      rw [squareBoundaryHomotopyPasting_side]
      exact (E s).zero t
    map_one_left := fun _ => rfl }
  let l (s : SquareSide) :
      Path _
        (old r _ (v (squareSideMap s 1))) := {
    toFun := fun t => (E s).map _
    continuous_toFun := (E s).map.continuous.comp (continuous_const.prodMk continuous_id)
    source' := ((E s).side_zero 1).trans (p (squareSideMap s 0)).target
    target' := ((E s).side_one 1).trans (p (squareSideMap s 1)).target }
  choose w hw Hwords using (fun s => graph_path_isWord r hr _ _ (l s))
  let W : BoundaryWords r := ⟨v, w, hw⟩
  let H (s : SquareSide) := Classical.choice (Hwords s)
  have hHV : ∀ s τ t, t = 0 ∨ t = 1 →
      H s (τ, t) = old r _
        (v (squareSideMap s t)) := by
    intro s τ t ht
    rcases ht with rfl | rfl
    · exact (H s).source τ
    · simp
  let G₁ := squareBoundaryHomotopyPasting _
    (fun _ z => old r _ _) hHV
  let H₁ : f₁.Homotopy W.squareMap := {
    toContinuousMap := G₁
    map_zero_left := by
      intro z
      obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
      change G₁ (0, squareSideMap s t) = G (1, squareSideMap s t)
      aesop
    map_one_left := by
      intro z
      obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
      change G₁ (1, squareSideMap s t) = W.squareMap (squareSideMap s t)
      aesop }
  exact ⟨W, ⟨H₀.trans H₁⟩⟩

theorem boundaryMap_homotopic_boundaryWords
    (f : C(UnitBoundary (Fin 2 → ℝ), DiskAttachment r)) :
    ∃ W : BoundaryWords r, f.Homotopic W.boundaryMap := by
  let e := unitBoundarySquareHomeomorph
  obtain ⟨W, hW⟩ := squareMap_homotopic_boundaryWords r hr (f.comp e.symm.toContinuousMap)
  have H := hW.comp (ContinuousMap.Homotopic.refl e.toContinuousMap)
  aesop

end FiniteChains.ClassicalGraphModel
