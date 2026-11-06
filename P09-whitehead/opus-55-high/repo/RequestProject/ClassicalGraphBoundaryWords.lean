import RequestProject.HomeomorphContinuousMap
import RequestProject.ClassicalGraphPathStraightening
import RequestProject.IntervalEndpointHomotopyExtension
import RequestProject.SquareBoundaryNormHomeomorph


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
  word : SquareSide → List (J × Bool)
  isPath : ∀ s, Comb.IsPath (graphSrc r) (graphTgt r) (word s)
    (vertex (squareSideMap s 0)) (vertex (squareSideMap s 1))

namespace BoundaryWords

variable {r} (W : BoundaryWords r)

def sidePath s :=
  realize _ _ _
    (graphEdgePath r) _ (W.isPath s)

theorem sidePath_endpoint s t (ht : t = 0 ∨ t = 1) :
    W.sidePath s t = old r (boundaryFamilyInclusion J (Fin 1 → ℝ))
      (W.vertex (squareSideMap s t)) := by
  grind

def squareMap : C(SquareBoundary, DiskAttachment r) :=
  squareBoundaryPasting _
    (fun z => old r _ (W.vertex z))
    W.sidePath_endpoint

@[simp] theorem squareMap_side s t :
    W.squareMap (squareSideMap s t) = W.sidePath s t :=
  squareBoundaryPasting_side _ _ _ s t

def boundaryMap :=
  W.squareMap.comp unitBoundarySquareHomeomorph.toContinuousMap

/-- The based combinatorial word obtained by travelling around the four
sides, reversing the two sides whose coordinate direction opposes travel. -/
def loopWord :=
  List.append (α := J × Bool)
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
  have h₀ := W.isPath (0, false)
  have h₁ := W.isPath (1, true)
  have h₂ := Comb.isPath_revPath (X := graphCx r) (W.isPath (0, true))
  have h₃ := Comb.isPath_revPath (X := graphCx r) (W.isPath (1, false))
  rw [← corner01] at h₁
  rw [← corner11] at h₂
  rw [← corner10, corner00] at h₃
  exact ((h₀.append h₁).append h₂).append h₃

end BoundaryWords

/-- The endpoint motions and edge-word homotopies descend through the
actual four-side quotient. No cellular approximation premise is assumed. -/
theorem squareMap_homotopic_boundaryWords [DiscreteTopology V] (hr : Continuous r)
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
  let f₁ : C(SquareBoundary, DiskAttachment r) :=
    G.comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  let H₀ : f.Homotopy f₁ := {
    toContinuousMap := G
    map_zero_left := by
      intro z
      obtain ⟨⟨s, t⟩, rfl⟩ := squareSideQuotient_surjective z
      change G (0, squareSideMap s t) = f (squareSideMap s t)
      rw [squareBoundaryHomotopyPasting_side]
      exact (E s).zero t
    map_one_left := fun _ => rfl }
  let l (s : SquareSide) :
      Path (old r _ (v (squareSideMap s 0)))
        (old r _ (v (squareSideMap s 1))) := {
    toFun := fun t => (E s).map (1, t)
    continuous_toFun := (E s).map.continuous.comp (continuous_const.prodMk continuous_id)
    source' := by grind
    target' := by grind }
  have hwords := fun s => graph_path_isWord r hr _ _ (l s)
  choose w hw Hwords using hwords
  let W : BoundaryWords r := by tauto
  let H (s : SquareSide) := Classical.choice (Hwords s)
  have hHV : ∀ s τ t, t = 0 ∨ t = 1 →
      H s (τ, t) = old r _
        (v (squareSideMap s t)) := by
    simp
  let G₁ := squareBoundaryHomotopyPasting _
    (fun _ z => old r _ (v z)) hHV
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

theorem boundaryMap_homotopic_boundaryWords [DiscreteTopology V] (hr : Continuous r)
    (f : C(UnitBoundary (Fin 2 → ℝ), DiskAttachment r)) :
    ∃ W : BoundaryWords r, f.Homotopic W.boundaryMap := by
  let e := unitBoundarySquareHomeomorph
  cases' squareMap_homotopic_boundaryWords r hr (f.comp e.symm.toContinuousMap) with W hW
  refine ⟨W, ?_⟩
  have H := hW.comp (ContinuousMap.Homotopic.refl e.toContinuousMap)
  aesop
