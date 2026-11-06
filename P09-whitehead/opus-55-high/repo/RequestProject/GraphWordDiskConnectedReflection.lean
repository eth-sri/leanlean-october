import RequestProject.ClassicalGraphBoundaryWords
import RequestProject.ComponentComplex
import Mathlib.Topology.Connected.TotallyDisconnected
import RequestProject.Tac


/-! Attaching word disks cannot connect distinct graph components.
Thus connectedness of an actual word-disk model supplies connectedness
of its labelled combinatorial graph. No finiteness is required. Unverified. -/

noncomputable section
bwd

namespace FiniteChains.ClassicalGraphModel
open RelativeAttachment
open scoped Classical unitInterval Topology
variable {V J M : Type} [TopologicalSpace V] [DiscreteTopology V]
  (r : BoundaryFamily J (Fin 1 → ℝ) → V)

def graphComponentSetoid : Setoid V where
  r := Comb.Reach (graphCx r)
  iseqv := {
    refl := Comb.reach_self (graphCx r)
    symm := by
      rintro a b ⟨l, hl⟩
      exact ⟨Comb.revPath l, Comb.isPath_revPath hl⟩
    trans := by
      rintro a b c ⟨l, hl⟩ ⟨m, hm⟩
      exact ⟨l ++ m, hl.append hm⟩ }

abbrev GraphComponents := Quotient (graphComponentSetoid r)
local instance : TopologicalSpace (GraphComponents r) := ⊥
local instance : DiscreteTopology (GraphComponents r) := ⟨rfl⟩

def graphComponentMap : C(DiskAttachment r, GraphComponents r) :=
  desc r (boundaryFamilyInclusion J _)
    ⟨Quotient.mk _, continuous_of_discreteTopology⟩
    ⟨fun d => Quotient.mk _ (graphSrc r d.1),
      continuous_sigma (fun j =>
        (continuous_const : Continuous (fun _ : ClosedUnitBall (Fin 1 → ℝ) =>
          Quotient.mk _ (graphSrc r j))))⟩
    (fun a => by
      cases' a with j a
      rcases graphBoundary_cases a with rfl | rfl
      · rfl
      · apply Eq.symm
        exact Quotient.sound (show Comb.Reach (graphCx r) (graphSrc r j) (graphTgt r j)
          from ⟨[(j, true)], rfl, rfl⟩))

theorem graphComponentMap_path
    (p : Path (old r (boundaryFamilyInclusion J _) x)
      (old r (boundaryFamilyInclusion J _) y)) t :
    graphComponentMap r (p t) = Quotient.mk (graphComponentSetoid r) x := by
  have h := TotallyDisconnectedSpace.eq_of_continuous
    _ ((graphComponentMap r).continuous.comp p.continuous) t 0
  aesop

theorem graphComponentMap_boundaryWord (W : BoundaryWords r)
    a :
    graphComponentMap r (W.boundaryMap a) =
      Quotient.mk (graphComponentSetoid r) (W.vertex (squareSideMap (0, false) 0)) := by
  have hedge (s : SquareSide) :
      Quotient.mk _ (W.vertex (squareSideMap s 0)) =
        Quotient.mk (graphComponentSetoid r) (W.vertex (squareSideMap s 1)) := Quotient.sound ⟨W.word s, W.isPath s⟩
  have hcorner (s : SquareSide) :
      Quotient.mk _ (W.vertex (squareSideMap s 0)) =
        Quotient.mk (graphComponentSetoid r) (W.vertex (squareSideMap (0, false) 0)) := by
    cases' s with i b
    fin_cases i <;> cases b
    · rfl
    · have h₁ : squareSideMap (0, true) 0 = squareSideMap (1, false) 1 := by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      have h₀ : squareSideMap (1, false) 0 = squareSideMap (0, false) 0 := by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      grind
    · have h₀ : squareSideMap (1, false) 0 = squareSideMap (0, false) 0 := by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      simp_all
    · have h₀ : squareSideMap (1, true) 0 = squareSideMap (0, false) 1 := by
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      simp_all
  obtain ⟨⟨s, t⟩, hs⟩ := squareSideQuotient_surjective _
  change squareSideMap s t = unitBoundarySquareHomeomorph a at hs
  change graphComponentMap r (W.squareMap (unitBoundarySquareHomeomorph a)) = _
  rw [← hs, W.squareMap_side, graphComponentMap_path]
  exact hcorner s

variable (W : M → BoundaryWords r)

def boundaryWordsAttaching : C(BoundaryFamily M (Fin 2 → ℝ), DiskAttachment r) :=
  ⟨fun a => (W a.1).boundaryMap a.2, continuous_sigma (fun m => (W m).boundaryMap.continuous)⟩

def wordDiskComponentMap : C(DiskAttachment (boundaryWordsAttaching r W), GraphComponents r) :=
  desc _ _
    _
    ⟨fun d => Quotient.mk _ ((W d.1).vertex (squareSideMap (0, false) 0)),
      continuous_sigma (fun j =>
        (continuous_const : Continuous (fun _ : ClosedUnitBall (Fin 2 → ℝ) =>
          Quotient.mk _ ((W j).vertex (squareSideMap (0, false) 0)))))⟩
    (graphComponentMap_boundaryWord r _ ·.2)

theorem graphCx_isConnected_of_wordDisks
    [PreconnectedSpace (DiskAttachment (boundaryWordsAttaching r W))] :
    Comb.IsConnected (graphCx r) := by
  intro a b
  apply Quotient.exact (s := graphComponentSetoid r)
  exact TotallyDisconnectedSpace.eq_of_continuous _
    (wordDiskComponentMap r W).continuous
    (old _ _ (old r _ a)) (old _ _ (old r _ b))

omit [DiscreteTopology V] in
theorem graph_vertices_nonempty_of_wordDisks
    [Nonempty (DiskAttachment (boundaryWordsAttaching r W))] : Nonempty V := by
  cases' (inferInstance : Nonempty (DiskAttachment (boundaryWordsAttaching r W))) with x
  obtain ⟨z, rfl⟩ := quotientMap_surjective _
    _ x
  cases z with
  | inr d => exact ⟨(W d.1).vertex (squareSideMap (0, false) 0)⟩
  | inl x =>
    obtain ⟨z, rfl⟩ := quotientMap_surjective r _ x
    cases z with
    | inl v => tauto
    | inr d => exact ⟨graphSrc r d.1⟩
