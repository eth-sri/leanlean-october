module

public import RequestProject.FiniteCycleWordComparison
public import RequestProject.OrderRoseRealizationHomeomorph
public import RequestProject.PresPosetAlpha

@[expose] public section

/-! The literal four-edge rose word and its actual continuous reading.
The positive generator is the specified once-around interval loop.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb RelativeAttachment ContinuousEdgeWords ClassicalGraphModel

variable {A : Type}

def roseGeneratorPath (a : A) : Path (orderRoseBase A) (orderRoseBase A) :=
  roseFourCycle.mappedLoop (roseCopy a) (roseCopy a).monotone

theorem roseGeneratorPath_apply (a : A) (t : I) :
    roseGeneratorPath a t = roseCopyRealization a (orderRoseTraversal t) :=
  roseFourCycle.mappedLoop_apply (roseCopy a) (roseCopy a).monotone t

theorem roseGeneratorPath_homotopic_word (a : A) :
    (roseGeneratorPath a).Homotopic (affineOrderWordPath (roseGeneratorWord a) (roseGeneratorWord_valid a)) := by
  let g  :=
    ![ordPos (Rose.base_le_edg a false), ordNeg (Rose.mid_le_edg a false),
      ordPos (Rose.mid_le_edg a true), ordNeg (Rose.base_le_edg a true)]
  have hs : ∀ i, roseCopy a (roseFourCycle.vertex i) =
      germSrc (orderCx (Rose A)).src (orderCx (Rose A)).tgt (g i) := by
    intro i
    fin_cases i <;> rfl
  have ht : ∀ i : Fin 3, germTgt (orderCx (Rose A)).src (orderCx (Rose A)).tgt (g i.castSucc) =
      roseCopy a (roseFourCycle.vertex i.succ) := by
    intro i
    fin_cases i <;> rfl
  have H := roseFourCycle.mappedLoop_homotopic_word (roseCopy a) (roseCopy a).monotone g hs ht rfl
  tauto

/-- Right-associated traversal of a finite signed word in based loops. -/
def readLoopWord {X E : Type*} [TopologicalSpace X] {a : X} (p : E → Path a a) :
    List (E × Bool) → Path a a
  | [] => Path.refl a
  | (e, b) :: l => (if b then p e else (p e).symm).trans (readLoopWord p l)

theorem readLoopWord_map {X Y E F : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {a : X} {b : Y} (f : X → Y) (g : E → F) (p : E → Path a a) (q : F → Path b b)
    (hbase : f a = b) (h : ∀ e t, f (p e t) = q (g e) t)
    (l : List (E × Bool)) (t : I) :
    f (readLoopWord p l t) = readLoopWord q (l.map fun e => (g e.1, e.2)) t := by
  induction l generalizing t with
  | nil => exact hbase
  | cons e l ih =>
      obtain ⟨e, s⟩ := e
      simp only [List.map_cons, readLoopWord, Path.trans_apply]
      split_ifs <;> cases s <;> simp [h, ih, Path.symm_apply]

abbrev orderRoseRead : List (A × Bool) → Path (orderRoseBase A) (orderRoseBase A) :=
  readLoopWord roseGeneratorPath

theorem roseLetterWord_homotopic_read (p : A × Bool) :
    (affineOrderWordPath (roseLetterWord p) (roseLetterWord_valid p)).Homotopic
      (if p.2 then roseGeneratorPath p.1 else (roseGeneratorPath p.1).symm) := by
  rcases p with ⟨a, b⟩
  cases b
  · exact (realize_revPath (K := orderCx (Rose A)) (orderNerveRealizationVertex (P := Rose A))
      (fun e => orderNerveAffineEdgePath (P := Rose A) e.property) (roseGeneratorWord a)
      (roseGeneratorWord_valid a)).symm.trans (roseGeneratorPath_homotopic_word a).symm.symm₂
  · exact (roseGeneratorPath_homotopic_word a).symm

theorem roseWord_homotopic_read (l : List (A × Bool)) :
    (affineOrderWordPath (roseWord l) (roseWord_valid l)).Homotopic (orderRoseRead l) := by
  induction l with
  | nil => aesop
  | cons p l ih =>
    exact (realize_append (orderCx (Rose A)).src (orderCx (Rose A)).tgt
      (orderNerveRealizationVertex (P := Rose A))
      (fun e => orderNerveAffineEdgePath (P := Rose A) e.property)
      (roseLetterWord p) (roseWord l) (roseLetterWord_valid p) (roseWord_valid l)).symm.trans
      ((roseLetterWord_homotopic_read p).hcomp ih)

abbrev classicalRoseRead : List (A × Bool) → Path (roseVertex A) (roseVertex A) :=
  readLoopWord (fun a : A => graphEdgePath (roseAttaching A) a)

theorem orderRoseRead_classical (l : List (A × Bool)) (t : I) :
    orderRoseRealizationHomeomorph A (orderRoseRead l t) = classicalRoseRead l t := by
  simpa using readLoopWord_map (orderRoseRealizationHomeomorph A) id roseGeneratorPath
    (fun a : A => (graphEdgePath (roseAttaching A) a : Path (roseVertex A) (roseVertex A)))
    (orderRoseRealizationHomeomorph_base A)
    (fun a t => (congrArg (orderRoseRealizationHomeomorph A) (roseGeneratorPath_apply a t)).trans
      (orderRoseRealizationHomeomorph_interval a t)) l t

theorem classicalRoseRead_eq_realize (l : List (A × Bool))
    (hl : IsPath (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A)) l PUnit.unit PUnit.unit) :
    classicalRoseRead l = realize (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A))
      (old (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ)))
      (graphEdgePath (roseAttaching A)) l hl := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a, b⟩
    cases b <;> simp only [readLoopWord, Bool.false_eq_true, ↓reduceIte,
      realize, germPath, Path.cast_rfl_rfl]
    all_goals tauto

end FiniteChains.PresModel
