import Mathlib.Tactic

import RequestProject.FiniteCycleWordComparison
import RequestProject.OrderRoseRealizationHomeomorph
import RequestProject.PresPosetAlpha

/-! The literal four-edge rose word and its actual continuous reading.
The positive generator is the specified once-around interval loop.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb RelativeAttachment ContinuousEdgeWords ClassicalGraphModel

variable {A J : Type}

  (a : A)
def roseGeneratorWord   :=
  [ordPos (Rose.base_le_edg a false), ordNeg (Rose.mid_le_edg a false),
    ordPos (Rose.mid_le_edg a true), ordNeg (Rose.base_le_edg a true)]

theorem roseGeneratorWord_valid  :
    IsPath (orderCx (Rose A)).src (orderCx (Rose A)).tgt (roseGeneratorWord a) .base .base :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

variable (p : A × Bool)
def roseLetterWord   :=
  if p.2 then roseGeneratorWord p.1 else revPath (X := orderCx (Rose A)) (roseGeneratorWord p.1)

variable (l : List (A × Bool))
def roseWord   := l.flatMap roseLetterWord

theorem roseLetterWord_valid  :
    IsPath (orderCx (Rose A)).src (orderCx (Rose A)).tgt (roseLetterWord p) .base .base := by
  rcases p with ⟨a, b⟩
  cases b
  · exact isPath_revPath (roseGeneratorWord_valid a)
  · exact roseGeneratorWord_valid a

theorem roseWord_valid  :
    IsPath (orderCx (Rose A)).src (orderCx (Rose A)).tgt (roseWord l) .base .base := by
  induction l with
  | nil => rfl
  | cons p l ih => exact (roseLetterWord_valid p).append ih

def roseGeneratorPath  : Path (orderRoseBase A) (orderRoseBase A) :=
  roseFourCycle.mappedLoop (roseCopy a) (roseCopy a).monotone

theorem roseGeneratorPath_apply  (t : I) :
    roseGeneratorPath a t = roseCopyRealization a (orderRoseTraversal t) :=
  roseFourCycle.mappedLoop_apply (roseCopy a) (roseCopy a).monotone t

theorem roseGeneratorPath_homotopic_word  :
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
  assumption

def orderRoseRead : List (A × Bool) → Path (orderRoseBase A) (orderRoseBase A)
  | [] => Path.refl _
  | (a, b) :: l => (if b then roseGeneratorPath a else (roseGeneratorPath a).symm).trans (orderRoseRead l)

theorem roseLetterWord_homotopic_read  :
    (affineOrderWordPath (roseLetterWord p) (roseLetterWord_valid p)).Homotopic
      (if p.2 then roseGeneratorPath p.1 else (roseGeneratorPath p.1).symm) := by
  rcases p with ⟨a, b⟩
  cases b
  · exact (realize_revPath (K := orderCx (Rose A)) (orderNerveRealizationVertex (P := Rose A))
      (fun e => orderNerveAffineEdgePath (P := Rose A) e.property) (roseGeneratorWord a)
      (roseGeneratorWord_valid a)).symm.trans (roseGeneratorPath_homotopic_word a).symm.symm₂
  · exact (roseGeneratorPath_homotopic_word a).symm

theorem roseWord_homotopic_read  :
    (affineOrderWordPath (roseWord l) (roseWord_valid l)).Homotopic (orderRoseRead l) := by
  induction l with
  | nil => exact Path.Homotopic.refl _
  | cons p l ih =>
    exact (realize_append (orderCx (Rose A)).src (orderCx (Rose A)).tgt
      (orderNerveRealizationVertex (P := Rose A))
      (fun e => orderNerveAffineEdgePath (P := Rose A) e.property)
      (roseLetterWord p) (roseWord l) (roseLetterWord_valid p) (roseWord_valid l)).symm.trans
      ((roseLetterWord_homotopic_read p).hcomp ih)

def classicalRoseRead : List (A × Bool) → Path (roseVertex A) (roseVertex A)
  | [] => Path.refl _
  | (a, b) :: l =>
      (if b then graphEdgePath (roseAttaching A) a else (graphEdgePath (roseAttaching A) a).symm).trans
        (classicalRoseRead l)

theorem orderRoseRead_classical  (t : I) :
    orderRoseRealizationHomeomorph A (orderRoseRead l t) = classicalRoseRead l t := by
  induction l generalizing t with
  | nil => exact orderRoseRealizationHomeomorph_base A
  | cons p l ih =>
    rcases p with ⟨a, b⟩
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [orderRoseRead, classicalRoseRead, Path.trans_apply, dif_pos ht]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Path.symm_apply, Function.comp_apply, roseGeneratorPath_apply, orderRoseRealizationHomeomorph_interval]
      all_goals rfl
    · simp only [orderRoseRead, classicalRoseRead, Path.trans_apply, dif_neg ht]
      exact ih _

theorem classicalRoseRead_eq_realize 
    (hl : IsPath (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A)) l PUnit.unit PUnit.unit) :
    classicalRoseRead l = realize (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A))
      (old (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ)))
      (graphEdgePath (roseAttaching A)) l hl := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨a, b⟩
    cases b <;> simp [classicalRoseRead]
    all_goals congr 1; exact ih _

variable (w : J → List (A × Bool))

  (j : J)
theorem mapPath_aFun_segAt  {k : ℕ} (hk : k < (w j).length) :
    mapPath (orderCxMap (aFun w) (aFun_monotone w)) (segAt w j k) = roseLetterWord (w j)[k] := by
  have hp  := List.getElem?_eq_getElem hk
  have hmid : aFun w (TCirc.pt w j k CPos.cmid) = Rose.mid (w j)[k].1 := by
    rw [aFun_pt_cmid_of_get w hp]
  have hL : aFun w (TCirc.pt w j k CPos.cedgL) = Rose.edg (w j)[k].1 (!(w j)[k].2) := by
    rw [aFun_pt_cedgL_of_get w hp]
  have hR : aFun w (TCirc.pt w j k CPos.cedgR) = Rose.edg (w j)[k].1 (w j)[k].2 := by
    rw [aFun_pt_cedgR_of_get w hp]
  rw [segAt, dif_pos hk]
  change [ordPos ((aFun_monotone w) (TCirc.cor_le_cedgL w hk)),
    ordNeg ((aFun_monotone w) (TCirc.cmid_le_cedgL w hk)),
    ordPos ((aFun_monotone w) (TCirc.cmid_le_cedgR w hk)),
    ordNeg ((aFun_monotone w) (TCirc.cor_csucc_le_cedgR w hk))] = _
  rcases he : (w j)[k] with ⟨a, b⟩
  rw [he] at hmid hL hR
  cases b
  · aesop
  · aesop

theorem mapPath_aFun_circPath  : ∀ {m : ℕ}, m ≤ (w j).length →
    mapPath (orderCxMap (aFun w) (aFun_monotone w)) (circPath w j m) = roseWord ((w j).take m) := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have hlt : m < (w j).length := by omega
    have hsplit : (w j).take (m + 1) = (w j).take m ++ [(w j)[m]] := by
      simp_all
    grind [mapPath, circPath, mapPath_aFun_segAt, roseWord]

theorem mapPath_aFun_circLoop  :
    mapPath (orderCxMap (aFun w) (aFun_monotone w)) (circLoop w j) = roseWord (w j) := by
  simp_all [circLoop, mapPath_aFun_circPath]

end FiniteChains.PresModel
