import RequestProject.FiniteCycleWordComparison
import RequestProject.OrderRoseRealizationHomeomorph
import RequestProject.PresPosetAlpha
import RequestProject.Tac


/-! The literal four-edge rose word and its actual continuous reading.
The positive generator is the specified once-around interval loop.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
bwd

namespace FiniteChains.PresModel
open Comb RelativeAttachment ContinuousEdgeWords ClassicalGraphModel

variable {A J : Type}

def roseGeneratorWord (a : A) :=
  [ordPos (Rose.base_le_edg a false), ordNeg (Rose.mid_le_edg a false),
    ordPos (Rose.mid_le_edg a true), ordNeg (Rose.base_le_edg a true)]

theorem roseGeneratorWord_valid a :
    IsPathX (orderCx (Rose A)) (roseGeneratorWord a) .base .base :=
  by trivial

def roseLetterWord (p : A × Bool) :=
  if p.2 then roseGeneratorWord p.1 else revPath (X := orderCx (Rose A)) (roseGeneratorWord p.1)

def roseWord (l : List (A × Bool)) := l.flatMap roseLetterWord

theorem roseLetterWord_valid p :
    IsPathX (orderCx (Rose A)) (roseLetterWord p) .base .base := by
  cases' p with a b
  cases b
  · trivial
  trivial

theorem roseWord_valid l :
    IsPathX (orderCx (Rose A)) (roseWord l) .base .base := by
  induction l with
  | nil => rfl
  | cons p l ih => exact (roseLetterWord_valid p).append ih

def roseGeneratorPath (a : A) : Path (orderRoseBase A) (orderRoseBase A) :=
  roseFourCycle.mappedLoop _ (roseCopy a).monotone

theorem roseGeneratorPath_apply (a : A) t :
    roseGeneratorPath a t = roseCopyRealization a (orderRoseTraversal t) :=
  roseFourCycle.mappedLoop_apply _ _ t

theorem roseGeneratorPath_homotopic_word (a : A) :
    (roseGeneratorPath a).Homotopic (affineOrderWordPath (roseGeneratorWord a) (roseGeneratorWord_valid a)) := by
  let g :=
    ![ordPos (Rose.base_le_edg a false), ordNeg (Rose.mid_le_edg a false),
      ordPos (Rose.mid_le_edg a true), ordNeg (Rose.base_le_edg a true)]
  have hs : ∀ i, roseCopy a (roseFourCycle.vertex i) =
      gSrcX (orderCx (Rose A)) (g i) := by
    intro i
    fin_cases i <;> rfl
  have ht : ∀ i : Fin 3, gTgtX (orderCx (Rose A)) (g i.castSucc) =
      roseCopy a (roseFourCycle.vertex i.succ) := by
    intro i
    fin_cases i <;> rfl
  have H := roseFourCycle.mappedLoop_homotopic_word _ (roseCopy a).monotone g hs ht rfl
  tauto

def orderRoseRead : List (A × Bool) → Path (orderRoseBase A) (orderRoseBase A)
  | [] => Path.refl _
  | (a, b) :: l => (if b then roseGeneratorPath a else (roseGeneratorPath a).symm).trans (orderRoseRead l)

theorem roseLetterWord_homotopic_read (p : A × Bool) :
    (affineOrderWordPath (roseLetterWord p) (roseLetterWord_valid p)).Homotopic
      (if p.2 then roseGeneratorPath p.1 else (roseGeneratorPath p.1).symm) := by
  cases' p with a b
  cases b
  · exact (realize_revPath (K := orderCx (Rose A)) _
      _ _
      _).symm.trans (roseGeneratorPath_homotopic_word a).symm.symm₂
  · exact (roseGeneratorPath_homotopic_word a).symm

theorem roseWord_homotopic_read (l : List (A × Bool)) :
    (affineOrderWordPath (roseWord l) (roseWord_valid l)).Homotopic (orderRoseRead l) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    exact (realize_append _ _
      _
      _
      _ _ _ _).symm.trans
      ((roseLetterWord_homotopic_read p).hcomp ih)

def classicalRoseRead : List (A × Bool) → Path (roseVertex A) (roseVertex A)
  | [] => Path.refl _
  | (a, b) :: l =>
      (if b then graphEdgePath (roseAttaching A) a else (graphEdgePath (roseAttaching A) a).symm).trans
        (classicalRoseRead l)

theorem orderRoseRead_classical l t :
    orderRoseRealizationHomeomorph A (orderRoseRead l t) = classicalRoseRead l t := by
  induction l generalizing t with
  | nil => exact orderRoseRealizationHomeomorph_base A
  | cons p l ih =>
    cases' p with a b
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [orderRoseRead, classicalRoseRead, Path.trans_apply, dif_pos ht]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Path.symm_apply,
        Function.comp_apply, roseGeneratorPath_apply, orderRoseRealizationHomeomorph_interval]
      all_goals rfl
    · simp only [orderRoseRead, classicalRoseRead, Path.trans_apply, dif_neg ht]
      exact ih _

theorem classicalRoseRead_eq_realize l
    hl :
    classicalRoseRead l = realize (graphSrc (roseAttaching A)) (graphTgt (roseAttaching A))
      (old (roseAttaching A) (boundaryFamilyInclusion A (Fin 1 → ℝ)))
      (graphEdgePath (roseAttaching A)) l hl := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    cases' p with a b
    cases b <;> simp only [classicalRoseRead, Bool.false_eq_true, ↓reduceIte,
      realize, germPath, Path.cast_rfl_rfl]
    all_goals tauto

variable (w : J → List (A × Bool))

theorem mapPath_aFun_segAt j {k} hk :
    mapPath (orderCxMap (aFun w) (aFun_monotone w)) (segAt w j k) = roseLetterWord (w j)[k] := by
  have hp := List.getElem?_eq_getElem hk
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
  cases' he : (w j)[k] with a b
  cases b
  · aesop
  aesop

theorem mapPath_aFun_circPath j : ∀ {m}, m ≤ (w j).length →
    mapPath (orderCxMap (aFun w) (aFun_monotone w)) (circPath w j m) = roseWord ((w j).take m) := by
  intro m
  induction m with
  | zero => tauto
  | succ m ih =>
    intro hm
    have hlt : m < (w j).length := by omega
    have hsplit : (w j).take (m + 1) = (w j).take m ++ [(w j)[m]] := by
      simp
    change mapPath _ (circPath w j m ++ segAt w j m) = _
    rw [mapPath_append, ih (Nat.le_of_lt hlt), mapPath_aFun_segAt w j hlt, hsplit]
    simp only [roseWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem mapPath_aFun_circLoop j :
    mapPath (orderCxMap (aFun w) (aFun_monotone w)) (circLoop w j) = roseWord (w j) := by
  simpa [List.take_length, circLoop] using mapPath_aFun_circPath w j (le_refl (w j).length)
