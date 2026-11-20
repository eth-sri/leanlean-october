module

public import RequestProject.RelatorCircleIndexedWord
public import RequestProject.FiniteCycleWordComparison

@[expose] public section

/-! The explicit once-around circle traversal represents its literal
four-edges-per-letter word as an actual based path homotopy.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb RelativeAttachment ContinuousEdgeWords

variable {A J : Type} (w : J → List (A × Bool)) (j : J) (hn : 0 < (w j).length)

def circleWordVertex (i : Fin (relatorCircleSize w j + 2)) : TCirc w :=
  (relatorCircleEnumeration w j hn i).val

def circleWordGerm (i : Fin (relatorCircleSize w j + 2)) : (orderCx (TCirc w)).E × Bool :=
  circleIndexedGerm w j (Fin.cast (relatorCircleSize_add_two w j hn) i)

theorem circleWordGerm_src (i : Fin (relatorCircleSize w j + 2)) :
    circleWordVertex w j hn i =
      germSrc (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circleWordGerm w j hn i) := by
  rw [circleWordGerm, circleIndexedGerm_src]
  rfl

theorem circleWordGerm_tgt (i : Fin (relatorCircleSize w j + 1)) :
    germTgt (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (circleWordGerm w j hn i.castSucc) = circleWordVertex w j hn i.succ := by
  rw [circleWordGerm, circleIndexedGerm_tgt w j hn]
  exact congrArg Subtype.val (relatorCircleEnumeration_next w j hn i)

theorem circleWordGerm_last_tgt :
    germTgt (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (circleWordGerm w j hn (Fin.last (relatorCircleSize w j + 1))) =
        circleWordVertex w j hn 0 := by
  rw [circleWordGerm, circleIndexedGerm_tgt w j hn]
  exact congrArg Subtype.val (relatorCircleEnumeration_last_next w j hn)

theorem circleWordGerms_eq : List.ofFn (circleWordGerm w j hn) = circLoop w j := by
  rw [List.ofFn_congr (relatorCircleSize_add_two w j hn)]
  have he : (fun i => circleWordGerm w j hn
      (Fin.cast (relatorCircleSize_add_two w j hn).symm i)) = circleIndexedGerm w j := by
    aesop
  rw [he, circleIndexedGerm_ofFn]

def circleFullLoop :
    Path (orderNerveRealizationVertex (circleWordVertex w j hn 0))
      (orderNerveRealizationVertex (circleWordVertex w j hn 0)) :=
  (relatorCircleCycle w j hn).mappedLoop Subtype.val (Subtype.mono_coe _)

theorem circleTraversal_to_full (t : I) :
    orderNerveRealizationMap (Subtype.val : RelatorCircle w j → TCirc w) (fun _ _ h => h)
      (relatorCircleTraversal w j hn t) = circleFullLoop w j hn t :=
  ((relatorCircleCycle w j hn).mappedLoop_apply Subtype.val (Subtype.mono_coe _) t).symm

def circleWordIndexedValid :
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (List.ofFn (circleWordGerm w j hn)) (circleWordVertex w j hn 0) (circleWordVertex w j hn 0) :=
  (relatorCircleCycle w j hn).mappedWordValid Subtype.val (circleWordGerm w j hn)
    (circleWordGerm_src w j hn) (circleWordGerm_tgt w j hn) (circleWordGerm_last_tgt w j hn)

def circleWordValid : IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
    (circLoop w j) (circleWordVertex w j hn 0) (circleWordVertex w j hn 0) := by
  rw [← circleWordGerms_eq w j hn]
  exact circleWordIndexedValid w j hn

theorem circleFullLoop_homotopic_word :
    (circleFullLoop w j hn).Homotopic
      (affineOrderWordPath (circLoop w j) (circleWordValid w j hn)) := by
  have h := (relatorCircleCycle w j hn).mappedLoop_homotopic_word Subtype.val (Subtype.mono_coe _)
    (circleWordGerm w j hn) (circleWordGerm_src w j hn) (circleWordGerm_tgt w j hn)
    (circleWordGerm_last_tgt w j hn)
  simp only [circleWordGerms_eq] at h
  exact h

end FiniteChains.PresModel
