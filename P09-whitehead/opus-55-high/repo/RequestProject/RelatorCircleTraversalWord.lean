import RequestProject.RelatorCircleIndexedWord
import RequestProject.OrderNerveAffinePathWords
import RequestProject.FinitePosetCycleNaturality
import RequestProject.Tac


/-! The explicit once-around circle traversal represents its literal
four-edges-per-letter word as an actual based path homotopy.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
bwd

namespace FiniteChains.PresModel
open Comb RelativeAttachment ContinuousEdgeWords

variable {A J : Type} (w : J → List (A × Bool)) (j : J) (hn : 0 < (w j).length)

def circleWordVertex (i : Fin (relatorCircleSize w j + 2)) :=
  (relatorCircleEnumeration w j hn i).val

def circleWordGerm (i : Fin (relatorCircleSize w j + 2)) :=
  circleIndexedGerm w j (Fin.cast (relatorCircleSize_add_two w j hn) i)

theorem circleWordGerm_src i :
    circleWordVertex w j hn i =
      gSrcX (orderCx (TCirc w)) (circleWordGerm w j hn i) := by
  rw [circleWordGerm, circleIndexedGerm_src]
  rfl

theorem circleWordGerm_tgt (i : Fin (relatorCircleSize w j + 1)) :
    gTgtX (orderCx (TCirc w))
      (circleWordGerm w j hn i.castSucc) = circleWordVertex w j hn i.succ := by
  rw [circleWordGerm, circleIndexedGerm_tgt w j hn]
  exact congrArg Subtype.val (relatorCircleEnumeration_next w j hn i)

theorem circleWordGerm_last_tgt :
    gTgtX (orderCx (TCirc w))
      (circleWordGerm w j hn (Fin.last (relatorCircleSize w j + 1))) =
        circleWordVertex w j hn 0 := by
  rw [circleWordGerm, circleIndexedGerm_tgt w j hn]
  exact congrArg Subtype.val (relatorCircleEnumeration_last_next w j hn)

theorem circleWordGerms_eq : List.ofFn (circleWordGerm w j hn) = circLoop w j := by
  rw [List.ofFn_congr (relatorCircleSize_add_two w j hn)]
  have he : (fun i => circleWordGerm w j hn
      (Fin.cast (relatorCircleSize_add_two w j hn).symm i)) = circleIndexedGerm w j := by
    rfl
  rw [he, circleIndexedGerm_ofFn]

def circleWordEdge (i : Fin (relatorCircleSize w j + 1)) :
    Path (orderNerveRealizationVertex (circleWordVertex w j hn i.castSucc))
      (orderNerveRealizationVertex (circleWordVertex w j hn i.succ)) :=
  orderNerveComparablePath (P := TCirc w) ((relatorCircleCycle w j hn).consecutive i)

def circleWordLastEdge :
    Path (orderNerveRealizationVertex
      (circleWordVertex w j hn (Fin.last (relatorCircleSize w j + 1))))
        (orderNerveRealizationVertex (circleWordVertex w j hn 0)) :=
  orderNerveComparablePath (P := TCirc w) (relatorCircleCycle w j hn).closing

def circleFullLoop :
    Path (orderNerveRealizationVertex (circleWordVertex w j hn 0))
      (orderNerveRealizationVertex (circleWordVertex w j hn 0)) :=
  (arcConcat _
    (orderNerveRealizationVertex ∘ circleWordVertex w j hn) (circleWordEdge w j hn)).trans
      (circleWordLastEdge w j hn)

theorem circleTraversal_to_full (t : I) :
    orderNerveRealizationMap (Subtype.val : RelatorCircle w j → TCirc w) (fun _ _ h => h)
      (relatorCircleTraversal w j hn t) = circleFullLoop w j hn t := by
  have he (i : Fin (relatorCircleSize w j + 1)) (s : I) :=
    orderNerveComparablePath_natural Subtype.val (fun _ _ h => h)
      ((relatorCircleCycle w j hn).consecutive i)
      ((relatorCircleCycle w j hn).consecutive i) s
  have hp := arcConcat_natural
    _
    _
    (orderNerveRealizationVertex ∘ (relatorCircleCycle w j hn).vertex)
    (orderNerveRealizationVertex ∘ circleWordVertex w j hn)
    _ _ he
  change orderNerveRealizationMap Subtype.val (fun _ _ h => h)
    (((relatorCircleCycle w j hn).prefix.trans (relatorCircleCycle w j hn).lastEdge) t) = _
  simp [circleFullLoop, Path.trans_apply]
  split_ifs
  · exact hp _
  · exact orderNerveComparablePath_natural Subtype.val _
      _ _ _

def circleWordIndexedValid :
    IsPathX (orderCx (TCirc w))
      (List.ofFn (circleWordGerm w j hn)) (circleWordVertex w j hn 0) (circleWordVertex w j hn 0) := by
  rw [List.ofFn_succ', List.concat_eq_append]
  exact (isPath_ofFn _ _ _ _
    _
    (circleWordGerm_src w j hn ·.castSucc) (circleWordGerm_tgt w j hn)).append
    ⟨circleWordGerm_src w j hn _, circleWordGerm_last_tgt w j hn⟩

def circleWordValid : IsPathX (orderCx (TCirc w))
    (circLoop w j) (circleWordVertex w j hn 0) (circleWordVertex w j hn 0) := by
  rw [← circleWordGerms_eq w j hn]
  exact circleWordIndexedValid w j hn

theorem circleFullLoop_homotopic_word :
    (circleFullLoop w j hn).Homotopic
      (affineOrderWordPath (circLoop w j) (circleWordValid w j hn)) := by
  have hp := (arcConcat_homotopic_concat _
      (orderNerveRealizationVertex ∘ circleWordVertex w j hn) (circleWordEdge w j hn)).trans
    (concat_homotopic_realize_ofFn _ (orderCx (TCirc w)).tgt
      _
      _
      _ _
      _
      (circleWordGerm_src w j hn ·.castSucc) (circleWordGerm_tgt w j hn)
      _ (fun i => comparablePath_homotopic_single (P := TCirc w)
        _ _
        (circleWordGerm_src w j hn i.castSucc) (circleWordGerm_tgt w j hn i)))
  have hl := comparablePath_homotopic_single (P := TCirc w) (relatorCircleCycle w j hn).closing
    _
    (circleWordGerm_src w j hn _) (circleWordGerm_last_tgt w j hn)
  have H := (hp.hcomp hl).trans
    (realize_append (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      _
      _
      _
      [circleWordGerm w j hn (Fin.last _)]
      _
      _)
  have hw : List.ofFn (circleWordGerm w j hn ·.castSucc) ++
      [circleWordGerm w j hn (Fin.last _)] = circLoop w j := by
    rw [← List.concat_eq_append, ← List.ofFn_succ', circleWordGerms_eq]
  aesop
