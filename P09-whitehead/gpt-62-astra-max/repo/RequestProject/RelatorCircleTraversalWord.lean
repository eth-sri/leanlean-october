module

public import RequestProject.RelatorCircleIndexedWord
public import RequestProject.OrderNerveAffinePathWords
public import RequestProject.FinitePosetCycleNaturality

@[expose] public section

/-! The explicit once-around circle traversal represents its literal
four-edges-per-letter word as an actual based path homotopy.
Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology

namespace FiniteChains.PresModel
open Comb RelativeAttachment ContinuousEdgeWords

variable {A J : Type} (w : J → List (A × Bool)) (j : J) (hn : 0 < (w j).length)

variable (i : Fin (relatorCircleSize w j + 2))

def circleWordVertex :=
  (relatorCircleEnumeration w j hn i).val

def circleWordGerm :=
  circleIndexedGerm w j (Fin.cast (relatorCircleSize_add_two w j hn) i)

theorem circleWordGerm_src :
    circleWordVertex w j hn i =
      germSrc (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt (circleWordGerm w j hn i) := by
  rw [circleWordGerm, circleIndexedGerm_src]
  rfl

theorem circleWordGerm_tgt (i : Fin _) :
    germTgt (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (circleWordGerm w j hn i.castSucc) = circleWordVertex w j hn i.succ := by
  rw [circleWordGerm, circleIndexedGerm_tgt w j hn]
  solve_by_elim [relatorCircleEnumeration_next]

theorem circleWordGerm_last_tgt :
    germTgt (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (circleWordGerm w j hn (Fin.last (relatorCircleSize w j + 1))) =
        circleWordVertex w j hn 0 := by
  rw [circleWordGerm, circleIndexedGerm_tgt w j hn]
  solve_by_elim [relatorCircleEnumeration_last_next]

theorem circleWordGerms_eq : List.ofFn (circleWordGerm w j hn) = circLoop w j := by
  rw [List.ofFn_congr (relatorCircleSize_add_two w j hn)]
  solve_by_elim [relatorCircleSize_add_two, circleIndexedGerm_ofFn]

def circleWordEdge (i : Fin _) :
    Path (orderNerveRealizationVertex (circleWordVertex w j hn i.castSucc))
      (orderNerveRealizationVertex (circleWordVertex w j hn i.succ)) :=
  orderNerveComparablePath ((relatorCircleCycle w j hn).consecutive i)

def circleWordLastEdge :
    Path (orderNerveRealizationVertex
      (circleWordVertex w j hn (Fin.last (relatorCircleSize w j + 1))))
        (orderNerveRealizationVertex (circleWordVertex w j hn 0)) :=
  orderNerveComparablePath (relatorCircleCycle w j hn).closing

def circleFullLoop :
    Path (orderNerveRealizationVertex (circleWordVertex w j hn 0))
      (orderNerveRealizationVertex (circleWordVertex w j hn 0)) :=
  (arcConcat _
    (orderNerveRealizationVertex ∘ circleWordVertex w j hn) (circleWordEdge w j hn)).trans
      (circleWordLastEdge w j hn)

theorem circleTraversal_to_full (t : I) :
    orderNerveRealizationMap Subtype.val (fun _ _ h => h)
      (relatorCircleTraversal w j hn t) = circleFullLoop w j hn t := by
  have he (i : Fin _) (s : I) :=
    orderNerveComparablePath_natural Subtype.val (fun _ _ h => h)
      ((relatorCircleCycle w j hn).consecutive i)
      ((relatorCircleCycle w j hn).consecutive i) s
  have hp := arcConcat_natural
    _
    _
    (orderNerveRealizationVertex ∘ (relatorCircleCycle w j hn).vertex)
    (orderNerveRealizationVertex ∘ circleWordVertex w j hn)
    _ _ he
  change orderNerveRealizationMap Subtype.val _
    (((relatorCircleCycle w j hn).prefix.trans _) t) = _
  simp only [circleFullLoop, Path.trans_apply]
  split_ifs
  · exact hp _
  · apply orderNerveComparablePath_natural

def circleWordIndexedValid :
    IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (List.ofFn (circleWordGerm w j hn)) (circleWordVertex w j hn 0) (circleWordVertex w j hn 0) := by
  rw [List.ofFn_succ', List.concat_eq_append]
  exact (isPath_ofFn _ _ _ _
    _
    (fun i => circleWordGerm_src w j hn i.castSucc) (circleWordGerm_tgt w j hn)).append
    ⟨circleWordGerm_src w j hn _, circleWordGerm_last_tgt w j hn⟩

def circleWordValid : IsPath (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
    (circLoop w j) (circleWordVertex w j hn 0) (circleWordVertex w j hn 0) := by
  rw [← circleWordGerms_eq w j hn]
  apply circleWordIndexedValid

theorem circleFullLoop_homotopic_word :
    (circleFullLoop w j hn).Homotopic
      (affineOrderWordPath (circLoop w j) (circleWordValid w j hn)) := by
  have hp := (arcConcat_homotopic_concat _
      (orderNerveRealizationVertex ∘ circleWordVertex w j hn) _).trans
    (concat_homotopic_realize_ofFn (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (orderNerveRealizationVertex (P := TCirc w))
      (fun e => orderNerveAffineEdgePath (P := TCirc w) e.property)
      (relatorCircleSize w j + 1) (circleWordVertex w j hn)
      (fun i => circleWordGerm w j hn i.castSucc)
      (fun i => circleWordGerm_src w j hn i.castSucc) (circleWordGerm_tgt w j hn)
      (circleWordEdge w j hn) (fun i => comparablePath_homotopic_single (P := TCirc w)
        ((relatorCircleCycle w j hn).consecutive i) _
        (circleWordGerm_src w j hn i.castSucc) (circleWordGerm_tgt w j hn i)))
  have hl := comparablePath_homotopic_single (P := TCirc w) (relatorCircleCycle w j hn).closing
    _
    (circleWordGerm_src w j hn _) (circleWordGerm_last_tgt w j hn)
  have H := (hp.hcomp hl).trans
    (realize_append (orderCx (TCirc w)).src (orderCx (TCirc w)).tgt
      (orderNerveRealizationVertex (P := TCirc w))
      (fun e => orderNerveAffineEdgePath (P := TCirc w) e.property)
      (List.ofFn (fun i : Fin (relatorCircleSize w j + 1) => circleWordGerm w j hn i.castSucc))
      [circleWordGerm w j hn (Fin.last (relatorCircleSize w j + 1))]
      (isPath_ofFn _ _ (relatorCircleSize w j + 1) (circleWordVertex w j hn)
        (fun i => circleWordGerm w j hn i.castSucc)
        (fun i => circleWordGerm_src w j hn i.castSucc) (circleWordGerm_tgt w j hn))
      ⟨circleWordGerm_src w j hn _, circleWordGerm_last_tgt w j hn⟩)
  have hw : List.ofFn (fun i => circleWordGerm w j hn i.castSucc) ++
      [circleWordGerm w j hn (Fin.last (relatorCircleSize w j + 1))] = circLoop w j := by
    rw [← List.concat_eq_append, ← List.ofFn_succ', circleWordGerms_eq]
  aesop

end FiniteChains.PresModel
