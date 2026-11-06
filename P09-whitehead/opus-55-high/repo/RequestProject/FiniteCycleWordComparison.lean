import RequestProject.FinitePosetCycleNaturality
import RequestProject.OrderNerveAffinePathWords
import RequestProject.Tac


/-! A monotone image of an explicit cycle reads its ordered edge word by
an actual endpoint-preserving path homotopy. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval Topology
bwd

namespace FiniteChains.Comb.FinitePosetCycle
open RelativeAttachment ContinuousEdgeWords

variable {P Q : Type} [PartialOrder P] [PartialOrder Q] {n : ℕ}
  (C : FinitePosetCycle P n) (f : P → Q) (hf : Monotone f)

def mappedEdge (i : Fin (n + 1)) :=
  orderNerveComparablePath ((C.consecutive i).imp (hf ·) (hf ·))

def mappedLastEdge := orderNerveComparablePath (C.closing.imp (hf ·) (hf ·))

def mappedLoop :=
  (arcConcat n (fun i => orderNerveRealizationVertex (f (C.vertex i)))
    (C.mappedEdge f hf)).trans (C.mappedLastEdge f hf)

theorem mappedLoop_apply t :
    C.mappedLoop f hf t = orderNerveRealizationMap f hf (C.traversal t) := by
  have hp := arcConcat_natural _ n
    (orderNerveRealizationVertex ∘ C.vertex)
    (fun i => orderNerveRealizationVertex (f (C.vertex i))) C.edge (C.mappedEdge f hf)
    (fun i s => orderNerveComparablePath_natural f hf
      _ _ s)
  simp [mappedLoop, traversal, Path.trans_apply]
  split_ifs
  · exact (hp _).symm
  · exact (orderNerveComparablePath_natural f hf C.closing
      _ _).symm

variable (g : Fin (n + 2) → (orderCx Q).E × Bool)
  (hs : ∀ i, f (C.vertex i) = gSrcX (orderCx Q) (g i))
  (ht : ∀ i : Fin (n + 1), gTgtX (orderCx Q) (g i.castSucc) =
    f (C.vertex i.succ))
  (hclose : gTgtX (orderCx Q) (g (Fin.last (n + 1))) = f (C.vertex 0))

def mappedWordValid : IsPathX (orderCx Q) (List.ofFn g)
    (f (C.vertex 0)) (f (C.vertex 0)) := by
  rw [List.ofFn_succ', List.concat_eq_append]
  exact (isPath_ofFn _ _ _ (f ∘ C.vertex) _
    (hs ·.castSucc) ht).append ⟨hs _, hclose⟩

theorem mappedLoop_homotopic_word :
    (C.mappedLoop f hf).Homotopic
      (affineOrderWordPath (List.ofFn g) (C.mappedWordValid f g hs ht hclose)) := by
  have hp := (arcConcat_homotopic_concat n
      (fun i => orderNerveRealizationVertex (f (C.vertex i))) (C.mappedEdge f hf)).trans
    (concat_homotopic_realize_ofFn _ _
      _ _
      _ (f ∘ C.vertex) _ (hs ·.castSucc) ht
      _ (fun i => comparablePath_homotopic_single
        _ _ (hs i.castSucc) (ht i)))
  have hl := comparablePath_homotopic_single
    (C.closing.imp (hf ·) (hf ·)) _
    (hs _) hclose
  have H := (hp.hcomp hl).trans
    (realize_append _ _ _
      _
      _ [g (Fin.last _)]
      _ _)
  have he : List.ofFn (g ·.castSucc) ++ [g (Fin.last _)] =
      List.ofFn g := by simpa [List.concat_eq_append] using (List.ofFn_succ' g).symm
  aesop
