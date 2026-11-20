module

public import NearlyMinimax.HistoryHeapFold


@[expose] public section

/-! Exact raw-state compatibility of actual independent marked canonical
append, derived from the genuine heap-coordinate transport. -/
noncomputable section
open MeasureTheory
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

def historyCanonicalWordMarks {dependent : J → J → Prop}
    {g : DependenceHeap dependent} {E : Type*}
    (marks : Fin (historyShapeLength g) → E) : Fin g.out.length → E :=
  fun i => marks (Fin.cast (historyShapeLength_out g).symm i)

theorem historyMarkedRawState_eq_wordMarkedState (dependent : J → J → Prop)
    {E X : Type*} (update : J → E → X → X) (initial : X)
    (g : DependenceHeap dependent)
    (marks : Fin (historyShapeLength g) → E) :
    historyMarkedRawState update initial ⟨g, marks⟩ =
      historyWordMarkedState update initial (historyCanonicalWordMarks marks) := by
  have hm : (List.ofFn (fun i =>
      (historyShapeCanonicalLabels g i, marks i))) =
      (List.ofFn (fun i => i)).map
        (fun i => (historyShapeCanonicalLabels g i, marks i)) := by
    rw [List.map_ofFn]
    rfl
  have ht : (List.ofFn (fun i =>
      (historyShapeCanonicalLabels g i, marks i))) =
      List.ofFn (fun i => (g.out.get i, historyCanonicalWordMarks marks i)) := by
    apply List.ext_getElem (by simp; exact historyShapeLength_out g)
    intro i hi hi'
    simp only [List.getElem_ofFn, historyShapeCanonicalLabels, historyCanonicalWordMarks]
    congr 1
  have hh := congrArg (fun l =>
    l.foldl (fun state p => update p.1 p.2 state) initial) (hm.symm.trans ht)
  rw [List.foldl_map] at hh
  exact hh

section
variable {dependent : J → J → Prop} (j : J) {g : DependenceHeap dependent} {E : Type*}
    [MeasurableSpace E] (fresh : E) (marks : Fin (historyShapeLength g) → E)

def historyAppendWordMarks : Fin (g.out ++ [j]).length → E :=
  fun i => historyFiniteMarkAppendEquiv (historyShapeLength g) (fresh, marks)
    (Fin.cast (by rw [historyShapeLength_out]; simp) i)

theorem historyCanonicalAppend_word_marks (dependent : J → J → Prop)
    [Std.Symm dependent]
    (j : J) (g : DependenceHeap dependent)
    {E : Type*} [MeasurableSpace E] (fresh : E)
    (marks : Fin (historyShapeLength g) → E) :
    historyCanonicalWordMarks
      (historyCanonicalMarkAppendEquiv j g (fresh, marks)) =
      historyHeapMarkEquiv (historyCanonicalAppendHeapIso j g)
        (historyAppendWordMarks j fresh marks) := by
  let e := historyCanonicalAppendHeapIso j g
  let hlen : historyShapeLength g + 1 = (g.out ++ [j]).length := by
    rw [historyShapeLength_out]; simp
  have hc x :
      historyCanonicalAppendCoordinates j g (Fin.cast hlen.symm x.position) =
      Fin.cast (historyShapeLength_out (historyShapeAppend j g)).symm (e x).position := rfl
  have hm (x : WordHeapPiece (g.out ++ [j]) dependent) :=
    MeasurableEquiv.piCongrLeft_apply_apply
      (historyCanonicalAppendCoordinates j g)
      (β := fun _ => E) (historyFiniteMarkAppendEquiv _ (fresh, marks)) (Fin.cast hlen.symm x.position)
  ext i
  let x  := e.symm ⟨i⟩
  have hx : (e x).position = i := by simp [x, e.apply_symm_apply]
  have hh := hm x
  rw [hc x, hx] at hh
  have ht := historyHeapMarkEquiv_position e (historyAppendWordMarks j fresh marks) x
  rw [hx] at ht
  exact hh.trans ht.symm

@[simp] theorem historyAppendWordMarks_old (x : WordHeapPiece g.out dependent) :
    historyAppendWordMarks j fresh marks
      (historyPrefixHeapEmbedding g.out dependent j x).position =
      historyCanonicalWordMarks marks x.position := by
  unfold historyAppendWordMarks historyCanonicalWordMarks
  have he : Fin.cast (by rw [historyShapeLength_out]; simp)
      (historyPrefixHeapEmbedding g.out dependent j x).position =
      (Fin.cast (historyShapeLength_out g).symm x.position).castSucc := by
    apply Fin.ext
    rfl
  rw [he, historyFiniteMarkAppendEquiv_old]

@[simp] theorem historyAppendWordMarks_fresh :
    historyAppendWordMarks j fresh marks (wordHeapAppendedPiece g.out dependent j).position = fresh := by
  unfold historyAppendWordMarks
  have he : Fin.cast (by rw [historyShapeLength_out]; simp)
      (wordHeapAppendedPiece g.out dependent j).position = Fin.last (historyShapeLength g) := by
    apply Fin.ext
    exact (historyShapeLength_out g).symm
  rw [he, historyFiniteMarkAppendEquiv_last]

end

variable (dependent : J → J → Prop)

theorem historyAppendWordMarkedState
    (j : J) (g : DependenceHeap dependent)
    {E X : Type*} [MeasurableSpace E] (fresh : E)
    (marks : Fin (historyShapeLength g) → E)
    (update : J → E → X → X) (initial : X) :
    historyWordMarkedState update initial
      (historyAppendWordMarks j fresh marks) =
      update j fresh (historyWordMarkedState update initial
        (historyCanonicalWordMarks marks)) := by
  have ht : (List.ofFn (fun i =>
      ((g.out ++ [j]).get i, historyAppendWordMarks j fresh marks i))) =
      (List.ofFn (fun i =>
        (g.out.get i, historyCanonicalWordMarks marks i))) ++ [(j, fresh)] := by
    apply List.ext_getElem (by simpa)
    intro i hi hi'
    by_cases hiold : i < g.out.length
    · rw [List.getElem_append_left (by simpa using hiold)]
      simp only [List.getElem_ofFn]
      have hg : (g.out ++ [j]).get ⟨i, by simpa using hi⟩ = g.out.get ⟨i, hiold⟩ := by
        simp_all
      rw [hg]
      exact congrArg (fun a => (g.out.get ⟨i, hiold⟩, a))
        (historyAppendWordMarks_old j fresh marks (⟨⟨i, hiold⟩⟩))
    · have hieq : i = g.out.length := by
        simp at hi
        omega
      subst i
      rw [List.getElem_append_right (by simpa)]
      simp only [List.length_ofFn, Nat.sub_self, List.getElem_cons_zero, List.getElem_ofFn]
      have hg : (g.out ++ [j]).get ⟨g.out.length, by simpa using hi⟩ = j := by
        simpa
      rw [hg]
      solve_by_elim [historyAppendWordMarks_fresh]
  unfold historyWordMarkedState historyWordState
  rw [ht, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Actual canonical marked append applies exactly the fresh local update
once, even when the canonical representative reorders old occurrences. -/
theorem historyMarkedRawState_append
    [Std.Symm dependent]
    {E X : Type*} [MeasurableSpace E] (update : J → E → X → X)
    (hcomm : ∀ j k, ¬ dependent j k → ∀ e f state,
      update k f (update j e state) = update j e (update k f state))
    (initial : X) (j : J) (h : HistoryMarked dependent E) (fresh : E) :
    historyMarkedRawState update initial
      (historyMarkedAppend j (h, fresh)) =
      update j fresh (historyMarkedRawState update initial h) := by
  obtain ⟨g, marks⟩ := h
  change historyMarkedRawState update initial
      ⟨historyShapeAppend j g, historyCanonicalMarkAppendEquiv j g (fresh, marks)⟩ = _
  rw [historyMarkedRawState_eq_wordMarkedState,
    historyCanonicalAppend_word_marks,
    historyHeapMarkEquiv_state hcomm
      (historyCanonicalAppendHeapIso_label dependent j g),
    historyAppendWordMarkedState, historyMarkedRawState_eq_wordMarkedState]

end NearlyMinimax
