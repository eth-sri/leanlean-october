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

def historyCanonicalWordMarks (dependent : J → J → Prop)
    (g : HistoryShape (fun a b => ¬ dependent a b)) {E : Type*}
    (marks : Fin (historyShapeLength dependent g) → E) : Fin g.out.length → E :=
  fun i => marks (Fin.cast (historyShapeLength_out dependent g).symm i)

theorem historyMarkedRawState_eq_wordMarkedState (dependent : J → J → Prop)
    {E X : Type*} (update : J → E → X → X) (initial : X)
    (g : HistoryShape (fun a b => ¬ dependent a b))
    (marks : Fin (historyShapeLength dependent g) → E) :
    historyMarkedRawState dependent update initial ⟨g, marks⟩ =
      historyWordMarkedState update initial g.out (historyCanonicalWordMarks dependent g marks) := by
  have hm : (List.ofFn (fun i : Fin (historyShapeLength dependent g) =>
      (historyShapeCanonicalLabels dependent g i, marks i))) =
      (List.ofFn (fun i : Fin (historyShapeLength dependent g) => i)).map
        (fun i => (historyShapeCanonicalLabels dependent g i, marks i)) := by
    rw [List.map_ofFn]
    rfl
  have ht : (List.ofFn (fun i : Fin (historyShapeLength dependent g) =>
      (historyShapeCanonicalLabels dependent g i, marks i))) =
      List.ofFn (fun i : Fin g.out.length => (g.out.get i, historyCanonicalWordMarks dependent g marks i)) := by
    apply List.ext_getElem (by grind [historyShapeLength_out])
    intro i hi hi'
    simp only [List.getElem_ofFn, historyShapeCanonicalLabels, historyCanonicalWordMarks]
    rfl
  have hh := congrArg (fun l : List (J × E) =>
    l.foldl (fun state p => update p.1 p.2 state) initial) (hm.symm.trans ht)
  rw [List.foldl_map] at hh
  assumption

def historyAppendWordMarks (dependent : J → J → Prop)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b))
    {E : Type*} [MeasurableSpace E] (fresh : E)
    (marks : Fin (historyShapeLength dependent g) → E) : Fin (g.out ++ [j]).length → E :=
  fun i => historyFiniteMarkAppendEquiv (historyShapeLength dependent g) (fresh, marks)
    (Fin.cast (by simp [historyShapeLength_out]) i)

section
variable (dependent : J → J → Prop)

theorem historyCanonicalAppend_word_marks
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b))
    {E : Type*} [MeasurableSpace E] (fresh : E)
    (marks : Fin (historyShapeLength dependent g) → E) :
    historyCanonicalWordMarks dependent (historyShapeAppend dependent j g)
      (historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)) =
      historyHeapMarkEquiv (historyCanonicalAppendHeapIso dependent hsymm j g)
        (historyAppendWordMarks dependent j g fresh marks) := by
  let e := historyCanonicalAppendHeapIso dependent hsymm j g
  let hlen : historyShapeLength dependent g + 1 = (g.out ++ [j]).length := by
    simp [historyShapeLength_out]
  have hc (x : WordHeapPiece (g.out ++ [j]) dependent) :
      historyCanonicalAppendCoordinates dependent hsymm j g (Fin.cast hlen.symm x.position) =
      Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm (e x).position := by
    rfl
  ext i
  let x := e.symm ⟨i⟩
  have hx : (e x).position = i := by simp only [x, e.apply_symm_apply]
  have hh := historyCanonicalMarkAppendEquiv_apply dependent hsymm j g (fresh, marks)
    (Fin.cast hlen.symm x.position)
  rw [hc x, hx] at hh
  have ht := historyHeapMarkEquiv_position e (historyAppendWordMarks dependent j g fresh marks) x
  rw [hx] at ht
  exact hh.trans ht.symm

section
variable (j : J) (g : HistoryShape (fun a b => ¬ dependent a b))

section
variable {E : Type*} [MeasurableSpace E] (fresh : E)
    (marks : Fin (historyShapeLength dependent g) → E)

@[simp] theorem historyAppendWordMarks_old (x : WordHeapPiece g.out dependent) :
    historyAppendWordMarks dependent j g fresh marks
      (historyPrefixHeapEmbedding g.out dependent j x).position =
      historyCanonicalWordMarks dependent g marks x.position := by
  unfold historyAppendWordMarks historyCanonicalWordMarks
  have he : Fin.cast (by simp [historyShapeLength_out])
      (historyPrefixHeapEmbedding g.out dependent j x).position =
      (Fin.cast (historyShapeLength_out dependent g).symm x.position).castSucc := by
    rfl
  simp_all

@[simp] theorem historyAppendWordMarks_fresh :
    historyAppendWordMarks dependent j g fresh marks (wordHeapAppendedPiece g.out dependent j).position = fresh := by
  unfold historyAppendWordMarks
  have he : Fin.cast (by simp [historyShapeLength_out])
      (wordHeapAppendedPiece g.out dependent j).position = Fin.last (historyShapeLength dependent g) := by
    apply Fin.ext
    exact (historyShapeLength_out dependent g).symm
  simp_all

end

theorem historyAppendWordMarkedState
    {E X : Type*} [MeasurableSpace E] (fresh : E)
    (marks : Fin (historyShapeLength dependent g) → E)
    (update : J → E → X → X) (initial : X) :
    historyWordMarkedState update initial (g.out ++ [j])
      (historyAppendWordMarks dependent j g fresh marks) =
      update j fresh (historyWordMarkedState update initial g.out
        (historyCanonicalWordMarks dependent g marks)) := by
  have ht : (List.ofFn (fun i : Fin (g.out ++ [j]).length =>
      ((g.out ++ [j]).get i, historyAppendWordMarks dependent j g fresh marks i))) =
      (List.ofFn (fun i : Fin g.out.length =>
        (g.out.get i, historyCanonicalWordMarks dependent g marks i))) ++ [(j, fresh)] := by
    apply List.ext_getElem (by grind)
    intro i hi hi'
    by_cases hiold : i < g.out.length
    · rw [List.getElem_append_left (by simpa only [List.length_ofFn] using hiold)]
      simp only [List.getElem_ofFn]
      have hg : (g.out ++ [j]).get ⟨i, by simpa only [List.length_ofFn] using hi⟩ = g.out.get ⟨i, hiold⟩ := by
        simp_all
      rw [hg]
      exact congrArg (fun a => (g.out.get ⟨i, hiold⟩, a))
        (historyAppendWordMarks_old dependent j g fresh marks (⟨⟨i, hiold⟩⟩ : WordHeapPiece g.out dependent))
    · have hieq : i = g.out.length := by
        grind
      subst i
      rw [List.getElem_append_right (by simp)]
      simp only [List.length_ofFn, Nat.sub_self, List.getElem_cons_zero, List.getElem_ofFn]
      have hg : (g.out ++ [j]).get ⟨g.out.length, by simp⟩ = j := by
        simp
      rw [hg]
      exact congrArg (fun a => (j, a)) (historyAppendWordMarks_fresh dependent j g fresh marks)
  unfold historyWordMarkedState historyWordState
  grind

end

/-- Actual canonical marked append applies exactly the fresh local update
once, even when the canonical representative reorders old occurrences. -/
theorem historyMarkedRawState_append
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {E X : Type*} [MeasurableSpace E] (update : J → E → X → X)
    (hcomm : ∀ j k, ¬ dependent j k → ∀ e f state,
      update k f (update j e state) = update j e (update k f state))
    (initial : X) (j : J) (h : HistoryMarked dependent E) (fresh : E) :
    historyMarkedRawState dependent update initial
      (historyMarkedAppend dependent hsymm j (h, fresh)) =
      update j fresh (historyMarkedRawState dependent update initial h) := by
  obtain ⟨g, marks⟩ := h
  change historyMarkedRawState dependent update initial
      ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩ = _
  rw [historyMarkedRawState_eq_wordMarkedState,
    historyCanonicalAppend_word_marks,
    historyHeapMarkEquiv_state dependent hsymm update hcomm
      (historyCanonicalAppendHeapIso dependent hsymm j g)
      (historyCanonicalAppendHeapIso_label dependent hsymm j g),
    historyAppendWordMarkedState, historyMarkedRawState_eq_wordMarkedState]

end

end NearlyMinimax
