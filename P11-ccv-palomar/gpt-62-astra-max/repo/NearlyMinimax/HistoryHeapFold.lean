module

public import NearlyMinimax.HistoryCanonicalDeletion


@[expose] public section

/-! Marked local updates have identical folded states along any two actual
linear extensions of one labelled dependency heap. -/
noncomputable section
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable {J E ι X : Type*} (dependent : J → J → Prop) (update : J → E → X → X) (initial : X)
    {word : List J} (marks : Fin word.length → E)

theorem historyFold_move_to_front {update : ι → X → X}
    (before after : List ι) {x : ι}
    (hcomm : ∀ y ∈ before, ∀ state, update x (update y state) = update y (update x state))
    (initial : X) :
    (before ++ x :: after).foldl (fun state y => update y state) initial =
      (before ++ after).foldl (fun state y => update y state) (update x initial) := by
  have hfold : ∀ state, update x (before.foldl (fun s y => update y s) state) =
      before.foldl (fun s y => update y s) (update x state) := by
    induction before with
    | nil => simp
    | cons y ys ih =>
      aesop
  grind

/-- Finite heap linear extensions preserve the actual marked update fold.
Only incomparable actions must commute. -/
theorem historyFold_linear_extension_invariant [PartialOrder ι]
    (dependent : ι → ι → Prop) (update : ι → X → X)
    (hcomp : ∀ x y, dependent x y → x ≤ y ∨ y ≤ x)
    (hcomm : ∀ x y, ¬ dependent x y → ∀ state,
      update y (update x state) = update x (update y state))
    {l l' : List ι} (hperm : l.Perm l')
    (hl : l.Pairwise (fun x y => ¬ y ≤ x))
    (hl' : l'.Pairwise (fun x y => ¬ y ≤ x)) (initial : X) :
    l.foldl (fun state x => update x state) initial =
      l'.foldl (fun state x => update x state) initial := by
  induction l' generalizing l initial with
  | nil =>
    have he  := List.perm_nil.mp hperm
    subst l
    rfl
  | cons x xs ih =>
    obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp (hperm.mem_iff.mpr List.mem_cons_self)
    obtain ⟨hbefore, hafter, hcross⟩ := List.pairwise_append.mp hl
    have htailperm  :=
      (List.perm_middle.symm.trans hperm).cons_inv
    have htail  :=
      hl.sublist (List.Sublist.append (List.Sublist.refl before) (List.Sublist.cons x (List.Sublist.refl after)))
    have hmove : ∀ y ∈ before, ∀ state, update x (update y state) = update y (update x state) := by
      intro y hy state
      grind [(List.pairwise_cons.mp hl').1 y (by
        grind)]
    rw [historyFold_move_to_front before after hmove initial]
    exact ih htailperm htail hl'.of_cons _

def historyWordMarkedState : X :=
  historyWordState (fun p => update p.1 p.2) initial
    (List.ofFn (fun i => (word.get i, marks i)))

theorem historyWordMarkedState_eq_heapFold :
    let fn := List.ofFn (fun i => (⟨i⟩ : WordHeapPiece word dependent))
    historyWordMarkedState update initial marks =
      (fn).foldl
        (fun state x => update (wordHeapLabel x) (marks x.position) state) initial := by
  intro fn
  unfold historyWordMarkedState historyWordState
  have heq : (List.ofFn (fun i => (word.get i, marks i))) =
      (fn).map
        (fun x => (wordHeapLabel x, marks x.position)) := by
    rw [List.map_ofFn]
    rfl
  rw [heq, List.foldl_map]

/-- Any actual labelled heap isomorphism transports all marks and the raw
folded state exactly. Representative invariance is a proved conclusion. -/
theorem historyHeapMarkEquiv_state [MeasurableSpace E]
    {dependent : J → J → Prop}
    [Std.Symm dependent]
    {update : J → E → X → X}
    (hcomm : ∀ j k, ¬ dependent j k → ∀ e f state,
      update k f (update j e state) = update j e (update k f state))
    {u v : List J} {e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent}
    (he : ∀ x, wordHeapLabel (e x) = wordHeapLabel x)
    (initial : X) (marks : Fin u.length → E) :
    historyWordMarkedState update initial (historyHeapMarkEquiv e marks) =
      historyWordMarkedState update initial marks := by
  classical
  let l := List.ofFn (fun i => (⟨i⟩ : WordHeapPiece u dependent))
  let l' := List.ofFn (fun i => e.symm (⟨i⟩))
  have hp : l.Perm l' := (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr (fun _ _ h => congrArg WordHeapPiece.position h)) (List.nodup_ofFn.mpr (fun _ _ h => congrArg WordHeapPiece.position (e.symm.injective h)))).mpr (by
    intro x
    constructor
    · intro _
      apply List.mem_ofFn.mpr
      exact ⟨(e x).position, by
        have hx : (⟨(e x).position⟩) = e x := rfl
        rw [ e.symm_apply_apply]⟩
    · intro _
      apply List.mem_ofFn.mpr
      simp)
  have hl' : l'.Pairwise (fun x y => ¬ y ≤ x) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij hle
    simp only [l', List.getElem_ofFn] at hle
    have hh := wordHeap_reachable_position_le (e.monotone hle)
    simp at hh
    exact (Nat.not_le_of_lt hij) hh
  let action := fun (x : WordHeapPiece u dependent) state =>
    update (wordHeapLabel x) (marks x.position) state
  have hfold := historyFold_linear_extension_invariant
    (fun x y => dependent (wordHeapLabel x) (wordHeapLabel y)) action
    (fun _ _ => wordHeap_dependent_comparable)
    (fun x y h state => hcomm _ _ h ..) hp (by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij hle
      grind [wordHeap_reachable_position_le hle]) hl' initial
  rw [historyWordMarkedState_eq_heapFold dependent update initial marks]
  rw [hfold, historyWordMarkedState_eq_heapFold dependent update initial (historyHeapMarkEquiv e marks)]
  have hmap : l' = (List.ofFn (fun i => (⟨i⟩))).map e.symm := by
    rw [List.map_ofFn]
    rfl
  rw [hmap, List.foldl_map]
  congr 1
  funext state x
  have hlabel := he (e.symm x)
  have hmark := historyHeapMarkEquiv_position e marks (e.symm x)
  simp at hlabel hmark
  simp only [action, hlabel, hmark]

end NearlyMinimax
