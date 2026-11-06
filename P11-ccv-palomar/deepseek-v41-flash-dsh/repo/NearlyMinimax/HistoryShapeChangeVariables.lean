module

public import NearlyMinimax.HistoryMaximalDelete

@[expose] public section

/-!
# Actual shape-level append/delete change of variables

The append range is identified with a true maximal-label condition in the
canonical heap. The actual append bijection and source rho factor yield an
exact infinite weighted sum change of variables. Mark integration and weak
transport are separate subsequent steps.
-/

noncomputable section
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

abbrev HistoryMaximalLabelShape (dependent : J → J → Prop) (j : J) :=
  {g : HistoryShape (fun a b => ¬ dependent a b) // ∃ x : WordHeapPiece g.out dependent,
    x ∈ historyMaximalPieces Finset.univ ∧ wordHeapLabel x = j}

variable (dependent : J → J → Prop) (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (j : J)

/-- The actual append bijection onto shapes having a true maximal piece with that label. -/
def historyShapeTerminalEquiv 
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (j : J) : HistoryShape (fun a b => ¬ dependent a b) ≃ HistoryMaximalLabelShape dependent j :=
  (Equiv.ofInjective (historyShapeAppend dependent j)
    (historyShapeAppend_injective dependent hrefl hsymm j)).trans
      ((Equiv.refl _).subtypeEquiv (fun g => historyShape_terminal_iff_maximal dependent hsymm j g))

omit [Fintype J] in
@[simp] theorem historyShapeTerminalEquiv_val 
    
    (g : HistoryShape (fun a b => ¬ dependent a b)) :
    (historyShapeTerminalEquiv dependent hrefl hsymm j g).val = historyShapeAppend dependent j g := rfl

end NearlyMinimax
