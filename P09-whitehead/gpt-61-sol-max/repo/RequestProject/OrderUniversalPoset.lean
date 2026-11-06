import Mathlib.Tactic

import RequestProject.StrictOrderComplex
import RequestProject.CombUniversalCover

/-! The order on the genuine path-class universal cover of a partial-order nerve. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable (P : Type u) [PartialOrder P]

/-- Actual path classes, with the lifted comparability order rather than any extra data. -/
def UOrder (a : P) := UV (orderCx P) a

variable {P} {a : P}

variable (v : UOrder P a)
def uOrderEnd  : P := endV v

variable (q : P)
noncomputable def uOrderStep   (h : uOrderEnd v ≤ q)  := extend (ordPos h) v

theorem uOrderStep_end   (h : uOrderEnd v ≤ q) :
    uOrderEnd (uOrderStep v q h) = q := endV_extend rfl

theorem uOrderStep_refl  :
    uOrderStep v (uOrderEnd v) (le_refl _) = v := by
  have h := extendList_htpy (c := (v : UV (orderCx P) a))
    (isPath_ordPos (le_refl (uOrderEnd v))) (htpy_ordSelf_nil (uOrderEnd v))
  simpa [extendList_cons (X := orderCx P), extendList_nil (X := orderCx P), uOrderStep] using h

/-- Triangle homotopy makes successive lifted comparabilities compose. -/
theorem uOrderStep_comp  {q r : P} (h : uOrderEnd v ≤ q) (hqr : q ≤ r) :
    uOrderStep (uOrderStep v q h) r ((uOrderStep_end v q h).le.trans hqr) =
      uOrderStep v r (h.trans hqr) := by
  have ht := extendList_htpy (X := orderCx P) (c := (v : UV (orderCx P) a))
    ((isPath_ordPos (P := P) h).append (isPath_ordPos (P := P) hqr))
    (htpy_orderCx_tri (P := P) h hqr)
  have hg : ordPos ((uOrderStep_end v q h).le.trans hqr) = ordPos hqr := by
    simp_all [uOrderStep_end]
  change extend (ordPos ((uOrderStep_end v q h).le.trans hqr))
    (extend (ordPos h) v) = extend (ordPos (h.trans hqr)) v
  rw [hg]
  simpa only [List.cons_append, List.nil_append, extendList_cons (X := orderCx P), extendList_nil (X := orderCx P)] using ht

def UOrderLe (v w : UOrder P a)  :=
  ∃ h : uOrderEnd v ≤ uOrderEnd w, uOrderStep v (uOrderEnd w) h = w

theorem uOrderStep_eq_of_end_eq  
    (h : uOrderEnd v ≤ q) (hq : q = uOrderEnd v) : uOrderStep v q h = v := by
  subst q
  exact uOrderStep_refl v

noncomputable instance uOrderPartialOrder : PartialOrder (UOrder P a) where
  le := UOrderLe
  le_refl v := ⟨le_refl _, uOrderStep_refl v⟩
  le_trans v w z hvw hwz := by
    grind [FiniteChains.Comb.UOrderLe, uOrderStep_comp]
  le_antisymm v w hvw hwv := by
    obtain ⟨hvw, hew⟩ := hvw
    obtain ⟨hwv, _⟩ := hwv
    have h  := le_antisymm hvw hwv
    have he  :=
      uOrderStep_eq_of_end_eq v _ hvw h.symm
    exact he.symm.trans hew

theorem uOrderEnd_monotone : Monotone (uOrderEnd (P := P) (a := a)) :=
  fun _ _ h => h.1

end FiniteChains.Comb
