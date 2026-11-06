import Mathlib.Tactic

import RequestProject.OrderUniversalPoset
import RequestProject.OrderPosetCovering

/-! Unique interval lifts in the genuine path-class universal-cover order. -/
namespace FiniteChains.Comb
variable {P : Type u} [PartialOrder P] {a : P}

  (v : UOrder P a)
  (q : P)
theorem uOrderStep_le   (h : uOrderEnd v ≤ q) :
    v ≤ uOrderStep v q h := by
  change UOrderLe _ _
  unfold UOrderLe
  simp only [uOrderStep_end]
  exact ⟨h, trivial⟩

theorem uOrderStep_eq_of_target_eq  {q r : P}
    (hq : uOrderEnd v ≤ q) (hr : uOrderEnd v ≤ r) (he : q = r) :
    uOrderStep v q hq = uOrderStep v r hr := by
  subst r
  rfl

theorem uOrder_unique_up   (h : uOrderEnd v ≤ q) :
    ∃! w : UOrder P a, v ≤ w ∧ uOrderEnd w = q := by
  refine ⟨uOrderStep v q h, ⟨uOrderStep_le v q h, uOrderStep_end v q h⟩, ?_⟩
  intro w hw
  obtain ⟨hle, he⟩ := hw.1
  exact he.symm.trans (uOrderStep_eq_of_target_eq v hle h hw.2)

noncomputable def uOrderBack   (h : q ≤ uOrderEnd v) :
    UOrder P a := extend (ordNeg h) v

theorem uOrderBack_end   (h : q ≤ uOrderEnd v) :
    uOrderEnd (uOrderBack v q h) = q := endV_extend rfl

theorem uOrderBack_le   (h : q ≤ uOrderEnd v) :
    uOrderBack v q h ≤ v := by
  let hb  :=
    (uOrderBack_end v q h).le.trans h
  refine ⟨hb, ?_⟩
  have hg : ordPos hb = revGerm (ordNeg h) := by
    simp_all [uOrderBack_end]
  change extend (ordPos hb) (extend (ordNeg h) v) = v
  rw [hg]
  exact extend_revGerm rfl

theorem uOrder_unique_down   (h : q ≤ uOrderEnd v) :
    ∃! w : UOrder P a, w ≤ v ∧ uOrderEnd w = q := by
  refine ⟨uOrderBack v q h, ⟨uOrderBack_le v q h, uOrderBack_end v q h⟩, ?_⟩
  intro w hw
  obtain ⟨hle, he⟩ := hw.1
  have hg : ordNeg hle = ordNeg h := by
    simp_all
  have hr : extend (ordNeg h) (extend (ordPos hle) w) = w := by
    rw [← hg]
    exact extend_revGerm (eb := ordPos hle) rfl
  have ht := congrArg (extend (ordNeg h)) he
  exact hr.symm.trans ht

/-- The endpoint map of actual path classes is a poset covering whenever the base
order complex is connected. -/
theorem uOrderEnd_isPosetCover (hc : IsConnected (orderCx P)) :
    IsPosetCover (uOrderEnd (P := P) (a := a)) where
  mono := uOrderEnd_monotone
  surj := endV_surjective hc
  up := uOrder_unique_up
  down := uOrder_unique_down

end FiniteChains.Comb
