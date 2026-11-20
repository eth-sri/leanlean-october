module

public import RequestProject.OrderUniversalPoset
public import RequestProject.OrderPosetCovering

@[expose] public section

/-! Unique interval lifts in the genuine path-class universal-cover order. -/
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

variable (v : UOrder P a)

theorem uOrderStep_le (q : P) (h : uOrderEnd v ≤ q) :
    v ≤ uOrderStep v q h := by
  change UOrderLe _ _
  unfold UOrderLe
  simp_all [uOrderStep_end]

variable (q : P)

theorem uOrder_unique_up (h : uOrderEnd v ≤ q) :
    ∃! w : UOrder P a, v ≤ w ∧ uOrderEnd w = q := by
  refine ⟨uOrderStep v q h, ⟨uOrderStep_le v q h, uOrderStep_end v q h⟩, ?_⟩
  intro w hw
  obtain ⟨hle, he⟩ := hw.1 <;> simp_all

section

variable (h : q ≤ uOrderEnd v)
include h

noncomputable def uOrderBack :
    UOrder P a := extend (ordNeg h) v

theorem uOrderBack_end :
    uOrderEnd (uOrderBack v q h) = q := endV_extend rfl

theorem uOrderBack_le :
    uOrderBack v q h ≤ v := by
  let hb :=
    (uOrderBack_end v q h).le.trans h
  refine ⟨hb, ?_⟩
  have hg : ordPos hb = revGerm (ordNeg h) := by
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (uOrderBack_end v q h) rfl
    · rfl
  change extend _ _ = v
  rw [hg]
  exact extend_revGerm rfl

theorem uOrder_unique_down :
    ∃! w : UOrder P a, w ≤ v ∧ uOrderEnd w = q := by
  refine ⟨uOrderBack v q h, ⟨uOrderBack_le v q h, uOrderBack_end v q h⟩, ?_⟩
  intro w hw
  obtain ⟨hle, he⟩ := hw.1
  have hg : ordNeg hle = ordNeg h := by
    apply Prod.ext
    · simp_all
    · rfl
  have hr : extend (ordNeg h) (extend (ordPos hle) w) = w := by
    rw [← hg]
    exact extend_revGerm (eb := ordPos hle) rfl
  exact hr.symm.trans (congrArg (extend (ordNeg h)) he)

end

/-- The endpoint map of actual path classes is a poset covering whenever the base
order complex is connected. -/
theorem uOrderEnd_isPosetCover (hc : IsConnected (orderCx P)) :
    IsPosetCover (uOrderEnd (a := a)) where
  mono := uOrderEnd_monotone
  surj := endV_surjective hc
  up := uOrder_unique_up
  down := uOrder_unique_down

end FiniteChains.Comb
