import RequestProject.OrderUniversalPoset
import RequestProject.OrderPosetCovering


/-! Unique interval lifts in the genuine path-class universal-cover order. -/
namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

theorem uOrderStep_le (v : UOrder P a) q h :
    v ≤ uOrderStep v q h := by
  change UOrderLe _ _
  unfold UOrderLe
  grind [uOrderStep_end]


theorem uOrder_unique_up v q (h : uOrderEnd v ≤ q) :
    ∃! w : UOrder P a, v ≤ w ∧ uOrderEnd w = q := by
  refine ⟨uOrderStep v q h, ⟨uOrderStep_le v q h, uOrderStep_end v q h⟩, ?_⟩
  intro w hw
  cases' hw.1 with hle he
  simp_all

noncomputable def uOrderBack (v : UOrder P a) q (h : q ≤ uOrderEnd v) :
    UOrder P a := extend (ordNeg h) v

theorem uOrderBack_end (v : UOrder P a) q h :
    uOrderEnd (uOrderBack v q h) = q := endV_extend rfl

theorem uOrderBack_le (v : UOrder P a) q h :
    uOrderBack v q h ≤ v := by
  let hb :=
    (uOrderBack_end v q h).le.trans h
  refine ⟨hb, ?_⟩
  have hg : ordPos hb = revGerm (ordNeg h) := by
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (uOrderBack_end v q h) rfl
    · rfl
  change extend (ordPos hb) (extend (ordNeg h) v) = v
  rw [hg]
  exact extend_revGerm rfl

theorem uOrder_unique_down v q (h : q ≤ uOrderEnd v) :
    ∃! w : UOrder P a, w ≤ v ∧ uOrderEnd w = q := by
  refine ⟨uOrderBack v q h, ⟨uOrderBack_le v q h, uOrderBack_end v q h⟩, ?_⟩
  intro w hw
  cases' hw.1 with hle he
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
