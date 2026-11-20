module

public import RequestProject.StrictOrderComplex
public import RequestProject.CombUniversalCover

@[expose] public section

/-! The order on the genuine path-class universal cover of a partial-order nerve. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable (P : Type u) [PartialOrder P]

/-- Actual path classes, with the lifted comparability order rather than any extra data. -/
def UOrder (a : P) := UV (orderCx P) a

variable {P} {a : P}

variable (v : UOrder P a)

def uOrderEnd : P := endV v

variable (q : P) (h : uOrderEnd v ≤ q)

noncomputable def uOrderStep :
    UOrder P a := extend (ordPos h) v

theorem uOrderStep_end :
    uOrderEnd (uOrderStep v q h) = q := endV_extend rfl

theorem uOrderStep_refl :
    uOrderStep v _ (le_refl _) = v := by
  have h := extendList_htpy
    (isPath_ordPos (le_refl (uOrderEnd v))) (htpy_ordSelf_nil (uOrderEnd v))
  assumption

/-- Triangle homotopy makes successive lifted comparabilities compose. -/
theorem uOrderStep_comp {q r : P} (h : uOrderEnd v ≤ q) (hqr : q ≤ r) :
    uOrderStep _ r ((uOrderStep_end v q h).le.trans hqr) =
      uOrderStep v r (h.trans hqr) := by
  have ht := extendList_htpy
    ((isPath_ordPos (P := P) h).append (isPath_ordPos (P := P) hqr))
    (htpy_orderCx_tri (P := P) h hqr)
  have hg : ordPos ((uOrderStep_end v q h).le.trans hqr) = ordPos hqr := by
    apply Prod.ext
    · grind [uOrderStep_end]
    · rfl
  change extend _
    (extend (ordPos h) v) = extend _ v
  simp_all

def UOrderLe (v w : UOrder P a) :=
  ∃ h : uOrderEnd v ≤ uOrderEnd w, uOrderStep v _ h = w

theorem uOrderStep_eq_of_end_eq (v : UOrder P a) (q : P)
    (h : uOrderEnd v ≤ q) (hq : q = uOrderEnd v) : uOrderStep v q h = v := by
  subst q
  exact uOrderStep_refl v

noncomputable instance uOrderPartialOrder : PartialOrder (UOrder P a) where
  le := UOrderLe
  le_refl v := ⟨le_refl _, uOrderStep_refl v⟩
  le_trans v w z hvw hwz := by
    obtain ⟨hvw, hew⟩ := hvw
    obtain ⟨hwz, hez⟩ := hwz
    refine ⟨hvw.trans hwz, ?_⟩
    grind [uOrderStep_comp]
  le_antisymm v w hvw hwv := by
    obtain ⟨hvw, hew⟩ := hvw
    obtain ⟨hwv, _⟩ := hwv
    grind [uOrderStep_eq_of_end_eq]

theorem uOrderEnd_monotone : Monotone (uOrderEnd (a := a)) :=
  fun _ _ h => h.1

end FiniteChains.Comb
