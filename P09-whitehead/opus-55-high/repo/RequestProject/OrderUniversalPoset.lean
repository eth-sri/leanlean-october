import RequestProject.StrictOrderComplex
import RequestProject.CombUniversalCover
import RequestProject.Tac
noncomputable section


/-! The order on the genuine path-class universal cover of a partial-order nerve. -/
bwd

namespace FiniteChains.Comb
universe u
variable (P : Type u) [PartialOrder P]

/-- Actual path classes, with the lifted comparability order rather than any extra data. -/
def UOrder (a : P) := UV (orderCx P) a

variable {P} {a : P}

def uOrderEnd (v : UOrder P a) : P := endV v

def uOrderStep (v : UOrder P a) q (h : uOrderEnd v ≤ q) :
    UOrder P a := extend (ordPos h) v

theorem uOrderStep_end (v : UOrder P a) q h :
    uOrderEnd (uOrderStep v q h) = q := endV_extend rfl

theorem uOrderStep_refl (v : UOrder P a) :
    uOrderStep v (uOrderEnd v) (le_refl _) = v := by
  have h := extendList_htpy (c := v)
    (by aesop) (htpy_ordSelf_nil _)
  tauto

/-- Triangle homotopy makes successive lifted comparabilities compose. -/
theorem uOrderStep_comp (v : UOrder P a) {q r} h hqr :
    uOrderStep (uOrderStep v q h) r ((uOrderStep_end v q h).le.trans hqr) =
      uOrderStep v r (h.trans hqr) := by
  have ht := extendList_htpy (X := orderCx P) (c := v)
    (by aesop)
    (htpy_orderCx_tri (P := P) h hqr)
  have hg : ordPos ((uOrderStep_end v q h).le.trans hqr) = ordPos hqr := by
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (uOrderStep_end v q h) rfl
    · rfl
  change extend (ordPos (by grind))
    (extend (ordPos h) v) = extend (ordPos (h.trans hqr)) v
  simp_all

def UOrderLe (v w : UOrder P a) :=
  ∃ h : uOrderEnd v ≤ uOrderEnd w, uOrderStep v _ h = w

theorem uOrderStep_eq_of_end_eq (v : UOrder P a) q
    h (hq : q = uOrderEnd v) : uOrderStep v q h = v := by
  subst q
  exact uOrderStep_refl v

instance uOrderPartialOrder : PartialOrder (UOrder P a) where
  le := UOrderLe
  le_refl v := ⟨le_refl _, uOrderStep_refl v⟩
  le_trans v w z hvw hwz := by
    cases' hvw with hvw hew
    cases' hwz with hwz hez
    refine ⟨hvw.trans hwz, ?_⟩
    have hc := uOrderStep_comp v hvw hwz
    grind
  le_antisymm v w hvw hwv := by
    cases' hvw with hvw hew
    cases' hwv with hwv _
    have h := le_antisymm hvw hwv
    have he :=
      uOrderStep_eq_of_end_eq v _ hvw h.symm
    exact he.symm.trans hew

theorem uOrderEnd_monotone : Monotone (uOrderEnd (P := P) (a := a)) :=
  fun _ _ h => h.1
