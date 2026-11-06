import Mathlib.Tactic

import RequestProject.CombPi2
import RequestProject.OrderUniversalPosetHom
import RequestProject.OrderNerveRealizationNestedSubcomplex

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

  (f : P → Q)
  (hf : Monotone f)
theorem uOrderMap_monotone   (a : P) :
    Monotone (α := UOrder P a) (β := UOrder Q (f a))
      (@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf)) := by
  intro v w hvw
  have he (v : UOrder P a) :
      uOrderEnd (@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v) = f (uOrderEnd v) :=
    @endV_univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v
  refine ⟨(he v).le.trans ((hf hvw.1).trans (he w).ge), ?_⟩
  have h := univLiftV_extend (X := orderCx P) (Y := orderCx Q) a (orderCxMap f hf) (eb := ordPos hvw.1) (c := v) rfl
  have hw : extend (ordPos hvw.1) v = w := hvw.2
  rw  [hw] at h
  change extend (ordPos _) (@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v) = _
  calc
    _ = extend ((orderCxMap f hf).onE (ordPos hvw.1).1, true)
        (@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v) := by
      apply_rules [Prod.ext, Subtype.ext]
    _ = _ := h.symm

/-- Functorial map between the actual ordered universal covers. -/
noncomputable def uOrderMap   (a : P) :
    UOrder P a →o UOrder Q (f a) :=
  ⟨@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf), uOrderMap_monotone f hf a⟩

abbrev uOrderMap_end   (a : P) (v : UOrder P a)  :=
  @endV_univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf) v

theorem uOrderMap_realization_projection   (a : P)
    (x : orderNerveRealization (UOrder P a)) :
    orderNerveRealizationMap uOrderEnd uOrderEnd_monotone
      (orderNerveRealizationMap (uOrderMap f hf a) (uOrderMap f hf a).monotone x) =
    orderNerveRealizationMap f hf
      (orderNerveRealizationMap uOrderEnd uOrderEnd_monotone x) := by
  rw  [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  have hm : (⟨uOrderEnd ∘ uOrderMap f hf a,
      uOrderEnd_monotone.comp (uOrderMap f hf a).monotone⟩ :
      {g : UOrder P a → Q // Monotone g}) =
      ⟨f ∘ uOrderEnd, hf.comp uOrderEnd_monotone⟩ :=
    Subtype.ext (funext (uOrderMap_end f hf a))
  exact congrArg (fun g => orderNerveRealizationMap g.1 g.2 x) hm

end FiniteChains.Comb
