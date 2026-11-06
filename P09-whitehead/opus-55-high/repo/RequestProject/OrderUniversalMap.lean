import RequestProject.CombPi2
import RequestProject.OrderUniversalPosetHom
import RequestProject.OrderNerveRealizationNestedSubcomplex
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

theorem uOrderMap_monotone f (hf : Monotone f) a :
    Monotone (α := UOrder P a) (β := UOrder Q (f a))
      (@univLiftV (orderCx P) (orderCx Q) a (orderCxMap f hf)) := by
  intro v w hvw
  have he (v : UOrder P a) :
      uOrderEnd (@univLiftV (orderCx P) _ a (orderCxMap f hf) v) = f (uOrderEnd v) :=
    @endV_univLiftV (orderCx P) _ a _ v
  refine ⟨(he v).le.trans ((hf hvw.1).trans (he w).ge), ?_⟩
  have h := univLiftV_extend (X := orderCx P) (Y := orderCx Q) a (orderCxMap f hf) (eb := ordPos hvw.1) (c := v) rfl
  have hw : extend (ordPos hvw.1) v = w := hvw.2
  rwd [hw] at h
  change extend (ordPos _) (@univLiftV (orderCx P) _ a _ v) = _
  calc
    _ = extend ((orderCxMap f hf).onE (ordPos hvw.1).1, true)
        (@univLiftV (orderCx P) _ a _ v) := by
      congr 1
      apply Prod.ext
      · apply Subtype.ext
        exact Prod.ext (he v) (he w)
      · rfl
    _ = _ := h.symm

/-- Functorial map between the actual ordered universal covers. -/
noncomputable def uOrderMap f (hf : Monotone f) a :
    UOrder P a →o UOrder Q (f a) :=
  ⟨@univLiftV _ _ a (orderCxMap f hf), uOrderMap_monotone f hf a⟩

theorem uOrderMap_end (f : P → Q) hf a v :
    uOrderEnd (uOrderMap f hf a v) = f (uOrderEnd v) :=
  @endV_univLiftV (orderCx P) _ a _ v

theorem uOrderMap_realization_projection (f : P → Q) hf a
    x :
    orderNerveRealizationMap uOrderEnd uOrderEnd_monotone
      (orderNerveRealizationMap (uOrderMap f hf a) (uOrderMap f hf a).monotone x) =
    orderNerveRealizationMap f hf
      (orderNerveRealizationMap uOrderEnd uOrderEnd_monotone x) := by
  rwd [orderNerveRealizationMap_comp, orderNerveRealizationMap_comp]
  have hm : (⟨uOrderEnd ∘ uOrderMap f hf a,
      uOrderEnd_monotone.comp (uOrderMap f hf a).monotone⟩ :
      {g : UOrder P a → Q // Monotone g}) =
      ⟨f ∘ uOrderEnd, hf.comp uOrderEnd_monotone⟩ :=
    Subtype.ext (funext (uOrderMap_end f hf a))
  simp_all
