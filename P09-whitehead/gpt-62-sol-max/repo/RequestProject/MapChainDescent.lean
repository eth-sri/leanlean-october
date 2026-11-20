module

public import RequestProject.ComponentComplex
public import RequestProject.TreeChainTopological
public import RequestProject.CombPi2
public import RequestProject.Pigeonhole
public import RequestProject.SubgroupCompactness
public import RequestProject.Pi2GenerationDescent

@[expose] public section

/-! Injectivity of the induced maps of cellular pushouts over the same overlap. -/

namespace FiniteChains.Comb
universe u

/-- The inclusion of the first term of a chain into its `i`-th term. -/
def inclFrom (c : ℕ → Complex2.{u}) (inc : ∀ i, Hom (c i) (c (i + 1))) :
    ∀ i, Hom (c 0) (c i)
  | 0 => Hom.id (c 0)
  | i + 1 => (inc i).comp (inclFrom c inc i)


section Functor

variable (K : Complex2.{u}) {L L' : Complex2.{u}} {D' : Complex2.{u}} (q : Hom D' K) (j : Hom D' L) (j' : Hom D' L')
  (k : Hom L L') (hjV : Function.Injective j.onV) (hjE : Function.Injective j.onE)
  (hj'V : Function.Injective j'.onV) (hj'E : Function.Injective j'.onE)
  (hj'F : Function.Injective j'.onF) (hkj : k.comp j = j')

include hkj in
theorem pushoutFunctor_injV (hkV : Function.Injective k.onV) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onV :=
  glueCell_functor_injective q.onV hkV (congrArg Hom.onV hkj) (fun _ => rfl) (fun _ => rfl)

include hkj in
theorem pushoutFunctor_injE (hkE : Function.Injective k.onE) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onE :=
  glueCell_functor_injective q.onE hkE (congrArg Hom.onE hkj) (fun _ => rfl) (fun _ => rfl)

include hkj in
theorem pushoutFunctor_injF (hkF : Function.Injective k.onF) :
    Function.Injective (pushoutFunctor q j j' k hjV hjE hj'V hj'E hj'F hkj).onF :=
  glueCell_functor_injective q.onF hkF (congrArg Hom.onF hkj) (fun _ => rfl) (fun _ => rfl)


end Functor
end FiniteChains.Comb
