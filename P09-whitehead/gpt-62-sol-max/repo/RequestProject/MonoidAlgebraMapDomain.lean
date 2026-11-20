module

public import Mathlib.Algebra.MonoidAlgebra.Basic

@[expose] public section

namespace MonoidAlgebra

variable {R M N P : Type*} [Semiring R]

/-- Composition of coefficient reindexing for the wrapped group algebra. -/
theorem mapDomain_comp (f : M → N) (g : N → P) (x : MonoidAlgebra R M) :
    mapDomain (g ∘ f) x = mapDomain g (mapDomain f x) := by
  apply coeff_injective
  exact Finsupp.mapDomain_comp

@[simp] theorem mapDomain_id (x : MonoidAlgebra R M) : mapDomain id x = x := by
  apply coeff_injective
  exact Finsupp.mapDomain_id

/-- Pushing coefficients along group homomorphisms is functorial. -/
theorem mapDomainRingHom_apply_comp {R G H K : Type*} [Semiring R]
    [Monoid G] [Monoid H] [Monoid K] (f : G →* H) (g : H →* K) (x : MonoidAlgebra R G) :
    MonoidAlgebra.mapDomainRingHom R g (MonoidAlgebra.mapDomainRingHom R f x) =
      MonoidAlgebra.mapDomainRingHom R (g.comp f) x :=
  DFunLike.congr_fun (MonoidAlgebra.mapDomainRingHom_comp (R := R) g f).symm x

end MonoidAlgebra
