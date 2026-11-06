module

public import RequestProject.Pi2Extension
public import RequestProject.BaseChangeCycles

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresMor


open MonoidAlgebra

universe u

variable {α J α' J' α'' J'' : Type u}
  {ρ : J → FreeGroup α} {ρ' : J' → FreeGroup α'} {ρ'' : J'' → FreeGroup α''}

theorem mapDomainRingHom_comp (g : PresGroup ρ' →* PresGroup ρ'') (f : PresGroup ρ →* PresGroup ρ')
    (c : MonoidAlgebra ℤ (PresGroup ρ)) :
    MonoidAlgebra.mapDomainRingHom ℤ (g.comp f) c
      = MonoidAlgebra.mapDomainRingHom ℤ g (MonoidAlgebra.mapDomainRingHom ℤ f c) := by
  change MonoidAlgebra.mapDomain (g.comp f) c = MonoidAlgebra.mapDomain g (MonoidAlgebra.mapDomain f c)
  rw [← MonoidAlgebra.mapDomain_comp]
  rfl
