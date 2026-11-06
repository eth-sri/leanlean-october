module

public import RequestProject.GenerationStep
public import RequestProject.FoxNaturality
public import RequestProject.CockcroftExtStep

@[expose] public section

namespace FiniteChains.BlockMor

theorem mapDomainRingHom_comp' {G H K : Type*} [Group G] [Group H] [Group K]
    (g : H →* K) (f : G →* H) (x : MonoidAlgebra ℤ G) :
    MonoidAlgebra.mapDomainRingHom ℤ g (MonoidAlgebra.mapDomainRingHom ℤ f x)
      = MonoidAlgebra.mapDomainRingHom ℤ (g.comp f) x := by
  change MonoidAlgebra.mapDomain g (MonoidAlgebra.mapDomain f x) = MonoidAlgebra.mapDomain (g.comp f) x
  rw [← MonoidAlgebra.mapDomain_comp]
  rfl
