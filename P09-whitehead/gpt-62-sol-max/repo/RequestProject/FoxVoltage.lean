module

public import RequestProject.Fox
public import RequestProject.PathVoltage

@[expose] public section

namespace FiniteChains.Comb.PathVoltage
open MonoidAlgebra

variable {E G A : Type*} [Group G]

/-- The product rule extends the signed Fox contribution of a single lifted germ. -/
theorem liftPath_fox (φ : FreeGroup A →* G) (w : E × Bool → FreeGroup A)
    (D : ((G × E) →₀ ℤ) →ₗ[ℤ] MonoidAlgebra ℤ G) (i : A)
    (h : ∀ g e, D (pathChain [liftGerm (φ ∘ w) g e]) =
      single g 1 * mapDomainRingHom ℤ φ (fox i (w e)))
    (p : List (E × Bool)) (g : G) :
    D (pathChain (liftPath (φ ∘ w) p g)) =
      single g 1 * mapDomainRingHom ℤ φ (fox i (p.map w).prod) := by
  induction p generalizing g with
  | nil => simp [liftPath]
  | cons e p ih =>
      change D (pathChain (liftGerm (φ ∘ w) g e :: _)) = _
      have hc : ∀ (z : (G × E) × Bool) l, pathChain (z :: l) = pathChain [z] + pathChain l :=
        fun z l => by simp [pathChain_cons]
      rw [hc, map_add, h, ih, List.map_cons, List.prod_cons, fox_mul, map_add, map_mul,
        mul_add, ← mul_assoc]
      congr 1
      rw [show mapDomainRingHom ℤ φ (grp (w e)) = single (φ (w e)) 1 from
        mapDomain_single, single_mul_single, mul_one]
      rfl

end FiniteChains.Comb.PathVoltage
