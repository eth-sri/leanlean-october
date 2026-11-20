module

public import RequestProject.OrderNerveRealizationSubcomplex
public import RequestProject.TopologicalSingular.MathlibComparison

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Opposite AlgebraicTopology
open TopologicalSingular
open scoped Simplicial

section

variable {P : Type} [PartialOrder P]

variable {n : ℕ}

variable (s : (nerve P).obj (op ⦋n⦌))

/-- The actual continuous singular simplex associated with an order simplex. -/
noncomputable def orderNerveSingularSimplex :
    Simplex (orderNerveRealization P) n :=
  (simplicesMathlibIso (orderNerveRealization P)).inv.app (op ⦋n⦌)
    ((orderNerveRealizationUnit P).app (op ⦋n⦌) s)

theorem orderNerveSingularSimplex_supported (A : Set P) (s : (nerve P).obj (op ⦋n⦌))
    (hs : ∀ i, s.obj i ∈ A) (z : Domain n) :
    orderNerveSingularSimplex s z ∈ (orderNerveRealizationSubcomplex P A :
      Set (orderNerveRealization P)) := orderNerveRealizationSimplex_supported A s hs ⟨ULift.up ((simplexCoordinates n).symm z), rfl⟩

end

/-- The canonical chain comparison, with explicit continuous simplices as basis. -/
noncomputable def orderNerveExplicitSingularMap (P : Type) [PartialOrder P] :=
  orderNerveRealizationChainComparison P ≫ (freeComplexMathlibIso (orderNerveRealization P)).inv

theorem orderNerveExplicitSingularMap_single {P : Type} [PartialOrder P]
    (n : ℕ) (s : (nerve P).obj (op ⦋n⦌)) (r : ℤ) :
    (orderNerveExplicitSingularMap P).f n (Finsupp.single s r) =
      Finsupp.single (orderNerveSingularSimplex s) r := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.single s r)) = _
  aesop

end FiniteChains.Comb
