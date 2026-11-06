import RequestProject.OrderNerveRealizationSubcomplex
import RequestProject.TopologicalSingular.MathlibComparison
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.Comb
open CategoryTheory Opposite AlgebraicTopology
open TopologicalSingular
open scoped Simplicial


/-- The actual continuous singular simplex associated with an order simplex. -/
def orderNerveSingularSimplex {P} [PartialOrder P]
    {n} (s : (nerve P).obj (op ⦋n⦌)) :
    Simplex (orderNerveRealization P) n :=
  (simplicesMathlibIso _).inv.app _
    ((orderNerveRealizationUnit P).app _ s)


theorem orderNerveSingularSimplex_face {P} [PartialOrder P]
    {n} s (i : Fin (n + 2)) :
    face i (orderNerveSingularSimplex s) = orderNerveSingularSimplex ((nerve P).δ i s) := by
  apply ContinuousMap.ext
  intro z
  have h := congrArg (· (ULift.up ((simplexCoordinates n).symm z)))
    (orderNerveRealizationSimplex_operator P (SimplexCategory.δ i) s)
  change orderNerveRealizationSimplex P s
    (ULift.up (Convexity.StdSimplex.map (SimplexCategory.δ i) ((simplexCoordinates n).symm z))) = _ at h
  have he : Convexity.StdSimplex.map (SimplexCategory.δ i) ((simplexCoordinates n).symm z) =
      (simplexCoordinates _).symm (stdSimplex.map (SimplexCategory.δ i) z) := by
    apply (simplexCoordinates _).injective
    grind [simplexCoordinates_map, Homeomorph.apply_symm_apply]
  aesop

theorem orderNerveSingularSimplex_supported {P} [PartialOrder P]
    {n} A s
    (hs : ∀ i, s.obj i ∈ A) (z : Domain n) :
    orderNerveSingularSimplex s z ∈ (orderNerveRealizationSubcomplex P A :
      Set (orderNerveRealization P)) := orderNerveRealizationSimplex_supported A s hs (by aesop)

/-- The canonical chain comparison, with explicit continuous simplices as basis. -/
def orderNerveExplicitSingularMap P [PartialOrder P] :
    AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P) ⟶ complex (orderNerveRealization P) :=
  orderNerveRealizationChainComparison P ≫ (freeComplexMathlibIso _).inv

theorem orderNerveExplicitSingularMap_single {P} [PartialOrder P]
    n s r :
    (orderNerveExplicitSingularMap P).f n (Finsupp.single s r) =
      Finsupp.single (orderNerveSingularSimplex s) r := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.single s r)) = _
  aesop
