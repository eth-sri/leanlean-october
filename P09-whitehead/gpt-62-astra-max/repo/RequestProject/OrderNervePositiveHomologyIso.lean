module

public import RequestProject.OrderNerveSingularH2Iso

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular

/-- The canonical realized-simplex map computes the actual positive integral
singular homology of every order-nerve realization, without finiteness assumptions. -/
theorem orderNerveExplicitSingularHomology_isIso (P : Type) [PartialOrder P] (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) (n + 1)) := by
  letI := orderNerveExplicitSingularHomology_mono P n
  letI := orderNerveExplicitSingularHomology_epi P n
  exact isIso_of_mono_of_epi _

noncomputable def orderNervePositiveSingularHomologyIso (P : Type) [PartialOrder P] (n : ℕ) :
    (AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology (n + 1) ≅
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) (n + 1)).obj (ModuleCat.of ℤ ℤ)).obj
        (orderNerveRealization P)) := by
  letI := orderNerveExplicitSingularHomology_isIso P n
  exact asIso (HomologicalComplex.homologyMap (orderNerveExplicitSingularMap P) _) ≪≫
    homologyMathlibIso _ _

end FiniteChains.Comb
