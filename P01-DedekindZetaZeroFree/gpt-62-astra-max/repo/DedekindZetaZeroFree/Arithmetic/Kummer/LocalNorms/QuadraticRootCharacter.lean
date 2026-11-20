module

public import DedekindZetaZeroFree.Arithmetic.Kummer.ConductorArtinCharacter

@[expose] public section

namespace DedekindZetaZeroFree.RMKummerLocalNormRoot
noncomputable section
open scoped NumberField Classical

variable (F : Type) [Field F] [NumberField F] (h12 : (primitiveRoots 12 F).Nonempty) (x : Fˣ)

theorem kappa_injective :
    Function.Injective (RMKummerConductor.kappa F h12 x) :=
  (rmKummerQuadraticRootsComplexMap_injective F h12 (RMKummerConductor.E F h12 x)).comp
    ((KummerTheory.nthRootsSubgroupEquivRootsOfUnity (RMKummerConductor.E F h12 x) 2).injective.comp
      (KummerTheory.chosenSimpleKummerRootCharacter_injective F (2 : ℕ+)
        (rmKummerTwo_ne_zero F) (rmKummerPrimitiveTwo F h12) x))

theorem kappa_continuous :
    Continuous (RMKummerConductor.kappa F h12 x) :=
  continuous_of_discreteTopology

theorem kappa_pow_two
    (σ : RMKummerConductor.E F h12 x ≃ₐ[F] RMKummerConductor.E F h12 x) :
    RMKummerConductor.kappa F h12 x σ ^ 2 = 1 :=
  rmKummerQuadraticRootsComplexMap_pow_two F h12 (RMKummerConductor.E F h12 x) _

end
end DedekindZetaZeroFree.RMKummerLocalNormRoot
