module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.RightBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.EulerContinuation

open DedekindZetaZeroFree.Quantitative.EulerDomain

noncomputable section

open DedekindZetaZeroFree NumberField

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem Hu_differentiableOn (u : D.Row) :
    DifferentiableOn ℂ (fun p : Coordinates => Hu D u p.1 p.2.1 p.2.2) OmegaStar :=
  (Hu_normal_convergence D u).2.2.1

end

end DedekindZetaZeroFree.Quantitative.EulerContinuation
