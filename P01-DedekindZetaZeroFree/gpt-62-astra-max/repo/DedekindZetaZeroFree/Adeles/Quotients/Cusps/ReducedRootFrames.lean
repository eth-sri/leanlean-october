module

public import DedekindZetaZeroFree.Metaplectic.Unipotent.RationalFrameConjugation

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ENNReal NNReal
namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
open KPMsClearedTruncationL2
variable {F : Type} [Field F] [NumberField F]
    {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {C : ModelData F ζ hζ} {D : Iwasawa F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    {A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ C D R P H}
    {U : Level F ζ hζ}

 theorem level_frame_algebra {G : Type} [Group G] (h a f c e u : G)
    (hfa : Commute f a) (he : ∀ g : G, g * e = e * g) :
    h * f * (a * c * e * u) = h * (a * c * e * ((c⁻¹ * f * c) * u)) := by
  calc
    _ = h * (a * (f * c) * e * u) := by
      calc
        _ = h * (f * a * (c * e * u)) := by group
        _ = h * (a * f * (c * e * u)) := by rw [hfa.eq]
        _ = _ := by group
    _ = h * (a * c * ((c⁻¹ * f * c) * e) * u) := by group
    _ = _ := by rw [he]; group

end DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability

end
