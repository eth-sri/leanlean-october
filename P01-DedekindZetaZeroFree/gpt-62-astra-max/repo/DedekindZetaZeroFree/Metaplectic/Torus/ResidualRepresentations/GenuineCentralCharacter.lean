module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.QuotientRealization

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open ResidualSphericalGeometry ResidualWeakEnergy KPGlobalResidualConstruction
open KPMsClearedTruncationL2.NativeWordBridge
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (M : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    {n : ℕ} (U : Fin n → KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (m : Fin n → ℕ)
    (w : ∀ i, Fin (m i) → List (Fin (KPContActualSphericalRightFieldIdentification.groupDimension F)))
variable (a : ∀ i, Fin (m i) → ℂ)
    (Z : ∀ i, Fin (m i) → KPContActualAllCuspSource.SmoothSections F ζ hζ M R P H (U i))
 abbrev genuineWordDerivative := KPSmoothActualFlowData.wordDerivative F ζ hζ

def originalGenuineSpace : Submodule ℂ (KPSmoothActualFlowData.X F ζ hζ → ℂ) where
  carrier := {f | ∀ g (ε : rootsOfUnity 3 F),
    f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε)) =
    (KPSmoothLocalQuotientCharts.ordinaryGenuine F ζ hζ ε : ℂ) *
      f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x ε
    change f _ + g _ = _ * (f _ + g _)
    rw [hf x ε, hg x ε, mul_add]
  smul_mem' := by
    intro c f hf x ε
    change c * f _ = _ * (c * f _)
    rw [hf x ε]
    ring

theorem finiteCenterSum_genuine :
    finiteCenterSum F ζ hζ M R P H U m w a Z ∈ originalGenuineSpace F ζ hζ := by
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact (KPMsClearedTruncationL2.ActualSmoothWordAction.word_mem F ζ hζ _
    ((w i j).map (wordIndexEquiv F)) (⟨originalScalar F ζ hζ _ R P H (Z i j), originalScalar_mem_smoothSpace F ζ hζ _ R P H (Z i j)⟩)).2.2

open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.ActualSmoothWordAction (word_right_covariant)

theorem original_word_genuine
    (f : KPSmoothActualFlowData.X F ζ hζ → ℂ)
    (hf : KPSmoothActualFlowData.SmoothAutomorphic F ζ hζ f)
    (hc : f ∈ originalGenuineSpace F ζ hζ)
    (v : List (KPSmoothActualFlowData.B F)) :
    genuineWordDerivative F ζ hζ v f ∈ originalGenuineSpace F ζ hζ := by
  intro g ε
  apply word_right_covariant F ζ hζ f hf _ _ _ (fun g => hc g ε) v g
  intro aa
  exact Subgroup.mem_center_iff.mp
    ((KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ)
      (MonoidHom.mem_range.mpr ⟨ε, rfl⟩)) _

theorem original_word_genuine_left
    (f : KPSmoothActualFlowData.X F ζ hζ → ℂ)
    (hf : KPSmoothActualFlowData.SmoothAutomorphic F ζ hζ f)
    (hc : f ∈ originalGenuineSpace F ζ hζ)
    (v : List (KPSmoothActualFlowData.B F)) (ε : rootsOfUnity 3 F)
    (g : KPSmoothActualFlowData.G F ζ hζ) :
    genuineWordDerivative F ζ hζ v f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε * g)) =
    (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      genuineWordDerivative F ζ hζ v f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) := by
  rw [← (Subgroup.mem_center_iff.mp
    ((KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ)
      (MonoidHom.mem_range.mpr ⟨ε, rfl⟩)) g)]
  exact original_word_genuine F ζ hζ f hf hc v g ε

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
