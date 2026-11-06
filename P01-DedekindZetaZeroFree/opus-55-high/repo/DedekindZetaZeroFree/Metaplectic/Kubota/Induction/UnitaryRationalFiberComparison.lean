module

public import DedekindZetaZeroFree.Eisenstein.Induction.ArchimedeanScalarEquivalence
public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteTensorPolarizationComparison

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open IsDedekindDomain

namespace DedekindZetaZeroFree
namespace PrincipalOfKP
namespace ResidueCoreBridge
namespace CanonicalBinding

open KPGlobalTorusFiniteStages
attribute [local instance] KPGlobalTorusPeriodizationInverse.modelTopology

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def badSet (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P) :
    Finset (KPGlobalResidualConstruction.Places F) :=
  (Finset.univ.image (Sum.inl : NumberField.InfinitePlace F →
      KPGlobalResidualConstruction.Places F)) ∪
    (C.exceptional.image (Sum.inr : HeightOneSpectrum (𝓞 F) →
      KPGlobalResidualConstruction.Places F))

theorem finite_mem_badSet (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∈ C.exceptional) :
    Sum.inr q ∈ badSet F ζ hζ P C :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem Sum.inr hq)

theorem localReference_ne_zero (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)
    (q : HeightOneSpectrum (𝓞 F)) : localReference F ζ hζ P C q ≠ 0 := by
  intro h
  have hone : (localReference F ζ hζ P C q).val 1 = 1 := by
    simp only [localReference, map_one]
    simp only [Subgroup.one_mem, dite_true]
    change (((C.polarization q).ωL 1 : ℂˣ) : ℂ) = 1
    simp
  simp_all

def productUnitaryToRational (P : CompatibleModelData F ζ hζ) :
    KPGlobalTorusPeriodizationInverse.ProductUnitary F ζ hζ P →ₗ[ℂ]
      ↥(KPGlobalResidualConstruction.smoothRationalFiber F ζ hζ) :=
  (KPGlobalTorusPeriodizationInverse.untwistRational F ζ hζ).symm.toLinearMap.comp
    (KPGlobalTorusPeriodizationInverse.unitaryPeriodization F ζ hζ P).toLinearMap

theorem productUnitaryToRational_injective (P : CompatibleModelData F ζ hζ) :
    Function.Injective (productUnitaryToRational F ζ hζ P) := by
  have hper_inj :
      Function.Injective (KPGlobalTorusPeriodizationInverse.unitaryPeriodization F ζ hζ P) := by
    intro a b h
    have h' := congrArg (KPGlobalTorusPeriodizationInverse.unitaryAveraging F ζ hζ P) h
    rw [KPGlobalTorusPeriodizationInverse.unitaryAveraging_unitaryPeriodization F ζ hζ P a,
      KPGlobalTorusPeriodizationInverse.unitaryAveraging_unitaryPeriodization F ζ hζ P b] at h'
    exact h'
  intro a b h
  have h' : (KPGlobalTorusPeriodizationInverse.untwistRational F ζ hζ).symm
        (KPGlobalTorusPeriodizationInverse.unitaryPeriodization F ζ hζ P a) =
      (KPGlobalTorusPeriodizationInverse.untwistRational F ζ hζ).symm
        (KPGlobalTorusPeriodizationInverse.unitaryPeriodization F ζ hζ P b) := h
  exact hper_inj ((KPGlobalTorusPeriodizationInverse.untwistRational F ζ hζ).symm.injective h')

theorem badSet_eq_fullBad (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P) :
    badSet F ζ hζ P C =
      KPGlobalResidualConstruction.ScalarAbsorption.fullBad
        (A := NumberField.InfinitePlace F) C.exceptional := by
  ext x
  simp only [badSet, KPGlobalResidualConstruction.ScalarAbsorption.fullBad,
    Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_disjSum]
