module

public import DedekindZetaZeroFree.Adeles.RestrictedProduct.LocalTopology
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalCompactOpenAnnihilators
public import DedekindZetaZeroFree.Adeles.Characters.ArchimedeanAdditiveCharacters

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

namespace DedekindZetaZeroFree.KPAdelicHaarReference

variable (F : Type) [Field F] [NumberField F]

instance infiniteAdeles_measurableSpace : MeasurableSpace (InfiniteAdeleRing F) := borel _

instance infiniteAdeles_borelSpace : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩

theorem halfDifferentFactor_eq_one_of_not_mem
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : localDifferentSupport F ⊆ (S : Set (HeightOneSpectrum (𝓞 F))))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    localHalfDifferentFactor F v = 1 := by
  simp [localHalfDifferentFactor, localDifferentExponent_eq_zero_of_not_mem F S hS v hv]

def referenceMass : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), localHalfDifferentFactor F v

theorem referenceMass_eq_prod
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : localDifferentSupport F ⊆ (S : Set (HeightOneSpectrum (𝓞 F)))) :
    referenceMass F = ∏ v ∈ S, localHalfDifferentFactor F v := by
  classical
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  by_contra h
  exact hv (halfDifferentFactor_eq_one_of_not_mem F S hS v h)

theorem referenceMass_pos : 0 < referenceMass F := by
  rw [referenceMass_eq_prod F (finite_localDifferentSupport F).toFinset (by simp)]
  exact Finset.prod_pos (fun v _ => localHalfDifferentFactor_pos F v)

def integralPositiveCompacts : PositiveCompacts (KPAdelicTopology.FiniteAdeles F) :=
  ⟨⟨(KPAdelicTopology.integralAdeles F : Set (KPAdelicTopology.FiniteAdeles F)),
      KPAdelicTopology.integralAdeles_isCompact F⟩, by
    rw [(KPAdelicTopology.integralAdeles_isOpen F).interior_eq]
    simp⟩

@[simp] theorem coe_integralPositiveCompacts :
    (integralPositiveCompacts F : Set (KPAdelicTopology.FiniteAdeles F)) =
      (KPAdelicTopology.integralAdeles F : Set (KPAdelicTopology.FiniteAdeles F)) := rfl

def finiteMeasure : Measure (KPAdelicTopology.FiniteAdeles F) :=
  ENNReal.ofReal (referenceMass F) • Measure.addHaarMeasure (integralPositiveCompacts F)

instance finiteMeasure_isAddHaarMeasure : (finiteMeasure F).IsAddHaarMeasure := by
  unfold finiteMeasure
  apply Measure.IsAddHaarMeasure.smul
  · exact ENNReal.ofReal_ne_zero_iff.mpr (referenceMass_pos F)
  simp

instance finiteMeasure_regular : (finiteMeasure F).Regular := by
  unfold finiteMeasure
  exact Measure.Regular.smul ENNReal.ofReal_ne_top

instance finiteMeasure_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts (finiteMeasure F) := by
  unfold finiteMeasure
  exact IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top

instance finiteMeasure_sigmaFinite : SigmaFinite (finiteMeasure F) := by
  infer_instance

end DedekindZetaZeroFree.KPAdelicHaarReference

end

section

noncomputable section

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

namespace DedekindZetaZeroFree.KPAdelicHaarReference

variable (F : Type) [Field F] [NumberField F]

theorem referenceMass_ofReal_lt_top : ENNReal.ofReal (referenceMass F) < ⊤ :=
  ENNReal.ofReal_lt_top

theorem finiteMeasure_integralAdeles :
    finiteMeasure F
      (KPAdelicTopology.integralAdeles F : Set (KPAdelicTopology.FiniteAdeles F)) =
      ENNReal.ofReal (referenceMass F) := by
  rw [finiteMeasure, Measure.smul_apply, smul_eq_mul,
    ← coe_integralPositiveCompacts, Measure.addHaarMeasure_self, mul_one]
