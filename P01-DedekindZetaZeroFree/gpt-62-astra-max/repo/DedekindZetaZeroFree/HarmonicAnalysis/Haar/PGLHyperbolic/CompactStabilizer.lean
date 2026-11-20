module

public import DedekindZetaZeroFree.Adeles.Quotients.ArithmeticProperActionsAndOrbifoldCharts

@[expose] public section

namespace DedekindZetaZeroFree.KPCompactStabilizerHaarSources

noncomputable section
open scoped Classical ENNReal Matrix.Norms.Operator
open MeasureTheory MeasureTheory.Measure

section

variable (d : ℕ)

abbrev G := KPArithmeticAction.ProjectiveGroup d

abbrev X := KPArch.Space d

def o : X d := fun _ => (0, 0)

def K : Subgroup (G d) := MulAction.stabilizer (G d) (o d)

end

instance groupMeasurableSpace (d : ℕ) : MeasurableSpace (G d) := borel _

instance groupBorelSpace (d : ℕ) : BorelSpace (G d) := ⟨rfl⟩

instance stabilizerMeasurableSpace (d : ℕ) : MeasurableSpace (K d) := borel _

instance stabilizerBorelSpace (d : ℕ) : BorelSpace (K d) := ⟨rfl⟩

instance glLocallyCompact :
    LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
  Units.isOpenEmbedding_val.locallyCompactSpace

instance glSecondCountable :
    SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

instance projectiveLocallyCompact :
    LocallyCompactSpace (Matrix.ProjGenLinGroup (Fin 2) ℂ) :=
  inferInstanceAs (LocallyCompactSpace
    (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))

instance projectiveSecondCountable :
    SecondCountableTopology (Matrix.ProjGenLinGroup (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology
    (Matrix.GeneralLinearGroup (Fin 2) ℂ ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) ℂ)))

instance groupLocallyCompact (d : ℕ) : LocallyCompactSpace (G d) :=
  inferInstanceAs (LocallyCompactSpace (Fin d → Matrix.ProjGenLinGroup (Fin 2) ℂ))

instance groupSecondCountable (d : ℕ) : SecondCountableTopology (G d) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Matrix.ProjGenLinGroup (Fin 2) ℂ))

theorem stabilizer_isCompact (d : ℕ) : IsCompact (K d : Set (G d)) :=
  KPArithmeticAction.product_origin_stabilizer_compact d

instance stabilizerCompactSpace (d : ℕ) : CompactSpace (K d) :=
  isCompact_iff_compactSpace.mp (stabilizer_isCompact d)

instance stabilizerLocallyCompact (d : ℕ) : LocallyCompactSpace (K d) :=
  inferInstance

instance stabilizerSecondCountable (d : ℕ) : SecondCountableTopology (K d) :=
  inferInstanceAs (SecondCountableTopology ↥(K d : Set (G d)))

def stabilizerHaar (d : ℕ) : Measure (K d) :=
  haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (K d))

instance stabilizerHaar_isHaarMeasure (d : ℕ) : (stabilizerHaar d).IsHaarMeasure := by
  unfold stabilizerHaar
  infer_instance

instance stabilizerHaar_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (stabilizerHaar d) where
  measure_univ := by
    exact haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (K d)))

end

end DedekindZetaZeroFree.KPCompactStabilizerHaarSources
