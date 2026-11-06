module

public import DedekindZetaZeroFree.Adeles.Quotients.ArchimedeanFiniteProduct

@[expose] public section

namespace DedekindZetaZeroFree.PGLComplex.AdelicSlicesRaw
open MeasureTheory Topology NumberField
open scoped Classical Pointwise ENNReal Matrix.Norms.Operator
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem productHaarTransport
    (μ : Measure (ActualCover F ζ hζ)) [μ.IsHaarMeasure]
    (μArch : Measure (ArchGroup F)) [μArch.IsHaarMeasure] :
    ∃ ν : Measure (finiteSubgroup F ζ hζ), ν.IsHaarMeasure ∧
      Measure.map (fun p : ArchGroup F × finiteSubgroup F ζ hζ =>
        archimedeanInsertion F ζ hζ p.1 * p.2) (μArch.prod ν) = μ := by
  obtain ⟨e, he, _, _, _, _, hLC⟩ := actualArchFiniteSplitting F ζ hζ
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI := hLC
  letI : BorelSpace (ArchGroup F) := ⟨rfl⟩
  letI : SecondCountableTopology (ArchGroup F × finiteSubgroup F ζ hζ) :=
    e.toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (ArchGroup F) :=
    (isEmbedding_prodMkLeft (1 : finiteSubgroup F ζ hζ)).secondCountableTopology
  letI : SecondCountableTopology (finiteSubgroup F ζ hζ) :=
    (isEmbedding_prodMkRight (1 : ArchGroup F)).secondCountableTopology
  letI : LocallyCompactSpace (ArchGroup F × finiteSubgroup F ζ hζ) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  letI : LocallyCompactSpace (ArchGroup F) :=
    (isOpenQuotientMap_fst (Y := finiteSubgroup F ζ hζ)).locallyCompactSpace
  letI : IsTopologicalGroup (ArchGroup F) := inferInstance
  let ν₀ : Measure (finiteSubgroup F ζ hζ) := MeasureTheory.Measure.haar
  haveI : ν₀.IsHaarMeasure := inferInstance
  haveI : SFinite ν₀ := inferInstance
  haveI : SFinite μArch := inferInstance
  let μ₀ := Measure.map e (μArch.prod ν₀)
  let c := Measure.haarScalarFactor μ μ₀
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne'
  letI : (c • ν₀).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul ν₀ hc
  refine ⟨c • ν₀, inferInstance, ?_⟩
  have heq : (fun p : ArchGroup F × finiteSubgroup F ζ hζ =>
      archimedeanInsertion F ζ hζ p.1 * p.2) = e := by
    funext p; exact (he p.1 p.2).symm
  rw [heq, Measure.prod_smul_right, Measure.map_smul]
  · exact (Measure.isMulLeftInvariant_eq_smul μ μ₀).symm
  fun_prop

namespace ProductHaarTransportProof
