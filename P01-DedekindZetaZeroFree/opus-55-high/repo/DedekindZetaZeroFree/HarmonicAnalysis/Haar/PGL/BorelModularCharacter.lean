module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RankOne.NormalizedInduction

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneInduction

namespace OrdinaryModularProof
open MeasureTheory TopologicalSpace
open scoped Matrix NNReal ENNReal Matrix.Norms.Operator
variable (F : Type) [Field F] [NumberField F]
 (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))

set_option maxHeartbeats 1200000
 instance fieldSC : SecondCountableTopology (LocalField F w) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : SeparableSpace (LocalField F w) :=
    SeparableSpace.of_denseRange _ (w.denseRange_algebraMap F)
  infer_instance

instance unitsLC : LocallyCompactSpace (LocalField F w)ˣ :=
  (Units.isOpenEmbedding_val (R := LocalField F w)).locallyCompactSpace

instance unitsSC : SecondCountableTopology (LocalField F w)ˣ :=
  (Units.isOpenEmbedding_val (R := LocalField F w)).isEmbedding.secondCountableTopology
