module
public import OAI.NumberTheory.DirichletL.PrimeRows.NormFiberExtraction
public import OAI.NumberTheory.DirichletL.Mellin.FiniteEulerRestoration

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius
namespace FiniteSFactor

end FiniteSFactor


namespace CompactScaleBridge

open ConcretePrimeRowBridge ShortDraftHeckeBridge

abbrev O := ConcretePrimeRowBridge.O

theorem idealsUpTo_card_le (N : ℕ) :
    (idealsUpTo N).card ≤ 64 * (N + 1) := by
  classical
  have himage : (columnsUpTo N).card = (idealsUpTo N).card := by
    unfold columnsUpTo
    exact Finset.card_image_of_injective _ idealGenerator_injective
  rw [← himage]
  apply ShortDraftLatticeCount.actual_eisenstein_count
  intro x hx
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hx
  have hqNat : ShortDraftLatticeCount.qNat (idealGenerator I) ≤ N := by
    rw [ActualEisensteinCubic.qNat_eq_absNorm_span, span_idealGenerator]
    exact ((mem_idealsUpTo.mp hI).2)
  change (ShortDraftLatticeCount.q
    (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat ≤ N at hqNat
  have hqInt :
      ((ShortDraftLatticeCount.q
        (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat : ℤ) ≤ N := by
    exact_mod_cast hqNat
  simpa using hqInt

end CompactScaleBridge

end

end OAI
