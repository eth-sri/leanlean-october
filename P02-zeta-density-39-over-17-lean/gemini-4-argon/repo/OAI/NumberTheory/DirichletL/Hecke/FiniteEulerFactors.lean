module
public import OAI.NumberTheory.DirichletL.PrimeRows.NormFiberExtraction
public import OAI.NumberTheory.DirichletL.Mellin.FiniteEulerRestoration

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid



namespace CompactScaleBridge

open ConcretePrimeRowBridge ShortDraftHeckeBridge


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
  have hnorm : Ideal.absNorm I ≤ N := (mem_idealsUpTo.mp hI).2
  have hqNat : ShortDraftLatticeCount.qNat (idealGenerator I) ≤ N := by
    rw [ActualEisensteinCubic.qNat_eq_absNorm_span, span_idealGenerator]
    exact hnorm
  have hnonneg := ShortDraftLatticeCount.qO_nonneg (idealGenerator I)
  have hcast : ((ShortDraftLatticeCount.q
      (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat : ℤ) =
      ShortDraftLatticeCount.q
        (ActualEisensteinCoordinates.coords (idealGenerator I)) :=
    Int.toNat_of_nonneg hnonneg
  change (ShortDraftLatticeCount.q
    (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat ≤ N at hqNat
  have hqInt :
      ((ShortDraftLatticeCount.q
        (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat : ℤ) ≤ N := by
    exact_mod_cast hqNat
  simpa only [hcast] using hqInt
