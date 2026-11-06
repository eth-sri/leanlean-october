module

public import OAI.NumberTheory.DirichletL.PrimeRows.NormFiberExtraction
public import OAI.NumberTheory.DirichletL.Mellin.FiniteEulerRestoration

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Filter Asymptotics Ideal NumberField


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

noncomputable def fixedTestWeight (W : ℝ → ℂ) (m n : ℕ) : ℂ :=
  W (2 * ((n : ℝ) / (2 * m : ℕ)))

theorem fixedTestWeight_eq (W : ℝ → ℂ) {m : ℕ} (hm : 0 < m) (n : ℕ) :
    fixedTestWeight W m n = W ((n : ℝ) / (m : ℝ)) := by
  unfold fixedTestWeight
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  push_cast
  field_simp

structure FixedTestPrimeMS
    {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (m : ℕ) (ε : ℝ) where
  H : ℕ
  selected : Finset O
  hp : ∀ p ∈ selected, p ≠ 0
  hprime : ∀ p ∈ selected, (Ideal.span {p} : Ideal O).IsMaximal
  hinj : Set.InjOn (fun p : O => (Ideal.span {p} : Ideal O)) (selected : Set O)
  hnormlower : ∀ p ∈ selected,
    ((2 * m : ℕ) : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ)
  hnormupper : ∀ p ∈ selected,
    (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤
      ((2 * m : ℕ) : ℝ) ^ (11 / 60 : ℝ)
  hH : Nat.floor (((2 * m : ℕ) : ℝ) ^ (11 / 10 : ℝ)) ≤ H
  hcount : ((2 * m : ℕ) : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤
    (selected.card : ℝ)
  hmean :
    (∑ u ∈ rowNormDisk H,
      ‖idealRowSum (outsideIdealsUpTo S (2 * m))
          (outsideIdealsUpTo_ne_bot S (2 * m))
          (outsideIdealsUpTo_good S (2 * m) hSbad)
          χ (fixedTestWeight W m) u‖ ^ 2) ≤
      ((2 * m : ℕ) : ℝ) ^ ((21 / 10 : ℝ) + ε)

theorem FixedTestPrimeMS.bound
    {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (m : ℕ) (ε : ℝ)
    (h : FixedTestPrimeMS χ S hSbad W m ε)
    (hm : 0 < m) (hε : 0 ≤ ε) (hW : ∀ y : ℝ, ‖W y‖ ≤ 1) :
    ‖∑ I ∈ outsideIdealsUpTo S (2 * m),
      baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))‖ ≤
      384 * ((2 * m : ℕ) : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  have hWeight : ∀ n : ℕ, ‖fixedTestWeight W m n‖ ≤ 1 := by
    intro n
    exact hW _
  have hD : 1 ≤ 2 * m := by omega
  have hbound := outsideCoeff_prime_extraction_from_MS χ
    (fixedTestWeight W m) S hSbad hWeight h.selected (fun p : O => p)
    (2 * m) h.H ε hD hε h.hp h.hprime h.hinj h.hnormlower
    h.hnormupper h.hH h.hcount h.hmean
  rw [← outsideIdealSum_eq_outsideCoeff_sum] at hbound
  simpa only [fixedTestWeight_eq W hm] using hbound

end CompactScaleBridge

end

end OAI
