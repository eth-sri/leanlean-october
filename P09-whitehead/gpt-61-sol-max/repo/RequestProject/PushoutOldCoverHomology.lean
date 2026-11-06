import Mathlib.Tactic

import RequestProject.PushoutOldCoverCopies
import RequestProject.EmbeddedAcyclicUnion

/-! Actual global homology of the inverse image of K in the universal
cover of K ∪ D L.  This discharges the old-part H1/H2 exactness used in
regular-cover descent, for arbitrary cell sets. Unverified source. -/

noncomputable section

namespace FiniteChains.Comb.PushoutOldCover
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hconn : IsConnected D) (d₀ : D.V) (ht : Pi1Trivial i)
  (hEconn : IsConnected (pushoutComplex p i hiV hiE))

include hr he hf hEconn in
theorem copy_ranges_eq_of_meet
    (g h : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (d e : D.V)
    (hmeet : (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d =
      (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onV e) :
    Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV =
      Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onV ∧
    Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onE =
      Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onE ∧
    Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF =
      Set.range (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onF := by
  obtain ⟨q, hV, hE, hF⟩ :=
    copies_identified_of_meet p a hr he hf i hiV hiE hiF hconn d₀ ht hEconn g h d e hmeet
  refine ⟨?_, ?_, ?_⟩
  · ext v
    constructor
    · aesop
    · rintro ⟨d, rfl⟩
      refine ⟨a.smulV q⁻¹ d, ?_⟩
      simpa only [← a.mul_smulV, mul_inv_cancel, a.one_smulV] using hV (a.smulV q⁻¹ d)
  · ext e
    constructor
    · aesop
    · rintro ⟨d, rfl⟩
      refine ⟨a.smulE q⁻¹ d, ?_⟩
      simpa only [← a.mul_smulE, mul_inv_cancel, a.one_smulE] using hE (a.smulE q⁻¹ d)
  · ext f
    constructor
    · aesop
    · rintro ⟨d, rfl⟩
      refine ⟨a.smulF q⁻¹ d, ?_⟩
      simpa only [← a.mul_smulF, mul_inv_cancel, a.one_smulF] using hF (a.smulF q⁻¹ d)

include hp hr he hf hiF hconn ht hEconn in
theorem old_two_cycle_zero (hD : IsAcyclic D)
    (z : (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))).F →₀ ℤ)
    (hs : ∀ f ∈ z.support, ∃ k : K.F, f.val.2 = Sum.inl k)
    (hz : bdry2 (uCover (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) z = 0) : z = 0 := by
  let φ := translatedOldLift p i hiV hiE hiF hconn d₀ ht
  have hs' : ∀ f ∈ z.support, AcyclicCopies.oldFace φ f := by
    grind [FiniteChains.Comb.AcyclicCopies.oldFace, old_faces_covered]
  exact AcyclicCopies.two_cycle_zero φ
    (translatedOldLift_injective_E p hp a hr he i hiV hiE hiF hconn d₀ ht)
    (translatedOldLift_injective_F p hp a hr he i hiV hiE hiF hconn d₀ ht)
    hD (copy_ranges_eq_of_meet p a hr he hf i hiV hiE hiF hconn d₀ ht hEconn) z hs' hz

end FiniteChains.Comb.PushoutOldCover
