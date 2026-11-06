module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceNaturalPrime

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_ray_slots_uniform  W  (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀θ : RayQuotient.Characters M H,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*
          HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := Exists.casesOn (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.natural_character_slot_bound M H hH W a b ha hWs hW Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ) fun degree h => Exists.casesOn h fun C h => And.casesOn h fun hC hbound => Exists.intro degree (Exists.intro C ⟨hC, fun η₀ => Filter.mp_mem (Filter.eventually_all.mpr fun θ => hbound (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.relativeCharacter M H hH η₀ θ)) (Filter.univ_mem' fun Z hz θ P hP hPcap η z hz0 F hcond Q hQM => hz θ P hP hPcap η z hz0 F hcond (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.internalQ Q η₀) (LE.le.trans inf_le_left hQM) (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.relativeCharacter_fixedQ M H hH η₀ θ (OAI.SevenEighths.CenteredMomentNaturalFixedRaySource.internalQ Q η₀) (LE.le.trans inf_le_left hQM) inf_le_right))⟩)

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
