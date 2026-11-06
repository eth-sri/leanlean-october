module

public import OAI.NumberTheory.DirichletL.Energy.SlotHeight
public import OAI.NumberTheory.DirichletL.Energy.Reindex
public import OAI.NumberTheory.DirichletL.Moments.SlotClassTransport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.CenteredMomentAllocatedRayDictionary
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
local notation "O" => HeckeFamily.O

variable {α : Type*} [Fintype α] [DecidableEq α]

def originalEmbedding (s : Input α) (C : Ideal HeckeFamily.O) (B : actualAllocations s.pools C) :
    CenteredMomentCommonProfile.liveIndices B.val ↪ α :=
  ⟨Subtype.val, Subtype.val_injective⟩

def remaining (s : Input α) (C : Ideal HeckeFamily.O) (B : actualAllocations s.pools C)
    (L : Ideal HeckeFamily.O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    Finset (CenteredMomentCommonProfile.liveIndices B.val) :=
  CenteredMomentDivisorRaw.liveIndices (ι := CenteredMomentCommonProfile.liveIndices B.val) L a \ J

def originalImage (s : Input α) (C : Ideal HeckeFamily.O) (B : actualAllocations s.pools C)
    (L : Ideal HeckeFamily.O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) : Finset α :=
  (remaining s C B L a J).map (originalEmbedding s C B)

section RayData
variable (M : Ideal HeckeFamily.O) [NeZero M]
local instance : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

structure Matches (s : Input α) (η₀ : Character)
    (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
    (W : ℝ → ℂ) (bslot Z : ℝ) : Prop where
  character : ∀ i I, s.ν i I = idealCoeff (relativeCharacter M H hH η₀ (θ i)) I
  profile : ∀ i y, s.W i y = W y * (y : ℂ)^(-HeckeDyadic.shift (σ i) (freq i))
  pool : ∀ i, s.slots i = primePool M H bslot (Z^(w i))
  scale : ∀ i, s.P i = Z^(w i)

variable {M H hH}
variable {s : Input α} {η₀ : Character} {θ : α → RayQuotient.Characters M H}
  {w σ freq : α → ℝ} {W : ℝ → ℂ} {bslot Z : ℝ}
  (h : Matches M H hH s η₀ θ w σ freq W bslot Z)

include h

omit [DecidableEq α] in
lemma common_coefficient (τ : Character) (v : ℝ) (C R : Ideal HeckeFamily.O)
    (B : actualAllocations s.pools C) (i : CenteredMomentCommonProfile.liveIndices B.val)
    (I : Ideal HeckeFamily.O) :
    (commonData (withHeight s τ v) C R B).coefficient i I =
      idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
        annularWeight W (Z^(w i.val)) (σ i.val) (freq i.val) I := by
  change s.ν i.val I * s.W i.val ((I.absNorm : ℝ) / s.P i.val) = _
  rw [h.character, h.profile, h.scale]
  rfl

theorem common_energy (τ : Character) (v : ℝ) (C R : Ideal HeckeFamily.O)
    (B : actualAllocations s.pools C) (L : Ideal HeckeFamily.O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (m A : HeckeFamily.O) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (keep : HeckeFamily.O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d := commonData (withHeight s τ v) C R B
    energy τ m A 0 W₁ W₂
      (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) X₁ X₂ keep Φ K =
    energy τ m A 0 W₁ W₂
      (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) X₁ X₂ keep Φ K := by
  dsimp only
  have hc : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).coefficient i.val) =
      fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i.val.val)) I *
        annularWeight W (Z^(w i.val.val)) (σ i.val.val) (freq i.val.val) I := by
    funext i I
    exact common_coefficient h τ v C R B i.val I
  have hp : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).P i.val) = fun i => Z^(w i.val.val) := by
    funext i
    exact h.scale i.val.val
  have hs : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).slots i.val) =
      fun i => primePool M H bslot (Z^(w i.val.val)) := by
    funext i
    exact h.pool i.val.val
  have hhc := congrArg (fun f => fun i : remaining s C B L a J => heightCoefficient (f i) v) hc
  rw [hhc, hp, hs]
  rw [CenteredMomentEnergySlotHeight.inherited_height_energy τ m A W₁ W₂ _ _ _ _ _ _
    (fun i => h.scale i.val.val ▸ s.P_pos i.val.val)
    (fun i I hI => (s.prime i.val.val I (by rw [h.pool]; omega)).ne_zero)
    v 0 X₁ X₂ keep Φ K]
  exact CenteredMomentEnergyReindex.energy_subset_map (originalEmbedding s C B)
    (remaining s C B L a J) τ m A W₁ W₂
    (fun i => primePool M H bslot (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
    (fun i => Z^(w i)) 0 X₁ X₂ keep Φ K

omit h

end RayData
end SevenEighths.CenteredMomentAllocatedRayDictionary

end

end OAI
