/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthCompleteFields
public import VaughtConjecture.Knight.CappedDonorNormalization
public import VaughtConjecture.Knight.CanonicalPairedProfiles

@[expose] public section

namespace VaughtConjecture.Knight.Growth

open Transform Value ExtOrd AmalgamationPlan CappedDonor.Ref SharpWitnessComposition

noncomputable section

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}

namespace State

def encoder (j : ℕ) (S : State DA DQ) : ExtOrd → ExtOrd :=
  PairedSlotIncoming.encoder j (PairedSlotEncoding.values S.profile)

def normalize (j : ℕ) (S : State DA DQ) : State DA DQ := S.map (S.encoder j)

theorem profile_normalize (j : ℕ) (S : State DA DQ) (f : Field DA DQ) :
    (S.normalize j).profile f = PairedSlotEncoding.normalize j S.profile f := by
  rw [normalize, profile_map]
  exact PairedSlotIncoming.encoder_profile j S.profile f

end State

variable (X : RelativeData DA semA DQ semQ)

/-- A bounded witness need only reflect bottom on the finite profile. -/
theorem Admitted.map_on_profile {j : ℕ} {S : State DA DQ} (hS : Admitted X j S)
    {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop j) σ) (hj : 1 ≤ j)
    (hbot : ∀ f : Field DA DQ, σ (S.profile f) = ⊥ → S.profile f = ⊥) : Admitted X j (S.map σ) := by
  have hb f : σ (S.profile f) = ⊥ ↔ S.profile f = ⊥ := ⟨hbot f, fun h => h ▸ hσ.bot⟩
  have hν := hσ.bounded
  refine ⟨map_respects_of_same_bottom_pattern hS.private_lawful hS.private_lawful
      (fun d => d.2.2) hν (fun d => hb (.inl d.1)),
    map_respects_of_same_bottom_pattern hS.donor_lawful hS.donor_lawful
      (fun d => d.2.2) hν (fun d => hb (.inr d.1)),
    fun f => by rw [State.profile_map]; exact selfVis_map hσ hj (hS.visible f),
    fun d => congrArg σ (hS.shared d), ?_⟩
  intro hN hc
  obtain ⟨hz, hf, ht⟩ := hS.correct hN (fun d => (hb (.inl d.1)).symm.trans (hc d))
  refine ⟨fun z hz' => ?_, fun f hf' => ?_, fun t ht' => ?_⟩
  · simpa only [State.map, Requests.sec, Function.comp_apply, hσ.mono.map_min, hσ.bot] using congrArg σ (hz z hz')
  · simpa only [Requests.tOf, State.map, Requests.sec, Function.comp_apply, hσ.mono.map_min, map_comm hσ hN _ (X.off_lt f hf')]
      using congrArg σ (hf f hf')
  · simpa only [Requests.dOf, State.map, Requests.sec, Function.comp_apply, hσ.mono.map_min, map_comm hσ hN _ X.req.R_lt_N.le]
      using hσ.mono (ht t ht')

theorem normalize_admitted {j : ℕ} (hj : 1 ≤ j) {S : State DA DQ}
    (hS : Admitted X j S) : Admitted X j (S.normalize j) :=
  hS.map_on_profile X (PairedSlotIncoming.encoder_witness j _) hj
    (fun f => PairedSlotIncoming.encoder_reflects_bottom j _ (S.profile f))

theorem normalize_inventory (j : ℕ) {S : State DA DQ} (hp : ∀ f, S.profile f ≠ ⊤) :
    (S.normalize j).profile ∈ CanonicalPairedProfiles.inventory (Field DA DQ) j := by
  rw [show (S.normalize j).profile = PairedSlotEncoding.normalize j S.profile from
    funext (State.profile_normalize j S)]
  exact CanonicalPairedProfiles.normalize_mem_inventory _ _ hp

/-- The fixed catalogue is the whole canonical admitted family, before any
lifting request. It does not depend on a proposed replacement. -/
@[implicit_reducible]
def Catalogue (j : ℕ) := ↥(CanonicalPairedProfiles.Realized (Field DA DQ) j State.profile (Admitted X j))

instance catalogueFinite (j : ℕ) : Finite (Catalogue X j) :=
  CanonicalPairedProfiles.realized_finite _ _ _ _

def normalizedMember {j : ℕ} (hj : 1 ≤ j) {S : State DA DQ}
    (hS : Admitted X j S) (hp : ∀ f, S.profile f ≠ ⊤) : Catalogue X j :=
  ⟨(S.normalize j).profile, normalize_inventory j hp,
    S.normalize j, normalize_admitted X hj hS, rfl⟩

/-- A catalogue seed obtained directly from the admitted zero state. -/
def zeroMember (j : ℕ) (hj : 1 ≤ j) : Catalogue X j :=
  normalizedMember X hj (zero_admitted X j) (fun f => by cases f <;> exact bot_ne_top)

end

end VaughtConjecture.Knight.Growth
