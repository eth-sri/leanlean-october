/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFilteredRoot
public import VaughtConjecture.Knight.CappedDonorNormalization
public import VaughtConjecture.Knight.CanonicalPairedProfiles
public import VaughtConjecture.Knight.CappedDonorRepairPackage
public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.RelativeLadderRankRendering
public import VaughtConjecture.Knight.ReceivingCatalogueRanks
public import VaughtConjecture.Knight.RecursiveRungRendering
public import VaughtConjecture.Knight.PaddedTower
public import VaughtConjecture.Knight.SeparatedLayerFace

@[expose] public section

namespace VaughtConjecture.Knight

namespace Growth
open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref SharpWitnessComposition
open CanonicalPairedInverse LadderScalarRendering ReceivingCatalogueRanks
noncomputable section

section Complete
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {j : ℕ} (u : Cell D → ExtOrd) {p : D.below (A, j) → ExtOrd}

theorem complete_lawful (hp : RespectsSemanticsBelow sem (A, j) p) :
    RespectsSemanticsBelow sem (A, j) (fun d => complete u p d.1) := by
  simpa only [complete_present] using hp

theorem complete_visible (hu : ∀ d, SelfVis 1 (u d))
    (hp : RespectsSemanticsBelow sem (A, j) p) (d : Cell D) : SelfVis 1 (complete u p d) := by
  by_cases hd : D.grade d ≤ j
  · let e : D.below (A, j) := ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩
    rw [complete_present u p e]
    exact (show SelfVis (D.grade d) (p e) from (hp.orderly e).symm).mono (D.grade_pos d)
  · rw [complete_future u p d (not_le.mp hd)]; exact hu d

theorem complete_caps {γ : ExtOrd} (h : ∀ d, min (p d) γ = min (u d.1) γ)
    (d : Cell D) : min (complete u p d) γ = min (u d) γ := by
  by_cases hd : D.grade d ≤ j
  · rw [complete_present u p ⟨d, D.isPlan.subset_of_mem (D.scope_mem_plan d), hd⟩]; exact h _
  · rw [complete_future u p d (not_le.mp hd)]
end Complete

section Norm
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}

namespace State
def encoder (j : ℕ) (S : State DA DQ) : ExtOrd → ExtOrd :=
  PairedSlotIncoming.encoder j (PairedSlotEncoding.values S.profile)

def normalize (j : ℕ) (S : State DA DQ) : State DA DQ := S.map (S.encoder j)

theorem profile_normalize (j : ℕ) (S : State DA DQ) (f : Field DA DQ) :
    (S.normalize j).profile f = PairedSlotEncoding.normalize j S.profile f :=
  (profile_map _ S f).trans (PairedSlotIncoming.encoder_profile j S.profile f)
end State

variable (X : RelativeData DA semA DQ semQ)

theorem Admitted.map {j : ℕ} {S : State DA DQ} (hS : Admitted X j S)
    {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop j) σ) (hj : 1 ≤ j)
    (hbot : ∀ x, σ x = ⊥ → x = ⊥) : Admitted X j (S.map σ) where
  private_lawful := map_respects_of_bottom_reflecting hS.private_lawful
    (fun d => d.2.2) (boundedMap_of_witness hσ) hbot
  donor_lawful := map_respects_of_bottom_reflecting hS.donor_lawful
    (fun d => d.2.2) (boundedMap_of_witness hσ) hbot
  visible f := by rw [State.profile_map]; exact selfVis_map hσ hj (hS.visible f)
  shared d := congrArg σ (hS.shared d)
  correct hN hc := by
    have hc' : InClass X.ZA S.privateValues := fun d =>
      ⟨fun hd => (hc d).mp (by change σ (S.privateValues d.1) = ⊥; rw [hd, hσ.bot]),
       fun hd => hbot _ ((hc d).mpr hd)⟩
    obtain ⟨hz, hf, ht⟩ := hS.correct hN hc'
    refine ⟨fun z hZ => ?_, fun f hF => ?_, fun y hT => ?_⟩
    · change min (σ (S.donorValues z)) (σ (S.privateValues X.req.C)) = ⊥
      rw [← hσ.mono.map_min]; exact (congrArg σ (hz z hZ)).trans hσ.bot
    · change min (σ (S.donorValues f)) (σ (S.privateValues X.req.C)) =
        min (extVisibilityReplace (σ (S.privateValues (X.req.ρ f).1)) X.req.N
          (X.req.off f)) (σ (S.privateValues X.req.C))
      rw [← map_comm hσ hN _ (X.off_lt f hF), ← hσ.mono.map_min, ← hσ.mono.map_min]
      exact congrArg σ (hf f hF)
    · change min (extVisibilityReplace (σ (S.privateValues X.req.a.1)) X.req.N X.req.R)
        (σ (S.privateValues X.req.C)) ≤
        min (σ (S.donorValues y)) (σ (S.privateValues X.req.C))
      rw [← map_comm hσ hN _ X.req.R_lt_N.le, ← hσ.mono.map_min, ← hσ.mono.map_min]
      exact hσ.mono (ht y hT)

theorem normalize_admitted {j : ℕ} (hj : 1 ≤ j) {S : State DA DQ}
    (hS : Admitted X j S) : Admitted X j (S.normalize j) :=
  hS.map X (PairedSlotIncoming.encoder_witness j _) hj
    (PairedSlotIncoming.encoder_reflects_bottom j _)

theorem normalize_inventory (j : ℕ) {S : State DA DQ} (hp : ∀ f, S.profile f ≠ ⊤) :
    (S.normalize j).profile ∈ CanonicalPairedProfiles.inventory (Field DA DQ) j := by
  rw [show (S.normalize j).profile = PairedSlotEncoding.normalize j S.profile from
    funext (State.profile_normalize j S)]
  exact CanonicalPairedProfiles.normalize_mem_inventory _ _ hp

def Catalogue (j : ℕ) :=
  {a : Field DA DQ → ExtOrd //
    a ∈ CanonicalPairedProfiles.inventory (Field DA DQ) j ∧
    ∃ S : State DA DQ, Admitted X j S ∧ S.profile = a}

instance catalogueFinite (j : ℕ) : Finite (Catalogue X j) := by
  classical
  let := (CanonicalPairedProfiles.inventory_finite (Field DA DQ) j).fintype
  exact Finite.of_injective (fun a : Catalogue X j => (⟨a.1, a.2.1⟩ :
    ↥(CanonicalPairedProfiles.inventory (Field DA DQ) j)))
    fun _ _ h => Subtype.ext (congrArg (fun x : ↥(CanonicalPairedProfiles.inventory (Field DA DQ) j) => x.val) h)

def normalizedMember {j : ℕ} (hj : 1 ≤ j) {S : State DA DQ}
    (hS : Admitted X j S) (hp : ∀ f, S.profile f ≠ ⊤) : Catalogue X j :=
  ⟨(S.normalize j).profile, normalize_inventory j hp,
    S.normalize j, normalize_admitted X hj hS, rfl⟩

def zeroMember (j : ℕ) (hj : 1 ≤ j) : Catalogue X j :=
  normalizedMember X hj (zero_admitted X j) fun f => by cases f <;> exact bot_ne_top

theorem exists_supported_decoder {j : ℕ} (hj : 1 ≤ j) {S : State DA DQ}
    (hS : Admitted X j S) :
    ∃ Q : State DA DQ, Admitted X j Q ∧
      Q.profile ∈ CanonicalPairedProfiles.inventory (Field DA DQ) j ∧
      ∃ δ : ExtOrd → ExtOrd, Witness (gTop j) δ ∧
        (∀ d, δ (Q.profile d) = S.profile d) ∧
        (∀ d, δ (Q.profile d) = ⊥ → Q.profile d = ⊥) ∧
        ∀ x, OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) S.profile (δ x) := by
  obtain ⟨U, hU, hcanon, _, rest⟩ := exists_supported_decoder_of_map State.profile State.map
    State.normalize (Admitted X j) State.profile_map State.profile_normalize hj hS
    (fun hf hb => hS.map X hf hj hb) (normalize_admitted X hj)
  exact ⟨U, hU, hcanon, rest⟩

structure ProtectedRepair (a : Field DA DQ → ExtOrd) (S : State DA DQ) (j B : ℕ) where
  encoded : State DA DQ
  admitted : Admitted X j encoded
  canonical : encoded.profile ∈ CanonicalPairedProfiles.inventory (Field DA DQ) j
  prefix_eq : ∀ d, min (encoded.profile d) (grid j B) = min (a d) (grid j B)
  decoder : ExtOrd → ExtOrd
  witness : Witness (gTop j) decoder
  readback : ∀ d, decoder (encoded.profile d) = S.profile d
  grid_fixed : ∀ b < B, decoder (grid j b) = grid j b
  reaches : grid j B ≤ decoder (grid j B)
  boundary_fixed : ∀ d, a d < grid j B → decoder (a d) = a d

theorem exists_protected_repair {j B : ℕ} (hj : 1 ≤ j) {a : Field DA DQ → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory (Field DA DQ) j)
    {S : State DA DQ} (hS : Admitted X j S)
    (hag : ∀ d, min (a d) (grid j B) = min (S.profile d) (grid j B)) :
    Nonempty (ProtectedRepair X a S j B) := by
  obtain ⟨U, δ, hU, hc, hp, hw, hr, hf, hreach, hb⟩ := exists_protected_repair_of_map
    State.profile State.map State.normalize (Admitted X j) State.profile_map
    State.profile_normalize hj ha hS (fun hf hb => hS.map X hf hj hb)
    (normalize_admitted X hj) hag
  exact ⟨⟨U, hU, hc, hp, δ, hw, hr, hf, hreach, hb⟩⟩

theorem exists_rank_anchor {j : ℕ} (hj : 1 ≤ j) {S : State DA DQ} (hs : Admitted X j S) :
    ∃ a : Catalogue X j, ∀ d, fieldRank a.val d = fieldRank S.profile d := by
  obtain ⟨U, hU, hcanon, hrank, _⟩ := exists_supported_decoder_of_map State.profile State.map
    State.normalize (Admitted X j) State.profile_map State.profile_normalize hj hs
    (fun hf hb => hs.map X hf hj hb) (normalize_admitted X hj)
  exact ⟨⟨U.profile, hcanon, U, hU, rfl⟩, hrank⟩
end Norm

section Fibres
variable {n J r : ℕ} {P : SemScheme (n + 1)} {C : SemScheme J}
  {F : SemScheme r} {fP : Fin r ↪ Fin (n + 1)}
  {hvP : Finset.univ.image fP ∈ P.scheme.plan} {hP : P.restrictFace fP hvP = F}
  {fC : Fin r ↪ Fin J} {hvC : Finset.univ.image fC ∈ C.scheme.plan}
  {hC : C.restrictFace fC hvC = F}
  {X : RelativeData C.scheme C.rows P.scheme P.rows}
  (R : RootAttachment F fP hvP hP fC hvC hC X)

namespace RootAttachment
theorem privateIncl (j : ℕ) : GradedLe (Finset.univ.image fC, j) (Finset.univ, j) :=
  ⟨Finset.subset_univ _, le_rfl⟩
theorem donorIncl (j : ℕ) : GradedLe (Finset.univ.image fP, j) (Finset.univ, j) :=
  ⟨Finset.subset_univ _, le_rfl⟩

local notation "aP" => donorIncl (fP := fP)
local notation "aC" => privateIncl (fC := fC)
local notation "e" => rootMap F fP hvP hP fC hvC hC

include R in
theorem shared_at {S : State C.scheme P.scheme} {j : ℕ} (hS : Admitted X j S)
    (a : P.scheme.below (Finset.univ.image fP, j)) :
    S.donorValues a.1 = S.privateValues (e j a).1 := by
  rw [R.at_occurrence a]; exact hS.shared (R.full a)

def replace {j : ℕ} (S : State C.scheme P.scheme)
    (u : C.scheme.below (Finset.univ, j) → ExtOrd)
    (v : P.scheme.below (Finset.univ, j) → ExtOrd) : State C.scheme P.scheme :=
  ⟨complete S.privateValues u, complete S.donorValues v⟩

include R

theorem replace_shared {j : ℕ} {S : State C.scheme P.scheme} (hS : Admitted X j S)
    (u : C.scheme.below (Finset.univ, j) → ExtOrd)
    (v : P.scheme.below (Finset.univ, j) → ExtOrd)
    (he : ∀ a : P.scheme.below (Finset.univ.image fP, j),
      v (CellScheme.below.mono (aP j) a) = u (CellScheme.below.mono (aC j) (e j a))) :
    ∀ d : P.scheme.below X.root,
      (replace S u v).donorValues d.1 = (replace S u v).privateValues (X.κ d).1 := fun d => by
  by_cases hd : P.scheme.grade d.1 ≤ j
  · let a := R.filtered d hd
    change complete S.donorValues v d.1 = complete S.privateValues u (X.κ d).1
    exact (complete_present S.donorValues v (CellScheme.below.mono (aP j) a)).trans
      ((he a).trans ((complete_present S.privateValues u
        (CellScheme.below.mono (aC j) (e j a))).symm.trans
        (congrArg (complete S.privateValues u) (R.at_occurrence a))))
  · change complete S.donorValues v d.1 = complete S.privateValues u (X.κ d).1
    rw [complete_future S.donorValues v d.1 (not_le.mp hd),
      complete_future S.privateValues u (X.κ d).1 (by rw [R.grade]; exact not_le.mp hd)]
    exact hS.shared d

theorem replace_admitted {j : ℕ} (hj : j < X.req.N) {S : State C.scheme P.scheme}
    (hS : Admitted X j S)
    {u : C.scheme.below (Finset.univ, j) → ExtOrd}
    {v : P.scheme.below (Finset.univ, j) → ExtOrd}
    (hu : RespectsSemanticsBelow C.rows (Finset.univ, j) u)
    (hv : RespectsSemanticsBelow P.rows (Finset.univ, j) v)
    (he : ∀ a : P.scheme.below (Finset.univ.image fP, j),
      v (CellScheme.below.mono (aP j) a) = u (CellScheme.below.mono (aC j) (e j a))) :
    Admitted X j (replace S u v) where
  private_lawful := complete_lawful _ hu
  donor_lawful := complete_lawful _ hv
  visible := fun
    | .inl d => complete_visible S.privateValues (fun d => hS.visible (.inl d)) hu d
    | .inr d => complete_visible S.donorValues (fun d => hS.visible (.inr d)) hv d
  shared := R.replace_shared hS u v he
  correct hN := (not_le.mpr hj hN).elim

theorem private_before {j : ℕ} (hj : j < X.req.N) {S : State C.scheme P.scheme}
    (hS : Admitted X j S) {u : C.scheme.below (Finset.univ, j) → ExtOrd}
    (hu : RespectsSemanticsBelow C.rows (Finset.univ, j) u)
    {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (u d) γ = min (S.privateValues d.1) γ) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      (∀ d : C.scheme.below (Finset.univ, j), T.privateValues d.1 = u d) ∧
      S.CapEq γ T ∧
      (∀ d, j < C.scheme.grade d → T.privateValues d = S.privateValues d) ∧
      ∀ d, j < P.scheme.grade d → T.donorValues d = S.donorValues d := by
  have hlaw := (rootMap_lawful F fP hvP hP fC hvC hC j _).mp (hu.mono (aC j))
  obtain ⟨v, hv, hcap, hread⟩ := extend_cutoff P.bountiful hvP hlaw hS.donor_lawful hγ fun a => by
    change min (S.donorValues a.1) γ = min (u (CellScheme.below.mono (aC j) (e j a))) γ
    rw [R.shared_at hS a]; exact (hag (CellScheme.below.mono (aC j) (e j a))).symm
  exact ⟨replace S u v, R.replace_admitted hj hS hu hv hread,
    complete_present S.privateValues u,
    fun | .inl d => complete_caps S.privateValues hag d | .inr d => complete_caps S.donorValues hcap d,
    complete_future S.privateValues u, complete_future S.donorValues v⟩

theorem donor_before {j : ℕ} (hj : j < X.req.N) {S : State C.scheme P.scheme}
    (hS : Admitted X j S) {v : P.scheme.below (Finset.univ, j) → ExtOrd}
    (hv : RespectsSemanticsBelow P.rows (Finset.univ, j) v)
    {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (v d) γ = min (S.donorValues d.1) γ) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      (∀ d : P.scheme.below (Finset.univ, j), T.donorValues d.1 = v d) ∧
      S.CapEq γ T ∧
      (∀ d, j < C.scheme.grade d → T.privateValues d = S.privateValues d) ∧
      ∀ d, j < P.scheme.grade d → T.donorValues d = S.donorValues d := by
  let p := fun a => v (CellScheme.below.mono (aP j) ((e j).symm a))
  have hlaw : RespectsSemanticsBelow C.rows (Finset.univ.image fC, j) p :=
    (rootMap_lawful F fP hvP hP fC hvC hC j p).mpr
      (by simpa only [p, Equiv.symm_apply_apply] using hv.mono (aP j))
  obtain ⟨u, hu, hcap, hread⟩ := extend_cutoff C.bountiful hvC hlaw hS.private_lawful hγ fun a => by
    have hs := R.shared_at hS ((e j).symm a); rw [Equiv.apply_symm_apply] at hs
    change min (S.privateValues a.1) γ = min (p a) γ; rw [← hs]
    exact (hag (CellScheme.below.mono (aP j) ((e j).symm a))).symm
  exact ⟨replace S u v, R.replace_admitted hj hS hu hv
      (fun a => by simpa only [p, Equiv.symm_apply_apply] using (hread (e j a)).symm),
    complete_present S.donorValues v,
    fun | .inl d => complete_caps S.privateValues hcap d | .inr d => complete_caps S.donorValues hag d,
    complete_future S.privateValues u, complete_future S.donorValues v⟩

theorem private_all {j : ℕ} {S : State C.scheme P.scheme} (hS : Admitted X j S)
    {u : C.scheme.below (Finset.univ, j) → ExtOrd}
    (hu : RespectsSemanticsBelow C.rows (Finset.univ, j) u)
    {γ : ExtOrd} (hγ : SelfVis j γ)
    (hag : ∀ d, min (u d) γ = min (S.privateValues d.1) γ) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      (∀ d : C.scheme.below (Finset.univ, j), T.privateValues d.1 = u d) ∧
      S.CapEq γ T ∧
      (∀ d, j < C.scheme.grade d → T.privateValues d = S.privateValues d) ∧
      ∀ d, j < P.scheme.grade d → T.donorValues d = S.donorValues d := by
  by_cases hj : j < X.req.N
  · exact R.private_before hj hS hu hγ hag
  · obtain ⟨T, hT, hread, hcap, hfuture⟩ := private_repair X (not_lt.mp hj) hS hu hγ hag
    exact ⟨T, hT, hread, hcap, hfuture,
      fun d hd => (not_lt.mpr ((X.grade_le d).trans (not_lt.mp hj)) hd).elim⟩

theorem private_protected_all {j B : ℕ} (hj : 1 ≤ j) {S : State C.scheme P.scheme}
    (hS : Admitted X j S)
    (hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field C.scheme P.scheme) j)
    {u : C.scheme.below (Finset.univ, j) → ExtOrd}
    (hu : RespectsSemanticsBelow C.rows (Finset.univ, j) u)
    (hag : ∀ d, min (u d) (grid j B) = min (S.privateValues d.1) (grid j B)) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      (∀ d : C.scheme.below (Finset.univ, j), T.privateValues d.1 = u d) ∧
      S.CapEq (grid j B) T ∧
      (∀ d, j < C.scheme.grade d → T.privateValues d = S.privateValues d) ∧
      (∀ d, j < P.scheme.grade d → T.donorValues d = S.donorValues d) ∧
      Nonempty (ProtectedRepair X S.profile T j B) := by
  obtain ⟨T, hT, hread, hcap, hfa, hfq⟩ := R.private_all hS hu (grid_visible j B) hag
  exact ⟨T, hT, hread, hcap, hfa, hfq, exists_protected_repair X hj hcanon hT fun f => (hcap f).symm⟩

theorem donor_protected_before {j B : ℕ} (hj : 1 ≤ j) (hN : j < X.req.N)
    {S : State C.scheme P.scheme} (hS : Admitted X j S)
    (hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field C.scheme P.scheme) j)
    {v : P.scheme.below (Finset.univ, j) → ExtOrd}
    (hv : RespectsSemanticsBelow P.rows (Finset.univ, j) v)
    (hag : ∀ d, min (v d) (grid j B) = min (S.donorValues d.1) (grid j B)) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      (∀ d : P.scheme.below (Finset.univ, j), T.donorValues d.1 = v d) ∧
      S.CapEq (grid j B) T ∧
      (∀ d, j < C.scheme.grade d → T.privateValues d = S.privateValues d) ∧
      (∀ d, j < P.scheme.grade d → T.donorValues d = S.donorValues d) ∧
      Nonempty (ProtectedRepair X S.profile T j B) := by
  obtain ⟨T, hT, hread, hcap, hfa, hfq⟩ := R.donor_before hN hS hv (grid_visible j B) hag
  exact ⟨T, hT, hread, hcap, hfa, hfq, exists_protected_repair X hj hcanon hT fun f => (hcap f).symm⟩

theorem private_bottom_state {j : ℕ} {u : C.scheme.below (Finset.univ, j) → ExtOrd}
    (hu : RespectsSemanticsBelow C.rows (Finset.univ, j) u) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      ∀ d : C.scheme.below (Finset.univ, j), T.privateValues d.1 = u d := by
  obtain ⟨T, hT, hread, _, _, _⟩ := R.private_all (zero_admitted X j) hu (selfVis_bot j) (fun _ => by simp)
  exact ⟨T, hT, hread⟩

theorem donor_bottom_state {j : ℕ} (hN : j < X.req.N)
    {v : P.scheme.below (Finset.univ, j) → ExtOrd}
    (hv : RespectsSemanticsBelow P.rows (Finset.univ, j) v) :
    ∃ T : State C.scheme P.scheme, Admitted X j T ∧
      ∀ d : P.scheme.below (Finset.univ, j), T.donorValues d.1 = v d := by
  obtain ⟨T, hT, hread, _, _, _⟩ := R.donor_before hN (zero_admitted X j) hv (selfVis_bot j) (fun _ => by simp)
  exact ⟨T, hT, hread⟩
end RootAttachment
end Fibres

theorem donor_grade_lt {m N : ℕ} (D : SemScheme m) (hm : m < N) (d : Cell D.scheme) :
    D.scheme.grade d < N :=
  ((D.scheme.grade_le_card_scope d).trans
    (by simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_univ (D.scheme.scope d))).trans_lt hm
end
end Growth

namespace GrowthOrderedBase
open Transform Value ExtOrd AmalgamationPlan Growth RelativeLadderLayer
noncomputable section

private theorem faceMap_eq {m n : ℕ} (D : SemScheme n) (F : SemScheme m)
    (f : Fin m ↪ Fin n) (hv : Finset.univ.image f ∈ D.scheme.plan)
    (hf : D.restrictFace f hv = F) (d : Cell F.scheme) :
    SemSchemeBoundaryInput.faceMap D F f hv hf d =
      CellScheme.restrictFace.toCell D.scheme f hv (SemScheme.castCell hf.symm d) := by
  subst F; rfl

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)

def field (d : Cell I.boundary) : Field I.right.scheme I.left.scheme :=
  match (OrderedFaceBoundary.enumeration I.leftScheme I.rightScheme I.shared).symm d with
  | .inl c => .inr c
  | .inr c => .inl c.1

theorem field_read (S : State I.right.scheme I.left.scheme) (d : Cell I.boundary) :
    S.profile (field I d) = I.paste S.donorValues S.privateValues d := by
  unfold field WholeDonorBoundary.Input.paste OrderedFaceBoundarySemantics.paste
  change S.profile (match (OrderedFaceBoundary.enumeration
      I.leftScheme I.rightScheme I.shared).symm d with
    | .inl c => .inr c | .inr c => .inl c.1) =
    ProfileFaceUnion.paste I.shared.g S.donorValues S.privateValues
      ((OrderedFaceBoundary.enumeration I.leftScheme I.rightScheme I.shared).symm d)
  cases (OrderedFaceBoundary.enumeration I.leftScheme I.rightScheme I.shared).symm d <;> rfl

include T in
theorem shared {j : ℕ} {S : State I.right.scheme I.left.scheme} (hs : Admitted X j S)
    (d : Cell I.common.scheme) :
    S.donorValues (I.shared.f d) = S.privateValues (I.shared.g d) := by
  let d' : I.common.scheme.below (Finset.univ, m) :=
    ⟨d, Finset.subset_univ _, (I.common.scheme.grade_le_card_scope d).trans
      (by simpa using Finset.card_le_univ (I.common.scheme.scope d))⟩
  let a : I.left.scheme.below (Finset.univ.image I.commonLeft, m) :=
    CappedDonor.bP I.commonLeft I.visibleLeft m (CappedDonor.castBelow I.faceLeft.symm (Finset.univ, m) d')
  have ha : a.1 = I.shared.f d := by
    change CellScheme.restrictFace.toCell _ _ _
      (CappedDonor.castBelow I.faceLeft.symm (Finset.univ, m) _).1 = _
    erw [CappedDonor.castBelow_val]; exact (faceMap_eq _ _ _ _ _ d).symm
  have hb : (rootMap I.common I.commonLeft I.visibleLeft I.faceLeft
      I.commonRight I.visibleRight I.faceRight m a).1 = I.shared.g d := by
    erw [CappedDonor.commonFace_apply]
    rw [show (CappedDonor.bP I.commonLeft I.visibleLeft m).symm a =
      CappedDonor.castBelow I.faceLeft.symm (Finset.univ, m) d' from Equiv.symm_apply_apply _ _,
      CappedDonor.castBelow_castBelow_symm]
    change CellScheme.restrictFace.toCell _ _ _
      (CappedDonor.castBelow I.faceRight.symm (Finset.univ, m) _).1 = _
    erw [CappedDonor.castBelow_val]; exact (faceMap_eq _ _ _ _ _ d).symm
  have he := hs.shared (T.full a)
  change S.donorValues a.1 = S.privateValues (X.κ (T.full a)).1 at he
  rwa [← T.at_occurrence a, ha, hb] at he

theorem field_donor (S : State I.right.scheme I.left.scheme) (d : Cell I.left.scheme) :
    S.profile (field I (I.leftFace.map d)) = S.donorValues d :=
  (field_read I S _).trans (I.paste_left _ _ d)

include T in
theorem field_private {j : ℕ} {S : State I.right.scheme I.left.scheme}
    (hs : Admitted X j S) (d : Cell I.right.scheme) :
    S.profile (field I (I.rightFace.map d)) = S.privateValues d :=
  (field_read I S _).trans (I.paste_right _ _ (shared I X T hs) d)

theorem proper (hB : B ⊂ A) (hC : C ⊂ A) (d : Cell I.boundary) : I.boundary.scope d ≠ A := by
  rcases OrderedFaceBoundaryRows.covered I.leftScheme I.rightScheme I.shared R I.isPlan
      I.leftPlan_le I.rightPlan_le d with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · have hs := I.leftScheme.isPlan.subset_of_mem (I.leftScheme.scope_mem_plan d)
    change I.boundary.scope (I.leftFace.map d) ≠ A
    rw [show I.boundary.scope (I.leftFace.map d) = I.leftScheme.scope d from
      congrArg Prod.fst (I.leftFace.index d)]
    exact fun he => hB.not_ge (he ▸ hs)
  · have hs := I.rightScheme.isPlan.subset_of_mem (I.rightScheme.scope_mem_plan d)
    change I.boundary.scope (I.rightFace.map d) ≠ A
    rw [show I.boundary.scope (I.rightFace.map d) = I.rightScheme.scope d from
      congrArg Prod.fst (I.rightFace.index d)]
    exact fun he => hC.not_ge (he ▸ hs)

include T in
theorem boundary_lawful_at {j : ℕ} {S : State I.right.scheme I.left.scheme} (hs : Admitted X j S) :
    RespectsSemanticsBelow I.rows (A, j) (fun d => S.profile (field I d.1)) := by
  let u := CellScheme.zeroAbove (fun d : I.left.scheme.below (Finset.univ, j) => S.donorValues d.1)
  let v := CellScheme.zeroAbove (fun d : I.right.scheme.below (Finset.univ, j) => S.privateValues d.1)
  have hshared (i : Cell I.common.scheme) : u (I.shared.f i) = v (I.shared.g i) := by
    have hg : I.left.scheme.grade (I.shared.f i) = I.right.scheme.grade (I.shared.g i) :=
      congrArg (fun x : Finset ι × ℕ => x.2) (I.shared.shared i)
    by_cases hd : I.left.scheme.grade (I.shared.f i) ≤ j
    · exact (CellScheme.zeroAbove_low (fun d : I.left.scheme.below (Finset.univ, j) => S.donorValues d.1)
          ⟨_, Finset.subset_univ _, hd⟩).trans
        ((shared I X T hs i).trans
          (CellScheme.zeroAbove_low (fun d : I.right.scheme.below (Finset.univ, j) => S.privateValues d.1)
            ⟨_, Finset.subset_univ _, show I.right.scheme.grade (I.shared.g i) ≤ j from hg ▸ hd⟩).symm)
    · exact (CellScheme.zeroAbove_high _ hd).trans (CellScheme.zeroAbove_high _ (hg ▸ hd)).symm
  have hl := (I.paste_respects hs.donor_lawful.zeroAbove hs.private_lawful.zeroAbove hshared).toBelow (A, j)
  have he : (fun d : I.boundary.below (A, j) => S.profile (field I d.1)) =
      fun d => I.paste u v d.1 := by
    funext d; rw [field_read]
    rcases OrderedFaceBoundaryRows.covered I.leftScheme I.rightScheme I.shared R I.isPlan
        I.leftPlan_le I.rightPlan_le d.1 with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hi : I.boundary.grade d.1 ≤ j := d.2.2
      rw [← hc] at hi ⊢
      have hg : I.left.scheme.grade c ≤ j := (congrArg Prod.snd (I.leftFace.index c)).ge.trans hi
      exact (I.paste_left _ _ c).trans
        ((CellScheme.zeroAbove_low (fun d : I.left.scheme.below (Finset.univ, j) => S.donorValues d.1)
          ⟨c, Finset.subset_univ _, hg⟩).symm.trans (I.paste_left u v c).symm)
    · have hi : I.boundary.grade d.1 ≤ j := d.2.2
      rw [← hc] at hi ⊢
      have hg : I.right.scheme.grade c ≤ j := (congrArg Prod.snd (I.rightFace.index c)).ge.trans hi
      exact (I.paste_right _ _ (shared I X T hs) c).trans
        ((CellScheme.zeroAbove_low (fun d : I.right.scheme.below (Finset.univ, j) => S.privateValues d.1)
          ⟨c, Finset.subset_univ _, hg⟩).symm.trans (I.paste_right u v hshared c).symm)
  exact he ▸ hl

instance : Fintype (Catalogue X 1) := Fintype.ofFinite _
abbrev fields (a : Catalogue X 1) := a.val

include T in
theorem anchor_lawful (a : Catalogue X 1) :
    RespectsSemanticsBelow I.rows (A, 1) (fun d => a.val (field I d.1)) := by
  obtain ⟨S, hs, he⟩ := a.property.2
  rw [← he]; exact boundary_lawful_at I X T hs

section Supply
variable (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev scheme := carrier I.boundary hA
  (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)
abbrev semantics := rows I.boundary I.rows hA (field I) (fields I X) (proper I hB hC)

def privateIncl (d : I.right.scheme.below (Finset.univ, 1)) : I.boundary.below (A, 1) :=
  ⟨I.rightFace.map d.1, I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
    (congrArg Prod.snd (I.rightFace.index d.1)).le.trans d.2.2⟩

def donorIncl (d : I.left.scheme.below (Finset.univ, 1)) : I.boundary.below (A, 1) :=
  ⟨I.leftFace.map d.1, I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
    (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2⟩

def oldAt (d : I.boundary.below (A, 1)) : (scheme I X hA).below (A, 1) :=
  ⟨old I.boundary hA d.1, by rw [old_index]; exact d.2⟩
abbrev privateAt (d : I.right.scheme.below (Finset.univ, 1)) := oldAt I X hA (privateIncl I d)
abbrev donorAt (d : I.left.scheme.below (Finset.univ, 1)) := oldAt I X hA (donorIncl I d)

include T in
theorem exists_physical_section {S : State I.right.scheme I.left.scheme} (hs : Admitted X 1 S) :
    ∃ w : (scheme I X hA).below (A, 1) → ExtOrd,
      RespectsSemanticsBelow (semantics I X hA hB hC) (A, 1) w ∧
      ∀ d : I.boundary.below (A, 1), w (oldAt I X hA d) = S.profile (field I d.1) := by
  obtain ⟨a, ha⟩ := exists_rank_anchor X le_rfl hs
  exact ⟨fun d => renderWith I.boundary hA (field I) (fields I X) a S.profile ⊤ d.1,
    renderWith_respects I.boundary I.rows hA (field I) (fields I X) (proper I hB hC)
      a S.profile ha (fun _ => le_top) hs.visible (extVisibilityReplace_top 1 1)
      (boundary_lawful_at I X T hs),
    fun d => renderWith_old I.boundary hA (field I) (fields I X) a S.profile ⊤ ha d.1⟩

include T in
theorem private_bottom_supply {p : I.right.scheme.below (Finset.univ, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 1) p) :
    ∃ w, RespectsSemanticsBelow (semantics I X hA hB hC) (A, 1) w ∧
      ∀ d, w (privateAt I X hA d) = p d := by
  obtain ⟨S, hs, he, _, _, _⟩ := T.private_all (zero_admitted X 1) hp (selfVis_bot 1) (fun _ => by simp)
  obtain ⟨w, hw, hr⟩ := exists_physical_section I X T hA hB hC hs
  exact ⟨w, hw, fun d => (hr (privateIncl I d)).trans ((field_private I X T hs d.1).trans (he d))⟩

include T in
theorem donor_bottom_supply (hN : 1 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 1) p) :
    ∃ w, RespectsSemanticsBelow (semantics I X hA hB hC) (A, 1) w ∧
      ∀ d, w (donorAt I X hA d) = p d := by
  obtain ⟨S, hs, he, _, _, _⟩ := T.donor_before hN (zero_admitted X 1) hp (selfVis_bot 1) (fun _ => by simp)
  obtain ⟨w, hw, hr⟩ := exists_physical_section I X T hA hB hC hs
  exact ⟨w, hw, fun d => (hr (donorIncl I d)).trans ((field_donor I S d.1).trans (he d))⟩
end Supply
end
end GrowthOrderedBase

namespace GrowthHigherSources
open Transform Value ExtOrd Growth GrowthOrderedBase
noncomputable section

section Catalogue
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

instance (j : ℕ) : Fintype (Catalogue X j) := Fintype.ofFinite _

abbrev fields (j : ℕ) (a : Catalogue X j) : Field DA DQ → ExtOrd := a.val

theorem anchor_proper {j : ℕ} (a : Catalogue X j) (f : Field DA DQ) :
    fields X j a f ≠ ⊤ := a.property.1.2 f

theorem anchor_bound {j : ℕ} (a : Catalogue X j) (f : Field DA DQ) :
    fields X j a f ≤ CanonicalFieldLayer.ceiling j (Field DA DQ) :=
  (CanonicalPairedProfiles.inventory_bound _ _ a.property.1 f).trans
    (ofOrd_le_ofOrd.mpr (add_le_add (by gcongr; omega) le_rfl))

theorem anchor_visible_one {j : ℕ} (a : Catalogue X j) (f : Field DA DQ) :
    SelfVis 1 (fields X j a f) := by
  obtain ⟨S, hs, he⟩ := a.property.2
  change SelfVis 1 (a.val f); rw [← he]; exact hs.visible f

def state {j : ℕ} (a : Catalogue X j) : State DA DQ := State.ofProfile a.val

theorem state_admitted {j : ℕ} (a : Catalogue X j) : Admitted X j (state X a) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  have hs : state X a = S := State.profile_injective ((State.profile_ofProfile a.val).trans he.symm)
  exact hs.symm ▸ hS

theorem state_profile {j : ℕ} (a : Catalogue X j) :
    (state X a).profile = fields X j a := State.profile_ofProfile a.val

theorem state_proper {j : ℕ} (a : Catalogue X j) (f : Field DA DQ) :
    (state X a).profile f ≠ ⊤ := by rw [state_profile]; exact anchor_proper X a f

def normalized {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    (S : State DA DQ) (hs : Admitted X j S) (hp : ∀ f, S.profile f ≠ ⊤) :
    Catalogue X i := normalizedMember X hi (hs.down X hij) hp

theorem normalized_fields {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    (S : State DA DQ) (hs : Admitted X j S) (hp : ∀ f, S.profile f ≠ ⊤) :
    fields X i (normalized X hi hij S hs hp) = PairedSlotEncoding.normalize i S.profile :=
  funext (State.profile_normalize i S)
end Catalogue

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)

include T in
theorem anchor_lawful_at {j : ℕ} (a : Catalogue X j) :
    RespectsSemanticsBelow I.rows (A, j) (fun d => fields X j a (field I d.1)) := by
  obtain ⟨S, hs, he⟩ := a.property.2
  change RespectsSemanticsBelow I.rows (A, j) (fun d => a.val (field I d.1))
  rw [← he]; exact boundary_lawful_at I X T hs
end
end GrowthHigherSources

section TowerInstall
open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources
open AmalgamationPlan CoatomBoundaryExtension

namespace GrowthPaddedSuccessor
noncomputable section

section Anchors
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

def baseAnchor (a : Catalogue X 2) : Catalogue X 1 :=
  normalized X (by decide) (by decide : 1 ≤ 2) (state X a) (state_admitted X a) (state_proper X a)

theorem baseAnchor_ranks (a : Catalogue X 2) (d : Field DA DQ) :
    RelativeLadderLayer.ranks (fields X 1) (baseAnchor X a) d =
      LadderScalarRendering.fieldRank (fields X 2 a) d := by
  change LadderScalarRendering.fieldRank (fields X 1 (baseAnchor X a)) d = _
  rw [baseAnchor, normalized_fields, state_profile]
  exact ReceivingCatalogueRanks.fieldRank_normalize 1 a.val a.property.1.2 d
end Anchors

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

@[reducible] def cat : PaddedTower.Catalogue I where
  hA := hA
  Fld := Field I.right.scheme I.left.scheme
  St := State I.right.scheme I.left.scheme
  profile := State.profile
  Admissible := Admitted X
  Anchor := Catalogue X
  fields := fields X
  anchor_inv a := a.property.1
  field := field I
  proper := proper I hB hC
  birth_lawful := GrowthOrderedBase.anchor_lawful I X T
  incoming_lawful := anchor_lawful_at I X T
  baseAnchor := baseAnchor X
  baseAnchor_ranks := baseAnchor_ranks X
  visible_one := anchor_visible_one X
  anchor_bound := anchor_bound X
  profile_visible_one {_} _ {_} hS := hS.visible
  boundary_lawful_at _ _ hS := boundary_lawful_at I X T hS
  normalized _ hk {_} hj S hS hp := normalized X hk hj S hS hp
  normalized_fields _ hk {_} hj S hS hp := normalized_fields X hk hj S hS hp
  state := state X
  state_admissible := state_admitted X
  state_profile := state_profile X
  state_proper := state_proper X
  zeroSt := zero
  zero_admissible t := zero_admitted X (t + 2)
  zero_proper f := by cases f <;> exact bot_ne_top

abbrev input := PaddedTower.input (cat I X T hA hB hC)
abbrev carrier := PaddedTower.succCarrier (cat I X T hA hB hC)
abbrev rows := PaddedTower.succRows (cat I X T hA hB hC)
abbrev source := PaddedTower.succSource (cat I X T hA hB hC)
abbrev old := PaddedTower.succOld (cat I X T hA hB hC)
abbrev leaf := PaddedTower.succLeaf (cat I X T hA hB hC)
abbrev cell_cases := PaddedTower.succ_cell_cases (cat I X T hA hB hC)
abbrev leaf_index := PaddedTower.succ_leaf_index (cat I X T hA hB hC)
abbrev leaf_row := PaddedTower.succ_leaf_row (cat I X T hA hB hC)
abbrev source_lawful := PaddedTower.succ_source_lawful (cat I X T hA hB hC)
abbrev source_ceiling := PaddedTower.succ_source_ceiling (cat I X T hA hB hC)
abbrev source_prefix := @PaddedTower.succ_source_prefix _ _ _ _ _ _ _ _ _ I (cat I X T hA hB hC)
abbrev source_supported := PaddedTower.succ_source_supported (cat I X T hA hB hC)
end
end GrowthPaddedSuccessor

namespace GrowthPaddedContract
open GrowthPaddedSuccessor
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (attach : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev base := PaddedTower.base (cat I X attach hA hB hC)
abbrev baseRows := PaddedTower.baseRows (cat I X attach hA hB hC)
abbrev base_full_grade := PaddedTower.base_full_grade (cat I X attach hA hB hC)
abbrev Layer := PaddedTower.Layer (cat I X attach hA hB hC)
abbrev initial := PaddedTower.initial (cat I X attach hA hB hC)
end
end GrowthPaddedContract

namespace GrowthPaddedStepRows
open GrowthPaddedSuccessor GrowthPaddedContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {attach : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X attach hA hB hC k)

abbrev grid := PaddedTower.stepGrid P
abbrev ceiling := PaddedTower.stepCeiling P
abbrev selected := PaddedTower.selected P

variable (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)
@[reducible] def carrier := PaddedTower.stepCarrier P hnext
@[reducible] def old := PaddedTower.stepOld P hnext
@[reducible] def controller := PaddedTower.stepController P hnext
@[reducible] def ownerEquiv := PaddedTower.stepOwnerEquiv P hk hnext
@[reducible] def member := PaddedTower.stepMember P hk hnext
@[reducible] def rows := PaddedTower.stepRows P hk hnext
@[reducible] def source := PaddedTower.stepSource P hk hnext
abbrev source_old := PaddedTower.step_source_old P hk hnext
abbrev source_lawful := PaddedTower.step_source_lawful P hk hnext
abbrev source_supported := PaddedTower.step_source_supported P hk hnext
abbrev source_agreement := @PaddedTower.step_source_agreement _ _ _ _ _ _ _ _ _ I (cat I X attach hA hB hC) k P hk hnext
abbrev inherited_row := PaddedTower.step_inherited_row P hk hnext
end
end GrowthPaddedStepRows

namespace GrowthPaddedIteration
open GrowthPaddedSuccessor GrowthPaddedContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {attach : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}

abbrev successor (P : Layer I X attach hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card) :=
  PaddedTower.successor P hk hnext

variable (I X attach hA hB hC)
abbrev build := PaddedTower.build (cat I X attach hA hB hC)
abbrev build_plan := PaddedTower.build_plan (cat I X attach hA hB hC)
end
end GrowthPaddedIteration

namespace GrowthPaddedInstallation
open GrowthPaddedSuccessor
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (attach : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev build_coded := PaddedTower.build_coded (cat I X attach hA hB hC)
abbrev face_map := @PaddedTower.buildFace_map _ _ _ _ _ _ _ _ _ I (cat I X attach hA hB hC)
abbrev donorFace := PaddedTower.donorFace (cat I X attach hA hB hC) hB
abbrev privateFace := PaddedTower.privateFace (cat I X attach hA hB hC) hC
abbrev donor_order := PaddedTower.donor_order (cat I X attach hA hB hC) hB
abbrev private_order := PaddedTower.private_order (cat I X attach hA hB hC) hC
abbrev full_occupied := PaddedTower.full_occupied (cat I X attach hA hB hC)
end
end GrowthPaddedInstallation

namespace GrowthPaddedCutTransport
open GrowthPaddedContract GrowthPaddedIteration GrowthPaddedStepRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows}
  {T : Growth.RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k)

theorem step_lift (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card) {U V : Finset ι × ℕ}
    (h : GradedLe U V) (hv : V.2 ≤ k) (hl : CappedLift P.rows h) :
    CappedLift (successor P hk hnext).rows h :=
  SeparatedLayerFace.lift P.carrier (Catalogue X (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated (by omega))
    P.rows (rows P hk hnext) (inherited_row P hk hnext) h (fun h => by have := h.2; omega) hl

def baseEquiv : (base I X T hA hB hC).below (A, 1) ≃ P.carrier.below (A, 1) :=
  Equiv.ofBijective
    (fun d => ⟨P.baseMap d.1, by simpa only [P.base_index] using d.2⟩)
    ⟨fun _ _ h => Subtype.ext (P.base_mono.injective (congrArg Subtype.val h)), fun d => by
      rcases P.cases d.1 with ⟨b, hb⟩ | ⟨_, hg, _⟩
      · exact ⟨⟨b, by simpa only [hb, P.base_index] using d.2⟩, Subtype.ext hb.symm⟩
      · have := d.2.2; change 2 ≤ (P.carrier.cell d.1).2 at hg; omega⟩

theorem base_respects_iff (p : (base I X T hA hB hC).below (A, 1) → ExtOrd) :
    RespectsSemanticsBelow (baseRows I X T hA hB hC) (A, 1) p ↔
      RespectsSemanticsBelow P.rows (A, 1) (p ∘ (baseEquiv P).symm) :=
  respects_iff_of_equiv (baseEquiv P)
    (fun d => (congrArg Prod.snd (P.base_index d.1)).symm)
    (fun x y => by
      change ((base I X T hA hB hC).cell x.1).1 ⊆ ((base I X T hA hB hC).cell y.1).1 ↔
        (P.carrier.cell (P.baseMap x.1)).1 ⊆ (P.carrier.cell (P.baseMap y.1)).1
      rw [P.base_index, P.base_index])
    (fun c d _ => (P.base_row c.1 d).symm) p
end
end GrowthPaddedCutTransport

namespace GrowthPaddedNativeRows
open GrowthPaddedContract GrowthPaddedIteration
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

def owner : (t : ℕ) → (ht : t + 2 ≤ A.card) → Catalogue X (t + 2) →
    Cell (build I X T hA hB hC t ht).carrier
  | 0, _, a => GrowthPaddedSuccessor.leaf I X T hA hB hC a
  | t + 1, _, a => (GrowthPaddedStepRows.controller
      (build I X T hA hB hC t (by omega)) (by omega) a).1

def source : (t : ℕ) → (ht : t + 2 ≤ A.card) → Catalogue X (t + 2) →
    Cell (build I X T hA hB hC t ht).carrier → ExtOrd
  | 0, _, a => GrowthPaddedSuccessor.source I X T hA hB hC a
  | t + 1, _, a => GrowthPaddedStepRows.source
      (build I X T hA hB hC t (by omega)) (by omega) (by omega) a

def anchor : (t : ℕ) → (ht : t + 2 ≤ A.card) → Catalogue X (t + 2) → Catalogue X 1
  | 0, _, a => GrowthPaddedSuccessor.baseAnchor X a
  | t + 1, _, a =>
    let P := build I X T hA hB hC t (by omega)
    P.birth (Nat.le_succ (t + 2)) (state X a) (state_admitted X a) (state_proper X a)

def ceiling (t : ℕ) : ExtOrd := CanonicalFieldLayer.ceiling (t + 2)
  (Field I.right.scheme I.left.scheme)

theorem owner_index (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2)) :
    (build I X T hA hB hC t ht).carrier.cell (owner I X T hA hB hC t ht a) = (A, t + 2) := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.leaf_index I X T hA hB hC a
  | succ _ => exact (GrowthPaddedStepRows.controller _ _ a).2

theorem owner_row (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (d : (build I X T hA hB hC t ht).carrier.below
      ((build I X T hA hB hC t ht).carrier.cell (owner I X T hA hB hC t ht a))) :
    (build I X T hA hB hC t ht).rows.E (owner I X T hA hB hC t ht a) d =
      source I X T hA hB hC t ht a d.1 := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.leaf_row I X T hA hB hC a d
  | succ _ => exact ScopedSourcePrefixLayer.Data.row_new _ _ d

theorem anchor_ranks (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (f : Field I.right.scheme I.left.scheme) :
    RelativeLadderLayer.ranks (fields X 1) (anchor I X T hA hB hC t ht a) f =
      LadderScalarRendering.fieldRank (fields X (t + 2) a) f := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.baseAnchor_ranks X a f
  | succ t =>
    let P := build I X T hA hB hC t (by omega)
    exact (P.birth_ranks (Nat.le_succ (t + 2)) (state X a)
      (state_admitted X a) (state_proper X a) f).trans
      (by dsimp only [GrowthPaddedSuccessor.cat]; rw [state_profile])

theorem source_base (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (d : Cell (base I X T hA hB hC)) :
    source I X T hA hB hC t ht a ((build I X T hA hB hC t ht).baseMap d) =
      RelativeLadderLayer.renderWith I.boundary (by omega : 0 < A.card)
        (field I) (fields X 1) (anchor I X T hA hB hC t ht a)
        (fields X (t + 2) a) (ceiling I t) d := by
  cases t with
  | zero => exact LadderWeightedSuccessor.Input.source_old _ a d
  | succ t =>
    let P := build I X T hA hB hC t (by omega)
    have he := P.render_base (Nat.le_succ (t + 2)) (state X a) (state_admitted X a)
      (state_proper X a) (G := GrowthPaddedStepRows.grid P) (H := GrowthPaddedStepRows.ceiling P)
      (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ _))
      ((PairedSlotComparison.sourceGrid_visible
        (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ _))
      (fun f => by dsimp only [GrowthPaddedSuccessor.cat]; rw [state_profile]; exact anchor_bound X a f) d
    refine (PaddedTower.step_source_old P (by omega) ht a (P.baseMap d)).trans ?_
    simpa only [PaddedTower.selected, GrowthPaddedSuccessor.cat, anchor, state_profile, ceiling] using he

theorem source_lawful (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2)) :
    RespectsSemanticsBelow (build I X T hA hB hC t ht).rows (A, t + 2)
      (fun d => source I X T hA hB hC t ht a d.1) := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.source_lawful I X T hA hB hC a
  | succ _ => exact GrowthPaddedStepRows.source_lawful _ _ _ a

theorem source_supported (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (d : Cell (build I X T hA hB hC t ht).carrier) :
    OrbitPrefixSupport.Supported (t + 2)
      (RecursiveRungRendering.grid (Field I.right.scheme I.left.scheme) (t + 2) : Set ExtOrd)
      (fields X (t + 2) a) (source I X T hA hB hC t ht a d) := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.source_supported I X T hA hB hC a d
  | succ _ => exact GrowthPaddedStepRows.source_supported _ _ _ a d

theorem source_prefix (t : ℕ) (ht : t + 2 ≤ A.card) (a b : Catalogue X (t + 2)) {h : ExtOrd}
    (hh : h ∈ RecursiveRungRendering.grid (Field I.right.scheme I.left.scheme) (t + 2))
    (hab : SourcePrefixRows.Agree (fields X (t + 2) a) (fields X (t + 2) b) h)
    (d : Cell (build I X T hA hB hC t ht).carrier) :
    min (source I X T hA hB hC t ht a d) h = min (source I X T hA hB hC t ht b d) h := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.source_prefix I X T hA hB hC a b hh hab d
  | succ _ => exact GrowthPaddedStepRows.source_agreement _ _ _ a b hh hab d

theorem owner_exhaustive (t : ℕ) (ht : t + 2 ≤ A.card)
    (c : Cell (build I X T hA hB hC t ht).carrier)
    (hc : (build I X T hA hB hC t ht).carrier.cell c = (A, t + 2)) :
    ∃ a, c = owner I X T hA hB hC t ht a := by
  cases t with
  | zero =>
    change (GrowthPaddedSuccessor.carrier I X T hA hB hC).cell c = (A, 2) at hc
    rcases GrowthPaddedSuccessor.cell_cases I X T hA hB hC c with ⟨x, hx⟩ | ⟨a, ha⟩
    · rw [hx, SourceLayerCarrier.cell_toCell] at hc
      exact False.elim ((GrowthPaddedSuccessor.input I X T hA hB hC).separation x (hc.symm ▸ GradedLe.refl _))
    · exact ⟨a, ha⟩
  | succ t =>
    let P := build I X T hA hB hC t (by omega)
    let ctrl : SourcePrefixLayer.Controller (GrowthPaddedStepRows.carrier P (by omega)) (t + 3) := ⟨c, hc⟩
    exact ⟨GrowthPaddedStepRows.member P (by omega) (by omega) ctrl,
      congrArg Subtype.val ((SeparatedSourceLayerCarrier.controllerEquiv P.carrier
        (Catalogue X (t + 3)) (t + 3) (Nat.succ_pos _) (by omega)
        (P.separated (by omega))).apply_symm_apply ctrl).symm⟩

theorem source_diagonal (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2)) :
    source I X T hA hB hC t ht a (owner I X T hA hB hC t ht a) = ceiling I t := by
  cases t with
  | zero => exact GrowthPaddedSuccessor.source_ceiling I X T hA hB hC a
  | succ _ => exact ScopedSourcePrefixLayer.Data.profile_diagonal _ _

theorem source_original (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (d : Cell I.boundary) :
    source I X T hA hB hC t ht a ((build I X T hA hB hC t ht).baseMap
      (RelativeLadderLayer.old I.boundary (by omega : 0 < A.card) d)) =
        fields X (t + 2) a (field I d) :=
  (source_base I X T hA hB hC t ht a _).trans
    (RelativeLadderLayer.renderWith_old _ _ _ _ _ _ _ (anchor_ranks I X T hA hB hC t ht a) d)

abbrev ladder (t : ℕ) (ht : t + 2 ≤ A.card)
    (v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :=
  (build I X T hA hB hC t ht).baseMap (RelativeLadderLayer.added I.boundary (by omega : 0 < A.card) v)

theorem ladder_index (t : ℕ) (ht : t + 2 ≤ A.card)
    (v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :
    (build I X T hA hB hC t ht).carrier.cell (ladder I X T hA hB hC t ht v) = (A, 1) := by
  rw [ladder, PaddedTower.Layer.base_index, RelativeLadderLayer.added_index]

theorem source_ladder (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)) :
    source I X T hA hB hC t ht a (ladder I X T hA hB hC t ht v) =
      SupportLadderRows.image (RelativeLadderLayer.ranks (fields X 1))
        (anchor I X T hA hB hC t ht a)
        (LadderScalarRendering.level (LadderScalarRendering.values (fields X (t + 2) a))
          (ceiling I t)) v := by
  rw [ladder, source_base]
  change RelativeLadderLayer.image _ _ _ _ _ _ (RelativeLadderLayer.added _ _ v) = _
  rw [RelativeLadderLayer.image, RelativeLadderLayer.rankIndex_added]; rfl

theorem source_shadow_sup (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (f : Field I.right.scheme I.left.scheme) :
    (Finset.univ : Finset (Catalogue X 1)).sup (fun b =>
      source I X T hA hB hC t ht a
        (ladder I X T hA hB hC t ht (SupportLadderRows.shadow b f))) = fields X (t + 2) a f := by
  classical
  have he := SupportLadderRows.readout_image
    (H := RelativeLadderLayer.rungs (X := Field I.right.scheme I.left.scheme))
    (fun b f => le_of_lt (RelativeLadderLayer.rank_bound (fields X 1) b f))
    (anchor I X T hA hB hC t ht a)
    (LadderScalarRendering.level_mono (LadderScalarRendering.values_bound (anchor_bound X a))) f
  simp only [SupportLadderRows.readout] at he
  rw [show Fintype.ofFinite (Catalogue X 1) = (inferInstance : Fintype (Catalogue X 1))
    from Subsingleton.elim _ _] at he
  simp only [source_ladder]; unfold ceiling
  rw [he, anchor_ranks, LadderScalarRendering.field_readback]

theorem source_spare (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2)) :
    source I X T hA hB hC t ht a (ladder I X T hA hB hC t ht
      (SupportLadderRows.leaf (Nat.succ_pos _) (anchor I X T hA hB hC t ht a))) = ceiling I t := by
  rw [source_ladder, SupportLadderRows.image]
  have he := SupportLadderRows.index_leaf
    (H := RelativeLadderLayer.rungs (X := Field I.right.scheme I.left.scheme))
    (profile := RelativeLadderLayer.ranks (fields X 1))
    (by unfold RelativeLadderLayer.rungs; omega)
    (anchor I X T hA hB hC t ht a) (anchor I X T hA hB hC t ht a)
  rw [FiniteProfileControllers.cut_refl] at he
  exact (congrArg (LadderScalarRendering.level
    (LadderScalarRendering.values (fields X (t + 2) a)) (ceiling I t)) he).trans
    (ite_eq_left (lt_of_le_of_lt (LadderScalarRendering.values_card_le (fields X (t + 2) a))
      (Nat.lt_succ_self _)))

theorem source_ceiling_at (t : ℕ) (ht : t + 2 ≤ A.card) (a : Catalogue X (t + 2))
    (i : ℕ) (hi : 1 ≤ i) (hit : i ≤ t + 2) :
    ∃ c : Cell (build I X T hA hB hC t ht).carrier,
      (build I X T hA hB hC t ht).carrier.cell c = (A, i) ∧
        source I X T hA hB hC t ht a c = ceiling I t := by
  by_cases he : i = t + 2
  · subst i; exact ⟨_, owner_index I X T hA hB hC t ht a, source_diagonal I X T hA hB hC t ht a⟩
  cases t with
  | zero =>
    obtain rfl : i = 1 := by omega
    exact ⟨_, ladder_index I X T hA hB hC 0 ht _, source_spare I X T hA hB hC 0 ht a⟩
  | succ t =>
    let P := build I X T hA hB hC t (by omega)
    obtain ⟨c, hc, hv⟩ := P.ceiling_at (Nat.le_succ (t + 2))
      (state X a) (state_admitted X a) (state_proper X a)
      (G := GrowthPaddedStepRows.grid P) (H := GrowthPaddedStepRows.ceiling P)
      (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ _))
      ((PairedSlotComparison.sourceGrid_visible
        (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ _))
      (fun f => by dsimp only [GrowthPaddedSuccessor.cat]; rw [state_profile]; exact anchor_bound X a f)
      i hi (by omega)
    exact ⟨GrowthPaddedStepRows.old P (by omega) c,
      (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans hc,
      (PaddedTower.step_source_old P (by omega) ht a c).trans hv⟩

end
end GrowthPaddedNativeRows
end TowerInstall
end VaughtConjecture.Knight
