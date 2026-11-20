/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorAdmission
public import VaughtConjecture.Knight.CappedDonorNormalization
public import VaughtConjecture.Knight.CappedDonorLowHighNormalization
public import VaughtConjecture.Knight.TerminalProfile

@[expose] public section

namespace VaughtConjecture.Knight.CappedDonor.Ref

open Transform Value ExtOrd

noncomputable section

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

variable (R) in
/-- **Ordinary admission at the threshold cutoff**: the complete source vectors of synchronized
admissible states at cutoff `N` whose gate is `N`-visible. -/
def Admitted (a : Field P C → ExtOrd) : Prop :=
  ∃ st : R.State N, R.Admissible st ∧ Synchronized st ∧ SelfVis N st.gate ∧ st.sourceProfile = a

theorem one_le_N (R : Ref I nP N J P C) : 1 ≤ N := by
  have := R.arity_lt
  omega

/-- Canonical normalization preserves admission. -/
theorem Admitted.normalize {a : Field P C → ExtOrd} (h : R.Admitted a) :
    R.Admitted (PairedSlotEncoding.normalize N a) := by
  obtain ⟨st, hst, hs, hg, rfl⟩ := h
  exact ⟨normalizeState st, normalizeState_admissible R.one_le_N hst,
    normalizeState_synchronized R.one_le_N hs, selfVis_map st.encoder_witness le_rfl hg,
    funext fun f => sourceProfile_normalizeState st f⟩

/-- Positive `N`-visible caps preserve admission. -/
theorem Admitted.cap {a : Field P C → ExtOrd} (h : R.Admitted a) {β : ExtOrd}
    (hβ : SelfVis N β) (hβbot : β ≠ ⊥) : R.Admitted (fun f => min (a f) β) := by
  obtain ⟨st, hst, hs, hg, rfl⟩ := h
  exact ⟨mapState (fun x => min x β) st,
    hst.map (capWitness hβ hβbot) (min_le_left _ _) R.one_le_N (capWitness_reflects_bottom hβbot),
    hs.map (capWitness hβ hβbot) R.one_le_N, selfVis_map (capWitness hβ hβbot) le_rfl hg,
    funext fun f => sourceProfile_map _ st f⟩

variable (R) in
/-- The zero vector is admitted (the all-bottom state, gate off). -/
theorem Admitted.zero : R.Admitted (fun _ => ⊥) :=
  ⟨zeroState R N, zeroState_admissible N, zeroState_synchronized N,
    extVisibilityReplace_bot _ _, funext (zeroState_sourceProfile N)⟩

/-- **Private-repair closure with complete-field receipts.**  A lawful private prescription
agreeing with an admitted source below a positive `N`-visible cap is installed exactly in an
admitted source that keeps every complete-field `γ`-cap: present fields numerically, future
fields persistently, the gate literally. -/
theorem Admitted.private_repair {a : Field P C → ExtOrd} (h : R.Admitted a)
    {v₁ : C.scheme.below (effC J N) → ExtOrd} (hv₁ : RespectsSemanticsBelow C.rows (effC J N) v₁)
    {γ : ExtOrd} (hγ : SelfVis N γ) (hγbot : γ ≠ ⊥)
    (hagree : ∀ d, min (v₁ d) γ = min (a (.priv d.1)) γ) :
    ∃ b : Field P C → ExtOrd, R.Admitted b ∧
      (∀ d : C.scheme.below (effC J N), b (.priv d.1) = v₁ d) ∧
      ∀ f, min (b f) γ = min (a f) γ := by
  obtain ⟨st, hst, hs, hg, rfl⟩ := h
  have hγ' : SelfVis (effC J N).2 γ := selfVis_mono hγ (min_le_left _ _)
  have hagree' : ∀ d, min (v₁ d) γ = min (st.v d) γ := fun d => by
    rw [hagree d, st.sourceProfile_of_present (f := .priv d.1) ((present_priv_iff N d.1).mp d.2)]
    rfl
  obtain ⟨st₁, hst₁, hv, hu, hrec, hlit⟩ := R.exists_private_lift hst hv₁ hγ' hagree'
  obtain ⟨hgate, -, -⟩ := hlit hγbot
  have hrec' := resync_capReceipts (R := R) hs hγ' hu (fun d => by simp_all) hrec
  refine ⟨(resync st₁).sourceProfile,
    ⟨resync st₁, hst₁.resync, resync_synchronized hst₁, ?_, rfl⟩, ?_, ?_⟩
  · change SelfVis N st₁.gate
    rw [hgate]
    exact hg
  · intro d
    rw [State.sourceProfile_of_present _ ((present_priv_iff N d.1).mp d.2)]
    change st₁.v ⟨d.1, _⟩ = v₁ d
    tauto
  · intro f
    by_cases hf : f.grade ≤ N
    · rw [State.sourceProfile_of_present _ hf, State.sourceProfile_of_present _ hf]
      cases f with
      | req d => exact hu _
      | priv d =>
          change min (st₁.v _) γ = min (st.v _) γ
          grind
      | gate =>
          tauto
    · rw [State.sourceProfile_of_future _ hf, State.sourceProfile_of_future _ hf]
      exact (capReceipts_iff γ st (resync st₁)).mp hrec' f

/-- The state with its gate switched off. -/
def gateOff {j : ℕ} (st : R.State j) : R.State j := { st with gate := ⊥ }

/-- Switching the gate off preserves admissibility: the support guard and the relation have a
positive-gate antecedent, and nothing else reads the gate. -/
theorem Admissible.gateOff {j : ℕ} {st : R.State j} (hst : R.Admissible st) :
    R.Admissible (Ref.gateOff st) where
  u_respects := hst.u_respects
  v_respects := hst.v_respects
  face := hst.face
  gate_vis := extVisibilityReplace_bot _ _
  shadowP_vis := hst.shadowP_vis
  shadowC_vis := hst.shadowC_vis
  shadowP_iff := hst.shadowP_iff
  shadowC_iff := hst.shadowC_iff
  support hg := absurd rfl hg
  relation _ hg := absurd rfl hg

/-- Switching the gate off preserves synchronization. -/
theorem Synchronized.gateOff {j : ℕ} (hj : 1 ≤ j) {st : R.State j} (hs : Synchronized st) :
    Synchronized (Ref.gateOff st) := by
  intro f
  cases f with
  | gate =>
      change (⊥ : ExtOrd) = extVisibilityReplace ((Ref.gateOff st).sourceProfile .gate) 1 1
      rw [State.sourceProfile_of_present _ (hj)]
      rfl
  | req d =>
      change st.shadowP d = _
      have h := hs (.req d)
      assumption
  | priv d =>
      change st.shadowC d = _
      have h := hs (.priv d)
      assumption

/-- Terminal insertion gives a proper canonical encoding with exact readback. -/
theorem Admitted.exists_terminal {a : Field P C → ExtOrd} (h : R.Admitted a)
    (hh : Ordinal.{0}) :
    ∃ b₀ : Field P C → ExtOrd, R.Admitted b₀ ∧ (∀ f, b₀ f ≠ ⊤) ∧
      (∀ f, min (b₀ f) (ofOrd hh) = min (a f) (ofOrd hh)) ∧ (∀ f, a f ≠ ⊤ → b₀ f = a f) ∧
      R.Admitted (PairedSlotEncoding.normalize N b₀) ∧
      PairedSlotEncoding.normalize N b₀ ∈ CanonicalPairedProfiles.inventory (Field P C) N ∧
      ∃ δ : ExtOrd → ExtOrd, Witness (gTop N) δ ∧
        ∀ f, δ (PairedSlotEncoding.normalize N b₀ f) = a f := by
  let b := TerminalProfile.clipped a hh N
  have hb : R.Admitted b := h.cap (TerminalProfile.cap_visible a hh N) (ofOrd_ne_bot _)
  refine ⟨b, hb, TerminalProfile.clipped_proper a hh N, TerminalProfile.clipped_prefix a hh N,
    TerminalProfile.clipped_literal a hh N, hb.normalize,
    CanonicalPairedProfiles.normalize_mem_inventory _ _ (TerminalProfile.clipped_proper a hh N),
    TerminalProfile.decoder a hh N, TerminalProfile.decoder_witness a hh N,
    TerminalProfile.decoder_read a hh N⟩

variable (R) in
/-- The canonical admitted catalogue: proper canonical fixed points that are admitted. -/
def Catalogue : Set (Field P C → ExtOrd) :=
  {a | a ∈ CanonicalPairedProfiles.inventory (Field P C) N ∧ R.Admitted a}

variable (R) in
theorem catalogue_finite : (R.Catalogue).Finite :=
  (CanonicalPairedProfiles.inventory_finite (Field P C) N).subset fun _ h => h.1

/-- The normalization of a proper admitted source is in the catalogue. -/
theorem Admitted.normalize_mem_catalogue {a : Field P C → ExtOrd} (h : R.Admitted a)
    (hproper : ∀ f, a f ≠ ⊤) : PairedSlotEncoding.normalize N a ∈ R.Catalogue :=
  ⟨CanonicalPairedProfiles.normalize_mem_inventory _ _ hproper, h.normalize⟩

end

end VaughtConjecture.Knight.CappedDonor.Ref
