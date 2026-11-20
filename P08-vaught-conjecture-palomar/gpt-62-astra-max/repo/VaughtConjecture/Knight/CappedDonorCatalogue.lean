/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingCatalogueRanks

public import VaughtConjecture.Knight.CappedDonorRetarget
public import VaughtConjecture.Knight.CappedDonorRelease
public import VaughtConjecture.Knight.CappedDonorNormalization
public import VaughtConjecture.Knight.TerminalBlock
public import VaughtConjecture.Knight.CanonicalPairedProfiles

/-! # Whole-inventory admission at the final receiving threshold

Here the context has arity exactly `N`. All request and private fields are present, so the
catalogue can be defined on the labels themselves. No shadow fields or synchronization
receipts are needed. Only the selected equation and the activity of the private cap matter
when the gate is on.
-/

@[expose] public section

namespace VaughtConjecture.Knight

/-- Compatible prescriptions at two caps can be met by using the witness at the larger cap. -/
theorem CappedEq.combine {X α : Type*} [LinearOrder α] {p q : X → α} {c h : α}
    {Q : (X → α) → Prop} (hpq : CappedEq p q (min c h))
    (u : ∃ r, Q r ∧ CappedEq r p c) (v : ∃ r, Q r ∧ CappedEq r q h) :
    ∃ r, Q r ∧ CappedEq r p c ∧ CappedEq r q h := by
  rcases le_total c h with hl | hl
  · rw [min_eq_left hl] at hpq
    obtain ⟨r,hr,he⟩ := v
    exact ⟨r,hr,fun d => (he.mono hl d).trans (hpq d).symm,he⟩
  · rw [min_eq_right hl] at hpq
    obtain ⟨r,hr,he⟩ := u
    exact ⟨r,hr,he,fun d => (he.mono hl d).trans (hpq d)⟩

end VaughtConjecture.Knight

namespace VaughtConjecture.Knight.CappedDonor.Ref

open Transform Value ExtOrd
noncomputable section

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

theorem one_le_N (R : Ref I nP N J P C) : 1 ≤ N := by
  have := R.arity_lt
  omega

variable {C : SemScheme N} {R : Ref I nP N N P C}

abbrev low (R : Ref I nP N N P C) (v : Cell C.scheme → ExtOrd) (d : R.Low) := v d.1

/-- Combine the two literal sections and the gate into the complete field inventory. -/
def pack (u : Cell P.scheme → ExtOrd) (v : Cell C.scheme → ExtOrd) (g : ExtOrd) : Field P C → ExtOrd
  | .req d => u d
  | .priv d => v d
  | .gate => g

variable (R) in
structure Admitted (a : Field P C → ExtOrd) : Prop where
  donor : RespectsSemantics P.rows (a ∘ Field.req)
  priv : RespectsSemantics C.rows (a ∘ Field.priv)
  face : ∀ d : P.scheme.below (R.A,R.KA), a (.req d.1) = a (.priv (R.face d).1)
  gate : SelfVis N (a .gate)
  active : a .gate ≠ ⊥ → a (.priv R.cap) ≠ ⊥ → R.Active (R.low (a ∘ Field.priv))
  relation : a .gate ≠ ⊥ → a (.priv R.cap) ≠ ⊥ → ∀ d,
    min (a (.req d)) (R.cut (R.low (a ∘ Field.priv))) = R.sel (R.low (a ∘ Field.priv)) d

private theorem map_full {n : ℕ} {S : SemScheme n} {p : Cell S.scheme → ExtOrd}
    (hp : RespectsSemantics S.rows p) (hn : n ≤ N) {σ} (hw : Witness (gTop N) σ)
    (hb : ∀ x, σ x = ⊥ → x = ⊥) : RespectsSemantics S.rows (σ ∘ p) :=
  (FiniteOrbitEmbedding.map_respects (hp.toBelow (Finset.univ,n))
    (fun d => d.2.2.trans hn) hw hb).toRespects (fun d => ⟨Finset.subset_univ _,gradeC_le d⟩)

theorem Admitted.map {a} (h : R.Admitted a) {σ} (hw : Witness (gTop N) σ)
    (hb : ∀ x, σ x = ⊥ → x = ⊥) : R.Admitted (σ ∘ a) := by
  have hv := map_full h.priv le_rfl hw hb
  have pos := map_ne_bot_iff hw hb
  refine ⟨map_full h.donor R.arity_lt.le hw hb,hv,fun d => congrArg σ (h.face d),
    selfVis_map hw le_rfl h.gate,?_,?_⟩
  · intro hg hc
    have H := h.active ((pos _).mp hg) ((pos _).mp hc)
    exact ⟨hv.toBelow _,hc,fun i => (pos _).mpr (H.ref_pos i),fun d hd => (congrArg σ (H.face_bot d hd)).trans hw.bot⟩
  · intro hg hc d
    change min (σ _) (R.cut (fun e => σ (a (.priv e.1)))) = R.sel (fun e => σ (a (.priv e.1))) d
    rw [cut_map hw le_rfl,sel_map hw le_rfl,← hw.mono.map_min]
    exact congrArg σ (h.relation ((pos _).mp hg) ((pos _).mp hc) d)

theorem Admitted.normalize {a} (h : R.Admitted a) : R.Admitted (PairedSlotEncoding.normalize N a) := by
  simpa only [Function.comp_def,PairedSlotIncoming.encoder_profile] using h.map
    (PairedSlotIncoming.encoder_witness N (PairedSlotEncoding.values a)) (PairedSlotIncoming.encoder_reflects_bottom _ _)

theorem Admitted.cap {a} (h : R.Admitted a) {β} (hv : SelfVis N β) (hb : β ≠ ⊥) :
    R.Admitted (fun f => min (a f) β) := h.map (capWitness hv hb) (capWitness_reflects_bottom hb)

variable (R) in
theorem Admitted.zero : R.Admitted (fun _ => ⊥) := ⟨RespectsSemantics.bot _, RespectsSemantics.bot _,
  fun _ => rfl,selfVis_bot N,fun h => (h rfl).elim,fun h => (h rfl).elim⟩

/-- Bountifulness installs the whole common face into a full lawful request section. -/
private theorem install {u : Cell P.scheme → ExtOrd} {v : Cell C.scheme → ExtOrd}
    (hu : RespectsSemantics P.rows u) (hv : RespectsSemantics C.rows v) {γ} (hγ : SelfVis N γ)
    (hc : ∀ e : P.scheme.below (R.A,R.KA), min (u e.1) γ = min (v (R.face e).1) γ) :
    ∃ w, (RespectsSemantics P.rows w ∧ ∀ e : P.scheme.below (R.A,R.KA), w e.1 = v (R.face e).1) ∧
      CappedEq w u γ := by
  obtain ⟨w,hw,hpre,hread⟩ := R.exists_installP (j := N) (hu.toBelow _) (hv.toBelow _)
    (R.selfVis_effP_of_N N hγ) (fun e _ => hc e)
  let hall := fun d : Cell P.scheme => (present_req_iff N d).mpr ((gradeP_le d).trans R.arity_lt.le)
  exact ⟨_,⟨hw.toRespects hall,fun e => hread e ((gradeP_le e.1).trans R.arity_lt.le)⟩,fun d => hpre ⟨d,hall d⟩⟩

/-- Repair even at bottom: switch the gate off there. At a positive cap the active private
pattern is unchanged and the selector and the old request agree below the smaller cut. -/
theorem Admitted.private_repair {a} (h : R.Admitted a) {v₁ : C.ClippedCells N → ExtOrd}
    (hv₁ : C.rows.Lawful v₁) {γ} (hγ : SelfVis N γ)
    (he : ∀ d, min (v₁ d) γ = min (a (.priv d.1)) γ) :
    ∃ b, R.Admitted b ∧ (∀ d, b (.priv d.1) = v₁ d) ∧ CappedEq b a γ := by
  let v := fun d => v₁ (privCell d (gradeC_le d))
  have hv : RespectsSemantics C.rows v := hv₁.toRespects (fun d => (present_priv_iff N d).mpr (gradeC_le d))
  have hp (d) : min (v d) γ = min (a (.priv d)) γ := he _
  have old := install (R := R) h.donor hv hγ (fun e =>
    (congrArg (min · γ) (h.face e)).trans (hp _).symm)
  by_cases hz : γ = ⊥
  · obtain ⟨w,⟨hw,hf⟩,_⟩ := old
    exact ⟨pack w v ⊥,⟨hw,hv,hf,selfVis_bot N,fun hn => (hn rfl).elim,fun hn => (hn rfl).elim⟩,
      fun _ => rfl,fun _ => by simp [hz]⟩
  have pat := SharpWitnessComposition.bottom_pattern_of_cap_agreement hz hp
  have act (hg : a .gate ≠ ⊥) (hc : v R.cap ≠ ⊥) : R.Active (R.low v) := by
    have H := h.active hg (fun x => hc ((pat _).mpr x))
    exact ⟨hv.toBelow _,hc,fun i hh => H.ref_pos i ((pat _).mp hh),fun d hd => (pat _).mpr (H.face_bot d hd)⟩
  let β := R.cut (R.low v)
  let sel := R.sel (R.low v)
  suffices ∃ w, (RespectsSemantics P.rows w ∧ ∀ e : P.scheme.below (R.A,R.KA), w e.1 = v (R.face e).1) ∧
      CappedEq w (a ∘ Field.req) γ ∧ (a .gate ≠ ⊥ → v R.cap ≠ ⊥ → ∀ d, min (w d) β = sel d) by
    obtain ⟨w,⟨hw,hf⟩,hpre,hrel⟩ := this
    refine ⟨pack w v (a .gate),⟨hw,hv,hf,h.gate,act,hrel⟩,fun _ => rfl,?_⟩
    rintro (d|d|_) <;> first | exact hpre d | exact hp d | rfl
  by_cases on : a .gate ≠ ⊥ ∧ v R.cap ≠ ⊥
  · have H := act on.1 on.2
    have hvis := R.selfVis_cut (Active.selfVis_cap R H)
    have hs := install (R := R) (Active.sel_respects R H) hv hvis (fun d => by
      rw [Active.sel_face R H d,min_assoc,min_self]; rfl)
    let u := R.low (a ∘ Field.priv)
    have heq : (fun e => min (R.low v e) γ) = (fun e => min (u e) γ) := funext fun _ => hp _
    have hcut : min β γ = min (R.cut u) γ := by rw [← R.cut_min hγ,← R.cut_min hγ,heq]
    have hsel d : min (sel d) γ = min (R.sel u d) γ := by rw [← R.sel_min hγ,← R.sel_min hγ,heq]
    have hag : CappedEq (a ∘ Field.req) sel (min γ β) := by
      intro d
      change min (a (.req d)) _ = _
      rw [min_comm γ β, hcut, ← min_assoc,h.relation on.1 (fun h0 => on.2 ((pat _).mpr h0)),← hsel,
        ← hcut,← min_assoc,min_eq_left (R.sel_le_cut _ _)]
    obtain ⟨w,hw,hpre,hrel⟩ := hag.combine old hs
    exact ⟨w,hw,hpre,fun _ _ d => (hrel d).trans (min_eq_left (R.sel_le_cut _ _))⟩
  · obtain ⟨w,hw,heq⟩ := old
    exact ⟨w,hw,heq,fun hg hc => (on ⟨hg,hc⟩).elim⟩

def profiles (R : Ref I nP N N P C) : ProfileCatalogue.Family (Field P C → ExtOrd) (Field P C) N where
  profile := id
  admitted := R.Admitted
  realize := fun {s} _ hs h => ⟨_, (hs.cap (TerminalProfile.visible s N h) (ofOrd_ne_bot _)).normalize, rfl⟩

/-! ## The finite canonical catalogue -/

variable (R) in
/-- The canonical admitted catalogue: proper canonical fixed points that are admitted. -/
def Catalogue : Set (Field P C → ExtOrd) :=
  {a | a ∈ CanonicalPairedProfiles.inventory (Field P C) N ∧ R.Admitted a}

variable (R) in
theorem catalogue_finite : (R.Catalogue).Finite :=
  (CanonicalPairedProfiles.inventory_finite (Field P C) N).subset fun _ h => h.1

/-- The normalization of a proper admitted source is in the catalogue. -/
theorem Admitted.normalize_mem_catalogue {a} (h : R.Admitted a)
    (hproper : ∀ f, a f ≠ ⊤) : PairedSlotEncoding.normalize N a ∈ R.Catalogue :=
  ⟨CanonicalPairedProfiles.normalize_mem_inventory _ _ hproper, h.normalize⟩

theorem Admitted.display {a : Field P C → ExtOrd} (ha : R.Admitted a) :
    ∃ (b : ↥R.Catalogue) (δ : ExtOrd → ExtOrd), Witness (gTop N) δ ∧
      (∀ f, δ (b.val f) = a f) ∧ ∀ f, δ (b.val f) = ⊥ ↔ b.val f = ⊥ := by
  obtain ⟨z,hz,hcan,δ,hw,hr,hb,_⟩ := ProfileCatalogue.supported_decoder R.profiles R.one_le_N ha
  exact ⟨⟨z,hcan,hz⟩,δ,hw,hr,fun f => ⟨hb f, fun he => he ▸ hw.bot⟩⟩

end
end VaughtConjecture.Knight.CappedDonor.Ref
