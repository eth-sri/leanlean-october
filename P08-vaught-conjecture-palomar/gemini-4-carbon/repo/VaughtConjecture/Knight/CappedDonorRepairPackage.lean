/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorCatalogue
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.PairedSlotComparison
public import VaughtConjecture.Knight.ReceivingCatalogueRanks

/-! # The scalar repair package of the ordinary final catalogue

The two scalar producers consumed by the physical final-grade layer's decoding
(`FinalGateDecoding.decode_source_prefix` on the integration branch, and its selected-display
decoder), composed from the existing private fibre, normalization, terminal insertion and the
supported inverse — none of whose machinery is re-proved here.

* **`positive_cap_repair`**: from a canonical admitted source `a` (a member of the fixed
  `Catalogue`) and a lawful **proper** private prescription agreeing with `a`'s private part at a
  source-grid endpoint `grid N B`: an admitted proper complete vector `b₀` retaining the
  prescription literally, with complete-field prefix agreement at the endpoint; its canonical
  normalization, a member of the **same** catalogue, with the same capped prefix agreement; and
  the actual supported inverse `κ` — a witness through `N` decoding `b₀` exactly from its
  normalization, fixing every unused grid endpoint below the cut (`fix_sourceGrid` gives the
  `sourceGrid` form) and every supported orbit of `a` below the cut, and reaching the cut.
* **`bottom_supply`**: independent bottom-cap private supply — from the zero admitted state,
  install an arbitrary lawful private prescription, **literal top included**, with the gate off;
  terminal insertion then gives a member of the catalogue with an exact decoder reading the
  installed prescription back.

Nothing here asserts a physical section, a display, admission of an arbitrary section or any
upward admission. -/

@[expose] public section

namespace VaughtConjecture.Knight.CappedDonor.Ref

open Transform Value ExtOrd
noncomputable section

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-- A witness fixing every grid endpoint below `B` fixes every source-grid value below the cut
`grid N B` (bottom included). -/
theorem fix_sourceGrid {κ : ExtOrd → ExtOrd} (hbot : κ ⊥ = ⊥) {B : ℕ}
    (hfix : ∀ b < B, κ (CanonicalPairedInverse.grid N b) = CanonicalPairedInverse.grid N b)
    (n : ℕ) : ∀ z ∈ PairedSlotComparison.sourceGrid N n, z < CanonicalPairedInverse.grid N B →
      κ z = z := by
  classical
  intro z hz hlt
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hbot
  · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hz
    refine hfix b ?_
    by_contra hle
    apply not_le.mpr hlt
    change ofOrd (Ordinal.omega0 * B + N) ≤ ofOrd (Ordinal.omega0 * b + N)
    exact ofOrd_le_ofOrd.mpr (add_le_add_left (omul_le_omul (not_lt.mp hle)) _)

/-- **Positive-cap repair through normalization and the supported inverse.** -/
theorem positive_cap_repair {a : Field P C → ExtOrd} (ha : a ∈ R.Catalogue)
    {v₁ : C.scheme.below (effC J N) → ExtOrd} (hv₁ : RespectsSemanticsBelow C.rows (effC J N) v₁)
    (hv₁p : ∀ d, v₁ d ≠ ⊤) {B : ℕ}
    (hagree : ∀ d, min (v₁ d) (CanonicalPairedInverse.grid N B) =
      min (a (.priv d.1)) (CanonicalPairedInverse.grid N B)) :
    ∃ b₀ : Field P C → ExtOrd, R.Admitted b₀ ∧ (∀ f, b₀ f ≠ ⊤) ∧
      (∀ d : C.scheme.below (effC J N), b₀ (.priv d.1) = v₁ d) ∧
      (∀ f, min (b₀ f) (CanonicalPairedInverse.grid N B) =
        min (a f) (CanonicalPairedInverse.grid N B)) ∧
      PairedSlotEncoding.normalize N b₀ ∈ R.Catalogue ∧
      (∀ f, min (PairedSlotEncoding.normalize N b₀ f) (CanonicalPairedInverse.grid N B) =
        min (a f) (CanonicalPairedInverse.grid N B)) ∧
      ∃ κ : ExtOrd → ExtOrd, Witness (gTop N) κ ∧
        (∀ f, κ (PairedSlotEncoding.normalize N b₀ f) = b₀ f) ∧
        (∀ b < B, κ (CanonicalPairedInverse.grid N b) = CanonicalPairedInverse.grid N b) ∧
        CanonicalPairedInverse.grid N B ≤ κ (CanonicalPairedInverse.grid N B) ∧
        ∀ f, a f < CanonicalPairedInverse.grid N B → ∀ k ≤ N, ∀ i ≤ k,
          κ (extVisibilityReplace (a f) k i) = extVisibilityReplace (a f) k i := by
  obtain ⟨hinv, hadm⟩ := ha
  have hgrid : SelfVis N (CanonicalPairedInverse.grid N B) :=
    CanonicalPairedInverse.grid_visible N B
  have hne : CanonicalPairedInverse.grid N B ≠ ⊥ := ofOrd_ne_bot _
  obtain ⟨b₁, hb₁, hpriv₁, hrec₁⟩ := hadm.private_repair hv₁ hgrid hne hagree
  obtain ⟨b₀, hb₀, hprop, hpre, hlit, -, -, -⟩ :=
    hb₁.exists_terminal (Ordinal.omega0 * B + N)
  have hpre' : ∀ f, min (b₀ f) (CanonicalPairedInverse.grid N B) =
      min (a f) (CanonicalPairedInverse.grid N B) := fun f => (hpre f).trans (hrec₁ f)
  have hag : ∀ f, min (a f) (CanonicalPairedInverse.grid N B) =
      min (b₀ f) (CanonicalPairedInverse.grid N B) := fun f => (hpre' f).symm
  refine ⟨b₀, hb₀, hprop, fun d => ?_, hpre', hb₀.normalize_mem_catalogue hprop, fun f => ?_, ?_⟩
  · rw [hlit _ (by rw [hpriv₁ d]; exact hv₁p d), hpriv₁ d]
  · exact CanonicalPairedProfiles.normalize_cap (Field P C) N hinv hag f
  · exact CanonicalPairedInverse.exists_supported_inverse hinv hprop hag

/-- **Independent bottom-cap private supply, with a supported decoder.**  From the zero
admitted state, an arbitrary lawful private prescription — literal top included — is installed
with the gate off; terminal insertion gives a member of the catalogue with an exact decoder
reading it back, every output of which is supported by the installed vector (bottom and top
allowed). -/
theorem bottom_supply' {v₁ : C.scheme.below (effC J N) → ExtOrd}
    (hv₁ : RespectsSemanticsBelow C.rows (effC J N) v₁) :
    ∃ a : Field P C → ExtOrd, R.Admitted a ∧
      (∀ d : C.scheme.below (effC J N), a (.priv d.1) = v₁ d) ∧ a .gate = ⊥ ∧
      ∃ b₀ : Field P C → ExtOrd, R.Admitted b₀ ∧ (∀ f, b₀ f ≠ ⊤) ∧
        PairedSlotEncoding.normalize N b₀ ∈ R.Catalogue ∧
        ∃ δ : ExtOrd → ExtOrd, Witness (gTop N) δ ∧
          (∀ f, δ (PairedSlotEncoding.normalize N b₀ f) = a f) ∧
          ∀ x, OrbitPrefixSupport.Supported N ({⊤} : Set ExtOrd) a (δ x) := by
  obtain ⟨st₁, hst₁, hv, -, -, -⟩ := R.exists_private_lift (zeroState_admissible N) hv₁
    (selfVis_bot _) (fun d => by simp only [min_bot_right])
  let st₂ : R.State N := Ref.gateOff (resync st₁)
  have hadm : R.Admitted st₂.sourceProfile :=
    ⟨st₂, hst₁.resync.gateOff, (resync_synchronized hst₁).gateOff R.one_le_N,
      extVisibilityReplace_bot _ _, rfl⟩
  obtain ⟨b₀, hb₀, hprop, -, -, hnorm, hmem, δ, hδ, hread, hsupp⟩ := hadm.exists_terminal' 0
  refine ⟨st₂.sourceProfile, hadm, fun d => ?_, ?_, b₀, hb₀, hprop, ⟨hmem, hnorm⟩, δ, hδ, hread,
    hsupp⟩
  · rw [State.sourceProfile_of_present _ ((present_priv_iff N d.1).mp d.2)]
    change st₁.v ⟨d.1, _⟩ = v₁ d
    rw [hv]
    exact congrArg v₁ (Subtype.ext rfl)
  · rw [State.sourceProfile_of_present _ (show (Field.gate : Field P C).grade ≤ N from R.one_le_N)]
    rfl

/-- **Independent bottom-cap private supply** (the decoder's support conjunct dropped). -/
theorem bottom_supply {v₁ : C.scheme.below (effC J N) → ExtOrd}
    (hv₁ : RespectsSemanticsBelow C.rows (effC J N) v₁) :
    ∃ a : Field P C → ExtOrd, R.Admitted a ∧
      (∀ d : C.scheme.below (effC J N), a (.priv d.1) = v₁ d) ∧ a .gate = ⊥ ∧
      ∃ b₀ : Field P C → ExtOrd, R.Admitted b₀ ∧ (∀ f, b₀ f ≠ ⊤) ∧
        PairedSlotEncoding.normalize N b₀ ∈ R.Catalogue ∧
        ∃ δ : ExtOrd → ExtOrd, Witness (gTop N) δ ∧
          ∀ f, δ (PairedSlotEncoding.normalize N b₀ f) = a f := by
  obtain ⟨a, h1, h2, h3, b₀, h4, h5, h6, δ, hδ, hread, -⟩ := bottom_supply' (R := R) hv₁
  exact ⟨a, h1, h2, h3, b₀, h4, h5, h6, δ, hδ, hread⟩

section GenericTerminal
open CanonicalPairedInverse LadderScalarRendering ReceivingCatalogueRanks

def profileFreshFloor {X : Type*} [Fintype X] (p : X → ExtOrd) (h : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.omega0 * ((insert h (PairedSlotEncoding.values p)).sup id + 1)

theorem profileFreshFloor_limit {X : Type*} [Fintype X] (p : X → ExtOrd) (h : Ordinal.{0}) :
    limitPart (profileFreshFloor p h) = profileFreshFloor p h := limitPart_omega0_mul _

theorem lt_profileFreshFloor {X : Type*} [Fintype X] (p : X → ExtOrd) (h : Ordinal.{0})
    {a : Ordinal.{0}} (ha : a ∈ insert h (PairedSlotEncoding.values p)) :
    a < profileFreshFloor p h := by
  unfold profileFreshFloor
  set m := (insert h (PairedSlotEncoding.values p)).sup id
  exact (Order.lt_add_one_iff.mpr (Finset.le_sup (f := id) ha)).trans_le
    (Ordinal.le_mul_right (m + 1) Ordinal.omega0_pos)

theorem profile_lt_freshFloor {X : Type*} [Fintype X] (p : X → ExtOrd) (h : Ordinal.{0}) (d : X) :
    p d < ofOrd (profileFreshFloor p h) ∨ p d = ⊤ := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · exact Or.inl (hb ▸ bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _))
  · exact Or.inr ht
  · exact Or.inl (by
      rw [ha, ofOrd_lt_ofOrd]
      exact lt_profileFreshFloor p h
        (Finset.mem_insert_of_mem (PairedSlotEncoding.mem_values.mpr ⟨d, ha⟩)))

theorem exists_supported_decoder_of_map {X St : Type*} [Fintype X]
    (prof : St → X → ExtOrd) (mapS : (ExtOrd → ExtOrd) → St → St)
    (normS : ℕ → St → St) (Adm : St → Prop)
    (hprof_map : ∀ (f : ExtOrd → ExtOrd) (T : St) (d : X), prof (mapS f T) d = f (prof T d))
    (hprof_norm : ∀ (j : ℕ) (T : St) (d : X),
      prof (normS j T) d = PairedSlotEncoding.normalize j (prof T) d)
    {j : ℕ} (hj : 1 ≤ j) {S : St} (hS : Adm S)
    (hadm_map : ∀ {f : ExtOrd → ExtOrd}, Witness (gTop j) f →
      (∀ x, f x = ⊥ → x = ⊥) → Adm (mapS f S))
    (hadm_norm : ∀ {T : St}, Adm T → Adm (normS j T)) :
    ∃ Q : St, Adm Q ∧ prof Q ∈ CanonicalPairedProfiles.inventory X j ∧
      (∀ d, fieldRank (prof Q) d = fieldRank (prof S) d) ∧
      ∃ δ : ExtOrd → ExtOrd, Witness (gTop j) δ ∧
        (∀ d, δ (prof Q d) = prof S d) ∧
        (∀ d, δ (prof Q d) = ⊥ → prof Q d = ⊥) ∧
        ∀ x, OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) (prof S) (δ x) := by
  let l := profileFreshFloor (prof S) 0
  have hlim : limitPart l = l := profileFreshFloor_limit (prof S) 0
  let β : ExtOrd := ofOrd (l + j)
  have hβvis : SelfVis j β := by
    rw [selfVis_ofOrd_iff]
    have he := finitePart_limitPart_add_nat l j
    rw [hlim] at he; exact he.ge
  have hβbot : β ≠ ⊥ := ofOrd_ne_bot _
  have hlβ : ofOrd l ≤ β := ofOrd_le_ofOrd.mpr le_self_add
  let S₀ := mapS (fun x => min x β) S
  have hS₀ : Adm S₀ := hadm_map (capWitness hβvis hβbot) (capWitness_reflects_bottom hβbot)
  have hproper (d : X) : prof S₀ d ≠ ⊤ := by
    rw [hprof_map]; exact fun ht => ofOrd_ne_top _ (min_eq_top.mp ht).2
  have hcap (d : X) : min (prof S d) (ofOrd 0) = min (prof S₀ d) (ofOrd 0) := by
    rw [hprof_map, min_assoc, min_eq_right
      ((ofOrd_le_ofOrd.mpr (lt_profileFreshFloor (prof S) 0
        (Finset.mem_insert_self _ _)).le).trans hlβ)]
  let Q := normS j S₀
  have hQeq : prof Q = PairedSlotEncoding.normalize j (prof S₀) := funext (hprof_norm j S₀)
  have hcanon : prof Q ∈ CanonicalPairedProfiles.inventory X j :=
    hQeq ▸ CanonicalPairedProfiles.normalize_mem_inventory X j hproper
  have hc := collapseBlock_witness j hlim
  have hi (d : X) : collapseBlock l (min (prof S d) β) = prof S d :=
    collapseBlock_min hlβ (profile_lt_freshFloor (prof S) 0 d)
  have hr₀ (d : X) : fieldRank (prof S₀) d = fieldRank (prof S) d := by
    have he : prof S₀ = fun d => min (prof S d) β := funext (hprof_map _ S)
    rw [he]
    exact fieldRank_of_leftInverse (prof S) (fun _ _ h => min_le_min_right _ h)
      hc.mono (min_bot_left _) hc.bot hi d
  have hrQ (d : X) : fieldRank (prof Q) d = fieldRank (prof S) d :=
    (congrArg (fun p => fieldRank p d) hQeq).trans
      ((fieldRank_normalize j (prof S₀) hproper d).trans (hr₀ d))
  have hG : ∀ z ∈ ({β} : Finset ExtOrd), SelfVis j z := fun z hz => by
    rw [Finset.mem_singleton.mp hz]; exact hβvis
  let δ := collapseBlock l ∘ PairedSlotDecoder.decode j (PairedSlotEncoding.values (prof S₀)) {β} β
  have hδ : Witness (gTop j) δ :=
    Witness.comp_of_bottom_reflecting (PairedSlotDecoder.decode_witness hG hβvis) hc le_rfl
      (collapseBlock_reflects_bottom l)
  have hread (d : X) : δ (prof Q d) = prof S d := by
    dsimp only [δ, Function.comp_apply]
    rw [hprof_norm, PairedSlotDecoder.decode_normalize hG hβvis hproper d, hprof_map]
    exact hi d
  refine ⟨Q, hadm_norm hS₀, hcanon, hrQ, δ, hδ, hread, fun d hd => ?_, fun x => ?_⟩
  · have hSd : prof S d = ⊥ := (hread d).symm.trans hd
    have he := hcap d
    rw [hSd, min_bot_left] at he
    have hS₀d : prof S₀ d = ⊥ := (min_eq_bot.mp he.symm).resolve_right (ofOrd_ne_bot 0)
    rw [hprof_norm]
    exact (PairedSlotEncoding.normalize_bot_iff j (prof S₀) d).mpr hS₀d
  · dsimp only [δ, Function.comp_apply]
    rcases PairedSlotDecoder.decode_supported (j := j) (K := j) (p := prof S₀)
        le_rfl (Finset.mem_singleton_self β) x with hz | hβ | ⟨d, i, hi', he⟩
    · rw [hz]; exact Or.inl hc.bot
    · rw [Finset.mem_singleton.mp (Finset.mem_coe.mp hβ), collapseBlock_of_le hlβ]
      exact Or.inr (Or.inl (Set.mem_singleton _))
    · rw [he, hprof_map]
      rcases profile_lt_freshFloor (prof S) 0 d with hlt | ht
      · rw [min_eq_left (hlt.le.trans hlβ), collapseBlock_of_lt (evr_lt_of_lt_limit hlim hlt j i)]
        exact Or.inr (Or.inr ⟨d, i, hi', rfl⟩)
      · rw [ht, min_top_left, evr_eq_self_of_selfVis hβvis i, collapseBlock_of_le hlβ]
        exact Or.inr (Or.inl (Set.mem_singleton _))

theorem exists_protected_repair_of_map {X St : Type*} [Fintype X]
    (prof : St → X → ExtOrd) (mapS : (ExtOrd → ExtOrd) → St → St)
    (normS : ℕ → St → St) (Adm : St → Prop)
    (hprof_map : ∀ (f : ExtOrd → ExtOrd) (T : St) (d : X), prof (mapS f T) d = f (prof T d))
    (hprof_norm : ∀ (j : ℕ) (T : St) (d : X),
      prof (normS j T) d = PairedSlotEncoding.normalize j (prof T) d)
    {j B : ℕ} (hj : 1 ≤ j) {a : X → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory X j)
    {S : St} (hS : Adm S)
    (hadm_map : ∀ {f : ExtOrd → ExtOrd}, Witness (gTop j) f →
      (∀ x, f x = ⊥ → x = ⊥) → Adm (mapS f S))
    (hadm_norm : ∀ {T : St}, Adm T → Adm (normS j T))
    (hag : ∀ d, min (a d) (grid j B) = min (prof S d) (grid j B)) :
    ∃ (Q : St) (δ : ExtOrd → ExtOrd), Adm Q ∧
      prof Q ∈ CanonicalPairedProfiles.inventory X j ∧
      (∀ d, min (prof Q d) (grid j B) = min (a d) (grid j B)) ∧
      Witness (gTop j) δ ∧
      (∀ d, δ (prof Q d) = prof S d) ∧
      (∀ b < B, δ (grid j b) = grid j b) ∧
      grid j B ≤ δ (grid j B) ∧
      ∀ d, a d < grid j B → δ (a d) = a d := by
  let h : Ordinal.{0} := Ordinal.omega0 * B + j
  let l := profileFreshFloor (prof S) h
  let β : ExtOrd := ofOrd (l + j)
  have hlim : limitPart l = l := profileFreshFloor_limit (prof S) h
  have hh : grid j B < ofOrd l :=
    ofOrd_lt_ofOrd.mpr (lt_profileFreshFloor (prof S) h (Finset.mem_insert_self _ _))
  have hβ : SelfVis j β := by
    rw [selfVis_ofOrd_iff]
    have he := finitePart_limitPart_add_nat l j
    rw [hlim] at he; exact he.ge
  have hlβ : ofOrd l ≤ β := ofOrd_le_ofOrd.mpr le_self_add
  let V := mapS (fun x => min x β) S
  have hV : Adm V := hadm_map (capWitness hβ (ofOrd_ne_bot _))
    (capWitness_reflects_bottom (ofOrd_ne_bot _))
  have hproper (d : X) : prof V d ≠ ⊤ := by
    rw [hprof_map]; exact fun ht => ofOrd_ne_top _ (min_eq_top.mp ht).2
  have hagV (d : X) : min (a d) (grid j B) = min (prof V d) (grid j B) := by
    rw [hprof_map, min_assoc, min_eq_right (hh.le.trans hlβ)]; exact hag d
  obtain ⟨κ, hw, hread, hfix, hreach, _⟩ := exists_supported_inverse ha hproper hagV
  let Q := normS j V
  have hQeq : prof Q = PairedSlotEncoding.normalize j (prof V) := funext (hprof_norm j V)
  have hprefix (d : X) : min (prof Q d) (grid j B) = min (a d) (grid j B) := by
    rw [hprof_norm]; exact CanonicalPairedProfiles.normalize_cap X j ha hagV d
  let δ := collapseBlock l ∘ κ
  have hδ : Witness (gTop j) δ :=
    Witness.comp_of_bottom_reflecting hw (collapseBlock_witness j hlim) le_rfl
      (collapseBlock_reflects_bottom l)
  have hδread (d : X) : δ (prof Q d) = prof S d := by
    dsimp only [δ, Function.comp_apply]
    rw [hprof_norm, hread, hprof_map]
    exact collapseBlock_min hlβ (profile_lt_freshFloor (prof S) h d)
  refine ⟨Q, δ, hadm_norm hV,
    hQeq ▸ CanonicalPairedProfiles.normalize_mem_inventory X j hproper,
    hprefix, hδ, hδread, fun b hb => ?_, ?_, fun d hd => ?_⟩
  · dsimp only [δ, Function.comp_apply]
    rw [hfix b hb]
    exact collapseBlock_of_lt (lt_of_le_of_lt
      (ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)) hh)
  · calc
      grid j B = collapseBlock l (grid j B) := (collapseBlock_of_lt hh).symm
      _ ≤ collapseBlock l (κ (grid j B)) := (collapseBlock_witness j hlim).mono hreach
  · exact (congrArg δ (PairedSlotEncoding.eq_of_cap_eq_lt (hprefix d).symm hd)).trans
      ((hδread d).trans (PairedSlotEncoding.eq_of_cap_eq_lt (hag d) hd).symm)

end GenericTerminal

end
end VaughtConjecture.Knight.CappedDonor.Ref
