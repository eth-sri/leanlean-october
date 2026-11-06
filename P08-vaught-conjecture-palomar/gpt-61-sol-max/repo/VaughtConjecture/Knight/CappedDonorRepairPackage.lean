
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CappedDonorCatalogue
import VaughtConjecture.Knight.CanonicalPairedInverse
import VaughtConjecture.Knight.PairedSlotComparison

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

namespace VaughtConjecture.Knight.CappedDonor.Ref

open  Value ExtOrd


variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

local notation "grid₀" => CanonicalPairedInverse.grid N

/-- A witness fixing every grid endpoint below `B` fixes every source-grid value below the cut
`grid N B` (bottom included). -/
theorem fix_sourceGrid {κ : LabelMap} (hbot : κ ⊥ = ⊥) {B : ℕ}
    (hfix : ∀ b < B, κ (grid₀ b) = grid₀ b)
    (n : ℕ) : ∀ z ∈ PairedSlotComparison.sourceGrid N n, z < grid₀ B →
      κ z = z := by
  
  intro z hz hlt
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hbot
  · obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hz
    refine hfix b ?_
    by_contra hle
    apply not_le.mpr hlt
    
    exact ofOrd_le_ofOrd.mpr (add_le_add_left (omul_le_omul (not_lt.mp hle)) _)

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow C.rows (effC J N)

local notation "below₀" => C.scheme.below (effC J N)

/-- **Positive-cap repair through normalization and the supported inverse.** -/
theorem positive_cap_repair {a : Field P C → ExtOrd} (ha : a ∈ R.Catalogue)
    {v₁ : below₀ → ExtOrd} (hv₁ : RespectsSemanticsBelow₀ v₁)
    (hv₁p : AvoidsValue v₁ ⊤) {B : ℕ}
    (hagree : ∀ d, min (v₁ d) (grid₀ B) =
      min (a (.priv d.1)) (grid₀ B)) :
    ∃ b₀ , R.Admitted b₀ ∧ (AvoidsValue b₀ ⊤) ∧
      (∀ d , b₀ (.priv d.1) = v₁ d) ∧
      (CappedEq b₀ a (grid₀ B)) ∧
      PairedSlotEncoding.normalize N b₀ ∈ R.Catalogue ∧
      (∀ f, min (PairedSlotEncoding.normalize N b₀ f) (grid₀ B) =
        min (a f) (grid₀ B)) ∧
      ∃ κ , Witness (gTop N) κ ∧
        (∀ f, κ (PairedSlotEncoding.normalize N b₀ f) = b₀ f) ∧
        (∀ b < B, κ (grid₀ b) = grid₀ b) ∧
        grid₀ B ≤ κ (grid₀ B) ∧
        ∀ f, a f < grid₀ B → ∀ k ≤ N, ∀ i ≤ k,
          κ (extVisibilityReplace (a f) k i) = extVisibilityReplace (a f) k i := by
  obtain ⟨hinv, hadm⟩ := ha
  have hgrid  :=
    CanonicalPairedInverse.grid_visible N B
  have hne : grid₀ B ≠ ⊥ := ofOrd_ne_bot _
  obtain ⟨b₁, hb₁, hpriv₁, hrec₁⟩ := hadm.private_repair hv₁ hgrid hne hagree
  obtain ⟨b₀, hb₀, hprop, hpre, hlit, -, -, -⟩ :=
    hb₁.exists_terminal (Ordinal.omega0 * B + N)
  have hpre'  := fun f => (hpre f).trans (hrec₁ f)
  have hag  := fun f => (hpre' f).symm
  refine ⟨b₀, hb₀, hprop, fun d => ?_, hpre', hb₀.normalize_mem_catalogue hprop, fun f => ?_, ?_⟩
  · grind
  · exact CanonicalPairedProfiles.normalize_cap hinv hag f
  · exact?

/-- **Independent bottom-cap private supply, with a supported decoder.**  From the zero
admitted state, an arbitrary lawful private prescription — literal top included — is installed
with the gate off; terminal insertion gives a member of the catalogue with an exact decoder
reading it back, every output of which is supported by the installed vector (bottom and top
allowed). -/
theorem bottom_supply' {v₁ : below₀ → ExtOrd}
    (hv₁ : RespectsSemanticsBelow₀ v₁) :
    ∃ a , R.Admitted a ∧
      (∀ d , a (.priv d.1) = v₁ d) ∧ a .gate = ⊥ ∧
      ∃ b₀ , R.Admitted b₀ ∧ (AvoidsValue b₀ ⊤) ∧
        PairedSlotEncoding.normalize N b₀ ∈ R.Catalogue ∧
        ∃ δ , Witness (gTop N) δ ∧
          (∀ f, δ (PairedSlotEncoding.normalize N b₀ f) = a f) ∧
          ∀ x, OrbitPrefixSupport.Supported N ({⊤} : Set ExtOrd) a (δ x) := by
  obtain ⟨st₁, hst₁, hv, -, -, -⟩ := R.exists_private_lift (zeroState_admissible N) hv₁
    (selfVis_bot) (fun d => by simp  )
  let st₂  := Ref.gateOff (resync st₁)
  have hadm : R.Admitted st₂.sourceProfile :=
    ⟨st₂, hst₁.resync.gateOff, (resync_synchronized hst₁).gateOff R.one_le_N,
      extVisibilityReplace_bot _ _, rfl⟩
  obtain ⟨b₀, hb₀, hprop, -, -, hnorm, hmem, δ, hδ, hread, hsupp⟩ := hadm.exists_terminal' 0
  refine ⟨st₂.sourceProfile, hadm, fun d => ?_, ?_, b₀, hb₀, hprop, ⟨hmem, hnorm⟩, δ, hδ, hread,
    hsupp⟩
  · rw [State.sourceProfile_of_present _ ((present_priv_iff).mp d.2)]
    change st₁.v ⟨d.1, _⟩ = v₁ d
    rw [hv]
    exact congrArg v₁ (Subtype.ext rfl)
  · rw [State.sourceProfile_of_present _ ((R.one_le_N))]
    rfl

/-- **Independent bottom-cap private supply** (the decoder's support conjunct dropped). -/
theorem bottom_supply {v₁ : below₀ → ExtOrd}
    (hv₁ : RespectsSemanticsBelow₀ v₁) :
    ∃ a , R.Admitted a ∧
      (∀ d , a (.priv d.1) = v₁ d) ∧ a .gate = ⊥ ∧
      ∃ b₀ , R.Admitted b₀ ∧ (AvoidsValue b₀ ⊤) ∧
        PairedSlotEncoding.normalize N b₀ ∈ R.Catalogue ∧
        ∃ δ , Witness (gTop N) δ ∧
          ∀ f, δ (PairedSlotEncoding.normalize N b₀ f) = a f := by
  obtain ⟨a, h1, h2, h3, b₀, h4, h5, h6, δ, hδ, hread, -⟩ := bottom_supply' (R := R) hv₁
  exact ⟨a, h1, h2, h3, b₀, h4, h5, h6, δ, hδ, hread⟩


