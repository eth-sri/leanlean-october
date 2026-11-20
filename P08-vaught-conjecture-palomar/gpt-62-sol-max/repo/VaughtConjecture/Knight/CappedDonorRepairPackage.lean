/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorCatalogue
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.PairedSlotComparison

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
      min (b₀ f) (CanonicalPairedInverse.grid N B) := by simp_all
  refine ⟨b₀, hb₀, hprop, fun d => ?_, hpre', hb₀.normalize_mem_catalogue hprop, fun f => ?_, ?_⟩
  · grind
  · exact CanonicalPairedProfiles.normalize_cap (Field P C) N hinv hag f
  · exact CanonicalPairedInverse.exists_supported_inverse hinv hprop hag

/-- Install any private prescription in an admitted source, with the gate off. -/
theorem exists_private_admitted {v : C.scheme.below (effC J N) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC J N) v) :
    ∃ a, R.Admitted a ∧ ∀ d, a (.priv d.1) = v d := by
  obtain ⟨st, hs, hread, -, -, -⟩ := R.exists_private_lift (zeroState_admissible N) hv
    (selfVis_bot _) (fun _ => by simp only [min_bot_right])
  let z := Ref.gateOff (resync st)
  refine ⟨z.sourceProfile, ⟨z, hs.resync.gateOff, (resync_synchronized hs).gateOff R.one_le_N,
    extVisibilityReplace_bot _ _, rfl⟩, fun d => ?_⟩
  rw [State.sourceProfile_of_present _ ((present_priv_iff N d.1).mp d.2)]
  exact congrFun hread d

end

end VaughtConjecture.Knight.CappedDonor.Ref
