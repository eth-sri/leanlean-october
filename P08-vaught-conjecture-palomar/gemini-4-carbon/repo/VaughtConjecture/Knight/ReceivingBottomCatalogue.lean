/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RequestCatalogueRepair

/-! # Independent bottom-cap catalogue supply on both original faces

At bottom cap no source prefix is protected. Use the proved bottom fibres,
resynchronize the source state, and construct terminal-block decoding into the
same canonical catalogue. This does not use positive-cap transport and does
not assert lawfulness of decoding a still-unconstructed physical renderer.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.ReceivingBottomCatalogue
open Transform Value ExtOrd CappedDonor CappedDonor.Ref ReceivingSupportedRepair
noncomputable section
variable {I : Type*} [Fintype I] {nP N J K j : ℕ}
  {P : SemScheme (nP + 1)} {C : SemScheme J} {R : Ref I nP N J P C}
  {L : R.LowRef K}

/-- Constructed exact decoding of an entire source state. Unlike active repair,
there is no preserved grid cut or owner clipping in this bottom-cap output. -/
structure Insertion (T : R.TState j) where
  encoded : R.TState j
  admitted : L.TAdmissible encoded
  synchronized : Synchronized encoded.st
  canonical : encoded.profile ∈ CanonicalPairedProfiles.inventory (TField P C) j
  decoder : ExtOrd → ExtOrd
  witness : Witness (gTop j) decoder
  readback : ∀ f, decoder (encoded.profile f) = T.profile f

/-- Literal-top handling moves tops into a fresh terminal block before
normalization and collapses the whole block afterward. No protected extra grid
is needed here: the external cap is bottom. -/
theorem exists_insertion (hj : 1 ≤ j) {T : R.TState j}
    (hT : L.TAdmissible T) (hs : Synchronized T.st) : Nonempty (Insertion (L := L) T) := by
  obtain ⟨l, β, _, hβdef, hβ, hcap, hproper, _, δ, hδ, hread⟩ :=
    L.exists_terminal_decoding hj hT 0
  let V := mapT (fun x => min x β) T
  have hbot : β ≠ ⊥ := by rw [hβdef]; exact ofOrd_ne_bot _
  have hsV : Synchronized V.st := hs.map (capWitness hβ hbot) hj
  refine ⟨{
    encoded := normalizeT V
    admitted := L.normalizeT_tadmissible hj hcap
    synchronized := normalizeT_synchronized hj hsV
    canonical := ?_
    decoder := δ
    witness := hδ
    readback := hread }⟩
  have he : (normalizeT V).profile = PairedSlotEncoding.normalize j V.profile :=
    funext (profile_normalizeT V)
  rw [he]
  exact CanonicalPairedProfiles.normalize_mem_inventory _ _ hproper

namespace Insertion
variable {T : R.TState j} (r : Insertion (L := L) T)

theorem catalogue : r.encoded.profile ∈ Catalogue (j := j) L :=
  ⟨r.canonical, r.encoded, r.admitted, r.synchronized, rfl⟩

end Insertion

end
end VaughtConjecture.Knight.ReceivingBottomCatalogue
