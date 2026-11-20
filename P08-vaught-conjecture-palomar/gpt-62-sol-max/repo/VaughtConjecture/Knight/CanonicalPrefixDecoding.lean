/- Copyright (c) 2026 Cameron Freer. Released under Apache 2.0. -/
module

public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.OrbitPrefixSupport
public import VaughtConjecture.Knight.SourcePrefixRows
public import VaughtConjecture.Knight.PairedSlotComparison

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalPrefixDecoding

open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison CanonicalPairedInverse

noncomputable section

theorem grid_mono (k : ℕ) : Monotone (grid k) :=
  fun _ _ h => ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)

theorem grid_fixed_below {k B n : ℕ} {δ : ExtOrd → ExtOrd} (hb : δ ⊥ = ⊥)
    (hf : ∀ i < B, δ (grid k i) = grid k i) {z : ExtOrd}
    (hz : z ∈ sourceGrid k n) (hlt : z < grid k B) : δ z = z := by
  classical
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hb
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact hf i (lt_of_not_ge (fun hi => hlt.not_ge (grid_mono k hi)))

/-- A protected grid prefix extends from the normalized boundary to the full
source, and is unchanged by its supported inverse. -/
theorem exists_decoder {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {X : Type*} [Fintype X] {k : ℕ}
    {a p : X → ExtOrd} (ha : a ∈ CanonicalPairedProfiles.inventory X k)
    (ht : ∀ x, p x ≠ ⊤) {B : ℕ} (hB : B ≤ 2 * Fintype.card X + 1)
    (hag : Agree a p (grid k B))
    (s t : Cell D → ExtOrd)
    (hs : RespectsSemanticsBelow sem (A, k) (fun d => s d.1))
    (ht' : RespectsSemanticsBelow sem (A, k) (fun d => t d.1))
    (hsupp : ∀ d, OrbitPrefixSupport.Supported k (sourceGrid k (Fintype.card X) : Set ExtOrd) a (s d))
    (hprefix : grid k B ∈ sourceGrid k (Fintype.card X) →
      Agree (PairedSlotEncoding.normalize k p) a (grid k B) → Agree t s (grid k B)) :
    ∃ δ, RespectsSemanticsBelow sem (A, k) (fun d => δ (t d.1)) ∧
      (∀ x, δ (PairedSlotEncoding.normalize k p x) = p x) ∧ Agree (δ ∘ t) s (grid k B) := by
  obtain ⟨δ, hw, hr, hfix, hreach, _⟩ := exists_supported_inverse ha ht hag
  have hn := CanonicalPairedProfiles.normalize_cap X k ha hag
  have hf (x) (hx : a x < grid k B) : δ (a x) = a x :=
    (congrArg δ (eq_of_cap_eq_lt (hn x).symm hx)).trans
      ((hr x).trans (eq_of_cap_eq_lt (hag x) hx).symm)
  have hc := OrbitPrefixSupport.decode_agree hw (grid_visible k B)
    (by rw [gTop_of_le le_rfl]; exact le_top) hreach
    (fun _ => grid_fixed_below hw.bot hfix) hf hsupp (hprefix (sourceGrid_endpoint hB) hn)
  exact ⟨δ, SharpWitnessComposition.map_respects_of_positive_cap_agreement ht' hs
    (fun d => d.2.2) (hw.bounded)
    (ofOrd_ne_bot _) (fun d => hc d.1), hr, hc⟩

end

end VaughtConjecture.Knight.CanonicalPrefixDecoding
