
import VaughtConjecture.Knight.PointwiseLabels
import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthNormalization
import VaughtConjecture.Knight.CappedDonorRepairPackage
import VaughtConjecture.Knight.ReferenceContext
import VaughtConjecture.Knight.CappedDonorLowHighNormalization
import VaughtConjecture.Knight.CanonicalPairedInverse

/-! # Supported growth catalogue insertion

The terminal-block and protected-grid calculations are adapted from
`LowOnlyTerminalSupport` and `LowOnlySupportedRepair`; their admission step is
the independently proved growth `Admitted.map`, not the LOW fibre. Top-valued
inputs are first capped above the entire protected prefix, then the whole fresh
terminal block is collapsed. No physical renderer lawfulness is assumed or claimed.
-/

namespace VaughtConjecture.Knight.Growth
open  Value ExtOrd   
open CanonicalPairedInverse
noncomputable section
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  {j B : ℕ}

local notation "State₀" => State DA DQ

namespace State

def freshFloor (S : State₀) (h : Ordinal₀) : Ordinal₀ :=
  Ordinal.omega0 * ((insert h (PairedSlotEncoding.values S.profile)).sup id + 1)

theorem freshFloor_limit (S : State₀) h :
    limitPart (S.freshFloor h) = S.freshFloor h := limitPart_omega0_mul _

theorem lt_freshFloor (S : State₀) h {a}
    (ha : a ∈ insert h (PairedSlotEncoding.values S.profile)) : a < S.freshFloor h := by
  
  set m := (insert h (PairedSlotEncoding.values S.profile)).sup id
  exact (Order.lt_add_one_iff.mpr (Finset.le_sup  ha)).trans_le
    (Ordinal.le_mul_right (m + 1) Ordinal.omega0_pos)

theorem profile_lt_freshFloor (S : State₀) h d :
    S.profile d < ofOrd (S.freshFloor h) ∨ S.profile d = ⊤ := by
  rcases ExtOrd.cases (S.profile d) with hb | ht | ⟨a, ha⟩
  · simp_all
  · exact Or.inr ht
  · refine Or.inl ?_
    rw [ha, ofOrd_lt_ofOrd]
    exact S.lt_freshFloor h (Finset.mem_insert_of_mem
      (PairedSlotEncoding.mem_values.mpr ⟨d, ha⟩))

end State

variable (X : RelativeData DA semA DQ semQ)

local notation "inventory₀" => CanonicalPairedProfiles.inventory (Field DA DQ)

/-- Literal-top insertion with all-output support, including unused decoder
arguments. The fresh terminal block need not lie below the final model stage. -/
theorem terminal_insertion_supported {j : ℕ} (hj : 1 ≤ j) {S : State₀}
    (hS : Admitted X j S) (h : Ordinal₀) :
    ∃ S₀ Q , Admitted X j S₀ ∧ (AvoidsValue S₀.profile ⊤) ∧
      S.CapEq (ofOrd h) S₀ ∧ Q = S₀.normalize j ∧ Admitted X j Q ∧
      Q.profile ∈ inventory₀ j ∧
      ∃ δ , Witness (gTop j) δ ∧
        (∀ d, δ (Q.profile d) = S.profile d) ∧
        ∀ x, OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) S.profile (δ x) := by
  let l := S.freshFloor h
  have hlim : limitPart l = l := S.freshFloor_limit h
  let β : ExtOrd := ofOrd (l + j)
  have hβvis  := by
    change SelfVis j (ofOrd (l + j))
    rw [selfVis_ofOrd_iff]
    have he := finitePart_limitPart_add_nat l j
    rw [hlim] at he
    exact he.ge
  have hβbot : β ≠ ⊥ := ofOrd_ne_bot _
  have hlβ : ofOrd l ≤ β := ofOrd_le_ofOrd.mpr le_self_add
  let S₀ := S.map (fun x => min x β)
  have hS₀ : Admitted X j S₀ :=
    hS.map X (capWitness hβvis hβbot) hj (capWitness_reflects_bottom hβbot)
  have hproper : AvoidsValue S₀.profile ⊤ := by
    intro d
    rw [State.profile_map]
    exact fun ht => ofOrd_ne_top _ ((min_eq_top.mp ht).2)
  have hprefix : S.CapEq (ofOrd h) S₀ := by
    intro d
    rw [State.profile_map, min_assoc, min_eq_right
      ((ofOrd_le_ofOrd.mpr (S.lt_freshFloor h (Finset.mem_insert_self _ _)).le).trans hlβ)]
  refine ⟨S₀, S₀.normalize j, hS₀, hproper, hprefix, rfl,
    normalize_admitted X hj hS₀, normalize_inventory j hproper, ?_⟩
  have hG : VisibleOn j ({β} : Finset ExtOrd) := fun z hz => by
    aesop
  refine ⟨collapseBlock l ∘ PairedSlotDecoder.decode j
    (PairedSlotEncoding.values S₀.profile) {β} β,
    Witness.comp_of_bottom_reflecting (PairedSlotDecoder.decode_witness hG hβvis)
      (collapseBlock_witness j hlim) le_rfl (collapseBlock_reflects_bottom l), ?_, ?_⟩
  · intro d
    rw [Function.comp_apply, State.profile_normalize,
      PairedSlotDecoder.decode_normalize hG hβvis hproper, State.profile_map]
    exact collapseBlock_min hlβ (S.profile_lt_freshFloor h d)
  · intro x
    rw [Function.comp_apply]
    rcases PairedSlotDecoder.decode_supported (j := j) (K := j) (p := S₀.profile)
        le_rfl (Finset.mem_singleton_self β) x with hz | hβ | ⟨d, i, hi, he⟩
    · rw [hz]
      exact Or.inl (collapseBlock_witness j hlim).bot
    · rw [Finset.mem_singleton.mp (Finset.mem_coe.mp hβ), collapseBlock_of_le hlβ]
      exact Or.inr (Or.inl (Set.mem_singleton _))
    · rw [he, State.profile_map]
      rcases S.profile_lt_freshFloor h d with hlt | ht
      · rw [min_eq_left (hlt.le.trans hlβ),
          collapseBlock_of_lt (evr_lt_of_lt_limit hlim hlt j i)]
        exact Or.inr (Or.inr ⟨d, i, hi, rfl⟩)
      · rw [ht, min_top_left, evr_eq_self_of_selfVis hβvis, collapseBlock_of_le hlβ]
        exact Or.inr (Or.inl (Set.mem_singleton _))

/-- A catalogue member and exact decoder with the finite bottom reflection
needed by the long padded rows, and support on every decoder argument. -/
theorem exists_supported_decoder {j : ℕ} (hj : 1 ≤ j) {S : State₀}
    (hS : Admitted X j S) :
    ∃ Q , Admitted X j Q ∧
      Q.profile ∈ inventory₀ j ∧
      ∃ δ , Witness (gTop j) δ ∧
        (PointwiseEq (δ ∘ Q.profile) S.profile) ∧
        (∀ d, δ (Q.profile d) = ⊥ → Q.profile d = ⊥) ∧
        ∀ x, OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) S.profile (δ x) := by
  obtain ⟨S₀, Q, _, _, hcap, hQeq, hQ, hcanon, δ, hδ, hread, hsupp⟩ :=
    terminal_insertion_supported X hj hS 0
  refine ⟨Q, hQ, hcanon, δ, hδ, hread, ?_, hsupp⟩
  intro d hd
  have hSd  := (hread d).symm.trans hd
  have he := hcap d
  rw [hSd, ] at he
  have hS₀ : S₀.profile d = ⊥ := (min_eq_bot.mp he).resolve_right (ofOrd_ne_bot 0)
  rw [hQeq, State.profile_normalize]
  exact (PairedSlotEncoding.normalize_bot_iff).mpr hS₀

/-- Constructed source repair, including protected unused grid endpoints. -/
structure ProtectedRepair (a : Field DA DQ → ExtOrd) (S : State₀) (j B : ℕ) where
  encoded : State₀
  admitted : Admitted X j encoded
  canonical : encoded.profile ∈ inventory₀ j
  prefix_eq : ∀ d, min (encoded.profile d) (grid j B) = min (a d) (grid j B)
  decoder : LabelMap
  witness : Witness (gTop j) decoder
  readback : ∀ d, decoder (encoded.profile d) = S.profile d
  grid_fixed : ∀ b < B, decoder (grid j b) = grid j b
  reaches : grid j B ≤ decoder (grid j B)
  boundary_fixed : ∀ d, a d < grid j B → decoder (a d) = a d

local notation "grid₀" => grid j B

/-- Properize above the cut, use the supported inverse, then collapse the whole
terminal block. Literal top does not sacrifice any protected grid point. -/
theorem exists_protected_repair (hj : 1 ≤ j) {a : Field DA DQ → ExtOrd}
    (ha : a ∈ inventory₀ j)
    {S : State₀} (hS : Admitted X j S)
    (hag : CappedEq a S.profile (grid₀)) :
    Nonempty (ProtectedRepair X a S j B) := by
  let h  := Ordinal.omega0 * B + j
  let l := S.freshFloor h
  let β : ExtOrd := ofOrd (l + j)
  have hlim  := S.freshFloor_limit h
  have hh  :=
    ofOrd_lt_ofOrd.mpr (S.lt_freshFloor h (Finset.mem_insert_self _ _))
  have hβ : SelfVis j β := by
    apply selfVis_ofOrd_iff.mpr
    have he := finitePart_limitPart_add_nat l j
    rw [hlim] at he
    exact he.ge
  have hlβ : ofOrd l ≤ β := ofOrd_le_ofOrd.mpr le_self_add
  have hcutβ : grid₀ ≤ β := hh.le.trans hlβ
  let V := S.map (fun x => min x β)
  have hV : Admitted X j V :=
    hS.map X (capWitness hβ (ofOrd_ne_bot _)) hj
      (capWitness_reflects_bottom (ofOrd_ne_bot _))
  have hproper : AvoidsValue V.profile ⊤ := by
    intro d
    rw [State.profile_map]
    exact fun ht => ofOrd_ne_top _ (min_eq_top.mp ht).2
  have hagV : CappedEq a V.profile (grid₀) := by
    intro d
    rw [State.profile_map, min_assoc, min_eq_right hcutβ]
    exact hag d
  obtain ⟨κ, hw, hread, hfix, hreach, _⟩ := exists_supported_inverse ha hproper hagV
  let Q := V.normalize j
  have hprefix : CappedEq Q.profile a (grid₀) := by
    intro d
    rw [State.profile_normalize]
    exact CanonicalPairedProfiles.normalize_cap ha hagV d
  let δ := collapseBlock l ∘ κ
  have hδ : Witness (gTop j) δ :=
    Witness.comp_of_bottom_reflecting hw (collapseBlock_witness j hlim) le_rfl
      (collapseBlock_reflects_bottom l)
  have hδread d : δ (Q.profile d) = S.profile d := by
    dsimp only [δ, Function.comp_apply]
    rw [State.profile_normalize, hread, State.profile_map]
    exact collapseBlock_min hlβ (S.profile_lt_freshFloor h d)
  refine ⟨{
    encoded := Q
    admitted := normalize_admitted X hj hV
    canonical := normalize_inventory j hproper
    prefix_eq := hprefix
    decoder := δ
    witness := hδ
    readback := hδread
    grid_fixed := ?_
    reaches := ?_
    boundary_fixed := ?_
  }⟩
  · intro b hb
    dsimp only [δ, Function.comp_apply]
    rw [hfix b hb]
    apply collapseBlock_of_lt
    apply lt_of_le_of_lt _ hh
    exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)
  · calc
      grid₀ = collapseBlock l (grid₀) := (collapseBlock_of_lt hh).symm
      _ ≤ collapseBlock l (κ (grid₀)) := (collapseBlock_witness j hlim).mono hreach
  · grind

