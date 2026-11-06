
import VaughtConjecture.Knight.PointwiseLabels
import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyNormalization
import VaughtConjecture.Knight.CappedDonorLowHighNormalization

/-! # Literal-top insertion in the gate-free canonical catalogue

Attribution: the fresh terminal block and scalar whole-block collapse are the
construction in `CappedDonorLowHighNormalization`. Only those scalar tools are
reused here; no `Ref`, LOW/HIGH state, or gate is constructed. Exact decoding is
on the complete original-field inventory, not on uninstalled physical rows.
-/

namespace VaughtConjecture.Knight.LowOnly

open  Value ExtOrd   

noncomputable section

variable {n K : ℕ} {P C : SemScheme n}

namespace State

def freshFloor (S : State P C) (h : Ordinal₀) : Ordinal₀ :=
  Ordinal.omega0 * ((insert h (PairedSlotEncoding.values S.profile)).sup id + 1)

theorem freshFloor_limit (S : State P C) h :
    limitPart (S.freshFloor h) = S.freshFloor h := limitPart_omega0_mul _

theorem lt_freshFloor (S : State P C) h {a}
    (ha : a ∈ insert h (PairedSlotEncoding.values S.profile)) : a < S.freshFloor h := by
  
  set m := (insert h (PairedSlotEncoding.values S.profile)).sup id
  exact (Order.lt_add_one_iff.mpr (Finset.le_sup  ha)).trans_le
    (Ordinal.le_mul_right (m + 1) Ordinal.omega0_pos)

theorem profile_lt_freshFloor (S : State P C) h d :
    S.profile d < ofOrd (S.freshFloor h) ∨ S.profile d = ⊤ := by
  rcases ExtOrd.cases (S.profile d) with hb | ht | ⟨a, ha⟩
  · simp_all
  · exact Or.inr ht
  · refine Or.inl ?_
    rw [ha, ofOrd_lt_ofOrd]
    exact S.lt_freshFloor h (Finset.mem_insert_of_mem
      (PairedSlotEncoding.mem_values.mpr ⟨d, ha⟩))

end State

namespace Family

variable (F : Family P C K)

/-- Every admitted complete vector, including literal top, has an admitted proper
canonical representative and an exact outgoing decoder. Properization preserves
the prescribed raw prefix; no unused physical-grid fixation is claimed. -/
theorem terminal_insertion {j} (hj : 1 ≤ j) {S}
    (hS : F.Admissible j S) h :
    ∃ S₀ Q , F.Admissible j S₀ ∧ (AvoidsValue S₀.profile ⊤) ∧
      S.CapEq (ofOrd h) S₀ ∧ Q = S₀.normalize j ∧ F.Admissible j Q ∧
      Q.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j ∧
      ∃ δ , Witness (gTop j) δ ∧ ∀ d, δ (Q.profile d) = S.profile d := by
  let l := S.freshFloor h
  have hlim : limitPart l = l := S.freshFloor_limit h
  let β : ExtOrd := ofOrd (l + j)
  have hβvis  := by
    change SelfVis j (ofOrd (l + j))
    rw [selfVis_ofOrd_iff]
    have h := finitePart_limitPart_add_nat l j
    rw [hlim] at h
    exact h.ge
  have hβbot : β ≠ ⊥ := ofOrd_ne_bot _
  have hlβ : ofOrd l ≤ β := ofOrd_le_ofOrd.mpr le_self_add
  let S₀ := S.map (fun x => min x β)
  have hS₀ : F.Admissible j S₀ :=
    hS.map F (capWitness hβvis hβbot) hj (capWitness_reflects_bottom hβbot)
  have hproper : AvoidsValue S₀.profile ⊤ := by
    intro d
    rw [State.profile_map]
    exact fun ht => ofOrd_ne_top _ ((min_eq_top.mp ht).2)
  have hprefix : S.CapEq (ofOrd h) S₀ := by
    apply State.capEq_iff_profile.mpr
    intro d
    rw [State.profile_map, min_assoc, min_eq_right
      ((ofOrd_le_ofOrd.mpr (S.lt_freshFloor h (Finset.mem_insert_self _ _)).le).trans hlβ)]
  refine ⟨S₀, S₀.normalize j, hS₀, hproper, hprefix, rfl,
    F.normalize_admissible hj hS₀, normalize_inventory j hproper, ?_⟩
  have hG : VisibleOn j (∅ : Finset ExtOrd) :=
    fun z hz => absurd hz (Finset.notMem_empty z)
  refine ⟨collapseBlock l ∘ PairedSlotDecoder.decode j
    (PairedSlotEncoding.values S₀.profile) ∅ β,
    Witness.comp_of_bottom_reflecting (PairedSlotDecoder.decode_witness hG hβvis)
      (collapseBlock_witness j hlim) le_rfl (collapseBlock_reflects_bottom l), ?_⟩
  intro d
  rw [Function.comp_apply, State.profile_normalize,
    PairedSlotDecoder.decode_normalize hG hβvis hproper, State.profile_map]
  exact collapseBlock_min hlβ (S.profile_lt_freshFloor h d)

