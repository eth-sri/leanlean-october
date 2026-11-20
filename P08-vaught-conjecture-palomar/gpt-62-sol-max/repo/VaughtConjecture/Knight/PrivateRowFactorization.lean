/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerLocalAlignment
public import VaughtConjecture.Knight.CanonicalPairedProfiles

@[expose] public section

namespace VaughtConjecture.Knight.PrivateRowFactorization

open Transform Value ExtOrd SharpWitnessComposition OwnerLocalEndpoint

noncomputable section

theorem code_spec {m j : ℕ} {x : ExtOrd}
    (hc : x ∈ ExtOrd.codedAlphabet m j) (hs : Short j x) :
    x = ⊥ ∨ ∃ b i : ℕ, b ≤ m ∧ i ≤ j ∧ x = ofOrd (Ordinal.omega0 * b + i) := by
  rcases ExtOrd.mem_codedAlphabet_iff.mp hc with hb | ⟨b, i, hb, _, he⟩
  · tauto
  · refine Or.inr ⟨b, i, hb, ?_, he⟩
    rcases hs with hz | ht | ⟨u, hu, hj⟩
    · aesop
    · aesop
    have heq := ofOrd_inj.mp (he.symm.trans hu)
    simpa [← heq, finitePart_mul_add] using hj

theorem code_bound {m j : ℕ} {x : ExtOrd}
    (hc : x ∈ ExtOrd.codedAlphabet m j) (hs : Short j x) :
    x ≤ ofOrd (Ordinal.omega0 * m + j) := by
  rcases code_spec hc hs with rfl | ⟨b, i, hb, hi, rfl⟩
  · simp
  · apply ofOrd_le_ofOrd.mpr
    apply add_le_add
    all_goals simp_all

theorem endpoint_grid {m j : ℕ} {x : ExtOrd}
    (hc : x ∈ ExtOrd.codedAlphabet (2 * m) j) (hs : Short j x) :
    endpoint j x ∈ PairedSlotComparison.sourceGrid j m := by
  rcases code_spec hc hs with rfl | ⟨b, i, hb, hi, rfl⟩
  · exact PairedSlotComparison.sourceGrid_bot j m
  · have he : endpoint j (ofOrd (Ordinal.omega0 * b + i)) =
        ofOrd (Ordinal.omega0 * b + j) := by
      by_cases hij : i < j
      · rw [endpoint, extVisibilityReplace_of_finitePart_lt (by
          rw [finitePart_mul_add]; assumption), limitPart_mul_add]
      · have hi' : i = j := by omega
        subst i
        apply endpoint_of_selfVis
        apply selfVis_ofOrd_iff.mpr
        rw [finitePart_mul_add]
    rw [he]
    exact PairedSlotComparison.sourceGrid_endpoint (hb.trans (Nat.le_succ _))

theorem short_replace {j k i : ℕ} {x : ExtOrd} (hx : Short j x)
    (hk : k ≤ j) (hi : i ≤ k) : Short j (extVisibilityReplace x k i) := by
  rcases hx with rfl | rfl | ⟨u, rfl, hu⟩
  · tauto
  · tauto
  · by_cases hut : finitePart u < k
    · rw [extVisibilityReplace_of_finitePart_lt hut]
      exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_limitPart_add_nat]; omega⟩)
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hut)]
      tauto

/-- Retuning and tail decoding retain the external cap on every short source,
not only represented fields. The final owner clip allows literal-top targets. -/
theorem outgoing_cap {j b : ℕ} {σ ρ : ExtOrd → ExtOrd} {h δ γ M : ExtOrd}
    (S : Finset Ordinal.{0}) (hσ : Monotone σ)
    (hρ : Witness (gTop j) ρ) (hδ : SelfVis j δ) (hM : SelfVis j M)
    (hroom : h < ofOrd (Ordinal.omega0 * b)) (hread : ρ h = δ)
    (hγδ : γ ≤ δ) (hδM : δ ≤ M) (hreach : γ ≤ σ h)
    (hcap : ∀ x, Short j x → min (ρ x) γ = min (σ x) γ)
    {x : ExtOrd} (hx : Short j x) :
    min (min (PaddedSourceDecoder.extend S j b ρ δ x) M) γ = min (σ x) γ := by
  by_cases hlow : x < ofOrd (Ordinal.omega0 * b)
  · rw [PaddedSourceDecoder.extend_before S hlow, min_assoc, min_eq_right (hγδ.trans hδM),
      min_assoc, min_eq_right hγδ]
    tauto
  · have hhx : h ≤ x := hroom.le.trans (not_lt.mp hlow)
    have hν := FreeDiagonal.clip_witness (PaddedSourceDecoder.extend_witness (b := b) S hρ hδ) hM
    have hat : min (PaddedSourceDecoder.extend S j b ρ δ h) M = δ := by
      rw [PaddedSourceDecoder.extend_before S hroom, hread, min_self, min_eq_left hδM]
    have hνx : γ ≤ min (PaddedSourceDecoder.extend S j b ρ δ x) M :=
      hγδ.trans (hat.ge.trans (hν.mono hhx))
    rw [min_eq_right hνx, min_eq_right (hreach.trans (hσ hhx))]

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable {sem : Semantics D}

/-- A repaired row and its capped outgoing decoder. -/
structure Factorization (c : Cell D) (s p : D.below (D.cell c) → ExtOrd)
    (σ : ExtOrd → ExtOrd) (γ δ : ExtOrd) where
  source : D.below (D.cell c) → ExtOrd
  outgoing : ExtOrd → ExtOrd
  lawful : RespectsSemanticsBelow sem (D.cell c) source
  proper : ∀ d, source d ≠ ⊤
  witness : Witness (gTop (D.grade c)) outgoing
  bounded : ∀ x, outgoing x ≤ p ⟨c, GradedLe.refl _⟩
  readback : ∀ d, outgoing (source d) = min (p d) (p ⟨c, GradedLe.refl _⟩)
  prefix_eq : ∀ d, min (source d) δ = min (s d) δ
  reaches : γ ≤ outgoing δ
  caps : ∀ x, Short (D.grade c) x → min (outgoing x) γ = min (σ x) γ

/-- Repair at the owner-local saturation endpoint, which belongs to the source grid. -/
theorem exists_factorization (c : Cell D) {s p : D.below (D.cell c) → ExtOrd} (m : ℕ)
    (hs : RespectsSemanticsBelow sem (D.cell c) s)
    (hp : RespectsSemanticsBelow sem (D.cell c) p)
    (hcoded : ∀ e, s e ∈ ExtOrd.codedAlphabet (2 * m) (D.grade c))
    (hshort : ∀ e, Short (D.grade c) (s e))
    {σ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hσ : Witness (gTop (D.grade c)) σ) (hγ : SelfVis (D.grade c) γ)
    (hpos : ⊥ < γ) (hpc : γ < p ⟨c, GradedLe.refl _⟩)
    (hface : ∀ e, min (σ (s e)) γ = min (p e) γ) :
    ∃ δ ∈ PairedSlotComparison.sourceGrid (D.grade c) m, ⊥ < δ ∧
      Nonempty (Factorization (sem := sem) c s p σ γ δ) := by
  classical
  let := Fintype.ofFinite (D.below (D.cell c))
  let self : D.below (D.cell c) := ⟨c, GradedLe.refl _⟩
  let M := p self
  let τ := fun x => min (σ x) γ
  have hτ : Witness (gTop (D.grade c)) τ := FreeDiagonal.clip_witness hσ hγ
  have hτbound : ∀ x, τ x ≤ γ := fun _ => min_le_right _ _
  have htface : ∀ e, τ (s e) = min (p e) γ := hface
  have hbudget := code_bound (hcoded self) (hshort self)
  obtain ⟨η, ρ, β, f, H, hηpos, _, hreach, hroom, hρ, hγβ, hβM, hβvis, hρη,
      hf, hfprefix, hfdef, hfread, _, hρcap⟩ :=
    OwnerLocalAlignment.exists_coded_face c hs hp hshort m hbudget
      hτ hγ hpos hτbound htface hpc
  have hηreach : γ ≤ σ η := hreach.ge.trans (min_le_left _ _)
  have hηgrid : η ∈ PairedSlotComparison.sourceGrid (D.grade c) m := by
    obtain ⟨e, _, he⟩ := H.exists_witness
    grind [endpoint_grid]
  let S := RelativePrefixEncoding.inventory (fun e => min (p e) M) β
  let ν := fun x => min (PaddedSourceDecoder.extend S (D.grade c) (2 * m + 1) ρ β x) M
  have hMvis : SelfVis (D.grade c) M := (hp.orderly self).symm
  have hν : Witness (gTop (D.grade c)) ν :=
    FreeDiagonal.clip_witness (PaddedSourceDecoder.extend_witness S hρ hβvis) hMvis
  have hcaps : ∀ x, Short (D.grade c) x → min (ν x) γ = min (σ x) γ := by
    intro x hx
    apply outgoing_cap S hσ.mono hρ hβvis hMvis hroom hρη hγβ hβM hηreach
      (fun z hz => ?_) hx
    grind
  refine ⟨η, hηgrid, hηpos, ⟨{
    source := f
    outgoing := ν
    lawful := hf
    proper := ?_
    witness := hν
    bounded := fun _ => min_le_right _ _
    readback := ?_
    prefix_eq := hfprefix
    reaches := ?_
    caps := hcaps }⟩⟩
  · intro e
    rw [hfdef]
    exact AlignedCutEncoding.encode_ne_top hroom e
  · grind
  · have hηshort : Short (D.grade c) η := by
      rcases Finset.mem_insert.mp hηgrid with rfl | he
      · solve_by_elim
      · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp he
        exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)
    have he := hcaps η hηshort
    grind

end

end VaughtConjecture.Knight.PrivateRowFactorization
