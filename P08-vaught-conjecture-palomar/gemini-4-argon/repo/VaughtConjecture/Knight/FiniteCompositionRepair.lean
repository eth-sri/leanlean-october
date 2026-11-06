/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SharpWitnessComposition
public import VaughtConjecture.Knight.FiniteFloorCompletion

/-! # Finite floor checks for composition repair

Bounded commutation plus a finite block-floor condition constructs a full faithful
witness on any finite source inventory. The witness is the lower envelope of the
completed strip table. This includes source offsets above the controller grade,
where grade-short composition does not apply.

The floor condition is sufficient for this particular table, not a necessary
condition for every possible interpolating witness. Failing it is not a semantic
impossibility certificate. No respect or existence of an extension is assumed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SharpWitnessComposition

open Transform Value ExtOrd

namespace BoundedMap

variable {m : ℕ} {f : ExtOrd → ExtOrd} (hf : BoundedMap m f)

include hf

/-- A killed block floor already forces every low strip slot to bottom. -/
theorem bot_on_strip {a : Ordinal.{0}} (ha : f (ofOrd (limitPart a)) = ⊥)
    {i : ℕ} (hi : i ≤ m) : f (ofOrd (limitPart a + i)) = ⊥ := by
  by_cases hm : m = 0
  · have hi0 : i = 0 := Nat.eq_zero_of_le_zero (hm ▸ hi)
    simpa only [hi0, Nat.cast_zero, add_zero] using ha
  have he := hf.comm (ofOrd (limitPart a)) m i le_rfl hi
  rw [extVisibilityReplace_of_finitePart_lt (by
    rw [finitePart_limitPart]; exact Nat.pos_of_ne_zero hm), limitPart_idem,
    ha, extVisibilityReplace_bot] at he
  exact he

/-- Only the original sources need testing: added low strip slots are automatic. -/
theorem floor_check_on_strip (s : Finset ExtOrd)
    (hfloor : ∀ x ∈ s, f (blockFloor x) = ⊥ → f x = ⊥) :
    ∀ x ∈ stripDomain m s, f (blockFloor x) = ⊥ → f x = ⊥ := by
  intro x hx hb
  rcases Finset.mem_union.mp hx with hx | hx
  · exact hfloor x hx hb
  · obtain ⟨y, _, hy⟩ := Finset.mem_biUnion.mp hx
    rcases ExtOrd.cases y with rfl | rfl | ⟨a, rfl⟩
    · simp at hy
    · simp at hy
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      rw [blockFloor_ofOrd, limitPart_limitPart_add_nat] at hb
      exact hf.bot_on_strip hb (by have := Finset.mem_range.mp hi; omega)

/-- On a finite full-strip table, the floor-support check is the missing
higher-threshold obligation. The existing bridge builds the witness explicitly. -/
theorem finite_witness (s : Finset ExtOrd)
    (hfloor : ∀ x ∈ stripDomain m s, f (blockFloor x) = ⊥ → f x = ⊥) :
    Witness (gTop m) (finiteLowerEnvelope (stripDomain m s) f) := by
  let t := stripDomain m s
  have hmono : ∀ a ∈ t, ∀ b ∈ t, a ≤ b → f a ≤ f b :=
    fun _ _ _ _ h => hf.mono h
  have hsupport : FloorSupport t f := by
    intro z hz _ hzb
    exact ⟨blockFloor z, stripDomain_floor_mem hz, le_rfl,
      fun h => hzb (hfloor z hz h)⟩
  have horbit : FiniteShifterWeakOrbit t f (gTop m) := by
    intro x hx k i hi hact
    by_cases hk : k ≤ m
    · exact Or.inr ⟨stripDomain_closed hx hk hi, hf.comm x k i hk hi⟩
    · exact Or.inl (le_bot_iff.mp (hact.trans_eq (gTop_of_gt (not_le.mp hk))))
  have hbridge : FiniteShifterBlockBridge t f (gTop m) := by
    intro x k hact i hi z hz hzx
    by_cases hk : k ≤ m
    · exact Or.inr (fullStrip_bridge m t f
        (fun a ha i hi => stripDomain_fullStrips ha hi) hmono
        (fun a _ k i hk hi => hf.comm a k i hk hi)
        (fun a ha k i hk hi => stripDomain_closed ha hk hi) x hk hi hz hzx)
    · exact bridge_tail_of_floorSupport t f (gTop m) m
        (fun k hk => gTop_of_gt hk) hsupport x k (not_le.mp hk) hact i z hz hzx
  exact ⟨(witness_id m).anti, (witness_id m).vis,
    finiteLowerEnvelope_bot t f (fun y _ hy => hy ▸ hf.bot),
    finiteLowerEnvelope_mono t f,
    fun x k hact i hi => finiteLowerEnvelope_visibility_eq t f (gTop m)
      horbit hbridge x k i hi hact⟩

/-- Every original table value is retained, not just its value below some cap. -/
theorem finite_read (s : Finset ExtOrd) {x : ExtOrd} (hx : x ∈ s) :
    finiteLowerEnvelope (stripDomain m s) f x = f x :=
  finiteLowerEnvelope_source _ _ (fun _ _ _ _ h => hf.mono h) (subset_stripDomain m s hx)

end BoundedMap

section Scheme

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ} {r : D.below BJ → ExtOrd}

/-- Actual normalized local witnesses of an already respecting labelling. The
source-floor values are auxiliary witness data, not new semantic occurrences. -/
structure LocalCharts (sem : Semantics D) (BJ : Finset ι × ℕ)
    (r : D.below BJ → ExtOrd) where
  shift : D.below BJ → ExtOrd → ExtOrd
  witness : ∀ c, Witness (gTop (D.grade c.1)) (shift c)
  read : ∀ (c : D.below BJ) (d : D.below (D.cell c.1)),
    shift c (sem.E c.1 d) = min (r (CellScheme.below.incl c d)) (r c)

/-- Existence is extracted from the old localities; it is not a new producer assumption. -/
theorem exists_localCharts (hr : RespectsSemanticsBelow sem BJ r) :
    Nonempty (LocalCharts sem BJ r) := by
  have h (c : D.below BJ) : ∃ σ, Witness (gTop (D.grade c.1)) σ ∧
      ∀ d : D.below (D.cell c.1),
        σ (sem.E c.1 d) = min (r (CellScheme.below.incl c d)) (r c) := by
    obtain ⟨σ, hw, _, he⟩ := exists_bounded_exact_capped_witness
      (c := (⟨c.1, GradedLe.refl _⟩ : D.below (D.cell c.1)))
      (p := fun d => r (CellScheme.below.incl c d))
      (fun d => d.2.2) (hr.orderly c).symm (hr.locality c)
    exact ⟨σ, hw, he⟩
  choose σ hw he using h
  exact ⟨⟨σ, hw, he⟩⟩
