/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PositiveNormalization

@[expose] public section

namespace VaughtConjecture.Knight.SharpWitnessComposition

open Transform Value ExtOrd

/-- Flatten the unused finite tail, without moving a source to another block. -/
noncomputable def trim (m : ℕ) : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ⊤
  | some (some a) => ofOrd (limitPart a + (min (finitePart a) m : ℕ))

@[simp] theorem trim_ofOrd (m : ℕ) (a : Ordinal.{0}) :
    trim m (ofOrd a) = ofOrd (limitPart a + (min (finitePart a) m : ℕ)) := rfl

theorem trim_eq {m : ℕ} {a : Ordinal.{0}} (ha : finitePart a ≤ m) :
    trim m (ofOrd a) = ofOrd a := by
  rw [trim_ofOrd, min_eq_left ha, decomposition]

theorem trim_mono (m : ℕ) : Monotone (trim m) := by
  intro x y hxy
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · exact bot_le
  · rw [top_le_iff.mp hxy]
  · rcases ExtOrd.cases y with rfl | rfl | ⟨b, rfl⟩
    · simp_all
    · exact le_top
    · rw [trim_ofOrd, trim_ofOrd, ofOrd_le_ofOrd]
      have hab := ofOrd_le_ofOrd.mp hxy
      rcases (limitPart_mono hab).eq_or_lt with he | hl
      · rw [he]
        exact add_le_add_right (Nat.cast_le.mpr
          (min_le_min_right m (finitePart_le_of_le he hab))) _
      · exact ((add_lt_add_right (Ordinal.natCast_lt_omega0 _) _).le.trans
          (limitPart_add_omega0_le hl)).trans le_self_add

/-- Bounded replacements commute with source flattening. -/
theorem trim_evr (m : ℕ) (x : ExtOrd) {k i : ℕ} (hk : k ≤ m) (hi : i ≤ k) :
    trim m (extVisibilityReplace x k i) = extVisibilityReplace (trim m x) k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rfl
  · rfl
  · by_cases ha : finitePart a < k
    · rw [extVisibilityReplace_of_finitePart_lt ha, trim_ofOrd,
        finitePart_limitPart_add_nat, limitPart_limitPart_add_nat,
        min_eq_left (hi.trans hk), trim_ofOrd,
        extVisibilityReplace_of_finitePart_lt (by
          rw [finitePart_limitPart_add_nat]; omega),
        limitPart_limitPart_add_nat]
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp ha), trim_ofOrd,
        extVisibilityReplace_of_le_finitePart (by
          rw [finitePart_limitPart_add_nat]; simp_all)]

/-- The weak data needed before repairing the higher-grade bottom guard. -/
structure BoundedMap (m : ℕ) (f : ExtOrd → ExtOrd) : Prop where
  bot : f ⊥ = ⊥
  mono : Monotone f
  comm : ∀ x k i, k ≤ m → i ≤ k →
    f (extVisibilityReplace x k i) = extVisibilityReplace (f x) k i

end VaughtConjecture.Knight.SharpWitnessComposition

namespace VaughtConjecture.Knight

open SharpWitnessComposition Value ExtOrd

theorem Witness.bounded {K : ℕ} {τ : ExtOrd → ExtOrd} (h : Witness (gTop K) τ) : BoundedMap K τ :=
  ⟨h.bot, h.mono, fun x _ _ => h.comm x⟩

open Transform
section StripReadback

variable {N : ℕ} {τ : ExtOrd → ExtOrd} (hτ : BoundedMap N τ)

include hτ in
/-- An invisible proper reading locates its source and reads the entire low strip. -/
theorem read_strip {x : ExtOrd} {t : Ordinal.{0}} (h : τ x = ofOrd t) (ht : finitePart t < N) :
    x = ofOrd (ordOf x) ∧ finitePart (ordOf x) = finitePart t ∧
      ∀ i ≤ N, τ (ofOrd (limitPart (ordOf x) + i)) = ofOrd (limitPart t + i) := by
  have hn : ¬ SelfVis N x := fun hx => (not_le_of_gt ht) (selfVis_ofOrd_iff.mp
    (h ▸ (hτ.comm x N N le_rfl le_rfl).symm.trans (congrArg τ hx)))
  rcases ExtOrd.cases x with rfl | rfl | ⟨s, rfl⟩
  · exact (hn (selfVis_bot N)).elim
  · exact (hn (extVisibilityReplace_top N N)).elim
  have hs := lt_of_not_ge (fun hs => hn (selfVis_ofOrd_iff.mpr hs))
  have horbit (i) (hi : i ≤ N) := hτ.comm (ofOrd s) N i le_rfl hi
  simp only [extVisibilityReplace_of_finitePart_lt hs, h,
    extVisibilityReplace_of_finitePart_lt ht] at horbit
  have he := horbit (finitePart s) hs.le
  rw [limitPart_add_finitePart, h, ofOrd_inj] at he
  have hf := congrArg finitePart he
  rw [finitePart_limitPart_add_nat] at hf
  rw [ordOf_ofOrd]
  exact ⟨rfl, hf.symm, horbit⟩

include hτ in
/-- A low-offset reading identifies the source and the entire low affine strip. -/
theorem read_strip_block {x : ExtOrd} {a : Ordinal.{0}} {i : ℕ}
    (ha : limitPart a = a) (hi : i < N) (h : τ x = ofOrd (a + i)) :
    x = ofOrd (ordOf x) ∧ finitePart (ordOf x) = i ∧
      ∀ n ≤ N, τ (ofOrd (limitPart (ordOf x) + n)) = ofOrd (a + n) := by
  have h' : τ x = ofOrd (limitPart a + i) := by rwa [ha]
  have hs := read_strip hτ h' (by rwa [finitePart_limitPart_add_nat])
  simp only [finitePart_limitPart_add_nat, limitPart_limitPart_add_nat] at hs
  simpa only [ha] using hs

theorem strip_le_of_affine (hm : Monotone τ) (hN : 0 < N)
    {s s' t t' : Ordinal.{0}}
    (h : ∀ i ≤ N, τ (ofOrd (limitPart s + i)) = ofOrd (t + i))
    (h' : ∀ i ≤ N, τ (ofOrd (limitPart s' + i)) = ofOrd (t' + i))
    (hle : t ≤ t') : limitPart s ≤ limitPart s' := by
  by_contra! hs
  have he := hm (ofOrd_le_ofOrd.mpr (limitPart_add_nat_le_of_lt hs N))
  have h0 := h 0 (Nat.zero_le _)
  simp only [Nat.cast_zero, add_zero] at h0
  rw [h' _ le_rfl, h0, ofOrd_le_ofOrd] at he
  have hlt : t' < t' + (N : Ordinal.{0}) := by
    simpa only [Nat.cast_zero, add_zero] using
      add_lt_add_right ((Nat.cast_lt (α := Ordinal.{0})).mpr hN) (t')
  exact (hle.trans_lt hlt).not_ge he

include hτ in
theorem strip_le_of_read {s s' t t' : Ordinal.{0}} (h : τ (ofOrd s) = ofOrd t)
    (h' : τ (ofOrd s') = ofOrd t') (ht : finitePart t < N) (ht' : finitePart t' < N)
    (hle : limitPart t ≤ limitPart t') : limitPart s ≤ limitPart s' := by
  have h₁ := (read_strip hτ h ht).2.2
  have h₂ := (read_strip hτ h' ht').2.2
  simp only [ordOf_ofOrd] at h₁ h₂
  exact strip_le_of_affine hτ.mono (Nat.zero_lt_of_lt ht) h₁ h₂ hle

include hτ in
theorem strip_lt_of_read {s s' t t' : Ordinal.{0}} (h : τ (ofOrd s) = ofOrd t)
    (h' : τ (ofOrd s') = ofOrd t') (ht : finitePart t < N) (ht' : finitePart t' < N)
    (hlt : limitPart t < limitPart t') : limitPart s < limitPart s' := by
  have h₁ := (read_strip hτ h ht).2.2 0 (Nat.zero_le _)
  have h₂ := (read_strip hτ h' ht').2.2 0 (Nat.zero_le _)
  by_contra! hs
  have he := hτ.mono (ofOrd_le_ofOrd.mpr hs)
  simp only [ordOf_ofOrd, Nat.cast_zero, add_zero] at h₁ h₂
  rw [h₂, h₁, ofOrd_le_ofOrd] at he
  exact hlt.not_ge he

include hτ in
/-- A pinned reading at offset `i` determines the whole source strip. -/
theorem read_strip_at {i : ℕ} {x : ExtOrd} {u : Ordinal.{0}} (hi : i < N)
    (hx : τ x = ofOrd (limitPart u + i)) :
    ∃ v : Ordinal.{0}, x = ofOrd (limitPart v + i) ∧
      ∀ n ≤ N, τ (ofOrd (limitPart v + n)) = ofOrd (limitPart u + n) := by
  obtain ⟨hv, hi', hread⟩ := read_strip_block hτ (limitPart_idem u) hi hx
  exact ⟨ordOf x, hv.trans (by rw [← hi', decomposition]), hread⟩

end StripReadback

end VaughtConjecture.Knight

namespace VaughtConjecture.Knight.SharpWitnessComposition

open Transform Value ExtOrd

namespace BoundedMap

theorem comp {m K : ℕ} {σ ν : ExtOrd → ExtOrd}
    (hν : BoundedMap K ν) (hσ : BoundedMap m σ) (hmK : m ≤ K) :
    BoundedMap m (ν ∘ σ) where
  bot := by simp [Function.comp_apply, hσ.bot, hν.bot]
  mono := hν.mono.comp hσ.mono
  comm x k i hk hi := by
    simp only [Function.comp_apply]
    rw [hσ.comm x k i hk hi, hν.comm _ k i (hk.trans hmK) hi]


variable {m : ℕ} {f : ExtOrd → ExtOrd} (hf : BoundedMap m f)

include hf

/-- If the repaired map kills one point of a block, it kills the entire block. -/
theorem trim_bot_block {a b : Ordinal.{0}} (hab : limitPart a = limitPart b)
    (ha : f (trim m (ofOrd a)) = ⊥) : f (trim m (ofOrd b)) = ⊥ := by
  have hfloor : f (ofOrd (limitPart a)) = ⊥ := by
    apply le_bot_iff.mp
    exact (hf.mono (ofOrd_le_ofOrd.mpr le_self_add)).trans_eq ha
  by_cases hm : m = 0
  · simp_all
  have he : extVisibilityReplace (ofOrd (limitPart a)) m (min (finitePart b) m) =
      trim m (ofOrd b) := by
    rw [extVisibilityReplace_of_finitePart_lt (by
      rw [finitePart_limitPart]; exact Nat.pos_of_ne_zero hm), limitPart_idem,
      trim_ofOrd, hab]
  rw [← he, hf.comm _ _ _ le_rfl (min_le_right _ _), hfloor,
    extVisibilityReplace_bot]

/-- The repaired function is a full faithful witness at every threshold. -/
theorem witness : Witness (gTop m) (f ∘ trim m) where
  anti := (witness_id m).anti
  vis := (witness_id m).vis
  bot := hf.bot
  mono := hf.mono.comp (trim_mono m)
  clause5 := by
    intro x k hact i hi
    change f (trim m (extVisibilityReplace x k i)) =
      extVisibilityReplace (f (trim m x)) k i
    by_cases hk : k ≤ m
    · rw [trim_evr m x hk hi, hf.comm _ _ _ hk hi]
    · have hz : f (trim m x) = ⊥ := by
        simpa [Function.comp_apply, gTop_of_gt (not_le.mp hk), le_bot_iff] using hact
      rw [hz, extVisibilityReplace_bot]
      rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
      · exact hf.bot
      · exact hz
      · rw [extVisibilityReplace_ofOrd]
        apply hf.trim_bot_block _ hz
        unfold visibilityReplace
        split_ifs
        · exact (limitPart_limitPart_add_nat _ _).symm
        · rfl

end BoundedMap

/-- Only the low source offsets are used; literal top is also harmless. -/
def Short (m : ℕ) (x : ExtOrd) : Prop :=
  x = ⊥ ∨ x = ⊤ ∨ ∃ a : Ordinal.{0}, x = ofOrd a ∧ finitePart a ≤ m

theorem trim_of_short {m : ℕ} {x : ExtOrd} (hx : Short m x) : trim m x = x := by
  rcases hx with rfl | rfl | ⟨a, rfl, ha⟩
  · rfl
  · rfl
  · exact trim_eq ha

/-- Repair the composite off the row. Every grade-short source is unchanged. -/
theorem comp_read {m K : ℕ} {σ ν : ExtOrd → ExtOrd}
    (hσ : Witness (gTop m) σ) (hν : Witness (gTop K) ν) (hmK : m ≤ K) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop m) τ ∧
      ∀ x, Short m x → τ x = ν (σ x) := by
  refine ⟨(ν ∘ σ) ∘ trim m, (hν.bounded.comp hσ.bounded hmK).witness, ?_⟩
  intro x hx
  simp [Function.comp_apply, trim_of_short hx]

/-- A source-short controller locality survives any normalized outer shifter of
at least its grade. The witness is repaired, not the semantic source row. -/
theorem map_capped_locality
    {X : Type*} {grade : X → ℕ} {E p : X → ExtOrd} {c : X}
    {K : ℕ} {ν : ExtOrd → ExtOrd}
    (hmax : ∀ d, grade d ≤ grade c) (hcK : grade c ≤ K)
    (hshort : ∀ d, Short (grade c) (E d))
    (hvis : SelfVis (grade c) (p c))
    (hloc : TransformsTo grade E (fun d => min (p d) (p c)))
    (hν : Witness (gTop K) ν) :
    TransformsTo grade E (fun d => min (ν (p d)) (ν (p c))) := by
  obtain ⟨σ, hσ, _, hread⟩ := exists_bounded_exact_capped_witness hmax hvis hloc
  obtain ⟨τ, hτ, hτread⟩ := comp_read hσ hν hcK
  exact hτ.transformsTo_top hmax (fun d => by rw [hτread _ (hshort d), hread, hν.mono.map_min])

end VaughtConjecture.Knight.SharpWitnessComposition
