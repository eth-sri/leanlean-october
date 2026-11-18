/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CapFirstScalar
public import VaughtConjecture.Knight.SourceBlockPadding

@[expose] public section

namespace VaughtConjecture.Knight.PaddedSourceDecoder

open Transform Value ExtOrd SharpWitnessComposition SourceBlockPadding

/-- Move nonbottom sources by `b` whole blocks. -/
noncomputable def reserve : ℕ → ExtOrd → ExtOrd
  | 0, x => x
  | b + 1, x => pad (reserve b x)

/-- Erase the reserved blocks; every erased block is killed in its entirety. -/
noncomputable def release : ℕ → ExtOrd → ExtOrd
  | 0, x => x
  | b + 1, x => release b (unpad x)

@[simp] theorem reserve_bot (b : ℕ) : reserve b ⊥ = ⊥ := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [reserve, ih, pad_bot]


/-- The inverse is literal at every padded source, including bottom and top. -/
theorem release_reserve (b : ℕ) (x : ExtOrd) : release b (reserve b x) = x := by
  induction b with
  | zero => rfl
  | succ b ih => simpa only [reserve, release, unpad_pad] using ih

/-- Repeated source padding preserves the finite part exactly. -/
theorem reserve_code (b u j : ℕ) : reserve b (ofOrd (Ordinal.omega0 * u + j)) =
    ofOrd (Ordinal.omega0 * (u + b : ℕ) + j) := by
  induction b with
  | zero => simp only [reserve, Nat.add_zero]
  | succ b ih => rw [reserve, ih, pad_code, Nat.add_assoc]

/-- Precomposition is justified by exact replacement commutation, not transitivity. -/
theorem witness_release {g : ℕ → ExtOrd} {τ : ExtOrd → ExtOrd}
    (hτ : Witness g τ) (b : ℕ) : Witness g (fun x => τ (release b x)) := by
  induction b with
  | zero => exact hτ
  | succ b ih => exact witness_precompose_unpad ih

private theorem unpad_lt_floor {b : ℕ} {x : ExtOrd}
    (hx : x < ofOrd (Ordinal.omega0 * (b + 1 : ℕ))) :
    unpad x < ofOrd (Ordinal.omega0 * b) := by
  classical
  rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
  · rw [unpad_bot]; exact bot_lt_ofOrd _
  · exact False.elim (not_lt_of_ge le_top hx)
  · by_cases hα : Ordinal.omega0 ≤ α
    · have he : pad (unpad (ofOrd α)) = ofOrd α := by
        rw [unpad_ofOrd, ite_eq_left hα, pad_ofOrd, Ordinal.add_sub_cancel_of_le hα]
      have hp : pad (ofOrd (Ordinal.omega0 * b)) =
          ofOrd (Ordinal.omega0 * (b + 1 : ℕ)) := by
        simpa only [Nat.cast_zero, add_zero] using pad_code b 0
      by_contra hn
      have hle := pad_mono (not_lt.mp hn)
      rw [he, hp] at hle
      exact not_lt_of_ge hle hx
    · rw [unpad_ofOrd, ite_eq_right hα]
      exact bot_lt_ofOrd _

/-- The decoder sees bottom on the entire reserved prefix, not just listed sources. -/
theorem release_eq_bot_of_lt {b : ℕ} {x : ExtOrd}
    (hx : x < ofOrd (Ordinal.omega0 * b)) : release b x = ⊥ := by
  induction b generalizing x with
  | zero =>
    change x = ⊥
    rcases ExtOrd.cases x with rfl | rfl | ⟨α, rfl⟩
    · rfl
    · exact False.elim (not_lt_of_ge le_top hx)
    · have hα := ofOrd_lt_ofOrd.mp hx
      simp only [Nat.cast_zero, mul_zero, not_lt_zero] at hα
  | succ b ih => exact ih (unpad_lt_floor hx)

/-- An alphabet of block bound `t` moves to block bound `t + b`. -/
theorem reserve_mem_codedAlphabet {t K : ℕ} {x : ExtOrd}
    (hx : x ∈ ExtOrd.codedAlphabet t K) (b : ℕ) :
    reserve b x ∈ ExtOrd.codedAlphabet (t + b) K := by
  rcases mem_codedAlphabet_iff.mp hx with rfl | ⟨u, j, hu, hj, rfl⟩
  · exact mem_codedAlphabet_iff.mpr (Or.inl (reserve_bot b))
  · exact mem_codedAlphabet_iff.mpr
      (Or.inr ⟨u + b, j, Nat.add_le_add_right hu b, hj, reserve_code b u j⟩)

/-- The actual finite tail code. Original literal top is represented by a proper code. -/
noncomputable def encode (S : Finset Ordinal.{0}) (K b : ℕ) (y : ExtOrd) : ExtOrd :=
  reserve b (canonicalNormalizer S K y)

/-- Exact alphabet accounting: no availability of this much room in a tower is assumed. -/
theorem encode_mem (S : Finset Ordinal.{0}) (K b : ℕ) (y : ExtOrd) :
    encode S K b y ∈ ExtOrd.codedAlphabet (S.card + b) K :=
  reserve_mem_codedAlphabet (canonicalNormalizer_mem_codedAlphabet le_rfl y) b

/-- Exact readback before taking any maximum with the old witness. -/
theorem decode_encode (S : Finset Ordinal.{0}) {K b : ℕ} {y : ExtOrd}
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) :
    canonicalDecoder S K (release b (encode S K b y)) = y := by
  rw [encode, release_reserve, canonicalDecoder_canonicalNormalizer hy]

/-- Every nonbottom tracked target really is placed beyond the reserved blocks. -/
theorem encode_ge_floor (S : Finset Ordinal.{0}) {K b : ℕ} {y : ExtOrd}
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) (hyb : y ≠ ⊥) :
    ofOrd (Ordinal.omega0 * b) ≤ encode S K b y := by
  by_contra hn
  have he := decode_encode (K := K) (b := b) S hy
  rw [release_eq_bot_of_lt (not_le.mp hn), canonicalDecoder_bot] at he
  exact hyb he.symm

/-- Join a clipped old witness to the new decoder. The join uses existing normalized
witness closure; its decoder is precomposed only with the exact source inverse. -/
noncomputable def extend (S : Finset Ordinal.{0}) (K b : ℕ)
    (σ : ExtOrd → ExtOrd) (γ : ExtOrd) (x : ExtOrd) : ExtOrd :=
  max (min (σ x) γ) (canonicalDecoder S K (release b x))

/-- The extension is globally faithful, including the higher-threshold bottom clauses. -/
theorem extend_witness (S : Finset Ordinal.{0}) {K b : ℕ}
    {σ : ExtOrd → ExtOrd} {γ : ExtOrd}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ) :
    Witness (gTop K) (extend S K b σ γ) :=
  (FreeDiagonal.clip_witness hσ hγ).max
    (witness_release (isStepShifter_canonicalDecoder (S := S) (K := K)).normalizedWitness b)

/-- Every value before the tail remains exactly the old value capped at `γ`. -/
theorem extend_before (S : Finset Ordinal.{0}) {K b : ℕ}
    {σ : ExtOrd → ExtOrd} {γ x : ExtOrd} (hx : x < ofOrd (Ordinal.omega0 * b)) :
    extend S K b σ γ x = min (σ x) γ := by
  rw [extend, release_eq_bot_of_lt hx, canonicalDecoder_bot, max_bot_right]

/-- New high targets are read literally, with no restriction on their finite part.
Bottom is allowed when the cap is bottom; top is handled by its proper code. -/
theorem extend_encode (S : Finset Ordinal.{0}) {K b : ℕ}
    {σ : ExtOrd → ExtOrd} {γ y : ExtOrd}
    (hy : y = ⊥ ∨ y = ⊤ ∨ ∃ α ∈ S, y = ofOrd α) (hγy : γ ≤ y) :
    extend S K b σ γ (encode S K b y) = y := by
  rw [extend, encode, release_reserve, canonicalDecoder_canonicalNormalizer hy]
  exact max_eq_right ((min_le_right _ _).trans hγy)

/-- The proposed new source map preserves output caps on every pair of sources
agreeing below an interior source cut. Nothing requires the old map to attain `γ`. -/
theorem extend_cap_agreement (S : Finset Ordinal.{0}) {K b : ℕ}
    {σ : ExtOrd → ExtOrd} {γ a x y : ExtOrd}
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ)
    (ha : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hxy : min x a = min y a) :
    min (extend S K b σ γ x) γ = min (σ y) γ :=
  CapFirstScalar.map_cap_agreement_of_clipped_prefix hσ.mono
    (extend_witness S hσ hγ).mono
    (fun _ hz => extend_before S (hz.trans_lt ha)) hxy hactive

end VaughtConjecture.Knight.PaddedSourceDecoder

namespace VaughtConjecture.Knight.RelativePrefixEncoding

open Transform Value ExtOrd SharpWitnessComposition SourceBlockPadding




section FiniteInventory

variable {X : Type*} [Fintype X]

open Classical in
/-- High occurrences are retained individually when counting the budget. -/
noncomputable def highCells (p : X → ExtOrd) (γ : ExtOrd) : Finset X :=
  Finset.univ.filter (fun d => γ < p d)

open Classical in
/-- Only high proper values need tracking; zero guarantees bottom reflection. -/
noncomputable def inventory (p : X → ExtOrd) (γ : ExtOrd) : Finset Ordinal.{0} :=
  insert 0 ((highCells p γ).image (fun d => ordOf (p d)))

theorem tracked_high (p : X → ExtOrd) (γ : ExtOrd) (d : X) (hd : γ < p d) :
    p d = ⊥ ∨ p d = ⊤ ∨ ∃ α ∈ inventory p γ, p d = ofOrd α := by
  classical
  rcases ExtOrd.cases (p d) with h | h | ⟨α, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨α, Finset.mem_insert_of_mem ?_, h⟩)
    exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩,
      by rw [h, ordOf_ofOrd]⟩

end FiniteInventory

end VaughtConjecture.Knight.RelativePrefixEncoding

namespace VaughtConjecture.Knight.AlignedCutJoin

open Transform Value ExtOrd SharpWitnessComposition

/-- Bounded commutation is closed under pointwise maximum. The above-grade
bottom clause of a faithful witness is deliberately not asserted here. -/
theorem bounded_max {K : ℕ} {f g : ExtOrd → ExtOrd}
    (hf : BoundedMap K f) (hg : BoundedMap K g) :
    BoundedMap K (fun x => max (f x) (g x)) where
  bot := by rw [hf.bot, hg.bot, max_self]
  mono := fun _ _ h => max_le_max (hf.mono h) (hg.mono h)
  comm x k i hk hi := by
    have hm : Monotone (fun y => extVisibilityReplace y k i) := fun _ _ h => evr_mono h hi
    rw [hf.comm x k i hk hi, hg.comm x k i hk hi, hm.map_max]

/-- A scalar tail gated at a visible output cap. It need not be faithful above
the grade bound, so its consumer repairs actual source blocks instead. -/
noncomputable def above (γ : ExtOrd) (f : ExtOrd → ExtOrd) (y : ExtOrd) : ExtOrd :=
  if y ≤ γ then ⊥ else f y

theorem above_of_le {γ y : ExtOrd} {f : ExtOrd → ExtOrd} (hy : y ≤ γ) :
    above γ f y = ⊥ := ite_eq_left hy

theorem above_of_gt {γ y : ExtOrd} {f : ExtOrd → ExtOrd} (hy : γ < y) :
    above γ f y = f y := ite_eq_right (not_le.mpr hy)

theorem above_bounded {K : ℕ} {γ : ExtOrd} {f : ExtOrd → ExtOrd}
    (hf : BoundedMap K f) (hγ : SelfVis K γ) : BoundedMap K (above γ f) where
  bot := above_of_le bot_le
  mono := by
    intro x y hxy
    by_cases hx : x ≤ γ
    · rw [above_of_le hx]; exact bot_le
    · have hy : γ < y := (not_le.mp hx).trans_le hxy
      rw [above_of_gt (not_le.mp hx), above_of_gt hy]
      exact hf.mono hxy
  comm x k i hk hi := by
    by_cases hx : x ≤ γ
    · rw [above_of_le hx, above_of_le ((replace_le_visible_cut_iff hγ hk hi).mpr hx),
        extVisibilityReplace_bot]
    · rw [above_of_gt (not_le.mp hx),
        above_of_gt (replace_gt_visible_cut hγ hk (not_le.mp hx))]
      exact hf.comm x k i hk hi

/-- The old source prefix and the new output tail are separate inputs. -/
noncomputable def paste {X : Type*} (s p : X → ExtOrd) (a : ExtOrd)
    (v : ExtOrd → ExtOrd) (d : X) : ExtOrd := max (min (s d) a) (v (p d))

section Scalar

variable {X : Type*} {s p : X → ExtOrd} {a γ : ExtOrd} {v : ExtOrd → ExtOrd}
  (hlow : ∀ d, p d ≤ γ → v (p d) = ⊥)
  (hhigh : ∀ d, γ < p d → a < v (p d))
  (halign : ∀ d, γ < p d → a ≤ s d)

include hlow in
theorem paste_of_le (d : X) (hd : p d ≤ γ) : paste s p a v d = min (s d) a := by
  rw [paste, hlow d hd, max_bot_right]

include hhigh in
theorem paste_of_gt (d : X) (hd : γ < p d) : paste s p a v d = v (p d) := by
  exact max_eq_right ((min_le_right _ _).trans (hhigh d hd).le)

include hlow hhigh halign in
/-- Every old source cut is preserved, even when the old output witness
identifies distinct source values. -/
theorem paste_cap (d : X) : min (paste s p a v d) a = min (s d) a := by
  by_cases hd : p d ≤ γ
  · rw [paste_of_le hlow d hd, min_assoc, min_self]
  · have hgt := not_le.mp hd
    rw [paste_of_gt hhigh d hgt, min_eq_right (hhigh d hgt).le,
      min_eq_right (halign d hgt)]

include hlow hhigh halign in
/-- This lattice identity is where the alignment hypothesis is used. It
identifies the actual capped target at every controller, not just global caps. -/
theorem paste_read (hv : Monotone v) (d c : X) :
    max (min (min (s d) (s c)) a) (v (min (p d) (p c))) =
      min (paste s p a v d) (paste s p a v c) := by
  rw [hv.map_min]
  by_cases hd : p d ≤ γ <;> by_cases hc : p c ≤ γ
  · rw [hlow d hd, hlow c hc, min_self, max_bot_right,
      paste_of_le hlow d hd, paste_of_le hlow c hc]
    simpa only [min_self] using (min_min_min_comm (s d) a (s c) a).symm
  · have hc' := not_le.mp hc
    rw [hlow d hd, min_bot_left, max_bot_right,
      paste_of_le hlow d hd, paste_of_gt hhigh c hc',
      min_eq_left ((min_le_right _ _).trans (hhigh c hc').le),
      min_assoc, min_eq_right (halign c hc')]
  · have hd' := not_le.mp hd
    rw [hlow c hc, min_bot_right, max_bot_right,
      paste_of_gt hhigh d hd', paste_of_le hlow c hc,
      min_eq_right ((min_le_right _ _).trans (hhigh d hd').le)]
    rw [min_comm (s d) (s c), min_assoc, min_eq_right (halign d hd')]
  · have hd' := not_le.mp hd
    have hc' := not_le.mp hc
    rw [paste_of_gt hhigh d hd', paste_of_gt hhigh c hc']
    exact max_eq_right ((min_le_right _ _).trans
      (le_min (hhigh d hd').le (hhigh c hc').le))

end Scalar

section Scheme

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

/-- Convert bounded read equations into an actual faithful locality using
only the block-bottom condition at the controller's actual source occurrences. -/
theorem locality_of_bounded_read {q : D.below BJ → ExtOrd}
    (hb : RowBlockBottom sem BJ q) (c : D.below BJ) {f : ExtOrd → ExtOrd}
    (hf : BoundedMap (D.grade c.1) f)
    (hread : ∀ d, f (sem.E c.1 d) = min (q (CellScheme.below.incl c d)) (q c)) :
    TransformsTo (fun d : D.below (D.cell c.1) => D.grade d.1) (sem.E c.1)
      (fun d => min (q (CellScheme.below.incl c d)) (q c)) := by
  classical
  let _ := Fintype.ofFinite (D.below (D.cell c.1))
  let sources := Finset.univ.image (sem.E c.1)
  have hbs : BlockBottom sources f := by
    intro x hx y hy hxy hz
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hy
    rw [hread d] at hz
    rw [hread e]
    exact hb c d e hxy hz
  obtain ⟨τ, hτ, hr⟩ := (hf.interpolate_iff_source_blocks sources).mpr hbs
  apply hτ.transformsTo
  intro d
  have hd : D.grade d.1 ≤ D.grade c.1 := d.2.2
  rw [gTop_of_le hd, min_top_right,
    hr _ (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩), hread d]

/-- The pasted labelling is lawful on the original scheme. No shared
availability selector, injective decoder, or pre-existing completion is assumed. -/
theorem paste_respects {s p : D.below BJ → ExtOrd} {K : ℕ} {a γ : ExtOrd}
    {v : ExtOrd → ExtOrd}
    (hs : RespectsSemanticsBelow sem BJ s) (hp : RespectsSemanticsBelow sem BJ p)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (ha : SelfVis K a) (hab : a ≠ ⊥) (hv : BoundedMap K v)
    (hlow : ∀ d, p d ≤ γ → v (p d) = ⊥)
    (hhigh : ∀ d, γ < p d → a < v (p d))
    (halign : ∀ d, γ < p d → a ≤ s d) :
    RespectsSemanticsBelow sem BJ (paste s p a v) := by
  have hbottom : RowBlockBottom sem BJ (paste s p a v) :=
    rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects hs)
      (bottom_pattern_of_cap_agreement hab (paste_cap hlow hhigh halign))
  obtain ⟨Cs⟩ := exists_localCharts hs
  obtain ⟨Cp⟩ := exists_localCharts hp
  refine ⟨?_, ?_, ?_⟩
  · intro d
    have hpv : SelfVis (D.grade d.1) (v (p d)) := by
      have h := hv.comm (p d) (D.grade d.1) (D.grade d.1) (hK d) le_rfl
      rw [← hp.orderly d] at h
      exact h.symm
    exact (selfVis_max (selfVis_min (hs.orderly d).symm (ha.mono (hK d))) hpv).symm
  · intro c
    apply locality_of_bounded_read hbottom c
      (bounded_max (boundedMap_of_witness
        (FreeDiagonal.clip_witness (Cs.witness c) (ha.mono (hK c))))
        (hv.comp_witness (Cp.witness c) (hK c)))
    intro d
    change max (min (Cs.shift c (sem.E c.1 d)) a) (v (Cp.shift c (sem.E c.1 d))) = _
    rw [Cs.read c d, Cp.read c d]
    exact paste_read hlow hhigh halign hv.mono _ _
  · intro d c hscope hgrade
    by_cases h : v (p d) ≤ min (s d) a
    · obtain ⟨e, he, hde⟩ := hs.availability d c hscope hgrade
      refine ⟨e, he, ?_⟩
      change max (min (s d) a) (v (p d)) ≤ max (min (s e) a) (v (p e))
      rw [max_eq_left h]
      exact (min_le_min hde le_rfl).trans (le_max_left _ _)
    · obtain ⟨e, he, hde⟩ := hp.availability d c hscope hgrade
      refine ⟨e, he, ?_⟩
      change max (min (s d) a) (v (p d)) ≤ max (min (s e) a) (v (p e))
      rw [max_eq_right (not_le.mp h).le]
      exact (hv.mono hde).trans (le_max_right _ _)

end Scheme

end VaughtConjecture.Knight.AlignedCutJoin

namespace VaughtConjecture.Knight.AlignedCutEncoding

open Transform Value ExtOrd SharpWitnessComposition AlignedCutJoin

private theorem tail_witness (S : Finset Ordinal.{0}) (K b : ℕ) :
    Witness (gTop K) (PaddedSourceDecoder.encode S K b) := by
  induction b with
  | zero => exact (isStepShifter_canonicalNormalizer (S := S) (K := K)).normalizedWitness
  | succ b ih =>
    exact ih.comp_of_bottom_reflecting (SourceBlockPadding.pad_step K).normalizedWitness
      le_rfl SourceBlockPadding.pad_reflects_bottom

section Finite

variable {X : Type*} [Fintype X]

/-- Old low sources are retained; new high outputs receive separate codes. -/
noncomputable def encode (s p : X → ExtOrd) (K b : ℕ) (a γ : ExtOrd) : X → ExtOrd :=
  AlignedCutJoin.paste s p a
    (above γ (PaddedSourceDecoder.encode (RelativePrefixEncoding.inventory p γ) K b))

theorem encode_of_le (s p : X → ExtOrd) (K b : ℕ) (a γ : ExtOrd)
    (d : X) (hd : p d ≤ γ) : encode s p K b a γ d = min (s d) a :=
  paste_of_le (fun _ h => above_of_le h) d hd

private theorem high_gap (p : X → ExtOrd) {K b : ℕ} {a γ : ExtOrd}
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (d : X) (hd : γ < p d) :
    a < above γ (PaddedSourceDecoder.encode (RelativePrefixEncoding.inventory p γ) K b)
      (p d) := by
  rw [above_of_gt hd]
  exact hroom.trans_le (PaddedSourceDecoder.encode_ge_floor _
    (RelativePrefixEncoding.tracked_high p γ d hd) (ne_of_gt (bot_le.trans_lt hd)))

theorem encode_of_gt (s p : X → ExtOrd) {K b : ℕ} {a γ : ExtOrd}
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (d : X) (hd : γ < p d) :
    encode s p K b a γ d =
      PaddedSourceDecoder.encode (RelativePrefixEncoding.inventory p γ) K b (p d) := by
  rw [encode, paste_of_gt (high_gap p hroom) d hd, above_of_gt hd]

/-- Capped source agreement is derived from the alignment of raised outputs. -/
theorem encode_cap (s p : X → ExtOrd) {K b : ℕ} {a γ : ExtOrd}
    (hroom : a < ofOrd (Ordinal.omega0 * b))
    (halign : ∀ d, γ < p d → a ≤ s d) (d : X) :
    min (encode s p K b a γ d) a = min (s d) a :=
  AlignedCutJoin.paste_cap (fun _ h => above_of_le h) (high_gap p hroom) halign d

/-- Literal readback uses no inverse or identity-prefix hypothesis on `σ`.
Only the new high outputs are inserted into the decoder's finite inventory. -/
theorem decode_encode (s p : X → ExtOrd) {K b : ℕ} {a γ : ExtOrd}
    {σ : ExtOrd → ExtOrd} (hσ : Monotone σ)
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hread : ∀ d, min (σ (s d)) γ = min (p d) γ) (d : X) :
    PaddedSourceDecoder.extend (RelativePrefixEncoding.inventory p γ) K b σ γ
      (encode s p K b a γ d) = p d := by
  by_cases hd : p d ≤ γ
  · rw [encode_of_le s p K b a γ d hd,
      PaddedSourceDecoder.extend_before _ ((min_le_right _ _).trans_lt hroom),
      hσ.map_min, min_assoc, min_eq_right hactive, hread d, min_eq_left hd]
  · rw [encode_of_gt s p hroom d (not_le.mp hd)]
    exact PaddedSourceDecoder.extend_encode _
      (RelativePrefixEncoding.tracked_high p γ d (not_le.mp hd)) (not_le.mp hd).le

end Finite

/-- The new codes form a lawful face on the original rows, not just a scalar
solution of the prescribed equations. Source block repair supplies locality. -/
theorem encode_respects
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} [Fintype (D.below BJ)]
    {s p : D.below BJ → ExtOrd} {K b : ℕ} {a γ : ExtOrd}
    (hs : RespectsSemanticsBelow sem BJ s) (hp : RespectsSemanticsBelow sem BJ p)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (ha : SelfVis K a) (hab : a ≠ ⊥) (hγ : SelfVis K γ)
    (hroom : a < ofOrd (Ordinal.omega0 * b))
    (halign : ∀ d, γ < p d → a ≤ s d) :
    RespectsSemanticsBelow sem BJ (encode s p K b a γ) :=
  paste_respects hs hp hK ha hab
    (above_bounded (boundedMap_of_witness (tail_witness _ K b)) hγ)
    (fun _ h => above_of_le h) (high_gap p hroom) halign

/-- Decode an independently constructed coded lift. Agreement at the source
cut preserves every ambient output cap, and positive-cap transport proves
respect of the output without assuming faithful transformations compose. -/
theorem decode_lift
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : Finset ι × ℕ} {X : Type*} [Fintype X]
    (s : D.below BJ → ExtOrd) (p : X → ExtOrd) (incl : X → D.below BJ)
    {r q : D.below BJ → ExtOrd} {K b : ℕ} {a γ : ExtOrd} {σ : ExtOrd → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) (hq : RespectsSemanticsBelow sem BJ q)
    (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K)
    (hσ : Witness (gTop K) σ) (hγ : SelfVis K γ) (hγb : γ ≠ ⊥)
    (hroom : a < ofOrd (Ordinal.omega0 * b)) (hactive : γ ≤ σ a)
    (hsource : ∀ d, min (r d) a = min (s d) a)
    (hambient : ∀ d, min (σ (s d)) γ = min (q d) γ)
    (hface : ∀ d, min (p d) γ = min (q (incl d)) γ)
    (hlit : ∀ d, r (incl d) = encode (s ∘ incl) p K b a γ d) :
    ∃ q' : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ q' ∧
      (∀ d, q' (incl d) = p d) ∧ ∀ d, min (q' d) γ = min (q d) γ := by
  let S := RelativePrefixEncoding.inventory p γ
  let τ := PaddedSourceDecoder.extend S K b σ γ
  have hτ : Witness (gTop K) τ := PaddedSourceDecoder.extend_witness S hσ hγ
  have hag d : min (τ (r d)) γ = min (q d) γ :=
    (PaddedSourceDecoder.extend_cap_agreement S hσ hγ hroom hactive (hsource d)).trans
      (hambient d)
  refine ⟨fun d => τ (r d),
    map_respects_of_positive_cap_agreement hr hq hK (boundedMap_of_witness hτ) hγb hag,
    ?_, hag⟩
  intro d
  change PaddedSourceDecoder.extend S K b σ γ (r (incl d)) = p d
  rw [hlit d]
  exact decode_encode (s ∘ incl) p hσ.mono hroom hactive
    (fun e => (hambient (incl e)).trans (hface e).symm) d

end VaughtConjecture.Knight.AlignedCutEncoding
