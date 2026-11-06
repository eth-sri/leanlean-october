
import VaughtConjecture.Knight.PointwiseLabels
import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.CappedLocalityRecoding
import VaughtConjecture.Knight.SemScheme

/-! # A shared finite source code at arbitrary bounded grades

Every lawful finite profile has a coded profile respecting the unchanged
semantics, with exact decoding and a direct outgoing faithful witness.
The codebook may contain additional values, so different profiles and
their restrictions can share it. Literal top receives a proper cap code.

Incoming locality uses `coded_locality_S` and the Cap Lemma, never general
transitivity. This constructs source profiles over existing lower domains,
not new controllers or the cross-localities between added rows. Decoding
an arbitrary lawful coded labelling is not asserted to preserve respect.
-/

namespace VaughtConjecture.Knight.SourceCode

open  Transform Value ExtOrd

/-- All proper values that must decode exactly are listed in the codebook. -/
def Supported (S : Finset Ordinal₀) (x : ExtOrd) :=
  ∀ v, x = ofOrd v → v ∈ S

theorem supported_bot S : Supported S ⊥ := by
  intro v h
  exact False.elim ((ofOrd_ne_bot v) h.symm)

theorem Supported.keyed {S} {x}
    (h : Supported S x) K : Keyed K S x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact keyed_bot _ _
  · exact keyed_top _ _
  · exact keyed_of_mem _ _ (h v rfl)

/-- One common codebook and grade bound; top is coded in the fresh cap block. -/
noncomputable def encode (K : ℕ) (S : Finset Ordinal₀) : LabelMap
  | ⊥ => ⊥
  | some ⊤ => ofOrd (capCode K S)
  | some (some v) => ofOrd (code K S v)

theorem encode_eq_cap K S x :
    encode K S x = min (encT K S x) (ofOrd (capCode K S)) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact (min_eq_left bot_le).symm
  · exact (min_eq_right le_top).symm
  · exact (min_eq_left (ofOrd_le_ofOrd.mpr (code_le_capCode K S v))).symm

theorem encode_coded K S x :
    IsCodedLabel K (encode K S x) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact Or.inl rfl
  · exact capCode_isCoded _ _
  · exact code_isCoded _ _ _

theorem encode_selfVis K S {k} (hk : k ≤ K)
    {x} (hx : SelfVis k x) : SelfVis k (encode K S x) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact selfVis_bot
  · exact (capCode_selfVis _ _).mono hk
  · exact code_selfVis _ _ (selfVis_ofOrd_iff.mp hx) hk

theorem encode_le K S {x y}
    (hx : Supported S x) (hy : Supported S y) (hxy : x ≤ y) :
    encode K S x ≤ encode K S y := by
  rw [encode_eq_cap, encode_eq_cap]
  exact min_le_min (encT_le_keyed _ _ (hx.keyed K) (hy.keyed K) hxy) le_rfl

/-- The decoder reads every supported label literally, including top. -/
theorem decode_encode K S {x}
    (hx : Supported S x) : shift K S ⊤ (encode K S x) = x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact shift_bot _ _ _
  · exact shift_capCode _ _ _
  · exact shift_code _ _ _ (hx v rfl)

/-- A direct outgoing witness for the whole coded profile. This does not
compose an incoming witness with a decoder. -/
theorem outgoing {X : Type*} (grade : X → ℕ) (p : X → ExtOrd) (K : ℕ)
    (S : Finset Ordinal₀) (hK : BoundedBy grade K) (hS : ∀ d, Supported S (p d))
    {ρ : ExtOrd} (hρ : SelfVis K ρ) :
    TransformsTo grade (fun d => encode K S (p d)) (fun d => min (p d) ρ) := by
  have h := transformsTo_of_shift K S ⊤ grade (extVisibilityReplace_top)
    (fun _ _ => le_top) (fun d => encode K S (p d)) hρ
  convert h using 1
  funext d
  rw [ite_eq_left (hK d), decode_encode K S (hS d)]

section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ  : GradedIndex ι} {p : BelowLabels D BJ}

/-- The coded profile respects every unchanged inherited row. The codebook
may contain other profiles' values; only inclusion of this one's is required. -/
theorem respectsBelow K S (hK : BJ.2 ≤ K)
    (hp : RespectsSemanticsBelow sem BJ p) (hS : ∀ d, Supported S (p d)) :
    RespectsSemanticsBelow sem BJ (fun d => encode K S (p d)) where
  orderly d := (encode_selfVis K S (d.2.2.trans hK) (hp.orderly d).symm).symm
  locality c := by
    let _ : Fintype (D.belowCell c.1) := Fintype.ofFinite _
    have he := coded_locality_S (fun d : D.belowCell c.1 => D.grade d.1)
      (sem.E c.1) (fun d => p (CellScheme.below.incl c d)) ⟨c.1, GradedLe.refl _⟩
      (fun d => d.2.2) (fun d => (hp.orderly _).symm) (hp.locality c)
      (c.2.2.trans hK) S
      (fun d => keyed_min _ _ ((hS (CellScheme.below.incl c d)).keyed K) ((hS c).keyed K))
    rw [show CellScheme.below.incl c ⟨c.1, GradedLe.refl _⟩ = c from rfl] at he
    have ht := he.cap (fun d => (d.2.2.trans c.2.2).trans hK) (capCode_selfVis K S)
    convert ht using 1
    funext d
    rw [encode_eq_cap, encode_eq_cap,
      encT_min_keyed _ _ ((hS (CellScheme.below.incl c d)).keyed K) ((hS c).keyed K),
      min_min_min_comm, min_self]
  availability d e hs hg := by
    obtain ⟨f, hf, hle⟩ := hp.availability d e hs hg
    exact ⟨f, hf, encode_le K S (hS d) (hS f) hle⟩


