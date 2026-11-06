/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedLocalityRecoding
public import VaughtConjecture.Knight.SemScheme

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

@[expose] public section

namespace VaughtConjecture.Knight.SourceCode

open AmalgamationPlan Transform Value ExtOrd

/-- All proper values that must decode exactly are listed in the codebook. -/
def Supported (S : Finset Ordinal.{0}) (x : ExtOrd) : Prop :=
  ∀ v, x = ofOrd v → v ∈ S

theorem supported_bot (S : Finset Ordinal.{0}) : Supported S ⊥ := by
  intro v h
  exact False.elim ((ofOrd_ne_bot v) h.symm)


theorem Supported.keyed {S : Finset Ordinal.{0}} {x : ExtOrd}
    (h : Supported S x) (K : ℕ) : Keyed K S x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact keyed_bot _ _
  · exact keyed_top _ _
  · exact keyed_of_mem _ _ (h v rfl)

/-- One common codebook and grade bound; top is coded in the fresh cap block. -/
noncomputable def encode (K : ℕ) (S : Finset Ordinal.{0}) : ExtOrd → ExtOrd
  | ⊥ => ⊥
  | some ⊤ => ofOrd (capCode K S)
  | some (some v) => ofOrd (code K S v)

theorem encode_eq_cap (K : ℕ) (S : Finset Ordinal.{0}) (x : ExtOrd) :
    encode K S x = min (encT K S x) (ofOrd (capCode K S)) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact (min_eq_left bot_le).symm
  · exact (min_eq_right le_top).symm
  · exact (min_eq_left (ofOrd_le_ofOrd.mpr (code_le_capCode K S v))).symm

theorem encode_coded (K : ℕ) (S : Finset Ordinal.{0}) (x : ExtOrd) :
    IsCodedLabel K (encode K S x) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact Or.inl rfl
  · exact capCode_isCoded _ _
  · exact code_isCoded _ _ _

theorem encode_selfVis (K : ℕ) (S : Finset Ordinal.{0}) {k : ℕ} (hk : k ≤ K)
    {x : ExtOrd} (hx : SelfVis k x) : SelfVis k (encode K S x) := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact selfVis_bot _
  · exact (capCode_selfVis _ _).mono hk
  · exact code_selfVis _ _ (selfVis_ofOrd_iff.mp hx) hk

theorem encode_le (K : ℕ) (S : Finset Ordinal.{0}) {x y : ExtOrd}
    (hx : Supported S x) (hy : Supported S y) (hxy : x ≤ y) :
    encode K S x ≤ encode K S y := by
  rw [encode_eq_cap, encode_eq_cap]
  exact min_le_min (encT_le_keyed _ _ (hx.keyed K) (hy.keyed K) hxy) le_rfl

/-- The decoder reads every supported label literally, including top. -/
theorem decode_encode (K : ℕ) (S : Finset Ordinal.{0}) {x : ExtOrd}
    (hx : Supported S x) : shift K S ⊤ (encode K S x) = x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨v, rfl⟩
  · exact shift_bot _ _ _
  · exact shift_capCode _ _ _
  · exact shift_code _ _ _ (hx v rfl)

/-- A direct outgoing witness for the whole coded profile. This does not
compose an incoming witness with a decoder. -/
theorem outgoing {X : Type*} (grade : X → ℕ) (p : X → ExtOrd) (K : ℕ)
    (S : Finset Ordinal.{0}) (hK : ∀ d, grade d ≤ K) (hS : ∀ d, Supported S (p d))
    {ρ : ExtOrd} (hρ : SelfVis K ρ) :
    TransformsTo grade (fun d => encode K S (p d)) (fun d => min (p d) ρ) := by
  have h := transformsTo_of_shift K S ⊤ grade (extVisibilityReplace_top _ _)
    (fun _ _ => le_top) (fun d => encode K S (p d)) hρ
  convert h using 1
  funext d
  rw [ite_eq_left (hK d), decode_encode K S (hS d)]

section Semantics

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ CI : Finset ι × ℕ} {p : D.below BJ → ExtOrd}

/-- The coded profile respects every unchanged inherited row. The codebook
may contain other profiles' values; only inclusion of this one's is required. -/
theorem respectsBelow (K : ℕ) (S : Finset Ordinal.{0}) (hK : BJ.2 ≤ K)
    (hp : RespectsSemanticsBelow sem BJ p) (hS : ∀ d, Supported S (p d)) :
    RespectsSemanticsBelow sem BJ (fun d => encode K S (p d)) where
  orderly d := (encode_selfVis K S (d.2.2.trans hK) (hp.orderly d).symm).symm
  locality c := by
    let _ : Fintype (D.below (D.cell c.1)) := Fintype.ofFinite _
    have he := coded_locality_S (fun d : D.below (D.cell c.1) => D.grade d.1)
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

end Semantics

end VaughtConjecture.Knight.SourceCode
