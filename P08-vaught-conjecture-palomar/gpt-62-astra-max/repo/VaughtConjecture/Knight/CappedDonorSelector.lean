/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteOrbitEmbedding
public import VaughtConjecture.Knight.SourceBlockPadding
public import VaughtConjecture.Knight.TopSupport

/-! # The coherent capped-donor selector (notes32 §§1–3, audit5 §§1–2)

The reviewer's notes32 (`/home/freer/work/vc-notes/audit-notes1/`
`notes32_coherent_capped_receiving.md`, audit5): a **whole lawful capped section of the donor**,
determined by one actual private row.

**Reference data** (`Ref`): a request scheme `P` (arity `nP + 1 < N`) with a lawful donor
labelling `p`, every proper donor label of the form `μ i + k` with `k < N` over the finite list
`μ` of distinct non-successor blocks (`p_code`; the block list may be empty); a private scheme
`C` of arity `J ≥ N` — cells above grade `N` are retained — containing an **acquisition face**
`C₀` of arity `N` on which the grade-`N` cap `cap` is full-scope (its index is `(C₀, N)`; its
row, the cap's lower domain, is not enlarged by the larger context), with one representative
`ref i` per block inside `C₀`; the actual private labelling `vact`, lawful,
positive at the cap, reading `μ i + off i` at the representatives and satisfying the
**endpoint margin** `μ i + N < vact cap` for every block (the strengthened bound (1)); and the
common face, a lower set `(A, KA)` of `P` identified with a lower set `(A', KA)` of `C` inside
`C₀` (literally common: the identification transports restricted lawfulness, `face_respects`; see
`Knight/CappedDonorFace.lean` for its derivation from literal face restrictions), on which the
actual tuple has the donor's type (`face_actual`).

Everything the selector reads lives on the **cap's lower domain** `Low = C.below (C₀, N)`,
the cells of `C₀` of grade at most `N`: the cap itself, the representatives and the face.
Sections are therefore labellings of `Low`, lawful for the restricted semantics at the cap; a
section on a larger cutoff restricts to one (`Knight/CappedDonorReceiving.lean`).

**The selector.**  For any labelling `v` of `Low`,

    cut v   = min (v cap) (max_i R_{N,N} (v (ref i)))                      (5)
    sel v d = ⊥ / min (R_{N,k} (v (ref i))) (cut v) / cut v                (6)

according as `p d` is bottom / proper `μ i + k` / top.  Both commute with every `N`-visible cap
(`cut_min`, `sel_min`) and with clipping the cap coordinate (`cut_clip`, `sel_clip`).

**The capped-donor lemma** (`Active.sel_respects`, `Active.sel_face`): for every *active* lawful
`v` (positive cap and references, bottom at the donor-bottom face cells), `sel v` is lawful on
the unchanged `P` and `sel v = v ∧ cut v` on the common face.  The proof is the notes32 one,
from the actual reference row and donor lawfulness, not from an assumed lawful image:

* the actual row `E = C.rows.E cap` and its exact normalized witness read each representative's
  source as `ω·b i + off i` (`srcE_ref`), in the block order of `μ` (`srcBlock_strict`); at a
  proper face cell the source is the replacement of the representative's source
  (`srcE_face_proper`, invisible-image rigidity), at a donor-top face cell it exceeds every
  `N`-endpoint (`srcE_face_top`, from the margin);
* the coded labelling `e = interpolate ∘ p` (`FiniteOrbitEmbedding`) is lawful on `P` and reads
  `ω·(b+1) + k` at proper cells and the common endpoint `L` at donor-top cells;
* for arbitrary lawful `v`, the witness of `v` at `cap` precomposed with source unpadding is a
  bounded map through `N` whose image of `e` is exactly `sel v` (`sel_eq_read`); the source-block
  criterion (`map_respects_iff_rowBlockBottom` with the same-pattern lemma) gives lawfulness.

**The empty block list** is handled explicitly (`sel_of_isEmpty`): with no proper donor label
the selector is identically bottom, which is lawful (`RespectsSemantics.bot`), and no
representative is required.

At the actual context `sel vact = p ∧ cut vact` with `cut vact = max_i (μ i + N)`
(`cut_actual`, `sel_actual`). -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd SharpWitnessComposition AmalgamationPlan

theorem Witness.comm_gTop {N} {τ} (hτ : Witness (gTop N) τ) x
    {i} (hi : i ≤ N) :
    τ (extVisibilityReplace x N i) = extVisibilityReplace (τ x) N i :=
  hτ.clause5 x N (by rw [gTop_of_le le_rfl]; exact le_top) i hi

namespace CappedDonor

/-- **The reference data** of notes32 §1: request scheme, donor, private scheme with cap and
representatives, the actual private labelling with the endpoint margin, and the common face. -/
structure Ref (I : Type*) [Fintype I] (nP N J : ℕ) (P : SemScheme (nP + 1)) (C : SemScheme J)
    where
  /-- The request arity is below the threshold. -/
  arity_lt : nP + 1 < N
  /-- The private context has arity at least the threshold. -/
  N_le : N ≤ J
  /-- The requested blocks. -/
  μ : I → Ordinal.{0}
  μ_limit : ∀ i, limitPart (μ i) = μ i
  μ_inj : Function.Injective μ
  /-- One representative per block. -/
  ref : I → Cell C.scheme
  /-- The representative offsets. -/
  off : I → ℕ
  off_lt : ∀ i, off i < N
  /-- The acquisition face inside the private context. -/
  C₀ : Finset (Fin J)
  /-- The private cap: a cell of grade `N`, full-scope on the acquisition face. -/
  cap : Cell C.scheme
  cap_cell : C.scheme.cell cap = (C₀, N)
  /-- The representatives lie inside the acquisition face. -/
  ref_scope : ∀ i, C.scheme.scope (ref i) ⊆ C₀
  /-- The actual private labelling. -/
  vact : Cell C.scheme → ExtOrd
  vact_respects : RespectsSemantics C.rows vact
  vact_ref : ∀ i, vact (ref i) = ofOrd (μ i + off i)
  /-- The actual cap is positive. -/
  cap_pos : ⊥ < vact cap
  /-- The endpoint margin (1). -/
  margin : ∀ i, ofOrd (μ i + N) < vact cap
  /-- The donor labelling. -/
  p : Cell P.scheme → ExtOrd
  p_respects : RespectsSemantics P.rows p
  /-- Every proper donor label is a requested block plus an offset below the threshold. -/
  p_code : ∀ d, p d ≠ ⊥ → p d ≠ ⊤ → ∃ (i : I) (k : ℕ), k < N ∧ p d = ofOrd (μ i + k)
  /-- The common face (the literal root) as a lower set of each scheme: visible faces `A`, `A'`
  and the root grade `KA` (at most the size of either face; `KA = 0` is the empty root). -/
  A : Finset (Fin (nP + 1))
  A' : Finset (Fin J)
  KA : ℕ
  A_mem : A ∈ P.scheme.plan
  A'_mem : A' ∈ C.scheme.plan
  KA_le_card : KA ≤ A.card
  KA_le_card' : KA ≤ A'.card
  /-- The private copy of the face lies inside the acquisition face. -/
  A'_sub : A' ⊆ C₀
  /-- The identification of the two copies of the face. -/
  face : P.scheme.below (A, KA) ≃ C.scheme.below (A', KA)
  /-- The identification preserves grades (so the portion of the face present at any cutoff is
  the same on both sides). -/
  face_grade : ∀ a, C.scheme.grade (face a).1 = P.scheme.grade a.1
  /-- The actual tuple has the donor's type on the face. -/
  face_actual : ∀ a, vact (face a).1 = p a.1
  /-- The face is literally common **at every grade**: the identification transports restricted
  lawfulness on every graded lower set `(A, k)`, `k ≤ KA`. -/
  face_respects : ∀ (k : ℕ) (hk : k ≤ KA) (r : C.scheme.below (A', k) → ExtOrd),
    RespectsSemanticsBelow C.rows (A', k) r ↔
      RespectsSemanticsBelow P.rows (A, k) (fun a => r
        ⟨(face ⟨a.1, a.2.trans ⟨Finset.Subset.refl _, hk⟩⟩).1,
          ⟨(face ⟨a.1, a.2.trans ⟨Finset.Subset.refl _, hk⟩⟩).2.1,
            (face_grade ⟨a.1, a.2.trans ⟨Finset.Subset.refl _, hk⟩⟩).trans_le a.2.2⟩⟩)

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  (R : Ref I nP N J P C)

/-! ## Basic geometry -/

theorem grade_cap : C.scheme.grade R.cap = N := congrArg Prod.snd R.cap_cell

theorem gradeP_le d : P.scheme.grade d ≤ nP + 1 :=
  (P.scheme.grade_le_card_scope d).trans (by simpa using Finset.card_le_univ (P.scheme.scope d))

theorem KA_le : R.KA ≤ nP + 1 :=
  R.KA_le_card.trans (by simpa using Finset.card_le_univ R.A)

theorem KA_lt_N : R.KA < N := R.KA_le.trans_lt R.arity_lt

theorem face_symm_grade b :
    P.scheme.grade (R.face.symm b).1 = C.scheme.grade b.1 := by
  have h := R.face_grade (R.face.symm b)
  simp_all

/-- A face cell of grade at most `k ≤ KA` as a cell of the lower set `(A, k)`. -/
def faceLift {k} (hk : k ≤ R.KA) (a : P.scheme.below (R.A, k)) : P.scheme.below (R.A, R.KA) :=
  ⟨a.1, a.2.trans ⟨Finset.Subset.refl _, hk⟩⟩

def faceLift' {k} (hk : k ≤ R.KA) (b : C.scheme.below (R.A', k)) :
    C.scheme.below (R.A', R.KA) :=
  ⟨b.1, b.2.trans ⟨Finset.Subset.refl _, hk⟩⟩

/-- **The identification at grade `k ≤ KA`**: the restriction of `face` to the lower sets
`(A, k)`, `(A', k)` — a bijection because the identification preserves grades. -/
def faceAt {k} (hk : k ≤ R.KA) : P.scheme.below (R.A, k) ≃ C.scheme.below (R.A', k) where
  toFun a := ⟨(R.face (R.faceLift hk a)).1, ⟨(R.face (R.faceLift hk a)).2.1,
    (R.face_grade (R.faceLift hk a)).trans_le a.2.2⟩⟩
  invFun b := ⟨(R.face.symm (R.faceLift' hk b)).1, ⟨(R.face.symm (R.faceLift' hk b)).2.1,
    (R.face_symm_grade (R.faceLift' hk b)).trans_le b.2.2⟩⟩
  left_inv a := by
    apply Subtype.ext
    change (R.face.symm ⟨(R.face (R.faceLift hk a)).1, _⟩).1 = a.1
    have h : (⟨(R.face (R.faceLift hk a)).1, _⟩ : C.scheme.below (R.A', R.KA)) =
        R.face (R.faceLift hk a) := rfl
    aesop
  right_inv b := by
    apply Subtype.ext
    change (R.face ⟨(R.face.symm (R.faceLift' hk b)).1, _⟩).1 = b.1
    have h : (⟨(R.face.symm (R.faceLift' hk b)).1, _⟩ : P.scheme.below (R.A, R.KA)) =
        R.face.symm (R.faceLift' hk b) := rfl
    aesop

/-- The face is literally common at every grade, through `faceAt`. -/
theorem faceAt_respects {k} (hk : k ≤ R.KA) r :
    C.rows.Lawful r ↔
      RespectsSemanticsBelow P.rows (R.A, k) (fun a => r (R.faceAt hk a)) :=
  R.face_respects k hk r

theorem finitePart_μ_add i (k : ℕ) : finitePart (R.μ i + k) = k := by
  have := finitePart_limitPart_add_nat (R.μ i) k
  rwa [R.μ_limit i] at this

/-- The representatives have grade below `N`: their actual labels are `N`-invisible. -/
theorem ref_grade_lt i : C.scheme.grade (R.ref i) < N := by
  have h : SelfVis (C.scheme.grade (R.ref i)) (R.vact (R.ref i)) :=
    (R.vact_respects.orderly (R.ref i)).symm
  rw [R.vact_ref i, selfVis_ofOrd_iff, R.finitePart_μ_add] at h
  exact h.trans_lt (R.off_lt i)

/-- The lower domain of the cap: the cells of the acquisition face of grade at most `N`. -/
abbrev Low : Type := C.scheme.RowDomain R.cap

/-- The cap in its own lower domain. -/
def capL : R.Low := ⟨R.cap, GradedLe.refl _⟩

/-- A representative in the cap's lower domain. -/
def lowRef (i : I) : R.Low := ⟨(R.ref i), by rw [R.cap_cell]; exact ⟨(R.ref_scope i), ((R.ref_grade_lt i).le)⟩⟩

/-- A face cell in the cap's lower domain. -/
def lowFace (a : P.scheme.below (R.A, R.KA)) : R.Low :=
  ⟨((R.face a).1), by rw [R.cap_cell]; exact ⟨((R.face a).2.1.trans R.A'_sub), ((R.face a).2.2.trans R.KA_lt_N.le)⟩⟩

/-- The actual reference row. -/
noncomputable abbrev srcE : R.Low → ExtOrd := C.rows.E R.cap

/-- The actual private labelling on the cap's lower domain. -/
abbrev vactL : R.Low → ExtOrd := fun d => R.vact d.1

theorem vactL_respects : C.rows.Lawful R.vactL :=
  R.vact_respects.toBelow _

/-! ## The block and offset of a proper donor label -/

/-- The block of a proper donor label. -/
noncomputable def blk d (h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤) : I :=
  (R.p_code d h.1 h.2).choose

/-- The offset of a proper donor label. -/
noncomputable def poff d (h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤) : ℕ :=
  (R.p_code d h.1 h.2).choose_spec.choose

theorem poff_lt d (h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤) : R.poff d h < N :=
  (R.p_code d h.1 h.2).choose_spec.choose_spec.1

theorem p_eq d (h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤) :
    R.p d = ofOrd (R.μ (R.blk d h) + R.poff d h) :=
  (R.p_code d h.1 h.2).choose_spec.choose_spec.2

/-! ## The selector -/

/-- The readout cap `β(v)` (5). -/
noncomputable def cut (v : R.Low → ExtOrd) : ExtOrd :=
  min (v R.capL) (Finset.univ.sup fun i => extVisibilityReplace (v (R.lowRef i)) N N)

open Classical in
/-- The capped donor section `G(v)` (6). -/
noncomputable def sel (v : R.Low → ExtOrd) (d : Cell P.scheme) : ExtOrd :=
  if h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤ then
    min (extVisibilityReplace (v (R.lowRef (R.blk d h))) N (R.poff d h)) (R.cut v)
  else if R.p d = ⊥ then ⊥ else R.cut v

theorem cut_le_cap v : R.cut v ≤ v R.capL := min_le_left _ _

theorem sel_of_bot {v} {d} (h : R.p d = ⊥) :
    R.sel v d = ⊥ := by
  unfold sel; simp_all

theorem sel_of_top {v} {d} (h : R.p d = ⊤) :
    R.sel v d = R.cut v := by
  unfold sel
  simp_all

theorem sel_of_proper {v} {d} (h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤) :
    R.sel v d =
      min (extVisibilityReplace (v (R.lowRef (R.blk d h))) N (R.poff d h)) (R.cut v) := by
  unfold sel; simp_all

theorem sel_le_cut v d : R.sel v d ≤ R.cut v := by
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · rw [R.sel_of_proper h]; simp
  by_cases hb : R.p d = ⊥
  · rw [R.sel_of_bot hb]; exact bot_le
  · rw [R.sel_of_top (not_not.mp fun ht => h ⟨hb, ht⟩)]

/-- With no requested block the selector is identically bottom. -/
theorem sel_of_isEmpty [IsEmpty I] v d : R.sel v d = ⊥ := by
  have hcut : R.cut v = ⊥ := by
    unfold cut
    rw [Finset.univ_eq_empty, Finset.sup_empty, min_bot_right]
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · exact (IsEmpty.false (R.blk d h)).elim
  by_cases hb : R.p d = ⊥
  · exact R.sel_of_bot hb
  · rw [R.sel_of_top (not_not.mp fun ht => h ⟨hb, ht⟩), hcut]

/-- The cut is `N`-visible. -/
theorem selfVis_cut {v} (hv : SelfVis N (v R.capL)) : SelfVis N (R.cut v) := by
  classical
  refine selfVis_min hv ?_
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => rfl
  | insert i s _ ih =>
    rw [Finset.sup_insert]
    exact TopSupport.selfVis_max_of (TopSupport.selfVis_evr_self N _) ih

/-! ### Cap naturality (8) -/

theorem sup_min_eq {γ} (f : I → ExtOrd) :
    (Finset.univ.sup fun i => min (f i) γ) = min (Finset.univ.sup f) γ := by
  rw [min_comm, Finset.sup_inf_distrib_left]
  grind

theorem cut_min {γ} (hγ : SelfVis N γ) v :
    R.cut (fun d => min (v d) γ) = min (R.cut v) γ := by
  unfold cut
  simp [evr_min_of_selfVis hγ le_rfl le_rfl]
  rw [sup_min_eq, min_min_min_comm, min_self]

theorem sel_min {γ} (hγ : SelfVis N γ) v d :
    R.sel (fun d => min (v d) γ) d = min (R.sel v d) γ := by
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · rw [R.sel_of_proper h, R.sel_of_proper h, R.cut_min hγ,
      evr_min_of_selfVis hγ le_rfl (R.poff_lt d h).le, min_min_min_comm, min_self]
  by_cases hb : R.p d = ⊥
  · rw [R.sel_of_bot hb, R.sel_of_bot hb, min_bot_left]
  · have ht := not_not.mp fun ht => h ⟨hb, ht⟩
    rw [R.sel_of_top ht, R.sel_of_top ht, R.cut_min hγ]

/-! ### Clipping the cap coordinate -/

/-! ## Exact witnesses at the cap -/

/-- One exact bounded witness for any labelling of the cap's lower domain lawful there. -/
theorem exists_witness {v}
    (hv : C.rows.Lawful v) :
    ∃ τ, Witness (gTop N) τ ∧ (∀ x, τ x ≤ v R.capL) ∧
      ∀ d : R.Low, τ (R.srcE d) = min (v d) (v R.capL) := by
  have h := exists_bounded_exact_capped_witness
     (p := v) (fun d => d.2.2) (hv.orderly R.capL).symm (hv.locality R.capL)
  have hg : C.scheme.grade R.capL.1 = N := R.grade_cap
  rwa [hg] at h

/-- Two ordinal sources with the same `N`-invisible image under a witness through `N` coincide
(ported from the reviewer's private `sources_equal_at_invisible_output`, `ReferenceOrbitIncoming`,
with attribution). -/
theorem sources_eq_of_invisible_image {τ} (hτ : Witness (gTop N) τ)
    {a b t} (ha : τ (ofOrd a) = ofOrd t) (hb : τ (ofOrd b) = ofOrd t)
    (ht : finitePart t < N) : a = b := by
  have hcomm : ∀ x i, i ≤ N →
      τ (extVisibilityReplace x N i) = extVisibilityReplace (τ x) N i :=
    fun x i hi => hτ.comm_gTop x hi
  have hnv : ¬ SelfVis N (ofOrd t) := by
    rw [selfVis_ofOrd_iff]; exact not_le_of_gt ht
  have hblock : limitPart a = limitPart b := by
    rcases lt_trichotomy (limitPart a) (limitPart b) with h | h | h
    · have hv := selfVis_of_equal_images_separated_blocks hτ.mono
        (fun x => hcomm x N le_rfl) h (ha.trans hb.symm)
      grind
    · exact h
    · have hv := selfVis_of_equal_images_separated_blocks hτ.mono
        (fun x => hcomm x N le_rfl) h (hb.trans ha.symm)
      grind
  have hfa := finitePart_eq_of_nonvisible_image hcomm ha ht
  rw [← decomposition a, ← decomposition b, hblock, hfa, (finitePart_eq_of_nonvisible_image hcomm hb ht)]

/-! ## The actual row: source blocks and the face equations (3), (4) -/

theorem ref_lt_cap i : R.vact (R.ref i) < R.vact R.cap :=
  (R.vact_ref i).symm ▸ ((ofOrd_lt_ofOrd.mpr ((add_lt_add_iff_left _).mpr
    (Nat.cast_lt.mpr (R.off_lt i)))).trans (R.margin i))

/-- The representative's source is coded in some source block with the representative's
offset. -/
theorem exists_srcBlock i :
    ∃ b : ℕ, R.srcE (R.lowRef i) = ofOrd (Ordinal.omega0 * b + R.off i) := by
  obtain ⟨τ, hτ, -, hread⟩ := R.exists_witness (R.vact_respects.toBelow _)
  have hr : τ (R.srcE (R.lowRef i)) = ofOrd (R.μ i + R.off i) := by
    rw [hread]
    change min (R.vact (R.ref i)) (R.vact R.cap) = _
    rw [min_eq_left (R.ref_lt_cap i).le, R.vact_ref i]
  rcases show IsCodedLabel N (R.srcE (R.lowRef i)) from by
          have := C.rows_coded R.cap (R.lowRef i)
          rwa [R.grade_cap] at this with hbot | ⟨b, j, -, hcode⟩
  · rw [hbot, hτ.bot] at hr
    exact False.elim (ofOrd_ne_bot _ hr.symm)
  · refine ⟨b, ?_⟩
    have hf := finitePart_eq_of_nonvisible_image (fun x i hi => hτ.comm_gTop x hi) (hcode ▸ hr)
      (by rw [R.finitePart_μ_add]; exact R.off_lt i)
    rw [finitePart_mul_add, R.finitePart_μ_add] at hf
    simp_all

/-- The source block of each representative. -/
noncomputable def srcBlock (i : I) : ℕ := (R.exists_srcBlock i).choose

theorem srcE_ref i :
    R.srcE (R.lowRef i) = ofOrd (Ordinal.omega0 * R.srcBlock i + R.off i) :=
  (R.exists_srcBlock i).choose_spec

/-- Any witness of any lawful `v` reads the replacement of a representative's source as the
replacement of `v`'s reading, capped. -/
theorem read_ref_rep {v : R.Low → ExtOrd} {τ} (hτ : Witness (gTop N) τ)
    (hread : ∀ d : R.Low, τ (R.srcE d) = min (v d) (v R.capL)) i {k} (hk : k ≤ N) :
    τ (ofOrd (Ordinal.omega0 * R.srcBlock i + k)) =
      extVisibilityReplace (min (v (R.lowRef i)) (v R.capL)) N k := by
  rw [← hread (R.lowRef i), ← hτ.comm_gTop _ hk, R.srcE_ref i,
    extVisibilityReplace_rep (limitPart_mul_nat _) (R.off_lt i)]

theorem read_ref_rep_actual {τ} (hτ : Witness (gTop N) τ)
    (hread : ∀ d : R.Low, τ (R.srcE d) = min (R.vactL d) (R.vactL R.capL)) i {k}
    (hk : k ≤ N) : τ (ofOrd (Ordinal.omega0 * R.srcBlock i + k)) = ofOrd (R.μ i + k) := by
  rw [R.read_ref_rep hτ hread i hk]
  change extVisibilityReplace (min (R.vact (R.ref i)) (R.vact R.cap)) N k = _
  rw [min_eq_left (R.ref_lt_cap i).le, R.vact_ref i,
    extVisibilityReplace_rep (R.μ_limit i) (R.off_lt i)]

/-- The source blocks follow the block order (notes32 §2). -/
theorem srcBlock_strict {i j} (h : R.μ i < R.μ j) : R.srcBlock i < R.srcBlock j := by
  obtain ⟨τ, hτ, -, hread⟩ := R.exists_witness (R.vact_respects.toBelow _)
  apply lt_of_not_ge
  intro hle
  have hs : ofOrd (Ordinal.omega0 * R.srcBlock j + (0 : ℕ)) ≤
      ofOrd (Ordinal.omega0 * R.srcBlock i + (0 : ℕ)) :=
    ofOrd_le_ofOrd.mpr (by
      simp_all)
  have hh := hτ.mono hs
  rw [R.read_ref_rep_actual hτ hread j (Nat.zero_le _),
    R.read_ref_rep_actual hτ hread i (Nat.zero_le _)] at hh
  simp_all <;> grind

/-- The proper face cell's source is the replacement of its block representative's source (3). -/
theorem srcE_face_proper a (h : R.p a.1 ≠ ⊥ ∧ R.p a.1 ≠ ⊤) :
    R.srcE (R.lowFace a) =
      ofOrd (Ordinal.omega0 * R.srcBlock (R.blk a.1 h) + R.poff a.1 h) := by
  obtain ⟨τ, hτ, -, hread⟩ := R.exists_witness (R.vact_respects.toBelow _)
  have hlt : ofOrd (R.μ (R.blk a.1 h) + R.poff a.1 h) < R.vact R.cap :=
    (ofOrd_lt_ofOrd.mpr ((add_lt_add_iff_left _).mpr
      (Nat.cast_lt.mpr (R.poff_lt a.1 h)))).trans (R.margin _)
  have hface : τ (R.srcE (R.lowFace a)) = ofOrd (R.μ (R.blk a.1 h) + R.poff a.1 h) := by
    rw [hread]
    change min (R.vact (R.face a).1) (R.vact R.cap) = _
    rw [R.face_actual a, R.p_eq a.1 h, min_eq_left hlt.le]
  have hrep := R.read_ref_rep_actual hτ hread (R.blk a.1 h) (R.poff_lt a.1 h).le
  rcases show IsCodedLabel N (R.srcE (R.lowFace a)) from by
          have := C.rows_coded R.cap (R.lowFace a)
          rwa [R.grade_cap] at this with hbot | ⟨b, j, -, hcode⟩
  · rw [hbot, hτ.bot] at hface
    exact False.elim (ofOrd_ne_bot _ hface.symm)
  · rw [hcode] at hface ⊢
    rw [sources_eq_of_invisible_image hτ hface hrep
      (by rw [R.finitePart_μ_add]; exact R.poff_lt a.1 h)]

/-- A donor-top face cell's source exceeds every representative's `N`-endpoint (4). -/
theorem srcE_face_top a (ht : R.p a.1 = ⊤) i :
    ofOrd (Ordinal.omega0 * R.srcBlock i + N) < R.srcE (R.lowFace a) := by
  obtain ⟨τ, hτ, -, hread⟩ := R.exists_witness (R.vact_respects.toBelow _)
  have hface : τ (R.srcE (R.lowFace a)) = R.vact R.cap := by
    rw [hread]
    change min (R.vact (R.face a).1) (R.vact R.cap) = _
    rw [R.face_actual a, ht, min_eq_right le_top]
  apply lt_of_not_ge
  intro hle
  have hh := hτ.mono hle
  rw [hface, R.read_ref_rep_actual hτ hread i le_rfl] at hh
  exact not_le_of_gt (R.margin i) hh

/-! ## The coded labelling `e` -/

/-- The padded source block of each requested block. -/
noncomputable def padBlock (i : I) : Ordinal.{0} :=
  Ordinal.omega0 * (R.srcBlock i + 1 : ℕ)

theorem padBlock_limit i : limitPart (R.padBlock i) = R.padBlock i := limitPart_mul_nat _

/-- The fixed source map: the bottom-reflecting block interpolation onto the padded source
blocks. -/
noncomputable def emb : ExtOrd → ExtOrd := FiniteOrbitEmbedding.interpolate N R.μ R.padBlock

/-- The coded labelling `e` of `P` (notes32 §3). -/
noncomputable def e (d : Cell P.scheme) : ExtOrd := R.emb (R.p d)

theorem emb_bot : R.emb ⊥ = ⊥ := by
  change max ⊥ (Finset.univ.sup fun _ => ⊥) = ⊥
  simp

theorem ray_top K μ ν :
    FiniteOrbitEmbedding.ray K μ ν ⊤ = ofOrd (ν + K) := rfl

theorem emb_proper i {k} (hk : k ≤ N) :
    R.emb (ofOrd (R.μ i + k)) = ofOrd (R.padBlock i + k) := by
  apply FiniteOrbitEmbedding.interpolate_at N R.μ R.padBlock R.μ_limit R.padBlock_limit
  · intro i j h
    exact (mul_lt_mul_iff_right₀ Ordinal.omega0_pos).mpr
      (Nat.cast_lt.mpr (by have := R.srcBlock_strict h; omega))
  · intro i j h
    rw [R.μ_inj h]
  · intro i _
    exact le_mul_of_one_le_right zero_le (Nat.one_le_cast.mpr (Nat.succ_pos _))
  exact hk

theorem e_of_bot {d} (h : R.p d = ⊥) : R.e d = ⊥ := by
  unfold e; rw [h, R.emb_bot]

theorem e_eq_bot_iff d : R.e d = ⊥ ↔ R.p d = ⊥ := ⟨FiniteOrbitEmbedding.interpolate_reflects_bottom _ _ _ _, fun h => h ▸ R.emb_bot⟩

/-- `e` is lawful on the unchanged `P`. -/
theorem e_respects :
    RespectsSemanticsBelow P.rows (Finset.univ, nP + 1) (fun d => R.e d.1) :=
  FiniteOrbitEmbedding.incoming_respects R.μ R.padBlock R.padBlock_limit
    (R.p_respects.toBelow _) (fun d => ((gradeP_le d.1).trans_lt R.arity_lt).le)

/-! ## Readback: the witness of `v` unpadded reads `e` as `sel v` -/

/-- The outer map of a witness `τ` at the cap: `τ ∘ unpad`. -/
noncomputable def read (τ : ExtOrd → ExtOrd) (x : ExtOrd) : ExtOrd := τ (SourceBlockPadding.unpad x)

theorem read_witness {τ} (hτ : Witness (gTop N) τ) : Witness (gTop N) (read τ) :=
  SourceBlockPadding.witness_precompose_unpad hτ

theorem unpad_padBlock i (k : ℕ) :
    SourceBlockPadding.unpad (ofOrd (R.padBlock i + k)) =
      ofOrd (Ordinal.omega0 * R.srcBlock i + k) := by
  rw [padBlock, ← SourceBlockPadding.pad_code, SourceBlockPadding.unpad_pad]

theorem unpad_nat (n : ℕ) : SourceBlockPadding.unpad (ofOrd ((0 : Ordinal) + n)) = ⊥ := by
  rw [SourceBlockPadding.unpad_ofOrd, zero_add,
    ite_eq_right (not_le_of_gt (Ordinal.natCast_lt_omega0 n))]

section Read

variable {v : R.Low → ExtOrd} {τ : ExtOrd → ExtOrd}

theorem read_e_proper (hτ : Witness (gTop N) τ)
    (hread : ∀ d : R.Low, τ (R.srcE d) = min (v d) (v R.capL)) (hvis : SelfVis N (v R.capL))
    {d} (h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤) : read τ (R.e d) = R.sel v d := by
  rw [show R.e d = ofOrd (R.padBlock (R.blk d h) + ↑(R.poff d h)) from by
        unfold e; rw [R.p_eq d h, R.emb_proper _ (R.poff_lt d h).le], read, R.unpad_padBlock, R.read_ref_rep hτ hread _ (R.poff_lt d h).le,
    evr_min_of_selfVis hvis le_rfl (R.poff_lt d h).le, R.sel_of_proper h]
  have hle : extVisibilityReplace (v (R.lowRef (R.blk d h))) N (R.poff d h) ≤
      extVisibilityReplace (v (R.lowRef (R.blk d h))) N N :=
    extVisibilityReplace_le_of_le_selfVis (R.poff_lt d h).le (TopSupport.selfVis_evr_self N _)
      (TopSupport.le_evr_self _ N)
  unfold cut
  rw [← min_assoc, min_eq_left ((min_le_left _ _).trans (hle.trans (Finset.le_sup
    (f := fun i => extVisibilityReplace (v (R.lowRef i)) N N) (Finset.mem_univ _))))]

theorem read_e_top (hτ : Witness (gTop N) τ)
    (hread : ∀ d : R.Low, τ (R.srcE d) = min (v d) (v R.capL)) (hvis : SelfVis N (v R.capL))
    {d} (ht : R.p d = ⊤) : read τ (R.e d) = R.sel v d := by
  rw [R.sel_of_top ht, e, ht, show R.emb ⊤ = max (ofOrd (0 + ↑N)) (Finset.univ.sup fun i => ofOrd (R.padBlock i + ↑N)) from by
          unfold emb FiniteOrbitEmbedding.interpolate
          simp only [ray_top], read, SourceBlockPadding.unpad_mono.map_max,
    Finset.apply_sup_eq_sup_comp SourceBlockPadding.unpad
      (fun _ _ => SourceBlockPadding.unpad_mono.map_max) SourceBlockPadding.unpad_bot, unpad_nat,
    max_bot_left, Finset.apply_sup_eq_sup_comp τ (fun _ _ => hτ.mono.map_max) hτ.bot]
  unfold cut
  rw [min_comm, ← sup_min_eq]
  congr 1
  funext i
  simp
  rw [R.unpad_padBlock, R.read_ref_rep hτ hread i le_rfl, evr_min_of_selfVis hvis le_rfl le_rfl]

/-- **The selector is the readback of `e`** (notes32 §3): for any exact witness of `v` at the
cap, `τ ∘ unpad` carries `e` to `sel v`. -/
theorem sel_eq_read (hτ : Witness (gTop N) τ)
    (hread : ∀ d : R.Low, τ (R.srcE d) = min (v d) (v R.capL)) (hvis : SelfVis N (v R.capL))
    d : R.sel v d = read τ (R.e d) := by
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · exact (R.read_e_proper hτ hread hvis h).symm
  by_cases hb : R.p d = ⊥
  · rw [R.sel_of_bot hb, show read τ (R.e d) = ⊥ from by
          rw [R.e_of_bot hb, read, SourceBlockPadding.unpad_bot, hτ.bot]]
  · exact (R.read_e_top hτ hread hvis (not_not.mp fun ht => h ⟨hb, ht⟩)).symm

end Read

/-! ## Active sections and the capped-donor lemma -/

/-- An **active** lawful private section on the cap's lower domain: positive cap and references,
bottom at every donor-bottom face cell (the support conditions enforced in the active part of
the construction, notes32 §4). -/
structure Active (v : R.Low → ExtOrd) : Prop where
  respects : C.rows.Lawful v
  cap_pos : v R.capL ≠ ⊥
  ref_pos : ∀ i, v (R.lowRef i) ≠ ⊥
  face_bot : ∀ a : P.scheme.below (R.A, R.KA), R.p a.1 = ⊥ → v (R.lowFace a) = ⊥

theorem Active.selfVis_cap {v} (hv : R.Active v) : SelfVis N (v R.capL) := by
  have h : SelfVis (C.scheme.grade R.cap) (v R.capL) := (hv.respects.orderly R.capL).symm
  rwa [R.grade_cap] at h

theorem Active.cut_ne_bot [Nonempty I] {v} (hv : R.Active v) :
    R.cut v ≠ ⊥ := by
  obtain ⟨i⟩ := ‹Nonempty I›
  intro h
  rcases min_eq_bot.mp h with h | h
  · exact hv.cap_pos h
  · exact extVisibilityReplace_ne_bot (hv.ref_pos i) N N
      (le_bot_iff.mp (h ▸ Finset.le_sup (f := fun i => extVisibilityReplace (v (R.lowRef i)) N N)
        (Finset.mem_univ i)))

/-- With at least one requested block, the selector has exactly the donor's bottom pattern. -/
theorem Active.sel_eq_bot_iff [Nonempty I] {v} (hv : R.Active v)
    d : R.sel v d = ⊥ ↔ R.p d = ⊥ := by
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · simp [R.sel_of_proper h, h.1]
    exact ⟨extVisibilityReplace_ne_bot (hv.ref_pos _) _ _, Active.cut_ne_bot R hv⟩
  by_cases hb : R.p d = ⊥
  · simp [R.sel_of_bot hb, hb]
  · simp [R.sel_of_top (not_not.mp fun ht => h ⟨hb, ht⟩), hb]
    exact Active.cut_ne_bot R hv

/-- **The capped-donor lemma, lawfulness**: for every active lawful private section `v`, the
selector `sel v` is lawful on the unchanged request scheme `P`.  With no requested block the
selector is identically bottom. -/
theorem Active.sel_respects {v} (hv : R.Active v) :
    RespectsSemantics P.rows (R.sel v) := by
  rcases isEmpty_or_nonempty I with hI | hI
  · rw [(funext (R.sel_of_isEmpty v))]
    exact RespectsSemantics.bot _
  obtain ⟨τ, hτ, -, hread⟩ := R.exists_witness hv.respects
  have hcap := Active.selfVis_cap R hv
  have hsel : (fun d : P.Native (nP + 1) => R.sel v d.1) =
      fun d => read τ (R.e d.1) := by
    funext d
    exact R.sel_eq_read hτ hread hcap d.1
  have hB : RespectsSemanticsBelow P.rows (Finset.univ, nP + 1)
      (fun d => read τ (R.e d.1)) := by
    refine (map_respects_iff_rowBlockBottom R.e_respects (fun d => ((gradeP_le d.1).trans_lt R.arity_lt).le)
      (boundedMap_of_witness (read_witness hτ))).mpr ?_
    refine rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects R.e_respects) ?_
    intro d
    rw [← R.sel_eq_read hτ hread hcap d.1, Active.sel_eq_bot_iff R hv, R.e_eq_bot_iff]
  rw [← hsel] at hB
  exact hB.toRespects (StageType.gradedLe_univ_succ P.scheme)

/-- **The capped-donor lemma, boundary** (7): on the common face the selector is the private
section capped at the cut. -/
theorem Active.sel_face {v} (hv : R.Active v)
    a : R.sel v a.1 = min (v (R.lowFace a)) (R.cut v) := by
  obtain ⟨τ, hτ, -, hread⟩ := R.exists_witness hv.respects
  have hcapvis := Active.selfVis_cap R hv
  by_cases h : R.p a.1 ≠ ⊥ ∧ R.p a.1 ≠ ⊤
  · rw [R.sel_of_proper h]
    have h1 := hread (R.lowFace a)
    rw [R.srcE_face_proper a h, R.read_ref_rep hτ hread _ (R.poff_lt a.1 h).le,
      evr_min_of_selfVis hcapvis le_rfl (R.poff_lt a.1 h).le] at h1
    calc min (extVisibilityReplace (v (R.lowRef (R.blk a.1 h))) N (R.poff a.1 h)) (R.cut v)
        = min (min (extVisibilityReplace (v (R.lowRef (R.blk a.1 h))) N (R.poff a.1 h))
            (v R.capL)) (R.cut v) := by
          rw [min_assoc, min_eq_right (R.cut_le_cap v)]
      _ = min (min (v (R.lowFace a)) (v R.capL)) (R.cut v) := by simp_all
      _ = min (v (R.lowFace a)) (R.cut v) := by rw [min_assoc, min_eq_right (R.cut_le_cap v)]
  by_cases hb : R.p a.1 = ⊥
  · rw [R.sel_of_bot hb, hv.face_bot a hb, min_bot_left]
  · have ht := not_not.mp fun ht => h ⟨hb, ht⟩
    rw [R.sel_of_top ht]
    symm
    apply min_eq_right
    -- every reference endpoint reads below the face value
    have hi : ∀ i, min (extVisibilityReplace (v (R.lowRef i)) N N) (v R.capL) ≤
        v (R.lowFace a) := by
      intro i
      have h1 := hτ.mono (R.srcE_face_top a ht i).le
      rw [R.read_ref_rep hτ hread i le_rfl, evr_min_of_selfVis hcapvis le_rfl le_rfl,
        hread (R.lowFace a)] at h1
      exact h1.trans (min_le_left _ _)
    unfold cut
    rw [min_comm, ← sup_min_eq]
    aesop

/-! ## The actual context (9) -/

theorem cut_actual : R.cut R.vactL = Finset.univ.sup fun i => ofOrd (R.μ i + N) := by
  unfold cut
  have hi : ∀ i, extVisibilityReplace (R.vactL (R.lowRef i)) N N = ofOrd (R.μ i + N) := by
    intro i
    change extVisibilityReplace (R.vact (R.ref i)) N N = _
    rw [R.vact_ref i, extVisibilityReplace_rep (R.μ_limit i) (R.off_lt i)]
  simp only [hi]
  exact min_eq_right (Finset.sup_le fun i _ => (R.margin i).le)

/-- The actual private section selects the donor capped at the actual cut. -/
theorem sel_actual d : R.sel R.vactL d = min (R.p d) (R.cut R.vactL) := by
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · rw [R.sel_of_proper h]
    change min (extVisibilityReplace (R.vact (R.ref (R.blk d h))) N (R.poff d h)) _ = _
    rw [R.vact_ref, extVisibilityReplace_rep (R.μ_limit _) (R.off_lt _), ← R.p_eq d h]
  by_cases hb : R.p d = ⊥
  · rw [R.sel_of_bot hb, hb, min_bot_left]
  · rw [R.sel_of_top (not_not.mp fun ht => h ⟨hb, ht⟩), not_not.mp fun ht => h ⟨hb, ht⟩,
      min_top_left]

end Ref

end CappedDonor

end VaughtConjecture.Knight
