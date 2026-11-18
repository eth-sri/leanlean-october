/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FiniteOrbitEmbedding
public import VaughtConjecture.Knight.SourceBlockPadding
public import VaughtConjecture.Knight.TopSupport

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd SharpWitnessComposition AmalgamationPlan

theorem Witness.comm_gTop {N : ℕ} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop N) τ) (x : ExtOrd)
    {i : ℕ} (hi : i ≤ N) :
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

theorem gradeP_le (d : Cell P.scheme) : P.scheme.grade d ≤ nP + 1 :=
  (P.scheme.grade_le_card_scope d).trans (by simpa using Finset.card_le_univ (P.scheme.scope d))

include R in
theorem gradeP_lt_N (d : Cell P.scheme) : P.scheme.grade d < N :=
  (gradeP_le d).trans_lt R.arity_lt

theorem KA_le : R.KA ≤ nP + 1 :=
  R.KA_le_card.trans (by simpa using Finset.card_le_univ R.A)

theorem KA_lt_N : R.KA < N := R.KA_le.trans_lt R.arity_lt

/-- The graded lower sets of the face are in the graded plans (positive grades only). -/
theorem face_mem {k : ℕ} (hk : 0 < k) (hkA : k ≤ R.KA) :
    (R.A, k) ∈ Plan.gradedPlan P.scheme.plan :=
  Plan.mem_gradedPlan.mpr ⟨R.A_mem, hk, hkA.trans R.KA_le_card⟩

theorem face_symm_grade (b : C.scheme.below (R.A', R.KA)) :
    P.scheme.grade (R.face.symm b).1 = C.scheme.grade b.1 := by
  have h := R.face_grade (R.face.symm b)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- A face cell of grade at most `k ≤ KA` as a cell of the lower set `(A, k)`. -/
def faceLift {k : ℕ} (hk : k ≤ R.KA) (a : P.scheme.below (R.A, k)) : P.scheme.below (R.A, R.KA) :=
  ⟨a.1, a.2.trans ⟨Finset.Subset.refl _, hk⟩⟩

def faceLift' {k : ℕ} (hk : k ≤ R.KA) (b : C.scheme.below (R.A', k)) :
    C.scheme.below (R.A', R.KA) :=
  ⟨b.1, b.2.trans ⟨Finset.Subset.refl _, hk⟩⟩

/-- **The identification at grade `k ≤ KA`**: the restriction of `face` to the lower sets
`(A, k)`, `(A', k)` — a bijection because the identification preserves grades. -/
def faceAt {k : ℕ} (hk : k ≤ R.KA) : P.scheme.below (R.A, k) ≃ C.scheme.below (R.A', k) where
  toFun a := ⟨(R.face (R.faceLift hk a)).1, ⟨(R.face (R.faceLift hk a)).2.1,
    (R.face_grade (R.faceLift hk a)).trans_le a.2.2⟩⟩
  invFun b := ⟨(R.face.symm (R.faceLift' hk b)).1, ⟨(R.face.symm (R.faceLift' hk b)).2.1,
    (R.face_symm_grade (R.faceLift' hk b)).trans_le b.2.2⟩⟩
  left_inv a := by
    apply Subtype.ext
    change (R.face.symm ⟨(R.face (R.faceLift hk a)).1, _⟩).1 = a.1
    have h : (⟨(R.face (R.faceLift hk a)).1, _⟩ : C.scheme.below (R.A', R.KA)) =
        R.face (R.faceLift hk a) := rfl
    rw [h, Equiv.symm_apply_apply]
    rfl
  right_inv b := by
    apply Subtype.ext
    change (R.face ⟨(R.face.symm (R.faceLift' hk b)).1, _⟩).1 = b.1
    have h : (⟨(R.face.symm (R.faceLift' hk b)).1, _⟩ : P.scheme.below (R.A, R.KA)) =
        R.face.symm (R.faceLift' hk b) := rfl
    rw [h, Equiv.apply_symm_apply]
    rfl

/-- The face is literally common at every grade, through `faceAt`. -/
theorem faceAt_respects {k : ℕ} (hk : k ≤ R.KA) (r : C.scheme.below (R.A', k) → ExtOrd) :
    RespectsSemanticsBelow C.rows (R.A', k) r ↔
      RespectsSemanticsBelow P.rows (R.A, k) (fun a => r (R.faceAt hk a)) :=
  R.face_respects k hk r

theorem finitePart_μ_add (i : I) (k : ℕ) : finitePart (R.μ i + k) = k := by
  have := finitePart_limitPart_add_nat (R.μ i) k
  rwa [R.μ_limit i] at this

/-- The representatives have grade below `N`: their actual labels are `N`-invisible. -/
theorem ref_grade_lt (i : I) : C.scheme.grade (R.ref i) < N := by
  have h : SelfVis (C.scheme.grade (R.ref i)) (R.vact (R.ref i)) :=
    (R.vact_respects.orderly (R.ref i)).symm
  rw [R.vact_ref i, selfVis_ofOrd_iff, R.finitePart_μ_add] at h
  exact h.trans_lt (R.off_lt i)

/-- The lower domain of the cap: the cells of the acquisition face of grade at most `N`. -/
abbrev Low : Type := C.scheme.below (C.scheme.cell R.cap)

/-- A cell of the acquisition face of grade at most `N` as a cell of the cap's lower domain. -/
def lowOf (d : Cell C.scheme) (hs : C.scheme.scope d ⊆ R.C₀) (h : C.scheme.grade d ≤ N) :
    R.Low :=
  ⟨d, by rw [R.cap_cell]; exact ⟨hs, h⟩⟩

/-- The cap in its own lower domain. -/
def capL : R.Low := ⟨R.cap, GradedLe.refl _⟩

/-- A representative in the cap's lower domain. -/
def lowRef (i : I) : R.Low := R.lowOf (R.ref i) (R.ref_scope i) (R.ref_grade_lt i).le

/-- A face cell in the cap's lower domain. -/
def lowFace (a : P.scheme.below (R.A, R.KA)) : R.Low :=
  R.lowOf (R.face a).1 ((R.face a).2.1.trans R.A'_sub) ((R.face a).2.2.trans R.KA_lt_N.le)

/-- The actual reference row. -/
noncomputable abbrev srcE : R.Low → ExtOrd := C.rows.E R.cap

theorem srcE_coded (d : R.Low) : IsCodedLabel N (R.srcE d) := by
  have := C.rows_coded R.cap d
  rwa [R.grade_cap] at this

/-- The actual private labelling on the cap's lower domain. -/
abbrev vactL : R.Low → ExtOrd := fun d => R.vact d.1

theorem vactL_respects : RespectsSemanticsBelow C.rows (C.scheme.cell R.cap) R.vactL :=
  R.vact_respects.toBelow _

/-! ## The block and offset of a proper donor label -/

/-- The block of a proper donor label. -/
noncomputable def blk (d : Cell P.scheme) (h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤) : I :=
  (R.p_code d h.1 h.2).choose

/-- The offset of a proper donor label. -/
noncomputable def poff (d : Cell P.scheme) (h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤) : ℕ :=
  (R.p_code d h.1 h.2).choose_spec.choose

theorem poff_lt (d : Cell P.scheme) (h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤) : R.poff d h < N :=
  (R.p_code d h.1 h.2).choose_spec.choose_spec.1

theorem p_eq (d : Cell P.scheme) (h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤) :
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

theorem cut_le_cap (v : R.Low → ExtOrd) : R.cut v ≤ v R.capL := min_le_left _ _

theorem sel_of_bot {v : R.Low → ExtOrd} {d : Cell P.scheme} (h : R.p d = ⊥) :
    R.sel v d = ⊥ := by
  unfold sel; rw [dite_eq_right (fun h' => h'.1 h), ite_eq_left h]

theorem sel_of_top {v : R.Low → ExtOrd} {d : Cell P.scheme} (h : R.p d = ⊤) :
    R.sel v d = R.cut v := by
  unfold sel
  rw [dite_eq_right (fun h' => h'.2 h), ite_eq_right (by rw [h]; exact top_ne_bot)]

theorem sel_of_proper {v : R.Low → ExtOrd} {d : Cell P.scheme} (h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤) :
    R.sel v d =
      min (extVisibilityReplace (v (R.lowRef (R.blk d h))) N (R.poff d h)) (R.cut v) := by
  unfold sel; rw [dite_eq_left h]

theorem sel_le_cut (v : R.Low → ExtOrd) (d : Cell P.scheme) : R.sel v d ≤ R.cut v := by
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · rw [R.sel_of_proper h]; exact min_le_right _ _
  by_cases hb : R.p d = ⊥
  · rw [R.sel_of_bot hb]; exact bot_le
  · rw [R.sel_of_top (not_not.mp fun ht => h ⟨hb, ht⟩)]

/-- With no requested block the selector is identically bottom. -/
theorem sel_of_isEmpty [IsEmpty I] (v : R.Low → ExtOrd) (d : Cell P.scheme) : R.sel v d = ⊥ := by
  have hcut : R.cut v = ⊥ := by
    unfold cut
    rw [Finset.univ_eq_empty, Finset.sup_empty, min_bot_right]
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · exact (IsEmpty.false (R.blk d h)).elim
  by_cases hb : R.p d = ⊥
  · exact R.sel_of_bot hb
  · rw [R.sel_of_top (not_not.mp fun ht => h ⟨hb, ht⟩), hcut]

/-- The cut is `N`-visible. -/
theorem selfVis_cut {v : R.Low → ExtOrd} (hv : SelfVis N (v R.capL)) : SelfVis N (R.cut v) := by
  classical
  refine selfVis_min hv ?_
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => exact selfVis_bot N
  | insert i s _ ih =>
    rw [Finset.sup_insert]
    exact TopSupport.selfVis_max_of (TopSupport.selfVis_evr_self N _) ih

/-! ### Cap naturality (8) -/

theorem sup_min_eq {γ : ExtOrd} (f : I → ExtOrd) :
    (Finset.univ.sup fun i => min (f i) γ) = min (Finset.univ.sup f) γ := by
  rw [min_comm, Finset.sup_inf_distrib_left]
  simp only [min_comm γ]

theorem cut_min {γ : ExtOrd} (hγ : SelfVis N γ) (v : R.Low → ExtOrd) :
    R.cut (fun d => min (v d) γ) = min (R.cut v) γ := by
  unfold cut
  simp only [evr_min_of_selfVis hγ le_rfl le_rfl]
  rw [sup_min_eq, min_min_min_comm, min_self]

theorem sel_min {γ : ExtOrd} (hγ : SelfVis N γ) (v : R.Low → ExtOrd) (d : Cell P.scheme) :
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
theorem exists_witness {v : R.Low → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (C.scheme.cell R.cap) v) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop N) τ ∧ (∀ x, τ x ≤ v R.capL) ∧
      ∀ d : R.Low, τ (R.srcE d) = min (v d) (v R.capL) := by
  have h := exists_bounded_exact_capped_witness (grade := fun d : R.Low => C.scheme.grade d.1)
    (c := R.capL) (p := v) (fun d => d.2.2) (hv.orderly R.capL).symm (hv.locality R.capL)
  have hg : C.scheme.grade R.capL.1 = N := R.grade_cap
  rwa [hg] at h

/-- Two ordinal sources with the same `N`-invisible image under a witness through `N` coincide
(ported from the reviewer's private `sources_equal_at_invisible_output`, `ReferenceOrbitIncoming`,
with attribution). -/
theorem sources_eq_of_invisible_image {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop N) τ)
    {a b t : Ordinal.{0}} (ha : τ (ofOrd a) = ofOrd t) (hb : τ (ofOrd b) = ofOrd t)
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
      exact False.elim (hnv (ha ▸ hv))
    · exact h
    · have hv := selfVis_of_equal_images_separated_blocks hτ.mono
        (fun x => hcomm x N le_rfl) h (hb.trans ha.symm)
      exact False.elim (hnv (hb ▸ hv))
  have hfa := finitePart_eq_of_nonvisible_image hcomm ha ht
  have hfb := finitePart_eq_of_nonvisible_image hcomm hb ht
  rw [← decomposition a, ← decomposition b, hblock, hfa, hfb]

/-! ## The actual row: source blocks and the face equations (3), (4) -/

theorem ref_lt_cap (i : I) : R.vact (R.ref i) < R.vact R.cap :=
  (R.vact_ref i).symm ▸ ((ofOrd_lt_ofOrd.mpr ((add_lt_add_iff_left _).mpr
    (Nat.cast_lt.mpr (R.off_lt i)))).trans (R.margin i))

/-- The representative's source is coded in some source block with the representative's
offset. -/
theorem exists_srcBlock (i : I) :
    ∃ b : ℕ, R.srcE (R.lowRef i) = ofOrd (Ordinal.omega0 * b + R.off i) := by
  obtain ⟨τ, hτ, -, hread⟩ := R.exists_witness R.vactL_respects
  have hr : τ (R.srcE (R.lowRef i)) = ofOrd (R.μ i + R.off i) := by
    rw [hread]
    change min (R.vact (R.ref i)) (R.vact R.cap) = _
    rw [min_eq_left (R.ref_lt_cap i).le, R.vact_ref i]
  rcases R.srcE_coded (R.lowRef i) with hbot | ⟨b, j, -, hcode⟩
  · rw [hbot, hτ.bot] at hr
    exact False.elim (ofOrd_ne_bot _ hr.symm)
  · refine ⟨b, ?_⟩
    have hf := finitePart_eq_of_nonvisible_image (fun x i hi => hτ.comm_gTop x hi) (hcode ▸ hr)
      (by rw [R.finitePart_μ_add]; exact R.off_lt i)
    rw [finitePart_mul_add, R.finitePart_μ_add] at hf
    rw [hcode, hf]

/-- The source block of each representative. -/
noncomputable def srcBlock (i : I) : ℕ := (R.exists_srcBlock i).choose

theorem srcE_ref (i : I) :
    R.srcE (R.lowRef i) = ofOrd (Ordinal.omega0 * R.srcBlock i + R.off i) :=
  (R.exists_srcBlock i).choose_spec

/-- Any witness of any lawful `v` reads the replacement of a representative's source as the
replacement of `v`'s reading, capped. -/
theorem read_ref_rep {v : R.Low → ExtOrd} {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop N) τ)
    (hread : ∀ d : R.Low, τ (R.srcE d) = min (v d) (v R.capL)) (i : I) {k : ℕ} (hk : k ≤ N) :
    τ (ofOrd (Ordinal.omega0 * R.srcBlock i + k)) =
      extVisibilityReplace (min (v (R.lowRef i)) (v R.capL)) N k := by
  rw [← hread (R.lowRef i), ← hτ.comm_gTop _ hk, R.srcE_ref i,
    extVisibilityReplace_rep (limitPart_mul_nat _) (R.off_lt i)]

theorem read_ref_rep_actual {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop N) τ)
    (hread : ∀ d : R.Low, τ (R.srcE d) = min (R.vactL d) (R.vactL R.capL)) (i : I) {k : ℕ}
    (hk : k ≤ N) : τ (ofOrd (Ordinal.omega0 * R.srcBlock i + k)) = ofOrd (R.μ i + k) := by
  rw [R.read_ref_rep hτ hread i hk]
  change extVisibilityReplace (min (R.vact (R.ref i)) (R.vact R.cap)) N k = _
  rw [min_eq_left (R.ref_lt_cap i).le, R.vact_ref i,
    extVisibilityReplace_rep (R.μ_limit i) (R.off_lt i)]

/-- The source blocks follow the block order (notes32 §2). -/
theorem srcBlock_strict {i j : I} (h : R.μ i < R.μ j) : R.srcBlock i < R.srcBlock j := by
  obtain ⟨τ, hτ, -, hread⟩ := R.exists_witness R.vactL_respects
  apply lt_of_not_ge
  intro hle
  have hs : ofOrd (Ordinal.omega0 * R.srcBlock j + (0 : ℕ)) ≤
      ofOrd (Ordinal.omega0 * R.srcBlock i + (0 : ℕ)) :=
    ofOrd_le_ofOrd.mpr (by
      simp only [Nat.cast_zero, add_zero]
      exact mul_le_mul_right (Nat.cast_le.mpr hle) _)
  have hh := hτ.mono hs
  rw [R.read_ref_rep_actual hτ hread j (Nat.zero_le _),
    R.read_ref_rep_actual hτ hread i (Nat.zero_le _), ofOrd_le_ofOrd] at hh
  simp only [Nat.cast_zero, add_zero] at hh
  exact not_le_of_gt h hh

/-- The proper face cell's source is the replacement of its block representative's source (3). -/
theorem srcE_face_proper (a : P.scheme.below (R.A, R.KA)) (h : R.p a.1 ≠ ⊥ ∧ R.p a.1 ≠ ⊤) :
    R.srcE (R.lowFace a) =
      ofOrd (Ordinal.omega0 * R.srcBlock (R.blk a.1 h) + R.poff a.1 h) := by
  obtain ⟨τ, hτ, -, hread⟩ := R.exists_witness R.vactL_respects
  have hlt : ofOrd (R.μ (R.blk a.1 h) + R.poff a.1 h) < R.vact R.cap :=
    (ofOrd_lt_ofOrd.mpr ((add_lt_add_iff_left _).mpr
      (Nat.cast_lt.mpr (R.poff_lt a.1 h)))).trans (R.margin _)
  have hface : τ (R.srcE (R.lowFace a)) = ofOrd (R.μ (R.blk a.1 h) + R.poff a.1 h) := by
    rw [hread]
    change min (R.vact (R.face a).1) (R.vact R.cap) = _
    rw [R.face_actual a, R.p_eq a.1 h, min_eq_left hlt.le]
  have hrep := R.read_ref_rep_actual hτ hread (R.blk a.1 h) (R.poff_lt a.1 h).le
  rcases R.srcE_coded (R.lowFace a) with hbot | ⟨b, j, -, hcode⟩
  · rw [hbot, hτ.bot] at hface
    exact False.elim (ofOrd_ne_bot _ hface.symm)
  · rw [hcode] at hface ⊢
    rw [sources_eq_of_invisible_image hτ hface hrep
      (by rw [R.finitePart_μ_add]; exact R.poff_lt a.1 h)]

/-- A donor-top face cell's source exceeds every representative's `N`-endpoint (4). -/
theorem srcE_face_top (a : P.scheme.below (R.A, R.KA)) (ht : R.p a.1 = ⊤) (i : I) :
    ofOrd (Ordinal.omega0 * R.srcBlock i + N) < R.srcE (R.lowFace a) := by
  obtain ⟨τ, hτ, -, hread⟩ := R.exists_witness R.vactL_respects
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
  Ordinal.omega0 * ((R.srcBlock i + 1 : ℕ) : Ordinal)

theorem padBlock_limit (i : I) : limitPart (R.padBlock i) = R.padBlock i := limitPart_mul_nat _

/-- The fixed source map: the bottom-reflecting block interpolation onto the padded source
blocks. -/
noncomputable def emb : ExtOrd → ExtOrd := FiniteOrbitEmbedding.interpolate N R.μ R.padBlock

/-- The coded labelling `e` of `P` (notes32 §3). -/
noncomputable def e (d : Cell P.scheme) : ExtOrd := R.emb (R.p d)

theorem emb_bot : R.emb ⊥ = ⊥ := by
  change max ⊥ (Finset.univ.sup fun _ => (⊥ : ExtOrd)) = ⊥
  rw [Finset.sup_bot, max_self]

theorem emb_eq_bot_iff (x : ExtOrd) : R.emb x = ⊥ ↔ x = ⊥ :=
  ⟨FiniteOrbitEmbedding.interpolate_reflects_bottom _ _ _ x, fun h => h ▸ R.emb_bot⟩

theorem ray_top (K : ℕ) (μ ν : Ordinal.{0}) :
    FiniteOrbitEmbedding.ray K μ ν ⊤ = ofOrd (ν + K) := rfl

/-- The common endpoint `L` at donor-top cells. -/
theorem emb_top : R.emb ⊤ =
    max (ofOrd ((0 : Ordinal) + N)) (Finset.univ.sup fun i => ofOrd (R.padBlock i + N)) := by
  unfold emb FiniteOrbitEmbedding.interpolate
  simp only [ray_top]

theorem emb_proper (i : I) {k : ℕ} (hk : k ≤ N) :
    R.emb (ofOrd (R.μ i + k)) = ofOrd (R.padBlock i + k) := by
  apply FiniteOrbitEmbedding.interpolate_at N R.μ R.padBlock R.μ_limit R.padBlock_limit
  · intro i j h
    exact (mul_lt_mul_iff_right₀ Ordinal.omega0_pos).mpr
      (Nat.cast_lt.mpr (by have := R.srcBlock_strict h; omega))
  · intro i j h
    rw [R.μ_inj h]
  · intro i _
    exact le_mul_of_one_le_right zero_le (Nat.one_le_cast.mpr (Nat.succ_pos _))
  · exact hk

theorem e_of_bot {d : Cell P.scheme} (h : R.p d = ⊥) : R.e d = ⊥ := by
  unfold e; rw [h, R.emb_bot]

theorem e_of_proper {d : Cell P.scheme} (h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤) :
    R.e d = ofOrd (R.padBlock (R.blk d h) + R.poff d h) := by
  unfold e; rw [R.p_eq d h, R.emb_proper _ (R.poff_lt d h).le]

theorem e_eq_bot_iff (d : Cell P.scheme) : R.e d = ⊥ ↔ R.p d = ⊥ := R.emb_eq_bot_iff _

/-- `e` is lawful on the unchanged `P`. -/
theorem e_respects :
    RespectsSemanticsBelow P.rows (Finset.univ, nP + 1) (fun d => R.e d.1) :=
  FiniteOrbitEmbedding.incoming_respects R.μ R.padBlock R.padBlock_limit
    (R.p_respects.toBelow _) (fun d => (R.gradeP_lt_N d.1).le)

/-! ## Readback: the witness of `v` unpadded reads `e` as `sel v` -/

/-- The outer map of a witness `τ` at the cap: `τ ∘ unpad`. -/
noncomputable def read (τ : ExtOrd → ExtOrd) (x : ExtOrd) : ExtOrd := τ (SourceBlockPadding.unpad x)

theorem read_witness {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop N) τ) : Witness (gTop N) (read τ) :=
  SourceBlockPadding.witness_precompose_unpad hτ

theorem read_boundedMap {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop N) τ) :
    BoundedMap N (read τ) :=
  boundedMap_of_witness (read_witness hτ)

theorem unpad_padBlock (i : I) (k : ℕ) :
    SourceBlockPadding.unpad (ofOrd (R.padBlock i + k)) =
      ofOrd (Ordinal.omega0 * R.srcBlock i + k) := by
  rw [padBlock, ← SourceBlockPadding.pad_code, SourceBlockPadding.unpad_pad]

theorem unpad_nat (n : ℕ) : SourceBlockPadding.unpad (ofOrd ((0 : Ordinal) + n)) = ⊥ := by
  rw [SourceBlockPadding.unpad_ofOrd, zero_add,
    ite_eq_right (not_le_of_gt (Ordinal.natCast_lt_omega0 n))]

section Read

variable {v : R.Low → ExtOrd} {τ : ExtOrd → ExtOrd}

theorem read_e_bot (hτ : Witness (gTop N) τ) {d : Cell P.scheme} (h : R.p d = ⊥) :
    read τ (R.e d) = ⊥ := by
  rw [R.e_of_bot h, read, SourceBlockPadding.unpad_bot, hτ.bot]

theorem read_e_proper (hτ : Witness (gTop N) τ)
    (hread : ∀ d : R.Low, τ (R.srcE d) = min (v d) (v R.capL)) (hvis : SelfVis N (v R.capL))
    {d : Cell P.scheme} (h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤) : read τ (R.e d) = R.sel v d := by
  rw [R.e_of_proper h, read, R.unpad_padBlock, R.read_ref_rep hτ hread _ (R.poff_lt d h).le,
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
    {d : Cell P.scheme} (ht : R.p d = ⊤) : read τ (R.e d) = R.sel v d := by
  rw [R.sel_of_top ht, e, ht, R.emb_top, read, SourceBlockPadding.unpad_mono.map_max,
    Finset.apply_sup_eq_sup_comp SourceBlockPadding.unpad
      (fun _ _ => SourceBlockPadding.unpad_mono.map_max) SourceBlockPadding.unpad_bot, unpad_nat,
    max_bot_left, Finset.apply_sup_eq_sup_comp τ (fun _ _ => hτ.mono.map_max) hτ.bot]
  unfold cut
  rw [min_comm, ← sup_min_eq]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [R.unpad_padBlock, R.read_ref_rep hτ hread i le_rfl, evr_min_of_selfVis hvis le_rfl le_rfl]

/-- **The selector is the readback of `e`** (notes32 §3): for any exact witness of `v` at the
cap, `τ ∘ unpad` carries `e` to `sel v`. -/
theorem sel_eq_read (hτ : Witness (gTop N) τ)
    (hread : ∀ d : R.Low, τ (R.srcE d) = min (v d) (v R.capL)) (hvis : SelfVis N (v R.capL))
    (d : Cell P.scheme) : R.sel v d = read τ (R.e d) := by
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · exact (R.read_e_proper hτ hread hvis h).symm
  by_cases hb : R.p d = ⊥
  · rw [R.sel_of_bot hb, R.read_e_bot hτ hb]
  · exact (R.read_e_top hτ hread hvis (not_not.mp fun ht => h ⟨hb, ht⟩)).symm

end Read

/-! ## Active sections and the capped-donor lemma -/

/-- An **active** lawful private section on the cap's lower domain: positive cap and references,
bottom at every donor-bottom face cell (the support conditions enforced in the active part of
the construction, notes32 §4). -/
structure Active (v : R.Low → ExtOrd) : Prop where
  respects : RespectsSemanticsBelow C.rows (C.scheme.cell R.cap) v
  cap_pos : v R.capL ≠ ⊥
  ref_pos : ∀ i, v (R.lowRef i) ≠ ⊥
  face_bot : ∀ a : P.scheme.below (R.A, R.KA), R.p a.1 = ⊥ → v (R.lowFace a) = ⊥

theorem Active.selfVis_cap {v : R.Low → ExtOrd} (hv : R.Active v) : SelfVis N (v R.capL) := by
  have h : SelfVis (C.scheme.grade R.cap) (v R.capL) := (hv.respects.orderly R.capL).symm
  rwa [R.grade_cap] at h

theorem Active.cut_ne_bot [Nonempty I] {v : R.Low → ExtOrd} (hv : R.Active v) :
    R.cut v ≠ ⊥ := by
  obtain ⟨i⟩ := ‹Nonempty I›
  intro h
  rcases min_eq_bot.mp h with h | h
  · exact hv.cap_pos h
  · exact extVisibilityReplace_ne_bot (hv.ref_pos i) N N
      (le_bot_iff.mp (h ▸ Finset.le_sup (f := fun i => extVisibilityReplace (v (R.lowRef i)) N N)
        (Finset.mem_univ i)))

/-- With at least one requested block, the selector has exactly the donor's bottom pattern. -/
theorem Active.sel_eq_bot_iff [Nonempty I] {v : R.Low → ExtOrd} (hv : R.Active v)
    (d : Cell P.scheme) : R.sel v d = ⊥ ↔ R.p d = ⊥ := by
  by_cases h : R.p d ≠ ⊥ ∧ R.p d ≠ ⊤
  · simp only [R.sel_of_proper h, h.1, iff_false, min_eq_bot, not_or]
    exact ⟨extVisibilityReplace_ne_bot (hv.ref_pos _) _ _, Active.cut_ne_bot R hv⟩
  by_cases hb : R.p d = ⊥
  · simp only [R.sel_of_bot hb, hb]
  · simp only [R.sel_of_top (not_not.mp fun ht => h ⟨hb, ht⟩), hb, iff_false]
    exact Active.cut_ne_bot R hv

/-- **The capped-donor lemma, lawfulness**: for every active lawful private section `v`, the
selector `sel v` is lawful on the unchanged request scheme `P`.  With no requested block the
selector is identically bottom. -/
theorem Active.sel_respects {v : R.Low → ExtOrd} (hv : R.Active v) :
    RespectsSemantics P.rows (R.sel v) := by
  rcases isEmpty_or_nonempty I with hI | hI
  · have hsel : R.sel v = fun _ => ⊥ := funext (R.sel_of_isEmpty v)
    rw [hsel]
    exact RespectsSemantics.bot _
  obtain ⟨τ, hτ, -, hread⟩ := R.exists_witness hv.respects
  have hcap := Active.selfVis_cap R hv
  have hsel : (fun d : P.scheme.below (Finset.univ, nP + 1) => R.sel v d.1) =
      fun d => read τ (R.e d.1) := by
    funext d
    exact R.sel_eq_read hτ hread hcap d.1
  have hB : RespectsSemanticsBelow P.rows (Finset.univ, nP + 1)
      (fun d : P.scheme.below (Finset.univ, nP + 1) => read τ (R.e d.1)) := by
    refine (map_respects_iff_rowBlockBottom R.e_respects (fun d => (R.gradeP_lt_N d.1).le)
      (read_boundedMap hτ)).mpr ?_
    refine rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects R.e_respects) ?_
    intro d
    rw [← R.sel_eq_read hτ hread hcap d.1, Active.sel_eq_bot_iff R hv, R.e_eq_bot_iff]
  rw [← hsel] at hB
  exact hB.toRespects (StageType.gradedLe_univ_succ P.scheme)

/-- **The capped-donor lemma, boundary** (7): on the common face the selector is the private
section capped at the cut. -/
theorem Active.sel_face {v : R.Low → ExtOrd} (hv : R.Active v)
    (a : P.scheme.below (R.A, R.KA)) : R.sel v a.1 = min (v (R.lowFace a)) (R.cut v) := by
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
      _ = min (min (v (R.lowFace a)) (v R.capL)) (R.cut v) := by rw [h1]
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
    exact Finset.sup_le fun i _ => hi i

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
theorem sel_actual (d : Cell P.scheme) : R.sel R.vactL d = min (R.p d) (R.cut R.vactL) := by
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

namespace VaughtConjecture.Knight

open Transform Value ExtOrd SharpWitnessComposition AmalgamationPlan

/-! ## Bountifulness with equal indices -/

/-- Bountifulness with the source index allowed to equal the target index. -/
theorem Semantics.IsBountiful.extend {ι : Type*} [DecidableEq ι] {A : Finset ι}
    {D : CellScheme A} {sem : Semantics D} (hb : sem.IsBountiful) {CI BJ : Finset ι × ℕ}
    (hCI : CI ∈ Plan.gradedPlan D.plan) (hBJ : BJ ∈ Plan.gradedPlan D.plan) (h : GradedLe CI BJ)
    {p : D.below CI → ExtOrd} {q : D.below BJ → ExtOrd} {γ : ExtOrd}
    (hp : RespectsSemanticsBelow sem CI p) (hq : RespectsSemanticsBelow sem BJ q)
    (hγ : extVisibilityReplace γ BJ.2 BJ.2 = γ)
    (hcompat : ∀ d : D.below CI, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) :
    ∃ q' : D.below BJ → ExtOrd, RespectsSemanticsBelow sem BJ q' ∧
      (∀ d : D.below BJ, min (q' d) γ = min (q d) γ) ∧
      ∀ d : D.below CI, q' (CellScheme.below.mono h d) = p d := by
  by_cases heq : CI = BJ
  · subst heq
    exact ⟨p, hp, fun d => (hcompat d).symm, fun _ => rfl⟩
  · exact hb CI BJ hCI hBJ h heq p q γ hp hq hγ hcompat

namespace CappedDonor

/-! ## Effective cutoffs -/

/-- The present request fields at cutoff `j`. -/
def effP (nP j : ℕ) : Finset (Fin (nP + 1)) × ℕ := (Finset.univ, min j (nP + 1))

/-- The present private fields at cutoff `j`. -/
def effC (J j : ℕ) : Finset (Fin J) × ℕ := (Finset.univ, min j J)

section Cutoffs

variable {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}

theorem effP_mem {j : ℕ} (hj : 0 < j) : effP nP j ∈ Plan.gradedPlan P.scheme.plan :=
  Plan.mem_gradedPlan.mpr ⟨P.scheme.isPlan.domain_mem, lt_min hj (Nat.succ_pos _), by
    change min j (nP + 1) ≤ (Finset.univ : Finset (Fin (nP + 1))).card
    rw [Finset.card_univ, Fintype.card_fin]
    exact min_le_right _ _⟩

theorem gradeC_le (d : Cell C.scheme) : C.scheme.grade d ≤ J :=
  (C.scheme.grade_le_card_scope d).trans (by simpa using Finset.card_le_univ (C.scheme.scope d))

theorem effC_mem {j : ℕ} (hj : 0 < j) (hJ : 0 < J) : effC J j ∈ Plan.gradedPlan C.scheme.plan :=
  Plan.mem_gradedPlan.mpr ⟨C.scheme.isPlan.domain_mem, lt_min hj hJ, by
    change min j J ≤ (Finset.univ : Finset (Fin J)).card
    rw [Finset.card_univ, Fintype.card_fin]
    exact min_le_right _ _⟩

end Cutoffs

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  (R : Ref I nP N J P C)

/-! ## Effective grades relative to the reference data -/

include R in
theorem effP_snd_le_N (j : ℕ) : (effP nP j).2 ≤ N := (min_le_right _ _).trans R.arity_lt.le

include R in
theorem effP_snd_le_effC (j : ℕ) : (effP nP j).2 ≤ (effC J j).2 :=
  min_le_min_left j (R.arity_lt.le.trans R.N_le)

/-- Once the cap is present, its whole lower domain is present. -/
theorem capLe {j : ℕ} (hj : N ≤ j) : GradedLe (C.scheme.cell R.cap) (effC J j) := by
  rw [R.cap_cell]
  exact ⟨Finset.subset_univ _, le_min hj R.N_le⟩

/-- The cap as a present field. -/
def capC {j : ℕ} (hj : N ≤ j) : C.scheme.below (effC J j) :=
  CellScheme.below.mono (R.capLe hj) R.capL

/-- The restriction of a present private section to the cap's lower domain. -/
def lowC {j : ℕ} (hj : N ≤ j) (v : C.scheme.below (effC J j) → ExtOrd) (d : R.Low) : ExtOrd :=
  v (CellScheme.below.mono (R.capLe hj) d)

theorem lowC_respects {j : ℕ} (hj : N ≤ j) {v : C.scheme.below (effC J j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC J j) v) :
    RespectsSemanticsBelow C.rows (C.scheme.cell R.cap) (R.lowC hj v) :=
  hv.mono (R.capLe hj)

include R in
theorem selfVis_N_of_effC {j : ℕ} (hj : N ≤ j) {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) :
    SelfVis N γ := hγ.mono (le_min hj R.N_le)

include R in
theorem selfVis_effP_of_effC {j : ℕ} {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) :
    SelfVis (effP nP j).2 γ := hγ.mono (R.effP_snd_le_effC j)

include R in
/-- An `N`-visible cut is permissible at the request scheme's own effective grade. -/
theorem selfVis_effP_of_N (j : ℕ) {β : ExtOrd} (hβ : SelfVis N β) : SelfVis (effP nP j).2 β :=
  hβ.mono (R.effP_snd_le_N j)

/-! ## The present portion of the face -/

/-- A face cell present at cutoff `j` as a present request field. -/
def reqFace {j : ℕ} (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j) :
    P.scheme.below (effP nP j) :=
  ⟨a.1, ⟨Finset.subset_univ _, le_min h (gradeP_le a.1)⟩⟩

/-- The private copy of a face cell present at cutoff `j` as a present private field. -/
def privFace {j : ℕ} (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j) :
    C.scheme.below (effC J j) :=
  ⟨(R.face a).1, ⟨Finset.subset_univ _, le_min ((R.face_grade a).trans_le h) (gradeC_le _)⟩⟩

/-- Every face cell is present once the cap is. -/
theorem face_grade_le_of_N {j : ℕ} (hj : N ≤ j) (a : P.scheme.below (R.A, R.KA)) :
    P.scheme.grade a.1 ≤ j := a.2.2.trans (R.KA_lt_N.le.trans hj)

/-- The present portion `(A, min KA j)` of the face at cutoff `j`. -/
theorem face_le_effP {j : ℕ} : GradedLe (R.A, min R.KA j) (effP nP j) :=
  ⟨Finset.subset_univ _, le_min (min_le_right _ _) ((min_le_left _ _).trans R.KA_le)⟩

theorem face_le_effC {j : ℕ} : GradedLe (R.A', min R.KA j) (effC J j) :=
  ⟨Finset.subset_univ _, le_min (min_le_right _ _)
    ((min_le_left _ _).trans (R.KA_lt_N.le.trans R.N_le))⟩

/-- No face cell is present when the present portion has grade zero. -/
theorem face_absent {j : ℕ} (hk : ¬ 0 < min R.KA j) (a : P.scheme.below (R.A, R.KA))
    (h : P.scheme.grade a.1 ≤ j) : False :=
  hk (lt_min ((P.scheme.grade_pos a.1).trans_le a.2.2) ((P.scheme.grade_pos a.1).trans_le h))

/-- A private section read on the present portion of the request copy of the face. -/
def faceSec {j : ℕ} (v : C.scheme.below (effC J j) → ExtOrd)
    (a : P.scheme.below (R.A, min R.KA j)) : ExtOrd :=
  v (R.privFace (R.faceLift (min_le_left _ _) a) (a.2.2.trans (min_le_right _ _)))

theorem faceSec_respects {j : ℕ} {v : C.scheme.below (effC J j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC J j) v) :
    RespectsSemanticsBelow P.rows (R.A, min R.KA j) (R.faceSec v) :=
  (R.faceAt_respects (min_le_left _ _) _).mp (hv.mono R.face_le_effC)

theorem lowC_face {j : ℕ} (hj : N ≤ j) (v : C.scheme.below (effC J j) → ExtOrd)
    (a : P.scheme.below (R.A, R.KA)) :
    R.lowC hj v (R.lowFace a) = v (R.privFace a (R.face_grade_le_of_N hj a)) := rfl

/-! ## States and admissibility -/

/-- A state at cutoff `j`: the present numerical sections, the gate, and the numerical
persistent shadows of every field (present or future). -/
structure State (R : Ref I nP N J P C) (j : ℕ) where
  /-- The current request section. -/
  u : P.scheme.below (effP nP j) → ExtOrd
  /-- The current private section. -/
  v : C.scheme.below (effC J j) → ExtOrd
  /-- The free grade-one gate. -/
  gate : ExtOrd
  /-- The persistent grade-one shadow of every request field. -/
  shadowP : Cell P.scheme → ExtOrd
  /-- The persistent grade-one shadow of every private field. -/
  shadowC : Cell C.scheme → ExtOrd

/-- **Admissibility** (notes32 §4): lawful sections, the literal common face on its present
portion (at every cutoff), `1`-visible gate and shadows, shadows carrying the present numerical
supports, the support guard (11), and the numerical relation (10) whenever the cap is present,
the gate is positive and the cap is positive. -/
structure Admissible {j : ℕ} (st : R.State j) : Prop where
  u_respects : RespectsSemanticsBelow P.rows (effP nP j) st.u
  v_respects : RespectsSemanticsBelow C.rows (effC J j) st.v
  face : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
    st.u (R.reqFace a h) = st.v (R.privFace a h)
  gate_vis : SelfVis 1 st.gate
  shadowP_vis : ∀ d, SelfVis 1 (st.shadowP d)
  shadowC_vis : ∀ d, SelfVis 1 (st.shadowC d)
  shadowP_iff : ∀ d : P.scheme.below (effP nP j), st.shadowP d.1 ≠ ⊥ ↔ st.u d ≠ ⊥
  shadowC_iff : ∀ d : C.scheme.below (effC J j), st.shadowC d.1 ≠ ⊥ ↔ st.v d ≠ ⊥
  support : st.gate ≠ ⊥ → st.shadowC R.cap ≠ ⊥ →
    (∀ i, st.shadowC (R.ref i) ≠ ⊥) ∧ ∀ d, st.shadowP d ≠ ⊥ ↔ R.p d ≠ ⊥
  relation : ∀ (hj : N ≤ j), st.gate ≠ ⊥ → st.v (R.capC hj) ≠ ⊥ →
    ∀ d : P.scheme.below (effP nP j),
      min (st.u d) (R.cut (R.lowC hj st.v)) = R.sel (R.lowC hj st.v) d.1

/-- In an active admissible state the restricted private section is active for the selector. -/
theorem Admissible.active {j : ℕ} {st : R.State j} (hst : R.Admissible st) (hj : N ≤ j)
    (hg : st.gate ≠ ⊥) (hc : st.v (R.capC hj) ≠ ⊥) : R.Active (R.lowC hj st.v) := by
  obtain ⟨href, hsupp⟩ := hst.support hg ((hst.shadowC_iff (R.capC hj)).mpr hc)
  refine ⟨R.lowC_respects hj hst.v_respects, hc, fun i => ?_, ?_⟩
  · exact (hst.shadowC_iff (CellScheme.below.mono (R.capLe hj) (R.lowRef i))).mp (href i)
  · intro a ha
    have hu : st.u (R.reqFace a (R.face_grade_le_of_N hj a)) = ⊥ := by
      by_contra hne
      exact (hsupp a.1).mp ((hst.shadowP_iff _).mpr hne) ha
    rw [R.lowC_face, ← hst.face a (R.face_grade_le_of_N hj a), hu]

/-! ## Cap receipts, persistence at a positive cap, and the bottom-cap state -/

/-- **Cap receipts**: the gate and every shadow of the new state agree with the old ones below
the comparison cap `γ`. -/
def CapReceipts {j : ℕ} (γ : ExtOrd) (st st₁ : R.State j) : Prop :=
  min st₁.gate γ = min st.gate γ ∧ (∀ d, min (st₁.shadowP d) γ = min (st.shadowP d) γ) ∧
    ∀ d, min (st₁.shadowC d) γ = min (st.shadowC d) γ

theorem capReceipts_bot {j : ℕ} (st st₁ : R.State j) : R.CapReceipts ⊥ st st₁ :=
  ⟨by rw [min_bot_right, min_bot_right], fun _ => by rw [min_bot_right, min_bot_right],
    fun _ => by rw [min_bot_right, min_bot_right]⟩

theorem capReceipts_of_eq {j : ℕ} (γ : ExtOrd) {st st₁ : R.State j} (hg : st₁.gate = st.gate)
    (hP : st₁.shadowP = st.shadowP) (hC : st₁.shadowC = st.shadowC) : R.CapReceipts γ st st₁ :=
  ⟨by rw [hg], fun _ => by rw [hP], fun _ => by rw [hC]⟩

/-- **Persistence**: at a positive cap the gate and every shadow are retained; new lawful
sections agreeing with the old ones below the cap, with the literal face and the relation, form
an admissible state. -/
theorem admissible_persist {j : ℕ} {st : R.State j} (hst : R.Admissible st) {γ : ExtOrd}
    (hγ : γ ≠ ⊥) {u₁ : P.scheme.below (effP nP j) → ExtOrd}
    {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁)
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    (hu : ∀ d, min (u₁ d) γ = min (st.u d) γ) (hv : ∀ d, min (v₁ d) γ = min (st.v d) γ)
    (hface : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      u₁ (R.reqFace a h) = v₁ (R.privFace a h))
    (hrel : ∀ (hj : N ≤ j), st.gate ≠ ⊥ → v₁ (R.capC hj) ≠ ⊥ →
      ∀ d : P.scheme.below (effP nP j),
        min (u₁ d) (R.cut (R.lowC hj v₁)) = R.sel (R.lowC hj v₁) d.1) :
    R.Admissible ⟨u₁, v₁, st.gate, st.shadowP, st.shadowC⟩ where
  u_respects := hu₁
  v_respects := hv₁
  face := hface
  gate_vis := hst.gate_vis
  shadowP_vis := hst.shadowP_vis
  shadowC_vis := hst.shadowC_vis
  shadowP_iff d := by
    rw [hst.shadowP_iff d]
    exact not_congr (bottom_pattern_of_cap_agreement hγ hu d).symm
  shadowC_iff d := by
    rw [hst.shadowC_iff d]
    exact not_congr (bottom_pattern_of_cap_agreement hγ hv d).symm
  support := hst.support
  relation := hrel

open Classical in
/-- **The bottom-cap state**: the gate switched off, the shadows of the present fields
recomputed as the `1`-visible roundings of the new sections, the shadows of the future fields
retained. -/
noncomputable def offState {j : ℕ} (st : R.State j) (u₁ : P.scheme.below (effP nP j) → ExtOrd)
    (v₁ : C.scheme.below (effC J j) → ExtOrd) : R.State j where
  u := u₁
  v := v₁
  gate := ⊥
  shadowP d := if h : GradedLe (P.scheme.cell d) (effP nP j) then
    extVisibilityReplace (u₁ ⟨d, h⟩) 1 1 else st.shadowP d
  shadowC d := if h : GradedLe (C.scheme.cell d) (effC J j) then
    extVisibilityReplace (v₁ ⟨d, h⟩) 1 1 else st.shadowC d

open Classical in
theorem admissible_off {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    {u₁ : P.scheme.below (effP nP j) → ExtOrd} {v₁ : C.scheme.below (effC J j) → ExtOrd}
    (hu₁ : RespectsSemanticsBelow P.rows (effP nP j) u₁)
    (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    (hface : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      u₁ (R.reqFace a h) = v₁ (R.privFace a h)) :
    R.Admissible (R.offState st u₁ v₁) where
  u_respects := hu₁
  v_respects := hv₁
  face := hface
  gate_vis := selfVis_bot 1
  shadowP_vis d := by
    change SelfVis 1 (if h : GradedLe (P.scheme.cell d) (effP nP j) then
      extVisibilityReplace (u₁ ⟨d, h⟩) 1 1 else st.shadowP d)
    split_ifs
    · exact TopSupport.selfVis_evr_self 1 _
    · exact hst.shadowP_vis d
  shadowC_vis d := by
    change SelfVis 1 (if h : GradedLe (C.scheme.cell d) (effC J j) then
      extVisibilityReplace (v₁ ⟨d, h⟩) 1 1 else st.shadowC d)
    split_ifs
    · exact TopSupport.selfVis_evr_self 1 _
    · exact hst.shadowC_vis d
  shadowP_iff d := by
    change (if h : GradedLe (P.scheme.cell d.1) (effP nP j) then
      extVisibilityReplace (u₁ ⟨d.1, h⟩) 1 1 else st.shadowP d.1) ≠ ⊥ ↔ u₁ d ≠ ⊥
    rw [dite_eq_left d.2]
    exact not_congr (evr_eq_bot_iff 1 1)
  shadowC_iff d := by
    change (if h : GradedLe (C.scheme.cell d.1) (effC J j) then
      extVisibilityReplace (v₁ ⟨d.1, h⟩) 1 1 else st.shadowC d.1) ≠ ⊥ ↔ v₁ d ≠ ⊥
    rw [dite_eq_left d.2]
    exact not_congr (evr_eq_bot_iff 1 1)
  support h := (h rfl).elim
  relation _ h := (h rfl).elim

/-! ## Installing a face prescription by old bountifulness -/

/-- Old `P`-bountifulness installs a lawful private face prescription into a request section at
a permissible cap, on the present portion of the face; nothing is done when that portion is
empty. -/
theorem exists_installP {j : ℕ} {u : P.scheme.below (effP nP j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effP nP j) u)
    {v₁ : C.scheme.below (effC J j) → ExtOrd} (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    {γ : ExtOrd} (hγ : SelfVis (effP nP j).2 γ)
    (hcompat : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      min (u (R.reqFace a h)) γ = min (v₁ (R.privFace a h)) γ) :
    ∃ u₁ : P.scheme.below (effP nP j) → ExtOrd, RespectsSemanticsBelow P.rows (effP nP j) u₁ ∧
      (∀ d, min (u₁ d) γ = min (u d) γ) ∧
      ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
        u₁ (R.reqFace a h) = v₁ (R.privFace a h) := by
  by_cases hk : 0 < min R.KA j
  · obtain ⟨u₁, hu₁, hcap, hface⟩ := P.bountiful.extend (R.face_mem hk (min_le_left _ _))
      (effP_mem (hk.trans_le (min_le_right _ _))) R.face_le_effP (R.faceSec_respects hv₁) hu hγ
      (fun a => hcompat (R.faceLift (min_le_left _ _) a) (a.2.2.trans (min_le_right _ _)))
    exact ⟨u₁, hu₁, hcap, fun a h => hface ⟨a.1, ⟨a.2.1, le_min a.2.2 h⟩⟩⟩
  · exact ⟨u, hu, fun _ => rfl, fun a h => (R.face_absent hk a h).elim⟩

/-! ## Clipping the coordinates of grade at least `N` -/

/-! ## The private-context-prescribed fibre (notes32 §5) -/

/-- **The private fibre**: an independently lawful private prescription `v₁` agreeing with the
current private section below a permissible cap `γ` lifts to an admissible state retaining `v₁`
literally, the whole request cap vector `u ∧ γ`, the entire common face, the cap receipts of the
gate and of every shadow — and, at a positive cap, the gate and every shadow literally.  The only
extension operation is old `P`-bountifulness. -/
theorem exists_private_lift {j : ℕ} {st : R.State j} (hst : R.Admissible st)
    {v₁ : C.scheme.below (effC J j) → ExtOrd} (hv₁ : RespectsSemanticsBelow C.rows (effC J j) v₁)
    {γ : ExtOrd} (hγ : SelfVis (effC J j).2 γ) (hagree : ∀ d, min (v₁ d) γ = min (st.v d) γ) :
    ∃ st₁ : R.State j, R.Admissible st₁ ∧ st₁.v = v₁ ∧ (∀ d, min (st₁.u d) γ = min (st.u d) γ) ∧
      R.CapReceipts γ st st₁ ∧
      (γ ≠ ⊥ → st₁.gate = st.gate ∧ st₁.shadowP = st.shadowP ∧ st₁.shadowC = st.shadowC) := by
  have hcompat : ∀ (a : P.scheme.below (R.A, R.KA)) (h : P.scheme.grade a.1 ≤ j),
      min (st.u (R.reqFace a h)) γ = min (v₁ (R.privFace a h)) γ := by
    intro a h
    rw [hst.face a h]
    exact (hagree _).symm
  by_cases hbot : γ = ⊥
  · -- bottom cap: switch the gate off
    subst hbot
    obtain ⟨u₁, hu₁, hcap, hface⟩ := R.exists_installP hst.u_respects hv₁ (selfVis_bot _) hcompat
    exact ⟨R.offState st u₁ v₁, R.admissible_off hst hu₁ hv₁ hface, rfl, hcap,
      R.capReceipts_bot _ _, fun h => absurd rfl h⟩
  have hγP : SelfVis (effP nP j).2 γ := R.selfVis_effP_of_effC hγ
  have hpat := bottom_pattern_of_cap_agreement hbot hagree
  by_cases hact : ∃ hj : N ≤ j, st.gate ≠ ⊥ ∧ st.v (R.capC hj) ≠ ⊥
  · obtain ⟨hj, hg, hc⟩ := hact
    have hγN : SelfVis N γ := R.selfVis_N_of_effC hj hγ
    have hA₀ := Admissible.active R hst hj hg hc
    have hrel₀ := hst.relation hj hg hc
    have hA₁ : R.Active (R.lowC hj v₁) :=
      ⟨R.lowC_respects hj hv₁, fun h => hc ((hpat _).mp h),
        fun i h => hA₀.ref_pos i ((hpat _).mp h), fun a ha => (hpat _).mpr (hA₀.face_bot a ha)⟩
    have hVγ : (fun d => min (R.lowC hj v₁ d) γ) = fun d => min (R.lowC hj st.v d) γ :=
      funext fun d => hagree _
    have hcutγ : min (R.cut (R.lowC hj v₁)) γ = min (R.cut (R.lowC hj st.v)) γ := by
      rw [← R.cut_min hγN, ← R.cut_min hγN, hVγ]
    have hselγ : ∀ e, min (R.sel (R.lowC hj v₁) e) γ = min (R.sel (R.lowC hj st.v) e) γ := by
      intro e
      rw [← R.sel_min hγN, ← R.sel_min hγN, hVγ]
    have hcutvis : SelfVis N (R.cut (R.lowC hj v₁)) :=
      R.selfVis_cut (Active.selfVis_cap R hA₁)
    by_cases hβ : R.cut (R.lowC hj v₁) ≤ γ
    · -- the cut is at most the cap: extend from the old ambient at `γ`
      obtain ⟨u₁, hu₁, hcap, hface⟩ := R.exists_installP hst.u_respects hv₁ hγP hcompat
      refine ⟨⟨u₁, v₁, st.gate, st.shadowP, st.shadowC⟩,
        R.admissible_persist hst hbot hu₁ hv₁ hcap hagree hface ?_, rfl, hcap,
        R.capReceipts_of_eq γ rfl rfl rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
      intro hj' _ _ d
      change min (u₁ d) (R.cut (R.lowC hj v₁)) = R.sel (R.lowC hj v₁) d.1
      have hβ' : R.cut (R.lowC hj v₁) = min (R.cut (R.lowC hj st.v)) γ := by
        rw [← hcutγ, min_eq_left hβ]
      calc min (u₁ d) (R.cut (R.lowC hj v₁))
          = min (min (u₁ d) γ) (R.cut (R.lowC hj v₁)) := by rw [min_assoc, min_eq_right hβ]
        _ = min (min (st.u d) γ) (R.cut (R.lowC hj v₁)) := by rw [hcap d]
        _ = min (st.u d) (R.cut (R.lowC hj v₁)) := by rw [min_assoc, min_eq_right hβ]
        _ = min (min (st.u d) (R.cut (R.lowC hj st.v))) γ := by rw [hβ', min_assoc]
        _ = min (R.sel (R.lowC hj st.v) d.1) γ := by rw [hrel₀ d]
        _ = min (R.sel (R.lowC hj v₁) d.1) γ := (hselγ d.1).symm
        _ = R.sel (R.lowC hj v₁) d.1 := min_eq_left ((R.sel_le_cut _ d.1).trans hβ)
    · -- the cap is below the cut: extend from the lawful selector at the cut
      have hγβ : γ ≤ R.cut (R.lowC hj v₁) := (not_le.mp hβ).le
      obtain ⟨u₁, hu₁, hcap₁, hface₁⟩ := R.exists_installP
        (u := fun d => R.sel (R.lowC hj v₁) d.1) ((Active.sel_respects R hA₁).toBelow _) hv₁
        (R.selfVis_effP_of_N j hcutvis) (by
          intro a h
          change min (R.sel (R.lowC hj v₁) a.1) (R.cut (R.lowC hj v₁)) =
            min (v₁ (R.privFace a h)) (R.cut (R.lowC hj v₁))
          rw [Active.sel_face R hA₁ a, R.lowC_face, min_assoc, min_self])
      have hrel₁ : ∀ d, min (u₁ d) (R.cut (R.lowC hj v₁)) = R.sel (R.lowC hj v₁) d.1 := by
        intro d
        rw [hcap₁ d]
        exact min_eq_left (R.sel_le_cut _ d.1)
      have hcap : ∀ d, min (u₁ d) γ = min (st.u d) γ := by
        intro d
        calc min (u₁ d) γ
            = min (min (u₁ d) (R.cut (R.lowC hj v₁))) γ := by
              rw [min_assoc, min_eq_right hγβ]
          _ = min (R.sel (R.lowC hj v₁) d.1) γ := by rw [hrel₁ d]
          _ = min (R.sel (R.lowC hj st.v) d.1) γ := hselγ d.1
          _ = min (min (st.u d) (R.cut (R.lowC hj st.v))) γ := by rw [hrel₀ d]
          _ = min (st.u d) (min (R.cut (R.lowC hj v₁)) γ) := by rw [min_assoc, hcutγ]
          _ = min (st.u d) γ := by rw [min_eq_right hγβ]
      refine ⟨⟨u₁, v₁, st.gate, st.shadowP, st.shadowC⟩,
        R.admissible_persist hst hbot hu₁ hv₁ hcap hagree hface₁ ?_, rfl, hcap,
        R.capReceipts_of_eq γ rfl rfl rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
      intro _ _ _ d
      exact hrel₁ d
  · -- inactive: plain matching-face bountifulness; the relation stays vacuous
    obtain ⟨u₁, hu₁, hcap, hface⟩ := R.exists_installP hst.u_respects hv₁ hγP hcompat
    refine ⟨⟨u₁, v₁, st.gate, st.shadowP, st.shadowC⟩,
      R.admissible_persist hst hbot hu₁ hv₁ hcap hagree hface ?_, rfl, hcap,
      R.capReceipts_of_eq γ rfl rfl rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
    intro hj hg hc
    exact absurd ⟨hj, hg, fun h => hc ((hpat _).mpr h)⟩ hact

/-! ## The request-prescribed fibre (notes32 §6) -/

/-! ## The actual state -/

/-- The actual pair — the donor on the request scheme and the actual private labelling — with
the gate on and the shadows the `1`-visible roundings of the actual values, at any cutoff. -/
noncomputable def actualState (j : ℕ) : R.State j where
  u d := R.p d.1
  v d := R.vact d.1
  gate := ⊤
  shadowP d := extVisibilityReplace (R.p d) 1 1
  shadowC d := extVisibilityReplace (R.vact d) 1 1

/-- The actual pair is admissible with a positive gate (notes32 §8, first step): it matches on
the face and satisfies the relation by `sel_actual`. -/
theorem actual_admissible (j : ℕ) : R.Admissible (R.actualState j) where
  u_respects := R.p_respects.toBelow _
  v_respects := R.vact_respects.toBelow _
  face a _ := (R.face_actual a).symm
  gate_vis := TopSupport.selfVis_top_ext 1
  shadowP_vis _ := TopSupport.selfVis_evr_self 1 _
  shadowC_vis _ := TopSupport.selfVis_evr_self 1 _
  shadowP_iff _ := not_congr (evr_eq_bot_iff 1 1)
  shadowC_iff _ := not_congr (evr_eq_bot_iff 1 1)
  support _ _ := ⟨fun i => by
    change extVisibilityReplace (R.vact (R.ref i)) 1 1 ≠ ⊥
    rw [R.vact_ref, ne_eq, evr_eq_bot_iff]
    exact ofOrd_ne_bot _, fun _ => not_congr (evr_eq_bot_iff 1 1)⟩
  relation _ _ _ d := by
    change min (R.p d.1) (R.cut R.vactL) = R.sel R.vactL d.1
    exact (R.sel_actual d.1).symm

end Ref

end CappedDonor

end VaughtConjecture.Knight
