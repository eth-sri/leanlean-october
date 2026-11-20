/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorSource

/-! # The two-threshold (LOW/HIGH) receiving family: low reference, states, policy (audit16 §1)

The reviewer's audit16 / `same_grade_LOW_HIGH.md` (audit-notes4) strengthen the receiving family
of `Knight/CappedDonorReceiving.lean` by a **stored cutoff** `b` of numerical grade `K` and a
second numerical condition **LOW**, present from grade `K`, next to the selector relation
**HIGH** of grade `N`.  This module sets up the data; the row operations, the fibres and the
normalization are in the following modules.

**The low reference** (`LowRef`): an original grade-`K` owner `c` of the private scheme whose
scope contains the private copy of the common face, a source cell `r ≤ c`, and the **strict
source gap** (GAP) on the *original* row of `c`, stated as explicit inputs:

    h = R_K(E_c r) < E_c c,      h < E_c a   for every donor-top face cell a.

Every donor-top occurrence has grade at most `K` (`top_grade`) and `K < N`.  **No bound on the
root arity** is imposed (newapproach2 §3.2): only the grade-`≤ K` part of the face lies in the
owner's lower domain (`faceLow`), and that is all the low reference reads — every donor-top face
cell has grade at most `K`, so its source gap is stated.  Nothing here is derived from the
receiving construction; these are the reference-row facts the note lists as inputs.

**The frontier** `e v = v c ∧ R_K (v r)` of a lawful section is `K`-visible (`e_selfVis`), at
most every donor-top face value (`e_le_top`, from GAP through the exact normalized witness of
the section at `c`), and commutes with every `K`-visible cap (`e_min`).

**Two-threshold states** (`TState`): a receiving state together with the stored cutoff.
**Admissibility** (`TAdmissible`): the receiving admissibility, `1`-visibility of `b` (its
persistent observation) and `K`-visibility once `b` is numerically present (`K ≤ j`), and, for a
positive gate,

    LOW  (K ≤ j) :  m(u) < b < H  ⟹  max b (e v) ≤ u t   for every donor-top field t,
    HIGH (N ≤ j) :  b ∧ H = cut v,

where `m(u)` is the maximum of the request fields with a non-top donor label (present or
future, read from the source vector, empty maximum bottom: `nonTopMax`) and `H` is the cap field
(numerical once present, persistent before: `capField`).  The selector half of HIGH is the
receiving relation.

**The cutoff policy** (`policy`, audit16 (2)): below `N` a positive-cap repair keeps `b` when
`H ≤ b` and clips it at the comparison cap otherwise; it is `K`-visible, carries `b`'s cap
receipt (`policy_min`), and can only activate LOW when it is the clipped value below the cap
(`policy_barrier`).  The **actual pair** with `b` the actual cut is admissible: HIGH is
`cut_actual ≤ vact cap` and LOW is discharged because every donor-top field is literally top
(`actual_tadmissible`), without imposing any physical history. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

/-! ## Order facts about visibility replacement -/

/-- A `k`-visible value strictly below `x` stays strictly below every `k`-replacement of `x`. -/
theorem lt_evr_of_selfVis_lt {k i : ℕ} {a x : ExtOrd} (ha : SelfVis k a) (hax : a < x) :
    a < extVisibilityReplace x k i := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
  · exact absurd hax not_lt_bot
  · rw [extVisibilityReplace_top]; exact hax
  · rw [extVisibilityReplace_ofOrd]
    unfold visibilityReplace
    split_ifs with hβ
    · unfold ordinalReplace
      rcases ExtOrd.cases a with rfl | rfl | ⟨α, rfl⟩
      · exact bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)
      · exact absurd hax not_top_lt
      · rw [selfVis_ofOrd_iff] at ha
        rw [ofOrd_lt_ofOrd] at hax ⊢
        apply lt_of_limitPart_lt
        rw [limitPart_limitPart_add_nat]
        by_contra hle
        have hle' : limitPart β ≤ limitPart α := not_lt.mp hle
        have h1 : limitPart β + (k : Ordinal) ≤ α :=
          calc limitPart β + (k : Ordinal) ≤ limitPart α + k := add_le_add_left hle' _
            _ ≤ limitPart α + (finitePart α : Ordinal) :=
              (add_le_add_iff_left _).mpr (Nat.cast_le.mpr ha)
            _ = α := decomposition α
        have h2 : β < limitPart β + (k : Ordinal) := by
          conv_lhs => rw [← decomposition β]
          exact (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hβ)
        exact absurd (h2.trans_le h1) (not_lt.mpr hax.le)
    · exact hax

/-- A replacement through `k ≤ K` of a value at most a `K`-visible `b` stays at most `b`. -/
theorem evr_le_of_le_selfVis {K k i : ℕ} {b x : ExtOrd} (hb : SelfVis K b) (hk : k ≤ K)
    (hi : i ≤ k) (hx : x ≤ b) : extVisibilityReplace x k i ≤ b :=
  extVisibilityReplace_le_of_le_selfVis hi (hb.mono hk) hx

/-- Cap agreement below a cap pins every value strictly below the cap. -/
theorem eq_of_capAgree_of_lt {x y γ : ExtOrd} (h : min x γ = min y γ) (hx : x < γ) : y = x := by
  rw [min_eq_left hx.le] at h
  rcases le_total y γ with hy | hy
  · rw [min_eq_left hy] at h
    exact h.symm
  · rw [min_eq_right hy] at h
    exact absurd h hx.ne

/-- Cap agreement below a cap and a value at least the cap force the other value at least the
cap. -/
theorem le_of_capAgree_of_le {x y γ : ExtOrd} (h : min x γ = min y γ) (hx : γ ≤ x) : γ ≤ y := by
  rw [min_eq_right hx] at h
  exact h.symm ▸ min_le_left _ _

namespace CappedDonor

/-! ## The cutoff policy -/

/-- **The floor cap** (audit16 (4)): floors built from cap-equivalent data are cap-equivalent. -/
theorem floor_min {b b' e e' γ : ExtOrd} (hb : min b' γ = min b γ) (he : min e' γ = min e γ) :
    min (max b' e') γ = min (max b e) γ := by
  rw [min_max_distrib_right, min_max_distrib_right, hb, he]

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  (R : Ref I nP N J P C)

/-! ## The low reference -/

/-- **The low reference** (same_grade_LOW_HIGH §2, explicit inputs): an original grade-`K` owner
`c` of the private scheme whose scope contains the private copy of the face, a source cell
`r ≤ c`, the strict source gap on the original row of `c`, and the grade bounds: donor-top
occurrences have grade at most `K`, and `K < N`.  The root arity is unrestricted. -/
structure LowRef (K : ℕ) where
  K_pos : 1 ≤ K
  K_lt_N : K < N
  /-- The low reference owner. -/
  c : Cell C.scheme
  c_grade : C.scheme.grade c = K
  /-- The low reference source, below its owner. -/
  r : C.scheme.below (C.scheme.cell c)
  /-- The private copy of the face lies in the owner's scope. -/
  A'_sub : R.A' ⊆ C.scheme.scope c
  /-- Every donor-top occurrence has grade at most `K`. -/
  top_grade : ∀ d, R.p d = ⊤ → P.scheme.grade d ≤ K
  /-- The strict source gap at the owner (GAP). -/
  gap_c : extVisibilityReplace (C.rows.E c r) K K < C.rows.E c ⟨c, GradedLe.refl _⟩
  /-- The strict source gap at every donor-top face cell (GAP). -/
  gap_top : ∀ (a : P.scheme.below (R.A, R.KA))
    (h : GradedLe (C.scheme.cell (R.face a).1) (C.scheme.cell c)),
    R.p a.1 = ⊤ → extVisibilityReplace (C.rows.E c r) K K < C.rows.E c ⟨(R.face a).1, h⟩

namespace LowRef

variable {R} {K : ℕ} (L : R.LowRef K)

/-- The lower domain of the low reference owner. -/
abbrev Dom : Type := C.scheme.below (C.scheme.cell L.c)

/-- The owner in its own lower domain. -/
def cL : L.Dom := ⟨L.c, GradedLe.refl _⟩

/-- The rounded source of the low reference. -/
noncomputable def h : ExtOrd := extVisibilityReplace (C.rows.E L.c L.r) K K

/-! ## The frontier -/

/-- The frontier `e v = v c ∧ R_K (v r)`. -/
noncomputable def e (v : L.Dom → ExtOrd) : ExtOrd :=
  min (v L.cL) (extVisibilityReplace (v L.r) K K)

section Lawful

variable {v : L.Dom → ExtOrd} (hv : RespectsSemanticsBelow C.rows (C.scheme.cell L.c) v)
include hv

end Lawful

/-! ## The frontier at a cutoff -/

theorem domLe {j : ℕ} (hj : K ≤ j) : GradedLe (C.scheme.cell L.c) (effC J j) :=
  ⟨Finset.subset_univ _, by
    change C.scheme.grade L.c ≤ min j J
    rw [L.c_grade]; exact le_min hj (L.K_lt_N.le.trans R.N_le)⟩

/-- The restriction of a present private section to the owner's lower domain. -/
def lowD {j : ℕ} (hj : K ≤ j) (v : C.scheme.below (effC J j) → ExtOrd) (d : L.Dom) : ExtOrd :=
  v (CellScheme.below.mono (L.domLe hj) d)

/-- The frontier of a present private section. -/
noncomputable def eC {j : ℕ} (hj : K ≤ j) (v : C.scheme.below (effC J j) → ExtOrd) : ExtOrd :=
  L.e (L.lowD hj v)

end LowRef

/-! ## Two-threshold states -/

/-- A two-threshold state: a receiving state and the stored cutoff. -/
structure TState (R : Ref I nP N J P C) (j : ℕ) where
  /-- The receiving state. -/
  st : R.State j
  /-- The stored cutoff. -/
  b : ExtOrd

variable {R}

open Classical in
/-- The maximum of the request fields with a non-top donor label, present or future (empty
maximum bottom). -/
noncomputable def State.nonTopMax {j : ℕ} (st : R.State j) : ExtOrd :=
  (Finset.univ.filter fun d : Cell P.scheme => R.p d ≠ ⊤).sup fun d => st.sourceProfile (.req d)

/-- The cap field: numerical once present, persistent before. -/
noncomputable def State.capField {j : ℕ} (st : R.State j) : ExtOrd := st.sourceProfile (.priv R.cap)

/-- **Two-threshold admissibility**: receiving admissibility, `K`-visibility of the stored
cutoff, LOW from grade `K` and HIGH from grade `N` (its selector half is the receiving
relation). -/
structure LowRef.TAdmissible {K : ℕ} (L : R.LowRef K) {j : ℕ} (S : R.TState j) : Prop where
  adm : R.Admissible S.st
  /-- The stored cutoff's persistent grade-one observation. -/
  b_vis : SelfVis 1 S.b
  /-- The stored cutoff is `K`-visible once numerically present. -/
  b_visK : K ≤ j → SelfVis K S.b
  low : ∀ hj : K ≤ j, S.st.gate ≠ ⊥ → S.st.nonTopMax < S.b → S.b < S.st.capField →
    ∀ t (ht : R.p t = ⊤),
      max S.b (L.eC hj S.st.v) ≤ S.st.u (reqCell t ((L.top_grade t ht).trans hj))
  high : ∀ hj : N ≤ j, S.st.gate ≠ ⊥ → min S.b (S.st.v (R.capC hj)) = R.cut (R.lowC hj S.st.v)

/-! ## The actual state -/

variable (R) in
/-- The actual two-threshold state: the actual pair with the stored cutoff the actual cut. -/
noncomputable def actualTState (j : ℕ) : R.TState j := ⟨R.actualState j, R.cut R.vactL⟩

/-- The actual state is admissible: HIGH because the actual cut is below the actual cap, LOW
because every donor-top field is literally top — no physical history is imposed. -/
theorem LowRef.actual_tadmissible {K : ℕ} (L : R.LowRef K) (j : ℕ) :
    L.TAdmissible (R.actualTState j) where
  adm := R.actual_admissible j
  b_vis := (R.selfVis_cut (Active.selfVis_cap R R.actual_active)).mono (L.K_pos.trans L.K_lt_N.le)
  b_visK _ := (R.selfVis_cut (Active.selfVis_cap R R.actual_active)).mono L.K_lt_N.le
  low _ _ _ _ t ht := by
    change _ ≤ R.p t
    rw [ht]; exact le_top
  high _ _ := by
    change min (R.cut R.vactL) (R.vact R.cap) = R.cut R.vactL
    exact min_eq_left (R.cut_le_cap _)

end Ref

end CappedDonor

end VaughtConjecture.Knight
