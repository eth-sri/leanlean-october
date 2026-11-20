/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceBlockLocalityTransport
public import VaughtConjecture.Knight.CoupledGradeOne
public import VaughtConjecture.Knight.CountedEncoding
public import VaughtConjecture.Knight.RestrictedComposition
public import VaughtConjecture.Knight.OrbitBlock
public import VaughtConjecture.Knight.Coface

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

theorem evr_monotone (k i : ℕ) (hi : i ≤ k) :
    Monotone (fun x : ExtOrd => extVisibilityReplace x k i) :=
  fun _ _ h => evr_mono h hi

/-- Replacement at grade at most `N` commutes with meets against an `N`-visible value. -/
theorem evr_min_of_selfVis {γ : ExtOrd} {N : ℕ} (hγ : SelfVis N γ) {k i : ℕ} (hk : k ≤ N)
    (hi : i ≤ k) (x : ExtOrd) :
    extVisibilityReplace (min x γ) k i = min (extVisibilityReplace x k i) γ := by
  rw [(evr_monotone k i hi).map_min, evr_eq_self_of_selfVis (hγ.mono hk) i]

/-- A replacement strictly below an `N`-visible value comes from a value strictly below it. -/
theorem lt_of_evr_lt {x γ : ExtOrd} {N i : ℕ} (hγ : SelfVis N γ)
    (h : extVisibilityReplace x N i < γ) : x < γ := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · assumption
  · assumption
  · by_cases hfp : N ≤ finitePart a
    · rwa [extVisibilityReplace_of_le_finitePart hfp] at h
    · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp hfp)] at h
      rcases ExtOrd.cases γ with rfl | rfl | ⟨g, rfl⟩
      · trivial
      · simp
      · rw [selfVis_ofOrd_iff] at hγ
        rw [ofOrd_lt_ofOrd] at h
        apply ofOrd_lt_ofOrd.mpr
        have hl : limitPart a ≤ limitPart g := by
          have := limitPart_mono h.le
          rwa [limitPart_limitPart_add_nat] at this
        rcases hl.lt_or_eq with hlt | heq
        · have h1 := limitPart_add_nat_le_of_lt hlt (finitePart a)
          rw [limitPart_add_finitePart] at h1
          refine lt_of_le_of_ne (h1.trans (limitPart_le g)) fun heq => hlt.ne ?_
          tauto
        · have h1 : a < limitPart a + (finitePart g : Ordinal.{0}) := by
            conv_lhs => rw [← limitPart_add_finitePart a]
            (simp_all <;> omega)
          rwa [heq, limitPart_add_finitePart] at h1

/-- Above an `N`-visible value, every replacement at grade `N` stays above it. -/
theorem le_evr_of_le {x γ : ExtOrd} {N : ℕ} (hγ : SelfVis N γ) (hx : γ ≤ x) (R : ℕ) :
    γ ≤ extVisibilityReplace x N R := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · assumption
  · assumption
  · by_cases hfp : N ≤ finitePart a
    · rwa [extVisibilityReplace_of_le_finitePart hfp]
    · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp hfp)]
      rcases ExtOrd.cases γ with rfl | rfl | ⟨g, rfl⟩
      · simp
      · trivial
      · rw [selfVis_ofOrd_iff] at hγ
        rw [ofOrd_le_ofOrd] at hx
        apply ofOrd_le_ofOrd.mpr
        have hl : limitPart g ≤ limitPart a := limitPart_mono hx
        rcases hl.lt_or_eq with hlt | heq
        · exact (limitPart_add_nat_le_of_lt hlt (finitePart g)).trans' (by
            rw [limitPart_add_finitePart]) |>.trans le_self_add
        · exfalso
          have h1 : limitPart a + (finitePart g : Ordinal.{0}) ≤
              limitPart a + (finitePart a : Ordinal.{0}) := by
            rw [← heq, limitPart_add_finitePart]
            conv_rhs => rw [heq, limitPart_add_finitePart]
            assumption
          (simp_all <;> omega)

/-- An `N`-visible value below a replacement at offset `R < N` is below the value itself. -/
theorem le_of_le_evr {x γ : ExtOrd} {N R : ℕ} (hγ : SelfVis N γ) (hR : R < N)
    (h : γ ≤ extVisibilityReplace x N R) : γ ≤ x := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · assumption
  · assumption
  · by_cases hfp : N ≤ finitePart a
    · rwa [extVisibilityReplace_of_le_finitePart hfp] at h
    · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp hfp)] at h
      rcases ExtOrd.cases γ with rfl | rfl | ⟨g, rfl⟩
      · simp
      · trivial
      · rw [selfVis_ofOrd_iff] at hγ
        rw [ofOrd_le_ofOrd] at h
        apply ofOrd_le_ofOrd.mpr
        have hl : limitPart g ≤ limitPart a := by
          have := limitPart_mono h
          rwa [limitPart_limitPart_add_nat] at this
        rcases hl.lt_or_eq with hlt | heq
        · exact ((limitPart_add_nat_le_of_lt hlt (finitePart g)).trans' (by
            rw [limitPart_add_finitePart])).trans (limitPart_le a)
        · exfalso
          have h1 : limitPart g + (finitePart g : Ordinal.{0}) ≤
              limitPart g + (R : Ordinal.{0}) := by
            rw [limitPart_add_finitePart, heq]; assumption
          (simp_all <;> omega)

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- A lawful section below an index dominating every cell is a lawful whole labelling. -/
theorem RespectsSemantics.of_below_top {top : Finset ι × ℕ} (htop : ∀ d, GradedLe (D.cell d) top)
    {r : D.below top → ExtOrd} (hr : RespectsSemanticsBelow sem top r) :
    RespectsSemantics sem (fun d => r ⟨d, htop d⟩) where
  orderly d := hr.orderly ⟨d, htop d⟩
  locality Sig := hr.locality ⟨Sig, htop Sig⟩
  availability Sig Xi₀ hs hg := by
    obtain ⟨Xi, hc, hle⟩ := hr.availability ⟨Sig, htop Sig⟩ ⟨Xi₀, htop Xi₀⟩ hs hg
    tauto

/-- **Same-bottom-pattern transport** (the reviewer's helper, notes3): a bounded
replacement-commuting image of a lawful section having the bottom flags of a lawful section is
lawful.  No bottom reflection of the scalar map is needed. -/
theorem map_respects_of_same_bottom_pattern {BJ : Finset ι × ℕ} {r q : D.below BJ → ExtOrd}
    (hr : RespectsSemanticsBelow sem BJ r) (hq : RespectsSemanticsBelow sem BJ q) {K : ℕ}
    {ν : ExtOrd → ExtOrd} (hK : ∀ d : D.below BJ, D.grade d.1 ≤ K) (hν : BoundedMap K ν)
    (hpattern : ∀ d, ν (r d) = ⊥ ↔ q d = ⊥) :
    RespectsSemanticsBelow sem BJ (fun d => ν (r d)) :=
  (map_respects_iff_rowBlockBottom hr hK hν).mpr
    (rowBlockBottom_of_same_pattern (rowBlockBottom_of_respects hq) hpattern)

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}

/-- **The request data**: the old cap `C` of grade `N`, the marker offset `R < N`, the
requested-bottom cells `Z`, the exactly requested cells `F` with their old references `ρ` and
offsets `off`, the high cells `T`, and the old marker `a`.  References and marker lie below
the cap. -/
structure Requests (DA : CellScheme A) (DQ : CellScheme Q) where
  /-- The old cap. -/
  C : Cell DA
  /-- The threshold, the cap's grade. -/
  N : ℕ
  /-- The marker offset (plan 21); the block-floor version is `R = 0`. -/
  R : ℕ
  R_lt_N : R < N
  /-- Requested bottom. -/
  Z : Set (Cell DQ)
  /-- Exactly requested proper values. -/
  F : Set (Cell DQ)
  /-- High values, read by a cutoff. -/
  T : Set (Cell DQ)
  /-- The old reference of an exact request, below the cap. -/
  ρ : Cell DQ → DA.below (DA.cell C)
  /-- Its offset. -/
  off : Cell DQ → ℕ
  /-- The old marker, below the cap. -/
  a : DA.below (DA.cell C)

namespace Requests

variable {DA : CellScheme A} {DQ : CellScheme Q} (r : Requests DA DQ)

/-- The cap as a cell of its own lower domain. -/
def capCell : DA.below (DA.cell r.C) := ⟨r.C, GradedLe.refl _⟩

/-- The restriction of an old labelling to the cap's lower domain. -/
def sec (u : Cell DA → ExtOrd) (d : DA.below (DA.cell r.C)) : ExtOrd := u d.1

@[simp] theorem sec_apply (u : Cell DA → ExtOrd) (d : DA.below (DA.cell r.C)) :
    r.sec u d = u d.1 := rfl

@[simp] theorem sec_capCell (u : Cell DA → ExtOrd) : r.sec u r.capCell = u r.C := rfl

/-- `t_f(s)`: the capped replacement of the reference, for a section `s` below the cap. -/
noncomputable def tOf (s : DA.below (DA.cell r.C) → ExtOrd) (f : Cell DQ) : ExtOrd :=
  min (extVisibilityReplace (s (r.ρ f)) r.N (r.off f)) (s r.capCell)

/-- `d(s)`: the capped offset-`R` replacement of the marker. -/
noncomputable def dOf (s : DA.below (DA.cell r.C) → ExtOrd) : ExtOrd :=
  min (extVisibilityReplace (s r.a) r.N r.R) (s r.capCell)

/-- **The target relations** between an old section `s` below the cap and a candidate
labelling `v`. -/
def Correct (s : DA.below (DA.cell r.C) → ExtOrd) (v : Cell DQ → ExtOrd) : Prop :=
  (∀ z ∈ r.Z, min (v z) (s r.capCell) = ⊥) ∧
    (∀ f ∈ r.F, min (v f) (s r.capCell) = r.tOf s f) ∧
    ∀ y ∈ r.T, r.dOf s ≤ min (v y) (s r.capCell)

end Requests

/-- The distinguished old bottom-pattern class, tested on a lower domain only. -/
def InClass {DA : CellScheme A} {BJ : Finset ιA × ℕ} (ZA : Set (DA.below BJ))
    (u : Cell DA → ExtOrd) : Prop :=
  ∀ d : DA.below BJ, u d.1 = ⊥ ↔ d ∈ ZA

/-- **The relative data**: the old scheme with a full-scope grade-`N` cap (cells above the
cap are allowed and untouched), the cleaned donor on the cap's lower domain, the candidate
scheme with its root face, its bountifulness, and the reference template. -/
structure RelativeData (DA : CellScheme A) (semA : Semantics DA) (DQ : CellScheme Q)
    (semQ : Semantics DQ) where
  /-- The requests. -/
  req : Requests DA DQ
  /-- The cap has grade `N`. -/
  grade_C : DA.grade req.C = req.N
  /-- The distinguished bottom pattern, on the lower domain below the cap. -/
  ZA : Set (DA.below (DA.cell req.C))
  C_notin : req.capCell ∉ ZA
  a_notin : req.a ∉ ZA
  ρ_notin : ∀ f ∈ req.F, req.ρ f ∉ ZA
  off_lt : ∀ f ∈ req.F, req.off f ≤ req.N
  /-- The cleaned donor: bottom exactly on the class, the cap's row elsewhere. -/
  e : DA.below (DA.cell req.C) → ExtOrd
  e_bot : ∀ d, e d = ⊥ ↔ d ∈ ZA
  e_eq : ∀ d, d ∉ ZA → e d = semA.E req.C d
  /-- The candidate's root and top indices. -/
  root : Finset ιQ × ℕ
  top : Finset ιQ × ℕ
  root_mem : root ∈ Plan.gradedPlan DQ.plan
  top_mem : top ∈ Plan.gradedPlan DQ.plan
  root_le : GradedLe root top
  root_ne : root ≠ top
  below_top : ∀ d, GradedLe (DQ.cell d) top
  top_le_N : top.2 ≤ req.N
  /-- Root cells are old cells below the cap, and lawful old sections below the cap pull back
  to lawful root sections. -/
  κ : DQ.below root → DA.below (DA.cell req.C)
  hroot : ∀ s : DA.below (DA.cell req.C) → ExtOrd, RespectsSemanticsBelow semA (DA.cell req.C) s →
    RespectsSemanticsBelow semQ root (fun d => s (κ d))
  /-- The candidate is bountiful. -/
  bountiful : semQ.IsBountiful
  /-- Every candidate cell is requested or a root cell. -/
  cover : ∀ d, d ∈ req.Z ∨ d ∈ req.F ∨ d ∈ req.T ∨ ∃ r : DQ.below root, r.1 = d
  /-- The reference template: lawful, the donor on the root, correct against the donor. -/
  V : Cell DQ → ExtOrd
  V_respects : RespectsSemantics semQ V
  V_root : ∀ r : DQ.below root, V r.1 = e (κ r)
  V_correct : req.Correct e V
  /-- The frame inequalities, when high values are requested. -/
  frame : req.T.Nonempty → ∀ f ∈ req.F, req.tOf e f ≤ req.dOf e

namespace RelativeData

variable {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

/-- An **allowed** pair: lawful on both faces, agreeing on the root, correct in the class. -/
def Allowed (u : Cell DA → ExtOrd) (v : Cell DQ → ExtOrd) : Prop :=
  RespectsSemantics semA u ∧ RespectsSemantics semQ v ∧
    (∀ r : DQ.below X.root, v r.1 = u (X.κ r).1) ∧
    (InClass X.ZA u → X.req.Correct (X.req.sec u) v)

theorem grade_le (d : Cell DQ) : DQ.grade d ≤ X.req.N :=
  (X.below_top d).2.trans X.top_le_N

/-- Lawful old labellings pull back to lawful root sections. -/
theorem hroot' (u : Cell DA → ExtOrd) (hu : RespectsSemantics semA u) :
    RespectsSemanticsBelow semQ X.root (fun d => u (X.κ d).1) :=
  X.hroot (fun d => u d.1) (hu.toBelow _)

/-- In the class the cap is nonbottom. -/
theorem cap_ne_bot {u : Cell DA → ExtOrd} (hcls : InClass X.ZA u) : u X.req.C ≠ ⊥ :=
  fun h => X.C_notin ((hcls X.req.capCell).mp h)

/-- **The root lift**: candidate bountifulness at the root–top pair installs a lawful old root
into a lawful candidate ambient at any `N`-visible cap, retaining the ambient's cap reading. -/
theorem lift_root {u' : Cell DA → ExtOrd} (hu' : RespectsSemantics semA u')
    {w : Cell DQ → ExtOrd} (hw : RespectsSemantics semQ w) {γ : ExtOrd}
    (hγ : SelfVis X.req.N γ)
    (hagr : ∀ r : DQ.below X.root, min (w r.1) γ = min (u' (X.κ r).1) γ) :
    ∃ v' : Cell DQ → ExtOrd, RespectsSemantics semQ v' ∧
      (∀ r : DQ.below X.root, v' r.1 = u' (X.κ r).1) ∧ ∀ d, min (v' d) γ = min (w d) γ := by
  obtain ⟨q', hq', hcap, hface⟩ := X.bountiful X.root X.top X.root_mem X.top_mem X.root_le
    X.root_ne (fun d => u' (X.κ d).1) (fun d => w d.1) γ (X.hroot' u' hu') (hw.toBelow X.top)
    (hγ.mono X.top_le_N) (fun d => hagr d)
  refine ⟨fun d => q' ⟨d, X.below_top d⟩, RespectsSemantics.of_below_top X.below_top hq', ?_, ?_⟩
  all_goals tauto

/-- **The capped decoder** of a lawful old labelling at the cap: the exact capped shifter of its
locality at the cap's row, capped at the cap's label — a bounded map reading the donor as the
capped labelling on the distinguished class. -/
theorem decoder {u' : Cell DA → ExtOrd} (hu' : RespectsSemantics semA u')
    (hcls : InClass X.ZA u') :
    ∃ θ : ExtOrd → ExtOrd, BoundedMap X.req.N θ ∧ (∀ x, θ x ≤ u' X.req.C) ∧
      ∀ d, θ (X.e d) = min (X.req.sec u' d) (u' X.req.C) := by
  obtain ⟨τ, hτ, hbound, hread⟩ := hu'.rowWitness X.req.C
  refine ⟨τ, X.grade_C ▸ hτ.bounded, hbound, fun d => ?_⟩
  by_cases hd : d ∈ X.ZA
  · have hb := (X.e_bot d).mpr hd
    have hf := (hcls d).mpr hd
    simp [hb, hf, hτ.bot, Requests.sec]
  · rw [X.e_eq d hd]
    exact hread d

end RelativeData

end VaughtConjecture.Knight
