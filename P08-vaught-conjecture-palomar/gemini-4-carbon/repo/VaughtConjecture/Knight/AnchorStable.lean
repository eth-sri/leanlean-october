/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.ENat.Lattice
public import VaughtConjecture.Knight.TopGradeStableCore
public import VaughtConjecture.Knight.BlockReflection
public import VaughtConjecture.Knight.ReferenceContext
public import VaughtConjecture.Knight.SlackCutPasting
public import VaughtConjecture.Knight.CountedEncoding

@[expose] public section

namespace VaughtConjecture.Knight
open TypeTower StageType KnightRealization Value ExtOrd Transform Filter AmalgamationPlan
universe w

theorem someProvisionalValue_top_form {β : Ordinal.{0}} {n : ℕ} {p : S β n}
    {Xi : Cell p.scheme.scheme} (htop : p.label Xi = ⊤) :
    ∃ j : ℕ, p.someProvisionalValue Xi = ofOrd (β + j) := by
  by_cases hcap : p.ProvisionalCap Xi
  · exact ⟨p.topGrade, someProvisionalValue_of_cap htop hcap⟩
  · obtain ⟨i, -, -, hval⟩ := someProvisionalValue_of_band htop hcap
    exact ⟨i, hval⟩

theorem RespectsSemantics.jump {n : ℕ} {D : SemScheme n} {v : Cell D.scheme → ExtOrd}
    (h : RespectsSemantics D.rows v) {β : Ordinal.{0}} (hβ : Order.IsSuccLimit β) (K : ℕ)
    (hgr : ∀ d : Cell D.scheme, D.scheme.grade d ≤ K) :
    RespectsSemantics D.rows (fun d => ExtOrd.jump (ofOrd (β + K)) (v d)) where
  orderly d := by
    change ExtOrd.jump (ofOrd (β + K)) (v d) =
      extVisibilityReplace (ExtOrd.jump (ofOrd (β + K)) (v d)) (D.scheme.grade d) (D.scheme.grade d)
    by_cases hle : v d ≤ ofOrd (β + K)
    · rw [jump_of_le hle]; exact h.orderly d
    · rw [jump_of_not_le hle, extVisibilityReplace_top]
  locality Sig := by
    have h1 := TransformsTo.comp_jump (h.locality Sig) hβ K K le_rfl (fun d => hgr d.1)
      (fun d hd => absurd (hgr d.1) (not_le.mpr hd))
    have h2 : (fun d : D.scheme.below (D.scheme.cell Sig) =>
        ExtOrd.jump (ofOrd (β + K)) (min (v d.1) (v Sig))) =
        fun d => min (ExtOrd.jump (ofOrd (β + K)) (v d.1))
          (ExtOrd.jump (ofOrd (β + K)) (v Sig)) := funext fun _ => jump_min _ _ _
    rwa [h2] at h1
  availability Sig Xi₀ hsub hgrade := by
    obtain ⟨Xi, hcell, hle⟩ := h.availability Sig Xi₀ hsub hgrade
    exact ⟨Xi, hcell, jump_mono _ hle⟩

def bandJump {J : Type*} (K : ℕ) (u : J → ℕ∞) : J → ℕ∞ :=
  fun j => if u j ≤ K then u j else ⊤

private theorem predicate_iSup_of_jump {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    {J : Type*} [Finite J] (f : J → I → ℕ) (hf : ∀ j, Monotone (f j)) (K0 : ℕ)
    (P : (J → ℕ∞) → Prop) (hjump : ∀ K, K0 ≤ K → ∀ z, P z → P (bandJump K z))
    (hfinite : ∀ i, P fun j => (f j i : ℕ∞)) : P fun j => ⨆ i, (f j i : ℕ∞) := by
  classical
  let _ := Fintype.ofFinite J
  let r : J → ℕ∞ := fun j => ⨆ a, (f j a : ℕ∞)
  let K : ℕ := max K0 (Finset.univ.sup fun j => (r j).toNat)
  have hev (j : J) : ∀ᶠ i in atTop,
      (r j ≠ ⊤ → (f j i : ℕ∞) = r j) ∧ (r j = ⊤ → (K : ℕ∞) < f j i) := by
    by_cases hr : r j = ⊤
    · obtain ⟨a, ha⟩ := lt_iSup_iff.mp (hr ▸ ENat.natCast_lt_top K)
      filter_upwards [eventually_ge_atTop a] with i hai
      exact ⟨fun h => (h hr).elim, fun _ => ha.trans_le (ENat.natCast_le_natCast.mpr (hf j hai))⟩
    · obtain ⟨a, ha⟩ := ENat.exists_eq_iSup_of_lt_top (lt_top_iff_ne_top.mpr hr)
      filter_upwards [eventually_ge_atTop a] with i hai
      exact ⟨fun _ => le_antisymm (le_iSup (fun a => (f j a : ℕ∞)) i)
        (ha.symm.trans_le (ENat.natCast_le_natCast.mpr (hf j hai))), fun h => (hr h).elim⟩
  obtain ⟨i, _, hi⟩ := DirectedNat.synchronize _ hev (Classical.arbitrary I)
  have heq : bandJump K (fun j => (f j i : ℕ∞)) = fun j => ⨆ a, (f j a : ℕ∞) := by
    funext j
    obtain ⟨h1, h2⟩ := hi i le_rfl j
    by_cases hr : r j = ⊤
    · exact (ite_eq_right (not_le.mpr (h2 hr))).trans hr.symm
    · have hK : r j ≤ K := by
        rw [← ENat.natCast_toNat hr]
        exact ENat.natCast_le_natCast.mpr
          ((Finset.le_sup (f := fun j => (r j).toNat) (Finset.mem_univ j)).trans (le_max_right _ _))
      exact (ite_eq_left ((h1 hr).trans_le hK)).trans (h1 hr)
  rw [← heq]; exact hjump K (le_max_left _ _) _ (hfinite i)

namespace ExtOrd
noncomputable def bandValue (β : Ordinal.{0}) (r : ℕ∞) : ExtOrd :=
  ENat.recTopCoe ⊤ (fun k : ℕ => ofOrd (β + k)) r

@[simp] theorem bandValue_natCast (β : Ordinal.{0}) (k : ℕ) :
    bandValue β k = ofOrd (β + k) := ENat.recTopCoe_natCast _ _ k

@[simp] theorem bandValue_top (β : Ordinal.{0}) : bandValue β ⊤ = ⊤ := ENat.recTopCoe_top _ _
end ExtOrd

namespace StageType
variable {β : Ordinal.{0}} {n : ℕ}
abbrev TopCell (p : S β n) := {Xi : Cell p.scheme.scheme // p.label Xi = ⊤}

noncomputable def bandLabel (p : S β n) (r : p.TopCell → ℕ∞) (Xi : Cell p.scheme.scheme) : ExtOrd :=
  if h : p.label Xi = ⊤ then bandValue β (r ⟨Xi, h⟩) else p.label Xi

theorem bandLabel_jump (p : S β n) (K : ℕ) (r : p.TopCell → ℕ∞) :
    p.bandLabel (bandJump K r) = fun Xi => ExtOrd.jump (ofOrd (β + K)) (p.bandLabel r Xi) := by
  funext Xi; unfold bandLabel
  by_cases h : p.label Xi = ⊤
  · rw [dite_eq_left h, dite_eq_left h]
    change bandValue β (if r ⟨Xi, h⟩ ≤ K then r ⟨Xi, h⟩ else ⊤) = _
    induction r ⟨Xi, h⟩ using ENat.recTopCoe with
    | top => simp [ExtOrd.jump]
    | coe k =>
      by_cases hk : k ≤ K
      · rw [ite_eq_left (Nat.cast_le.mpr hk), bandValue_natCast,
          jump_of_le (ofOrd_le_ofOrd.mpr ((add_le_add_iff_left β).mpr (Nat.cast_le.mpr hk)))]
      · rw [ite_eq_right (fun h' => hk (Nat.cast_le.mp h')), bandValue_top, bandValue_natCast,
          jump_of_not_le fun h' =>
            hk (Nat.cast_le.mp (le_of_add_le_add_left (ofOrd_le_ofOrd.mp h')))]
  · rw [dite_eq_right h, dite_eq_right h, jump_of_le]
    exact (((p.label_bound Xi).resolve_right h).trans_le (ofOrd_le_ofOrd.mpr le_self_add)).le
end StageType

private theorem respects_someProvisionalValue_mapCell {β : Ordinal.{0}} (hβ : Order.IsSuccLimit β)
    {m n : ℕ} {p : S β n} {q : S β m} {f : Fin n ↪ Fin m} (hpq : typeMap f q = some p) :
    RespectsSemantics p.scheme.rows (fun Xi => q.someProvisionalValue (mapCell hpq Xi)) := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some hpq, restrictFace_eq_of_typeMap_eq_some hpq⟩
  exact (provisionalLift_respects q hβ).restrictFace f hr

namespace KnightRealization
variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

noncomputable def stableValue (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M)
    (p : S α.1 n) (Xi : Cell p.scheme.scheme) : ExtOrd :=
  Classical.choose (exists_hasStableValue (R := R) t p Xi)

theorem hasStableValue_stableValue (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M)
    (p : S α.1 n) (Xi : Cell p.scheme.scheme) :
    R.HasStableValue t p Xi (R.stableValue t p Xi) :=
  Classical.choose_spec (exists_hasStableValue (R := R) t p Xi)

theorem stableValue_of_stabilizesTo (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} {γ : ExtOrd}
    (hγ : γ < ofOrd (α.1 + Ordinal.omega0)) (h : R.StabilizesTo t p Xi γ) :
    R.stableValue t p Xi = γ :=
  HasStableValue.unique hcons hcov hpt (R.hasStableValue_stableValue t p Xi) (Or.inl ⟨hγ, h⟩)

theorem stableValue_of_ne_top (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} (hne : p.label Xi ≠ ⊤) :
    R.stableValue t p Xi = p.label Xi :=
  stableValue_of_stabilizesTo hcons hcov hpt
    (((p.label_bound Xi).resolve_right hne).trans
      (ofOrd_lt_ofOrd.mpr (lt_add_of_pos_right _ Ordinal.omega0_pos)))
    (stabilizesTo_label_of_ne_top ⟨n, t, p, hpt⟩ hne hcons hcov)

theorem le_stableValue_of_top {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (_hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} (htop : p.label Xi = ⊤) :
    ofOrd α.1 ≤ R.stableValue t p Xi := by
  rcases R.hasStableValue_stableValue t p Xi with ⟨-, hs⟩ | ⟨heq, -⟩
  · obtain ⟨_, _, _, _, q, hpq, _, _, _, hval⟩ := hs t
    exact (le_someProvisionalValue_of_top ((label_mapCell hpq Xi).trans htop)).trans_eq
      (isProvisionalValue_iff.mp hval).symm
  · rw [heq]; exact le_top

theorem stabilizesTo_mapCell_iff' (hcons : R.IsExactParentConsistent) {n m : ℕ}
    {t : Fin n ↪ M} {p : S α.1 n} {u : Fin m ↪ M} {q : S α.1 m} (hqu : R.eval u = some q)
    {f : Fin n ↪ Fin m} (hfu : f.trans u = t) (hpq : typeMap f q = some p)
    (Xi : Cell p.scheme.scheme) (γ : ExtOrd) :
    R.StabilizesTo u q (mapCell hpq Xi) γ ↔ R.StabilizesTo t p Xi γ := by
  refine ⟨fun hs k s => ?_, fun hs k s => ?_⟩
  · obtain ⟨l, z, g, e, r, hqr, hz, hgz, hez, hv⟩ := hs s
    have hpr : typeMap (f.trans e) r = some p := by rw [← typeMap_trans f e r q hqr]; exact hpq
    exact ⟨l, z, g, f.trans e, r, hpr, hz, hgz, by rw [Function.Embedding.trans_assoc, hez, hfu],
      by rw [mapCell_trans hqr hpq hpr Xi]; exact hv⟩
  · obtain ⟨l, w, a, hwu, hws⟩ := exists_common_tuple u s
    obtain ⟨j, z, g, e, r, hpr, hz, hgz, hez, hv⟩ := hs w
    set b : Fin m ↪ Fin j := (Fin.castAddEmb l).trans g with hb
    have hbz : b.trans z = u := by rw [hb, Function.Embedding.trans_assoc, hgz, hwu]
    have hqr : typeMap b r = some q := by
      have h := hcons z r b hz; rw [hbz, hqu] at h; exact h.symm
    have hfbz : (f.trans b).trans z = t := by rw [Function.Embedding.trans_assoc, hbz, hfu]
    obtain rfl : e = f.trans b := Function.Embedding.ext fun i => z.injective
      ((DFunLike.congr_fun hez i).trans (DFunLike.congr_fun hfbz i).symm)
    rw [mapCell_trans hqr hpq hpr Xi] at hv
    exact ⟨j, z, a.trans g, b, r, hqr, hz, by rw [Function.Embedding.trans_assoc, hgz, hws], hbz, hv⟩

theorem stableValue_mapCell' (hcons : R.IsExactParentConsistent) {n m : ℕ}
    {t : Fin n ↪ M} {p : S α.1 n} {u : Fin m ↪ M} {q : S α.1 m} (hqu : R.eval u = some q)
    {f : Fin n ↪ Fin m} (hfu : f.trans u = t) (hpq : typeMap f q = some p)
    (Xi : Cell p.scheme.scheme) :
    R.stableValue u q (mapCell hpq Xi) = R.stableValue t p Xi := by
  have h := fun δ => stabilizesTo_mapCell_iff' hcons hqu hfu hpq Xi δ
  have hiff : R.HasStableValue u q (mapCell hpq Xi) (R.stableValue t p Xi) ↔
      R.HasStableValue t p Xi (R.stableValue t p Xi) :=
    or_congr (and_congr_right fun _ => h _)
      (and_congr_right fun _ => forall_congr' fun δ => imp_congr_right fun _ => not_congr (h δ))
  exact HasStableValue.unique_of_consistent hcons (R.hasStableValue_stableValue u q _)
    (hiff.mpr (R.hasStableValue_stableValue t p Xi))

set_option linter.unusedVariables false in
theorem stableValue_mapCell (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n m : ℕ} {t : Fin n ↪ M} {p : S α.1 n} {u : Fin m ↪ M}
    {q : S α.1 m} (hpt : R.eval t = some p) (hqu : R.eval u = some q) {f : Fin n ↪ Fin m}
    (hfu : f.trans u = t) (hpq : typeMap f q = some p) (Xi : Cell p.scheme.scheme) :
    R.stableValue u q (mapCell hpq Xi) = R.stableValue t p Xi :=
  stableValue_mapCell' hcons hqu hfu hpq Xi

abbrev RootedCover (x : R.LabelledExt) := {y : R.LabelledExt // x ≤ y}

namespace RootedCover
variable {x : R.LabelledExt}

instance : Nonempty (RootedCover x) := ⟨⟨x, le_rfl⟩⟩

theorem isDirectedOrder (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering)
    (x : R.LabelledExt) : IsDirectedOrder (RootedCover x) :=
  ⟨fun y z => let ⟨w, hyw, hzw⟩ := directed_labelledExt hcons hcov y.1 z.1;
    ⟨⟨w, y.2.trans hyw⟩, hyw, hzw⟩⟩

noncomputable def emb (y : RootedCover x) : Fin x.arity ↪ Fin y.1.arity := y.2.choose
theorem emb_trans (y : RootedCover x) : (emb y).trans y.1.tuple = x.tuple := y.2.choose_spec.1
theorem emb_typeMap (y : RootedCover x) : typeMap (emb y) y.1.type = some x.type := y.2.choose_spec.2

noncomputable def cell (y : RootedCover x) (Xi : Cell x.type.scheme.scheme) :
    Cell y.1.type.scheme.scheme := mapCell (emb_typeMap y) Xi

theorem cell_eq (y : RootedCover x) {f : Fin x.arity ↪ Fin y.1.arity}
    (hf : typeMap f y.1.type = some x.type) (hft : f.trans y.1.tuple = x.tuple)
    (Xi : Cell x.type.scheme.scheme) : cell y Xi = mapCell hf Xi := by
  have h : ∀ (g : Fin x.arity ↪ Fin y.1.arity) (hg : typeMap g y.1.type = some x.type),
      g = f → mapCell hg Xi = mapCell hf Xi := by rintro _ _ rfl; rfl
  exact h (emb y) (emb_typeMap y) (LabelledExt.emb_unique (emb_trans y) hft)

theorem label_cell (y : RootedCover x) (Xi : Cell x.type.scheme.scheme) :
    y.1.type.label (cell y Xi) = x.type.label Xi := label_mapCell (emb_typeMap y) Xi

noncomputable def value (y : RootedCover x) (Xi : Cell x.type.scheme.scheme) : ExtOrd :=
  y.1.type.someProvisionalValue (cell y Xi)

theorem value_mono (Xi : Cell x.type.scheme.scheme) :
    Monotone fun y : RootedCover x => value y Xi := fun y z h => by
  obtain ⟨g, hgt, hg⟩ := (h : y.1 ≤ z.1)
  have hpz : typeMap ((emb y).trans g) z.1.type = some x.type := by
    rw [← typeMap_trans (emb y) g z.1.type y.1.type hg]; exact emb_typeMap y
  have hcz : cell z Xi = mapCell hg (cell y Xi) :=
    (cell_eq z hpz (by rw [Function.Embedding.trans_assoc, hgt, emb_trans]) Xi).trans
      (mapCell_trans hg (emb_typeMap y) hpz Xi)
  change y.1.type.someProvisionalValue (cell y Xi) ≤ z.1.type.someProvisionalValue (cell z Xi)
  rw [hcz]; exact provisional_le_mapCell_of_least α.2 hg (cell y Xi)

section Top
variable (Xi : Cell x.type.scheme.scheme) (htop : x.type.label Xi = ⊤)

include htop in
theorem exists_offset (y : RootedCover x) : ∃ j : ℕ, value y Xi = ofOrd (α.1 + j) :=
  someProvisionalValue_top_form ((label_cell y Xi).trans htop)

noncomputable def offset (y : RootedCover x) : ℕ := (exists_offset Xi htop y).choose

theorem value_eq_offset (y : RootedCover x) :
    value y Xi = ofOrd (α.1 + offset Xi htop y) := (exists_offset Xi htop y).choose_spec

theorem offset_le_of_value_le {y : RootedCover x} {K : ℕ}
    (h : value y Xi ≤ ofOrd (α.1 + K)) : offset Xi htop y ≤ K := by
  rw [value_eq_offset Xi htop y, ofOrd_le_ofOrd] at h
  exact Nat.cast_le.mp (le_of_add_le_add_left h)

theorem offset_mono : Monotone (offset Xi htop) := fun y z h => by
  have := value_mono Xi h; change value y Xi ≤ value z Xi at this
  rw [value_eq_offset Xi htop y, value_eq_offset Xi htop z, ofOrd_le_ofOrd] at this
  exact Nat.cast_le.mp (le_of_add_le_add_left this)

variable (hcons : R.IsExactParentConsistent) (hcov : R.IsInitialSegmentCovering)
include hcons hcov

theorem stabilizesTo_of_eventually {k : ℕ} (h : ∀ᶠ y in atTop, offset Xi htop y = k) :
    R.StabilizesTo x.tuple x.type Xi (ofOrd (α.1 + k)) := by
  have := isDirectedOrder hcons hcov x
  rw [stabilizesTo_iff_isDominating hcons hcov x Xi]
  intro a
  obtain ⟨i, hi⟩ := eventually_atTop.mp h
  obtain ⟨w, haw, hiw⟩ := directed_labelledExt hcons hcov a i.1
  let w' : RootedCover x := ⟨w, i.2.trans hiw⟩
  have hw : value w' Xi = ofOrd (α.1 + k) := by rw [value_eq_offset Xi htop w', hi w' hiw]
  exact ⟨w, hw ▸ ⟨emb w', emb_trans w', emb_typeMap w', isProvisionalValue_someProvisionalValue _ _⟩, haw⟩

theorem exists_stabilizesTo_of_bddAbove (hb : BddAbove (Set.range (offset Xi htop))) :
    ∃ i : RootedCover x, R.StabilizesTo x.tuple x.type Xi (ofOrd (α.1 + offset Xi htop i)) := by
  have := isDirectedOrder hcons hcov x
  obtain ⟨i, hi⟩ := DirectedNat.eventually_eq_of_bddAbove (offset_mono Xi htop) hb
  exact ⟨i, stabilizesTo_of_eventually Xi htop hcons hcov hi⟩

theorem stableValue_dichotomy :
    (∃ k : ℕ, (∀ᶠ y in atTop, offset Xi htop y = k) ∧
      R.stableValue x.tuple x.type Xi = ofOrd (α.1 + k)) ∨
    (Tendsto (offset Xi htop) atTop atTop ∧ R.stableValue x.tuple x.type Xi = ⊤) := by
  have := isDirectedOrder hcons hcov x
  rcases DirectedNat.eventually_constant_or_tendsto (offset_mono Xi htop) with ⟨k, hk⟩ | ht
  · exact Or.inl ⟨k, hk, stableValue_of_stabilizesTo hcons hcov x.eval_eq
      (ofOrd_lt_ofOrd.mpr ((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 k)))
      (stabilizesTo_of_eventually Xi htop hcons hcov hk)⟩
  · refine Or.inr ⟨ht, ?_⟩
    rcases R.hasStableValue_stableValue x.tuple x.type Xi with ⟨-, hs⟩ | ⟨heq, -⟩
    · obtain ⟨m, u, _, f, q, hpq, hu, -, hfu, hval⟩ := hs x.tuple
      let y : RootedCover x := ⟨⟨m, u, q, hu⟩, f, hfu, hpq⟩
      have hδ : R.stableValue x.tuple x.type Xi = ofOrd (α.1 + offset Xi htop y) := by
        rw [← value_eq_offset Xi htop y, isProvisionalValue_iff.mp hval]
        exact congrArg _ (cell_eq y hpq hfu Xi).symm
      obtain ⟨i, hi⟩ := tendsto_atTop_atTop.mp ht (offset Xi htop y + 1)
      obtain ⟨m', u', g', f', q', hpq', hu', hgu', hfu', hval'⟩ := hs i.1.tuple
      let z : RootedCover x := ⟨⟨m', u', q', hu'⟩, f', hfu', hpq'⟩
      have hiz : i ≤ z := ⟨g', hgu', by
        have hc := hcons u' q' g' hu'; rw [hgu', i.1.eval_eq] at hc; exact hc.symm⟩
      have hz : value z Xi = ofOrd (α.1 + offset Xi htop y) := by
        rw [← hδ, isProvisionalValue_iff.mp hval']; exact congrArg _ (cell_eq z hpq' hfu' Xi)
      have heq0 := Nat.cast_injective (add_left_cancel (ofOrd_inj.mp ((value_eq_offset Xi htop z).symm.trans hz)))
      have := hi z hiz; omega
    · exact heq
end Top

theorem eventually_syncValues (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x : R.LabelledExt) (K : ℕ) :
    ∀ᶠ y : RootedCover x in atTop, ∀ Xi : Cell x.type.scheme.scheme,
      (R.stableValue x.tuple x.type Xi ≠ ⊤ → value y Xi = R.stableValue x.tuple x.type Xi) ∧
      (x.type.label Xi = ⊤ → R.stableValue x.tuple x.type Xi = ⊤ → ofOrd (α.1 + K) < value y Xi) := by
  have := isDirectedOrder hcons hcov x
  refine eventually_all.mpr fun Xi => ?_
  by_cases htop : x.type.label Xi = ⊤
  · rcases stableValue_dichotomy Xi htop hcons hcov with ⟨k, hk, hval⟩ | ⟨ht, hsv⟩
    · exact hk.mono fun y hy => ⟨fun _ => by rw [value_eq_offset Xi htop y, hy, hval],
        fun _ hsv => absurd (hval.symm.trans hsv) (ofOrd_ne_top _)⟩
    · exact (ht.eventually (eventually_gt_atTop K)).mono fun y hy =>
        ⟨fun hne => absurd hsv hne, fun _ _ => by
          rw [value_eq_offset Xi htop y, ofOrd_lt_ofOrd]
          exact (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr hy)⟩
  · refine Eventually.of_forall fun y => ⟨fun _ => ?_, fun h => absurd h htop⟩
    rw [stableValue_of_ne_top hcons hcov x.eval_eq htop]
    change y.1.type.someProvisionalValue (cell y Xi) = x.type.label Xi
    rw [someProvisionalValue_of_ne_top (by rw [label_cell]; exact htop), label_cell]
end RootedCover

theorem exists_syncCover' (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) (K : ℕ) :
    ∃ (y : R.LabelledExt) (f : Fin n ↪ Fin y.arity) (_ : f.trans y.tuple = t)
      (hpq : typeMap f y.type = some p),
      ∀ Xi : Cell p.scheme.scheme,
        (R.stableValue t p Xi ≠ ⊤ →
          y.type.someProvisionalValue (mapCell hpq Xi) = R.stableValue t p Xi) ∧
        (p.label Xi = ⊤ → R.stableValue t p Xi = ⊤ →
          ofOrd (α.1 + K) < y.type.someProvisionalValue (mapCell hpq Xi)) := by
  let x : R.LabelledExt := ⟨n, t, p, hpt⟩
  have := RootedCover.isDirectedOrder hcons hcov x
  obtain ⟨y, hy⟩ := (RootedCover.eventually_syncValues hcons hcov x K).exists
  exact ⟨y.1, RootedCover.emb y, RootedCover.emb_trans y, RootedCover.emb_typeMap y, hy⟩

private theorem stableLiftRespects_ext (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x : R.LabelledExt) :
    RespectsSemantics x.type.scheme.rows (fun Xi => R.stableValue x.tuple x.type Xi) := by
  classical
  have := RootedCover.isDirectedOrder hcons hcov x
  have hsup (Xi : Cell x.type.scheme.scheme) (htop : x.type.label Xi = ⊤) :
      R.stableValue x.tuple x.type Xi =
        bandValue α.1 (⨆ y : RootedCover x, (RootedCover.offset Xi htop y : ℕ∞)) := by
    rcases RootedCover.stableValue_dichotomy Xi htop hcons hcov with ⟨k, hk, hval⟩ | ⟨ht, hsv⟩
    · obtain ⟨i, hi⟩ := eventually_atTop.mp hk
      have hs : (⨆ y : RootedCover x, (RootedCover.offset Xi htop y : ℕ∞)) = k := by
        refine le_antisymm (iSup_le fun y => ?_)
          ((hi i le_rfl).symm ▸ le_iSup (fun y : RootedCover x => (RootedCover.offset Xi htop y : ℕ∞)) i)
        obtain ⟨z, hyz, hiz⟩ := exists_ge_ge y i
        exact_mod_cast (RootedCover.offset_mono Xi htop hyz).trans (hi z hiz).le
      rw [hs, bandValue_natCast, hval]
    · have hs : (⨆ y : RootedCover x, (RootedCover.offset Xi htop y : ℕ∞)) = ⊤ := by
        refine ENat.eq_top_iff_forall_ge.mpr fun k => ?_
        obtain ⟨y, hy⟩ := (ht.eventually (eventually_ge_atTop k)).exists
        exact (Nat.cast_le.mpr hy).trans
          (le_iSup (fun y : RootedCover x => (RootedCover.offset Xi htop y : ℕ∞)) y)
      rw [hs, bandValue_top, hsv]
  have hlaw : RespectsSemantics x.type.scheme.rows
      (x.type.bandLabel fun d : x.type.TopCell =>
        ⨆ y : RootedCover x, (RootedCover.offset d.1 d.2 y : ℕ∞)) :=
    predicate_iSup_of_jump (fun d : x.type.TopCell => RootedCover.offset d.1 d.2)
      (fun d => RootedCover.offset_mono d.1 d.2)
      (Finset.univ.sup fun d => x.type.scheme.scheme.grade d)
      (fun r => RespectsSemantics x.type.scheme.rows (x.type.bandLabel r))
      (fun K hK r hr => by
        rw [x.type.bandLabel_jump]
        exact RespectsSemantics.jump hr α.2 K fun d =>
          (Finset.le_sup (f := fun d => x.type.scheme.scheme.grade d) (Finset.mem_univ d)).trans hK)
      (fun y => by
        have heq : x.type.bandLabel (fun d : x.type.TopCell => (RootedCover.offset d.1 d.2 y : ℕ∞)) =
            fun Xi => RootedCover.value y Xi := by
          funext Xi; unfold StageType.bandLabel
          by_cases h : x.type.label Xi = ⊤
          · rw [dite_eq_left h, RootedCover.value_eq_offset Xi h y, bandValue_natCast]
          · rw [dite_eq_right h]
            change x.type.label Xi = y.1.type.someProvisionalValue (RootedCover.cell y Xi)
            rw [someProvisionalValue_of_ne_top (by rw [RootedCover.label_cell]; exact h),
              RootedCover.label_cell]
        rw [heq]
        exact respects_someProvisionalValue_mapCell α.2 (RootedCover.emb_typeMap y))
  have hst : x.type.bandLabel (fun d : x.type.TopCell =>
      ⨆ y : RootedCover x, (RootedCover.offset d.1 d.2 y : ℕ∞)) =
      fun Xi => R.stableValue x.tuple x.type Xi := by
    funext Xi; unfold StageType.bandLabel
    by_cases h : x.type.label Xi = ⊤
    · rw [dite_eq_left h, hsup Xi h]
    · rw [dite_eq_right h, stableValue_of_ne_top hcons hcov x.eval_eq h]
  rwa [hst] at hlaw

theorem stableLiftRespects_of_consistent (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) :
    RespectsSemantics p.scheme.rows (fun Xi => R.stableValue t p Xi) :=
  stableLiftRespects_ext hcons hcov ⟨n, t, p, hpt⟩

theorem stableLiftRespects (hR : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) :
    RespectsSemantics p.scheme.rows (fun Xi => R.stableValue t p Xi) :=
  stableLiftRespects_of_consistent hR.consistent hR.covering hpt

theorem truncExt_stableValue (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) (Xi : Cell p.scheme.scheme) :
    truncExt α.1 (R.stableValue t p Xi) = p.label Xi := by
  by_cases htop : p.label Xi = ⊤
  · rw [truncExt_eq_top_of_ge (le_stableValue_of_top hpt htop), htop]
  · rw [stableValue_of_ne_top hcons hcov hpt htop]
    exact truncExt_id_of_lt ((p.label_bound Xi).resolve_right htop)

noncomputable def stableLiftType (hR : R.IsModel) {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (hpt : R.eval t = some p) : S (α.1 + Ordinal.omega0) n where
  scheme := p.scheme
  label Xi := R.stableValue t p Xi
  label_bound Xi := (R.hasStableValue_stableValue t p Xi).imp And.left And.left
  respects := stableLiftRespects hR hpt

noncomputable def stableLift (hR : R.IsModel) : KnightRealization α.nextBlock M where
  eval {_n} t :=
    match h : R.eval t with
    | none => none
    | some p => some (stableLiftType hR t p h)

theorem stableLift_eval_none (hR : R.IsModel) {n : ℕ} {t : Fin n ↪ M}
    (h : R.eval t = none) : (stableLift hR).eval t = none := by
  change (match h' : R.eval t with | none => none | some p => some (stableLiftType hR t p h')) = none
  split
  · rfl
  · next _ h' => rw [h] at h'; cases h'

theorem stableLift_eval_some (hR : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (h : R.eval t = some p) :
    (stableLift hR).eval t = some (stableLiftType hR t p h) := by
  change (match h' : R.eval t with | none => none | some p => some (stableLiftType hR t p h')) = _
  split
  · next h' => rw [h] at h'; cases h'
  · next p' h' => obtain rfl : p' = p := Option.some_injective _ (h'.symm.trans h); rfl

theorem stableLift_eval_eq_some (hR : R.IsModel) {n : ℕ} {t : Fin n ↪ M}
    {q : S α.nextBlock.1 n} (h : (stableLift hR).eval t = some q) :
    ∃ (p : S α.1 n) (hp : R.eval t = some p), q = stableLiftType hR t p hp := by
  by_cases hs : (R.eval t).isSome
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
    rw [stableLift_eval_some hR hp] at h
    exact ⟨p, hp, (Option.some_injective _ h).symm⟩
  · rw [stableLift_eval_none hR (Option.not_isSome_iff_eq_none.mp hs)] at h; cases h

theorem stableLift_reduct (hR : R.IsModel) : (stableLift hR).reduct α.le_nextBlock = R := by
  apply Realization.ext; intro n t; rw [Realization.reduct_eval]
  by_cases hs : (R.eval t).isSome
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
    rw [stableLift_eval_some hR hp, hp]
    exact congrArg some (StageType.ext rfl
      (heq_of_eq (funext (truncExt_stableValue hR.consistent hR.covering hp))))
  · have hn := Option.not_isSome_iff_eq_none.mp hs
    rw [stableLift_eval_none hR hn, hn]; rfl

theorem stableLift_consistent (hR : R.IsModel) : (stableLift hR).IsExactParentConsistent := by
  intro m n t q' f hq'
  obtain ⟨p, hp, rfl⟩ := stableLift_eval_eq_some hR hq'
  have hRf := hR.consistent t p f hp
  change (stableLift hR).eval (f.trans t) = typeMap f (stableLiftType hR t p hp)
  by_cases hr : Finset.univ.image f ∈ p.scheme.scheme.plan
  · have hRf' : R.eval (f.trans t) = some (p.restrictFace f hr) := hRf.trans (typeMap_eq_some f p hr)
    rw [stableLift_eval_some hR hRf', typeMap_eq_some f (stableLiftType hR t p hp) hr]
    refine congrArg some (StageType.ext rfl (heq_of_eq (funext fun Xi => ?_)))
    exact (stableValue_mapCell hR.consistent hR.covering hRf' hp rfl (typeMap_eq_some f p hr) Xi).symm
  · have h3 : typeMap f p = none := by
      by_contra hne
      obtain ⟨q'', hq''⟩ := Option.ne_none_iff_exists'.mp hne
      exact hr ((typeMap_isSome_iff f p).mp (by rw [hq'']; rfl))
    have h4 : typeMap f (stableLiftType hR t p hp) = none := by
      by_contra hne
      obtain ⟨q'', hq''⟩ := Option.ne_none_iff_exists'.mp hne
      exact hr ((typeMap_isSome_iff f (stableLiftType hR t p hp)).mp (by rw [hq'']; rfl))
    rw [stableLift_eval_none hR (hRf.trans h3), h4]; rfl

theorem stableLift_covering (hR : R.IsModel) : (stableLift hR).IsInitialSegmentCovering := by
  intro n t
  obtain ⟨k, s, hs, hsome⟩ := hR.covering t
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨k, s, hs, by rw [stableLift_eval_some hR hp]; rfl⟩
end KnightRealization

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

theorem limitPart_stage : limitPart α.1 = α.1 :=
  limitPart_eq_self_of_isNonSuccessor (Or.inr α.2)

theorem stable_ge_of_top (hM : R.IsModel) {m : ℕ} {u : Fin m ↪ M} {q : S α.1 m}
    (hu : R.eval u = some q) {Θ : Cell q.scheme.scheme} (hΘ : q.label Θ = ⊤) :
    ofOrd (α.1 + q.scheme.scheme.grade Θ) ≤ R.stableValue u q Θ := by
  have hα := le_stableValue_of_top (R := R) hu hΘ
  have hvis : SelfVis (q.scheme.scheme.grade Θ) (R.stableValue u q Θ) :=
    ((stableLiftRespects hM hu).orderly Θ).symm
  rcases ExtOrd.cases (R.stableValue u q Θ) with hb | ht | ⟨γ, hγ⟩
  · rw [hb] at hα; exact absurd hα (not_ofOrd_le_bot _)
  · rw [ht]; exact le_top
  · rw [hγ] at hα hvis ⊢; rw [selfVis_ofOrd_iff] at hvis
    have h1 : α.1 ≤ limitPart γ := by
      have := limitPart_mono (ofOrd_le_ofOrd.mp hα); rwa [limitPart_stage] at this
    exact ofOrd_le_ofOrd.mpr ((add_le_add_left h1 _).trans
      ((add_le_add_right (Nat.cast_le.mpr hvis) _).trans_eq (limitPart_add_finitePart γ)))

private theorem source_pinned {τ : ExtOrd → ExtOrd} (hbot : τ ⊥ = ⊥) {N j : ℕ} (hjN : j < N)
    (hcomm : ∀ x k i, k ≤ N → i ≤ k →
      τ (extVisibilityReplace x k i) = extVisibilityReplace (τ x) k i)
    {α : Ordinal.{0}} (hα : limitPart α = α) {x : ExtOrd} (hτx : τ x = ofOrd (α + j)) :
    ∃ ξ : Ordinal.{0}, limitPart ξ = ξ ∧ x = ofOrd (ξ + j) ∧ τ (ofOrd ξ) = ofOrd α := by
  have hevr (k : ℕ) (_ : k ≤ N) : extVisibilityReplace (ofOrd (α + j)) N k = ofOrd (α + k) := by
    rw [extVisibilityReplace_of_finitePart_lt (by
      rw [finitePart_limitPart_add_nat' hα]; exact hjN), limitPart_add_nat_of_limitPart_eq hα]
  rcases ExtOrd.cases x with rfl | rfl | ⟨ξ', rfl⟩
  · rw [hbot] at hτx; exact absurd hτx.symm (ofOrd_ne_bot _)
  · have h := hcomm ⊤ N N le_rfl le_rfl
    rw [extVisibilityReplace_top, hτx, hevr N le_rfl, ofOrd_inj] at h
    exact (hjN.ne (Nat.cast_injective (add_left_cancel h))).elim
  · by_cases hfp : N ≤ finitePart ξ'
    · have h := hcomm (ofOrd ξ') N N le_rfl le_rfl
      rw [extVisibilityReplace_of_le_finitePart hfp, hτx, hevr N le_rfl, ofOrd_inj] at h
      exact (hjN.ne (Nat.cast_injective (add_left_cancel h))).elim
    · have hfp' := not_le.mp hfp
      have hk (k : ℕ) (hk : k ≤ N) : τ (ofOrd (limitPart ξ' + k)) = ofOrd (α + k) := by
        have h := hcomm (ofOrd ξ') N k le_rfl hk
        rwa [extVisibilityReplace_of_finitePart_lt hfp', hτx, hevr k hk] at h
      have hj : finitePart ξ' = j := by
        have h := hk (finitePart ξ') hfp'.le
        rw [limitPart_add_finitePart, hτx, ofOrd_inj] at h
        exact (Nat.cast_injective (add_left_cancel h)).symm
      exact ⟨limitPart ξ', limitPart_idem ξ', by rw [← hj, limitPart_add_finitePart], by
        simpa using hk 0 (Nat.zero_le _)⟩

theorem isInfinityAnchor_of_stable (hM : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hpt : R.eval t = some p) {Xi : Cell p.scheme.scheme} (hXi : p.label Xi = ⊤) {j : ℕ}
    (hs : R.stableValue t p Xi = ofOrd (α.1 + j)) : R.IsInfinityAnchor t p Xi (j + 1) := by
  refine ⟨hXi, fun s f q hfs hq hpq Θ hΘgr hΘtop Sig hSig hXi' => ?_⟩
  suffices hlt : q.scheme.rows.E Θ ⟨mapCell hpq Xi, hXi'⟩ <
      extVisibilityReplace (q.scheme.rows.E Θ Sig) (j + 1) (j + 1) from ⟨hlt.le, fun _ => hlt⟩
  have hσr := stableLiftRespects hM hq
  have hσa : R.stableValue s q (mapCell hpq Xi) = ofOrd (α.1 + j) :=
    (stableValue_mapCell hM.consistent hM.covering hpt hq hfs hpq Xi).trans hs
  have hσΘ := stable_ge_of_top hM hq hΘtop
  have hσS := stable_ge_of_top hM hq hSig
  have hαjΘ : ofOrd (α.1 + j) ≤ R.stableValue s q Θ :=
    (ofOrd_lt_ofOrd.mpr (add_lt_add_right (Nat.cast_lt.mpr (show j < _ from hΘgr)) _)).le.trans hσΘ
  obtain ⟨τ, hbot, hmono, hread, hcomm, -⟩ := exists_exact_capped_shifter
    (D := q.scheme.scheme.below (q.scheme.scheme.cell Θ))
    (grade := fun d => q.scheme.scheme.grade d.1) (p := fun d => R.stableValue s q d.1)
    (c := ⟨Θ, GradedLe.refl _⟩) (fun d => d.2.2) (hσr.orderly Θ).symm (hσr.locality Θ)
  have hτa : τ (q.scheme.rows.E Θ ⟨mapCell hpq Xi, hXi'⟩) = ofOrd (α.1 + j) := by
    have h := hread ⟨mapCell hpq Xi, hXi'⟩
    change τ _ = min (R.stableValue s q (mapCell hpq Xi)) (R.stableValue s q Θ) at h
    rwa [hσa, min_eq_left hαjΘ] at h
  have hτS : ofOrd (α.1 + ((1 : ℕ) : Ordinal.{0})) ≤ τ (q.scheme.rows.E Θ Sig) := by
    have h := hread Sig; change τ _ = min _ _ at h; rw [h]
    exact le_min ((ofOrd_le_ofOrd.mpr (add_le_add_right
      (Nat.cast_le.mpr (q.scheme.scheme.grade_pos Sig.1)) _)).trans hσS)
      ((ofOrd_le_ofOrd.mpr (add_le_add_right
        (Nat.cast_le.mpr (q.scheme.scheme.grade_pos Θ)) _)).trans hσΘ)
  obtain ⟨ξ, hξ, hEa, hτξ⟩ := source_pinned hbot hΘgr hcomm limitPart_stage hτa
  have hSξ : ofOrd ξ < q.scheme.rows.E Θ Sig := by
    by_contra hle
    have h1 : ofOrd (α.1 + ((1 : ℕ) : Ordinal.{0})) ≤ ofOrd α.1 :=
      hτS.trans (hτξ ▸ hmono (not_lt.mp hle))
    exact absurd (ofOrd_le_ofOrd.mp h1) (not_le.mpr (lt_add_of_pos_right _ (by norm_num)))
  rw [hEa]
  have hstep : ξ + (j : Ordinal.{0}) < ξ + ((j + 1 : ℕ) : Ordinal.{0}) :=
    add_lt_add_right (Nat.cast_lt.mpr (Nat.lt_succ_self j)) _
  rcases ExtOrd.cases (q.scheme.rows.E Θ Sig) with hb | htop | ⟨η, he⟩
  · rw [hb] at hSξ; exact absurd hSξ not_lt_bot
  · rw [htop, extVisibilityReplace_top]; exact ofOrd_lt_top _
  · rw [he] at hSξ ⊢
    have hl : ξ ≤ limitPart η := hξ ▸ limitPart_mono (ofOrd_lt_ofOrd.mp hSξ).le
    by_cases hfp : j + 1 ≤ finitePart η
    · rw [extVisibilityReplace_of_le_finitePart hfp, ofOrd_lt_ofOrd]
      exact hstep.trans_le ((add_le_add_left hl _).trans
        ((add_le_add_right (Nat.cast_le.mpr hfp) _).trans_eq (limitPart_add_finitePart η)))
    · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp hfp), ofOrd_lt_ofOrd]
      exact hstep.trans_le (add_le_add_left hl _)

theorem stableValue_eq_label_of_hollow (hM : R.IsModel) (hh : R.IsHollow) {n : ℕ}
    {t : Fin n ↪ M} {p : S α.1 n} (hpt : R.eval t = some p) (Xi : Cell p.scheme.scheme) :
    R.stableValue t p Xi = p.label Xi := by
  by_cases htop : p.label Xi = ⊤
  · rcases R.hasStableValue_stableValue t p Xi with ⟨hlt, -⟩ | ⟨heq, -⟩
    · obtain ⟨j, hj⟩ := exists_nat_of_band (le_stableValue_of_top (R := R) hpt htop) hlt
      exact (hh ⟨n, t, p, hpt, Xi, j + 1, isInfinityAnchor_of_stable hM hpt htop hj⟩).elim
    · rw [heq, htop]
  · exact stableValue_of_ne_top hM.consistent hM.covering hpt htop

private theorem evr_self_le_evr_self (x : ExtOrd) {k k' : ℕ} (h : k ≤ k') :
    extVisibilityReplace x k k ≤ extVisibilityReplace x k' k' := by
  rcases ExtOrd.cases x with rfl | rfl | ⟨a, rfl⟩
  · rw [extVisibilityReplace_bot, extVisibilityReplace_bot]
  · rw [extVisibilityReplace_top, extVisibilityReplace_top]
  · by_cases h' : k' ≤ finitePart a
    · rw [extVisibilityReplace_of_le_finitePart h',
        extVisibilityReplace_of_le_finitePart (h.trans h')]
    · have h'' := not_le.mp h'; rw [extVisibilityReplace_of_finitePart_lt h'']
      by_cases hk : k ≤ finitePart a
      · rw [extVisibilityReplace_of_le_finitePart hk, ofOrd_le_ofOrd]
        conv_lhs => rw [← limitPart_add_finitePart a]
        exact add_le_add_right (Nat.cast_le.mpr h''.le) _
      · rw [extVisibilityReplace_of_finitePart_lt (not_le.mp hk), ofOrd_le_ofOrd]
        exact add_le_add_right (Nat.cast_le.mpr h) _

private theorem someProvisionalValue_le_of_anchor {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    {Xi : Cell p.scheme.scheme} {K' : ℕ} (h : R.IsInfinityAnchor t p Xi K') {m : ℕ}
    {s : Fin m ↪ M} {f : Fin n ↪ Fin m} {q : S α.1 m} (hfs : f.trans s = t)
    (hq : R.eval s = some q) (hpq : typeMap f q = some p) :
    q.someProvisionalValue (mapCell hpq Xi) ≤ ofOrd (α.1 + K') := by
  classical
  by_cases hN : K' < q.topGrade
  · set Xi' := mapCell hpq Xi
    have htop' : q.label Xi' = ⊤ := (label_mapCell hpq Xi).trans h.1
    obtain ⟨Θ, hsc, hgr, hΘ⟩ := exists_topCell_of_topGrade_pos q (Nat.zero_le K' |>.trans_lt hN)
    have hXiΘ : GradedLe (q.scheme.scheme.cell Xi') (q.scheme.scheme.cell Θ) := by
      refine ⟨?_, ?_⟩
      · change q.scheme.scheme.scope Xi' ⊆ q.scheme.scheme.scope Θ
        rw [hsc]; exact Finset.subset_univ _
      · change q.scheme.scheme.grade Xi' ≤ q.scheme.scheme.grade Θ
        rw [hgr]; exact le_csSup (topGrades_bddAbove q) (grade_mem_topGrades htop')
    have hstrict := (h.2 s f q hfs hq hpq Θ (hgr ▸ hN.le) hΘ ⟨Xi', hXiΘ⟩ htop' hXiΘ).2 (hgr ▸ hN)
    obtain ⟨a, ha, hfp⟩ : ∃ a : Ordinal.{0}, q.scheme.rows.E Θ ⟨Xi', hXiΘ⟩ = ofOrd a ∧
        finitePart a < K' := by
      rcases ExtOrd.cases (q.scheme.rows.E Θ ⟨Xi', hXiΘ⟩) with hb | ht | ⟨a, ha⟩
      · rw [hb, extVisibilityReplace_bot] at hstrict; exact (lt_irrefl _ hstrict).elim
      · rw [ht, extVisibilityReplace_top] at hstrict; exact (lt_irrefl _ hstrict).elim
      · refine ⟨a, ha, ?_⟩
        by_contra hk
        rw [ha, extVisibilityReplace_of_le_finitePart (not_lt.mp hk)] at hstrict
        exact lt_irrefl _ hstrict
    have hcap : ¬ q.ProvisionalCap Xi' := fun ⟨Θ', hXi'', Sig', _, hgr', hΘ', hSig', hle⟩ =>
      lt_irrefl _ ((((h.2 s f q hfs hq hpq Θ' (hgr' ▸ hN.le) hΘ' Sig' hSig' hXi'').2
        (hgr' ▸ hN)).trans_le (evr_self_le_evr_self _ hN.le)).trans_le hle)
    have hband : q.ProvisionalBand Xi' (finitePart a) :=
      ⟨Θ, hXiΘ, hsc, hgr, hΘ, by
        rw [ha, extVisibilityReplace_of_finitePart_lt (hfp.trans hN), limitPart_add_finitePart]⟩
    have hex : ∃ i, q.ProvisionalBand Xi' i := ⟨_, hband⟩
    unfold someProvisionalValue
    rw [ite_eq_left htop', ite_eq_right hcap, dite_eq_left hex, ofOrd_le_ofOrd]
    exact add_le_add_right (Nat.cast_le.mpr ((Nat.find_le hband).trans hfp.le)) _
  · exact (someProvisionalValue_le q _).trans
      (ofOrd_le_ofOrd.mpr (add_le_add_right (Nat.cast_le.mpr (not_lt.mp hN)) _))

private theorem exists_stabilizesTo_of_bounded (hcons : R.IsExactParentConsistent)
    (hcov : R.IsInitialSegmentCovering) (x : R.LabelledExt) {Xi : Cell x.type.scheme.scheme}
    (htop : x.type.label Xi = ⊤) (K : ℕ)
    (hB : ∀ (y : R.LabelledExt) (f : Fin x.arity ↪ Fin y.arity), f.trans y.tuple = x.tuple →
      ∀ hpq : typeMap f y.type = some x.type,
        y.type.someProvisionalValue (mapCell hpq Xi) ≤ ofOrd (α.1 + K)) :
    ∃ j ≤ K, R.StabilizesTo x.tuple x.type Xi (ofOrd (α.1 + j)) := by
  have hle (y : RootedCover x) : RootedCover.offset Xi htop y ≤ K :=
    RootedCover.offset_le_of_value_le Xi htop
      (hB y.1 (RootedCover.emb y) (RootedCover.emb_trans y) (RootedCover.emb_typeMap y))
  obtain ⟨i, hi⟩ := RootedCover.exists_stabilizesTo_of_bddAbove Xi htop hcons hcov
    ⟨K, by rintro _ ⟨y, rfl⟩; exact hle y⟩
  exact ⟨_, hle i, hi⟩

theorem hasInfinityAnchor_iff_exists_finite_stable (hM : R.IsModel) :
    R.HasInfinityAnchor ↔ ∃ (n : ℕ) (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p ∧
      ∃ (Xi : Cell p.scheme.scheme) (j : ℕ), p.label Xi = ⊤ ∧
        R.stableValue t p Xi = ofOrd (α.1 + j) := by
  refine ⟨?_, fun ⟨n, t, p, hpt, Xi, j, hXi, hs⟩ =>
    ⟨n, t, p, hpt, Xi, j + 1, isInfinityAnchor_of_stable hM hpt hXi hs⟩⟩
  rintro ⟨n, t, p, hpt, Xi, K', h⟩
  obtain ⟨j, -, hs⟩ := exists_stabilizesTo_of_bounded hM.consistent hM.covering
    ⟨n, t, p, hpt⟩ h.1 K' (fun y f hf hpq => someProvisionalValue_le_of_anchor h hf y.eval_eq hpq)
  exact ⟨n, t, p, hpt, Xi, j, h.1, stableValue_of_stabilizesTo hM.consistent hM.covering hpt
    (ofOrd_lt_ofOrd.mpr ((add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 j))) hs⟩

end VaughtConjecture.Knight
