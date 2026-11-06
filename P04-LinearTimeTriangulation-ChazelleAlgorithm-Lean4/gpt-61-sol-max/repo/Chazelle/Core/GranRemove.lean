module

public import Chazelle.Core.GranArcs

/-!
# WP-F, part 2: removing one chord — arcs and weights

Let `S` be a finite admissible family of a model satisfying the walk axioms, `c ∈ S`, and
`S' = S \ {c}`.  Removing `c` merges the two regions `R₁ ≠ R₂` of `S` touched by `c` into the
region `P` of `S'` (the data `Merge.IsSplit M.D S' c P R₁ R₂`).  The keys that stop being cuts are
the **lost keys** (`lostKeys`): attachments of `c` at which no other chord of `S` is attached.

* `lost_attach`, `lost_sides`: at a lost key only `c` is attached, and the arcs of `S` starting
  and ending there belong to `R₁` or `R₂`;
* `arcs_other` (**locality**): a region of `S` other than `R₁`, `R₂` is a region of `S'` with the
  same arcs; hence `weight_other` (the weight is local, `weightLocal`);
* `arcs_merged_ge`: every arc of `R₁` (or `R₂`) lies inside an arc of `P`;
* `arcs_merged_cases`: an arc of `P` is an arc of `R₁` or `R₂`, or contains a lost key;
* `arc_around_lost`: an arc of `S'` containing a lost key is an arc of `P`;
* `weight_merged_le`, `le_weight_merged`: the weight of `P` is the largest of the weights of
  `R₁`, `R₂` and of the arcs of `S'` containing a lost key.
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn)

variable {M : Model}

/-- The keys that are cuts of `S` but not of `S \ {c}`. -/
def lostKeys (M : Model) (S : Set (Set Point)) (c : Set Point) : Set ℝ :=
  {k | M.IsCut S k ∧ ¬ M.IsCut (S \ {c}) k}

/-- A gap of `G`: two distinct cut keys with no cut strictly between them. -/
def Gap (M : Model) (G : Set (Set Point)) (l r : ℝ) : Prop :=
  M.IsCut G l ∧ M.IsCut G r ∧ l ≠ r ∧ ∀ k, sideInArc l r k → ¬ M.IsCut G k

section Split

variable {S : Set (Set Point)} {c P R₁ R₂ : Set Point}

theorem sdiff_sub : S \ {c} ⊆ S := sdiff_subset

theorem not_mem_sdiff_self : c ∉ S \ {c} := fun h => h.2 rfl

section
variable (hc : c ∈ S) (hs : Merge.IsSplit M.D (S \ {c}) c P R₁ R₂)
include hc hs
theorem split_mem₁ :
    R₁ ∈ M.regions S := by
  have := hs.mem₁; aesop

theorem split_mem₂ :
    R₂ ∈ M.regions S := split_mem₁ hc hs.symm

section
variable {X : Set Point}
include X
/-- The regions of `S`: `R₁`, `R₂`, and regions of `S'` other than `P`. -/
theorem split_cases
    (hX : X ∈ M.regions S) : X = R₁ ∨ X = R₂ ∨ (X ∈ M.regions (S \ {c}) ∧ X ≠ P) := by
  have hX' : X ∈ regionsIn M.D (insert c (S \ {c})) := by
    aesop
  rcases hs.mem_cases hX' with h | h | h
  · exact Or.inr (Or.inr h)
  all_goals simp_all

/-- A region of `S'` other than `P` is a region of `S`. -/
theorem split_old
    (hX : X ∈ M.regions (S \ {c})) (hXP : X ≠ P) : X ∈ M.regions S := by
  have := hs.mem_of_ne hX hXP
  aesop



end

end

/-- `c` touches exactly `R₁` and `R₂`. -/
theorem split_touches_iff (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D (S \ {c}) c P R₁ R₂) {X : Set Point} (hX : X ∈ M.regions S) :
    TouchesIn M.D c X ↔ X = R₁ ∨ X = R₂ := by
  have hF := hM.sys S hS hfin
  have hX' : X ∈ regionsIn M.D (insert c (S \ {c})) := by
    aesop
  exact hs.touches_iff hF sdiff_sub hc not_mem_sdiff_self X hX'

section
variable (hc : c ∈ S)
include hc
/-- If `S'` is empty, `S = {c}` and the two regions of `S` are `R₁` and `R₂`. -/
theorem split_sdiff_nonempty (hM : WalkAx M)
    (hs : Merge.IsSplit M.D (S \ {c}) c P R₁ R₂) {X : Set Point} (hX : X ∈ M.regions S)
    (h1 : X ≠ R₁) (h2 : X ≠ R₂) : (S \ {c}).Nonempty := by
  rcases split_cases hc hs hX with h | h | ⟨hX', hXP⟩
  · simp_all
  · simp_all
  · by_contra he
    rw [not_nonempty_iff_eq_empty] at he
    have hD : regionsIn M.D ∅ = {M.D} := Chazelle.Chain.regionsIn_empty hM.preconn hM.nonempty
    have hP : P ∈ regionsIn M.D (S \ {c}) := hs.mem
    have hX'' : X ∈ regionsIn M.D (S \ {c}) := hX'
    simp_all

/-! ## Lost keys -/

/-- **Only `c` is attached at a lost key.** -/
theorem lost_attach {k : ℝ} (hk : k ∈ lostKeys M S c) :
    ∃ p t, SideAttach M.W c p t ∧ k = p + t ∧ ∀ c' ∈ S, SideAttach M.W c' p t → c' = c := by
  obtain ⟨⟨d, hd, p, t, hA, rfl⟩, hno⟩ := hk
  have hdc : d = c := by
    by_contra hne
    exact hno ⟨d, ⟨hd, hne⟩, p, t, hA, rfl⟩
  subst hdc
  refine ⟨p, t, hA, rfl, fun c' hc' hA' => ?_⟩
  by_contra hne
  exact hno ⟨c', ⟨hc', hne⟩, p, t, hA', rfl⟩


end

/-- **The arcs of `S` at a lost key belong to `R₁` or `R₂`.** -/
theorem lost_sides (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D (S \ {c}) c P R₁ R₂) {k : ℝ} (hk : k ∈ lostKeys M S c) :
    ∃ U V l r, U ∈ M.regions S ∧ V ∈ M.regions S ∧ M.IsArc S U k r ∧ M.IsArc S V l k ∧
      (U = R₁ ∨ U = R₂) ∧ (V = R₁ ∨ V = R₂) := by
  obtain ⟨p, t, hA, rfl, hone⟩ := lost_attach hc hk
  obtain ⟨U, V, l, r, hU, hV, -, hUa, hVa, htouch⟩ := hM.attach_face hS hfin hc hA
  obtain ⟨hcU, hcV⟩ := htouch hone
  exact ⟨U, V, l, r, hU, hV, hUa, hVa, (split_touches_iff hM hS hfin hc hs hU).1 hcU,
    (split_touches_iff hM hS hfin hc hs hV).1 hcV⟩

theorem sub_P (hs : Merge.IsSplit M.D (S \ {c}) c P R₁ R₂) {U : Set Point}
    (h : U = R₁ ∨ U = R₂) : U ⊆ P := by
  rcases h with rfl | rfl
  · exact hs.sub₁
  · exact hs.sub₂

section
variable (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S) (hs : Merge.IsSplit M.D (S \ {c}) c P R₁ R₂)
include hM hS hfin hc hs
/-- **Arcs of `S'` around a lost key belong to `P`.** -/
theorem arc_around_lost {k : ℝ} (hk : k ∈ lostKeys M S c)
    {Z : Set Point} (hZ : Z ∈ M.regions (S \ {c})) {l r : ℝ} (h : M.IsArc (S \ {c}) Z l r)
    (hin : sideInArc l r k) : Z = P := by
  obtain ⟨U, -, -, r', hU, -, hUa, -, hU12, -⟩ := lost_sides hM hS hfin hc hs hk
  obtain ⟨p, t, hA, rfl, -⟩ := lost_attach hc hk
  have hne : S.Nonempty := ⟨c, hc⟩
  obtain ⟨-, -, hkr⟩ := WalkAx.arc_cuts hne hUa
  obtain ⟨t', ht', h1, h2⟩ := exists_pos_after_both (p := p) hA.2.1 hA.2.2.1
    (A := sideInArc l r) (B := sideInArc (p + t) r') (eventually_in_of_mem hin)
    (WalkAx.eventually_after_start hkr)
  have fZ := h.2.2.2.2.2.2 p t' hA.1 ht'.1 ht'.2 h1
  have fU := hUa.2.2.2.2.2.2 p t' hA.1 ht'.1 ht'.2 h2
  exact WalkAx.faces_unique hZ hs.mem fZ (faces_mono fU (sub_P hs hU12))

section
variable {X : Set Point} (hX : X ∈ M.regions S) (h1 : X ≠ R₁) (h2 : X ≠ R₂)
include X hX h1 h2
/-- **Locality**: a region of `S` other than `R₁`, `R₂` is a region of `S'` with the same arcs. -/
theorem arcs_other (a b : ℝ) :
    M.IsArc (S \ {c}) X a b ↔ M.IsArc S X a b := by
  have hne : S.Nonempty := ⟨c, hc⟩
  have hne' := split_sdiff_nonempty hc hM hs hX h1 h2
  obtain ⟨hX', hXP⟩ := (split_cases hc hs hX).resolve_left h1 |>.resolve_left h2
  constructor
  · intro h
    obtain ⟨ha, hb, hab⟩ := WalkAx.arc_cuts hne' h
    obtain ⟨ha0, han, hb0, hbn, -, hfree, hfac⟩ := h
    refine ⟨ha0, han, hb0, hbn, Or.inl ⟨Model.isCut_mono M sdiff_sub ha,
      Model.isCut_mono M sdiff_sub hb, hab⟩, fun x hx hcut => ?_, hfac⟩
    have hk : x ∈ lostKeys M S c := ⟨hcut, hfree x hx⟩
    have := arc_around_lost hM hS hfin hc hs hk hX' ⟨ha0, han, hb0, hbn,
      Or.inl ⟨ha, hb, hab⟩, hfree, hfac⟩ hx
    simp_all
  · intro h
    obtain ⟨ha, hb, hab⟩ := WalkAx.arc_cuts hne h
    obtain ⟨ha0, han, hb0, hbn, -, hfree, hfac⟩ := h
    have harc : M.IsArc S X a b := ⟨ha0, han, hb0, hbn, Or.inl ⟨ha, hb, hab⟩, hfree, hfac⟩
    have ha' : M.IsCut (S \ {c}) a := by
      by_contra hna
      obtain ⟨U, -, -, r, hU, -, hUa, -, hU12, -⟩ := lost_sides hM hS hfin hc hs ⟨ha, hna⟩
      have := (arc_start_unique hne hX hU harc hUa).2
      grind
    have hb' : M.IsCut (S \ {c}) b := by
      by_contra hnb
      obtain ⟨-, V, l, -, -, hV, -, hVa, -, hV12⟩ := lost_sides hM hS hfin hc hs ⟨hb, hnb⟩
      have := (arc_end_unique hne hX hV harc hVa).2
      grind
    exact ⟨ha0, han, hb0, hbn, Or.inl ⟨ha', hb', hab⟩,
      fun x hx hcut => hfree x hx (Model.isCut_mono M sdiff_sub hcut), hfac⟩

/-- **The weight is local**: removing `c` does not change the weight of the regions it does not
touch. -/
theorem weight_other : M.weight (S \ {c}) X = M.weight S X := by
  rw [weight_eq, weight_eq]
  congr 1
  unfold arcWts
  congr 1
  ext ab
  exact arcs_other hM hS hfin hc hs hX h1 h2 ab.1 ab.2


end

/-- **An arc of `R₁` lies inside an arc of `P`** (or `S'` is empty and `P` has the pinned arc,
which weighs the most). -/
theorem arcs_merged_ge {a b : ℝ} (h : M.IsArc S R₁ a b) :
    ∃ a' b', M.IsArc (S \ {c}) P a' b' ∧ M.arcWt a b ≤ M.arcWt a' b' := by
  have hne : S.Nonempty := ⟨c, hc⟩
  have hS' : S \ {c} ⊆ M.Adm := sdiff_sub.trans hS
  have hfin' : (S \ {c}).Finite := hfin.subset sdiff_sub
  rcases (S \ {c}).eq_empty_or_nonempty with he | hne'
  · refine ⟨0, 0, ?_, arcWt_le_zero_zero a b⟩
    have hP := hs.mem
    rw [he] at hP ⊢
    exact (isArc_empty_iff hM hP).2 ⟨rfl, rfl⟩
  · obtain ⟨p, hp, t, ht, hin, hncut, hf⟩ := WalkAx.exists_pos_in_arc hne h
    have hncut' : ¬ M.IsCut (S \ {c}) (p + t) := fun h' =>
      hncut (Model.isCut_mono M sdiff_sub h')
    obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := hM.two_cuts hS' hne'
    obtain ⟨l, hl, r, hr, hlr, hxin, hno⟩ := Chazelle.Core.exists_gap (hM.finite_cuts hS' hfin') hk₁
      hk₂ hk hncut'
    obtain ⟨Z, hZ, hZa⟩ := hM.arc_of_gap hS' hfin' hl hr hlr (fun k hk hc' => hno k hc' hk)
    have fZ := hZa.2.2.2.2.2.2 p t hp ht.1 ht.2 hxin
    have hZP : Z = P := WalkAx.faces_unique hZ hs.mem fZ (faces_mono hf hs.sub₁)
    subst hZP
    refine ⟨l, r, hZa, M.arcWt_mono fun y hy => ?_⟩
    have hl' : ¬ sideInArc a b l := fun h' => h.2.2.2.2.2.1 l h' (Model.isCut_mono M sdiff_sub hl)
    have hr' : ¬ sideInArc a b r := fun h' => h.2.2.2.2.2.1 r h' (Model.isCut_mono M sdiff_sub hr)
    exact (Chazelle.Core.cyc_same hy hin hl' hr' hlr).2 hxin

/-- **An arc of `P` is an arc of `R₁` or of `R₂`, or contains a lost key.** -/
theorem arcs_merged_cases (hne' : (S \ {c}).Nonempty) {a b : ℝ}
    (h : M.IsArc (S \ {c}) P a b) :
    M.IsArc S R₁ a b ∨ M.IsArc S R₂ a b ∨ ∃ k ∈ lostKeys M S c, sideInArc a b k := by
  have hne : S.Nonempty := ⟨c, hc⟩
  by_cases hk : ∃ k, M.IsCut S k ∧ sideInArc a b k
  · obtain ⟨k, hk1, hk2⟩ := hk
    exact Or.inr (Or.inr ⟨k, ⟨hk1, h.2.2.2.2.2.1 k hk2⟩, hk2⟩)
  push Not at hk
  obtain ⟨ha, hb, hab⟩ := WalkAx.arc_cuts hne' h
  obtain ⟨Y, hY, hYa⟩ := hM.arc_of_gap hS hfin (Model.isCut_mono M sdiff_sub ha)
    (Model.isCut_mono M sdiff_sub hb) hab (fun k hk' hcut => hk k hcut hk')
  rcases split_cases hc hs hY with rfl | rfl | ⟨hY', hYP⟩
  · simp_all
  · simp_all
  · exfalso
    obtain ⟨p, hp, t, ht, hin, -, hf⟩ := WalkAx.exists_pos_in_arc hne hYa
    exact hYP (WalkAx.faces_unique hY' hs.mem hf (h.2.2.2.2.2.2 p t hp ht.1 ht.2 hin))

/-- A gap of `S'` containing a lost key is an arc of `P`. -/
theorem gap_lost_arc {k : ℝ} (hk : k ∈ lostKeys M S c) {l r : ℝ}
    (hg : Gap M (S \ {c}) l r) (hin : sideInArc l r k) : M.IsArc (S \ {c}) P l r := by
  have hS' : S \ {c} ⊆ M.Adm := sdiff_sub.trans hS
  have hfin' : (S \ {c}).Finite := hfin.subset sdiff_sub
  obtain ⟨hl, hr, hlr, hfree⟩ := hg
  obtain ⟨Z, hZ, hZa⟩ := hM.arc_of_gap hS' hfin' hl hr hlr hfree
  have := arc_around_lost hM hS hfin hc hs hk hZ hZa hin
  simp_all


end

/-- An arc of a nonempty family is a gap. -/
theorem gap_of_arc {G : Set (Set Point)} (hne : G.Nonempty) {U : Set Point} {a b : ℝ}
    (h : M.IsArc G U a b) : Gap M G a b := by
  obtain ⟨ha, hb, hab⟩ := WalkAx.arc_cuts hne h
  exact ⟨ha, hb, hab, h.2.2.2.2.2.1⟩

section
variable (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S) (hs : Merge.IsSplit M.D (S \ {c}) c P R₁ R₂)
include hM hS hfin hc hs
/-- **Upper bound for the merged weight** (`S'` nonempty). -/
theorem weight_merged_le (hne' : (S \ {c}).Nonempty) {w : ℕ}
    (h1 : M.weight S R₁ ≤ w) (h2 : M.weight S R₂ ≤ w)
    (hJ : ∀ l r, Gap M (S \ {c}) l r → (∃ k ∈ lostKeys M S c, sideInArc l r k) →
      M.arcWt l r ≤ w) : M.weight (S \ {c}) P ≤ w := by
  refine weight_le fun a b h => ?_
  rcases arcs_merged_cases hM hS hfin hc hs hne' h with h' | h' | h'
  · exact (le_weight hM hS hfin (split_mem₁ hc hs) h').trans h1
  · exact (le_weight hM hS hfin (split_mem₂ hc hs) h').trans h2
  · exact hJ a b (gap_of_arc hne' h) h'

/-- The weights of `R₁` and `R₂` are at most the merged weight. -/
theorem weight_le_merged₁ :
    M.weight S R₁ ≤ M.weight (S \ {c}) P := by
  have hS' : S \ {c} ⊆ M.Adm := sdiff_sub.trans hS
  have hfin' : (S \ {c}).Finite := hfin.subset sdiff_sub
  refine weight_le fun a b h => ?_
  obtain ⟨a', b', h', hle⟩ := arcs_merged_ge hM hS hfin hc hs h
  exact hle.trans (le_weight hM hS' hfin' hs.mem h')

theorem weight_le_merged₂ :
    M.weight S R₂ ≤ M.weight (S \ {c}) P :=
  weight_le_merged₁ hM hS hfin hc hs.symm

/-- A gap of `S'` around a lost key weighs at most the merged weight. -/
theorem gap_le_merged {k : ℝ} (hk : k ∈ lostKeys M S c) {l r : ℝ}
    (hg : Gap M (S \ {c}) l r) (hin : sideInArc l r k) :
    M.arcWt l r ≤ M.weight (S \ {c}) P := by
  have hS' : S \ {c} ⊆ M.Adm := sdiff_sub.trans hS
  have hfin' : (S \ {c}).Finite := hfin.subset sdiff_sub
  exact le_weight hM hS' hfin' hs.mem (gap_lost_arc hM hS hfin hc hs hk hg hin)


end

/-- **The merged weight when `S'` is empty**: `size`. -/
theorem weight_merged_empty (hM : WalkAx M) (hs : Merge.IsSplit M.D (S \ {c}) c P R₁ R₂)
    (he : S \ {c} = ∅) : M.weight (S \ {c}) P = M.size := by
  have hP := hs.mem
  rw [he] at hP ⊢
  exact weight_empty hM hP

end Split

/-- **The model weight is local** (`Merge.WeightLocal` for `M.weight`), on the admissible
families of a model satisfying the walk axioms. -/
theorem weightLocal (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite) :
    Merge.WeightLocal M.D F M.weight := by
  intro S hSF c hc X hX hcX
  have hS : S ⊆ M.Adm := hSF.trans hF
  have hSfin : S.Finite := hfin.subset hSF
  have hsys := hM.sys S hS hSfin
  obtain ⟨P, R₁, R₂, hs⟩ := Merge.exists_removal_split hsys subset_rfl hc
  have hX1 : X ≠ R₁ := by
    rintro rfl
    exact hcX ((split_touches_iff hM hS hSfin hc hs hX).2 (Or.inl rfl))
  have hX2 : X ≠ R₂ := by
    rintro rfl
    exact hcX ((split_touches_iff hM hS hSfin hc hs hX).2 (Or.inr rfl))
  exact weight_other hM hS hSfin hc hs hX hX1 hX2

end

end Gran

end Chazelle.Core
