module

public import Chazelle.Golf

public import Chazelle.Core.SpecFacts

/-!
# WP-B, part 1: the cut structure of a disk model from walk axioms

This file isolates what the combinatorial Lemmas 2.1–2.2 (`CutStructureSpec`) need to know about
a disk model `M` into a structure of **walk axioms** `WalkAx M`, and proves the cut structure
from them.  The two good models (`chainModel C`, `interiorModel Q`) satisfy the axioms
(`Chazelle.Core.FactsChain`, `Chazelle.Core.FactsInterior`).

## The walk axioms (`WalkAx`)

* the domain is open, preconnected and nonempty;
* the walk edges are nondegenerate, the walk avoids the domain, and every position is *clean*
  (`SideClean`: near its point, the open left sector lies in the domain);
* every finite admissible family is a `ChordSystem` of the domain (Lemma 2.1 in its Euclidean
  form is available for it);
* every admissible chord is a horizontal segment `[a, b]`, `a ≠ b`, with open part in the domain,
  attached to the walk at each endpoint, and two distinct positions at an endpoint have disjoint
  left sectors near it (`WalkEnd`);
* **reach**: from a point of the domain at a height that is not the height of a walk vertex, the
  horizontal ray to the east stays in the domain until it hits the walk at a point inside an
  edge that goes up (so that the domain is on its left, i.e. to the west).

## Results

* `WalkAx.faces_existsUnique` (part 1 of `CutStructureSpec`): at a non-cut position inside a walk
  edge, the walk faces exactly one region;
* `WalkAx.exists_faces` (part 2): every region is faced at some position inside a walk edge;
* `WalkAx.eq_iff_not_separates` (part 3, **for non-cut positions**): two non-cut positions face
  the same region iff no chord separates their keys.

The original part 3 of `CutStructureSpec` (without non-cut hypotheses) was false for positions
whose key is a cut (review finding B1): such a position faces a region, but its key is on neither
side of the chord in the sense of `sideInArc`.  `CutStructureSpec` now carries the two non-cut
hypotheses; `CutStructureSpecNC` (same statement) is kept for reference, and
`Chazelle.Core.cutStructure` proves the spec.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft SideClean SideSectorIn ChordSystem
  freeIn regionsIn sideLeft_edge sideKey_inj sideInArc_swap sideArc_split)
open Chazelle.Jordan (offset nrm sqLen sqLen_pos det_offset eventually_offset_mem convex_det_pos)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext lerp_mem_segment)

/-! ## The walk axioms -/

/-- The endpoint condition for a chord `c` at its endpoint `a`: `c` is attached to the walk at a
position of point `a`, and two distinct positions of point `a` have disjoint left sectors near
`a`. -/
def WalkEnd (W : Polygon) (c : Set Point) (a : Point) : Prop :=
  (∃ p t, SideAttach W c p t ∧ sidePt W p t = a) ∧
    ∀ (p p' : ℕ) (t t' : ℝ), p < W.n → 0 ≤ t → t < 1 → p' < W.n → 0 ≤ t' → t' < 1 →
      (p = p' → t ≠ t') → sidePt W p t = a → sidePt W p' t' = a →
        ∃ r > 0, ∀ x ∈ ball a r, sideLeft W p t x → ¬ sideLeft W p' t' x

/-- **The walk axioms** of a disk model (see the module docstring). -/
structure WalkAx (M : Model) : Prop where
  isOpen : IsOpen M.D
  preconn : IsPreconnected M.D
  nonempty : M.D.Nonempty
  nd : ∀ p < M.W.n, M.W.vtx p ≠ M.W.vtx ((p + 1) % M.W.n)
  trace : ∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → sidePt M.W p t ∉ M.D
  clean : ∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → SideClean M.W M.D p t
  sys : ∀ F, F ⊆ M.Adm → F.Finite → ChordSystem M.D F
  ends : ∀ c ∈ M.Adm, ∃ a b : Point, a ≠ b ∧ c = Chazelle.segment a b ∧ a.2 = b.2 ∧
    (∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ M.D) ∧ WalkEnd M.W c a ∧ WalkEnd M.W c b
  reach : ∀ z ∈ M.D, (∀ i < M.W.n, z.2 ≠ (M.W.vtx i).2) →
    ∃ s > (0 : ℝ), (∀ s' ∈ Ico (0 : ℝ) s, ((z.1 + s', z.2) : Point) ∈ M.D) ∧
      ∃ p < M.W.n, ∃ t ∈ Ioo (0 : ℝ) 1, sidePt M.W p t = ((z.1 + s, z.2) : Point) ∧
        (M.W.vtx p).2 < (M.W.vtx ((p + 1) % M.W.n)).2

/-- **Corrected cut structure** (`CutStructureSpec` with part 3 restricted to non-cut
positions). -/
def CutStructureSpecNC : Prop :=
  ∀ (M : Model) (Q : Polygon) (F : Set (Set Point)), GoodModel M → M.ChordFamily Q F →
    (∀ (p : ℕ) (t : ℝ), p < M.W.n → 0 < t → t < 1 → ¬ M.IsCut F (p + t) →
      ∃! U, U ∈ M.regions F ∧ M.Faces p t U) ∧
    (∀ U ∈ M.regions F, ∃ (p : ℕ) (t : ℝ), p < M.W.n ∧ 0 < t ∧ t < 1 ∧ M.Faces p t U) ∧
    (∀ (p p' : ℕ) (t t' : ℝ) (U U' : Set Point), U ∈ M.regions F → U' ∈ M.regions F →
      p < M.W.n → p' < M.W.n → 0 < t → t < 1 → 0 < t' → t' < 1 →
      ¬ M.IsCut F (p + t) → ¬ M.IsCut F (p' + t') →
      M.Faces p t U → M.Faces p' t' U' →
        (U = U' ↔ ∀ c ∈ F, ¬ M.Separates c (p + t) (p' + t')))

namespace WalkAx

variable {M : Model}

/-! ## Elementary consequences -/

theorem wa_eq (p : ℕ) : M.wa p = M.W.vtx p := rfl

theorem wb_eq (p : ℕ) : M.wb p = M.W.vtx ((p + 1) % M.W.n) := rfl

theorem lerp_eq_sidePt (p : ℕ) (t : ℝ) : lerp (M.wa p) (M.wb p) t = sidePt M.W p t := rfl

/-- The offsets of a position inside an edge are eventually in any ball around its point and in
its left sector. -/
theorem eventually_offset_left (hM : WalkAx M) {p : ℕ} (hp : p < M.W.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset (M.wa p) (M.wb p) t δ ∈ ball (sidePt M.W p t) r ∧
      sideLeft M.W p t (offset (M.wa p) (M.wb p) t δ) := by
  have hne := hM.nd p hp
  filter_upwards [eventually_offset_mem 1 isOpen_ball (mem_ball_self hr), self_mem_nhdsWithin]
    with δ hδ hδ0
  Ξ' one_mul at hδ
  refine ⟨hδ, ?_⟩
  Ξ sideLeft_edge hne ht, ← wa_eq, ← wb_eq, det_offset
  have hδ0' := hδ0
  exact mul_pos hδ0' (sqLen_pos hne)

/-- A position inside an edge whose small left sector lies in `K` faces only sets meeting `K`. -/
theorem faces_meets (hM : WalkAx M) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {K U : Set Point} (hK : SideSectorIn M.W K p t) (hU : M.Faces p t U) : (U ∩ K).Nonempty := by
  obtain ⟨r, hr, hsec⟩ := hK
  obtain ⟨δ, h1, h2⟩ := (hU.and (hM.eventually_offset_left hp ht hr)).exists
  exact ⟨_, h1, hsec _ h2.1 h2.2⟩

/-- A point of an attached set is its endpoint when the set is a segment with open part in the
domain. -/
theorem attach_endpoint (hM : WalkAx M) {a b : Point}
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ M.D) {p : ℕ} {t : ℝ}
    (h : SideAttach M.W (Chazelle.segment a b) p t) : sidePt M.W p t = a ∨ sidePt M.W p t = b := by
  obtain ⟨hp, ht, ht1, hmem, -⟩ := h
  have hnd := hM.trace p hp t ht ht1.le
  obtain ⟨s, hs0, hs1, he⟩ := Geometry.mem_segment_iff_lerp.1 hmem
  Ξ' he at hnd ⊢
  rcases hs0.lt_or_eq with hs0 | hs0
  · rcases hs1.lt_or_eq with hs1 | hs1
    · exact absurd (hopen s ⟨hs0, hs1⟩) hnd
    · right; Ξ hs1, Geometry.lerp_one
  · left; Ξ ← hs0, Geometry.lerp_zero

/-- The open part of a reversed segment. -/
theorem open_rev {D : Set Point} {a b : Point} (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ D) :
    ∀ s ∈ Ioo (0 : ℝ) 1, lerp b a s ∈ D := by
  intro s hs
  have e : lerp b a s = lerp a b (1 - s) := by
    apply point_ext <;> simp [lerp] <;> ring
  rw [e]; exact hopen _ ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- **Two attachments with distinct points** of an admissible chord: the chord is the segment
between their points, horizontal, with open part in the domain, and the endpoint conditions hold
at both points. -/
theorem attach_seg (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) :
    c = Chazelle.segment (sidePt M.W pa ta) (sidePt M.W pb tb) ∧
      (sidePt M.W pa ta).2 = (sidePt M.W pb tb).2 ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp (sidePt M.W pa ta) (sidePt M.W pb tb) s ∈ M.D) ∧
      WalkEnd M.W c (sidePt M.W pa ta) ∧ WalkEnd M.W c (sidePt M.W pb tb) := by
  obtain ⟨a, b, hab, rfl, hy, hopen, ha, hb⟩ := hM.ends c hc
  rcases hM.attach_endpoint hopen hA with h1 | h1 <;>
    rcases hM.attach_endpoint hopen hB with h2 | h2 <;> Ξ' h1, h2 at hAB ⊢
  · exact absurd rfl hAB
  · exact ⟨rfl, hy, hopen, ha, hb⟩
  · exact ⟨Geometry.segment_comm _ _, hy.symm, open_rev hopen, hb, ha⟩
  · exact absurd rfl hAB

/-- **The two sides of an admissible chord** lie in different components of the domain minus
the chord (from the chord system `{c}`, Lemma 2.1). -/
theorem hsep (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {a b : Point}
    (hcab : c = Chazelle.segment a b) (hab : a ≠ b) (hy : a.2 = b.2)
    (hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a b s ∈ M.D) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      connectedComponentIn (M.D \ Chazelle.segment a b) (offset a b (1 / 2) δ) ≠
        connectedComponentIn (M.D \ Chazelle.segment a b) (offset b a (1 / 2) δ) := by
  have hF := hM.sys {c} (singleton_subset_iff.2 hc) (finite_singleton c)
  have hmid := hopen (1 / 2) ⟨⊛, ⊛⟩
  have hmc : lerp a b (1 / 2) ∈ c := by
    rw [hcab]; exact lerp_mem_segment _ _ (⊛) (⊛)
  obtain ⟨ε₀, hε₀, hsep⟩ := hF.chord_separates_in subset_rfl (mem_singleton c) hmc hmid
  have hfree : freeIn M.D {c} = M.D \ Chazelle.segment a b := by
    Ξ freeIn, sUnion_singleton, hcab
  Ξ' hfree at hsep
  have hd : b.1 - a.1 ≠ 0 := by
    intro h; apply hab; exact point_ext (⟡) hy
  have hdpos : 0 < |b.1 - a.1| := abs_pos.2 hd
  filter_upwards [Ioo_mem_nhdsGT (div_pos hε₀ hdpos)] with δ hδ
  have hε : 0 < δ * |b.1 - a.1| := mul_pos hδ.1 hdpos
  have hε' : δ * |b.1 - a.1| < ε₀ := by
    have := hδ.2; Ξ' lt_div_iff₀ hdpos at this; exact this
  obtain ⟨-, -, hne⟩ := hsep _ hε hε'
  have e1 : offset a b (1 / 2) δ =
      ((lerp a b (1 / 2)).1, (lerp a b (1 / 2)).2 + δ * (b.1 - a.1)) := by
    apply point_ext <;> Θ offset, nrm, lerp, hy
  have e2 : offset b a (1 / 2) δ =
      ((lerp a b (1 / 2)).1, (lerp a b (1 / 2)).2 - δ * (b.1 - a.1)) := by
    apply point_ext <;> simp [offset, nrm, lerp, hy] <;> ring
  Ξ e1, e2
  rcases lt_or_gt_of_ne hd with h | h
  · Ξ' abs_of_neg h at hne
    have e3 : δ * (b.1 - a.1) = -(δ * -(b.1 - a.1)) := ⋆
    Ξ e3, sub_neg_eq_add, ← sub_eq_add_neg
    exact fun h' => hne h'.symm
  · Ξ' abs_of_pos h at hne
    exact hne

/-- **The split of the walk by an admissible chord** (the side-aware Lemma 2.1, from the generic
`sideArc_split`): for two attachments `A`, `B` of `c ∈ Adm` with distinct points, there are two
distinct components `K₁ ≠ K₂` of `D \ c` such that positions strictly between `A` and `B` have
their small left sector in `K₁`, and positions strictly between `B` and `A` in `K₂`. -/
theorem split (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {pa pb : ℕ} {ta tb : ℝ}
    (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) :
    ∃ K₁ K₂ : Set Point, K₁ ≠ K₂ ∧
      (∃ c₁, K₁ = connectedComponentIn (M.D \ c) c₁) ∧
      (∃ c₂, K₂ = connectedComponentIn (M.D \ c) c₂) ∧
      (∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc (pa + ta) (pb + tb) (p + t) →
        SideSectorIn M.W K₁ p t) ∧
      (∀ p < M.W.n, ∀ t : ℝ, 0 ≤ t → t < 1 → sideInArc (pb + tb) (pa + ta) (p + t) →
        SideSectorIn M.W K₂ p t) := by
  obtain ⟨hcab, hy, hopen, hEA, hEB⟩ := hM.attach_seg hc hA hB hAB
  have hA' := hA
  have hB' := hB
  Ξ' hcab at hA' hB'
  obtain ⟨hpa, hta, hta1, -⟩ := hA
  obtain ⟨hpb, htb, htb1, -⟩ := hB
  obtain ⟨K₁, K₂, hne, h₁, h₂, hK₁, hK₂, -, -⟩ := sideArc_split M.W hM.isOpen hAB hM.nd hM.trace
    hM.clean hopen hA' rfl hB' rfl
    (fun p hp t ht ht1 hne' heq => hEA.2 pa p ta t hpa hta hta1 hp ht ht1
      (fun h => fun h' => hne' h.symm h'.symm) rfl heq)
    (fun p hp t ht ht1 hne' heq => hEB.2 pb p tb t hpb htb htb1 hp ht ht1
      (fun h => fun h' => hne' h.symm h'.symm) rfl heq)
    (hM.hsep hc hcab hAB hy hopen)
  Ξ' ← hcab at h₁ h₂
  exact ⟨K₁, K₂, hne, h₁, h₂, hK₁, hK₂⟩

/-! ## Part 1: a non-cut position faces exactly one region -/

/-- Two regions faced at the same position are equal. -/
theorem faces_unique {F : Set (Set Point)} {p : ℕ} {t : ℝ} {U U' : Set Point}
    (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F) (h : M.Faces p t U) (h' : M.Faces p t U') :
    U = U' := by
  obtain ⟨δ, h1, h2⟩ := (h.and h').exists
  rcases Chazelle.Chain.regionsIn_eq_or_disjoint hU hU' with heq | hdisj
  · exact heq
  · exact absurd (hdisj.le_bot ⟨h1, h2⟩) (fun h => h)

/-- At a non-cut position inside a walk edge, the left offsets eventually avoid every chord of
a finite admissible family. -/
theorem eventually_offset_not_mem (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut F (p + t))
    {c : Set Point} (hc : c ∈ F) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset (M.wa p) (M.wb p) t δ ∉ c := by
  obtain ⟨a, b, hab, hcab, -, hopen, -, -⟩ := hM.ends c (hF hc)
  set q := sidePt M.W p t with hq
  have hne := hM.nd p hp
  by_cases hqc : q ∈ c
  · -- `q` is an endpoint of `c`
    have hqD : q ∉ M.D := hM.trace p hp t ht.1.le ht.2.le
    obtain ⟨q', hcq⟩ : ∃ q', c = Chazelle.segment q q' := by
      Ξ' hcab at hqc ⊢
      obtain ⟨s, hs0, hs1, he⟩ := Geometry.mem_segment_iff_lerp.1 hqc
      rcases hs0.lt_or_eq with hs0 | hs0
      · rcases hs1.lt_or_eq with hs1 | hs1
        · exact absurd (he ▸ hopen s ⟨hs0, hs1⟩) hqD
        · refine ⟨a, ?_⟩
          Ξ he, hs1, Geometry.lerp_one, Geometry.segment_comm
      · exact ⟨b, Ρ he, ← hs0, Geometry.lerp_zero⟩
    -- the chord does not go into the open left half-plane
    have hq0 : det (M.wa p) (M.wb p) q = 0 := by
      rw [hq, ← lerp_eq_sidePt]; exact Geometry.det_lerp_self _ _ _
    have hle : det (M.wa p) (M.wb p) q' ≤ 0 := by
      by_contra hpos
      push Not at hpos
      apply hcut
      refine ⟨c, hc, p, t, ⟨hp, ht.1.le, ht.2, ?_, 1, one_pos, fun x hx hxq _ => ?_⟩, rfl⟩
      · rw [hcq]; exact Geometry.left_mem_segment _ _
      · Ξ' hcq at hx
        obtain ⟨s, hs0, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
        have hs : 0 < s := by
          rcases hs0.lt_or_eq with h | h
          · exact h
          · exact absurd (Ρ ← h, Geometry.lerp_zero) hxq
        Ξ sideLeft_edge hne ht, ← wa_eq, ← wb_eq, Geometry.det_lerp, hq0
        nlinarith
    filter_upwards [self_mem_nhdsWithin] with δ hδ hmem
    Ξ' hcq at hmem
    obtain ⟨s, hs0, hs1, he⟩ := Geometry.mem_segment_iff_lerp.1 hmem
    have h1 := det_offset (M.wa p) (M.wb p) t δ
    Ξ' he, Geometry.det_lerp, hq0 at h1
    have hδ' := hδ
    have hsq : 0 < sqLen (M.wa p) (M.wb p) := sqLen_pos hne
    have := mul_pos hδ' hsq
    nlinarith [mul_nonneg hs0 (neg_nonneg.2 hle)]
  · have hcl : IsClosed c := by rw [hcab]; exact Geometry.isClosed_segment _ _
    have := eventually_offset_mem 1 hcl.isOpen_compl (u := M.wa p) (v := M.wb p) (t := t) hqc
    exact this.mono fun δ h => by simpa using h

/-- **Part 1 (existence).**  At a non-cut position inside a walk edge the walk faces some
region. -/
theorem exists_faces_of_not_cut (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F (p + t)) : ∃ U ∈ M.regions F, M.Faces p t U := by
  obtain ⟨r, hr, hcl⟩ := hM.clean p hp t ht.1.le ht.2
  have hall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), offset (M.wa p) (M.wb p) t δ ∈ freeIn M.D F := by
    have h1 := (hfin.eventually_all (p := fun c δ => offset (M.wa p) (M.wb p) t δ ∉ c)).2
      (fun c hc => hM.eventually_offset_not_mem hF hp ht hcut hc)
    filter_upwards [h1, hM.eventually_offset_left hp ht hr] with δ hδ1 hδ2
    refine ⟨?_, fun ⟨c, hc, hmem⟩ => hδ1 c hc hmem⟩
    by_contra hD
    exact hcl _ hδ2.1 hD hδ2.2
  obtain ⟨δ₀, hδ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  Ξ' mem_Ioi at hδ₀
  set L := (offset (M.wa p) (M.wb p) t) '' Ioo 0 δ₀ with hL
  have hLc : IsPreconnected L :=
    isPreconnected_Ioo.image _ (Chazelle.Jordan.continuous_offset _ _ _).continuousOn
  have hLF : L ⊆ freeIn M.D F := by
    rintro _ ⟨δ, hδ, rfl⟩; exact hsub hδ
  set z := offset (M.wa p) (M.wb p) t (δ₀ / 2) with hz
  have hzL : z ∈ L := ⟨δ₀ / 2, ⟨⟡, ⟡⟩, rfl⟩
  refine ⟨connectedComponentIn (freeIn M.D F) z, ⟨z, hLF hzL, rfl⟩, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
  exact hLc.subset_connectedComponentIn hzL hLF ⟨δ, hδ, rfl⟩

/-- **Part 1.**  At a non-cut position inside a walk edge the walk faces exactly one region. -/
theorem faces_existsUnique (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut F (p + t)) : ∃! U, U ∈ M.regions F ∧ M.Faces p t U := by
  obtain ⟨U, hU, hf⟩ := hM.exists_faces_of_not_cut hF hfin hp ht hcut
  exact ⟨U, ⟨hU, hf⟩, fun U' ⟨hU', hf'⟩ => faces_unique hU' hU hf' hf⟩

/-! ## Part 2: every region is faced -/

/-- The heights of the points of a finite chord family form a finite set. -/
theorem finite_chord_heights {F : Set (Set Point)} (hF : ChordSystem M.D F) :
    {y : ℝ | ∃ c ∈ F, ∃ x ∈ c, x.2 = y}.Finite := by
  have : {y : ℝ | ∃ c ∈ F, ∃ x ∈ c, x.2 = y} ⊆ ⋃ c ∈ F, Prod.snd '' c := by
    rintro y ⟨c, hc, x, hx, rfl⟩
    ϴ mem_iUnion
    exact ⟨c, hc, x, hx, rfl⟩
  refine Set.Finite.subset (hF.finite.biUnion fun c hc => ?_) this
  obtain ⟨y, a, b, -, rfl⟩ := hF.hchord c hc
  refine (finite_singleton y).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hx.1

/-- **Part 2.**  Every region of a finite admissible family is faced at some position inside a
walk edge. -/
theorem exists_faces (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {U : Set Point} (hU : U ∈ M.regions F) :
    ∃ (p : ℕ) (t : ℝ), p < M.W.n ∧ 0 < t ∧ t < 1 ∧ M.Faces p t U := by
  have hsys := hM.sys F hF hfin
  have hUo : IsOpen U := hsys.regionsIn_open subset_rfl hU
  obtain ⟨z₀, hz₀⟩ := Chazelle.Chain.regionsIn_nonempty hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hUo z₀ hz₀
  -- a point of `U` at a generic height
  set B : Set ℝ := {y | ∃ i < M.W.n, (M.W.vtx i).2 = y} ∪ {y | ∃ c ∈ F, ∃ x ∈ c, x.2 = y}
    with hB
  have hBfin : B.Finite := by
    refine Set.Finite.union ?_ (finite_chord_heights hsys)
    have : {y | ∃ i < M.W.n, (M.W.vtx i).2 = y} = (fun i => (M.W.vtx i).2) '' Iio M.W.n := by
      ext y; Θ mem_Iio
    rw [this]; exact (finite_Iio _).image _
  obtain ⟨y, hyI, hyB⟩ := ((Ioo_infinite (lt_add_of_pos_right z₀.2 hr)).sdiff hBfin).nonempty
  set z : Point := (z₀.1, y) with hz
  have hzU : z ∈ U := by
    apply hball
    Ξ mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq
    ϴ hz, sub_self, abs_zero
    Ξ max_lt_iff, abs_of_pos (by linarith [hyI.1])
    exact ⟨hr, by linarith [hyI.2]⟩
  have hUfree : U ⊆ freeIn M.D F := Chazelle.Chain.regionsIn_subset hU
  have hzD : z ∈ M.D := (hUfree hzU).1
  have hzv : ∀ i < M.W.n, z.2 ≠ (M.W.vtx i).2 := fun i hi h => hyB (Or.inl ⟨i, hi, h.symm⟩)
  have hzc : ∀ x : Point, x.2 = y → x ∉ ⋃₀ F := by
    rintro x hx ⟨c, hc, hxc⟩
    exact hyB (Or.inr ⟨c, hc, x, hxc, hx⟩)
  obtain ⟨s, hs, hseg, p, hp, t, ht, hq, hup⟩ := hM.reach z hzD hzv
  set q : Point := (z.1 + s, z.2) with hqdef
  -- the segment from `z` to `q` (half-open) is in `U`
  set L := (fun s' : ℝ => ((z.1 + s', z.2) : Point)) '' Ico 0 s with hL
  have hLc : IsPreconnected L :=
    isPreconnected_Ico.image _ (by fun_prop : Continuous fun s' : ℝ => ((z.1 + s', z.2) : Point)).continuousOn
  have hLF : L ⊆ freeIn M.D F := by
    rintro _ ⟨s', hs', rfl⟩
    exact ⟨hseg s' hs', hzc _ rfl⟩
  have hzL : z ∈ L := ⟨0, ⟨le_rfl, hs⟩, ⊚ hz⟩
  have hLU : L ⊆ U := by
    Ξ Chazelle.Chain.regionsIn_eq_component hU hzU
    exact hLc.subset_connectedComponentIn hzL hLF
  -- a half-disk on the left of the edge at `q` is free
  have hqF : q ∉ ⋃₀ F := hzc q rfl
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.isOpen_iff.1 (hsys.isClosed_sUnion subset_rfl).isOpen_compl q hqF
  obtain ⟨r₂, hr₂, hcl⟩ := hM.clean p hp t ht.1.le ht.2
  have hne := hM.nd p hp
  set u := M.W.vtx p
  set v := M.W.vtx ((p + 1) % M.W.n)
  set H : Set Point := ball q (min r₁ r₂) ∩ {x | 0 < 1 * det u v x} with hH
  have hHc : IsPreconnected H := ((convex_ball _ _).inter (convex_det_pos _ _ 1)).isPreconnected
  have hHF : H ⊆ freeIn M.D F := by
    rintro x ⟨hx1, hx2⟩
    ϴ' mem_ofPred_eq, one_mul at hx2
    refine ⟨?_, hb₁ (ball_subset_ball (min_le_left _ _) hx1)⟩
    by_contra hxD
    refine hcl x ?_ hxD ?_
    · rw [hq]; exact ball_subset_ball (min_le_right _ _) hx1
    · rw [sideLeft_edge hne ht]; exact hx2
  -- a point of the segment lies in the half-disk
  have hq0 : det u v q = 0 := by
    rw [← hq]; exact Geometry.det_lerp_self _ _ _
  set ε := min (min r₁ r₂) s / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; have := lt_min (lt_min hr₁ hr₂) hs; linarith
  have hεr : ε < min r₁ r₂ := by rw [hε]; have := min_le_left (min r₁ r₂) s; linarith
  have hεs : ε < s := by rw [hε]; have := min_le_right (min r₁ r₂) s; linarith
  have hw : ((z.1 + (s - ε), z.2) : Point) ∈ H := by
    refine ⟨?_, ?_⟩
    · Ξ mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq
      ϴ hqdef, sub_self, abs_zero
      Ξ max_lt_iff, show z.1 + (s - ε) - (z.1 + s) = -ε by ring, abs_neg, abs_of_pos hε0
      exact ⟨hεr, lt_of_le_of_lt le_rfl (lt_min (lt_min hr₁ hr₂) hr₂ |>.trans_le (min_le_left _ _))⟩
    · ϴ mem_ofPred_eq, one_mul
      have e : det u v ((z.1 + (s - ε), z.2) : Point) = det u v q + ε * (v.2 - u.2) := by
        simp only [hqdef, det]; ring
      Ξ e, hq0
      have : 0 < v.2 - u.2 := ⟡
      nlinarith
  have hwL : ((z.1 + (s - ε), z.2) : Point) ∈ L := ⟨s - ε, ⟨⟡, ⟡⟩, rfl⟩
  have hHU : H ⊆ U := by
    Ξ Chazelle.Chain.regionsIn_eq_component hU (hLU hwL)
    exact hHc.subset_connectedComponentIn hw hHF
  refine ⟨p, t, hp, ht.1, ht.2, ?_⟩
  filter_upwards [hM.eventually_offset_left hp ht (lt_min hr₁ hr₂)] with δ hδ
  apply hHU
  refine ⟨by rw [← hq]; exact hδ.1, ?_⟩
  ϴ mem_ofPred_eq, one_mul
  Ξ ← sideLeft_edge hne ht
  exact hδ.2

/-! ## Part 3: the parenthesis structure -/

/-- **Separation by a single chord** (generic): in a chord system of a preconnected domain, two
free points of a submap `S` that no chord of `S` separates (they lie in the same component of
`D \ c` for every `c ∈ S`) lie in the same region of `S`. -/
theorem sameComp_of_forall {D : Set Point} {F : Set (Set Point)} (hF : ChordSystem D F)
    (hD : IsPreconnected D) {S : Set (Set Point)} (hS : S ⊆ F) :
    ∀ {u u' : Point}, u ∈ freeIn D S → u' ∈ freeIn D S →
      (∀ c ∈ S, connectedComponentIn (D \ c) u = connectedComponentIn (D \ c) u') →
        connectedComponentIn (freeIn D S) u = connectedComponentIn (freeIn D S) u' := by
  have hfin : S.Finite := hF.finite.subset hS
  induction S, hfin using Set.Finite.induction_on with
  | empty =>
    intro u u' hu hu' _
    Ξ' Chazelle.Chain.freeIn_empty at hu hu' ⊢
    Ξ hD.connectedComponentIn hu, hD.connectedComponentIn hu'
  | @insert c S hcS hSfin ih =>
    intro u u' hu hu' h
    have hS' : S ⊆ F := (subset_insert c S).trans hS
    have hc : c ∈ F := hS (mem_insert c S)
    have hins : insert c S ⊆ F := insert_subset hc hS'
    set A := freeIn D S with hA
    set A' := freeIn D (insert c S) with hA'
    have hA'eq : A' = A \ c := Chazelle.Chain.freeIn_insert D c S
    have huA : u ∈ A := (hA'eq ▸ hu).1
    have hu'A : u' ∈ A := (hA'eq ▸ hu').1
    have hIH : connectedComponentIn A u = connectedComponentIn A u' :=
      ih hS' huA hu'A fun d hd => h d (mem_insert_of_mem c hd)
    obtain ⟨R, hR, hcR, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ := hF.regionsIn_insert hS' hc hcS
    -- the region of `u` in `insert c S`
    set V := connectedComponentIn A' u with hV
    have hVmem : V ∈ regionsIn D (insert c S) := ⟨u, hu, rfl⟩
    have huV : u ∈ V := mem_connectedComponentIn hu
    have hfin_eq : ∀ {x : Point} {X : Set Point}, X ∈ regionsIn D (insert c S) → x ∈ X →
        X = connectedComponentIn A' x := fun hX hx => Chazelle.Chain.regionsIn_eq_component hX hx
    Ξ' heq at hVmem
    rcases hVmem with ⟨hVS, hVR⟩ | hVR₁₂
    · -- `V` is an old region
      have hV' : V = connectedComponentIn A u := Chazelle.Chain.regionsIn_eq_component hVS huV
      have hu'V : u' ∈ V := by rw [hV', hIH]; exact mem_connectedComponentIn hu'A
      exact connectedComponentIn_eq hu'V
    · -- `V` is one of the two new regions
      have hR₁R : R₁ ⊆ R \ c := fun x hx => hunion ▸ Or.inl hx
      have hR₂R : R₂ ⊆ R \ c := fun x hx => hunion ▸ Or.inr hx
      have hVR : V ⊆ R \ c := by
        rcases hVR₁₂ with h1 | h1
        · rw [h1]; exact hR₁R
        · Ξ' mem_singleton_iff at h1; rw [h1]; exact hR₂R
      have hRu : R = connectedComponentIn A u := Chazelle.Chain.regionsIn_eq_component hR (hVR huV).1
      have hu'R : u' ∈ R := by rw [hRu, hIH]; exact mem_connectedComponentIn hu'A
      have hu'c : u' ∉ c := (hA'eq ▸ hu').2
      -- the two sides of `c` at a point `w`
      obtain ⟨w, hwc, hwD⟩ := (hF.chord_inter_nonempty_isPreconnected hc).1
      have hRo : IsOpen R := hF.regionsIn_open hS' hR
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hRo w (hcR ⟨hwc, hwD⟩)
      obtain ⟨ε₁, hε₁, hs₁⟩ := hF.chord_separates_in hins (mem_insert c S) hwc hwD
      obtain ⟨ε₂, hε₂, hs₂⟩ := hF.chord_separates_in (singleton_subset_iff.2 hc)
        (mem_singleton c) hwc hwD
      set ε := min (min ε₁ ε₂) r / 2 with hε
      have hε0 : 0 < ε := by rw [hε]; have := lt_min (lt_min hε₁ hε₂) hr; linarith
      have hεm : ε < min (min ε₁ ε₂) r := by rw [hε]; have := lt_min (lt_min hε₁ hε₂) hr; linarith
      have hε₁' : ε < ε₁ := hεm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      have hε₂' : ε < ε₂ := hεm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
      have hεr : ε < r := hεm.trans_le (min_le_right _ _)
      obtain ⟨hp₁, hm₁, hne₁⟩ := hs₁ ε hε0 hε₁'
      obtain ⟨-, -, hne₂⟩ := hs₂ ε hε0 hε₂'
      have hfc : freeIn D {c} = D \ c := Ρ Chazelle.Chain.freeIn, sUnion_singleton
      Ξ' hfc at hne₂
      set wp : Point := (w.1, w.2 + ε) with hwp
      set wm : Point := (w.1, w.2 - ε) with hwm
      have hwpR : wp ∈ R := hball (by
        Ξ mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq
        ϴ hwp, sub_self, abs_zero, add_sub_cancel_left, abs_of_pos hε0
        exact max_lt hr hεr)
      have hwmR : wm ∈ R := hball (by
        Ξ mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq
        ϴ hwm, sub_self, abs_zero, sub_sub_cancel_left, abs_neg, abs_of_pos hε0
        exact max_lt hr hεr)
      -- the region of every point of `R \ c` is `R₁` or `R₂`
      have hin12 : ∀ x ∈ R \ c, connectedComponentIn A' x = R₁ ∨ connectedComponentIn A' x = R₂ := by
        intro x hx
        Ξ' ← hunion at hx
        rcases hx with hx | hx
        · exact Or.inl (hfin_eq hR₁ hx).symm
        · exact Or.inr (hfin_eq hR₂ hx).symm
      have hwpc : wp ∉ c := by
        have : wp ∈ A' := hp₁
        Ξ' hA'eq at this; exact this.2
      have hwmc : wm ∉ c := by
        have : wm ∈ A' := hm₁
        Ξ' hA'eq at this; exact this.2
      -- the component of a free point of `insert c S` in `D \ c`
      have hcomp : ∀ x w0 : Point, w0 ∈ A' → x ∈ connectedComponentIn A' w0 →
          connectedComponentIn (D \ c) x = connectedComponentIn (D \ c) w0 := by
        intro x w0 hw0 hx
        have hsub : connectedComponentIn A' w0 ⊆ D \ c := by
          Ξ ← hfc
          exact (connectedComponentIn_subset _ _).trans
            (Chazelle.Chain.freeIn_anti D (singleton_subset_iff.2 (mem_insert c S)))
        have := isPreconnected_connectedComponentIn.subset_connectedComponentIn hx hsub
        exact connectedComponentIn_eq (this (mem_connectedComponentIn hw0))
      by_contra hfalse
      have hVne := hfalse
      rcases hin12 wp ⟨hwpR, hwpc⟩ with hp | hp <;> rcases hin12 wm ⟨hwmR, hwmc⟩ with hm | hm <;>
        rcases hin12 u ⟨(hVR huV).1, (hVR huV).2⟩ with hU | hU <;>
        rcases hin12 u' ⟨hu'R, hu'c⟩ with hU' | hU'
      all_goals first
        | exact hne₁ (hp.trans hm.symm)
        | exact hVne (hU.trans hU'.symm)
        | skip
      all_goals refine absurd (h c (mem_insert c S)) ?_
      all_goals first
        | (rw [hcomp u wp hp₁ (by rw [hp, ← hU]; exact mem_connectedComponentIn hu),
            hcomp u' wm hm₁ (by rw [hm, ← hU']; exact mem_connectedComponentIn hu')]
           exact hne₂)
        | (rw [hcomp u wm hm₁ (by rw [hm, ← hU]; exact mem_connectedComponentIn hu),
            hcomp u' wp hp₁ (by rw [hp, ← hU']; exact mem_connectedComponentIn hu')]
           exact fun h' => hne₂ h'.symm)

/-- A region faced at a position whose small left sector lies in a component `K` of `D \ c`
(`c ∈ F`) is contained in `K`. -/
theorem region_subset_of_sector (hM : WalkAx M) {F : Set (Set Point)} {c : Set Point}
    (hc : c ∈ F) {U : Set Point} (hU : U ∈ M.regions F) {p : ℕ} (hp : p < M.W.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hf : M.Faces p t U) {k : Point}
    (hK : SideSectorIn M.W (connectedComponentIn (M.D \ c) k) p t) :
    U ⊆ connectedComponentIn (M.D \ c) k := by
  obtain ⟨x, hxU, hxK⟩ := hM.faces_meets hp ht hK hf
  have hsub : U ⊆ M.D \ c := fun y hy =>
    ⟨(Chazelle.Chain.regionsIn_subset hU hy).1,
      fun hyc => (Chazelle.Chain.regionsIn_subset hU hy).2 ⟨c, hc, hyc⟩⟩
  Ξ connectedComponentIn_eq hxK
  exact (Chazelle.Chain.regionsIn_isPreconnected hU).subset_connectedComponentIn hxU hsub

/-- The key of a non-cut position differs from the key of every attachment of a chord of `F`. -/
theorem key_ne_of_not_cut {F : Set (Set Point)} {c : Set Point} (hc : c ∈ F) {p pa : ℕ}
    {t ta : ℝ} (hcut : ¬ M.IsCut F (p + t)) (hA : SideAttach M.W c pa ta) :
    (p : ℝ) + t ≠ pa + ta := fun h => hcut ⟨c, hc, pa, ta, hA, h⟩

/-- Two attachments with distinct points have distinct keys. -/
theorem key_ne_of_pt_ne {pa pb : ℕ} {ta tb : ℝ} {c d : Set Point} (hA : SideAttach M.W c pa ta)
    (hB : SideAttach M.W d pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) :
    (pa : ℝ) + ta ≠ pb + tb := by
  intro h
  obtain ⟨rfl, rfl⟩ := sideKey_inj hA.2.1 hA.2.2.1 hB.2.1 hB.2.2.1 h
  exact hAB rfl

/-- **Part 3 (for non-cut positions).**  Two non-cut positions inside walk edges face the same
region iff no chord of `F` separates their keys. -/
theorem eq_iff_not_separates (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {p p' : ℕ} {t t' : ℝ} {U U' : Set Point} (hU : U ∈ M.regions F)
    (hU' : U' ∈ M.regions F) (hp : p < M.W.n) (hp' : p' < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (ht' : t' ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut F (p + t)) (hcut' : ¬ M.IsCut F (p' + t'))
    (hf : M.Faces p t U) (hf' : M.Faces p' t' U') :
    U = U' ↔ ∀ c ∈ F, ¬ M.Separates c (p + t) (p' + t') := by
  -- the two arcs of a chord
  have harcs : ∀ c ∈ F, ∀ {pa pb : ℕ} {ta tb : ℝ}, SideAttach M.W c pa ta →
      SideAttach M.W c pb tb → sidePt M.W pa ta ≠ sidePt M.W pb tb →
      ∃ k₁ k₂ : Point, connectedComponentIn (M.D \ c) k₁ ≠ connectedComponentIn (M.D \ c) k₂ ∧
        (sideInArc (pa + ta) (pb + tb) (p + t) → U ⊆ connectedComponentIn (M.D \ c) k₁) ∧
        (¬ sideInArc (pa + ta) (pb + tb) (p + t) → U ⊆ connectedComponentIn (M.D \ c) k₂) ∧
        (sideInArc (pa + ta) (pb + tb) (p' + t') → U' ⊆ connectedComponentIn (M.D \ c) k₁) ∧
        (¬ sideInArc (pa + ta) (pb + tb) (p' + t') →
          U' ⊆ connectedComponentIn (M.D \ c) k₂) := by
    intro c hc pa pb ta tb hA hB hAB
    obtain ⟨K₁, K₂, hne, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, h₁, h₂⟩ := hM.split (hF hc) hA hB hAB
    have hkAB := key_ne_of_pt_ne hA hB hAB
    refine ⟨k₁, k₂, hne, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · exact hM.region_subset_of_sector hc hU hp ht hf (h₁ p hp t ht.1.le ht.2 h)
    · have h' := (sideInArc_swap hkAB (key_ne_of_not_cut hc hcut hA)
        (key_ne_of_not_cut hc hcut hB)).2
      have h'' : sideInArc (pb + tb) (pa + ta) (p + t) := by
        by_contra hh; exact h (h' hh)
      exact hM.region_subset_of_sector hc hU hp ht hf (h₂ p hp t ht.1.le ht.2 h'')
    · exact hM.region_subset_of_sector hc hU' hp' ht' hf' (h₁ p' hp' t' ht'.1.le ht'.2 h)
    · have h' := (sideInArc_swap hkAB (key_ne_of_not_cut hc hcut' hA)
        (key_ne_of_not_cut hc hcut' hB)).2
      have h'' : sideInArc (pb + tb) (pa + ta) (p' + t') := by
        by_contra hh; exact h (h' hh)
      exact hM.region_subset_of_sector hc hU' hp' ht' hf' (h₂ p' hp' t' ht'.1.le ht'.2 h'')
  obtain ⟨u, hu⟩ := Chazelle.Chain.regionsIn_nonempty hU
  obtain ⟨u', hu'⟩ := Chazelle.Chain.regionsIn_nonempty hU'
  constructor
  · rintro rfl c hc ⟨pa, pb, ta, tb, hA, hB, hAB, hiff⟩
    obtain ⟨k₁, k₂, hne, h1, h2, h1', h2'⟩ := harcs c hc hA hB hAB
    by_cases hx : sideInArc (pa + ta) (pb + tb) (p + t)
    · have hx' := hiff.1 hx
      have e1 := h1 hx hu
      have e2 := h2' hx' hu
      exact hne ((connectedComponentIn_eq e1).trans (connectedComponentIn_eq e2).symm)
    · have hx' : sideInArc (pa + ta) (pb + tb) (p' + t') := by
        by_contra hh; exact hx (hiff.2 hh)
      have e1 := h2 hx hu
      have e2 := h1' hx' hu
      exact hne ((connectedComponentIn_eq e2).trans (connectedComponentIn_eq e1).symm)
  · intro hno
    by_contra hUU
    have hsys := hM.sys F hF hfin
    have hcomp : connectedComponentIn (freeIn M.D F) u ≠ connectedComponentIn (freeIn M.D F) u' := by
      rw [← Chazelle.Chain.regionsIn_eq_component hU hu,
        ← Chazelle.Chain.regionsIn_eq_component hU' hu']
      exact hUU
    have hex : ∃ c ∈ F, connectedComponentIn (M.D \ c) u ≠ connectedComponentIn (M.D \ c) u' := by
      by_contra hall
      push Not at hall
      exact hcomp (sameComp_of_forall hsys hM.preconn subset_rfl
        (Chazelle.Chain.regionsIn_subset hU hu) (Chazelle.Chain.regionsIn_subset hU' hu') hall)
    obtain ⟨c, hc, hcne⟩ := hex
    obtain ⟨a, b, hab, -, -, -, ⟨⟨pa, ta, hA, hAa⟩, -⟩, ⟨⟨pb, tb, hB, hBb⟩, -⟩⟩ := hM.ends c (hF hc)
    have hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb := by rw [hAa, hBb]; exact hab
    obtain ⟨k₁, k₂, -, h1, h2, h1', h2'⟩ := harcs c hc hA hB hAB
    apply hno c hc
    refine ⟨pa, pb, ta, tb, hA, hB, hAB, ?_⟩
    by_cases hx : sideInArc (pa + ta) (pb + tb) (p + t) <;>
      by_cases hx' : sideInArc (pa + ta) (pb + tb) (p' + t')
    · exact absurd ((connectedComponentIn_eq (h1 hx hu)).symm.trans
        (connectedComponentIn_eq (h1' hx' hu'))) hcne
    · exact ⟨fun _ => hx', fun _ => hx⟩
    · exact ⟨fun h => absurd h hx, fun h => absurd hx' h⟩
    · exact absurd ((connectedComponentIn_eq (h2 hx hu)).symm.trans
        (connectedComponentIn_eq (h2' hx' hu'))) hcne

end WalkAx

end

end Chazelle.Core
