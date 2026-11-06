module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvTasks
public import Chazelle.Core.SweepIoRec
public import Chazelle.Core.SweepMachine5

/-!
# The sweep (WP-D), stage 2: the attachments of a chord seen from a point (mathematics)

For a point `a` off the domain of a chain `C` (not above its top) with a free direction `σ`, the
chord `e = shoot C a σ` runs from `a` to its far end `w = farPt C a σ`.

* `shoot_off_dom`: the points of `e` off the domain are `a` and `w`;
* `attach_of_origin`, `attach_of_far`: the arrival positions of `a` (direction `-σ`) and of `w`
  (direction `σ`) are attachments of `e`;
* `attach_cases`: every attachment of `e` is one of them;
* `lend_shoot`, `rend_shoot`: the ends of `e`;
* `aug_eq_of_lend`, `aug_eq_of_rend`: two augmented chords with the same left (right) end are
  equal (the dedupe of the stop list).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace SweepStop

open Sweep

variable {C : Chain}

/-- **The far end of the chord seen from `a`** in the direction `σ`. -/
noncomputable def farPt (C : Chain) (a : Point) (σ : ℝ) : Point := rayPt a σ (C.hitParam a σ)

theorem dirOf_cases' (v : ℕ) : dirOf v = 1 ∨ dirOf v = -1 := by
  unfold dirOf; split_ifs <;> simp

theorem neg_cases {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : -σ = 1 ∨ -σ = -1 := by
  rcases hσ with rfl | rfl <;> norm_num

/-- The points of the ray up to the first hit lie on the chord. -/
theorem rayPt_mem_shoot (C : Chain) (a : Point) (σ : ℝ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ C.hitParam a σ) : rayPt a σ s ∈ Merge.shoot C a σ := by
  unfold Merge.shoot
  Ξ Geometry.mem_segment_iff_lerp
  rcases hs0.lt_or_eq with hs0 | rfl
  · have hT : 0 < C.hitParam a σ := lt_of_lt_of_le hs0 hs
    refine ⟨s / C.hitParam a σ, div_nonneg hs0.le hT.le, (div_le_one hT).2 hs, ?_⟩
    apply Geometry.point_ext
    · simp only [Geometry.lerp_fst, rayPt_fst]; field_simp; ring
    · simp only [Geometry.lerp_snd, rayPt_snd]; ring
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    Ξ Geometry.lerp_zero
    apply Geometry.point_ext <;> simp [rayPt]

/-- The chord seen from `a` is the segment of the ray points up to the first hit. -/
theorem mem_shoot_iff (C : Chain) (a : Point) {σ : ℝ} (_hσ : σ = 1 ∨ σ = -1)
    (hT : 0 ≤ C.hitParam a σ) {x : Point} :
    x ∈ Merge.shoot C a σ ↔ ∃ s, 0 ≤ s ∧ s ≤ C.hitParam a σ ∧ x = rayPt a σ s := by
  constructor
  · intro hx
    unfold Merge.shoot at hx
    obtain ⟨u, hu0, hu1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
    refine ⟨u * C.hitParam a σ, mul_nonneg hu0 hT, ⊞, ?_⟩
    apply Geometry.point_ext
    · simp only [Geometry.lerp_fst, rayPt_fst]; ring
    · simp only [Geometry.lerp_snd, rayPt_snd]; ring
  · rintro ⟨s, hs0, hs, rfl⟩
    exact rayPt_mem_shoot C a σ hs0 hs

/-- **The points of the chord off the domain** are its two ends. -/
theorem shoot_off_dom (C : Chain) {a : Point} (ha : a.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hf : FreeAt C a σ) {x : Point} (hx : x ∈ Merge.shoot C a σ)
    (hxD : x ∉ C.dom) : x = a ∨ x = farPt C a σ := by
  obtain ⟨hT, -, hin⟩ := Merge.hit_of_freeAt C ha hσ hf
  obtain ⟨s, hs0, hs, rfl⟩ := (mem_shoot_iff C a hσ hT.le).1 hx
  rcases hs0.lt_or_eq with hs0 | rfl
  · rcases hs.lt_or_eq with hs | rfl
    · exact absurd (hin s hs0 hs) hxD
    · right; rfl
  · left; apply Geometry.point_ext <;> simp [rayPt]

/-- **The sector of an attachment** contains the direction of the chord from the position's point. -/
theorem sideLeft_of_attach {W : Polygon} {e : Set Point} {p : ℕ} {t : ℝ}
    (hA : SideAttach W e p t) {δ : ℝ} (hδ : δ = 1 ∨ δ = -1) {ε : ℝ} (hε : 0 < ε)
    (hin : ∀ s, 0 < s → s < ε → rayPt (sidePt W p t) δ s ∈ e) :
    sideLeft W p t (rayPt (sidePt W p t) δ 1) := by
  obtain ⟨-, -, -, -, r, hr, hsec⟩ := hA
  set s := min (r / 2) (ε / 2) with hsdef
  have hs : 0 < s := lt_min (half_pos hr) (half_pos hε)
  have hsr : s ≤ r / 2 := min_le_left _ _
  have hsε : s ≤ ε / 2 := min_le_right _ _
  have hd : dist (rayPt (sidePt W p t) δ s) (sidePt W p t) = s :=
    Sweep.dist_rayPt _ hδ hs.le
  have hne : rayPt (sidePt W p t) δ s ≠ sidePt W p t := by
    intro h; rw [h, dist_self] at hd; linarith
  have hsl := hsec _ (hin s hs (⟡)) hne (by rw [hd]; linarith)
  exact (Sweep.sideLeft_rayPt_iff W p t δ one_pos hs).2 hsl

variable (hP : C.P.Simple)
include hP

/-- **The arrival position of the origin** (direction `-σ`) is an attachment of the chord. -/
theorem attach_of_origin {a : Point} (ha : a.2 ≤ C.top.2) (haD : a ∉ C.dom) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hf : FreeAt C a σ) {p : ℕ} {t : ℝ}
    (hA : Arrival (chainModel C).W a (-σ) p t) : SideAttach (chainModel C).W (Merge.shoot C a σ) p t := by
  obtain ⟨hp, ht0, ht1, hpt, hsec⟩ := hA
  rw [neg_neg] at hsec
  have he := Merge.shoot_mem_augChords C ha haD hσ hf
  obtain ⟨hT, -, -⟩ := Merge.hit_of_freeAt C ha hσ hf
  refine sideAttach_of_along C hP he hp ht0 ht1 hσ (by rw [hpt]; exact hsec) ?_
  Ξ hpt
  filter_upwards [Ioo_mem_nhdsGT hT] with s hs
  exact rayPt_mem_shoot C a σ hs.1.le hs.2.le

/-- **The arrival position of the far end** (direction `σ`) is an attachment of the chord. -/
theorem attach_of_far {a : Point} (ha : a.2 ≤ C.top.2) (haD : a ∉ C.dom) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hf : FreeAt C a σ) {p : ℕ} {t : ℝ}
    (hA : Arrival (chainModel C).W (farPt C a σ) σ p t) :
    SideAttach (chainModel C).W (Merge.shoot C a σ) p t := by
  obtain ⟨hp, ht0, ht1, hpt, hsec⟩ := hA
  have he := Merge.shoot_mem_augChords C ha haD hσ hf
  obtain ⟨hT, -, -⟩ := Merge.hit_of_freeAt C ha hσ hf
  refine sideAttach_of_along C hP he hp ht0 ht1 (neg_cases hσ) (by rw [hpt]; exact hsec) ?_
  Ξ hpt
  filter_upwards [Ioo_mem_nhdsGT hT] with s hs
  unfold farPt
  Ξ Sweep.rayPt_back
  exact rayPt_mem_shoot C a σ (by linarith [hs.2]) (by linarith [hs.1])

/-- **Every attachment of the chord** is the arrival position of its origin or of its far end. -/
theorem attach_cases {a : Point} (ha : a.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hf : FreeAt C a σ) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel C).W (Merge.shoot C a σ) p t) :
    (sidePt (chainModel C).W p t = a ∧ Arrival (chainModel C).W a (-σ) p t) ∨
      (sidePt (chainModel C).W p t = farPt C a σ ∧
        Arrival (chainModel C).W (farPt C a σ) σ p t) := by
  have hM : WalkAx (chainModel C) := FactsChain.walkAx C hP
  obtain ⟨hT, -, -⟩ := Merge.hit_of_freeAt C ha hσ hf
  have hxD : sidePt (chainModel C).W p t ∉ C.dom := hM.trace p hA.1 t hA.2.1 hA.2.2.1.le
  rcases shoot_off_dom C ha hσ hf hA.2.2.2.1 hxD with h | h
  · refine Or.inl ⟨h, hA.1, hA.2.1, hA.2.2.1, h, ?_⟩
    Ξ neg_neg
    have := sideLeft_of_attach hA hσ hT (fun s hs0 hs => by
      rw [h]; exact rayPt_mem_shoot C a σ hs0.le hs.le)
    rwa [h] at this
  · refine Or.inr ⟨h, hA.1, hA.2.1, hA.2.2.1, h, ?_⟩
    have := sideLeft_of_attach hA (neg_cases hσ) hT (fun s hs0 hs => by
      rw [h]; unfold farPt; rw [Sweep.rayPt_back]
      exact rayPt_mem_shoot C a σ (⟡) (by linarith))
    rwa [h] at this

omit hP in
/-- The ends of the chord seen in the direction `1`. -/
theorem ends_shoot_pos (C : Chain) {a : Point} (hT : 0 ≤ C.hitParam a 1) :
    Merge.lend (Merge.shoot C a 1) = a ∧ Merge.rend (Merge.shoot C a 1) = farPt C a 1 := by
  unfold Merge.shoot farPt
  rw [Merge.segment_rayPt_pos a hT, Merge.lend_hseg (⟡), Merge.rend_hseg (by linarith)]
  exact ⟨rfl, by apply Geometry.point_ext <;> simp [rayPt]⟩

omit hP in
/-- The ends of the chord seen in the direction `-1`. -/
theorem ends_shoot_neg (C : Chain) {a : Point} (hT : 0 ≤ C.hitParam a (-1)) :
    Merge.lend (Merge.shoot C a (-1)) = farPt C a (-1) ∧ Merge.rend (Merge.shoot C a (-1)) = a := by
  unfold Merge.shoot farPt
  rw [Merge.segment_rayPt_neg a hT, Merge.lend_hseg (⟡), Merge.rend_hseg (by linarith)]
  refine ⟨by apply Geometry.point_ext <;> simp [rayPt, sub_eq_add_neg], rfl⟩

omit hP in
/-- **Two augmented chords with the same left end are equal.** -/
theorem aug_eq_of_lend {c c' : Set Point} (hc : c ∈ Merge.augChords C)
    (hc' : c' ∈ Merge.augChords C) (h : Merge.lend c = Merge.lend c') : c = c' := by
  obtain ⟨y, a, b, hH, -, rfl, hl, -⟩ := Merge.augChords_spec hc
  obtain ⟨y', a', b', hH', -, rfl, hl', -⟩ := Merge.augChords_spec hc'
  rw [hl, hl'] at h
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h
  rcases lt_trichotomy b b' with hb | rfl | hb
  · exact absurd (hH'.open_mem b hH.lt hb) hH.right_not
  · rfl
  · exact absurd (hH.open_mem b' hH'.lt hb) hH'.right_not

omit hP in
/-- **Two augmented chords with the same right end are equal.** -/
theorem aug_eq_of_rend {c c' : Set Point} (hc : c ∈ Merge.augChords C)
    (hc' : c' ∈ Merge.augChords C) (h : Merge.rend c = Merge.rend c') : c = c' := by
  obtain ⟨y, a, b, hH, -, rfl, -, hr⟩ := Merge.augChords_spec hc
  obtain ⟨y', a', b', hH', -, rfl, -, hr'⟩ := Merge.augChords_spec hc'
  rw [hr, hr'] at h
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h
  rcases lt_trichotomy a a' with ha | rfl | ha
  · exact absurd (hH.open_mem a' ha hH'.lt) hH'.left_not
  · rfl
  · exact absurd (hH'.open_mem a ha hH.lt) hH.left_not

omit hP in
/-- The ends of an augmented chord are distinct. -/
theorem lend_ne_rend {c : Set Point} (hc : c ∈ Merge.augChords C) : Merge.lend c ≠ Merge.rend c := by
  obtain ⟨y, a, b, hH, -, rfl, hl, hr⟩ := Merge.augChords_spec hc
  Ξ hl, hr
  intro h
  have := congrArg Prod.fst h
  simp only at this
  linarith [hH.lt]

end SweepStop

end

end Chazelle.Core
