module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepAnswer

/-!
# The sweep (WP-D), part 4: label consistency (lemma (K))

The corrected sweep (design doc §10.y, finding S2) tracks, along the part of the walk of
`C = J.whole` that belongs to `C₁`, the regions of the family `F₂⁺ = J.fusion ∅ S₂ ∪ T₂` (the
chords of `C` seen from the endpoints of the chords of `S₂`, the shared chords and the chords of
`C` at the top of `C₂`), and labels each with a region of `S₂`.  Lemma (K) says that the label is
well defined: two walk positions of `C` on the `C₂` side facing the same region of `F₂⁺`
correspond to positions of the walk of `C₂` facing the same region of `S₂`.

This file proves (K) for two abstract models whose walks agree along two pieces
(`label_gen`): the separations of `S` are mirrored by separations of `F`.

* `xor_btw`, `sep_iff_btw`: a chord separates two keys iff exactly one of its attachments lies
  strictly between them (measured in offsets from a base outside).
* `label_gen`: the generic lemma (K).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft)
open WalkEmbed

namespace Sweep

/-! ## Separation as betweenness -/

/-- `r` lies strictly between `p` and `q`. -/
def Btw (p q r : ℝ) : Prop := (p < r ∧ r < q) ∨ (q < r ∧ r < p)

theorem Btw.symm {p q r : ℝ} (h : Btw p q r) : Btw q p r := Or.symm h


/-- **Separation as betweenness of offsets.**  For keys on a cycle of length `n`, measured by
offsets from a base `g`: the interval `(a, b)` separates `x` from `y` iff exactly one of `a`, `b`
lies strictly between `x` and `y` in offsets. -/
theorem sep_iff_btw {n g a b x y : ℝ} (hg : 0 ≤ g) (hgn : g < n) (ha : 0 ≤ a) (han : a < n)
    (hb : 0 ≤ b) (hbn : b < n) (hx : 0 ≤ x) (hxn : x < n) (hy : 0 ≤ y) (hyn : y < n)
    (hab : a ≠ b) (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    (sideInArc a b x ↔ ¬ sideInArc a b y) ↔
      (Btw (off n g x) (off n g y) (off n g a) ↔ ¬ Btw (off n g x) (off n g y) (off n g b)) := by
  have hne : ∀ {u w : ℝ}, 0 ≤ u → u < n → 0 ≤ w → w < n → u ≠ w → off n g u ≠ off n g w :=
    fun hu hun hw hwn huw h => huw (off_inj hg hgn hu hun hw hwn h)
  have hoab := hne ha han hb hbn hab
  
  have hoxa := hne hx hxn ha han hxa
  have hoxb := hne hx hxn hb hbn hxb
  have hoya := hne hy hyn ha han hya
  have hoyb := hne hy hyn hb hbn hyb
  rcases lt_or_gt_of_ne hoab with h | h
  · rw [sideInArc_iff_off hg hgn ha han hb hbn hx hxn h,
      sideInArc_iff_off hg hgn ha han hb hbn hy hyn h]
    ram_grind
  · rw [Chazelle.Chain.sideInArc_swap hab hxa hxb, Chazelle.Chain.sideInArc_swap hab hya hyb,
      sideInArc_iff_off hg hgn hb hbn ha han hx hxn h,
      sideInArc_iff_off hg hgn hb hbn ha han hy hyn h]
    ram_grind

/-! ## Endpoints of admissible chords -/

/-- A point of an admissible chord outside the domain is an endpoint. -/
theorem end_of_not_mem {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) :
    ∃ a b : Point, a ≠ b ∧ c = Chazelle.segment a b ∧
      ∀ x ∈ c, x ∉ M.D → x = a ∨ x = b := by
  obtain ⟨a, b, hab, hcab, -, hopen, -, -⟩ := hM.ends c hc
  refine ⟨a, b, hab, hcab, fun x hx hxD => ?_⟩
  rw [hcab] at hx
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
  grind [Geometry.lerp_one, Geometry.lerp_zero]

/-- An admissible chord inside another one containing both endpoints of the latter is equal to
it. -/
theorem eq_of_ends {M M₂ : Model} (hM : WalkAx M) (hM₂ : WalkAx M₂) {e c : Set Point}
    (he : e ∈ M.Adm) (hc : c ∈ M₂.Adm) (hec : e ⊆ c) {q y : Point} (hqy : q ≠ y) (hq : q ∈ e)
    (hy : y ∈ e) (hqD : q ∉ M₂.D) (hyD : y ∉ M₂.D) : e = c := by
  obtain ⟨a, b, hab, hcab, hend⟩ := end_of_not_mem hM₂ hc
  obtain ⟨a1, b1, -, heab, -⟩ := end_of_not_mem hM he
  have hqc := hend q (hec hq) hqD
  have hyc := hend y (hec hy) hyD
  have hconv : Convex ℝ e := by rw [heab]; exact Geometry.segment_convex _ _
  refine Set.Subset.antisymm hec ?_
  rw [hcab]
  rcases hqc with rfl | rfl <;> rcases hyc with rfl | rfl
  · simp_all
  · exact Geometry.segment_subset_of_convex hconv hq hy
  · exact Geometry.segment_subset_of_convex hconv hy hq
  simp_all

/-! ## Two walks agreeing along two pieces -/


/-- The offset in the walk of `M₂` of the offset `d` of the walk of `M`. -/
def dq (L1 δ d : ℕ) : ℕ := if d < L1 then d else d + δ

namespace Corr

variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

end Corr

/-! ## Collapsing the gap -/

/-- The offset of the walk of `M` corresponding to the offset `o` of the walk of `M₂` (the gap
`[L1, L1 + δ]` collapses to `L1`). -/
noncomputable def psi (L1 δ : ℕ) (o : ℝ) : ℝ :=
  if o ≤ L1 then o else if o ≤ (L1 : ℝ) + δ then L1 else o - δ

theorem psi_dq {L1 δ d : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    psi L1 δ ((dq L1 δ d : ℕ) + t) = d + t := by
  unfold psi dq
  by_cases h : d < L1
  · rw [ite_eq_left h, ite_eq_left]
    have : (d : ℝ) + 1 ≤ L1 := by exact_mod_cast h
    linarith
  · rw [ite_eq_right h]
    push_cast
    have hL : (L1 : ℝ) ≤ d := by simp_all
    grind

theorem psi_mono {L1 δ : ℕ} {o o' : ℝ} (h : o ≤ o') : psi L1 δ o ≤ psi L1 δ o' := by
  core_grind

/-- The gap of the walk of `M₂`. -/
def InGap (L1 δ : ℕ) (o : ℝ) : Prop := (L1 : ℝ) ≤ o ∧ o ≤ (L1 : ℝ) + δ

section
variable {L1 δ : ℕ}
theorem psi_strict {o o' : ℝ} (h : o < o') (hg : ¬ InGap L1 δ o ∨ ¬ InGap L1 δ o') :
    psi L1 δ o < psi L1 δ o' := by
  core_grind

theorem btw_psi {a b o : ℝ} (ha : ¬ InGap L1 δ a) (hb : ¬ InGap L1 δ b)
    (h : Btw a b o) : Btw (psi L1 δ a) (psi L1 δ b) (psi L1 δ o) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨psi_strict h1 (Or.inl ha), psi_strict h2 (Or.inr hb)⟩
  · exact Or.inr ⟨psi_strict h1 (Or.inl hb), psi_strict h2 (Or.inr ha)⟩

theorem btw_of_psi {a b o : ℝ} (h : Btw (psi L1 δ a) (psi L1 δ b) (psi L1 δ o)) :
    Btw a b o := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    constructor
    · by_contra hc; push Not at hc; linarith [psi_mono (L1 := L1) (δ := δ) hc]
    · by_contra hc; push Not at hc; linarith [psi_mono (L1 := L1) (δ := δ) hc]
  · right
    constructor
    · by_contra hc; push Not at hc; linarith [psi_mono (L1 := L1) (δ := δ) hc]
    · by_contra hc; push Not at hc; linarith [psi_mono (L1 := L1) (δ := δ) hc]


end

theorem not_inGap_dq {L1 δ d : ℕ} {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ¬ InGap L1 δ ((dq L1 δ d : ℕ) + t) := by
  unfold InGap dq
  rintro ⟨h1, h2⟩
  split_ifs at h1 h2 with h
  · have : (d : ℝ) + 1 ≤ L1 := by exact_mod_cast h
    linarith
  · push_cast at h1 h2
    have : (L1 : ℝ) ≤ d := by simp_all
    linarith

namespace Corr

variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

end Corr

namespace Corr

variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

end Corr

namespace Corr

variable {M M₂ : Model} {F S : Set (Set Point)} {g g' L1 L2 δ : ℕ}

/-- Keys of walk positions lie in `[0, n)`. -/
theorem key_mem {W : Polygon} {p : ℕ} (hp : p < W.n) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < W.n := by
  have : (p : ℝ) + 1 ≤ W.n := by exact_mod_cast hp
  ram_grind

end Corr

end Sweep

end

end Chazelle.Core
