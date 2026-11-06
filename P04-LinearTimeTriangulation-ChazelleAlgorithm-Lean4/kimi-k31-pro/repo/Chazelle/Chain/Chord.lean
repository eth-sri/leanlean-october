module

public import Chazelle.Chain.Basic

/-!
# Vertex chords of the subchain visibility model

At a chain vertex `v = C.vertex k` (`k ≤ m`) and for a horizontal direction `σ ∈ {1, -1}`, the
points `rayPt v σ t` for small `t > 0` are

* all in the domain `dom C` (`DirFree C k σ`, the direction is *free*), or
* all on the chain (`DirChain C k σ`: an incident chain edge is horizontal and leaves `v` in
  direction `σ`),

and exactly one of the two holds (`dirFree_or_dirChain`, `dirFree_not_dirChain`).  There is no
third case: the domain is the whole complement of the chain inside the box (minus the slit, which
is never met near a chain vertex).

When `DirFree C k σ` holds, the **chord** of `v` in direction `σ` is the closed horizontal segment
from `v` to the first point `chordEnd C k σ` of `(dom C)ᶜ` on the open ray
(`chordParam C k σ = hitParam C v σ`).  The hit always exists because the ray leaves the box
(`hitSet_nonempty`), so no parity argument is needed.

* `chord_spec`: `0 < chordParam`, `chordEnd ∉ dom C`, the open chord is in `dom C`;
* `chordEnd_cases`: the far endpoint is on the chain (**finite chord**) or on the vertical side
  `x = σ R` of the box (**box chord**); it is never on the open slit;
* `hchordIn_inter` / `chordSet_inter`: two chords are equal or meet only in endpoints of both;
* `chords_ncard_le`: there are at most `2 (m + 1)` chords.

The abstract notion is `IsHChordIn D y a b`: a horizontal segment `[a, b] × {y}` with endpoints
off `D` and open part inside `D`; for `D = P.filled \ P.boundary` it is
`Chazelle.Visibility.IsHChord`.
-/

namespace Chazelle

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd rayPt_zero continuous_rayPt rayPt_injective
  hseg segment_horizontal_eq_hseg)

namespace Chain

variable (C : Chain)

/-! ### The two local possibilities at a chain vertex -/

/-- The points just after `vertex k` in direction `σ` are in the domain. -/
def DirFree (k : ℕ) (σ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt (C.vertex k) σ t ∈ C.dom

/-! ### Horizontal rays and their first hit of the obstacle -/

/-- The parameters `t > 0` at which the ray from `v` in direction `σ` meets the complement of
the domain. -/
def hitSet (v : Point) (σ : ℝ) : Set ℝ := {t : ℝ | 0 < t ∧ rayPt v σ t ∈ C.domᶜ}

/-- The parameter of the first point of the open ray outside the domain. -/
noncomputable def hitParam (v : Point) (σ : ℝ) : ℝ := sInf (C.hitSet v σ)

theorem hitSet_bddBelow (v : Point) (σ : ℝ) : BddBelow (C.hitSet v σ) :=
  ⟨0, fun _ ht => ht.1.le⟩

/-- The ray from a point of the box leaves the box: the hit set is nonempty. -/
theorem hitSet_nonempty {v : Point} (hv : v ∈ box C.radius) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    (C.hitSet v σ).Nonempty := by
  refine ⟨C.radius - σ * v.1, ?_, ?_⟩
  · have := abs_lt.1 hv.1
    rcases hσ with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;> linarith
  · intro hmem
    have hbox := hmem.1
    have hx := hbox.1
    simp only [rayPt_fst] at hx
    have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have : v.1 + σ * (C.radius - σ * v.1) = σ * C.radius := by linear_combination (-v.1) * hσ2
    rw [this, abs_mul] at hx
    have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
    rw [hσ1, one_mul, abs_of_pos C.radius_pos] at hx
    exact lt_irrefl _ hx

/-- **The first hit.**  If an initial open stretch `(0, t₀)` of the ray from a point of the box
is in the domain, then the first-hit parameter is at least `t₀`, the first-hit point is outside
the domain, and every point of the ray strictly before it is in the domain. -/
theorem hit_of_initial {v : Point} (hv : v ∈ box C.radius) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hint : ∀ t, 0 < t → t < t₀ → rayPt v σ t ∈ C.dom) :
    t₀ ≤ C.hitParam v σ ∧ rayPt v σ (C.hitParam v σ) ∈ C.domᶜ ∧
      ∀ t, 0 < t → t < C.hitParam v σ → rayPt v σ t ∈ C.dom := by
  have hne := C.hitSet_nonempty hv hσ
  have hge : ∀ t ∈ C.hitSet v σ, t₀ ≤ t := by
    intro t ht
    by_contra h
    exact ht.2 (hint t ht.1 (not_le.1 h))
  have h1 : t₀ ≤ C.hitParam v σ := le_csInf hne hge
  have hset : C.hitSet v σ = {t : ℝ | t₀ ≤ t ∧ rayPt v σ t ∈ C.domᶜ} := by
    ext t
    constructor
    · intro ht; exact ⟨hge t ht, ht.2⟩
    · intro ht; exact ⟨lt_of_lt_of_le ht₀ ht.1, ht.2⟩
  have hclosed : IsClosed (C.hitSet v σ) := by
    rw [hset]
    exact isClosed_Ici.inter (C.isClosed_dom_compl.preimage (continuous_rayPt v σ))
  have h2 : rayPt v σ (C.hitParam v σ) ∈ C.domᶜ :=
    (hclosed.csInf_mem hne (C.hitSet_bddBelow v σ)).2
  refine ⟨h1, h2, fun t ht1 ht2 => ?_⟩
  by_contra hmem
  have : t ∈ C.hitSet v σ := ⟨ht1, hmem⟩
  exact absurd (csInf_le (C.hitSet_bddBelow v σ) this) (not_le.2 ht2)

/-- Every point of the open ray outside the domain is at or after the first hit. -/
theorem hitParam_le_of_not_mem_dom (v : Point) (σ : ℝ) {t : ℝ} (ht : 0 < t)
    (hmem : rayPt v σ t ∉ C.dom) : C.hitParam v σ ≤ t :=
  csInf_le (C.hitSet_bddBelow v σ) ⟨ht, hmem⟩

/-- **Uniqueness of the first hit.** -/
theorem hitParam_eq_of_first (v : Point) (σ : ℝ) {t : ℝ} (ht : 0 < t)
    (hmem : rayPt v σ t ∉ C.dom) (hfirst : ∀ s, 0 < s → s < t → rayPt v σ s ∈ C.dom) :
    C.hitParam v σ = t := by
  refine le_antisymm (C.hitParam_le_of_not_mem_dom v σ ht hmem) (le_csInf ⟨t, ht, hmem⟩ ?_)
  intro s hs
  by_contra h
  exact hs.2 (hfirst s hs.1 (not_le.1 h))

/-! ### The chord -/

/-- The parameter of the far endpoint of the chord of vertex `k` in direction `σ`. -/
noncomputable def chordParam (k : ℕ) (σ : ℝ) : ℝ := C.hitParam (C.vertex k) σ

/-- The far endpoint of the chord of vertex `k` in direction `σ`. -/
noncomputable def chordEnd (k : ℕ) (σ : ℝ) : Point := rayPt (C.vertex k) σ (C.chordParam k σ)

/-- The closed chord of vertex `k` in direction `σ`. -/
noncomputable def chordSet (k : ℕ) (σ : ℝ) : Set Point :=
  Chazelle.segment (C.vertex k) (C.chordEnd k σ)

/-- The open chord: the chord without its two endpoints. -/
noncomputable def openChordSet (k : ℕ) (σ : ℝ) : Set Point :=
  rayPt (C.vertex k) σ '' Ioo 0 (C.chordParam k σ)

@[simp] theorem chordEnd_fst (k : ℕ) (σ : ℝ) :
    (C.chordEnd k σ).1 = (C.vertex k).1 + σ * C.chordParam k σ := rfl

@[simp] theorem chordEnd_snd (k : ℕ) (σ : ℝ) : (C.chordEnd k σ).2 = (C.vertex k).2 := rfl

/-- **The chord exists.**  When direction `σ` at vertex `k` is free: the chord parameter is
positive, the far endpoint is outside the domain, and every point of the open chord is in the
domain. -/
theorem chord_spec {k : ℕ} (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : C.DirFree k σ) :
    0 < C.chordParam k σ ∧ C.chordEnd k σ ∈ C.domᶜ ∧
      ∀ t, 0 < t → t < C.chordParam k σ → rayPt (C.vertex k) σ t ∈ C.dom := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  rw [mem_Ioi] at hu
  obtain ⟨h1, h2, h3⟩ := C.hit_of_initial (C.set_subset_box (C.vertex_mem_set hk)) hσ hu
    (fun t ht1 ht2 => hsub ⟨ht1, ht2⟩)
  exact ⟨lt_of_lt_of_le hu h1, h2, h3⟩

theorem chordParam_pos {k : ℕ} (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) : 0 < C.chordParam k σ :=
  (C.chord_spec hk hσ h).1

theorem chordEnd_not_mem_dom {k : ℕ} (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) : C.chordEnd k σ ∉ C.dom :=
  (C.chord_spec hk hσ h).2.1

/-- The open chord is in the domain. -/
theorem openChordSet_subset_dom {k : ℕ} (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) : C.openChordSet k σ ⊆ C.dom := by
  rintro _ ⟨t, ht, rfl⟩
  exact (C.chord_spec hk hσ h).2.2 t ht.1 ht.2

/-- The far endpoint is not the vertex. -/
theorem chordEnd_ne_vertex {k : ℕ} (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) : C.chordEnd k σ ≠ C.vertex k := by
  intro heq
  have := congrArg Prod.fst heq
  simp only [chordEnd_fst] at this
  have hpos := C.chordParam_pos hk hσ h
  have : σ * C.chordParam k σ = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · rcases hσ with rfl | rfl <;> norm_num at h'
  · exact hpos.ne' h'

/-- The far endpoint of a chord, when outside the box, is on the vertical side `x = σ R`. -/
theorem chordEnd_fst_eq_of_not_mem_box {k : ℕ} (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) (hbox : C.chordEnd k σ ∉ box C.radius) :
    (C.chordEnd k σ).1 = σ * C.radius := by
  obtain ⟨hpos, -, hint⟩ := C.chord_spec hk hσ h
  have hv := C.set_subset_box (C.vertex_mem_set hk)
  have hv1 := abs_lt.1 hv.1
  have hv2 := hv.2
  -- the far endpoint has `|x| ≤ R`: otherwise a slightly earlier ray point would be outside
  have hle : |(C.chordEnd k σ).1| ≤ C.radius := by
    by_contra hgt
    push Not at hgt
    set T := C.chordParam k σ with hT
    -- `t := (T + R - σ v.1)/2 ∈ (0, T)` has `|x| > R`
    have hcase : ∀ s, 0 < s → s < T → |(C.vertex k).1 + σ * s| < C.radius := by
      intro s hs1 hs2
      exact (hint s hs1 hs2).1.1
    rcases hσ with rfl | rfl
    · simp only [chordEnd_fst, one_mul] at hgt
      have hgt' : C.radius < (C.vertex k).1 + T := by
        rcases lt_abs.1 hgt with h | h
        · exact h
        · linarith
      have := hcase ((T + C.radius - (C.vertex k).1) / 2) (by linarith) (by linarith)
      rw [one_mul, abs_lt] at this
      linarith [this.2]
    · simp only [chordEnd_fst, neg_one_mul] at hgt
      have hgt' : C.radius < -((C.vertex k).1 + -T) := by
        rcases lt_abs.1 hgt with h | h
        · linarith
        · exact h
      have := hcase ((T + C.radius + (C.vertex k).1) / 2) (by linarith) (by linarith)
      rw [neg_one_mul, abs_lt] at this
      linarith [this.1]
  have hnot : ¬ |(C.chordEnd k σ).1| < C.radius := fun hlt => hbox ⟨hlt, by
    rw [chordEnd_snd]; exact hv2⟩
  have habs : |(C.chordEnd k σ).1| = C.radius := le_antisymm hle (not_lt.1 hnot)
  rcases hσ with rfl | rfl
  · simp only [chordEnd_fst, one_mul] at habs ⊢
    rcases abs_eq (C.radius_pos.le) |>.1 habs with h | h
    · exact h
    · linarith
  · simp only [chordEnd_fst, neg_one_mul] at habs ⊢
    rcases abs_eq (C.radius_pos.le) |>.1 habs with h | h
    · linarith
    · linarith

/-- **The two kinds of chord.**  The far endpoint lies on the chain (finite chord) or on the
vertical side `x = σ R` of the box (box chord).  In particular it is never on the open slit. -/
theorem chordEnd_cases {k : ℕ} (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) :
    C.chordEnd k σ ∈ C.set ∨ (C.chordEnd k σ).1 = σ * C.radius := by
  have hnd := C.chordEnd_not_mem_dom hk hσ h
  rw [mem_dom_iff] at hnd
  by_cases hbox : C.chordEnd k σ ∈ box C.radius
  · have hnd' : C.chordEnd k σ ∈ C.set ∨ C.chordEnd k σ ∈ C.slit := by
      by_contra hcon
      push Not at hcon
      exact hnd ⟨hbox, hcon.1, hcon.2⟩
    rcases hnd' with hset | hslit
    · exact Or.inl hset
    · -- on the slit at the height of a chain vertex: it is the top vertex
      left
      obtain ⟨h1, h2, -⟩ := C.mem_slit_iff.1 hslit
      have h3 : (C.chordEnd k σ).2 ≤ C.top.2 := by
        rw [chordEnd_snd]; exact C.snd_le_top_of_mem_set (C.vertex_mem_set hk)
      have : C.chordEnd k σ = C.top := Prod.ext h1 (le_antisymm h3 h2)
      rw [this]; exact C.top_mem_set
  · exact Or.inr (C.chordEnd_fst_eq_of_not_mem_box hk hσ h hbox)

/-- The chord as the image of the closed parameter interval. -/
theorem chordSet_eq_image {k : ℕ} (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) :
    C.chordSet k σ = rayPt (C.vertex k) σ '' Icc 0 (C.chordParam k σ) := by
  have hpos := C.chordParam_pos hk hσ h
  ext p
  unfold chordSet Chazelle.segment
  simp only [mem_ofPred_eq, mem_image, mem_Icc, chordEnd_fst, chordEnd_snd]
  constructor
  · rintro ⟨t, ht0, ht1, rfl⟩
    refine ⟨t * C.chordParam k σ, ⟨mul_nonneg ht0 hpos.le, ?_⟩, ?_⟩
    · nlinarith
    · rw [Geometry.point_ext_iff]; simp only [rayPt_fst, rayPt_snd]; constructor <;> ring
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
    refine ⟨s / C.chordParam k σ, div_nonneg hs0 hpos.le, (div_le_one hpos).2 hs1, ?_⟩
    rw [Geometry.point_ext_iff]; simp only [rayPt_fst, rayPt_snd]
    constructor
    · field_simp
      ring
    · ring

/-- The closed chord is the open chord with its two endpoints. -/
theorem chordSet_eq_openChordSet_union {k : ℕ} (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) :
    C.chordSet k σ = C.openChordSet k σ ∪ {C.vertex k, C.chordEnd k σ} := by
  rw [chordSet_eq_image C hk hσ h]
  ext p
  simp only [openChordSet, mem_union, mem_image, mem_Icc, mem_Ioo, mem_insert_iff,
    mem_singleton_iff]
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    rcases ht0.lt_or_eq with h0 | h0
    · rcases ht1.lt_or_eq with h1 | h1
      · exact Or.inl ⟨t, ⟨h0, h1⟩, rfl⟩
      · right; right; rw [h1]; rfl
    · right; left; rw [← h0, rayPt_zero]
  · rintro (⟨t, ht, rfl⟩ | rfl | rfl)
    · exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
    · exact ⟨0, ⟨le_rfl, (C.chordParam_pos hk hσ h).le⟩, rayPt_zero _ _⟩
    · exact ⟨C.chordParam k σ, ⟨(C.chordParam_pos hk hσ h).le, le_rfl⟩, rfl⟩

/-! ### Abstract horizontal chords of a domain -/

/-- A horizontal chord of the domain `D`: a horizontal segment `[a, b] × {y}` with `a < b`,
both endpoints off `D`, and the open part inside `D`. -/
structure IsHChordIn (D : Set Point) (y a b : ℝ) : Prop where
  lt : a < b
  left_not : ((a, y) : Point) ∉ D
  right_not : ((b, y) : Point) ∉ D
  open_mem : ∀ x, a < x → x < b → ((x, y) : Point) ∈ D

/-- **Two horizontal chords of a domain are equal or meet only in common endpoints.** -/
theorem hchordIn_inter {D : Set Point} {y a b y' a' b' : ℝ} (h : IsHChordIn D y a b)
    (h' : IsHChordIn D y' a' b') {p : Point} (hp : p ∈ hseg y a b) (hp' : p ∈ hseg y' a' b') :
    (y = y' ∧ a = a' ∧ b = b') ∨
      ((p = (a, y) ∨ p = (b, y)) ∧ (p = (a', y') ∨ p = (b', y'))) := by
  obtain ⟨hpy, hpa, hpb⟩ := hp
  obtain ⟨hpy', hpa', hpb'⟩ := hp'
  have hyy : y = y' := hpy.symm.trans hpy'
  subst hyy
  by_cases hend : p.1 = a ∨ p.1 = b
  · have hpD : p ∉ D := by
      rcases hend with he | he
      · have : p = (a, y) := Prod.ext he hpy
        rw [this]; exact h.left_not
      · have : p = (b, y) := Prod.ext he hpy
        rw [this]; exact h.right_not
    right
    refine ⟨?_, ?_⟩
    · rcases hend with he | he
      · exact Or.inl (Prod.ext he hpy)
      · exact Or.inr (Prod.ext he hpy)
    · by_contra hne
      push Not at hne
      have ha' : a' < p.1 := lt_of_le_of_ne hpa' (fun e => hne.1 (Prod.ext e.symm hpy))
      have hb' : p.1 < b' := lt_of_le_of_ne hpb' (fun e => hne.2 (Prod.ext e hpy))
      have := h'.open_mem p.1 ha' hb'
      rw [show ((p.1, y) : Point) = p from Prod.ext rfl hpy.symm] at this
      exact hpD this
  · push Not at hend
    have ha : a < p.1 := lt_of_le_of_ne hpa (Ne.symm hend.1)
    have hb : p.1 < b := lt_of_le_of_ne hpb hend.2
    have hint := h.open_mem p.1 ha hb
    rw [show ((p.1, y) : Point) = p from Prod.ext rfl hpy.symm] at hint
    have ha' : a' < p.1 := by
      rcases hpa'.lt_or_eq with h1 | h1
      · exact h1
      · exfalso
        apply h'.left_not
        rw [show p = (a', y) from Prod.ext h1.symm hpy] at hint
        exact hint
    have hb' : p.1 < b' := by
      rcases hpb'.lt_or_eq with h1 | h1
      · exact h1
      · exfalso
        apply h'.right_not
        rw [show p = (b', y) from Prod.ext h1 hpy] at hint
        exact hint
    left
    refine ⟨rfl, ?_, ?_⟩
    · apply le_antisymm
      · by_contra hlt
        push Not at hlt
        exact h.left_not (h'.open_mem a hlt (ha.trans hb'))
      · by_contra hlt
        push Not at hlt
        exact h'.left_not (h.open_mem a' hlt (ha'.trans hb))
    · apply le_antisymm
      · by_contra hlt
        push Not at hlt
        exact h'.right_not (h.open_mem b' (ha.trans hb') hlt)
      · by_contra hlt
        push Not at hlt
        exact h.right_not (h'.open_mem b (ha'.trans hb) hlt)

/-- The chord of a vertex, as a horizontal segment between its two abscissae. -/
theorem chordSet_eq_hseg (k : ℕ) (σ : ℝ) :
    C.chordSet k σ = hseg (C.vertex k).2 (min (C.vertex k).1 (C.chordEnd k σ).1)
      (max (C.vertex k).1 (C.chordEnd k σ).1) :=
  segment_horizontal_eq_hseg (C.chordEnd_snd k σ).symm

/-- **The chord of a vertex is a horizontal chord of the domain.** -/
theorem isHChordIn_chord {k : ℕ} (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) :
    IsHChordIn C.dom (C.vertex k).2 (min (C.vertex k).1 (C.chordEnd k σ).1)
      (max (C.vertex k).1 (C.chordEnd k σ).1) := by
  obtain ⟨hpos, hend, hint⟩ := C.chord_spec hk hσ h
  have hv : ((C.vertex k).1, (C.vertex k).2) = C.vertex k := rfl
  have he : ((C.chordEnd k σ).1, (C.vertex k).2) = C.chordEnd k σ := rfl
  have hvD : C.vertex k ∉ C.dom := fun hd => C.not_mem_set_of_mem_dom hd (C.vertex_mem_set hk)
  rcases hσ with rfl | rfl
  · have hlt : (C.vertex k).1 < (C.chordEnd k 1).1 := by
      simp only [chordEnd_fst, one_mul]; linarith
    rw [min_eq_left hlt.le, max_eq_right hlt.le]
    refine ⟨hlt, hv ▸ hvD, he ▸ hend, fun x hx1 hx2 => ?_⟩
    have := hint (x - (C.vertex k).1) (by linarith)
      (by simp only [chordEnd_fst, one_mul] at hx2; linarith)
    simp only [rayPt, one_mul, add_sub_cancel] at this
    exact this
  · have hlt : (C.chordEnd k (-1)).1 < (C.vertex k).1 := by
      simp only [chordEnd_fst, neg_one_mul]; linarith
    rw [min_eq_right hlt.le, max_eq_left hlt.le]
    refine ⟨hlt, he ▸ hend, hv ▸ hvD, fun x hx1 hx2 => ?_⟩
    have := hint ((C.vertex k).1 - x) (by linarith)
      (by simp only [chordEnd_fst, neg_one_mul] at hx1; linarith)
    simp only [rayPt, neg_one_mul, neg_sub, add_sub_cancel] at this
    exact this

/-! ### The set of all chords -/

/-- The set of all vertex chords of the chain (in free directions). -/
def chords : Set (Set Point) :=
  {S | ∃ k σ, k ≤ C.m ∧ (σ = 1 ∨ σ = -1) ∧ C.DirFree k σ ∧ S = C.chordSet k σ}

theorem chords_subset_image :
    C.chords ⊆ (fun x : ℕ × ℝ => C.chordSet x.1 x.2) ''
      ((↑(Finset.range (C.m + 1)) : Set ℕ) ×ˢ ({1, -1} : Set ℝ)) := by
  rintro S ⟨k, σ, hk, hσ, -, rfl⟩
  refine ⟨(k, σ), ⟨by simp [hk], ?_⟩, rfl⟩
  simp only [mem_insert_iff, mem_singleton_iff]
  exact hσ

theorem chords_finite : C.chords.Finite :=
  ((Finset.range (C.m + 1)).finite_toSet.prod ((finite_singleton (-1 : ℝ)).insert 1)).image _
    |>.subset C.chords_subset_image

/-- Every chord is a horizontal chord of the domain. -/
theorem chords_spec {S : Set Point} (hS : S ∈ C.chords) :
    ∃ k σ, k ≤ C.m ∧ (σ = 1 ∨ σ = -1) ∧ C.DirFree k σ ∧ S = C.chordSet k σ ∧
      IsHChordIn C.dom (C.vertex k).2 (min (C.vertex k).1 (C.chordEnd k σ).1)
        (max (C.vertex k).1 (C.chordEnd k σ).1) := by
  obtain ⟨k, σ, hk, hσ, h, rfl⟩ := hS
  exact ⟨k, σ, hk, hσ, h, rfl, C.isHChordIn_chord hk hσ h⟩

end Chain

end

end Chazelle
