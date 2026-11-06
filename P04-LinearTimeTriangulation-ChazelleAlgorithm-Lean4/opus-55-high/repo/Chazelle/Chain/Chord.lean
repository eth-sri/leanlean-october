module

public import Chazelle.MacT
public import Chazelle.Final.Wedge

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
  ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt ztib σ t ∈ C.dom

/-! ### Horizontal rays and their first hit of the obstacle -/

/-- The parameters `t > 0` at which the ray from `v` in direction `σ` meets the complement of
the domain. -/
def hitSet (v : Point) (σ : ℝ) : Set ℝ := {t : ℝ | 0 < t ∧ rayPt v σ t ∈ C.domᶜ}

/-- The parameter of the first point of the open ray outside the domain. -/
noncomputable def hitParam (v : Point) (σ : ℝ) : ℝ := sInf ztnjv
theorem hitSet_bddBelow (v : Point) (σ : ℝ) : BddBelow ztnjv :=
  ⟨0, fun _ ht => ht.1.le⟩
variable {v : Point} {k : ℕ}
/-- The ray from a point of the box leaves the box: the hit set is nonempty. -/
theorem hitSet_nonempty (hv : v ∈ box C.radius) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    (C.hitSet v σ).Nonempty := by
  refine ⟨C.radius - σ * v.1, ?_, ?_⟩
  · have := abs_lt.1 hv.1
    rcases hσ with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;> linarith
  · zuhgp
    have hbox := hmem.1
    have hx := hbox.1
    zufbx
    grind

/-- **The first hit.**  If an initial open stretch `(0, t₀)` of the ray from a point of the box
is in the domain, then the first-hit parameter is at least `t₀`, the first-hit point is outside
the domain, and every point of the ray strictly before it is in the domain. -/
theorem hit_of_initial (hv : v ∈ box C.radius) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hint : ∀ t, 0 < t → t < t₀ → rayPt v σ t ∈ C.dom) :
    t₀ ≤ C.hitParam v σ ∧ rayPt v σ (C.hitParam v σ) ∈ C.domᶜ ∧
      ∀ t, 0 < t → t < C.hitParam v σ → rayPt v σ t ∈ C.dom := by
  have hne := C.hitSet_nonempty hv hσ
  have hge : ∀ t ∈ C.hitSet v σ, t₀ ≤ t := by
    zucj
    zumv
    exact ht.2 (hint t ht.1 zteue)
  have h1 := le_csInf hne hge
  have hset : C.hitSet v σ = {t : ℝ | t₀ ≤ t ∧ rayPt v σ t ∈ C.domᶜ} := by
    zufso
    constructor
    · zuhgs
    · zuhgr
  have hclosed : IsClosed ztnjv := by
    zucju
    exact isClosed_Ici.inter (C.isClosed_dom_compl.preimage zttig)
  have h2 :=
    (hclosed.csInf_mem hne ztnjw).2
  refine ⟨h1, h2, fun t ht1 ht2 => ?_⟩
  by_contra hmem
  have : t ∈ C.hitSet v σ := by_grind
  exact absurd (csInf_le ztnjw this) ztwah

/-- Every point of the open ray outside the domain is at or after the first hit. -/
theorem hitParam_le_of_not_mem_dom (v : Point) (σ : ℝ) {t : ℝ} (ht : 0 < t)
    (hmem : rayPt v σ t ∉ C.dom) : C.hitParam v σ ≤ t :=
  csInf_le ztnjw ztoor

/-- **Uniqueness of the first hit.** -/
theorem hitParam_eq_of_first (v : Point) (σ : ℝ) {t : ℝ} (ht : 0 < t)
    (hmem : rayPt v σ t ∉ C.dom) (hfirst : ∀ s, 0 < s → s < t → rayPt v σ s ∈ C.dom) :
    C.hitParam v σ = t := by
  refine le_antisymm (C.hitParam_le_of_not_mem_dom v σ ht hmem) ztlqs
  zugg
  zumv
  exact hs.2 (hfirst s hs.1 zteue)

/-! ### The chord -/

/-- The parameter of the far endpoint of the chord of vertex `k` in direction `σ`. -/
noncomputable def chordParam (k : ℕ) (σ : ℝ) : ℝ := C.hitParam ztib σ

/-- The far endpoint of the chord of vertex `k` in direction `σ`. -/
noncomputable def chordEnd (k : ℕ) (σ : ℝ) : Point := rayPt ztib σ ztnju

/-- The closed chord of vertex `k` in direction `σ`. -/
noncomputable def chordSet (k : ℕ) (σ : ℝ) : Set Point :=
  Chazelle.segment ztib (C.chordEnd k σ)

/-- The open chord: the chord without its two endpoints. -/
noncomputable def openChordSet (k : ℕ) (σ : ℝ) : Set Point :=
  rayPt ztib σ '' Ioo 0 ztnju
@[simp] theorem chordEnd_fst (k : ℕ) (σ : ℝ) :
    (C.chordEnd k σ).1 = (C.vertex k).1 + σ * C.chordParam k σ := rfl
@[simp] theorem chordEnd_snd (k : ℕ) (σ : ℝ) : (C.chordEnd k σ).2 = (C.vertex k).2 := rfl

/-- **The chord exists.**  When direction `σ` at vertex `k` is free: the chord parameter is
positive, the far endpoint is outside the domain, and every point of the open chord is in the
domain. -/
theorem chord_spec (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : C.DirFree k σ) :
    0 < C.chordParam k σ ∧ C.chordEnd k σ ∈ C.domᶜ ∧
      ∀ t, 0 < t → t < C.chordParam k σ → rayPt ztib σ t ∈ C.dom := by
  zuvg
  zuduw
  obtain ⟨h1, h2, h3⟩ := C.hit_of_initial ztyhi hσ hu
    ztjwo
  exact ztooy
theorem chordParam_pos (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) : 0 < C.chordParam k σ :=
  (C.chord_spec hk hσ h).1
theorem chordEnd_not_mem_dom (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) : C.chordEnd k σ ∉ C.dom :=
  (C.chord_spec hk hσ h).2.1

/-- The open chord is in the domain. -/
theorem openChordSet_subset_dom (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) : C.openChordSet k σ ⊆ C.dom := by
  zupc
  exact (C.chord_spec hk hσ h).2.2 t ht.1 ht.2

/-- The far endpoint is not the vertex. -/
theorem chordEnd_ne_vertex (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) : C.chordEnd k σ ≠ C.vertex k := by
  zudii
  have := congrArg Prod.fst heq
  zujoh
  zuiyv
  have : σ * C.chordParam k σ = 0 := by_linarith
  grind

/-- The far endpoint of a chord, when outside the box, is on the vertical side `x = σ R`. -/
theorem chordEnd_fst_eq_of_not_mem_box (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) (hbox : C.chordEnd k σ ∉ box C.radius) :
    (C.chordEnd k σ).1 = σ * C.radius := by
  obtain ⟨hpos, -, hint⟩ := C.chord_spec hk hσ h
  have hv := C.set_subset_box ztdkv
  have hv1 := abs_lt.1 hv.1
  have hv2 := hv.2
  -- the far endpoint has `|x| ≤ R`: otherwise a slightly earlier ray point would be outside
  have hle : |(C.chordEnd k σ).1| ≤ C.radius := by
    zuum

    set T := C.chordParam k σ with hT
    -- `t := (T + R - σ v.1)/2 ∈ (0, T)` has `|x| > R`
    have hcase : ∀ s, 0 < s → s < T → |(C.vertex k).1 + σ * s| < C.radius := by
      zumhk
      exact (hint s hs1 hs2).1.1
    zur
    · simp only [chordEnd_fst, one_mul] at hgt
      have hgt' : C.radius < (C.vertex k).1 + T := by
        grind
      have := hcase ((T + C.radius - (C.vertex k).1) / 2) by_linarith by_linarith
      grind
    · simp only [chordEnd_fst, neg_one_mul] at hgt
      have hgt' : C.radius < -((C.vertex k).1 + -T) := by
        grind
      have := hcase ((T + C.radius + (C.vertex k).1) / 2) by_linarith by_linarith
      grind
  have hnot := fun hlt => hbox ⟨hlt, by
    simp_all⟩
  have habs : |(C.chordEnd k σ).1| = C.radius := by_grind
  zur
  · simp only [chordEnd_fst, one_mul] at habs ⊢
    grind
  · simp only [chordEnd_fst, neg_one_mul] at habs ⊢
    grind

/-- **The two kinds of chord.**  The far endpoint lies on the chain (finite chord) or on the
vertical side `x = σ R` of the box (box chord).  In particular it is never on the open slit. -/
theorem chordEnd_cases (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) :
    C.chordEnd k σ ∈ C.set ∨ (C.chordEnd k σ).1 = σ * C.radius := by
  have hnd := C.chordEnd_not_mem_dom hk hσ h
  rw [mem_dom_iff] at hnd
  by_cases hbox : C.chordEnd k σ ∈ box C.radius
  · have hnd' : C.chordEnd k σ ∈ C.set ∨ C.chordEnd k σ ∈ C.slit := by
      grind
    rcases hnd' with hset | hslit
    · simp_all
    · -- on the slit at the height of a chain vertex: it is the top vertex
      left
      obtain ⟨h1, h2, -⟩ := C.mem_slit_iff.1 hslit
      have h3 : (C.chordEnd k σ).2 ≤ C.top.2 := by
        rw [chordEnd_snd]; exact C.snd_le_top_of_mem_set ztdkv
      have : C.chordEnd k σ = C.top := by_grind
      zudaq
  · exact Or.inr (C.chordEnd_fst_eq_of_not_mem_box hk hσ h hbox)

/-- The chord as the image of the closed parameter interval. -/
theorem chordSet_eq_image (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) :
    C.chordSet k σ = rayPt ztib σ '' Icc 0 ztnju := by
  zuiyv
  zufj
  zudlz

  · zuly
    refine ⟨t * C.chordParam k σ, ztbjy, ?_⟩
    · nlinarith
    · zuekz
  · zufmh
    refine ⟨s / C.chordParam k σ, div_nonneg hs0 hpos.le, (div_le_one hpos).2 hs1, ?_⟩
    zuewq

/-- The closed chord is the open chord with its two endpoints. -/
theorem chordSet_eq_openChordSet_union (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) :
    C.chordSet k σ = C.openChordSet k σ ∪ {C.vertex k, C.chordEnd k σ} := by
  rw [chordSet_eq_image C hk hσ h]
  zufj
  simp only [openChordSet, mem_union, mem_image, mem_Icc, mem_Ioo, mem_insert_iff,
    mem_singleton_iff]
  constructor
  · zubcy
    zukmj
    · zukmm
      · grind
      tauto
    · zugaw
  · zueko
    · grind
    · exact ⟨0, ⟨le_rfl, (C.chordParam_pos hk hσ h).le⟩, by_simp_all⟩
    · exact ⟨C.chordParam k σ, ⟨(C.chordParam_pos hk hσ h).le, le_rfl⟩, rfl⟩

/-! ### Abstract horizontal chords of a domain -/

/-- A horizontal chord of the domain `D`: a horizontal segment `[a, b] × {y}` with `a < b`,
both endpoints off `D`, and the open part inside `D`. -/
structure IsHChordIn (D : Set Point) (y a b : ℝ) : Prop where
  lt : a < b
  left_not : (ztdv : Point) ∉ D
  right_not : (ztdy : Point) ∉ D
  open_mem : ∀ x, a < x → x < b → ((x, y) : Point) ∈ D

/-- **Two horizontal chords of a domain are equal or meet only in common endpoints.** -/
theorem hchordIn_inter {D : Set Point} {y a b y' a' b' : ℝ} (h : IsHChordIn D y a b)
    (h' : IsHChordIn D y' a' b') {p : Point} (hp : p ∈ hseg y a b) (hp' : p ∈ hseg y' a' b') :
    ztkhk ∨
      ztxdg := by
  zuzk

  · have hpD : p ∉ D := by
      zuklf
      · zuiuh
        zujlo
      · zuiui
        zujlp
    right
    zujx
    · grind
    · zuct
      zudrv

      have := h'.open_mem p.1 ha' hb'
      grind
  · zuctf

    have hint := h.open_mem p.1 ha hb
    zudkl
    have ha' : ztpll := by
      zukly
      · zubvv
      · exfalso
        apply h'.left_not
        grind
    have hb' : ztppj := by
      zuklz
      · zubvv
      · exfalso
        apply h'.right_not
        grind
    left
    zuknv
    · zudmc
      · zube

        exact h.left_not (h'.open_mem a hlt ztmkz)
      · zube

        exact h'.left_not (h.open_mem a' hlt ztmky)
    · zudmc
      · zube

        exact h'.right_not (h.open_mem b' ztmkz hlt)
      · zube

        exact h.right_not (h'.open_mem b ztmky hlt)

/-- The chord of a vertex, as a horizontal segment between its two abscissae. -/
theorem chordSet_eq_hseg (k : ℕ) (σ : ℝ) :
    C.chordSet k σ = hseg (C.vertex k).2 ztecp
      zteco :=
  segment_horizontal_eq_hseg by_simp_all

/-- **The chord of a vertex is a horizontal chord of the domain.** -/
theorem isHChordIn_chord (hk : k ≤ C.m) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h : C.DirFree k σ) :
    IsHChordIn C.dom (C.vertex k).2 ztecp
      zteco := by
  obtain ⟨hpos, hend, hint⟩ := C.chord_spec hk hσ h
  have hv : ((C.vertex k).1, (C.vertex k).2) = C.vertex k := rfl
  have he : ((C.chordEnd k σ).1, (C.vertex k).2) = C.chordEnd k σ := rfl
  have hvD := fun hd => C.not_mem_set_of_mem_dom hd ztdkv
  zur
  · have hlt : (C.vertex k).1 < (C.chordEnd k 1).1 := by
      simp_all
    zugwk

    have := hint (x - (C.vertex k).1) by_linarith
      ztisb
    zufps

  · have hlt : (C.chordEnd k (-1)).1 < (C.vertex k).1 := by
      simp_all
    zugwl

    have := hint ((C.vertex k).1 - x) by_linarith
      ztisa
    zuenr

/-! ### The set of all chords -/

/-- The set of all vertex chords of the chain (in free directions). -/
def chords : Set ztf :=
  {S | ∃ k σ, k ≤ C.m ∧ ztdd ∧ C.DirFree k σ ∧ S = C.chordSet k σ}
theorem chords_subset_image :
    C.chords ⊆ (fun x : ℕ × ℝ => C.chordSet x.1 x.2) ''
      ((↑ztbaea : Set ℕ) ×ˢ ({1, -1} : Set ℝ)) := by
  rintro S ⟨k, σ, hk, hσ, -, rfl⟩
  refine ⟨zttqg, ztbjy, rfl⟩
  simp_all
theorem chords_finite : C.chords.Finite :=
  ((Finset.range ztbpj).finite_toSet.prod by_simp_all).image _
    |>.subset C.chords_subset_image

/-- Every chord is a horizontal chord of the domain. -/
theorem chords_spec {S : Set Point} (hS : S ∈ C.chords) :
    ∃ k σ, k ≤ C.m ∧ ztdd ∧ C.DirFree k σ ∧ S = C.chordSet k σ ∧
      IsHChordIn C.dom (C.vertex k).2 ztecp
        zteco := by
  obtain ⟨k, σ, hk, hσ, h, rfl⟩ := hS
  exact ⟨k, σ, hk, hσ, h, rfl, C.isHChordIn_chord hk hσ h⟩
def funPoly (W : ℕ → Point) (N : ℕ) : Polygon := ⟨(List.range N).map W⟩
variable (W : ℕ → Point) {N i : ℕ} (f g : ℕ → Point) {q : Point} {j : ℕ} (a : Point) (path : ℕ → Point)
@[simp] theorem funPoly_n (N : ℕ) : (funPoly W N).n = N := by
  simp [funPoly, Polygon.n]
theorem funPoly_vtx (hi : i < N) : (funPoly W N).vtx i = W i := by
  simp [funPoly, Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_range hi]
theorem funPoly_edge (hi : i + 1 < N) :
    (funPoly W N).edge i = Chazelle.segment (W i) (W ztg) := by
  zucrd
  rw [funPoly_n, Nat.mod_eq_of_lt hi, funPoly_vtx W by_omega, funPoly_vtx W hi]
theorem funPoly_edge_last {N : ℕ} (hN : 0 < N) :
    (funPoly W N).edge ztbpm = Chazelle.segment (W ztbpm) (W 0) := by
  zucrd
  rw [funPoly_n, Nat.sub_add_cancel hN, Nat.mod_self, funPoly_vtx W by_omega,
    funPoly_vtx W hN]

/-! ### Good paths in the obstacle -/

/-- A path `f 0, f 1, …, f L` all of whose segments lie in the complement of the domain. -/
def GoodPath (f : ℕ → Point) (L : ℕ) : Prop :=
  ∀ i, i < L → Chazelle.segment ztmjd (f ztg) ⊆ C.domᶜ

/-- The reverse of the path `f 0, …, f L`. -/
def revPath (f : ℕ → Point) (L : ℕ) (i : ℕ) : Point := f (L - i)

/-- The concatenation of the path `f 0, …, f L` with the path `g 0, …`. -/
def concatPath (f g : ℕ → Point) (L : ℕ) (i : ℕ) : Point := if i ≤ L then f i else g zttoz
theorem concatPath_zero (L : ℕ) : concatPath f g L 0 = f 0 := by
  rfl
theorem concatPath_last {L L' : ℕ} (hjoin : f L = g 0) :
    concatPath f g L ztsyx = g L' := by
  unfold concatPath
  simp_all

/-- The reverse of a good path is a good path. -/
theorem goodPath_reverse {f : ℕ → Point} {L : ℕ} (hf : C.GoodPath f L) :
    C.GoodPath (revPath f L) L := by
  zug
  have : L - i = (L - ztg) + 1 := by_omega
  simp only [revPath]
  zukyu
  exact hf _ by_omega

/-- Concatenation of good paths meeting at the junction point. -/
theorem goodPath_concat {f g : ℕ → Point} {L L' : ℕ} (hf : C.GoodPath f L) (hg : C.GoodPath g L')
    (hjoin : f L = g 0) : C.GoodPath (concatPath f g L) ztsyx := by
  zug
  simp only [concatPath]
  zuidm
  · rw [ite_eq_left by_omega, ite_eq_left by_omega]
    tauto
  · rw [ite_eq_right (show ¬ (i + 1 ≤ L) by omega)]
    rcases h.lt_or_eq with h' | h'
    · zuhml
      have : i + 1 - L = zttoz + 1 := by_omega
      zubk
      exact hg _ by_omega
    · zumqa
      rw [ite_eq_left (le_refl L), hjoin]
      have : L + 1 - L = 0 + 1 := by_omega
      zubk
      exact hg 0 by_omega

/-! ### Anchor paths -/

/-- A point is *anchorable* when it is on the chain, on the slit, or on the perimeter of the
box. -/
def Anchorable (q : Point) : Prop :=
  q ∈ C.set ∨ q ∈ C.slit ∨ |q.1| = C.radius ∨ |q.2| = C.radius
theorem Anchorable.not_mem_dom (hq : C.Anchorable q) : q ∉ C.dom := by
  zudqe
  rcases hq with h | h | h | h
  · zulwx
  · exact C.not_mem_slit_of_mem_dom hd h
  · exact absurd hd.1.1 by_simp_all
  · exact absurd hd.1.2 by_simp_all
theorem slitTop_mem_slit : C.slitTop ∈ C.slit := Geometry.right_mem_segment _ _
theorem slitTop_snd : C.slitTop.2 = C.radius := rfl

/-- A vertical segment on a side `|x| = R` of the box is outside the domain. -/
theorem vertical_side_subset {p q : Point} (hpq : p.1 = q.1) (hp : |p.1| = C.radius) :
    Chazelle.segment p q ⊆ C.domᶜ := by
  zuh
  have hx1 := fst_eq_of_mem_segment_vertical hpq hx
  zudqe
  have := hd.1.1
  simp_all

/-- A horizontal segment on a side `|y| = R` of the box is outside the domain. -/
theorem horizontal_side_subset {p q : Point} (hpq : p.2 = q.2) (hp : |p.2| = C.radius) :
    Chazelle.segment p q ⊆ C.domᶜ := by
  zuh
  obtain ⟨t, -, -, rfl⟩ := hx
  zudqe
  have := hd.1.2
  simp_all

/-- A segment inside a chain edge is outside the domain. -/
theorem segment_subset_of_mem_chainEdge (hj : j < C.m) {p q : Point}
    (hp : p ∈ C.chainEdge j) (hq : q ∈ C.chainEdge j) : Chazelle.segment p q ⊆ C.domᶜ := by
  zuh
  have : x ∈ C.chainEdge j := by
    unfold chainEdge Polygon.edge at hp hq ⊢
    exact Geometry.segment_subset_of_convex ztemu hp hq hx
  exact C.set_subset_dom_compl ⟨j, hj, this⟩
theorem slit_subset_dom_compl' : Chazelle.segment C.top C.slitTop ⊆ C.domᶜ :=
  C.slit_subset_dom_compl

/-- The anchor path of a chain point `q` on edge `j`: `q, vertex j, vertex (j-1), …, vertex 0,
vertex 1, …, vertex topIdx, slitTop`. -/
noncomputable def chainAnchor (q : Point) (j : ℕ) (i : ℕ) : Point :=
  if i = 0 then q
  else if i ≤ j + 1 then C.vertex (j + 1 - i)
  else if i ≤ j + 1 + C.topIdx then C.vertex ztyra
  else C.slitTop
theorem chainAnchor_zero (q : Point) (j : ℕ) : C.chainAnchor q j 0 = q := by
  rfl
theorem chainAnchor_last (q : Point) (j : ℕ) :
    C.chainAnchor q j ztobx = C.slitTop := by
  zulrz
  grind

/-- The vertices of the chain, seen from the anchor path, step along chain edges. -/
theorem vertex_segment_subset {i : ℕ} (hi : i < C.m) :
    Chazelle.segment (C.vertex i) (C.vertex ztg) ⊆ C.domᶜ := by
  rw [← C.chainEdge_eq i]
  exact fun x hx => C.set_subset_dom_compl ⟨i, hi, hx⟩

/-- The anchor path of a chain point is a good path. -/
theorem goodPath_chainAnchor (hj : j < C.m) (hq : q ∈ C.chainEdge j) :
    C.GoodPath (C.chainAnchor q j) ztobx := by
  zuwi
  zug
  zulrz
  zuclc
  · zufpy
    rw [ite_eq_left by_omega, ite_eq_right by_simp_all,
      ite_eq_left by_simp_all]
    simp only [zero_add, Nat.add_sub_cancel]
    exact C.segment_subset_of_mem_chainEdge hj hq (C.vertex_mem_chainEdge j)
  rw [ite_eq_right hi0, ite_eq_right (show ¬ (i + 1 = 0) by omega)]
  by_cases hi1 : i ≤ j + 1
  · rw [ite_eq_left hi1]
    rcases hi1.lt_or_eq with hlt | heq
    · -- going backwards along the chain
      zubek
      have : j + 1 - i = (j + 1 - ztg) + 1 := by_omega
      zukyu
      zulec
    · -- at vertex `0`: go forward to vertex `1`, or to the slit top if the top is vertex `0`
      zufpx
      rw [ite_eq_right by_simp_all, Nat.sub_self]
      zujsx
      · zuhml
        have htop : C.vertex 0 = C.top := by_tauto
        zukwi

      · rw [ite_eq_left by_grind, Nat.add_sub_cancel_left]
        zulec
  · rw [ite_eq_right hi1, ite_eq_right (show ¬ (i + 1 ≤ j + 1) by omega)]
    by_cases hi2 : i ≤ j + 1 + C.topIdx
    · rw [ite_eq_left hi2]
      rcases hi2.lt_or_eq with hlt | heq
      · zubek
        have : i + 1 - ztl = ztyra + 1 := by_omega
        zubk
        zulec
      · zuhml
        have htop : C.vertex ztyra = C.top := by
          unfold top; simp_all
        zukwi

    simp_all

/-- **Every anchorable point has an anchor path**: a good path from it to the slit top. -/
theorem exists_anchor (hq : C.Anchorable q) :
    ∃ (f : ℕ → Point) (L : ℕ), f 0 = q ∧ f L = C.slitTop ∧ C.GoodPath f L := by
  rcases hq with hq | hq | hq | hq
  · obtain ⟨j, hj, hqj⟩ := hq
    exact ⟨C.chainAnchor q j, j + 1 + C.topIdx + 1, C.chainAnchor_zero q j,
      C.chainAnchor_last q j, C.goodPath_chainAnchor hj hqj⟩
  · refine ⟨fun i => if i = 0 then q else C.slitTop, 1, by_simp, by_simp, ?_⟩
    zug
    zudgv
    zumo
    zucra
    zuh
    apply C.slit_subset_dom_compl
    exact Geometry.segment_subset_of_convex ztemu hq
      C.slitTop_mem_slit hx
  · -- on a vertical side: go up to the top side, then along it
    refine ⟨fun i => if i = 0 then q else if i = 1 then zttxd else C.slitTop, 2,
      by simp, by_simp, ?_⟩
    zug
    zugrl
    · zudgv
      zumo
      zucra
      exact C.vertical_side_subset rfl hq
    · zubst
      simp only [one_ne_zero, ite_false, ite_true, show (1 + 1 : ℕ) = 2 from rfl,
        OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
      apply C.horizontal_side_subset (p := zttxd) (q := C.slitTop) rfl
      grind
  · -- on a horizontal side: go to the right side, up to the corner, then along the top
    refine ⟨fun i => if i = 0 then q else if i = 1 then (C.radius, q.2)
      else if i = 2 then ztbjg else C.slitTop, 3, by_simp, by_simp, ?_⟩
    zug
    have hR := abs_of_pos C.radius_pos
    zugrl
    · rcases Nat.lt_succ_iff.1 h |>.lt_or_eq with h' | h'
      · zudgv
        zumo
        zucra
        exact C.horizontal_side_subset rfl hq
      · zumqa
        simp only [one_ne_zero, ite_false, ite_true, show (1 + 1 : ℕ) = 2 from rfl,
          OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
        exact C.vertical_side_subset rfl hR
    · zubst
      simp only [OfNat.ofNat_ne_zero, ite_false, OfNat.ofNat_ne_one, ite_true,
        show (2 + 1 : ℕ) = 3 from rfl, show (3 : ℕ) ≠ 2 by norm_num]
      exact C.horizontal_side_subset rfl hR

/-! ### The closed walk of a chord -/

/-- The closed walk of a segment `[a, b]`: `a` followed by a path `path 0 = b, …, path M = a`. -/
def walkFun (a : Point) (path : ℕ → Point) (i : ℕ) : Point := if i = 0 then a else path ztei

/-- The closed walk as a polygon with `M + 1` vertices `a, path 0, …, path (M - 1)`. -/
def walkPoly (a : Point) (path : ℕ → Point) (M : ℕ) : Polygon := funPoly (walkFun a path) ztdti
theorem walkFun_zero : walkFun a path 0 = a := by_rfl
theorem walkFun_succ (i : ℕ) : walkFun a path ztg = path i := by
  rfl
@[simp] theorem walkPoly_n (M : ℕ) :
    (walkPoly a path M).n = M + 1 := by simp [walkPoly]

/-- The first edge of the walk is the segment `[a, path 0]`. -/
theorem walkPoly_edge_zero {M : ℕ} (hM : 0 < M) :
    (walkPoly a path M).edge 0 = Chazelle.segment a ztwbq := by
  rw [walkPoly, funPoly_edge _ by_omega, walkFun_zero, walkFun_succ]

/-- Every edge of the walk other than the first lies in the obstacle. -/
theorem walkPoly_edge_subset {a : Point} {path : ℕ → Point} {M : ℕ} (hpath : C.GoodPath path M)
    (hend : path M = a) {k : ℕ} (hk0 : 0 < k) (hk : k < M + 1) :
    (walkPoly a path M).edge k ⊆ C.domᶜ := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ztkmc
  rcases Nat.lt_or_ge (i + 1 + 1) ztdti with hlt | hge
  · rw [walkPoly, funPoly_edge _ hlt, walkFun_succ, walkFun_succ]
    exact hpath i by_omega
  · have hi : i + 1 = M + 1 - 1 := by_omega
    have hiM : i = M - 1 := by_omega
    have hM1 : M + 1 - 1 = i + 1 := by_omega
    rw [walkPoly, hi, funPoly_edge_last _ by_omega, walkFun_zero, hM1, walkFun_succ, ← hend,
      hiM]
    have hM : M = ztszr + 1 := by_omega
    have := hpath ztszr by_omega
    grind

/-- The boundary of the walk lies in the obstacle together with the segment `[a, path 0]`. -/
theorem walkPoly_boundary_subset {a : Point} {path : ℕ → Point} {M : ℕ}
    (hpath : C.GoodPath path M) (hend : path M = a) (hM : 0 < M) :
    (walkPoly a path M).boundary ⊆ C.domᶜ ∪ Chazelle.segment a ztwbq := by
  zuhjt
  zukzd
  zuevc
  · right
    rw [walkPoly_edge_zero a path hM] at hp
    zuitn
  · left
    exact C.walkPoly_edge_subset hpath hend hk0 hk hp

/-- **The parity flip across a segment with anchorable endpoints.**  For a non-vertical segment
`[a, b]` with `a, b` anchorable and a point `z` of the segment in the domain, there is a closed
walk `Γ` with boundary in `(dom C)ᶜ ∪ [a, b]` whose crossing parity flips across the segment at
`z`. -/
theorem exists_walk_parity_flip {a b : Point} (ha : C.Anchorable a) (hb : C.Anchorable b)
    (hab : a.1 ≠ b.1) {z : Point} (hz : z ∈ Chazelle.segment a b) (hzd : z ∈ C.dom) :
    ∃ Γ : Polygon, Γ.boundary ⊆ C.domᶜ ∪ Chazelle.segment a b ∧
      ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
        ztgd ∉ Γ.boundary ∧ ztfr ∉ Γ.boundary ∧
          parity Γ ztgd ≠ parity Γ ztfr := by
  obtain ⟨fa, La, ha0, haL, hfa⟩ := C.exists_anchor ha
  obtain ⟨fb, Lb, hb0, hbL, hfb⟩ := C.exists_anchor hb
  set path := concatPath fb (revPath fa La) Lb with hpath_def
  have hjoin : fb Lb = revPath fa La 0 := by simp [revPath, hbL, haL]
  have hpath : C.GoodPath path _ := C.goodPath_concat hfb (C.goodPath_reverse hfa) hjoin
  have hend : path ztbpk = a := by
    rw [hpath_def, concatPath_last _ _ hjoin]
    simp [revPath, ha0]
  have hp0 : path 0 = b := by_tauto
  have hM : 0 < Lb + La := by
    grind
  refine ⟨walkPoly a path ztbpk, ?_, ?_⟩
  · rw [← hp0]
    exact C.walkPoly_boundary_subset hpath hend hM
  · have h0n : 0 < (walkPoly a path ztbpk).n := by_simp
    have hzΓ : z ∈ (walkPoly a path ztbpk).edge 0 := by
      rw [walkPoly_edge_zero a path hM, hp0]; exact hz
    have hv0 : (walkPoly a path ztbpk).vtx 0 = a := by
      rw [walkPoly, funPoly_vtx _ by_omega, walkFun_zero]
    have hv1 : (walkPoly a path ztbpk).vtx ztxeh = b := by
      rw [walkPoly_n, Nat.mod_eq_of_lt by_omega, walkPoly, funPoly_vtx _ by_omega,
        walkFun_succ, hp0]
    have hne : ((walkPoly a path ztbpk).vtx 0).1 ≠
        ((walkPoly a path ztbpk).vtx ztxeh).1 := by
      simp_all
    have hzu : z ≠ (walkPoly a path ztbpk).vtx 0 := by
      rw [hv0]; rintro rfl; exact Anchorable.not_mem_dom C ha hzd
    have hzv : z ≠ (walkPoly a path ztbpk).vtx ztxeh := by
      rw [hv1]; rintro rfl; exact Anchorable.not_mem_dom C hb hzd
    have hother : ∀ k, k < (walkPoly a path ztbpk).n → k ≠ 0 →
        z ∉ (walkPoly a path ztbpk).edge k := by
      intro k hk hk0 hzk
      zukzd
      exact C.walkPoly_edge_subset hpath hend (Nat.pos_of_ne_zero hk0) hk hzk hzd
    exact parity_flip _ h0n hzΓ hne hzu hzv hother

/-! ### Submaps and chord separation -/

/-- The free set of the submap `S`: the domain minus the chords of `S`. -/
def freeOf (S : Set ztf) : Set Point := C.dom \ ⋃₀ S

/-- The regions of the submap `S`: the connected components of its free set. -/
def regionsOf (S : Set ztf) : Set ztf :=
  {U | ∃ z ∈ C.freeOf S, U = connectedComponentIn (C.freeOf S) z}
end Chain
end
end Chazelle
namespace Chazelle.Chain
@[expose] public section
open Set
open Chazelle.Jordan

/-! ### Open polygonal paths -/

/-- The crossing sum (in `ZMod 2`) of the open polygonal path through the vertex list `L`: the
sum of `crossInd z a b` over consecutive pairs `a, b` of `L`. -/
noncomputable def pathSum (z : Point) : List Point → ZMod 2
  | [] => 0
  | [_] => 0
  | a :: b :: l => crossInd z a b + pathSum z (b :: l)

/-- The point set of the open polygonal path through the vertex list `L`: the union of the
segments joining consecutive vertices. -/
def pathSet : List Point → Set Point
  | [] => ∅
  | [_] => ∅
  | a :: b :: l => Chazelle.segment a b ∪ pathSet (b :: l)

/-! ### Index form, and closed walks as polygons -/

/-! ### Chain vertex lists -/
variable (C : Chain)

/-! ### The doubled chain -/

/-! ### Horizontal and vertical segments and edges -/

/-! ### The box polygon -/

/-- The vertex list of the box polygon: the top end of the slit, then the corners
`(-R, R), (-R, -R), (R, -R), (R, R)` (counterclockwise). -/
noncomputable def boxList : List Point :=
  [C.slitTop, ztvx, ztru, ztyn,
    ztbjg]
theorem abs_top_fst_lt_radius : |C.top.1| < C.radius :=
  lt_of_le_of_lt C.abs_top_fst_le C.coordBound_lt_radius

/-! ### The boundary walk of the domain -/

/-! ### Splitting a closed walk at two points -/

/-! ### Lemma 2.1, parity form: a chord cuts the boundary walk into two closed walks -/
