module

public import Chazelle.MacT
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.ClusterLabelStage
public import Chazelle.Mountain.PieceSteps
public import Chazelle.Core.SpecNF
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Chain.Submap

namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideKey_inj)
namespace WalkEmbed
noncomputable def off (n g x : ℝ) : ℝ := if g ≤ x then x - g else x - g + n
theorem off_nonneg {n g x : ℝ} (hx : 0 ≤ x) (hg : g < n) : 0 ≤ off n g x := by
  zumts
theorem off_lt {n g x : ℝ} (hx : x < n) (hg : 0 ≤ g) : off n g x < n := by
  zumts
theorem off_self (n g : ℝ) : off n g g = 0 := by simp [off]

/-- The offset of a walk position: vertex `(g + d) mod n`, parameter `t`. -/
theorem off_key {n g d : ℕ} (hg : g < n) (hd : d < n) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    off n g ztwuf = d + t := by
  zumtr
  by_cases h : g + d < n
  · zukp
    grind
  · obtain ⟨k, hk⟩ : ∃ k, g + d = n + k := ⟨g + d - n, by_omega⟩
    have hkg : k + 1 ≤ g := by_omega
    have e : ztbe % n = k := by
      rw [hk, Nat.add_mod_left, Nat.mod_eq_of_lt by_grind]
    zui
    have hlt' : (k : ℝ) + 1 ≤ g := by exact_mod_cast hkg
    have hk' : (g : ℝ) + d = n + k := by exact_mod_cast hk
    grind

/-- The offset (as a natural number) of the walk vertex `p` from the walk vertex `g`. -/
def dOf (n g p : ℕ) : ℕ := ztgle % n
variable {n : ℕ} {l r z x : ℝ}
theorem dOf_lt (hn : 0 < n) (g p : ℕ) : dOf n g p < n := Nat.mod_lt _ hn
theorem add_dOf {n g p : ℕ} (hg : g < n) (hp : p < n) : ztpbz % n = p := by
  zujqj
  by_cases h : g ≤ p
  · have e : ztgle % n = p - g := by
      zucub
    rw [e, show g + ztkbw = p by omega, Nat.mod_eq_of_lt hp]
  · have e : ztgle % n = p + n - g := Nat.mod_eq_of_lt by_grind
    rw [e, show g + ztgle = p + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hp]

/-- The offset of a key on the walk vertex `p`. -/
theorem off_key' {n g p : ℕ} (hg : g < n) (hp : p < n) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    off n g ztdj = dOf n g p + t := by
  have h := off_key hg (dOf_lt by_omega g p) ht ht1
  rwa [add_dOf hg hp] at h

/-- Injectivity of `d ↦ (g + d) mod n` on `[0, n)`. -/
theorem add_mod_inj {n g d d' : ℕ} (hd : d < n) (hd' : d' < n) (h : ztbe % n = ztsb % n) :
    d = d' := by
  have h1 : d % n = d' % n := Nat.ModEq.add_left_cancel' g h
  rwa [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hd'] at h1

/-- **Cyclic intervals are intervals of offsets** (measured from a base key outside them). -/
theorem sideInArc_iff_off {n g u w x : ℝ} (_hg : 0 ≤ g) (_hgn : g < n) (hu : 0 ≤ u) (hun : u < n)
    (hw : 0 ≤ w) (hwn : w < n) (hx : 0 ≤ x) (hxn : x < n) (huw : off n g u < off n g w) :
    sideInArc u w x ↔ off n g u < off n g x ∧ off n g x < off n g w := by
  unfold off at *
  zuiq

/-- **Convexity**: a cyclic interval not containing the base `g` contains every key whose
offset lies between the offsets of two of its keys. -/
theorem sideInArc_convex {n g a b x y w : ℝ} (_hg : 0 ≤ g) (_hgn : g < n) (hx : 0 ≤ x)
    (_hxn : x < n) (_hy : 0 ≤ y) (hyn : y < n) (hw : 0 ≤ w) (hwn : w < n)
    (hga : ¬ sideInArc a b g) (hxa : sideInArc a b x) (hya : sideInArc a b y)
    (h1 : off n g x < off n g w) (h2 : off n g w < off n g y) : sideInArc a b w := by
  zuul
  · have hg' : g ≤ a ∨ b ≤ g := by
      unfold sideInArc at hga; grind
    unfold sideInArc at hxa hya ⊢; rw [ite_eq_left hab] at hxa hya ⊢
    zulca

  · have hg' : b ≤ g ∧ g ≤ a := by
      unfold sideInArc at hga; simp_all
    unfold sideInArc at hxa hya ⊢; rw [ite_eq_right hab] at hxa hya ⊢
    zulca

/-- If `z` is inside `(l, r)` and `x` is not (and `x ≠ r`), then `r` lies between `z` and `x`. -/
theorem sideInArc_right (hlr : l ≠ r) (hz : sideInArc l r z) (hx : ¬ sideInArc l r x)
    (hxr : x ≠ r) : sideInArc z x r := by
  zujej
  · unfold sideInArc at *
    grind
  · unfold sideInArc at *
    grind

/-- If `z` is inside `(l, r)` and `x` is not (and `x ≠ l`), then `l` lies between `x` and `z`. -/
theorem sideInArc_left (hlr : l ≠ r) (hz : sideInArc l r z) (hx : ¬ sideInArc l r x)
    (hxl : x ≠ l) : sideInArc x z l := by
  zujej
  · unfold sideInArc at *
    grind
  · unfold sideInArc at *
    grind

/-! ## Agreeing stretches of two walks -/

/-- The walks `W` and `W'` **agree** on the stretch of length `L` starting at their vertices `g`
and `g'`: for `d ≤ L`, vertex `g + d` of `W` is vertex `g' + d` of `W'` (indices modulo the
lengths). -/
def Agree (W W' : Polygon) (g g' L : ℕ) : Prop :=
  ∀ d, d ≤ L → W.vtx ztwnv = W'.vtx ztwtx
theorem mod_succ_mod (n g d : ℕ) : (ztbe % n + 1) % n = ztzvu % n := by
  grind
theorem mod_pred_mod (hn : 0 < n) (g : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    (ztbe % n + n - 1) % n = (g + ztku) % n := by
  rw [show ztbe % n + n - 1 = ztbe % n + ztkl by omega, Nat.mod_add_mod,
    show g + d + ztkl = g + ztku + n by omega, Nat.add_mod_right]
namespace Agree
variable {W W' : Polygon} {g g' L : ℕ}

/-- Agreeing stretches have the same point at the same offset. -/
theorem sidePt_eq (hA : Agree W W' g g' L) {d : ℕ} (hd : d < L) (t : ℝ) :
    sidePt W ztwnv t = sidePt W' ztwtx t := by
  zucky
  rw [mod_succ_mod, mod_succ_mod, hA d hd.le, hA _ hd]

/-- Agreeing stretches have the same next vertex at the same offset. -/
theorem sideNext_eq (hA : Agree W W' g g' L) {d : ℕ} (hd : d < L) :
    sideNext W ztwnv = sideNext W' ztwtx := by
  zumuu
  rw [mod_succ_mod, mod_succ_mod, hA _ hd]

/-- Agreeing stretches have the same previous point at the same offset, away from the start. -/
theorem sidePrev_eq (hA : Agree W W' g g' L) (hn : 0 < W.n) (hn' : 0 < W'.n) {d : ℕ}
    (hd : d < L) {t : ℝ} (ht : t = 0 → 1 ≤ d) :
    sidePrev W ztwnv t = sidePrev W' ztwtx t := by
  zulcf
  by_cases h0 : t = 0
  · rw [ite_eq_left h0, ite_eq_left h0, mod_pred_mod hn _ ztvwk, mod_pred_mod hn' _ ztvwk,
      hA _ by_omega]
  · rw [ite_eq_right h0, ite_eq_right h0, hA d hd.le]

/-- **Agreeing stretches have the same left sectors** at the same offset, away from the
start. -/
theorem sideLeft_eq (hA : Agree W W' g g' L) (hn : 0 < W.n) (hn' : 0 < W'.n) {d : ℕ}
    (hd : d < L) {t : ℝ} (ht : t = 0 → 1 ≤ d) :
    sideLeft W ztwnv t = sideLeft W' ztwtx t := by
  funext x
  zuluz
  rw [hA.sidePrev_eq hn hn' hd ht, hA.sidePt_eq hd, hA.sideNext_eq hd]

/-- **Agreeing stretches attach the same sets** at the same offset (the walk embedding preserves
`SideAttach`). -/
theorem sideAttach_iff (hA : Agree W W' g g' L) (hn : 0 < W.n) (hn' : 0 < W'.n) {d : ℕ}
    (hd : d < L) {t : ℝ} (ht : t = 0 → 1 ≤ d) (c : Set Point) :
    SideAttach W c ztwnv t ↔ SideAttach W' c ztwtx t := by
  unfold SideAttach
  rw [hA.sideLeft_eq hn hn' hd ht, hA.sidePt_eq hd]
  constructor
  · rintro ⟨-, h⟩; exact ⟨Nat.mod_lt _ hn', h⟩
  · rintro ⟨-, h⟩; exact ⟨Nat.mod_lt _ hn, h⟩

/-- A set attached to `W'` at an offset of the stretch attaches its subsets through the same
point to `W` at the same offset. -/
theorem sideAttach_subset (hA : Agree W W' g g' L) (hn : 0 < W.n) (hn' : 0 < W'.n) {d : ℕ}
    (hd : d < L) {t : ℝ} (ht : t = 0 → 1 ≤ d) {c e : Set Point}
    (hc : SideAttach W' c ztwtx t) (hec : e ⊆ c)
    (he : sidePt W' ztwtx t ∈ e) : SideAttach W e ztwnv t := by
  rw [hA.sideAttach_iff hn hn' hd ht]
  obtain ⟨hp, ht0, ht1, -, r, hr, hl⟩ := hc
  exact ⟨hp, ht0, ht1, he, r, hr, fun x hx => hl x ztvuy⟩
end Agree

/-! ## The stretch bound -/

/-- An arc meets at most `n` walk edges. -/
theorem arcWt_le_n (M : Model) (a b : ℝ) : M.arcWt a b ≤ M.W.n := by
  zujhb
  calc (M.arcEdges a b).ncard ≤ (Set.Iio M.W.n).ncard :=
        Set.ncard_le_ncard ztqoa ztvde
    _ = M.W.n := by zunzd

/-- The weight of a region bounds its arcs. -/
theorem arcWt_le_weight (M : Model) {F : Set ztf} {U : Set Point} {a b : ℝ}
    (h : M.IsArc F U a b) : M.arcWt a b ≤ M.weight F U :=
  le_csSup ⟨M.W.n, by rintro _ ⟨ab, -, rfl⟩; exact arcWt_le_n M _ _⟩ ⟨(a, b), h, rfl⟩
variable {M : Model} {a b k x : ℝ}
/-- Every non-cut key inside a walk edge of a good model lies in an arc of some region. -/
theorem exists_arc_around (hM : GoodModel M) {Q : Polygon} {F : Set ztf}
    (hF : M.ChordFamily Q F) {x : ℝ} (hx0 : 0 < x) (hx : ¬ M.IsCut F x) :
    ∃ U ∈ M.regions F, ∃ l r : ℝ, M.IsArc F U l r ∧ sideInArc l r x := by
  zuqx
  · obtain ⟨⟨U, hU, a, b, harc⟩, -⟩ := arcCover M Q ∅ hM hF
    zutn
    · simp_all
    · refine ⟨U, hU, 0, 0, harc, ?_⟩
      zuxb
  · exact (walkAx_of_goodModel hM).arc_around hF.2.1 hF.1 hne hx

/-- **The stretch bound (step (a) of the `γ + 1` bound).**  Let the counted edges and the cuts of
a γ-semigranular family `F'` of a good model `M'` transfer to a family `F` of a model `M` along a
stretch of length `L` (starting at the walk vertices `g` of `M` and `g'` of `M'`).  Then every
`F`-cut-free key interval of `M` whose keys lie strictly inside the stretch meets at most `γ`
counted edges. -/
theorem arcWt_le_of_stretch {M M' : Model} (hM' : GoodModel M') {Q : Polygon}
    {F F' : Set ztf} (hF' : M'.ChordFamily Q F') {γ : ℕ} (hsg : M'.Semigranular F' γ)
    {g g' L : ℕ} (hg : g < M.W.n) (hg' : g' < M'.W.n) (hLn : L ≤ M.W.n) (hLn' : L ≤ M'.W.n)
    (hcount : ∀ d, d < L → M.counted ztwje → M'.counted ztbaag)
    (hcut : ∀ d, d < L → ∀ t : ℝ, 0 ≤ t → t < 1 → 0 < (d : ℝ) + t →
      M'.IsCut F' ((zthr % M'.W.n : ℕ) + t) → M.IsCut F ztwjt)
    {a b : ℝ}
    (hstr : ∀ x : ℝ, 0 ≤ x → x < M.W.n → sideInArc a b x →
      0 < off M.W.n g x ∧ off M.W.n g x < L)
    (hfree : ∀ x, sideInArc a b x → ¬ M.IsCut F x) :
    M.arcWt a b ≤ γ := by
  classical
  zucqo
  zukzv
  zuqi
  zucau

  -- keys of the walk of `M` inside a walk edge
  have hkey : ∀ p : ℕ, p < n → ∀ t : ℝ, 0 ≤ t → t < 1 → 0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < n :=
    fun p hp t ht ht1 => by
      zuhuw

  have hkey' : ∀ p : ℕ, p < n' → ∀ t : ℝ, 0 ≤ t → t < 1 →
      0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < n' :=
    fun p hp t ht ht1 => by
      have : (p : ℝ) + 1 ≤ n' := by exact_mod_cast hp
      exact ztomv
  -- a key of the walk of `M` met by the interval has its offset in the stretch
  have hin : ∀ p : ℕ, p < n → ∀ t : ℝ, 0 < t → t < 1 → sideInArc a b ztk →
      dOf n g p < L ∧ (p = ztpbz % n) ∧ off n g ztk = dOf n g p + t := by
    intro p hp t ht ht1 hx
    have hoff := off_key' hg hp ht.le ht1
    have hs := hstr _ by_grind by_grind hx
    rw [hoff] at hs
    refine ⟨?_, (add_dOf hg hp).symm, hoff⟩
    have : (dOf n g p : ℝ) < L := by_grind
    zufc
  -- the base of the stretch is not in the interval
  have hga : ztsoa := fun h => by
    have := (hstr g ztdys hgR h).1
    rw [off_self] at this; grind
  -- a cut of `F'` strictly inside the stretch between two keys of the interval gives a cut
  -- of `F` inside the interval
  have htransfer : ∀ (p q : ℕ) (t u : ℝ), p < n → q < n → 0 < t → t < 1 → 0 < u → u < 1 →
      sideInArc a b ztk → sideInArc a b ztzq → ∀ y' : ℝ, M'.IsCut F' y' →
      (dOf n g p : ℝ) + t < off n' g' y' → off n' g' y' < (dOf n g q : ℝ) + u → False := by
    intro p q t u hp hq ht ht1 hu hu1 hpin hqin y' hy' h1 h2
    obtain ⟨hdpL, -, hoffp⟩ := hin p hp t ht ht1 hpin
    obtain ⟨hdqL, -, hoffq⟩ := hin q hq u hu hu1 hqin
    obtain ⟨c, hc, pr, tr, hA, rfl⟩ := hy'
    have hpr := hA.1
    have htr0 := hA.2.1
    have htr1 := hA.2.2.1
    rw [off_key' hg' hpr htr0 htr1] at h1 h2
    set dr := dOf n' g' pr
    have hdrL : dr < L := by
      have : (dr : ℝ) < L := by
        have : (dOf n g q : ℝ) + 1 ≤ L := by exact_mod_cast hdqL
        linarith
      zufc
    have hcut' := hcut dr hdrL tr htr0 htr1 (by
      grind) (by rw [add_dOf hg' hpr]; exact ⟨c, hc, pr, tr, hA, rfl⟩)
    have hoffy := off_key hg (show dr < n by omega) htr0 htr1
    have hyb := hkey ((g + dr) % n) zthp tr htr0 htr1
    have hpb := hkey p hp t ht.le ht1
    have hqb := hkey q hq u hu.le hu1
    refine hfree _ ?_ hcut'
    exact sideInArc_convex ztdys hgR hpb.1 hpb.2 hqb.1 hqb.2 hyb.1 hyb.2 hga
      hpin hqin by_grind by_grind
  zujhb
  rcases (M.arcEdges a b).eq_empty_or_nonempty with hE | ⟨p₀, hp₀n, -, t₀, ht₀, ht₀1, hx₀⟩
  · rw [hE, Set.ncard_empty]; omega
  obtain ⟨hd₀L, hp₀, hoff₀⟩ := hin p₀ hp₀n t₀ ht₀ ht₀1 hx₀
  set d₀ := dOf n g p₀
  set z' : ℝ := ((zttkt % n' : ℕ) : ℝ) + t₀ with hz'
  have hd₀n' : d₀ < n' := by_omega
  -- `z'` is not a cut of `F'`
  have hz'cut : ¬ M'.IsCut F' z' := by
    zuchg
    have := hcut d₀ hd₀L t₀ ht₀.le ht₀1 by_positivity hc
    rw [← hp₀] at this
    exact hfree _ hx₀ this
  have hz'pos : 0 < z' := by_positivity
  obtain ⟨U', hU', l', r', harc', hz'in⟩ := exists_arc_around hM' hF' hz'pos hz'cut
  have hwt : M'.arcWt l' r' ≤ γ := (arcWt_le_weight M' harc').trans (hsg U' hU')
  -- the edge map
  let f : ℕ → ℕ := fun p => (g' + dOf n g p) % n'
  have hmaps : Set.MapsTo f ztszt (M'.arcEdges l' r') := by
    rintro p ⟨hpn, hpc, t, ht, ht1, hx⟩
    obtain ⟨hdL, hp, hoff⟩ := hin p hpn t ht ht1 hx
    set d := dOf n g p
    have hdn' : d < n' := by_omega
    refine ⟨Nat.mod_lt _ hn', hcount d hdL (hp ▸ hpc), t, ht, ht1, ?_⟩
    set x' : ℝ := ((f p : ℕ) : ℝ) + t with hx'
    have hx'cut : ¬ M'.IsCut F' x' := by
      zuchg
      have := hcut d hdL t ht.le ht1 by_positivity hc
      rw [← hp] at this
      exact hfree _ hx this
    by_contra hnot
    rcases harc'.2.2.2.2.1 with ⟨hl'c, hr'c, hl'r'⟩ | ⟨-, rfl, rfl⟩
    · have hx'r : x' ≠ r' := fun h => hx'cut (h ▸ hr'c)
      have hx'l : x' ≠ l' := fun h => hx'cut (h ▸ hl'c)
      -- offsets in the walk of `M'`
      have hoffz := off_key hg' hd₀n' ht₀.le ht₀1
      have hoffx := off_key hg' hdn' ht.le ht1
      have hz'b : 0 ≤ z' ∧ z' < n' := hkey' _ ztdtl t₀ ht₀.le ht₀1
      have hx'b : 0 ≤ x' ∧ x' < n' := hkey' _ ztdtl t ht.le ht1
      have hg'0 : ztehf := Nat.cast_nonneg g'
      rcases lt_trichotomy ((d₀ : ℝ) + t₀) ztbcr with hlt | heq | hgt
      · have hr := sideInArc_right hl'r' hz'in hnot hx'r
        obtain ⟨c, hc, pr, tr, hA, hr'eq⟩ := hr'c
        have hrb := hkey' pr hA.1 tr hA.2.1 hA.2.2.1
        rw [← hr'eq] at hrb
        rw [sideInArc_iff_off hg'0 hg'R hz'b.1 hz'b.2 hx'b.1 hx'b.2 hrb.1 hrb.2
          by_linarith, hoffz, hoffx] at hr
        exact htransfer p₀ p t₀ t hp₀n hpn ht₀ ht₀1 ht ht1 hx₀ hx r' ⟨c, hc, pr, tr, hA, hr'eq⟩
          hr.1 hr.2
      · obtain ⟨e1, e2⟩ := sideKey_inj ht₀.le ht₀1 ht.le ht1 heq
        zulvs
        rw [hx', show f p = zttkt % n' by simp only [f, d, e1]] at *
        rw [← e2]; omega
      · have hl := sideInArc_left hl'r' hz'in hnot hx'l
        obtain ⟨c, hc, pl, tl, hA, hl'eq⟩ := hl'c
        have hlb := hkey' pl hA.1 tl hA.2.1 hA.2.2.1
        rw [← hl'eq] at hlb
        rw [sideInArc_iff_off hg'0 hg'R hx'b.1 hx'b.2 hz'b.1 hz'b.2 hlb.1 hlb.2
          by_linarith, hoffz, hoffx] at hl
        exact htransfer p p₀ t t₀ hpn hp₀n ht ht1 ht₀ ht₀1 hx hx₀ l' ⟨c, hc, pl, tl, hA, hl'eq⟩
          hl.1 hl.2
    · zulvs
      unfold sideInArc; zuoqz; left; positivity
  have hinj : Set.InjOn f ztszt := by
    rintro p ⟨hpn, -, t, ht, ht1, hx⟩ q ⟨hqn, -, u, hu, hu1, hy⟩ hpq
    obtain ⟨hdpL, hp, -⟩ := hin p hpn t ht ht1 hx
    obtain ⟨hdqL, hq, -⟩ := hin q hqn u hu hu1 hy
    have := add_mod_inj (show dOf n g p < n' by omega) (show dOf n g q < n' by omega) hpq
    rw [hp, hq, this]
  calc (M.arcEdges a b).ncard ≤ (M'.arcEdges l' r').ncard :=
        Set.ncard_le_ncard_of_injOn f hmaps hinj (M'.arcEdges_finite l' r')
    _ = M'.arcWt l' r' := (Model.arcWt_eq M' l' r').symm
    _ ≤ γ := hwt

/-! ## Covering a walk by pieces -/
theorem off_inj {n g x y : ℝ} (_hg : 0 ≤ g) (_hgn : g < n) (hx : 0 ≤ x) (hxn : x < n) (hy : 0 ≤ y)
    (hyn : y < n) (h : off n g x = off n g y) : x = y := by
  zugis

/-- **A piece of the walk of `M`**: a stretch starting at the walk vertex `g`, of length `L < n`,
whose two end keys lie in `K`, along which every `F`-cut-free key interval meets at most `γ`
counted edges. -/
def PieceOK (M : Model) (F : Set ztf) (K : Set ℝ) (γ g L : ℕ) : Prop :=
  g < M.W.n ∧ L < M.W.n ∧ (g : ℝ) ∈ K ∧ ((zttkl % M.W.n : ℕ) : ℝ) ∈ K ∧
    ∀ a b : ℝ, (∀ x : ℝ, 0 ≤ x → x < M.W.n → sideInArc a b x →
        0 < off M.W.n g x ∧ off M.W.n g x < L) →
      ztivv → M.arcWt a b ≤ γ

/-- **Assembly**: if every key inside a counted walk edge lies strictly inside some piece, then every
`F`-cut-free key interval avoiding `K` meets at most `γ` counted edges.  (Such an interval is
confined to the piece of any of its counted keys, because it avoids the end keys of the piece.) -/
theorem arcWt_le_of_pieces {F : Set ztf} {K : Set ℝ} {γ : ℕ}
    (hcover : ∀ p : ℕ, p < M.W.n → M.counted p → ∀ t : ℝ, 0 < t → t < 1 →
      ∃ g L, PieceOK M F K γ g L ∧ 0 < off M.W.n g ztk ∧ off M.W.n g ztk < L)
    {a b : ℝ} (hK : ∀ x ∈ K, ¬ sideInArc a b x) (hfree : ∀ x, sideInArc a b x → ¬ M.IsCut F x) :
    M.arcWt a b ≤ γ := by
  classical
  have hE := M.arcEdges_finite a b
  rcases (M.arcEdges a b).eq_empty_or_nonempty with hE0 | ⟨p₀, hp₀n, hp₀c, t₀, ht₀, ht₀1, hx₀⟩
  · rw [Model.arcWt_eq, hE0, Set.ncard_empty]; omega
  obtain ⟨g, L, ⟨hg, hLn, hgK, heK, hbound⟩, hz0, hzL⟩ := hcover p₀ hp₀n hp₀c t₀ ht₀ ht₀1
  refine hbound a b (fun x hx0 hxn hx => ?_) hfree
  zugys
  have hgR : ztcrg := by exact_mod_cast hg
  have hga : ztsoa := by_grind
  have hz : 0 ≤ (p₀ : ℝ) + t₀ ∧ (p₀ : ℝ) + t₀ < n := by
    have : (p₀ : ℝ) + 1 ≤ n := by exact_mod_cast hp₀n
    grind
  have hxg : x ≠ g := by_grind
  have hx0' : 0 < off n g x := by
    rcases (off_nonneg hx0 hgR).lt_or_eq with h | h
    · zubh
    · exact absurd (off_inj ztdys hgR hx0 hxn ztdys hgR
        (by rw [off_self]; grind)) hxg
  refine ⟨hx0', ?_⟩
  zucux
  zugrh
  set e : ℕ := zttkl % n
  have hen : e < n := Nat.mod_lt _ by_omega
  have heR : (e : ℝ) < n := by exact_mod_cast hen
  have hoffe : off n g e = L := by
    have := off_key hg hLn le_rfl one_pos
    grind
  have hea : ¬ sideInArc a b e := by_grind
  rcases hge.lt_or_eq with hlt | heq
  · exact hea (sideInArc_convex ztdys hgR hz.1 hz.2 hx0 hxn ztvad heR
      hga hx₀ hx by_grind by_grind)
  · have := off_inj ztdys hgR hx0 hxn ztvad heR by_grind
    simp_all

/-! ## Small cyclic facts -/
theorem sideInArc_sub_left (hk : sideInArc a b k) (hx : sideInArc a k x) :
    sideInArc a b x := by
  unfold sideInArc at *
  grind
theorem sideInArc_sub_right (hk : sideInArc a b k) (hx : sideInArc k b x) :
    sideInArc a b x := by
  unfold sideInArc at *
  grind

/-- A cut `q` just after an inner key `k` bounds the part of the interval after `k`. -/
theorem sideInArc_before_cut {a b k q x : ℝ} (hk : sideInArc a b k) (hq : ¬ sideInArc a b q)
    (hkq : k < q) (hx : sideInArc k b x) : sideInArc k q x := by
  have hqk := fun h => hq (sideInArc_sub_right hk h)
  zujqz

/-- A cut `q` just before an inner key `k` bounds the part of the interval before `k`. -/
theorem sideInArc_after_cut {a b k q x : ℝ} (hk : sideInArc a b k) (hq : ¬ sideInArc a b q)
    (hqk' : q < k) (hx : sideInArc a k x) : sideInArc q k x := by
  have hqk := fun h => hq (sideInArc_sub_left hk h)
  zujqz

/-- An interval inside one walk edge meets at most that edge. -/
theorem arcWt_le_one_of_within (M : Model) {k : ℕ} {a b : ℝ} (hab : a < b) (ha : (k : ℝ) ≤ a)
    (hb : b ≤ k + 1) : M.arcWt a b ≤ 1 := by
  zujhb
  calc (M.arcEdges a b).ncard ≤ ({k} : Set ℕ).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.finite_singleton k)
        rintro p ⟨-, -, t, ht0, ht1, hx⟩
        zuhba
        rw [ite_eq_left hab] at hx
        have h1 : (p : ℝ) < k + 1 := by_grind
        zujyj
        have h1' : p < k + 1 := by exact_mod_cast h1
        zucgf
        grind
    _ = 1 := Set.ncard_singleton k
end WalkEmbed
open Chazelle.Chain (sideE)
namespace WalkEmbed
section ChainWalk
variable (C : Chain)

/-- The tour position of the box (a copy of the top vertex). -/
noncomputable def bS : ℕ := C.sideS C.sideBeta
theorem bS_le : bS C ≤ 2 * C.m := C.sideS_lt _

/-- The tour offset of the tour position `J` from the box. -/
noncomputable def tpos (J : ℕ) : ℕ := ztdyo % ztbb
theorem tpos_lt (J : ℕ) : tpos C J < 2 * C.m := Nat.mod_lt _ C.two_m_pos

/-- The vertex at step `d` of the Euler tour read from the tour position `J`. -/
noncomputable def tourV (J d : ℕ) : Point := C.vertex (sideE C.m ((J + d) % ztbb))

/-- The box block of the walk, read from the top vertex: the top, the top of the slit, the four
corners, the top of the slit and the top again. -/
noncomputable def boxPt : ℕ → Point
  | 0 => C.top
  | 1 => C.slitTop
  | 2 => ztvx
  | 3 => ztru
  | 4 => ztyn
  | 5 => ztbjg
  | 6 => C.slitTop
  | _ => C.top
theorem cm_W : (chainModel C).W = C.sideWalk C.sideBeta := rfl
theorem cm_n : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
theorem bS_add_tpos (J : ℕ) : bS C + tpos C J ≡ J [MOD 2 * C.m] := by
  unfold tpos
  have hb := bS_le C
  have e : (bS C + ztdyo % ztbb) % ztbb =
      (bS C + ztdyo) % ztbb := by_simp_all
  unfold Nat.ModEq
  rw [e, show bS C + ztdyo = J + 2 * C.m by omega, Nat.add_mod_right]

/-- **The walk read from a tour position**: before the box. -/
theorem walk_tour (J d : ℕ) (hd : tpos C J + d ≤ 2 * C.m) :
    (chainModel C).W.vtx ((6 + tpos C J + d) % (chainModel C).W.n) = tourV C J d := by
  rw [cm_n, Nat.mod_eq_of_lt by_omega, cm_W, show 6 + tpos C J + d = (tpos C J + d) + 6 by ring,
    C.sideWalk_vtx_tour _ hd]
  unfold Chain.sideTour tourV
  zuewl
  zugjz
  have h := (bS_add_tpos C J).add_right d
  unfold Nat.ModEq at h
  zulqu
  zubh
theorem box_mod {e : ℕ} (he0 : 1 ≤ e) (he : e ≤ 7) : (2 * C.m + 6 + e) % ztz = e - 1 := by
  zul
  omega

/-- **The walk read from a tour position**: the box block. -/
theorem walk_box (J e : ℕ) (he : e ≤ 7) :
    (chainModel C).W.vtx ((6 + tpos C J + ztbpe + e) % (chainModel C).W.n) =
      boxPt C e := by
  zudpi
  rw [cm_n, show 6 + tpos C J + ztbpe + e = 2 * C.m + 6 + e by omega, cm_W]
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · rw [Nat.mod_eq_of_lt by_omega, add_zero, C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m]
    rfl
  rw [box_mod C he0 he]
  interval_cases e <;> first | rfl | exact C.sideWalk_vtx_six _

/-- **The walk read from a tour position**: after the box. -/
theorem walk_after (J e : ℕ) (he : e ≤ 2 * C.m) :
    (chainModel C).W.vtx ((6 + tpos C J + ztbpe + 7 + e) % (chainModel C).W.n) =
      tourV C J (2 * C.m - tpos C J + e) := by
  zudpi
  rw [cm_n, show 6 + tpos C J + ztbpe + 7 + e = (e + 6) + ztz by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt by_omega, cm_W, C.sideWalk_vtx_tour _ he]
  unfold Chain.sideTour tourV
  zuewl
  zugjz
  -- `J + (2m - tpos) ≡ bS`
  have h1 := bS_add_tpos C J
  have h2 : J + ztbpe ≡ bS C [MOD 2 * C.m] := by
    apply Nat.ModEq.add_right_cancel' (tpos C J)
    rw [show J + ztbpe + tpos C J = J + 2 * C.m by omega]
    calc J + 2 * C.m ≡ J + 0 [MOD 2 * C.m] := by_simp_all
      _ = J := by_omega
      _ ≡ bS C + tpos C J [MOD 2 * C.m] := h1.symm
  have h3 := h2.add_right e
  unfold Nat.ModEq at h3
  zulqu
  tauto

/-- The top of the slit is not in the open box. -/
theorem slitTop_not_mem_box : C.slitTop ∉ Chain.box C.radius := fun h => by
  have := h.2
  simp only [Chain.slitTop, abs_of_pos C.radius_pos] at this
  simp_all
theorem corner_not_mem_box {a b : ℝ} (h : a = C.radius ∨ a = -C.radius) :
    (ztvk : Point) ∉ Chain.box C.radius := fun hb => by
  have := hb.1
  grind

/-- **Counted walk edges are the edges joining two points of the open box.** -/
theorem counted_iff_box {p : ℕ} (hp : p < (chainModel C).W.n) :
    (chainModel C).counted p ↔ (chainModel C).W.vtx p ∈ Chain.box C.radius ∧
      (chainModel C).W.vtx ztwkm ∈ Chain.box C.radius := by
  zukk
  zueyb
  show 6 ≤ p ∧ p < 2 * C.m + 6 ↔ _
  zugue
  constructor
  · zubf
    zuii
    rw [C.sideWalk_vtx_tour _ by_omega, show i + 6 + 1 = ztg + 6 by ring,
      Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_tour _ by_omega]
    exact ⟨C.set_subset_box ztxuz,
      C.set_subset_box ztxuz⟩
  · zubf
    zukr
    zubo
    rcases (show p ≤ 5 ∨ p = 2 * C.m + 6 by omega) with hp5 | rfl
    · interval_cases p
      · zulzt
      · zuleu
      · zuleu
      · zulev
      · zulev
      · zulzt
    · rw [box_mod C le_rfl by_omega] at h2
      exact slitTop_not_mem_box C h2

/-- The box block depends only on the top vertex and the box radius. -/
theorem boxPt_congr {C' : Chain} (ht : C.top = C'.top) (hR : C.radius = C'.radius) (e : ℕ) :
    boxPt C e = boxPt C' e := by
  unfold boxPt Chain.slitTop
  simp_all

/-- The top vertex starts the box block. -/
theorem boxPt_zero : boxPt C 0 = C.top := rfl
end ChainWalk

/-! ## Agreement of two chain walks along a common tour stretch -/
section TwoChains
variable {C C' : Chain} {J J' ℓ : ℕ}

/-- **Case N** (no box inside the stretch in either walk): the walks agree along the tour. -/
theorem agree_N (hT : ∀ e, e ≤ ℓ → tourV C J e = tourV C' J' e)
    (hs : ℓ ≤ 2 * C.m - tpos C J) (hs' : ℓ ≤ 2 * C'.m - tpos C' J') :
    Agree (chainModel C).W (chainModel C').W ztjgd ztjge ℓ := by
  zuip
  rw [walk_tour C J d (by have := tpos_lt C J; omega),
    walk_tour C' J' d (by have := tpos_lt C' J'; omega)]
  simp_all

/-- The top vertices agree when the boxes sit at the same offset of the stretch. -/
theorem top_eq_of_box (hT : ∀ e, e ≤ ℓ → tourV C J e = tourV C' J' e)
    (hss : 2 * C.m - tpos C J = 2 * C'.m - tpos C' J') (hsl : 2 * C.m - tpos C J ≤ ℓ) :
    C.top = C'.top := by
  have h1 := walk_box C J 0 by_omega
  have h2 := walk_box C' J' 0 by_omega
  have h3 := walk_tour C J ztbpe (by have := tpos_lt C J; omega)
  have h4 := walk_tour C' J' ztcks (by have := tpos_lt C' J'; omega)
  zvncl at h1 h2
  rw [boxPt_zero] at h1 h2
  simp_all

/-- **Case Sh** (the box at the same offset strictly inside the stretch of both walks): the walks
agree along the tour and the box. -/
theorem agree_Sh (hT : ∀ e, e ≤ ℓ → tourV C J e = tourV C' J' e) (hR : C.radius = C'.radius)
    (hℓ : ℓ ≤ 2 * C.m) (hℓ' : ℓ ≤ 2 * C'.m)
    (hss : 2 * C.m - tpos C J = 2 * C'.m - tpos C' J') (hsl : 2 * C.m - tpos C J < ℓ) :
    Agree (chainModel C).W (chainModel C').W ztjgd ztjge ztole := by
  have htop := top_eq_of_box hT hss hsl.le
  zudpi
  zukge
  set s := 2 * C.m - tpos C J with hs
  zuip
  rcases le_or_gt d s with h1 | h1
  · rw [walk_tour C J d by_omega, walk_tour C' J' d by_omega]
    grind
  rcases le_or_gt d ztyd with h2 | h2
  · obtain ⟨e, rfl⟩ : ∃ e, d = s + e := ⟨d - s, by_omega⟩
    have hb := walk_box C J e by_omega
    have hb' := walk_box C' J' e by_omega
    rw [show 6 + tpos C J + ztkei = 6 + tpos C J + ztbpe + e by omega, hb,
      show 6 + tpos C' J' + ztkei = 6 + tpos C' J' + ztcks + e by omega, hb']
    exact boxPt_congr C htop hR e
  · obtain ⟨e, rfl⟩ : ∃ e, d = s + 7 + e := ⟨d - s - 7, by_omega⟩
    have hb := walk_after C J e by_omega
    have hb' := walk_after C' J' e by_omega
    grind

/-- **Case G, first piece** (the box strictly inside the stretch of the second walk only): the
walks agree up to the box of the second walk. -/
theorem agree_G1 (hT : ∀ e, e ≤ ℓ → tourV C J e = tourV C' J' e)
    (hs : ℓ ≤ 2 * C.m - tpos C J) (hs' : 2 * C'.m - tpos C' J' < ℓ) :
    Agree (chainModel C).W (chainModel C').W ztjgd ztjge
      ztcks := by
  zuip
  rw [walk_tour C J d by_omega,
    walk_tour C' J' d (by have := tpos_lt C' J'; omega)]
  grind

/-- **Case G, second piece**: the walks agree from the box of the second walk (skipped) to the
end of the stretch. -/
theorem agree_G2 (hT : ∀ e, e ≤ ℓ → tourV C J e = tourV C' J' e) (hℓ' : ℓ ≤ 2 * C'.m)
    (hs : ℓ ≤ 2 * C.m - tpos C J) (hs' : 2 * C'.m - tpos C' J' < ℓ) :
    Agree (chainModel C).W (chainModel C').W
      ((6 + tpos C J + ztcks) % (chainModel C).W.n)
      ((6 + tpos C' J' + ztcks + 7) % (chainModel C').W.n)
      (ℓ - ztcks) := by
  zudpi
  zukge
  zuip
  rw [Nat.mod_add_mod, Nat.mod_add_mod, Nat.add_assoc _,
    walk_tour C J _ by_omega, walk_after C' J' d by_omega]
  grind
end TwoChains

/-! ## The tours of a junction -/
section Junction
variable (J : Merge.Junction)
variable {e : ℕ}
/-- **The left half of the tour**: the tour of `C₁` read from the shared vertex is the tour of
`C` read from the copy of the shared vertex left towards `C₁` (tour position `m₁ + 2 m₂`). -/
theorem tourV_left (he : e ≤ 2 * J.m₁) :
    tourV J.whole ztbv e = tourV J.left J.m₁ e := by
  zulch
  simp only [Merge.Junction.whole_m, Merge.Junction.left_m]
  zufz

  rw [Merge.Junction.whole_vertex]
  zucr
  rcases Nat.lt_or_ge e J.m₁ with h | h
  · rw [Nat.mod_eq_of_lt by_grind,
      Nat.mod_eq_of_lt by_grind]
    zumu
  · rw [Nat.mod_eq_sub_mod by_omega,
      Nat.mod_eq_of_lt by_grind,
      Nat.mod_eq_sub_mod by_omega,
      Nat.mod_eq_of_lt by_grind]
    zumu

/-- **The right half of the tour**: the tour of `C₂` read from the shared vertex (tour position
`0`) is the tour of `C` read from the copy of the shared vertex left towards `C₂` (tour position
`m₁`). -/
theorem tourV_right (he : e ≤ 2 * J.m₂) :
    tourV J.whole J.m₁ e = tourV J.right 0 e := by
  zulch
  simp only [Merge.Junction.whole_m, Merge.Junction.right_m, zero_add]
  zufz

  rw [Nat.mod_eq_of_lt by_grind]
  rcases Nat.lt_or_ge e ztgyh with h | h
  · zukp
    rcases le_or_gt e J.m₂ with h' | h'
    · have e1 : sideE ztom ztsyk = J.m₁ + e := by unfold sideE; simp_all
      have e2 : sideE J.m₂ e = e := by unfold sideE; simp_all
      zuihl
    · have e1 : sideE ztom ztsyk = J.m₁ + (2 * J.m₂ - e) := by
        zumu
      have e2 : sideE J.m₂ e = 2 * J.m₂ - e := by unfold sideE; simp_all
      zuihl
  · have he' : e = 2 * J.m₂ := by_omega
    zulta
    rw [Nat.mod_self]
    have e1 : sideE ztom ztbv = J.m₁ + 0 := by
      zumu
    tauto

/-- The shared vertex starts the left tour. -/
theorem tourV_left_zero : tourV J.left J.m₁ 0 = J.shared := by
  zulch
  simp only [Merge.Junction.left_m, add_zero]
  rw [Nat.mod_eq_of_lt (by have := J.one_le_m₁; omega)]
  unfold sideE; rw [ite_eq_left le_rfl]; rfl

/-- The shared vertex ends the left tour. -/
theorem tourV_left_end : tourV J.left J.m₁ (2 * J.m₁) = J.shared := by
  have := tourV_left_zero J
  unfold tourV at this ⊢
  simp_all

/-- The shared vertex starts the right tour. -/
theorem tourV_right_zero : tourV J.right 0 0 = J.shared := by
  rfl

/-- The shared vertex ends the right tour. -/
theorem tourV_right_end : tourV J.right 0 ztgyh = J.shared := by
  zulch
  simp only [zero_add, Merge.Junction.right_m, Nat.mod_self, Chain.sideE_zero]
  rfl

/-! ### Where the boxes are -/

/-- If the top of `C` lies strictly inside `C₁`, it is the top of `C₁`. -/
theorem left_topIdx_eq (h : J.whole.topIdx < J.m₁) : J.left.topIdx = J.whole.topIdx := by
  zueqr
  zudmc
  · refine J.left.topIdx_min ztnsx fun i hi => ?_
    rw [Merge.Junction.left_m] at hi
    rw [← Merge.Junction.whole_vertex, ← Merge.Junction.whole_vertex]
    exact J.whole.vertex_snd_le_top ztnsz
  · have hL := J.left.topIdx_le
    rw [Merge.Junction.left_m] at hL
    refine J.whole.topIdx_min ztnsz fun i hi => ?_
    calc (J.whole.vertex i).2 ≤ J.whole.top.2 := J.whole.vertex_snd_le_top hi
      _ = (J.left.vertex J.whole.topIdx).2 := rfl
      _ ≤ (J.left.vertex J.left.topIdx).2 :=
          J.left.vertex_snd_le_top ztnsx
      _ = (J.whole.vertex J.left.topIdx).2 := rfl

/-- If the top of `C` lies strictly inside `C₂`, it is the top of `C₂`. -/
theorem right_topIdx_eq (h : J.m₁ < J.whole.topIdx) :
    J.right.topIdx = J.whole.topIdx - J.m₁ := by
  zueqr
  rw [Merge.Junction.whole_m] at hT
  have hv : ztorr := fun j =>
    (Merge.Junction.whole_vertex_add J j).symm
  zudmc
  · refine J.right.topIdx_min ztnsy fun i hi => ?_
    rw [Merge.Junction.right_m] at hi
    rw [hv, hv, show J.m₁ + ztsyo = J.whole.topIdx by omega]
    exact J.whole.vertex_snd_le_top by_simp_all
  · have hR := J.right.topIdx_le
    rw [Merge.Junction.right_m] at hR
    suffices J.whole.topIdx ≤ J.m₁ + J.right.topIdx by omega
    refine J.whole.topIdx_min by_simp_all fun i hi => ?_
    calc (J.whole.vertex i).2 ≤ J.whole.top.2 := J.whole.vertex_snd_le_top hi
      _ = (J.right.vertex _).2 := by
          rw [hv, show J.m₁ + ztsyo = J.whole.topIdx by omega]; rfl
      _ ≤ (J.right.vertex J.right.topIdx).2 :=
          J.right.vertex_snd_le_top ztnsy
      _ = (J.whole.vertex _).2 := by zvmyq
theorem left_sideBeta_eq (h : J.whole.topIdx < J.m₁) : J.left.sideBeta = J.whole.sideBeta := by
  have e := left_topIdx_eq J h
  have htop : J.left.top = J.whole.top := by unfold Chain.top; tauto
  unfold Chain.sideBeta Chain.slitTop
  rw [htop, e]
  rfl
theorem right_sideBeta_eq (h : J.m₁ < J.whole.topIdx) : J.right.sideBeta = J.whole.sideBeta := by
  have e := right_topIdx_eq J h
  have hv : ztorr := fun j =>
    (Merge.Junction.whole_vertex_add J j).symm
  have hr : ztpkl := rfl
  have htop : J.right.top = J.whole.top := by
    unfold Chain.top; grind
  unfold Chain.sideBeta Chain.slitTop
  grind

/-- **The box of `C` inside the left stretch is the box of `C₁`**: if the box of the walk of `C`
lies strictly inside the stretch read from the copy of the shared vertex left towards `C₁`, then
the box of the walk of `C₁` lies at the same offset of the left tour. -/
theorem left_box_eq (h : 2 * J.whole.m - tpos J.whole ztbv < 2 * J.m₁) :
    2 * J.left.m - tpos J.left J.m₁ = 2 * J.whole.m - tpos J.whole ztbv := by
  zufz

  zueqr
  simp only [Merge.Junction.whole_m, Merge.Junction.left_m] at hT h ⊢
  unfold tpos bS Chain.sideS at *
  simp only [Merge.Junction.whole_m, Merge.Junction.left_m] at *
  -- the top of `C` is inside `C₁`
  have hTl : J.whole.topIdx < J.m₁ := by
    cases hb : J.whole.sideBeta <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    · zukr
      rw [Nat.mod_eq_sub_mod by_omega,
        Nat.mod_eq_of_lt by_omega] at h
      omega
    · rw [Nat.mod_eq_sub_mod by_omega,
        Nat.mod_eq_of_lt by_omega] at h
      omega
  rw [left_sideBeta_eq J hTl, left_topIdx_eq J hTl]
  cases hb : J.whole.sideBeta <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  · rw [Nat.mod_eq_of_lt (show J.m₁ + 2 * J.m₂ + 2 * ztom -
        ztzax < 2 * ztom by omega),
      Nat.mod_eq_of_lt by_grind]
    omega
  · rw [Nat.mod_eq_sub_mod (show 2 * ztom ≤
        J.m₁ + 2 * J.m₂ + 2 * ztom - J.whole.topIdx by omega),
      Nat.mod_eq_of_lt (show J.m₁ + 2 * J.m₂ + 2 * ztom - J.whole.topIdx -
        2 * ztom < 2 * ztom by omega),
      Nat.mod_eq_sub_mod by_omega,
      Nat.mod_eq_of_lt by_grind]
    omega

/-- **The box of `C` inside the right stretch is the box of `C₂`.** -/
theorem right_box_eq (h : 2 * J.whole.m - tpos J.whole J.m₁ < 2 * J.m₂) :
    2 * J.right.m - tpos J.right 0 = 2 * J.whole.m - tpos J.whole J.m₁ := by
  zufz

  zueqr
  simp only [Merge.Junction.whole_m, Merge.Junction.right_m] at hT h ⊢
  unfold tpos bS Chain.sideS at *
  simp only [Merge.Junction.whole_m, Merge.Junction.right_m] at *
  have hTr : J.m₁ < J.whole.topIdx := by
    cases hb : J.whole.sideBeta <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    · zukr
      rw [Nat.mod_eq_of_lt by_grind] at h
      omega
    · zukr
      rw [Nat.mod_eq_sub_mod by_omega,
        Nat.mod_eq_of_lt by_omega] at h
      omega
  have hTR := right_topIdx_eq J hTr
  rw [right_sideBeta_eq J hTr, hTR]
  cases hb : J.whole.sideBeta <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  · rw [Nat.mod_eq_of_lt (show J.m₁ + 2 * ztom -
        ztzax < 2 * ztom by omega),
      Nat.mod_eq_of_lt by_grind]
    omega
  · rw [Nat.mod_eq_of_lt (show J.m₁ + 2 * ztom - J.whole.topIdx < 2 * ztom by
        omega),
      Nat.mod_eq_of_lt by_grind]
    omega
end Junction
end WalkEmbed
open Chazelle.Geometry (lerp)
namespace ShootCut
@[simp] theorem param_hgt0 (M : Model) (Q : Polygon) (p : ℕ) : M.param Q ⟨p, 0⟩ = 0 := rfl
@[simp] theorem key_hgt0 (M : Model) (Q : Polygon) (p : ℕ) : M.key Q ⟨p, 0⟩ = p := by
  simp [Model.key]
theorem lerp_mem_segment {a b : Point} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    lerp a b t ∈ Chazelle.segment a b := ztopq

/-- **The point set of the key interval `[p₀, p₀ + w]`** (walk vertices, `w ≥ 1`): the union of
the segments of the walk edges `p₀, …, p₀ + w - 1`. -/
theorem arcSet_nat {M : Model} {p₀ w : ℕ} (hw : 1 ≤ w) (hn : p₀ + w < M.W.n) (x : Point) :
    x ∈ M.arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ) ↔
      ∃ d, d < w ∧ x ∈ Chazelle.segment (M.W.vtx zteur) (M.W.vtx (p₀ + d + 1)) := by
  have hab : (p₀ : ℝ) < ((p₀ + w : ℕ) : ℝ) := by exact_mod_cast (by omega : p₀ < p₀ + w)
  have hwb : ∀ p, p + 1 < M.W.n → M.wb p = M.W.vtx ztr := fun p hp => by
    unfold Model.wb; zuosz
  constructor
  · rintro ⟨p, t, hp, ht0, ht1, hc, rfl⟩
    have hrange : (p₀ : ℝ) ≤ p + t ∧ (p : ℝ) + t ≤ ((p₀ + w : ℕ) : ℝ) := by
      zuik
      · zucrg
      · simp_all
      simp_all
    push_cast at hrange
    by_cases hlo : p < p₀
    · -- `p = p₀ - 1`, `t = 1`: the vertex `p₀`
      have h1 : (p : ℝ) + 1 ≤ p₀ := by exact_mod_cast hlo
      zucmr
      have hpp : p + 1 = p₀ := by
        have : (p₀ : ℝ) ≤ p + 1 := by_linarith
        have : p₀ ≤ p + 1 := by exact_mod_cast this
        omega
      refine ⟨0, by_omega, 0, le_rfl, zero_le_one, ?_⟩
      zujpz
      rw [ht, hwb p by_omega, hpp]
      simp
    by_cases hhi : p₀ + w ≤ p
    · -- `p = p₀ + w`, `t = 0`: the vertex `p₀ + w`
      have h1 : ((p₀ + w : ℕ) : ℝ) ≤ p := by exact_mod_cast hhi
      zulnx
      zufwk
      have hpp : p = p₀ + w := by
        have : (p : ℝ) ≤ p₀ + w := by_linarith
        have : p ≤ p₀ + w := by exact_mod_cast this
        omega
      refine ⟨w - 1, by_omega, 1, zero_le_one, le_rfl, ?_⟩
      zujpz
      rw [ht, hpp, show p₀ + (w - 1) + 1 = p₀ + w by omega]
      simp
    · refine ⟨p - p₀, by_omega, t, ht0, ht1, ?_⟩
      zujpz
      rw [hwb p by_omega, show p₀ + (p - p₀) = p by omega]
      rfl
  · rintro ⟨d, hd, t, ht0, ht1, rfl⟩
    refine ⟨p₀ + d, t, by_omega, ht0, ht1, ?_, ?_⟩
    · have hk0 : (p₀ : ℝ) ≤ ((p₀ + d : ℕ) : ℝ) + t := by_grind
      have hk1 : ((p₀ + d : ℕ) : ℝ) + t ≤ ((p₀ + w : ℕ) : ℝ) := by
        have : ((d : ℕ) : ℝ) + 1 ≤ w := by exact_mod_cast hd
        grind
      rcases hk0.lt_or_eq with hk0 | hk0
      · rcases hk1.lt_or_eq with hk1 | hk1
        · zucnl
        simp_all
      grind
    · zujpz
      rw [hwb zteur by_omega]
      rfl

/-! ## Stretches along the tour of a chain -/
variable (Cα : Chain) {d : ℕ}
theorem tourV_up (hd : d ≤ Cα.m) : WalkEmbed.tourV Cα 0 d = Cα.vertex d := by
  unfold WalkEmbed.tourV
  have := Cα.one_le
  rw [zero_add, Nat.mod_eq_of_lt by_omega]
  zuhay
theorem tourV_down (hd : d ≤ Cα.m) :
    WalkEmbed.tourV Cα Cα.m d = Cα.vertex ztclf := by
  unfold WalkEmbed.tourV
  have := Cα.one_le
  rcases hd.lt_or_eq with hd | rfl
  · zuey
    zudma

  · rw [show Cα.m + Cα.m = 2 * Cα.m by ring, Nat.mod_self]
    unfold sideE; simp
theorem segment_mem_set (Cα : Chain) {k : ℕ} (hk : k < Cα.m) {x : Point}
    (hx : x ∈ Chazelle.segment ztpwz ztzbo) : x ∈ Cα.set :=
  ⟨k, hk, by rw [Cα.chainEdge_eq]; exact hx⟩

/-- **The point set of a kind-1 piece**: a stretch of `Cα.m` walk edges whose vertices are those
of the tour of `Cα` read upward (`J = 0`) or downward (`J = Cα.m`) has the point set `Cα.set`. -/
theorem arcSet_tour {M : Model} {Cα : Chain} {p₀ J : ℕ} (hJ : J = 0 ∨ J = Cα.m)
    (hn : p₀ + Cα.m < M.W.n)
    (hV : ∀ d, d ≤ Cα.m → M.W.vtx zteur = WalkEmbed.tourV Cα J d) :
    M.arcSet (p₀ : ℝ) ((p₀ + Cα.m : ℕ) : ℝ) = Cα.set := by
  zumax
  zumx
  rw [arcSet_nat h1 hn]
  rcases hJ with rfl | rfl
  · have hV' : ∀ d, d ≤ Cα.m → M.W.vtx zteur = Cα.vertex d := fun d hd => by
      rw [hV d hd, tourV_up Cα hd]
    constructor
    · zuifo
      rw [hV' d hd.le, show p₀ + d + 1 = p₀ + ztet by ring, hV' ztet hd] at hx
      exact segment_mem_set Cα hd hx
    · zuecq
      zugbv
      grind
  · have hV' : ∀ d, d ≤ Cα.m → M.W.vtx zteur = Cα.vertex ztclf := fun d hd => by
      rw [hV d hd, tourV_down Cα hd]
    constructor
    · zuifo
      rw [hV' d hd.le, show p₀ + d + 1 = p₀ + ztet by ring, hV' ztet hd,
        Chazelle.Geometry.segment_comm] at hx
      refine segment_mem_set Cα (k := Cα.m - ztet) by_omega ?_
      grind
    · zuecq
      zugbv
      refine ⟨Cα.m - zts, by_omega, ?_⟩
      rw [hV' _ by_omega, show p₀ + ztzte + 1 = p₀ + ztswh by omega,
        hV' _ by_omega, show Cα.m - ztzte = k + 1 by omega,
        show Cα.m - ztswh = k by omega, Chazelle.Geometry.segment_comm]
      zufsg

/-- **The walk of a kind-1 piece** (`PieceWalk`, finding E5): a stretch of `Cα.m` walk edges of
`M` agreeing with the tour of `Cα` read from any tour position `J`. -/
theorem pieceWalk_tour {M : Model} {Cα : Chain} {p₀ J : ℕ} (hp₀ : p₀ < M.W.n)
    (hV : ∀ d, d ≤ Cα.m → M.W.vtx ztzzr = WalkEmbed.tourV Cα J d) :
    PieceWalk M Cα zteyz ⟨(p₀ + Cα.m) % M.W.n, 0⟩ := by
  zudxx

  refine ⟨rfl, rfl, hp₀, rfl, ?_⟩
  by_cases hs : WalkEmbed.tpos Cα J + Cα.m ≤ 2 * Cα.m
  · refine ⟨6 + WalkEmbed.tpos Cα J, by_omega, Or.inl ?_⟩
    zuip
    zufng
  · set L₁ := 2 * Cα.m - WalkEmbed.tpos Cα J with hL₁
    refine ⟨6 + WalkEmbed.tpos Cα J, by_omega, Or.inr ⟨L₁, by_omega, by_omega, by_omega, ?_, ?_⟩⟩
    · zuip
      zufnf
    · zuip
      have e1 : ((p₀ + L₁) % M.W.n + d) % M.W.n = (p₀ + (L₁ + d)) % M.W.n := by
        grind
      have e2 : ztfmw % (chainModel Cα).W.n =
          (6 + WalkEmbed.tpos Cα J + ztbpf + 7 + d) %
            (chainModel Cα).W.n := by
        rw [hn', show 6 + WalkEmbed.tpos Cα J + ztbpf + 7 + d =
          ztfmw + ztgb by omega, Nat.add_mod_right]
      zudtr

/-! ## Weights in a chain model -/

/-- **The weight of a stretch of counted edges** in a chain model: `w`. -/
theorem arcWt_chain_nat (C : Chain) {p₀ w : ℕ} (hw : 1 ≤ w) (h6 : 6 ≤ p₀)
    (hn : p₀ + w ≤ 2 * C.m + 6) :
    (chainModel C).arcWt (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ) = w := by
  have h := (chainModel C).arcWt_closed (lo := 6) (hi := 2 * C.m + 6)
    ztmjw ztntf
    (ea := p₀) (eb := p₀ + w) (fa := 0) (fb := 0) ztuja ztuja
  simp only [add_zero] at h
  zuzx
  zuluc
  rw [ite_eq_left (by exact_mod_cast (by omega : p₀ < p₀ + w)), ite_eq_left rfl]
  omega
variable (M : Model)

/-- The walk points with a key congruent modulo `n` to a point of `[A, B]`. -/
def wset (A B : ℝ) : Set Point :=
  {x | ∃ p : ℕ, ∃ t : ℝ, p < M.W.n ∧ 0 ≤ t ∧ t ≤ 1 ∧
    (∃ X : ℝ, A ≤ X ∧ X ≤ B ∧ ∃ j : ℤ, (p : ℝ) + t = X + j * M.W.n) ∧
      x = lerp ztpr ztoa t}
theorem wset_union {A B C : ℝ} (hAB : A ≤ B) (hBC : B ≤ C) :
    wset M A B ∪ wset M B C = wset M A C := by
  zumx
  constructor
  · rintro (⟨p, t, hp, h0, h1, ⟨X, hX1, hX2, j, hj⟩, rfl⟩ | ⟨p, t, hp, h0, h1, ⟨X, hX1, hX2, j, hj⟩, rfl⟩)
    · exact ⟨p, t, hp, h0, h1, ⟨X, hX1, by_linarith, j, hj⟩, rfl⟩
    · exact zteyt
  · zudc
    by_cases hXB : X ≤ B
    · exact Or.inl ⟨p, t, hp, h0, h1, ⟨X, hX1, hXB, j, hj⟩, rfl⟩
    · exact Or.inr zteyt
theorem wset_shift (A B : ℝ) (i : ℤ) :
    wset M (A + i * M.W.n) (B + i * M.W.n) = wset M A B := by
  zumx
  constructor
  · zudc
    refine ⟨p, t, hp, h0, h1, ⟨X - i * M.W.n, by_linarith, by_linarith, j + i, ?_⟩, rfl⟩
    grind
  · zudc
    refine ⟨p, t, hp, h0, h1, ⟨X + i * M.W.n, by_linarith, by_linarith, j - i, ?_⟩, rfl⟩
    grind

/-- The last walk edge ends where the first begins. -/
theorem wb_last (hn : 0 < M.W.n) : M.wb (M.W.n - 1) = M.wa 0 := by
  unfold Model.wb Model.wa
  rw [Nat.sub_add_cancel hn, Nat.mod_self]

/-- The integer `j` of a key `y ∈ [0, n]` congruent to `X ∈ [0, 2n)`. -/
theorem int_range {n y X : ℝ} {j : ℤ} (hn : 0 < n) (hy0 : 0 ≤ y) (hy1 : y ≤ n)
    (hX0 : 0 ≤ X) (hX1 : X < 2 * n) (hj : y = X + j * n) :
    j = -1 ∨ j = 0 ∨ j = 1 := by
  have h1' : (j : ℝ) > -2 := by
    zubdi
  have h2' : (j : ℝ) ≤ 1 := by
    zubdi
  have h3 : j > -2 := by exact_mod_cast h1'
  have h4 : j ≤ 1 := by exact_mod_cast h2'
  omega

/-- **The point set of a closed cyclic key interval** as an unwrapped interval. -/
theorem arcSet_eq_wset {a b : ℝ} (ha : 0 ≤ a) (han : a < M.W.n) (hb : 0 ≤ b) (hbn : b < M.W.n) :
    M.arcSet a b = wset M a (if a < b then b else b + M.W.n) := by
  have hn : ztcfu := by_linarith
  have hn' : ztbiy := by_simp_all
  zumx
  constructor
  · rintro ⟨p, t, hp, h0, h1, hc, rfl⟩
    zucgv
    refine ztdxl
    split_ifs with hab
    · refine ⟨p + t, ?_, ?_, 0, by_simp⟩
      · zuik
        · zucrg
        · simp_all
        grind
      · zuik
        · zucrg
        · linarith
        simp_all
    · have hy : a ≤ (p : ℝ) + t ∨ (p : ℝ) + t ≤ b := by
        zuik
        · zucrg
        · simp_all
        simp_all
      rcases hy with hy | hy
      · exact ⟨p + t, hy, by_linarith, 0, by_simp⟩
      · exact ⟨p + t + M.W.n, by_grind, by_linarith, -1,
          by simp⟩
  · zudc
    zucgv
    have hy0 : 0 ≤ (p : ℝ) + t := by_positivity
    have hy1 : (p : ℝ) + t ≤ M.W.n := by_linarith
    -- the alias of the key `n`: the walk vertex `0`
    have halias : (p : ℝ) + t = M.W.n → lerp ztpr ztoa t = lerp (M.wa 0) (M.wb 0) 0 := by
      zufhz
      have ht1 : ztjar := by
        grind
      have hp1 : ztsku := by
        have : ztmrq := by_linarith
        have : ztiwq := by_grind
        have := (Nat.cast_inj (R := ℝ)).1 this
        omega
      rw [ht1, hp1, wb_last M hn']
      simp
    have hX3 : X < 2 * M.W.n := by_grind
    rcases int_range hn hy0 hy1 by_linarith hX3 hj with rfl | rfl | rfl
    · -- `j = -1`: `y = X - n`
      zujcg
      zulso
      · grind
      · refine ztdxl
        rcases (show (p : ℝ) + t < b ∨ (p : ℝ) + t = b by
          rcases lt_or_eq_of_le ztitk with h | h
          · simp_all
          · simp_all) with h | h
        · zucnl
        simp_all
    · -- `j = 0`: `y = X`
      zuggx
      refine ztdxl
      zulso
      · zujdz
        · rcases lt_or_eq_of_le ztitk with h' | h'
          · zucnl
          simp_all
        simp_all
      · zujdz
        · zucnl
        simp_all
    · -- `j = 1`: `y = X + n`, so `X = 0 = a` and `y = n`: the alias
      zujcg
      have hX0 : X = 0 := by_linarith
      have ha0 : a = 0 := by_linarith
      rw [halias by_linarith]
      refine ⟨0, 0, hn', le_rfl, zero_le_one, Or.inr ztmbv, rfl⟩

/-- The unwrapped length of the piece from key `k` to key `k'`. -/
noncomputable def len (n k k' : ℝ) : ℝ := if k < k' then k' - k else k' - k + n

/-- **One piece** (keys `k`, `k'` on the cycle, `k` unwrapped to `K = k + i n`). -/
theorem arcSet_step {k k' : ℝ} (hk : 0 ≤ k) (hkn : k < M.W.n) (hk' : 0 ≤ k') (hk'n : k' < M.W.n)
    (i : ℤ) :
    M.arcSet k k' = wset M (k + i * M.W.n) (k + i * M.W.n + len M.W.n k k') := by
  rw [arcSet_eq_wset M hk hkn hk' hk'n, show k + i * M.W.n + len M.W.n k k' =
    (if k < k' then k' else k' + M.W.n) + i * M.W.n by unfold len; split_ifs <;> ring,
    wset_shift]
variable (n k k' : ℝ)
theorem len_pos (hk : k < n) (hk' : 0 ≤ k') : 0 < len n k k' := by
  zuhaq
theorem len_le (hk : 0 ≤ k) (hk' : k' < n) : len n k k' ≤ n := by
  zuhaq

/-! ## Lists of pieces -/
end ShootCut
open Chazelle.Geometry (lerp_fst lerp_snd)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
namespace ShootCut
def subSeg (M : Model) (p : ℕ) (s₀ s₁ : ℝ) : Set Point :=
  {x | ∃ s, s₀ ≤ s ∧ s ≤ s₁ ∧ x = lerp ztpr ztoa s}
theorem wa_succ (M : Model) {p : ℕ} (hp : p + 1 < M.W.n) : M.wa ztr = M.wb p := by
  unfold Model.wa Model.wb; zuosz
variable (a b : Point)
theorem lerp_zero' : lerp a b 0 = a := by_simp
theorem lerp_one' : lerp a b 1 = b := by
  simp

/-- **An unwrapped key range inside one walk edge.** -/
theorem wset_edge (M : Model) {p : ℕ} (hp : p < M.W.n) {s₀ s₁ : ℝ} (h0 : 0 ≤ s₀) (h01 : s₀ ≤ s₁)
    (h1 : s₁ ≤ 1) (i : ℤ) :
    wset M (p + s₀ + i * M.W.n) (p + s₁ + i * M.W.n) = subSeg M p s₀ s₁ := by
  rw [wset_shift]
  have hn' : ztbiy := by_omega
  have hn : ztcfu := by_simp_all
  zucgv
  zumx
  constructor
  · rintro ⟨p', t, hp', ht0, ht1, ⟨X, hX1, hX2, j, hj⟩, rfl⟩
    have hp'n : ztgtp := by exact_mod_cast hp'
    have hy0 : 0 ≤ (p' : ℝ) + t := by_positivity
    rcases int_range hn hy0 by_linarith by_grind by_linarith hj with rfl | rfl | rfl
    · -- `j = -1`: `X = n`, so `p = n - 1`, `s₁ = 1`, and the position is the vertex `0`
      zujcg
      have hX : X = M.W.n := by_linarith
      have hpp : ztmrq := by_linarith
      have hs1 : s₁ = 1 := by_linarith
      have hp'0 : (p' : ℝ) = 0 ∧ t = 0 := by_grind
      have hp'0' : p' = 0 := by_simp_all
      have hpn1 : ztsku := by
        have : ztiwq := by_simp_all
        have := (Nat.cast_inj (R := ℝ)).1 this; omega
      refine ⟨1, by_linarith, by_linarith, ?_⟩
      rw [hp'0', hp'0.2, lerp_zero', lerp_one', hpn1, wb_last M hn']
    · zuggx
      -- `p' + t ∈ [p, p + 1]`
      have hlo : (p : ℝ) ≤ p' + t := by_linarith
      have hhi : (p' : ℝ) + t ≤ p + 1 := by_linarith
      have hp'1 : p' ≤ p + 1 := by
        have : (p' : ℝ) ≤ p + 1 := by_linarith
        zufc
      have hp'2 : p ≤ p' + 1 := by
        have : (p : ℝ) ≤ p' + 1 := by_linarith
        zufc
      rcases (show p' = p ∨ p' = p + 1 ∨ p' + 1 = p by omega) with rfl | rfl | h
      · exact ⟨t, by_linarith, by_linarith, rfl⟩
      · push_cast at hhi
        zufwk
        refine ⟨1, by_linarith, by_grind, ?_⟩
        rw [ht, lerp_zero', lerp_one', wa_succ M hp']
      · have hpR : (p : ℝ) = p' + 1 := by exact_mod_cast h.symm
        zucmr
        refine ztolh
        rw [ht, lerp_zero', lerp_one', ← h, wa_succ M by_omega]
    · -- `j = 1`: `X = 0`, so `p = 0`, `s₀ = 0`, and the position is the end of the last edge
      zujcg
      have hX : X = 0 := by_linarith
      have hp0 : (p : ℝ) = 0 := by_grind
      have hp0' : ztidy := by_simp_all
      have hs0 : s₀ = 0 := by_linarith
      have ht : ztjar := by
        grind
      have hp'n1 : p' = M.W.n - 1 := by
        have : ((p' + 1 : ℕ) : ℝ) = M.W.n := by_simp_all
        have := (Nat.cast_inj (R := ℝ)).1 this; omega
      refine ztolh
      rw [ht, lerp_zero', lerp_one', hp'n1, wb_last M hn', hp0']
  · rintro ⟨s, hs0, hs1, rfl⟩
    exact ⟨p, s, hp, by_linarith, by_linarith, ⟨p + s, by_linarith, by_linarith, 0, by_simp⟩, rfl⟩

/-! ## First hits on simple sets -/

/-- The parameter of the point at height `y` of the segment `[u, v]`. -/
noncomputable def hpar (u v : Point) (y : ℝ) : ℝ := ztuem / ztgv
theorem hpar_snd {u v : Point} (huv : u.2 ≠ v.2) (y : ℝ) : (lerp u v (hpar u v y)).2 = y := by
  unfold hpar
  zubzv
  grind

/-! ## Horizontal segments on the line of the ray -/
end ShootCut
open Chazelle.Visibility (xAt xAt_left xAt_right xAt_lerp edgeX)
namespace ShootCut
theorem goodEnv_distinct {P : Polygon} (hG : GoodEnv P) : DistinctHeights zta :=
  (goodShear_epsOf hG.2).2.1

/-- A point lies on the line through `u` and `w` (as a graph over the height). -/
def OnLine (u w a : Point) : Prop := a.1 = xAt u w a.2

/-- **Two points of a line define it.** -/
theorem xAt_eq_of_line {u w a b : Point} (huw : u.2 ≠ w.2) (hab : a.2 ≠ b.2) (ha : OnLine u w a)
    (hb : OnLine u w b) (y : ℝ) : xAt a b y = xAt u w y := by
  unfold OnLine at ha hb
  unfold xAt at ha hb ⊢
  grind

/-- **The edge of `Q` carrying a host edge** (for `HostEdgeOK` pairs). -/
def edgeOf (n : ℕ) : SymPt → SymPt → ℕ
  | .vtx i, .vtx j => if j = ztg % n then i else j
  | .vtx _, .onEdge e _ => e
  | .onEdge e _, _ => e
variable {Q : Polygon}
theorem vtx_onLine (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {e : ℕ} (he : e < Q.n) :
    OnLine ztgep ztbakx ztgep ∧
      OnLine ztgep ztbakx ztbakx := by
  have hne : ztbamn :=
    hD _ _ he ztcv (by
      zuq
      zukni
      · zupe
      · rw [h', Nat.mod_self] at h; omega)
  exact ⟨(xAt_left _ _).symm, (xAt_right hne).symm⟩

/-- The edges of `Q` are not horizontal. -/
theorem edge_nh (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {e : ℕ} (he : e < Q.n) :
    (Q.vtx e).2 ≠ (Q.vtx ztwki).2 :=
  hD _ _ he ztcv (by
      zuq
      zukni
      · zupe
      · rw [h', Nat.mod_self] at h; omega)

/-- **The symbolic points of a regular host edge lie on the line of its edge of `Q`.** -/
theorem hostEdge_onLine (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {sp₁ sp₂ : SymPt}
    (hl₁ : sp₁.Lt Q.n) (hl₂ : sp₂.Lt Q.n) (hok : HostEdgeOK Q.n sp₁ sp₂)
    (hnh : (sp₁.eval Q).2 ≠ (sp₂.eval Q).2) :
    edgeOf Q.n sp₁ sp₂ < Q.n ∧
      OnLine ztbafg ztihp ztwep ∧
      OnLine ztbafg ztihp ztweq := by
  have onE : ∀ e h, e < Q.n → OnLine ztgep ztbakx ((SymPt.onEdge e h).eval Q) :=
    fun e h _ => rfl
  cases sp₁ with
  | vtx i =>
    cases sp₂ with
    | vtx j =>
      zudby
      zueeq
      zuhtb
      · have e : edgeOf Q.n ztuwb ztmae = i := by zuonq
        zui
        subst hj
        exact ⟨hl₁, (vtx_onLine hD hn hl₁).1, (vtx_onLine hD hn hl₁).2⟩
      · have e : edgeOf Q.n ztuwb ztmae = j := by zuonq
        zui
        have hi : ztzqg := hok.resolve_left hj
        zuipx
        exact ⟨hl₂, (vtx_onLine hD hn hl₂).2, (vtx_onLine hD hn hl₂).1⟩
    | onEdge e h =>
      zudby
      zueeq
      refine ⟨hl₂.1, ?_, onE e h hl₂.1⟩
      zubuh
      · exact (vtx_onLine hD hn hl₂.1).1
      · exact (vtx_onLine hD hn hl₂.1).2
  | onEdge e h =>
    simp only [SymPt.Lt] at hl₁
    refine ⟨hl₁.1, onE e h hl₁.1, ?_⟩
    cases sp₂ with
    | vtx j =>
      zudby
      zubuh
      · exact (vtx_onLine hD hn hl₁.1).1
      · exact (vtx_onLine hD hn hl₁.1).2
    | onEdge e' h' =>
      zudby
      zubuh
      · tauto
      · rfl

/-- **A walk position at a vertex height on a non-horizontal regular host edge** is the symbolic
point `onEdge e h`, `e` the edge of `Q` carrying the host edge. -/
theorem pos_eq_onEdge (M : Model) (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {p h : ℕ}
    {sp₁ sp₂ : SymPt} (ha : M.wa p = sp₁.eval Q) (hb : M.wb p = sp₂.eval Q) (hl₁ : sp₁.Lt Q.n)
    (hl₂ : sp₂.Lt Q.n) (hok : HostEdgeOK Q.n sp₁ sp₂) (hnh : (M.wa p).2 ≠ (M.wb p).2) :
    M.pos Q ztdw = (SymPt.onEdge ztlnf h).eval Q := by
  rw [ha, hb] at hnh
  obtain ⟨he, h1, h2⟩ := hostEdge_onLine hD hn hl₁ hl₂ hok hnh
  have hQnh := edge_nh hD hn he
  unfold Model.pos Model.param
  zubi
  rw [ite_eq_right by_simp_all, ha, hb]
  have hy : (lerp ztwep ztweq
      ztdrp).2 = (Q.vtx h).2 :=
    hpar_snd hnh _
  have hx := xAt_lerp hnh ztdrp
  rw [hy, xAt_eq_of_line hQnh hnh h1 h2] at hx
  ext
  · tauto
  tauto

/-! ## Shifting the origin along the ray line -/

/-- **Shifting the origin**: if every point of `S` on the ray line is strictly ahead of both `z`
and `z'` (same height), the first hits from `z` and `z'` correspond. -/
theorem firstHit_shift {S : Set Point} {z z' : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hy : z.2 = z'.2) (hahead : ∀ x ∈ S, x.2 = z.2 → 0 < σ * (x.1 - z.1) ∧ 0 < σ * (x.1 - z'.1)) :
    ztxcv ∧
      ztlfk := by
  zudps
  have key : ∀ t, rayPt z σ t = rayPt z' σ ztzhh := by
    zujbn
    ext
    · zudch
    tauto
  -- parameters of points of `S` on the line
  have ahead_z : ∀ t, rayPt z σ t ∈ S → 0 < t := by
    zucj
    have := (hahead _ ht rfl).1
    zudv
    have : σ * (σ * t) = t := by_grind
    nlinarith
  refine ⟨fun t' ht' => ⟨?_, ?_, fun s hs1 hs2 hsS => ?_⟩, fun hN t ht hS => ?_⟩
  · apply ahead_z
    zueyx
  · zueyx
  · rw [key] at hsS
    have hpos : 0 < s - σ * ztdir := by
      have := (hahead _ hsS by_tauto).2
      zudv
      have e : σ * (σ * (s - σ * ztdir)) = s - σ * ztdir := by
        grind
      nlinarith
    exact ht'.2.2 _ hpos by_linarith hsS
  · rw [key] at hS
    have hpos : 0 < t - σ * ztdir := by
      have := (hahead _ hS by_tauto).2
      zudv
      have e : σ * (σ * ztzhh) = t - σ * ztdir := by
        grind
      nlinarith
    tauto
theorem wt_within (M : Model) {e : ℕ} {a b : ℝ} (hab : a < b) (ha : (e : ℝ) ≤ a)
    (hb : b ≤ e + 1) : M.arcWt a b ≤ 1 :=
  WalkEmbed.arcWt_le_one_of_within M hab ha hb

/-- The key of a position of the walk proper lies in `[edge, edge + 1)`. -/
theorem key_bounds {M : Model} {Q : Polygon} {n : ℕ} {x : WPos} (hx : ProperPos M Q n x) :
    (x.edge : ℝ) ≤ M.key Q x ∧ M.key Q x < x.edge + 1 := by
  zuhqn
  exact ⟨by zungt, by zunsm⟩
variable (M : Model) (Q : Polygon) {n : ℕ}
/-- **From a position to the end of its edge** (a walk vertex). -/
theorem wt_to_next {x : WPos} (hx : ProperPos M Q n x) :
    M.arcWt ztbys ((x.edge + 1 : ℕ) : ℝ) ≤ 1 := by
  have := key_bounds hx
  exact wt_within M (e := x.edge) by_simp_all this.1 by_simp

/-- **From the start vertex of an edge to a position strictly inside it.** -/
theorem wt_from_start {y : WPos} (hy : ProperPos M Q n y)
    (hpos : 0 < M.param Q y) : M.arcWt (y.edge : ℝ) ztfof ≤ 1 := by
  have := key_bounds hy
  exact wt_within M (e := y.edge) (by unfold Model.key; linarith) le_rfl this.2.le

/-- **Two positions of one edge, in order.** -/
theorem wt_same {x y : WPos} (hx : ProperPos M Q n x)
    (hy : ProperPos M Q n y) (he : x.edge = y.edge) (hlt : M.key Q x < M.key Q y) :
    M.arcWt ztbys ztfof ≤ 1 := by
  have h1 := key_bounds hx
  have h2 := key_bounds hy
  zvndl at h2
  exact wt_within M (e := x.edge) hlt h1.1 h2.2.le

/-! ## The uncounted block -/
variable (C : Chain)

/-- The walk edge `p` lies in the uncounted block `U` (`2m + 6` or `0 … 5`). -/
def InU (p : ℕ) : Prop := p ≤ 5 ∨ p = 2 * C.m + 6

/-- The weight of a chain model in closed form, for positions of the walk proper. -/
theorem arcWt_chain (Q : Polygon) {n : ℕ} {x y : WPos} (hx : ProperPos ztc Q n x)
    (hy : ProperPos ztc Q n y) :
    (chainModel C).arcWt ztlb ztov =
      arcWtNat 6 ztcc x.edge ztuy y.edge
        ztqq :=
  (chainModel C).arcWt_key ztmjw
    ztntf Q ztuip ⟨hy.1, hy.2.1⟩
theorem keyCeil_le (e : ℕ) (f : ℝ) : keyCeil e f ≤ e + 1 := by
  zufdj
theorem le_keyCeil (e : ℕ) (f : ℝ) : e ≤ keyCeil e f := by
  zufdj

/-- The vertex position `⟨p, 0⟩` is proper. -/
theorem proper_vtx (M : Model) (Q : Polygon) (n p : ℕ) : ProperPos M Q n ztcye :=
  ⟨le_rfl, by_simp, Nat.zero_le _⟩

/-- **From a position of `U` to the walk vertex `6`**: weight `0`. -/
theorem wt_U_to_six (Q : Polygon) {n : ℕ} {x : WPos} (hx : ProperPos ztc Q n x)
    (hU : InU C x.edge) :
    (chainModel C).arcWt ztlb (6 : ℕ) = 0 := by
  have e6 : ((6 : ℕ) : ℝ) = (chainModel C).key Q ztbcw := by_simp
  rw [e6, arcWt_chain C Q hx (proper_vtx _ Q n 6)]
  have hc := le_keyCeil 6 ztxjq
  have hc' := keyCeil_le 6 ztxjq
  have hk : keyCeil 6 ztxjq = 6 := by
    zumtf
  unfold arcWtNat
  zujja
  zus
  · omega
  · zufzr
    · exfalso
      zuhrs
      have : (x.edge : ℝ) + 1 ≤ 6 := by exact_mod_cast (by omega : x.edge + 1 ≤ 6)
      zujor
      push_cast
      zunsm
    omega

/-- **From the walk vertex `2m + 5` to a position of `U`**: weight at most `1`. -/
theorem wt_last_to_U (Q : Polygon) {n : ℕ} {y : WPos} (hy : ProperPos ztc Q n y)
    (hU : InU C y.edge) :
    (chainModel C).arcWt ((2 * C.m + 5 : ℕ) : ℝ) ztov ≤ 1 := by
  have e5 : ((2 * C.m + 5 : ℕ) : ℝ) = (chainModel C).key Q ⟨2 * C.m + 5, 0⟩ := by_simp
  rw [e5, arcWt_chain C Q (proper_vtx _ Q n _) hy]
  zurs

  zubt
  unfold arcWtNat
  zubvt
  zus
  · omega
  · zufzr
    · omega
    · exfalso
      zuhrs
      zujor
      zulpt

      linarith [hy.1]

/-- The order of the uncounted block: `2m + 6` first, then `0, …, 5`. -/
def uIdx (p : ℕ) : ℕ := if p = 2 * C.m + 6 then 0 else p + 1

/-- **Two positions of `U` in walk order** (on different edges, the second later in `U`):
weight `0`. -/
theorem wt_U_U (Q : Polygon) {n : ℕ} {x y : WPos} (hx : ProperPos ztc Q n x)
    (hy : ProperPos ztc Q n y) (hxU : InU C x.edge) (hyU : InU C y.edge)
    (hlt : uIdx C x.edge < uIdx C y.edge) :
    (chainModel C).arcWt ztlb ztov = 0 := by
  zuigz
  zurs

  zubt
  have hx1 := hx.2.1
  have hy0 := hy.1
  unfold uIdx at hlt
  unfold arcWtNat
  rcases hxU with hxU | hxU <;> rcases hyU with hyU | hyU
  · rw [ite_eq_right (by omega : x.edge ≠ 2 * C.m + 6), ite_eq_right (by omega : y.edge ≠ 2 * C.m + 6)] at hlt
    have : ztddx := by exact_mod_cast (by omega : x.edge + 1 ≤ y.edge)
    grind
  · simp_all
  · grind
  simp_all
end ShootCut
open Metric
open Chazelle.Chain (sideLeftOf sideCcw sideCross sideDot TouchesIn freeIn regionsIn)
namespace FuseDeg
variable {M : Model}

/-- The exit chords of a region. -/
def exits (M : Model) (F : Set ztf) (R : Set Point) : Set ztf :=
  {c | c ∈ F ∧ TouchesIn M.D c R}

/-- A region is faced just after the key `k`. -/
def FacedAfter (M : Model) (R : Set Point) (p : ℕ) (t : ℝ) : Prop :=
  ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p ztuf R

/-- A region is faced just before the key `k`. -/
def FacedBefore (M : Model) (R : Set Point) (p : ℕ) (t : ℝ) : Prop :=
  ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces p ztfuw R

/-- **A region is on one side of each chord**: it cannot face positions on both sides of the two
attachments of a chord. -/
theorem sep_false (hM : WalkAx M) {F : Set ztf} {c : Set Point} (hc : c ∈ F)
    (hcA : c ∈ M.Adm) {pa pb : ℕ} {ta tb : ℝ} (hA : SideAttach M.W c pa ta)
    (hB : SideAttach M.W c pb tb) (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) {R : Set Point}
    (hR : R ∈ M.regions F) {p p' : ℕ} {t t' : ℝ} (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hin : sideInArc ztbf ztbd ztk) (hf : M.Faces p t R) (hp' : p' < M.W.n)
    (ht' : t' ∈ Ioo (0 : ℝ) 1) (hin' : sideInArc ztbd ztbf ztjg)
    (hf' : M.Faces p' t' R) : False := by
  obtain ⟨K₁, K₂, hne, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hK₁, hK₂⟩ := hM.split hcA hA hB hAB
  have hU1 := hM.region_subset_of_sector hc hR hp ht hf ztoaj
  have hU2 := hM.region_subset_of_sector hc hR hp' ht' hf' (hK₂ p' hp' t' ht'.1.le ht'.2 hin')
  obtain ⟨u, hu⟩ := Chazelle.Chain.regionsIn_nonempty hR
  exact hne ztdas

/-- The keys just before the end of an interval are inside it. -/
theorem eventually_before_end {l r : ℝ} (_hlr : l ≠ r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc l r zttxh := by
  zufdq
  zus
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT ztto]
      with ε hε hε'
    grind
  · zulg
    simp_all
variable {F : Set (Set Point)} {R : Set Point} {p : ℕ} {A : Set Point}
theorem faced_after {t r : ℝ} (hp : p < M.W.n)
    (ht : 0 ≤ t) (ht1 : t < 1) (harc : M.IsArc F R ztk r) (hne : (p : ℝ) + t ≠ r) :
    FacedAfter M R p t := by
  unfold FacedAfter
  filter_upwards [WalkAx.exists_pos_after ht ht1, WalkAx.eventually_after_start hne]
    with s h1 h2
  exact harc.2.2.2.2.2.2 p _ hp h1.1 h1.2 by_grind
theorem faced_before {t l : ℝ} (hp : p < M.W.n)
    (ht : 0 < t) (ht1 : t < 1) (harc : M.IsArc F R l ztk) (hne : l ≠ (p : ℝ) + t) :
    FacedBefore M R p t := by
  unfold FacedBefore
  filter_upwards [eventually_before_end hne, Ioo_mem_nhdsGT ht] with s h1 h2
  refine harc.2.2.2.2.2.2 p _ hp by_simp_all by_grind ?_
  grind

/-! ## Chords at one position -/
set_option hygiene false
local macro "zqiq" : tactic => `(tactic| exact ⟨div_pos by_linarith by_linarith, (div_lt_one by_linarith).2 by_linarith⟩)
local macro "zqir" : tactic => `(tactic| (unfold sideCcw sideCross sideDot at hX; rw [hE2, hW2] at hX; rcases hX with ⟨h1, -, -⟩ | ⟨h1, -⟩ | ⟨-, -, h3⟩ | ⟨-, h2, -⟩))
local macro "zqis" : tactic => `(tactic| rcases hX with ⟨-, -, h3⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> nlinarith)
local macro "zqit" : tactic => `(tactic| rcases hX with ⟨-, h2, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> nlinarith)
local macro "zqiu" : tactic => `(tactic| rcases lt_trichotomy e₁.1 e₂.1 with h | h | h)
local macro "zqiv" : tactic => `(tactic| (rintro x ⟨⟨p, t, hA, rfl⟩, -⟩; exact hM.trace p hA.1 t hA.2.1 hA.2.2.1.le))
local macro "zqiw" : tactic => `(tactic| (zvmxy; apply hop; rcases hbtw with ⟨h1, h2⟩ | ⟨h1, h2⟩))
local macro "zqix" : tactic => `(tactic| filter_upwards [ev2] with s hs)
local macro "zqiy" : tactic => `(tactic| filter_upwards [ev1] with s hs)
local macro "zqiz" : tactic => `(tactic| (rw [h1, mul_zero, add_zero] at I1; by_contra hc2; push Not at hc2; nlinarith))
set_option hygiene true
/-- An attached admissible chord from the point `a` in the horizontal direction of `x`. -/
theorem sameDir_eq (hM : WalkAx M) {c c' : Set Point} (hc : c ∈ M.Adm) (hc' : c' ∈ M.Adm)
    {p p' : ℕ} {t t' : ℝ} (hA : SideAttach M.W c p t) (hA' : SideAttach M.W c' p' t')
    (hpt : sidePt M.W p t = sidePt M.W p' t')
    (hdir : ∀ q q' : Point, q ∈ c → q' ∈ c' → q ≠ sidePt M.W p t → q' ≠ sidePt M.W p t →
      ((sidePt M.W p t).1 < q.1 ↔ (sidePt M.W p t).1 < q'.1)) : c = c' := by
  obtain ⟨e₁, hce₁, hne₁, hy₁, hop₁, hD₁⟩ := hM.chord_from hc hA
  obtain ⟨e₂, hce₂, hne₂, hy₂, hop₂, hD₂⟩ := hM.chord_from hc' hA'
  zvnbr at hce₂ hne₂ hy₂ hop₂
  set a := sidePt M.W p t
  have key : ∀ {f f' : Point},
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp a f s ∈ M.D) → f' ∉ M.D → f.2 = a.2 → f'.2 = a.2 →
      ((a.1 < f'.1 ∧ f'.1 < f.1) ∨ (f.1 < f'.1 ∧ f'.1 < a.1)) → False := by
    zucxd

    have e1 : f' = lerp a f ((f'.1 - a.1) / (f.1 - a.1)) := by
      have hfe : f.1 - a.1 ≠ 0 := by
        grind
      zufqm
      · zufau
      · zudbx
    zqiw
    · zqiq
    · exact ⟨div_pos_of_neg_of_neg by_linarith by_linarith,
        (div_lt_one_of_neg by_linarith).2 by_linarith⟩
  have hsame := hdir e₁ e₂ (by rw [hce₁]; exact Geometry.right_mem_segment _ _)
    (by rw [hce₂]; exact Geometry.right_mem_segment _ _) hne₁ hne₂
  have hx₁ : e₁.1 ≠ a.1 := by_grind
  have hx₂ : e₂.1 ≠ a.1 := by_grind
  have heq : ztsil := by
    zulvo
    zuevp
    · have h₂ : e₂.1 < a.1 := by
        grind
      zqiu
      · grind
      · zubh
      grind
    · zuhfz
      zqiu
      · grind
      · zubh
      grind
  grind

/-- The far point of an attached chord leaves the position into its left sector. -/
theorem sideLeft_far (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) {q : Point} (hq : q ∈ c) (hqa : q ≠ sidePt M.W p t) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), sideLeft M.W p t ztyfg := by
  obtain ⟨e₁, hce₁, hne₁, -, -, -⟩ := hM.chord_from hc hA
  zuddt
  have hqs : ∀ s ∈ Icc (0 : ℝ) 1, lerp ztbp q s ∈ c := by
    zugg
    zubwm
    rw [hce₁] at hq' ⊢
    obtain ⟨u, hu0, hu1, hqu⟩ := Geometry.mem_segment_iff_lerp.1 hq'
    have : lerp ztbp q s = lerp ztbp e₁ zttzb := by
      rw [hqu]; apply Geometry.point_ext <;> zundk <;> ring
    zubk
    exact Geometry.lerp_mem_segment _ _ ztqer ztepr
  have hd : 0 < dist q _ := dist_pos.2 hqa
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (r / dist q
    _) from lt_min one_pos (div_pos hr hd))] with s hs hs'
  zufwh
  refine hl _ by_grind ?_ ?_
  · zuq
    have : lerp ztbp q s = lerp ztbp q 0 := by_simp_all
    have := Geometry.lerp_injective (Ne.symm hqa) this
    linarith
  · have e : dist ztyfg ztbp = s * dist q ztbp := by
      zuecv
      have : sidePt M.W p t - lerp ztbp q s = s • (sidePt M.W p t - q) := by
        zuhbe
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, norm_sub_rev]
    zui
    have h2 : s < r / dist q _ := hs'.2.trans_le ztgh
    calc s * dist q _ < r / dist q _ * dist q _ :=
          mul_lt_mul_of_pos_right h2 hd
      _ = r := div_mul_cancel₀ _ hd.ne'

/-- **At a position inside a walk edge at most one chord is attached.** -/
theorem one_chord_interior (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) {c c' : Set Point}
    (hc : c ∈ F) (hc' : c' ∈ F) {p : ℕ} {t : ℝ} (ht : 0 < t) (hA : SideAttach M.W c p t)
    (hA' : SideAttach M.W c' p t) : c = c' := by
  zuerz
  zumew
  zund
  set u := M.W.vtx p
  set v := M.W.vtx ztwjk
  -- the side of a point of a chord leaving the position
  have hside : ∀ d ∈ M.Adm, SideAttach M.W d p t → ∀ q ∈ d, q ≠ sidePt M.W p t →
      0 < -ztbaas := by
    intro d hd hAd q hq hqa
    obtain ⟨e₁, hce₁, hne₁, hy₁, -, -⟩ := hM.chord_from hd hAd
    have hqy : q.2 = (sidePt M.W p t).2 := by
      rw [hce₁] at hq
      obtain ⟨s, -, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hq
      simp_all
    obtain ⟨s, hs1, hs2⟩ := ((sideLeft_far hM hd hAd hq hqa).and self_mem_nhdsWithin).exists
    rw [Chazelle.Chain.sideLeft_edge hne ztuih] at hs1
    zumeu
    have hpt : sidePt M.W p t = lerp u v t := rfl
    have e : det u v ztyfg =
        s * -ztbaas := by
      zulbn
      zubzm
      rw [hqy, hpt]
      zubzm
      ring
    zvmwe at hs1
    exact pos_of_mul_pos_right hs1 hs0.le
  refine sameDir_eq hM ztlz ztesy hA hA' rfl fun q q' hq hq' hqa hq'a => ?_
  have h1 := hside c ztlz hA q hq hqa
  have h2 := hside c' ztesy hA' q' hq' hq'a
  constructor
  · zuq
    zudxc
    zugrd

    · nlinarith
    grind
  · zuq
    zudxc
    zugrd

    · nlinarith
    simp_all

/-- **A region touching the only chord at an attachment is faced next to it.** -/
theorem sides_single (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {e : Set Point} (he : e ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W e p t)
    (hsole : ∀ c' ∈ F, SideAttach M.W c' p t → c' = e) {R : Set Point} (hR : R ∈ M.regions F)
    (hRe : TouchesIn M.D e R) :
    ztwxj ∨ ztwxi := by
  obtain ⟨U, V, l, r, hU, hV, hUV, harcU, harcV, htouch⟩ := hM.attach_face hF hfin he hA
  obtain ⟨hUe, hVe⟩ := htouch hsole
  obtain ⟨Up, Dn, -, -, -, -, hiff⟩ := chordSides_of_system ztbip he
  have hR' := (hiff R hR).1 hRe
  have hU' := (hiff U hU).1 hUe
  have hV' := (hiff V hV).1 hVe
  grind

/-! ## Two chords at a walk vertex: the wedge -/

/-- Near a point, the chords of a finite admissible family lie on the horizontal line of the
point. -/
theorem chords_off_line (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (a : Point) : ∃ r > 0, ∀ x ∈ ball a r, x.2 ≠ a.2 → x ∉ ⋃₀ F := by
  have hev : ∀ᶠ x in 𝓝 a, ∀ c ∈ F, a ∉ c → x ∉ c := by
    refine (Filter.eventually_all_finite hfin).2 fun c hc => ?_
    zujsy
    · simp_all
    · obtain ⟨u, w, -, rfl, -, -, -, -⟩ := hM.ends c ztlz
      have hcl : IsClosed (Chazelle.segment u w) := Geometry.isClosed_segment _ _
      filter_upwards [hcl.isOpen_compl.mem_nhds hac] with x hx _ using hx
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨r, hr, fun x hx hxy ⟨c, hc, hxc⟩ => ?_⟩
  zujsy
  · obtain ⟨u, w, -, rfl, huw, -, -, -⟩ := hM.ends c ztlz
    have hy : ∀ z ∈ Chazelle.segment u w, z.2 = u.2 := by
      zugh
      obtain ⟨s, -, -, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hz
      zudbx
    grind
  simp_all

/-- **A sector part of a walk corner is a preconnected free set** when it lies in the left
sector of the walk at a vertex and off the horizontal line of the vertex. -/
theorem sector_side (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {p : ℕ} (hp : p < M.W.n) {a' b' : Point} (ha' : a' ≠ M.W.vtx p) (hb' : b' ≠ M.W.vtx p)
    (hsub : ∀ X : Point, sideCcw (b' - M.W.vtx p) X (a' - M.W.vtx p) →
      sideCcw (sideNext M.W p - M.W.vtx p) X (sidePrev M.W p 0 - M.W.vtx p) ∧ X.2 ≠ 0) :
    ∃ Sg : Set Point, Chazelle.Jordan.SectorSide (freeIn M.D F)ᶜ Sg a' ztoy b' 1 := by
  zuhog
  zuebj
  obtain ⟨r₂, hr₂, hch⟩ := chords_off_line hM hF hfin a
  zuhzx
  refine ⟨_, Chazelle.Chain.sideSector ha' hb' ztftb fun x hx hxS hl => hxS ?_⟩
  obtain ⟨hw, hne⟩ := hsub _ hl
  have hx1 : x ∈ ball ztfs r₁ := by
    zvmxe; exact ball_subset_ball ztff hx
  have hx2 := ball_subset_ball ztgh hx
  have hxD : x ∈ M.D := by
    zuhtn
    apply hcl x hx1 hnd
    zuhrd
    grind
  refine ⟨hxD, fun hxF => hch x hx2 (fun h => hne ?_) hxF⟩
  simp only [Prod.snd_sub]; grind

/-- Regions meeting both ends of a sector part coincide. -/
theorem sector_regions_eq {Sg : Set Point} {a' v b' : Point}
    (hSg : Chazelle.Jordan.SectorSide (freeIn M.D F)ᶜ Sg a' v b' 1) {X Y : Set Point}
    (hX : X ∈ M.regions F) (hY : Y ∈ M.regions F)
    (hXo : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Chazelle.Jordan.offset a' v zteb δ ∈ X)
    (hYo : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Chazelle.Jordan.offset v b' s δ ∈ Y) : X = Y := by
  obtain ⟨hSgS, hSgc, hoff⟩ := hSg
  have hSgF : Sg ⊆ freeIn M.D F := by_simp_all
  obtain ⟨s, ⟨h1, h2⟩, h3⟩ := ((hoff.and hXo).and hYo).exists
  obtain ⟨δ, ⟨⟨d1, d2⟩, d3⟩, d4⟩ := ((h1.and h2).and h3).exists
  zvohi at d1 d2
  have hSgX := Chazelle.Chain.subset_regionsIn_of_inter hX hSgc hSgF ⟨_, d1, d3⟩
  have hSgY := Chazelle.Chain.subset_regionsIn_of_inter hY hSgc hSgF ⟨_, d2, d4⟩
  rcases Chazelle.Chain.regionsIn_eq_or_disjoint hX hY with h | h
  · zubh
  grind

/-- Offsets of a horizontal segment are vertical translates of its points. -/
theorem offset_horiz {u v : Point} (huv : u.2 = v.2) (t δ : ℝ) :
    Chazelle.Jordan.offset u v t δ =
      ((lerp u v t).1, (lerp u v t).2 + δ * ztmu) := by
  zufqm
  · rw [Chazelle.Jordan.offset_fst]; simp_all
  rfl

/-- **The offsets of a horizontal chord piece lie in its side regions.** -/
theorem offsets_side {d Up Dn : Set Point}
    (hside : ∀ z ∈ d, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (ztcxe : Point) ∈ Up ∧ (ztcxf : Point) ∈ Dn)
    {u v : Point} (huv : u.2 = v.2) (hseg : ∀ s ∈ Ioo (0 : ℝ) 1, lerp u v s ∈ d ∧ lerp u v s ∈ M.D)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    (0 < v.1 - u.1 → ∀ᶠ δ in 𝓝[>] (0 : ℝ), Chazelle.Jordan.offset u v s δ ∈ Up) ∧
      (v.1 - u.1 < 0 → ∀ᶠ δ in 𝓝[>] (0 : ℝ), Chazelle.Jordan.offset u v s δ ∈ Dn) := by
  obtain ⟨hzd, hzD⟩ := hseg s hs
  have h := hside _ hzd hzD
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · filter_upwards [eventually_mul_pos (h.mono fun _ h => h.1) hw] with δ hδ
    zuory; exact hδ
  · filter_upwards [eventually_mul_pos (h.mono fun _ h => h.2) (neg_pos.2 hw)] with δ hδ
    zuory
    grind

/-- The sign case at a vertex whose left sector contains both horizontal directions. -/
theorem sign_case {b c E W : Point} (hE2 : E.2 = 0) (hE1 : 0 < E.1) (hW2 : W.2 = 0) (hW1 : W.1 < 0)
    (hbE : sideCcw b E c) (hbW : sideCcw b W c) (hb : b ≠ 0) (_hc : c ≠ 0) :
    (b.2 < 0 ∧ c.2 < 0) ∨ (0 < b.2 ∧ 0 < c.2) := by
  have hbb := Chazelle.Chain.sideDot_self_pos hb
  unfold sideCcw sideCross sideDot at *
  rw [hE2] at hbE
  rw [hW2] at hbW
  have hbq : 0 < b.1 ^ 2 + b.2 ^ 2 := by_nlinarith
  have I1 : c.2 * (b.1 ^ 2 + b.2 ^ 2) =
      (b.1 * c.1 + b.2 * c.2) * b.2 + b.1 * (b.1 * c.2 - b.2 * c.1) := by_ring
  rcases lt_trichotomy b.2 0 with hb2 | hb2 | hb2
  · left
    refine ztuhd
    rcases hbW with ⟨-, h2, -⟩ | ⟨-, h2 | h2⟩ | ⟨-, -, h3⟩ | ⟨h1, h2, -⟩
    · nlinarith
    · nlinarith
    · nlinarith
    · nlinarith
    · zqiz
  · exfalso
    rw [hb2] at hbE hbW I1
    have hE' : (b.1 * c.2 - 0 * c.1 < 0 ∧ 0 < c.2) ∨
        (b.1 * c.2 - 0 * c.1 = 0 ∧ 0 < b.1 * c.1 + 0 * c.2 ∧ b.1 < 0) := by
      rcases hbE with ⟨-, h2, -⟩ | ⟨h1, h2 | h2⟩ | ⟨-, -, h3⟩ | ⟨h1, h2, h3⟩
      · grind
      · grind
      · zumhz
      · grind
      · zumky
        zujh
        · grind
        · nlinarith
    have hW' : (b.1 * c.2 - 0 * c.1 < 0 ∧ c.2 < 0) ∨
        (b.1 * c.2 - 0 * c.1 = 0 ∧ 0 < b.1 * c.1 + 0 * c.2 ∧ 0 < b.1) := by
      rcases hbW with ⟨-, h2, -⟩ | ⟨h1, h2 | h2⟩ | ⟨-, -, h3⟩ | ⟨h1, h2, h3⟩
      · grind
      · grind
      · zumhz
      · grind
      · zumky
        zujh
        · grind
        · nlinarith
    grind
  · right
    refine ztuhd
    rcases hbE with ⟨-, h2, -⟩ | ⟨-, h2 | h2⟩ | ⟨-, -, h3⟩ | ⟨h1, h2, -⟩
    · nlinarith
    · nlinarith
    · nlinarith
    · nlinarith
    · zqiz

/-- **Two chords at a walk vertex: the wedge.**  Let the chords `dE` (to the east) and `dW` (to
the west) be attached at the walk vertex `p`.  Then, for `τ = 1` (wedge above) or `τ = -1`
(wedge below), the regions touching either chord are the region `X` between them on the side
`τ`, and the regions `U`, `V` faced just after and just before the vertex; `X` contains the
points just on the side `τ` of both chords, and the half-disk on the side `τ` near the vertex
lies in the domain. -/
theorem wedge_core (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {dE dW : Set Point} (hdE : dE ∈ F) (hdW : dW ∈ F) {p : ℕ}
    (hAE : SideAttach M.W dE p 0) (hAW : SideAttach M.W dW p 0) {qE qW : Point}
    (hcE : dE = Chazelle.segment ztoy qE) (hcW : dW = Chazelle.segment ztoy qW)
    (hyE : qE.2 = (M.W.vtx p).2) (hyW : qW.2 = (M.W.vtx p).2)
    (hopE : ∀ s ∈ Ioo (0 : ℝ) 1, lerp ztoy qE s ∈ M.D)
    (hopW : ∀ s ∈ Ioo (0 : ℝ) 1, lerp ztoy qW s ∈ M.D)
    (hlt : qW.1 < (M.W.vtx p).1) (hgt : (M.W.vtx p).1 < qE.1) :
    ∃ τ : ℝ, ztoi ∧ ∃ (X U V : Set Point) (l r : ℝ), X ∈ M.regions F ∧
      M.IsArc F U ztcfa r ∧ M.IsArc F V l ztcfa ∧
      TouchesIn M.D dE X ∧ TouchesIn M.D dW X ∧
      (TouchesIn M.D dE U ∨ TouchesIn M.D dW U) ∧ (TouchesIn M.D dE V ∨ TouchesIn M.D dW V) ∧
      (∀ R ∈ M.regions F, TouchesIn M.D dE R → R = X ∨ R = U ∨ R = V) ∧
      (∀ R ∈ M.regions F, TouchesIn M.D dW R → R = X ∨ R = U ∨ R = V) ∧
      (∀ z ∈ dE ∪ dW, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztbfc : Point) ∈ X) ∧
      ∃ r' > 0, ∀ x ∈ ball ztoy r', 0 < τ * ztewq → x ∈ M.D := by
  set a := M.W.vtx p with ha
  have hp := hAE.1
  zuiy
  zuhzx
  set nx := sideNext M.W p with hnx
  set pv := sidePrev M.W p 0 with hpv
  have hpv' : pv = M.W.vtx ztcm := by
    rw [hpv]; unfold sidePrev; simp
  have hmodp : ztbaqx := by
    rw [Nat.mod_add_mod, show p + M.W.n - 1 + 1 = p + M.W.n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hp]
  have hnxa : nx ≠ a := fun h => hM.nd p hp h.symm
  have hpva : pv ≠ a := by
    rw [hpv']; intro h
    have := hM.nd ztcm zthp
    grind
  set B := nx - a
  set Av := pv - a
  set E := qE - a
  set Wv := qW - a
  have hE2 : E.2 = 0 := by simp [E, hyE]
  have hE1 : 0 < E.1 := by simp only [E, Prod.fst_sub]; linarith
  have hW2 : Wv.2 = 0 := by simp [Wv, hyW]
  have hW1 : Wv.1 < 0 := by simp only [Wv, Prod.fst_sub]; linarith
  have hB0 := sub_ne_zero.2 hnxa
  have hA0 := sub_ne_zero.2 hpva
  have hE0 : E ≠ 0 := by_grind
  have hW0 : Wv ≠ 0 := by_grind
  have hqEa : qE ≠ a := by_grind
  have hqWa : qW ≠ a := by_grind
  -- both horizontal directions lie in the left sector of the walk
  have hdir : ∀ {d : Set Point} {q : Point}, d ∈ F → SideAttach M.W d p 0 →
      d = Chazelle.segment a q → q ≠ a → sideCcw B ztkcr Av := by
    intro d q hd hAd hcd hqa
    have hqd : q ∈ d := by rw [hcd]; exact Geometry.right_mem_segment _ _
    obtain ⟨s, hs1, hs2⟩ := ((sideLeft_far hM ztvsy hAd hqd by_grind).and
      self_mem_nhdsWithin).exists
    zumeu
    unfold sideLeft sideLeftOf at hs1
    zvmxe at hs1
    have e : lerp a q s - a = s • ztkcr := by
      apply Geometry.point_ext <;> zundk
    rw [e, Chazelle.Chain.sideCcw_smul hs0] at hs1
    omega
  have hBE := hdir hdE hAE hcE hqEa
  have hBW := hdir hdW hAW hcW hqWa
  -- the region faces and sides
  obtain ⟨U, V, l, r, hU, hV, -, harcU, harcV, -⟩ := hM.attach_face hF hfin hdE hAE
  have hne : F.Nonempty := ⟨dE, hdE⟩
  have hUa := faced_after hp le_rfl one_pos harcU (WalkAx.arc_cuts hne harcU).2.2
  have hVne := (WalkAx.arc_cuts hne harcV).2.2
  -- the positions just before the vertex face `V`
  have hVb : ∀ᶠ s in 𝓝[>] (0 : ℝ), M.Faces ztcm zteb V := by
    zuevd
    · zuhyz

      have hl0' := lt_of_le_of_ne hl0 (fun h => hVne (by rw [← h, h0]; simp))
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 ztszs from
        lt_min one_pos by_linarith)] with s hs hs'
      zufwh
      have hs1 := hs'.2.trans_le ztff
      have hs2 := hs'.2.trans_le ztgh
      have e : ztcrd := by
        simp
      zuelq

      have hc : zticr := by rw [Nat.cast_sub by_omega]; simp
      zuktq
      zuiq

    · zufes
      have e : ztxfk := by
        rw [show p + M.W.n - 1 = p - 1 + M.W.n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt by_omega]
      zui
      refine harcV.2.2.2.2.2.2 _ _ by_omega by_grind by_grind ?_
      have hc : zticy := by rw [Nat.cast_sub by_omega]; simp
      grind
  obtain ⟨UpE, DnE, hUpE, hDnE, -, hsideE, hiffE⟩ := chordSides_of_system ztbip hdE
  obtain ⟨UpW, DnW, hUpW, hDnW, -, hsideW, hiffW⟩ := chordSides_of_system ztbip hdW
  -- points of the chords
  have hsegE : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a qE s ∈ dE ∧ lerp a qE s ∈ M.D := fun s hs =>
    ⟨by rw [hcE]; exact Geometry.lerp_mem_segment _ _ hs.1.le hs.2.le, by_grind⟩
  have hsegW : ∀ s ∈ Ioo (0 : ℝ) 1, lerp a qW s ∈ dW ∧ lerp a qW s ∈ M.D := fun s hs =>
    ⟨by rw [hcW]; exact Geometry.lerp_mem_segment _ _ hs.1.le hs.2.le, by_grind⟩
  have hsegE' : ∀ s ∈ Ioo (0 : ℝ) 1, lerp qE a s ∈ dE ∧ lerp qE a s ∈ M.D := fun s hs => by
    zuoyd; exact hsegE _ by_grind
  have hsegW' : ∀ s ∈ Ioo (0 : ℝ) 1, lerp qW a s ∈ dW ∧ lerp qW a s ∈ M.D := fun s hs => by
    zuoyd; exact hsegW _ by_grind
  have ev1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := by
    zufss
    omega
  have ev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 1 - s ∈ Ioo (0 : ℝ) 1 := by
    zufss
    grind
  -- walk offsets
  have hwa : M.wa p = a := rfl
  have hwb : M.wb p = nx := rfl
  have hwa' : M.wa _ = pv := hpv'.symm
  have hwb' : M.wb ztcm = a := by
    show M.W.vtx _ = a; grind
  have hUo : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Chazelle.Jordan.offset a nx s δ ∈ U := by
    filter_upwards [hUa] with s hs
    rw [zero_add] at hs
    tauto
  have hVo : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Chazelle.Jordan.offset pv a zteb δ ∈ V := by
    filter_upwards [hVb] with s hs
    unfold Model.Faces at hs; rw [hwa', hwb'] at hs; exact hs
  -- the clean half-disk
  zuebj
  have hhalf : ∀ X : Point, sideCcw B X Av → ∀ x ∈ ball a r₁, x - a = X → x ∈ M.D := by
    intro X hX x hx hxX
    zuhtn
    apply hcl x by_grind hnd
    unfold sideLeft sideLeftOf; grind
  rcases sign_case hE2 hE1 hW2 hW1 hBE hBW hB0 hA0 with ⟨hb2, hc2⟩ | ⟨hb2, hc2⟩
  · -- wedge above
    have hup : ∀ X : Point, 0 < X.2 → sideCcw B X Av := by
      zufxi
      refine Chazelle.Chain.sideCcw_sub_right hB0 hE0 hA0 hBE ?_
      unfold sideCcw sideCross; rw [hE2]
      zugav
    -- the wedge sector
    obtain ⟨Sw, hSw⟩ := sector_side hM hF hfin hp hqWa hqEa fun X hX => by
      have hX2 : 0 < X.2 := by
        zqir
        · linarith
        · linarith
        · nlinarith
        · nlinarith
      exact ⟨hup X hX2, hX2.ne'⟩
    have hUpEW : UpW = UpE := by
      refine sector_regions_eq hSw hUpW hUpE ?_ ?_
      · zqix
        exact (offsets_side hsideW hyW hsegW' hs).1 by_linarith
      · zqiy
        exact (offsets_side hsideE hyE.symm hsegE hs).1 by_linarith
    -- the corner after the vertex: below `dE`, then the walk edge
    obtain ⟨Sa, hSa⟩ := sector_side hM hF hfin hp hqEa hnxa fun X hX => by
      refine ⟨Chazelle.Chain.sideCcw_sub_left hB0 hBE hX, ?_⟩
      zufdn
      zuksj
      zqis
    have hDnEU : DnE = U := by
      refine sector_regions_eq hSa hDnE hU ?_ hUo
      zqix
      exact (offsets_side hsideE hyE hsegE' hs).2 by_linarith
    -- the corner before the vertex: the walk edge, then below `dW`
    obtain ⟨Sb, hSb⟩ := sector_side hM hF hfin hp hpva hqWa fun X hX => by
      refine ⟨Chazelle.Chain.sideCcw_sub_right hB0 hW0 hA0 hBW hX, ?_⟩
      zufdn
      zukth
      zqit
    have hVDnW : V = DnW := by
      refine sector_regions_eq hSb hV hDnW hVo ?_
      zqiy
      exact (offsets_side hsideW hyW.symm hsegW hs).2 by_linarith
    refine ⟨1, Or.inl rfl, UpE, U, V, l, r, hUpE, harcU, harcV, (hiffE _ hUpE).2 ztp,
      (hiffW _ hUpE).2 (Or.inl hUpEW.symm), Or.inl ((hiffE _ hU).2 (Or.inr hDnEU.symm)),
      Or.inr ((hiffW _ hV).2 (Or.inr hVDnW)), fun R hR h => ?_, fun R hR h => ?_, ?_,
      r₁, hr₁, fun x hx hx2 => hhalf _ (hup _ ztdzb) x hx rfl⟩
    · zuflf
      · simp
      · exact Or.inr (Or.inl hDnEU)
    · zuflg
      · exact Or.inl hUpEW
      · exact Or.inr (Or.inr hVDnW.symm)
    · zuifj
      · zugko
        zvohi; exact hδ.1
      · zugkp
        rw [one_mul, ← hUpEW]; exact hδ.1
  · -- wedge below
    have hdown : ∀ X : Point, X.2 < 0 → sideCcw B X Av := by
      zufxi
      refine Chazelle.Chain.sideCcw_sub_right hB0 hW0 hA0 hBW ?_
      unfold sideCcw sideCross; rw [hW2]
      zugav
    -- the wedge sector
    obtain ⟨Sw, hSw⟩ := sector_side hM hF hfin hp hqEa hqWa fun X hX => by
      have hX2 : X.2 < 0 := by
        zqir
        · linarith
        · linarith
        · nlinarith
        · nlinarith
      exact ⟨hdown X hX2, hX2.ne⟩
    have hDnEW : DnE = DnW := by
      refine sector_regions_eq hSw hDnE hDnW ?_ ?_
      · zqix
        exact (offsets_side hsideE hyE hsegE' hs).2 by_linarith
      · zqiy
        exact (offsets_side hsideW hyW.symm hsegW hs).2 by_linarith
    -- the corner after the vertex: above `dW`, then the walk edge
    obtain ⟨Sa, hSa⟩ := sector_side hM hF hfin hp hqWa hnxa fun X hX => by
      refine ⟨Chazelle.Chain.sideCcw_sub_left hB0 hBW hX, ?_⟩
      zufdn
      zukth
      zqis
    have hUpWU : UpW = U := by
      refine sector_regions_eq hSa hUpW hU ?_ hUo
      zqix
      exact (offsets_side hsideW hyW hsegW' hs).1 by_linarith
    -- the corner before the vertex: the walk edge, then above `dE`
    obtain ⟨Sb, hSb⟩ := sector_side hM hF hfin hp hpva hqEa fun X hX => by
      refine ⟨Chazelle.Chain.sideCcw_sub_right hB0 hE0 hA0 hBE hX, ?_⟩
      zufdn
      zuksj
      zqit
    have hVUpE : V = UpE := by
      refine sector_regions_eq hSb hV hUpE hVo ?_
      zqiy
      exact (offsets_side hsideE hyE.symm hsegE hs).1 by_linarith
    refine ⟨-1, Or.inr rfl, DnE, U, V, l, r, hDnE, harcU, harcV, (hiffE _ hDnE).2 ztbt,
      (hiffW _ hDnE).2 (Or.inr hDnEW), Or.inr ((hiffW _ hU).2 (Or.inl hUpWU.symm)),
      Or.inl ((hiffE _ hV).2 (Or.inl hVUpE)), fun R hR h => ?_, fun R hR h => ?_, ?_,
      r₁, hr₁, fun x hx hx2 => hhalf _ (hdown _ ztdzb) x hx rfl⟩
    · zuflf
      · exact Or.inr (Or.inr hVUpE.symm)
      simp
    · zuflg
      · exact Or.inr (Or.inl hUpWU)
      · exact Or.inl hDnEW.symm
    · zuifj
      · zugko
        zungh; exact hδ.2
      · zugkp
        rw [show z.2 + -1 * δ = z.2 - δ by ring, hDnEW]; exact hδ.2

/-! ## Attachments and faced regions -/

/-- Two distinct chords attached at one walk vertex leave it in opposite horizontal directions. -/
theorem opposite_dirs (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) {e e' : Set Point}
    (he : e ∈ F) (he' : e' ∈ F) {p : ℕ} (hA : SideAttach M.W e p 0) (hA' : SideAttach M.W e' p 0)
    (hne : e' ≠ e) :
    ∃ q q' : Point, e = Chazelle.segment ztoy q ∧ e' = Chazelle.segment ztoy q' ∧
      q.2 = (M.W.vtx p).2 ∧ q'.2 = (M.W.vtx p).2 ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp ztoy q s ∈ M.D) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp ztoy q' s ∈ M.D) ∧ q ∉ M.D ∧ q' ∉ M.D ∧
      ((q.1 < (M.W.vtx p).1 ∧ (M.W.vtx p).1 < q'.1) ∨
        (q'.1 < (M.W.vtx p).1 ∧ (M.W.vtx p).1 < q.1)) := by
  have hpt : ztbrq := Chazelle.Chain.sidePt_zero _ _
  obtain ⟨q, hce, hqa, hqy, hqo, hqD⟩ := hM.chord_from ztesz hA
  obtain ⟨q', hce', hqa', hqy', hqo', hqD'⟩ := hM.chord_from ztvsz hA'
  zvmxe at hce hqa hqy hqo hce' hqa' hqy' hqo'
  refine ⟨q, q', hce, hce', hqy, hqy', hqo, hqo', hqD, hqD', ?_⟩
  zuhog
  have hx : q.1 ≠ a.1 := by_grind
  have hx' : q'.1 ≠ a.1 := by_grind
  have hside : ∀ {c : Set Point} {f : Point}, c = Chazelle.segment a f → ∀ z ∈ c, z ≠ a →
      (a.1 < z.1 ↔ a.1 < f.1) := by
    intro c f hc z hz hza
    zvnmd at hz
    zuje
    have hs : ztppw := by rintro rfl; simp_all
    have hs' : ztxx := by_grind
    simp_all
  zulwf
  zufqo
  refine (sameDir_eq hM ztesz ztvsz hA hA' rfl fun z z' hz hz' hza hza' => ?_).symm
  zvmxe at hza hza' ⊢
  rw [hside hce z hz hza, hside hce' z' hz' hza']
  rcases lt_or_gt_of_ne hx with h | h <;> rcases lt_or_gt_of_ne hx' with h' | h'
  · grind
  · grind
  · grind
  grind

/-- **A region touching an attached chord** is faced next to the attachment (it has an arc
starting or ending there), or the attachment is a walk vertex carrying a second chord in the
opposite direction, and the region is the wedge on one side `τ` of both chords. -/
theorem adj_or_wedge (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {e : Set Point} (he : e ∈ F) {p : ℕ} {t : ℝ} (hA : SideAttach M.W e p t) {R : Set Point}
    (hR : R ∈ M.regions F) (hRe : TouchesIn M.D e R) :
    (ztwxj ∨ ztwxi) ∨
    (t = 0 ∧ ∃ e' ∈ F, e' ≠ e ∧ SideAttach M.W e' p 0 ∧ TouchesIn M.D e' R ∧
      ∃ τ : ℝ, ztoi ∧
      (∀ z ∈ e ∪ e', z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztbfc : Point) ∈ R) ∧
      ∃ r' > 0, ∀ x ∈ ball ztoy r', 0 < τ * ztewq → x ∈ M.D) := by
  by_cases hsole : ∀ c' ∈ F, SideAttach M.W c' p t → c' = e
  · exact Or.inl (sides_single hM hF hfin he hA hsole hR hRe)
  zumiu
  obtain ⟨e', he', hA', hne⟩ := hsole
  have ht : ztbhh := by
    zumv
    exact hne (one_chord_interior hM hF he' he (lt_of_le_of_ne hA.2.1 zthrm) hA' hA)
  zucfb
  obtain ⟨q, q', hce, hce', hqy, hqy', hqo, hqo', -, -, hdir⟩ :=
    opposite_dirs hM hF he he' hA hA' hne
  zuejv
  · obtain ⟨τ, hτ, X, U, V, l, r, -, harcU, harcV, hEX, -, -, -, -, hallW, hside, r', hr', hball⟩ :=
      wedge_core hM hF hfin he' he hA' hA hce' hce hqy' hqy hqo' hqo h1 h2
    rcases hallW R hR hRe with rfl | rfl | rfl
    · refine Or.inr ⟨rfl, e', he', hne, hA', hEX, τ, hτ, fun z hz hzD => hside z ?_ hzD, r', hr', hball⟩
      grind
    · grind
    grind
  · obtain ⟨τ, hτ, X, U, V, l, r, -, harcU, harcV, -, hWX, -, -, hallE, -, hside, r', hr', hball⟩ :=
      wedge_core hM hF hfin he he' hA hA' hce hce' hqy hqy' hqo hqo' h1 h2
    rcases hallE R hR hRe with rfl | rfl | rfl
    · exact Or.inr ⟨rfl, e', he', hne, hA', hWX, τ, hτ, hside, r', hr', hball⟩
    · grind
    grind

/-- An arc starting or ending at a key inside a walk edge makes its region faced just after or
just before that key. -/
theorem faced_of_arc (hne : F.Nonempty) {R : Set Point} {p : ℕ} {t : ℝ}
    (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (h : ztwxj ∨ ztwxi) :
    FacedAfter M R p t ∨ FacedBefore M R p t := by
  rcases h with ⟨r, harc⟩ | ⟨l, harc⟩
  · exact Or.inl (faced_after hp ht.1.le ht.2 harc (WalkAx.arc_cuts hne harc).2.2)
  · exact Or.inr (faced_before hp ht.1 ht.2 harc (WalkAx.arc_cuts hne harc).2.2)

/-- A chord is not attached twice inside one walk edge. -/
theorem attach_other_edge (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p pb : ℕ}
    {t tb : ℝ} (hA : SideAttach M.W c p t) (hB : SideAttach M.W c pb tb)
    (hne : sidePt M.W p t ≠ sidePt M.W pb tb) : pb ≠ p := by
  zunq
  obtain ⟨q, hcq, hqa, -, hop, -⟩ := hM.chord_from hc hA
  have hqb : sidePt M.W pb tb = q := by
    have hmem := hB.2.2.2.1
    zuktt
    obtain ⟨s, hs0, hs1, hs⟩ := Geometry.mem_segment_iff_lerp.1 hmem
    zunl
    · zuqy
      · exact absurd by_simp_all (hM.trace pb hB.1 tb hB.2.1 hB.2.2.1.le)
      simp_all
    · exact absurd (by zunvo) hne
  have hmid : lerp (sidePt M.W pb t) q ztcn = sidePt M.W pb ((t + tb) / 2) := by
    rw [← hqb]; unfold sidePt; apply Geometry.point_ext <;> zundk <;> ring
  exact hM.trace pb hB.1 _ (by linarith [hA.2.1, hB.2.1]) (by linarith [hA.2.2.1, hB.2.2.1])
    (hmid ▸ hop _ by_grind)

/-- The keys of one walk edge around a key of it, against a key of another walk edge. -/
theorem key_sides {p pb : ℕ} (hpb : pb ≠ p) {tb t : ℝ} (htb : 0 ≤ tb) (htb1 : tb < 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (t < u → sideInArc ztk ztbd zttve) ∧
      (u < t → sideInArc ztbd ztk zttve) := by
  rcases lt_or_gt_of_ne hpb with h | h
  · have h' : (pb : ℝ) + 1 ≤ p := by exact_mod_cast h
    refine ztlvz <;> unfold sideInArc <;> split_ifs <;>
      first | (constructor! <;> linarith)
  · have h' : (p : ℝ) + 1 ≤ pb := by exact_mod_cast h
    refine ztlvz <;> unfold sideInArc <;> split_ifs <;>
      first | (constructor! <;> linarith) | (right; linarith)

/-- A set of reals without three increasing elements has at most two elements. -/
theorem ncard_le_two_of_no_three {S : Set ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x < y → y < z → False) : S.ncard ≤ 2 := by
  zube

  have hfin : S.Finite := Set.finite_of_ncard_pos by_omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff hfin).1 hlt
  grind

/-- **The wall-gap argument** (review, "at most two (β) chords per wall"): at most two positions
inside one walk edge carry exit chords of a region. -/
theorem edge_two (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {R : Set Point} (hR : R ∈ M.regions F) (p : ℕ) :
    {t : ℝ | 0 < t ∧ ∃ c ∈ exits M F R, SideAttach M.W c p t}.ncard ≤ 2 := by
  refine ncard_le_two_of_no_three ?_
  rintro t₁ ⟨h₁0, c₁, ⟨hc₁, hc₁R⟩, hA₁⟩ t₂ ⟨h₂0, c₂, ⟨hc₂, hc₂R⟩, hA₂⟩ t₃ ⟨h₃0, c₃, ⟨hc₃, hc₃R⟩, hA₃⟩
    h12 h23
  have hp := hA₂.1
  have hne : F.Nonempty := ⟨c₁, hc₁⟩
  have hface : ∀ {c : Set Point} {t : ℝ}, c ∈ F → TouchesIn M.D c R → 0 < t →
      SideAttach M.W c p t → FacedAfter M R p t ∨ FacedBefore M R p t := by
    intro c t hc hcR ht hA
    refine faced_of_arc hne hp ⟨ht, hA.2.2.1⟩ (sides_single hM hF hfin hc hA ?_ hR hcR)
    zujax
    exact one_chord_interior hM hF hc' hc ht hA' hA
  -- a faced position near `t` in a given interval around it
  have hnear : ∀ {t a b : ℝ}, FacedAfter M R p t ∨ FacedBefore M R p t → a < t → t < b →
      ∃ u ∈ Ioo a b, M.Faces p u R := by
    intro t a b h ha hb
    zuy
    · obtain ⟨s, hs, hs'⟩ := (h.and (Ioo_mem_nhdsGT (show (0 : ℝ) < b - t by linarith))).exists
      grind
    · obtain ⟨s, hs, hs'⟩ := (h.and (Ioo_mem_nhdsGT (show (0 : ℝ) < t - a by linarith))).exists
      grind
  obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach ztqpg hA₂
  have hpb := attach_other_edge hM ztqpg hA₂ hB ztbsb
  obtain ⟨u₁, hu₁, hf₁⟩ := hnear (hface hc₁ hc₁R h₁0 hA₁) (show 0 < t₁ from h₁0) h12
  obtain ⟨u₃, hu₃, hf₃⟩ := hnear (hface hc₃ hc₃R h₃0 hA₃) h23 hA₃.2.2.1
  have hu₁' : u₁ ∈ Ioo (0 : ℝ) 1 := by_grind
  have hu₃' : u₃ ∈ Ioo (0 : ℝ) 1 := by_grind
  have hsep := fun {u u' : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hin : sideInArc _ _ _)
      (hf : M.Faces p u R) (hu' : u' ∈ Ioo (0 : ℝ) 1)
      (hin' : sideInArc _ _ _) (hf' : M.Faces p u' R) =>
    sep_false hM hc₂ ztqpg hA₂ hB ztbsb hR hp hu hin hf hp hu' hin' hf'
  have hks := fun {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) =>
    key_sides hpb hB.2.1 hB.2.2.1 h₂0.le hA₂.2.2.1 hu.1.le hu.2
  grind

/-! ## Sides of chords and strips -/

/-- The region `R` lies on the side `τ` of the chord `e`: the points just on that side of the
chord are in `R`. -/
def SideIn (M : Model) (R e : Set Point) (τ : ℝ) : Prop :=
  ∀ z ∈ e, z ∈ M.D → ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztbfc : Point) ∈ R

/-- The open half-ball on the side `τ` of the point `z` near `z` lies in `A`. -/
def HalfIn (A : Set Point) (τ : ℝ) (z : Point) : Prop :=
  ∃ r > 0, ∀ y ∈ ball z r, 0 < τ * ztkhl → y ∈ A

/-- The region `R` is faced next to the key of the position `(p, t)`: it has an arc starting or
ending there. -/
def Adj (M : Model) (F : Set ztf) (R : Set Point) (p : ℕ) (t : ℝ) : Prop :=
  ztwxj ∨ ztwxi
theorem halfIn_of_mem (hA : IsOpen A) (τ : ℝ) {z : Point} (hz : z ∈ A) :
    HalfIn A τ z := by
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 hA z hz
  exact ⟨r, hr, by_grind⟩

/-- **A region is on one side of a chord only.** -/
theorem side_unique (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {e : Set Point} (he : e ∈ F) {R : Set Point} (hR : R ∈ M.regions F) {z : Point} (hz : z ∈ e)
    (hzD : z ∈ M.D) {τ τ' : ℝ} (hτ : τ = 1 ∨ τ = -1) (hτ' : τ' = 1 ∨ τ' = -1)
    (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztbfc : Point) ∈ R)
    (h' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((z.1, z.2 + τ' * δ) : Point) ∈ R) : τ = τ' := by
  obtain ⟨Up, Dn, hUp, hDn, hne, hside, -⟩ := chordSides_of_system ztbip he
  have hmeet : ∀ {X : Set Point}, X ∈ M.regions F → ∀ {σ : ℝ},
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztewt : Point) ∈ R) →
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztewt : Point) ∈ X) → R = X := by
    intro X hX σ h1 h2
    obtain ⟨δ, h3, h4⟩ := (h1.and h2).exists
    exact (Chazelle.Chain.regionsIn_eq_or_disjoint hR hX).resolve_right
      by_grind
  have hup : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztokn : Point) ∈ Up := by
    simp_all
  have hdn : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (ztmpk : Point) ∈ Dn := by
    zugkn
    zungh; simp_all
  rcases hτ with rfl | rfl <;> rcases hτ' with rfl | rfl
  · rfl
  · exact absurd ((hmeet hUp h hup).symm.trans (hmeet hDn h' hdn)) hne
  · exact absurd ((hmeet hUp h' hup).symm.trans (hmeet hDn h hdn)) hne
  · rfl

/-- The open half-ball is preconnected. -/
theorem isPreconnected_half (z : Point) (r τ : ℝ) :
    IsPreconnected {y | y ∈ ball z r ∧ 0 < τ * ztkhl} := by
  have hc : Convex ℝ {y : Point | 0 < τ * ztkhl} := by
    intro y hy w hw a b ha hb hab
    simp only [mem_ofPred_eq, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hy hw ⊢
    have e : τ * (a * y.2 + b * w.2 - z.2) = a * (τ * ztkhl) + b * (τ * (w.2 - z.2)) := by
      grind
    zui
    zucoq
    · positivity
    · zudba

  exact ((convex_ball z r).inter hc).isPreconnected

/-- **The strip argument**: if every point of a horizontal segment has its open half-ball on the
side `τ` inside `A`, the points just on that side of its two ends lie in one component of `A`. -/
theorem strip_const {h τ : ℝ} (hτ : τ = 1 ∨ τ = -1) {x₀ x₁ : ℝ} (hx : x₀ ≤ x₁)
    (hgood : ∀ x ∈ Icc x₀ x₁, HalfIn A τ (ztcon : Point)) :
    ∃ w ∈ A, (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((x₀, h + τ * δ) : Point) ∈ connectedComponentIn A w) ∧
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((x₁, h + τ * δ) : Point) ∈ connectedComponentIn A w) := by
  have hτa : |τ| = 1 := by_grind
  let P : ℝ → ℝ → Prop := fun x y => ∃ w ∈ A,
    (∀ᶠ δ in 𝓝[>] (0 : ℝ), ((x, h + τ * δ) : Point) ∈ connectedComponentIn A w) ∧
      (∀ᶠ δ in 𝓝[>] (0 : ℝ), (zthlh : Point) ∈ connectedComponentIn A w)
  -- the side points of `y` near `x` are in the half-ball at `x`
  have hnear : ∀ {x r y : ℝ}, |y - x| < r → ∀ δ, 0 < δ → δ < r →
      (zthlh : Point) ∈ {q | q ∈ ball (ztcon : Point) r ∧ 0 < τ * zttxe} := by
    intro x r y hy δ hδ hδr
    zujx
    · zukxn
      simp only [Real.dist_eq]
      grind
    · show 0 < τ * ztnzy
      rw [show τ * ztnzy = (τ * τ) * δ by ring]
      rcases hτ with rfl | rfl <;> norm_num <;> exact hδ
  have hloc : ∀ x ∈ Icc x₀ x₁, ∀ᶠ y in 𝓝[Icc x₀ x₁] x, P x y := by
    zuh
    obtain ⟨r, hr, hsub⟩ := hgood x hx
    set H := {q : Point | q ∈ ball (ztcon : Point) r ∧ 0 < τ * zttxe}
    have hHA : H ⊆ A := by_grind
    have hw : (ztyse : Point) ∈ H := hnear by_grind _ by_linarith
      by_linarith
    have hHc :=
      (isPreconnected_half (ztcon : Point) r τ).subset_connectedComponentIn hw hHA
    have hev : ∀ {y : ℝ}, |y - x| < r →
        ∀ᶠ δ in 𝓝[>] (0 : ℝ), (zthlh : Point) ∈
          connectedComponentIn A (ztyse : Point) := by
      zusy
      filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hr] with δ hδ hδ'
      grind
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x hr)] with y hy
    exact ⟨_, hHA hw, hev by_grind, hev by_tauto⟩
  refine (isPreconnected_Icc.induction₂ P hloc ?_ ?_ by_grind by_grind)
  · rintro x y z - - - ⟨w, hw, h1, h2⟩ ⟨w', hw', h3, h4⟩
    obtain ⟨δ, h5, h6⟩ := (h2.and h3).exists
    refine ⟨w, hw, h1, ?_⟩
    rw [(connectedComponentIn_eq h5).trans (connectedComponentIn_eq h6).symm]
    zulyj
  grind

/-! ## Chains of wedges -/

/-- An admissible chord from its end in the direction `σ` back to its other end. -/
theorem sigma_end (hM : WalkAx M) {e : Set Point} (he : e ∈ M.Adm) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    ∃ w q : Point, e = Chazelle.segment w q ∧ q.2 = w.2 ∧ σ * q.1 < σ * w.1 ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp w q s ∈ M.D) ∧ WalkEnd M.W e w ∧ q ∉ M.D := by
  obtain ⟨a, b, hab, hce, hy, hop, ha, hb⟩ := hM.ends e he
  have hnD : ∀ {x : Point}, WalkEnd M.W e x → x ∉ M.D := by
    zqiv
  have hx : ztsdk := by_grind
  have hσx : σ * a.1 ≠ σ * b.1 := by
    grind
  rcases lt_or_gt_of_ne hσx with h | h
  · exact ⟨b, a, hce.trans ztfnp, hy, h, WalkAx.open_rev hop, hb, hnD ha⟩
  grind

/-- The points of a horizontal segment lie between its ends. -/
theorem mem_seg_sigma {w q : Point} (hy : q.2 = w.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hqw : σ * q.1 < σ * w.1) {y : Point} (hyc : y ∈ Chazelle.segment w q) :
    y.2 = w.2 ∧ σ * q.1 ≤ σ * y.1 ∧ σ * y.1 ≤ σ * w.1 := by
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hyc
  zubzm
  refine ⟨by_simp_all, ?_, ?_⟩ <;> rcases hσ with rfl | rfl <;> nlinarith

/-- The points strictly between the ends of a horizontal segment are open points of it. -/
theorem open_pt {D : Set Point} {w q : Point} (hy : q.2 = w.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hop : ∀ s ∈ Ioo (0 : ℝ) 1, lerp w q s ∈ D) {x : ℝ} (h1 : σ * q.1 < σ * x)
    (h2 : σ * x < σ * w.1) :
    (ztkhd : Point) ∈ Chazelle.segment w q ∧ (ztkhd : Point) ∈ D := by
  have hne : q.1 - w.1 ≠ 0 := by
    grind
  set s := (x - w.1) / (q.1 - w.1) with hs
  have hpt : lerp w q s = (ztkhd : Point) := by
    zufqm
    · simp_all
    simp_all
  have hs01 : ztgut := by
    zur
    · simp only [one_mul] at h1 h2
      exact ⟨div_pos_of_neg_of_neg by_linarith by_linarith,
        (div_lt_one_of_neg by_linarith).2 by_linarith⟩
    · simp only [neg_mul, one_mul, neg_lt_neg_iff] at h1 h2
      zqiq
  zuezz
  exact ⟨Geometry.lerp_mem_segment _ _ hs01.1.le hs01.2.le, by_grind⟩

/-- The chords beyond `e` in the direction `σ`. -/
def beyond (F : Set ztf) (e : Set Point) (σ : ℝ) : Set ztf :=
  {g | g ∈ F ∧ ∃ x ∈ g, ∀ y ∈ e, σ * y.1 < σ * x.1}

/-- The conclusion of `chain_end`. -/
def ChainOut (M : Model) (F : Set ztf) (R : Set Point) (τ σ : ℝ) (e : Set Point) : Prop :=
  ∃ f ∈ F, TouchesIn M.D f R ∧ (∃ p t, SideAttach M.W f p t ∧ Adj M F R p t) ∧
    SideIn M R f τ ∧ ∃ z₀ ∈ e, z₀ ∈ M.D ∧ ∃ z₁ ∈ f, z₁ ∈ M.D ∧ z₁.2 = z₀.2 ∧
      σ * z₀.1 ≤ σ * z₁.1 ∧ ∀ x : ℝ, σ * z₀.1 ≤ σ * x → σ * x ≤ σ * z₁.1 →
        HalfIn M.D τ (ztueb : Point)

/-- **Following a chain of wedges.**  Let the region `R` lie on the side `τ` of a chord `e`.
Going from `e` in the direction `σ` through the wedge vertices of `R`, one reaches a chord `f`
at which `R` is faced next to an attachment; all points of the horizontal segment from a point
of `e` to a point of `f` have their half-balls on the side `τ` in the domain. -/
theorem chain_end (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {R : Set Point} (hR : R ∈ M.regions F) {τ σ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hσ : σ = 1 ∨ σ = -1) :
    ∀ n : ℕ, ∀ e ∈ F, TouchesIn M.D e R → SideIn M R e τ → (beyond F e σ).ncard ≤ n →
      ChainOut M F R τ σ e := by
  zubgl
  have hσinj : ∀ {x y : ℝ}, σ * x = σ * y → x = y := fun {x y} h => by
    grind
  zugok
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro e he hRe hside hn
    obtain ⟨w, q, hce, hqy, hqw, hop, hwe, hqD⟩ := sigma_end hM ztesz hσ
    obtain ⟨⟨p, t, hA, hAw⟩, -⟩ := hwe
    -- a middle point of `e`
    set m : Point := ((σ * σ * ((w.1 + q.1) / 2)), w.2) with hm
    have hm1 : σ * q.1 < σ * m.1 := by zvmwi; dsimp only; zuokx; linarith
    have hm2 : σ * m.1 < σ * w.1 := by zvmwi; dsimp only; zuokx; linarith
    obtain ⟨hme, hmD⟩ := open_pt hqy hσ hop hm1 hm2
    rw [← hce] at hme
    rcases adj_or_wedge hM hF hfin he hA hR hRe with hadj | ⟨ht0, e', he', hne, hA', hRe', τ', hτ',
      hside', r', hr', hball⟩
    · refine ⟨e, he, hRe, ⟨p, t, hA, hadj⟩, hside, _, hme, hmD, _, hme, hmD, rfl, le_rfl,
        fun x h1 h2 => ?_⟩
      have hx : x = m.1 := by_grind
      zucjv
      exact halfIn_of_mem hM.isOpen τ hmD
    zudlw
    have hwv : w = M.W.vtx p := by rw [← hAw, Chazelle.Chain.sidePt_zero]
    have hττ : τ = τ' :=
      side_unique hM hF hfin he hR hme hmD hτ hτ' (hside m hme hmD) by_grind
    subst hττ
    obtain ⟨q₁, q', hce₁, hce', -, hqy', -, hop', -, hqD', hdir⟩ :=
      opposite_dirs hM hF he he' hA hA' hne
    rw [← hwv] at hce₁ hce' hqy' hop'
    have hq₁ : σ * q₁.1 < σ * w.1 := by
      have hq₁e : q₁ ∈ e := by rw [hce₁]; exact Geometry.right_mem_segment _ _
      zvnme at hq₁e
      obtain ⟨-, -, h2⟩ := mem_seg_sigma hqy hσ hqw hq₁e
      grind
    have hq' : σ * w.1 < σ * q'.1 := by
      rw [← hwv] at hdir
      rcases hσ with rfl | rfl <;> simp only [one_mul, neg_mul, neg_lt_neg_iff] at hq₁ ⊢ <;>
        rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hce'' : e' = Chazelle.segment q' w := hce'.trans ztfnp
    have hwq' : w.2 = q'.2 := hqy'.symm
    -- `e'` is beyond `e`, and fewer chords are beyond `e'`
    have hmemw : ∀ y ∈ e, σ * y.1 ≤ σ * w.1 := fun y hy => by
      zvnme at hy; exact (mem_seg_sigma hqy hσ hqw hy).2.2
    have hmemw' : ∀ y ∈ e', σ * w.1 ≤ σ * y.1 := fun y hy => by
      rw [hce''] at hy; exact (mem_seg_sigma hwq' hσ hq' hy).2.1
    have hwe' : w ∈ e' := by zuoye; exact Geometry.left_mem_segment _ _
    have hsub : beyond F e' σ ⊂ beyond F e σ := by
      constructor
      · rintro g ⟨hg, x, hx, hlt⟩
        exact ⟨hg, x, hx, by_grind⟩
      · zuq
        obtain ⟨-, x, hx, hlt⟩ := h ⟨he', q', by zuoye; exact Geometry.right_mem_segment _ _,
          by grind⟩
        grind
    have hlt := Set.ncard_lt_ncard hsub (hfin.subset fun g hg => hg.1)
    have hIH : ChainOut M F R τ σ e' := by
      first
        | exact by_grind
        | exact ih e' he' hRe' (fun z hz hzD => by_grind) by_omega
    obtain ⟨f, hf, hRf, hadjf, hsidef, z₀', hz₀', hz₀'D, z₁, hz₁, hz₁D, hz₁y, hz₀₁, hgood⟩ := hIH
    have hz₀'s : z₀'.2 = w.2 ∧ σ * w.1 ≤ σ * z₀'.1 ∧ σ * z₀'.1 ≤ σ * q'.1 := by
      rw [hce''] at hz₀'
      obtain ⟨h1, h2, h3⟩ := mem_seg_sigma hwq' hσ hq' hz₀'
      grind
    have hz₀'q : σ * z₀'.1 < σ * q'.1 := by
      grind
    have hmw : m.2 = w.2 := rfl
    refine ⟨f, hf, hRf, hadjf, hsidef, m, hme, hmD, z₁, hz₁, hz₁D, by_grind,
      by grind, fun x h1 h2 => ?_⟩
    rw [hmw]
    rcases lt_trichotomy _ (σ * w.1) with h | h | h
    · exact halfIn_of_mem hM.isOpen τ (open_pt hqy hσ hop (hm1.trans_le h1) h).2
    · have hx : (ztkhd : Point) = M.W.vtx p := by
        grind
      zucjv
      exact ⟨r', hr', hball⟩
    · rcases lt_or_ge (σ * x) (σ * z₀'.1) with h' | h'
      · have := (open_pt hwq' hσ (WalkAx.open_rev hop') h (h'.trans hz₀'q)).2
        rw [← hwq'] at this
        exact halfIn_of_mem hM.isOpen τ this
      · have := hgood x h' h2
        grind

/-! ## Counting chords at points and positions -/

/-- An admissible chord through a point off the domain is a segment from that point. -/
theorem chord_through (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {v : Point} (hv : v ∈ c)
    (hvD : v ∉ M.D) :
    ∃ q : Point, c = Chazelle.segment v q ∧ q ≠ v ∧ q.2 = v.2 ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp v q s ∈ M.D) ∧ q ∉ M.D := by
  obtain ⟨a, b, hab, hce, hy, hop, ha, hb⟩ := hM.ends c hc
  have hnD : ∀ {x : Point}, WalkEnd M.W c x → x ∉ M.D := by
    zqiv
  zvnme at hv
  obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hv
  zunl
  · zuqy
    · simp_all
    · zucuj
      zujgn
      exact ⟨a, hce.trans ztfnp, hab, hy, WalkAx.open_rev hop, hnD ha⟩
  · zubvi
    zumlh
    grind

/-- **At most two chords of `F` pass through a point off the domain** (one to the east, one to
the west). -/
theorem ncard_through_le (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) {v : Point}
    (hvD : v ∉ M.D) : {c | c ∈ F ∧ v ∈ c}.ncard ≤ 2 := by
  classical
  let dir : Set Point → Bool := fun c => decide (∃ x ∈ c, v.1 < x.1)
  have hdir : ∀ c : Set Point, ∀ e', c = Chazelle.segment v e' → (dir c = true ↔ v.1 < e'.1) := by
    zufhw

    · zueku

      zufr
      simp only [Geometry.lerp_fst] at hlt
      zuhbv
    · zufia
      exact zticj
  have key : ∀ {f f' : Point}, (∀ s ∈ Ioo (0 : ℝ) 1, lerp v f s ∈ M.D) → f' ∉ M.D →
      f.2 = v.2 → f'.2 = v.2 → (v.1 < f'.1 ∧ f'.1 < f.1 ∨ f.1 < f'.1 ∧ f'.1 < v.1) → False := by
    zucxd

    have hfe : f.1 - v.1 ≠ 0 := by
      grind
    have e1 : f' = lerp v f ((f'.1 - v.1) / (f.1 - v.1)) := by
      zufqm
      · simp_all
      simp_all
    zqiw
    · zqiq
    · exact ⟨div_pos_of_neg_of_neg by_linarith by_linarith,
        (div_lt_one_of_neg by_linarith).2 by_linarith⟩
  have hinj : InjOn dir {c | c ∈ F ∧ v ∈ c} := by
    zukjb
    obtain ⟨e₁, hce₁, hne₁, hy₁, hop₁, hD₁⟩ := chord_through hM ztmko hc.2 hvD
    obtain ⟨e₂, hce₂, hne₂, hy₂, hop₂, hD₂⟩ := chord_through hM ztvsx hc'.2 hvD
    have hsame : v.1 < e₁.1 ↔ v.1 < e₂.1 := by
      rw [← hdir c e₁ hce₁, ← hdir c' e₂ hce₂, hdd]
    have hx₁ : e₁.1 ≠ v.1 := by_grind
    have hx₂ : e₂.1 ≠ v.1 := by_grind
    have heq : ztsil := by
      zulvo
      zuevp
      · have h₂ : e₂.1 < v.1 := by
          grind
        zqiu
        · zucve
        · zubh
        · zucvf
      · zuhfz
        zqiu
        · grind
        · zubh
        grind
    grind
  calc {c | c ∈ F ∧ v ∈ c}.ncard ≤ (Set.univ : Set Bool).ncard :=
        ncard_le_ncard_of_injOn dir by_grind hinj
    _ = 2 := by_simp

/-- At most two chords of `F` are attached at any position. -/
theorem ncard_at_le (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (p : ℕ) (t : ℝ) : {c | c ∈ F ∧ SideAttach M.W c p t}.ncard ≤ 2 := by
  by_cases hp : p < M.W.n ∧ 0 ≤ t ∧ t ≤ 1
  · refine le_trans (Set.ncard_le_ncard ?_
      ztvvg) (ncard_through_le hM hF
        (hM.trace p hp.1 t hp.2.1 hp.2.2))
    exact fun c hc => ⟨hc.1, hc.2.2.2.2.1⟩
  · have : {c | c ∈ F ∧ SideAttach M.W c p t} = ∅ := by
      zubcj
      zughe
      intro _ hA
      exact hp ⟨hA.1, hA.2.1, hA.2.2.1.le⟩
    zuedz
end FuseDeg
end
namespace Gran
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn)
variable {M : Model}

/-! ## Faces -/
variable {p : ℕ} {t : ℝ} {G : Set (Set Point)}
/-- Facing a set is monotone in the set. -/
theorem faces_mono {U U' : Set Point} (h : M.Faces p t U) (hUU : U ⊆ U') :
    M.Faces p t U' :=
  h.mono fun _ hδ => hUU hδ

/-! ## Arcs with a common end -/

/-- **Two arcs starting at the same key coincide** (nonempty family): the same end, the same
region. -/
theorem arc_start_unique (hne : G.Nonempty) {X Y : Set Point}
    (hX : X ∈ M.regions G) (hY : Y ∈ M.regions G) {a b b' : ℝ} (h : M.IsArc G X a b)
    (h' : M.IsArc G Y a b') : b = b' ∧ X = Y := by
  obtain ⟨-, hb, hab⟩ := WalkAx.arc_cuts hne h
  obtain ⟨-, hb', hab'⟩ := WalkAx.arc_cuts hne h'
  have hbb : b = b' := by
    zuirz
    zuirh
    · exact h.2.2.2.2.2.1 b' h1 hb'
    · have h2 : sideInArc a b' b := by
        by_contra h3
        exact h1 ((Chazelle.Core.cyc_rot hab hab' hne').2 h3)
      exact h'.2.2.2.2.2.1 b h2 hb
  subst hbb
  zubee
  zubub

/-- **Two arcs ending at the same key coincide** (nonempty family). -/
theorem arc_end_unique (hne : G.Nonempty) {X Y : Set Point}
    (hX : X ∈ M.regions G) (hY : Y ∈ M.regions G) {a a' b : ℝ} (h : M.IsArc G X a b)
    (h' : M.IsArc G Y a' b) : a = a' ∧ X = Y := by
  obtain ⟨ha, -, hab⟩ := WalkAx.arc_cuts hne h
  obtain ⟨ha', -, hab'⟩ := WalkAx.arc_cuts hne h'
  have haa : ztsdh := by
    refine Chazelle.Core.cyc_start_eq hab hab' (fun h1 => h.2.2.2.2.2.1 a' h1 ha')
      (fun h1 => h'.2.2.2.2.2.1 a h1 ha)
  subst haa
  zubee
  zubub

/-! ## Positions just after a key -/

/-- The keys just after `k` lie in every cyclic interval containing `k`. -/
theorem eventually_in_of_mem {a b k : ℝ} (h : sideInArc a b k) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc a b zthig := Chazelle.Core.cyc_open h

/-- **A position just after a key** `p + t` (with `0 ≤ t < 1`), inside a walk edge, satisfying
two eventual properties of the keys just after it. -/
theorem exists_pos_after_both (ht : 0 ≤ t) (ht1 : t < 1) {A B : ℝ → Prop}
    (hA : ∀ᶠ ε in 𝓝[>] (0 : ℝ), A ztlcv)
    (hB : ∀ᶠ ε in 𝓝[>] (0 : ℝ), B ztlcv) :
    ∃ t' ∈ Ioo (0 : ℝ) 1, A ztdvo ∧ B ztdvo := by
  obtain ⟨ε, h1, h2, h3⟩ := ((WalkAx.exists_pos_after ht ht1).and (hA.and hB)).exists
  grind

/-! ## Weights -/

/-- The set of weights of the arcs of `U`. -/
def arcWts (M : Model) (G : Set ztf) (U : Set Point) : Set ℕ :=
  (fun ab : ℝ × ℝ => M.arcWt ab.1 ab.2) '' {ab | M.IsArc G U ab.1 ab.2}
theorem weight_eq (G : Set ztf) (U : Set Point) : M.weight G U = sSup (arcWts M G U) :=
  rfl
theorem arcWts_finite (hM : WalkAx M) {G : Set ztf} (hG : G ⊆ M.Adm) (hfin : G.Finite)
    {U : Set Point} (hU : U ∈ M.regions G) : (arcWts M G U).Finite :=
  (hM.arcs_bound hG hfin hU).1.image _

/-- An arc weighs at most the weight of its region. -/
theorem le_weight (hM : WalkAx M) {G : Set ztf} (hG : G ⊆ M.Adm) (hfin : G.Finite)
    {U : Set Point} (hU : U ∈ M.regions G) {a b : ℝ} (h : M.IsArc G U a b) :
    M.arcWt a b ≤ M.weight G U :=
  le_csSup (arcWts_finite hM hG hfin hU).bddAbove ⟨ztvk, h, rfl⟩

/-- A bound on all arcs bounds the weight. -/
theorem weight_le {U : Set Point} {w : ℕ}
    (h : ∀ a b, M.IsArc G U a b → M.arcWt a b ≤ w) : M.weight G U ≤ w := by
  rw [weight_eq]
  rcases (arcWts M G U).eq_empty_or_nonempty with he | hne
  · simp_all
  · refine csSup_le hne ?_
    zuhji
    simp_all

/-! ## The pinned arc of the empty family -/

/-- The pinned arc `(0, 0)` meets every counted edge: it weighs the most. -/
theorem arcWt_le_zero_zero (a b : ℝ) : M.arcWt a b ≤ M.arcWt 0 0 := by
  rw [Model.arcWt_eq, Model.arcWt_eq]
  refine Set.ncard_le_ncard ?_ (M.arcEdges_finite 0 0)
  rintro p ⟨hp, hc, t, ht0, ht1, -⟩
  refine ⟨hp, hc, t, ht0, ht1, ?_⟩
  zuiq

/-- The pinned arc weighs `size`. -/
theorem arcWt_zero_zero : M.arcWt 0 0 = M.size := by
  zultu
  zucr
  zufj
  zuwb
  constructor
  · simp_all
  · rintro ⟨hp, hc⟩
    refine ⟨hp, hc, 1 / 2, by_norm_num, by_norm_num, ?_⟩
    zuiq

/-- **The empty family**: its only region is the domain, whose only arc is the pinned `(0, 0)`. -/
theorem isArc_empty_iff (hM : WalkAx M) {U : Set Point} (hU : U ∈ M.regions ∅) {a b : ℝ} :
    M.IsArc ∅ U a b ↔ a = 0 ∧ b = 0 := by
  constructor
  · zuq
    rcases h.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, ha, hb⟩
    · simp_all
    simp_all
  · rintro ⟨rfl, rfl⟩
    have hn : ztcfu := by
      have : ztbiy := by
        zuccr
        zuidf
        obtain ⟨s, -, -, p, hp, -⟩ := hM.reach z hz (fun i hi => absurd hi by_omega)
        omega
      simp_all
    refine ⟨le_rfl, hn, le_rfl, hn, Or.inr ztrei, fun x _ ⟨c, hc, _⟩ => ?_, ?_⟩
    · simp_all
    · zujbi
      obtain ⟨V, hV, hfV⟩ := hM.exists_faces_of_not_cut ztzi finite_empty hp
        ⟨ht0, ht1⟩ (fun ⟨c, hc, _⟩ => absurd hc ztwab)
      have hD : M.regions ∅ = {M.D} := Chazelle.Chain.regionsIn_empty hM.preconn hM.nonempty
      simp_all

/-- The weight of the only region of the empty family is `size`. -/
theorem weight_empty (hM : WalkAx M) {U : Set Point} (hU : U ∈ M.regions ∅) :
    M.weight ∅ U = M.size := by
  refine le_antisymm (weight_le fun a b h => ?_) ?_
  · zuorz; exact arcWt_le_zero_zero a b
  · zuorz
    exact le_weight hM ztzi finite_empty hU ((isArc_empty_iff hM hU).2 ztrh)
def lostKeys (M : Model) (S : Set ztf) (c : Set Point) : Set ℝ :=
  {k | M.IsCut S k ∧ ¬ M.IsCut ztdb k}

/-- A gap of `G`: two distinct cut keys with no cut strictly between them. -/
def Gap (M : Model) (G : Set ztf) (l r : ℝ) : Prop :=
  M.IsCut G l ∧ M.IsCut G r ∧ l ≠ r ∧ ∀ k, sideInArc l r k → ¬ M.IsCut G k
section Split
variable {S : Set (Set Point)} {c : Set Point} {P R₁ R₂ : Set Point}
theorem sdiff_sub : S \ {c} ⊆ S := sdiff_subset
theorem not_mem_sdiff_self : c ∉ S \ {c} := by_simp_all
theorem split_mem₁ (hc : c ∈ S) (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) :
    R₁ ∈ M.regions S := by
  have := hs.mem₁; rwa [Merge.insert_sdiff_self hc] at this
theorem split_mem₂ (hc : c ∈ S) (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) :
    R₂ ∈ M.regions S := split_mem₁ hc hs.symm

/-- The regions of `S`: `R₁`, `R₂`, and regions of `S'` other than `P`. -/
theorem split_cases (hc : c ∈ S) (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) {X : Set Point}
    (hX : X ∈ M.regions S) : X = R₁ ∨ X = R₂ ∨ (X ∈ M.regions ztdb ∧ X ≠ P) := by
  have hX' : ztbaqn := by
    zuigr
  rcases hs.mem_cases hX' with h | h | h
  · tauto
  · simp_all
  simp_all

/-- A region of `S'` other than `P` is a region of `S`. -/
theorem split_old (hc : c ∈ S) (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) {X : Set Point}
    (hX : X ∈ M.regions ztdb) (hXP : X ≠ P) : X ∈ M.regions S := by
  have := hs.mem_of_ne hX hXP
  rwa [Merge.insert_sdiff_self hc] at this

/-- `c` touches exactly `R₁` and `R₂`. -/
theorem split_touches_iff (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) {X : Set Point} (hX : X ∈ M.regions S) :
    TouchesIn M.D c X ↔ X = R₁ ∨ X = R₂ := by
  have hF := hM.sys S hS hfin
  have hX' : ztbaqn := by
    zuigr
  exact hs.touches_iff hF sdiff_sub hc not_mem_sdiff_self X hX'

/-- If `S'` is empty, `S = {c}` and the two regions of `S` are `R₁` and `R₂`. -/
theorem split_sdiff_nonempty (hc : c ∈ S) (hM : WalkAx M)
    (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) {X : Set Point} (hX : X ∈ M.regions S)
    (h1 : X ≠ R₁) (h2 : X ≠ R₂) : (S \ {c}).Nonempty := by
  rcases split_cases hc hs hX with h | h | ⟨hX', hXP⟩
  · simp_all
  · simp_all
  · by_contra he
    zukxz
    have hD := Chazelle.Chain.regionsIn_empty hM.preconn hM.nonempty
    have hP : P ∈ regionsIn M.D _ := hs.mem
    have hX'' : X ∈ regionsIn M.D _ := hX'
    simp_all

/-! ## Lost keys -/

/-- **Only `c` is attached at a lost key.** -/
theorem lost_attach (hc : c ∈ S) {k : ℝ} (hk : k ∈ lostKeys M S c) :
    ∃ p t, SideAttach M.W c p t ∧ k = p + t ∧ ∀ c' ∈ S, SideAttach M.W c' p t → c' = c := by
  obtain ⟨⟨d, hd, p, t, hA, rfl⟩, hno⟩ := hk
  have hdc : d = c := by
    zuct
    exact hno ⟨d, by_simp_all, p, t, hA, rfl⟩
  subst hdc
  refine ⟨p, t, hA, rfl, fun c' hc' hA' => ?_⟩
  zuct
  exact hno ⟨c', by_simp_all, p, t, hA', rfl⟩

/-- **The arcs of `S` at a lost key belong to `R₁` or `R₂`.** -/
theorem lost_sides (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) {k : ℝ} (hk : k ∈ lostKeys M S c) :
    ∃ U V l r, U ∈ M.regions S ∧ V ∈ M.regions S ∧ M.IsArc S U k r ∧ M.IsArc S V l k ∧
      (U = R₁ ∨ U = R₂) ∧ (V = R₁ ∨ V = R₂) := by
  obtain ⟨p, t, hA, rfl, hone⟩ := lost_attach hc hk
  obtain ⟨U, V, l, r, hU, hV, -, hUa, hVa, htouch⟩ := hM.attach_face hS hfin hc hA
  obtain ⟨hcU, hcV⟩ := htouch hone
  exact ⟨U, V, l, r, hU, hV, hUa, hVa, (split_touches_iff hM hS hfin hc hs hU).1 hcU,
    (split_touches_iff hM hS hfin hc hs hV).1 hcV⟩
theorem sub_P (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) {U : Set Point}
    (h : U = R₁ ∨ U = R₂) : U ⊆ P := by
  rcases h with rfl | rfl
  · exact hs.sub₁
  · exact hs.sub₂

/-- **Arcs of `S'` around a lost key belong to `P`.** -/
theorem arc_around_lost (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) {k : ℝ} (hk : k ∈ lostKeys M S c)
    {Z : Set Point} (hZ : Z ∈ M.regions ztdb) {l r : ℝ} (h : M.IsArc ztdb Z l r)
    (hin : sideInArc l r k) : Z = P := by
  obtain ⟨U, -, -, r', hU, -, hUa, -, hU12, -⟩ := lost_sides hM hS hfin hc hs hk
  obtain ⟨p, t, hA, rfl, -⟩ := lost_attach hc hk
  zudow
  obtain ⟨-, -, hkr⟩ := WalkAx.arc_cuts hne hUa
  obtain ⟨t', ht', h1, h2⟩ := exists_pos_after_both (p := p) hA.2.1 hA.2.2.1
    (A := sideInArc l r) (B := sideInArc ztk r') (eventually_in_of_mem hin)
    ztqdf
  have fZ := h.2.2.2.2.2.2 p t' hA.1 ht'.1 ht'.2 h1
  have fU := hUa.2.2.2.2.2.2 p t' hA.1 ht'.1 ht'.2 h2
  exact WalkAx.faces_unique hZ hs.mem fZ (faces_mono fU (sub_P hs hU12))

/-- **Locality**: a region of `S` other than `R₁`, `R₂` is a region of `S'` with the same arcs. -/
theorem arcs_other (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) {X : Set Point} (hX : X ∈ M.regions S)
    (h1 : X ≠ R₁) (h2 : X ≠ R₂) (a b : ℝ) :
    M.IsArc ztdb X a b ↔ M.IsArc S X a b := by
  zudow
  have hne' := split_sdiff_nonempty hc hM hs hX h1 h2
  obtain ⟨hX', hXP⟩ := (split_cases hc hs hX).resolve_left h1 |>.resolve_left h2
  constructor
  · zuq
    zufjm
    zudek
    refine ⟨ha0, han, hb0, hbn, Or.inl ⟨Model.isCut_mono M sdiff_sub ha,
      Model.isCut_mono M sdiff_sub hb, hab⟩, fun x hx hcut => ?_, hfac⟩
    have hk : x ∈ lostKeys M S c := ⟨hcut, by_simp_all⟩
    have := arc_around_lost hM hS hfin hc hs hk hX' ⟨ha0, han, hb0, hbn,
      by simp_all, hfree, hfac⟩ hx
    simp_all
  · zuq
    zufjl
    zudek
    have harc : M.IsArc S X a b := ⟨ha0, han, hb0, hbn, by_simp_all, hfree, hfac⟩
    have ha' : M.IsCut ztdb a := by
      by_contra hna
      obtain ⟨U, -, -, r, hU, -, hUa, -, hU12, -⟩ := lost_sides hM hS hfin hc hs ⟨ha, hna⟩
      have := (arc_start_unique hne hX hU harc hUa).2
      simp_all
    have hb' : M.IsCut ztdb b := by
      by_contra hnb
      obtain ⟨-, V, l, -, -, hV, -, hVa, -, hV12⟩ := lost_sides hM hS hfin hc hs ⟨hb, hnb⟩
      have := (arc_end_unique hne hX hV harc hVa).2
      simp_all
    exact ⟨ha0, han, hb0, hbn, by_simp_all,
      fun x hx hcut => hfree x hx (Model.isCut_mono M sdiff_sub hcut), hfac⟩

/-- **The weight is local**: removing `c` does not change the weight of the regions it does not
touch. -/
theorem weight_other (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) {X : Set Point} (hX : X ∈ M.regions S)
    (h1 : X ≠ R₁) (h2 : X ≠ R₂) : M.weight ztdb X = M.weight S X := by
  rw [weight_eq, weight_eq]
  zucr
  unfold arcWts
  zucr
  ext ab
  exact arcs_other hM hS hfin hc hs hX h1 h2 ab.1 ab.2

/-- **An arc of `R₁` lies inside an arc of `P`** (or `S'` is empty and `P` has the pinned arc,
which weighs the most). -/
theorem arcs_merged_ge (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) {a b : ℝ} (h : M.IsArc S R₁ a b) :
    ∃ a' b', M.IsArc ztdb P a' b' ∧ M.arcWt a b ≤ M.arcWt a' b' := by
  zudow
  zuwh

  rcases (S \ {c}).eq_empty_or_nonempty with he | hne'
  · refine ⟨0, 0, ?_, arcWt_le_zero_zero a b⟩
    zufts

    exact (isArc_empty_iff hM hP).2 by_simp_all
  · obtain ⟨p, hp, t, ht, hin, hncut, hf⟩ := WalkAx.exists_pos_in_arc hne h
    have hncut' : ¬ M.IsCut ztdb _ := fun h' =>
      hncut (Model.isCut_mono M sdiff_sub h')
    obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := hM.two_cuts hS' hne'
    obtain ⟨l, hl, r, hr, hlr, hxin, hno⟩ := Chazelle.Core.exists_gap (hM.finite_cuts hS' hfin') hk₁
      hk₂ hk hncut'
    obtain ⟨Z, hZ, hZa⟩ := hM.arc_of_gap hS' hfin' hl hr hlr by_grind
    have fZ := hZa.2.2.2.2.2.2 p t hp ht.1 ht.2 hxin
    have hZP := WalkAx.faces_unique hZ hs.mem fZ (faces_mono hf hs.sub₁)
    subst hZP
    refine ⟨l, r, hZa, M.arcWt_mono fun y hy => ?_⟩
    have hl' := fun h' => h.2.2.2.2.2.1 l h' (Model.isCut_mono M sdiff_sub hl)
    have hr' := fun h' => h.2.2.2.2.2.1 r h' (Model.isCut_mono M sdiff_sub hr)
    exact (Chazelle.Core.cyc_same hy hin hl' hr' hlr).2 hxin

/-- **An arc of `P` is an arc of `R₁` or of `R₂`, or contains a lost key.** -/
theorem arcs_merged_cases (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) (hne' : (S \ {c}).Nonempty) {a b : ℝ}
    (h : M.IsArc ztdb P a b) :
    M.IsArc S R₁ a b ∨ M.IsArc S R₂ a b ∨ ∃ k ∈ lostKeys M S c, sideInArc a b k := by
  zudow
  by_cases hk : ∃ k, M.IsCut S k ∧ sideInArc a b k
  · obtain ⟨k, hk1, hk2⟩ := hk
    exact Or.inr (Or.inr ⟨k, ⟨hk1, h.2.2.2.2.2.1 k hk2⟩, hk2⟩)
  zumio
  zufjm
  obtain ⟨Y, hY, hYa⟩ := hM.arc_of_gap hS hfin (Model.isCut_mono M sdiff_sub ha)
    (Model.isCut_mono M sdiff_sub hb) hab (fun k hk' hcut => hk k hcut hk')
  rcases split_cases hc hs hY with rfl | rfl | ⟨hY', hYP⟩
  · simp_all
  · simp_all
  · exfalso
    obtain ⟨p, hp, t, ht, hin, -, hf⟩ := WalkAx.exists_pos_in_arc hne hYa
    exact hYP (WalkAx.faces_unique hY' hs.mem hf (h.2.2.2.2.2.2 p t hp ht.1 ht.2 hin))

/-- A gap of `S'` containing a lost key is an arc of `P`. -/
theorem gap_lost_arc (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) {k : ℝ} (hk : k ∈ lostKeys M S c) {l r : ℝ}
    (hg : Gap M ztdb l r) (hin : sideInArc l r k) : M.IsArc ztdb P l r := by
  zuwh

  obtain ⟨hl, hr, hlr, hfree⟩ := hg
  obtain ⟨Z, hZ, hZa⟩ := hM.arc_of_gap hS' hfin' hl hr hlr hfree
  have := arc_around_lost hM hS hfin hc hs hk hZ hZa hin
  simp_all

/-- An arc of a nonempty family is a gap. -/
theorem gap_of_arc {G : Set ztf} (hne : G.Nonempty) {U : Set Point} {a b : ℝ}
    (h : M.IsArc G U a b) : Gap M G a b := by
  zufjl
  exact ⟨ha, hb, hab, h.2.2.2.2.2.1⟩

/-- **Upper bound for the merged weight** (`S'` nonempty). -/
theorem weight_merged_le (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) (hne' : (S \ {c}).Nonempty) {w : ℕ}
    (h1 : M.weight S R₁ ≤ w) (h2 : M.weight S R₂ ≤ w)
    (hJ : ∀ l r, Gap M ztdb l r → (∃ k ∈ lostKeys M S c, sideInArc l r k) →
      M.arcWt l r ≤ w) : M.weight (S \ {c}) P ≤ w := by
  zuifb
  rcases arcs_merged_cases hM hS hfin hc hs hne' h with h' | h' | h'
  · exact (le_weight hM hS hfin (split_mem₁ hc hs) h').trans h1
  · exact (le_weight hM hS hfin (split_mem₂ hc hs) h').trans h2
  · exact hJ a b (gap_of_arc hne' h) h'

/-- The weights of `R₁` and `R₂` are at most the merged weight. -/
theorem weight_le_merged₁ (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) :
    M.weight S R₁ ≤ M.weight ztdb P := by
  zuwh

  zuifb
  obtain ⟨a', b', h', hle⟩ := arcs_merged_ge hM hS hfin hc hs h
  exact hle.trans (le_weight hM hS' hfin' hs.mem h')
theorem weight_le_merged₂ (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) :
    M.weight S R₂ ≤ M.weight ztdb P :=
  weight_le_merged₁ hM hS hfin hc hs.symm

/-- A gap of `S'` around a lost key weighs at most the merged weight. -/
theorem gap_le_merged (hM : WalkAx M) (hS : S ⊆ M.Adm) (hfin : S.Finite) (hc : c ∈ S)
    (hs : Merge.IsSplit M.D ztdb c P R₁ R₂) {k : ℝ} (hk : k ∈ lostKeys M S c) {l r : ℝ}
    (hg : Gap M ztdb l r) (hin : sideInArc l r k) :
    M.arcWt l r ≤ M.weight ztdb P := by
  zuwh

  exact le_weight hM hS' hfin' hs.mem (gap_lost_arc hM hS hfin hc hs hk hg hin)

/-- **The merged weight when `S'` is empty**: `size`. -/
theorem weight_merged_empty (hM : WalkAx M) (hs : Merge.IsSplit M.D ztdb c P R₁ R₂)
    (he : S \ {c} = ∅) : M.weight ztdb P = M.size := by
  zufts

  exact weight_empty hM hP
end Split

/-- **The model weight is local** (`Merge.WeightLocal` for `M.weight`), on the admissible
families of a model satisfying the walk axioms. -/
theorem weightLocal (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm) (hfin : F.Finite) :
    Merge.WeightLocal M.D F M.weight := by
  intro S hSF c hc X hX hcX
  have hS := hSF.trans hF
  have hSfin := hfin.subset hSF
  have hsys := hM.sys S hS hSfin
  obtain ⟨P, R₁, R₂, hs⟩ := Merge.exists_removal_split hsys subset_rfl hc
  have hX1 : X ≠ R₁ := by
    zunq
    exact hcX ((split_touches_iff hM hS hSfin hc hs hX).2 ztp)
  have hX2 : X ≠ R₂ := by
    zunq
    exact hcX ((split_touches_iff hM hS hSfin hc hs hX).2 ztbt)
  exact weight_other hM hS hSfin hc hs hX hX1 hX2
