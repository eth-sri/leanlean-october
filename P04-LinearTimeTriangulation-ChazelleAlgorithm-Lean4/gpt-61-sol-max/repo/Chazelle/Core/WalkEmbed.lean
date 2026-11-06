module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SpecMerge
public import Chazelle.Core.Facts2
public import Chazelle.Core.FactsL23

/-!
# Walk embeddings, part 1: stretches of two walks that agree (gap O1, generic part)

The weight bound of the revised fusion (`FusionWeightSpec`, `docs/design-merge-v2.md` §2.4)
compares an arc of the walk of `C = J.whole` with arcs of the walks of `C₁ = J.left` and
`C₂ = J.right`.  Away from the glue points the walks *agree*: read from suitable starting
vertices `g` (in `W`) and `g'` (in `W'`), they visit the same vertices for `L` steps
(`Agree W W' g g' L`).  This file proves the generic consequences of such an agreement.

* **Offsets on the cycle** (`off n g x`): the key `x` measured from the walk vertex `g`, and the
  translation of cyclic betweenness (`sideInArc`) into offsets (`sideInArc_iff_off`,
  `sideInArc_convex`, `sideInArc_right`, `sideInArc_left`).
* **Agreement** (`Agree`): positions at the same offset of two agreeing stretches have the same
  point, the same neighbours and the same left sector (`Agree.sidePt_eq`, `Agree.sideLeft_eq`),
  hence the same attached sets (`Agree.sideAttach_iff`) and the same faced sets
  (`Agree.faces_iff`) — the walk embedding of gap O1.
* **The stretch bound** (`arcWt_le_of_stretch`): if the counted edges and the cuts of a family
  `F'` of the model `M'` transfer along a stretch to the model `M` and a family `F`, and `F'` is
  γ-semigranular, then every `F`-cut-free key interval of `M` inside the stretch meets at most
  `γ` counted edges.  This is step (a) of the paper proof of the `γ + 1` bound.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sidePrev sideNext sideLeft sideKey_inj)

namespace WalkEmbed

/-! ## Offsets on a cycle -/

/-- The offset of the key `x` from the key `g` on a cycle of length `n` (both in `[0, n)`). -/
noncomputable def off (n g x : ℝ) : ℝ := if g ≤ x then x - g else x - g + n

theorem off_nonneg {n g x : ℝ} (hx : 0 ≤ x) (hg : g < n) : 0 ≤ off n g x := by
  core_grind

theorem off_lt {n g x : ℝ} (hx : x < n) (hg : 0 ≤ g) : off n g x < n := by
  core_grind

theorem off_self (n g : ℝ) : off n g g = 0 := by simp [off]

/-- The offset of a walk position: vertex `(g + d) mod n`, parameter `t`. -/
theorem off_key {n g d : ℕ} (hg : g < n) (hd : d < n) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    off n g (((g + d) % n : ℕ) + t) = d + t := by
  unfold off
  by_cases h : g + d < n
  · rw [Nat.mod_eq_of_lt h]
    grind
  · obtain ⟨k, hk⟩ : ∃ k, g + d = n + k := ⟨g + d - n, by omega⟩
    have hkg : k + 1 ≤ g := by omega
    have e : (g + d) % n = k := by
      rw [hk, Nat.add_mod_left, Nat.mod_eq_of_lt (show k < n by omega)]
    rw [e]
    have hlt' : (k : ℝ) + 1 ≤ g := by exact_mod_cast hkg
    have hk' : (g : ℝ) + d = n + k := by exact_mod_cast hk
    grind

/-- The offset (as a natural number) of the walk vertex `p` from the walk vertex `g`. -/
def dOf (n g p : ℕ) : ℕ := (p + n - g) % n

theorem dOf_lt {n : ℕ} (hn : 0 < n) (g p : ℕ) : dOf n g p < n := Nat.mod_lt _ hn

section
variable {n g p : ℕ} (hg : g < n) (hp : p < n)
include hg hp
theorem add_dOf : (g + dOf n g p) % n = p := by
  unfold dOf
  by_cases h : g ≤ p
  · have e : (p + n - g) % n = p - g := by
      rw [show p + n - g = (p - g) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e, show g + (p - g) = p by omega, Nat.mod_eq_of_lt hp]
  · have e : (p + n - g) % n = p + n - g := Nat.mod_eq_of_lt (show p + n - g < n by omega)
    rw [e, show g + (p + n - g) = p + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hp]

/-- The offset of a key on the walk vertex `p`. -/
theorem off_key' {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    off n g ((p : ℝ) + t) = dOf n g p + t := by
  have h := off_key hg (dOf_lt (by omega) g p) ht ht1
  rwa [add_dOf hg hp] at h


end

/-- Injectivity of `d ↦ (g + d) mod n` on `[0, n)`. -/
theorem add_mod_inj {n g d d' : ℕ} (hd : d < n) (hd' : d' < n) (h : (g + d) % n = (g + d') % n) :
    d = d' := by
  have h1 : d % n = d' % n := Nat.ModEq.add_left_cancel' g h
  rwa [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hd'] at h1

/-- **Cyclic intervals are intervals of offsets** (measured from a base key outside them). -/
theorem sideInArc_iff_off {n g u w x : ℝ} (_hg : 0 ≤ g) (_hgn : g < n) (hu : 0 ≤ u) (hun : u < n)
    (hw : 0 ≤ w) (hwn : w < n) (hx : 0 ≤ x) (hxn : x < n) (huw : off n g u < off n g w) :
    sideInArc u w x ↔ off n g u < off n g x ∧ off n g x < off n g w := by
  grind [off, sideInArc]

/-- **Convexity**: a cyclic interval not containing the base `g` contains every key whose
offset lies between the offsets of two of its keys. -/
theorem sideInArc_convex {n g a b x y w : ℝ} (_hg : 0 ≤ g) (_hgn : g < n) (hx : 0 ≤ x)
    (_hxn : x < n) (_hy : 0 ≤ y) (hyn : y < n) (hw : 0 ≤ w) (hwn : w < n)
    (hga : ¬ sideInArc a b g) (hxa : sideInArc a b x) (hya : sideInArc a b y)
    (h1 : off n g x < off n g w) (h2 : off n g w < off n g y) : sideInArc a b w := by
  core_grind

section
variable {l r z x : ℝ} (hlr : l ≠ r) (hz : sideInArc l r z) (hx : ¬ sideInArc l r x)
include l r hlr hz hx
/-- If `z` is inside `(l, r)` and `x` is not (and `x ≠ r`), then `r` lies between `z` and `x`. -/
theorem sideInArc_right
    (hxr : x ≠ r) : sideInArc z x r := by
  core_grind

/-- If `z` is inside `(l, r)` and `x` is not (and `x ≠ l`), then `l` lies between `x` and `z`. -/
theorem sideInArc_left
    (hxl : x ≠ l) : sideInArc x z l := by
  core_grind

/-! ## Agreeing stretches of two walks -/


end

/-- The walks `W` and `W'` **agree** on the stretch of length `L` starting at their vertices `g`
and `g'`: for `d ≤ L`, vertex `g + d` of `W` is vertex `g' + d` of `W'` (indices modulo the
lengths). -/
def Agree (W W' : Polygon) (g g' L : ℕ) : Prop :=
  ∀ d, d ≤ L → W.vtx ((g + d) % W.n) = W'.vtx ((g' + d) % W'.n)

theorem mod_succ_mod (n g d : ℕ) : ((g + d) % n + 1) % n = (g + (d + 1)) % n := by
  grind

theorem mod_pred_mod {n : ℕ} (hn : 0 < n) (g : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    ((g + d) % n + n - 1) % n = (g + (d - 1)) % n := by
  rw [show (g + d) % n + n - 1 = (g + d) % n + (n - 1) by omega, Nat.mod_add_mod,
    show g + d + (n - 1) = g + (d - 1) + n by omega, Nat.add_mod_right]

namespace Agree

variable {W W' : Polygon} {g g' L : ℕ}

section
variable (hA : Agree W W' g g' L) {d : ℕ} (hd : d < L)
include hA hd
/-- Agreeing stretches have the same point at the same offset. -/
theorem sidePt_eq (t : ℝ) :
    sidePt W ((g + d) % W.n) t = sidePt W' ((g' + d) % W'.n) t := by
  unfold sidePt
  rw [mod_succ_mod, mod_succ_mod, hA d hd.le, hA (d + 1) hd]

/-- Agreeing stretches have the same next vertex at the same offset. -/
theorem sideNext_eq :
    sideNext W ((g + d) % W.n) = sideNext W' ((g' + d) % W'.n) := by
  unfold sideNext
  rw [mod_succ_mod, mod_succ_mod, hA (d + 1) hd]


end

section
variable (hA : Agree W W' g g' L) (hn : 0 < W.n) (hn' : 0 < W'.n) {d : ℕ} (hd : d < L) {t : ℝ} (ht : t = 0 → 1 ≤ d)
include hA hn hn' hd ht
/-- Agreeing stretches have the same previous point at the same offset, away from the start. -/
theorem sidePrev_eq :
    sidePrev W ((g + d) % W.n) t = sidePrev W' ((g' + d) % W'.n) t := by
  unfold sidePrev
  by_cases h0 : t = 0
  · rw [ite_eq_left h0, ite_eq_left h0, mod_pred_mod hn _ (ht h0), mod_pred_mod hn' _ (ht h0),
      hA (d - 1) (by omega)]
  aesop (add safe (by omega))

/-- **Agreeing stretches have the same left sectors** at the same offset, away from the
start. -/
theorem sideLeft_eq :
    sideLeft W ((g + d) % W.n) t = sideLeft W' ((g' + d) % W'.n) t := by
  funext x
  unfold sideLeft
  rw [hA.sidePrev_eq hn hn' hd ht, hA.sidePt_eq hd, hA.sideNext_eq hd]

/-- **Agreeing stretches attach the same sets** at the same offset (the walk embedding preserves
`SideAttach`). -/
theorem sideAttach_iff (c : Set Point) :
    SideAttach W c ((g + d) % W.n) t ↔ SideAttach W' c ((g' + d) % W'.n) t := by
  unfold SideAttach
  rw [hA.sideLeft_eq hn hn' hd ht, hA.sidePt_eq hd]
  constructor
  · rintro ⟨-, h⟩; exact ⟨Nat.mod_lt _ hn', h⟩
  · rintro ⟨-, h⟩; exact ⟨Nat.mod_lt _ hn, h⟩

/-- A set attached to `W'` at an offset of the stretch attaches its subsets through the same
point to `W` at the same offset. -/
theorem sideAttach_subset {c e : Set Point}
    (hc : SideAttach W' c ((g' + d) % W'.n) t) (hec : e ⊆ c)
    (he : sidePt W' ((g' + d) % W'.n) t ∈ e) : SideAttach W e ((g + d) % W.n) t := by
  rw [hA.sideAttach_iff hn hn' hd ht]
  obtain ⟨hp, ht0, ht1, -, r, hr, hl⟩ := hc
  exact ⟨hp, ht0, ht1, he, r, hr, fun x hx => hl x (hec hx)⟩


end

end Agree

/-! ## The stretch bound -/

/-- An arc meets at most `n` walk edges. -/
theorem arcWt_le_n (M : Model) (a b : ℝ) : M.arcWt a b ≤ M.W.n := by
  rw [Model.arcWt_eq]
  calc (M.arcEdges a b).ncard ≤ (Set.Iio M.W.n).ncard :=
        Set.ncard_le_ncard (fun p hp => hp.1) (Set.finite_Iio _)
    _ = M.W.n := by rw [Set.ncard_eq_toFinset_card', Set.toFinset_Iio, Nat.card_Iio]

/-- The weight of a region bounds its arcs. -/
theorem arcWt_le_weight (M : Model) {F : Set (Set Point)} {U : Set Point} {a b : ℝ}
    (h : M.IsArc F U a b) : M.arcWt a b ≤ M.weight F U :=
  le_csSup ⟨M.W.n, by rintro _ ⟨ab, -, rfl⟩; exact arcWt_le_n M _ _⟩ ⟨(a, b), h, rfl⟩

/-- Every non-cut key inside a walk edge of a good model lies in an arc of some region. -/
theorem exists_arc_around {M : Model} (hM : GoodModel M) {Q : Polygon} {F : Set (Set Point)}
    (hF : M.ChordFamily Q F) {x : ℝ} (hx0 : 0 < x) (hx : ¬ M.IsCut F x) :
    ∃ U ∈ M.regions F, ∃ l r : ℝ, M.IsArc F U l r ∧ sideInArc l r x := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨⟨U, hU, a, b, harc⟩, -⟩ := arcCover M Q ∅ hM hF
    rcases harc.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, rfl, rfl⟩
    all_goals (grind [sideInArc])
  · exact (walkAx_of_goodModel hM).arc_around hF.2.1 hF.1 hne hx

/-- **The stretch bound (step (a) of the `γ + 1` bound).**  Let the counted edges and the cuts of
a γ-semigranular family `F'` of a good model `M'` transfer to a family `F` of a model `M` along a
stretch of length `L` (starting at the walk vertices `g` of `M` and `g'` of `M'`).  Then every
`F`-cut-free key interval of `M` whose keys lie strictly inside the stretch meets at most `γ`
counted edges. -/
theorem arcWt_le_of_stretch {M M' : Model} (hM' : GoodModel M') {Q : Polygon}
    {F F' : Set (Set Point)} (hF' : M'.ChordFamily Q F') {γ : ℕ} (hsg : M'.Semigranular F' γ)
    {g g' L : ℕ} (hg : g < M.W.n) (hg' : g' < M'.W.n) (hLn : L ≤ M.W.n) (hLn' : L ≤ M'.W.n)
    (hcount : ∀ d, d < L → M.counted ((g + d) % M.W.n) → M'.counted ((g' + d) % M'.W.n))
    (hcut : ∀ d, d < L → ∀ t : ℝ, 0 ≤ t → t < 1 → 0 < (d : ℝ) + t →
      M'.IsCut F' (((g' + d) % M'.W.n : ℕ) + t) → M.IsCut F (((g + d) % M.W.n : ℕ) + t))
    {a b : ℝ}
    (hstr : ∀ x : ℝ, 0 ≤ x → x < M.W.n → sideInArc a b x →
      0 < off M.W.n g x ∧ off M.W.n g x < L)
    (hfree : ∀ x, sideInArc a b x → ¬ M.IsCut F x) :
    M.arcWt a b ≤ γ := by
  classical
  set n := M.W.n with hn_def
  set n' := M'.W.n with hn'_def
  have hn : 0 < n := by omega
  have hn' : 0 < n' := by omega
  have hgR : (g : ℝ) < n := by exact_mod_cast hg
  have hg'R : (g' : ℝ) < n' := by exact_mod_cast hg'
  -- keys of the walk of `M` inside a walk edge
  have hkey : ∀ p : ℕ, p < n → ∀ t : ℝ, 0 ≤ t → t < 1 → 0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < n :=
    fun p hp t ht ht1 => by
      have : (p : ℝ) + 1 ≤ n := by exact_mod_cast hp
      grind
  have hkey' : ∀ p : ℕ, p < n' → ∀ t : ℝ, 0 ≤ t → t < 1 →
      0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < n' :=
    fun p hp t ht ht1 => by
      have : (p : ℝ) + 1 ≤ n' := by exact_mod_cast hp
      exact ⟨by positivity, by linarith⟩
  -- a key of the walk of `M` met by the interval has its offset in the stretch
  have hin : ∀ p : ℕ, p < n → ∀ t : ℝ, 0 < t → t < 1 → sideInArc a b (p + t) →
      dOf n g p < L ∧ (p = (g + dOf n g p) % n) ∧ off n g (p + t) = dOf n g p + t := by
    intro p hp t ht ht1 hx
    have hoff := off_key' hg hp ht.le ht1
    have hs := hstr _ (hkey p hp t ht.le ht1).1 (hkey p hp t ht.le ht1).2 hx
    rw [hoff] at hs
    refine ⟨?_, (add_dOf hg hp).symm, hoff⟩
    have : (dOf n g p : ℝ) < L := by linarith
    exact_mod_cast this
  -- the base of the stretch is not in the interval
  have hga : ¬ sideInArc a b g := fun h => by
    have := (hstr g (Nat.cast_nonneg g) hgR h).1
    rw [off_self] at this; grind
  -- a cut of `F'` strictly inside the stretch between two keys of the interval gives a cut
  -- of `F` inside the interval
  have htransfer : ∀ (p q : ℕ) (t u : ℝ), p < n → q < n → 0 < t → t < 1 → 0 < u → u < 1 →
      sideInArc a b (p + t) → sideInArc a b (q + u) → ∀ y' : ℝ, M'.IsCut F' y' →
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
      exact_mod_cast this
    have hcut' := hcut dr hdrL tr htr0 htr1 (by
      linarith) (by rw [add_dOf hg' hpr]; exact ⟨c, hc, pr, tr, hA, rfl⟩)
    have hoffy := off_key hg (show dr < n by omega) htr0 htr1
    have hyb := hkey ((g + dr) % n) (Nat.mod_lt _ hn) tr htr0 htr1
    have hpb := hkey p hp t ht.le ht1
    have hqb := hkey q hq u hu.le hu1
    refine hfree _ ?_ hcut'
    exact sideInArc_convex (Nat.cast_nonneg g) hgR hpb.1 hpb.2 hqb.1 hqb.2 hyb.1 hyb.2 hga
      hpin hqin (by grind) (by grind)
  rw [Model.arcWt_eq]
  rcases (M.arcEdges a b).eq_empty_or_nonempty with hE | ⟨p₀, hp₀n, -, t₀, ht₀, ht₀1, hx₀⟩
  · rw [hE, Set.ncard_empty]; omega
  obtain ⟨hd₀L, hp₀, hoff₀⟩ := hin p₀ hp₀n t₀ ht₀ ht₀1 hx₀
  set d₀ := dOf n g p₀
  set z' : ℝ := (((g' + d₀) % n' : ℕ) : ℝ) + t₀ with hz'
  have hd₀n' : d₀ < n' := by omega
  -- `z'` is not a cut of `F'`
  have hz'cut : ¬ M'.IsCut F' z' := by
    intro hc
    have := hcut d₀ hd₀L t₀ ht₀.le ht₀1 (by positivity) hc
    rw [← hp₀] at this
    exact hfree _ hx₀ this
  have hz'pos : 0 < z' := by positivity
  obtain ⟨U', hU', l', r', harc', hz'in⟩ := exists_arc_around hM' hF' hz'pos hz'cut
  have hwt : M'.arcWt l' r' ≤ γ := (arcWt_le_weight M' harc').trans (hsg U' hU')
  -- the edge map
  let f : ℕ → ℕ := fun p => (g' + dOf n g p) % n'
  have hmaps : Set.MapsTo f (M.arcEdges a b) (M'.arcEdges l' r') := by
    rintro p ⟨hpn, hpc, t, ht, ht1, hx⟩
    obtain ⟨hdL, hp, hoff⟩ := hin p hpn t ht ht1 hx
    set d := dOf n g p
    have hdn' : d < n' := by omega
    refine ⟨Nat.mod_lt _ hn', hcount d hdL (hp ▸ hpc), t, ht, ht1, ?_⟩
    set x' : ℝ := ((f p : ℕ) : ℝ) + t with hx'
    have hx'cut : ¬ M'.IsCut F' x' := by
      intro hc
      have := hcut d hdL t ht.le ht1 (by positivity) hc
      rw [← hp] at this
      exact hfree _ hx this
    by_contra hnot
    rcases harc'.2.2.2.2.1 with ⟨hl'c, hr'c, hl'r'⟩ | ⟨-, rfl, rfl⟩
    · have hx'r : x' ≠ r' := fun h => hx'cut (h ▸ hr'c)
      have hx'l : x' ≠ l' := fun h => hx'cut (h ▸ hl'c)
      -- offsets in the walk of `M'`
      have hoffz : off n' g' z' = d₀ + t₀ := off_key hg' hd₀n' ht₀.le ht₀1
      have hoffx : off n' g' x' = d + t := off_key hg' hdn' ht.le ht1
      have hz'b : 0 ≤ z' ∧ z' < n' := hkey' ((g' + d₀) % n') (Nat.mod_lt _ hn') t₀ ht₀.le ht₀1
      have hx'b : 0 ≤ x' ∧ x' < n' := hkey' (f p) (Nat.mod_lt _ hn') t ht.le ht1
      have hg'0 : (0 : ℝ) ≤ g' := Nat.cast_nonneg g'
      rcases lt_trichotomy ((d₀ : ℝ) + t₀) (d + t) with hlt | heq | hgt
      · have hr := sideInArc_right hl'r' hz'in hnot hx'r
        obtain ⟨c, hc, pr, tr, hA, hr'eq⟩ := hr'c
        have hrb := hkey' pr hA.1 tr hA.2.1 hA.2.2.1
        rw [← hr'eq] at hrb
        rw [sideInArc_iff_off hg'0 hg'R hz'b.1 hz'b.2 hx'b.1 hx'b.2 hrb.1 hrb.2
          (by rw [hoffz, hoffx]; exact hlt), hoffz, hoffx] at hr
        exact htransfer p₀ p t₀ t hp₀n hpn ht₀ ht₀1 ht ht1 hx₀ hx r' ⟨c, hc, pr, tr, hA, hr'eq⟩
          hr.1 hr.2
      · obtain ⟨e1, e2⟩ := sideKey_inj ht₀.le ht₀1 ht.le ht1 heq
        apply hnot
        rw [hx', show f p = (g' + d₀) % n' by simp only [f, d, e1]] at *
        rw [← e2]; exact hz'in
      · have hl := sideInArc_left hl'r' hz'in hnot hx'l
        obtain ⟨c, hc, pl, tl, hA, hl'eq⟩ := hl'c
        have hlb := hkey' pl hA.1 tl hA.2.1 hA.2.2.1
        rw [← hl'eq] at hlb
        rw [sideInArc_iff_off hg'0 hg'R hx'b.1 hx'b.2 hz'b.1 hz'b.2 hlb.1 hlb.2
          (by rw [hoffz, hoffx]; exact hgt), hoffz, hoffx] at hl
        exact htransfer p p₀ t t₀ hpn hp₀n ht ht1 ht₀ ht₀1 hx hx₀ l' ⟨c, hc, pl, tl, hA, hl'eq⟩
          hl.1 hl.2
    · apply hnot
      unfold sideInArc; rw [ite_eq_right (lt_irrefl _)]; left; positivity
  have hinj : Set.InjOn f (M.arcEdges a b) := by
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
  core_grind

/-- **A piece of the walk of `M`**: a stretch starting at the walk vertex `g`, of length `L < n`,
whose two end keys lie in `K`, along which every `F`-cut-free key interval meets at most `γ`
counted edges. -/
def PieceOK (M : Model) (F : Set (Set Point)) (K : Set ℝ) (γ g L : ℕ) : Prop :=
  g < M.W.n ∧ L < M.W.n ∧ (g : ℝ) ∈ K ∧ (((g + L) % M.W.n : ℕ) : ℝ) ∈ K ∧
    ∀ a b : ℝ, (∀ x : ℝ, 0 ≤ x → x < M.W.n → sideInArc a b x →
        0 < off M.W.n g x ∧ off M.W.n g x < L) →
      (∀ x, sideInArc a b x → ¬ M.IsCut F x) → M.arcWt a b ≤ γ

/-- **Assembly**: if every key inside a counted walk edge lies strictly inside some piece, then every
`F`-cut-free key interval avoiding `K` meets at most `γ` counted edges.  (Such an interval is
confined to the piece of any of its counted keys, because it avoids the end keys of the piece.) -/
theorem arcWt_le_of_pieces {M : Model} {F : Set (Set Point)} {K : Set ℝ} {γ : ℕ}
    (hcover : ∀ p : ℕ, p < M.W.n → M.counted p → ∀ t : ℝ, 0 < t → t < 1 →
      ∃ g L, PieceOK M F K γ g L ∧ 0 < off M.W.n g (p + t) ∧ off M.W.n g (p + t) < L)
    {a b : ℝ} (hK : ∀ x ∈ K, ¬ sideInArc a b x) (hfree : ∀ x, sideInArc a b x → ¬ M.IsCut F x) :
    M.arcWt a b ≤ γ := by
  classical
  
  rcases (M.arcEdges a b).eq_empty_or_nonempty with hE0 | ⟨p₀, hp₀n, hp₀c, t₀, ht₀, ht₀1, hx₀⟩
  · grind [Model.arcWt_eq, Set.ncard_empty]
  obtain ⟨g, L, ⟨hg, hLn, hgK, heK, hbound⟩, hz0, hzL⟩ := hcover p₀ hp₀n hp₀c t₀ ht₀ ht₀1
  refine hbound a b (fun x hx0 hxn hx => ?_) hfree
  set n := M.W.n
  have hgR : (g : ℝ) < n := by exact_mod_cast hg
  have hga : ¬ sideInArc a b g := hK _ hgK
  have hz : 0 ≤ (p₀ : ℝ) + t₀ ∧ (p₀ : ℝ) + t₀ < n := by
    have : (p₀ : ℝ) + 1 ≤ n := by exact_mod_cast hp₀n
    exact ⟨by positivity, by linarith⟩
  have hxg : x ≠ g := fun e => hga (e ▸ hx)
  have hx0' : 0 < off n g x := by
    rcases (off_nonneg hx0 hgR).lt_or_eq with h | h
    · exact h
    · exact absurd (off_inj (Nat.cast_nonneg g) hgR hx0 hxn (Nat.cast_nonneg g) hgR
        (by grind [off_self])) hxg
  refine ⟨hx0', ?_⟩
  by_contra hge
  push Not at hge
  set e : ℕ := (g + L) % n
  have hen : e < n := Nat.mod_lt _ (by omega)
  have heR : (e : ℝ) < n := by exact_mod_cast hen
  have hoffe : off n g e = L := by
    have := off_key (t := 0) hg hLn le_rfl one_pos
    grind
  have hea : ¬ sideInArc a b e := hK _ heK
  rcases hge.lt_or_eq with hlt | heq
  · exact hea (sideInArc_convex (Nat.cast_nonneg g) hgR hz.1 hz.2 hx0 hxn (Nat.cast_nonneg e) heR
      hga hx₀ hx (by grind) (by grind))
  · have := off_inj (Nat.cast_nonneg g) hgR hx0 hxn (Nat.cast_nonneg e) heR (by grind)
    simp_all

/-! ## Small cyclic facts -/

section
variable {a b k x : ℝ} (hk : sideInArc a b k)
include hk
theorem sideInArc_sub_left (hx : sideInArc a k x) :
    sideInArc a b x := by
  core_grind

theorem sideInArc_sub_right (hx : sideInArc k b x) :
    sideInArc a b x := by
  core_grind


end

section
variable {a b k q x : ℝ} (hk : sideInArc a b k) (hq : ¬ sideInArc a b q)
include a b hk hq
/-- A cut `q` just after an inner key `k` bounds the part of the interval after `k`. -/
theorem sideInArc_before_cut
    (hkq : k < q) (hx : sideInArc k b x) : sideInArc k q x := by
  core_grind

/-- A cut `q` just before an inner key `k` bounds the part of the interval before `k`. -/
theorem sideInArc_after_cut
    (hqk' : q < k) (hx : sideInArc a k x) : sideInArc q k x := by
  core_grind


end

/-- An interval inside one walk edge meets at most that edge. -/
theorem arcWt_le_one_of_within (M : Model) {k : ℕ} {a b : ℝ} (hab : a < b) (ha : (k : ℝ) ≤ a)
    (hb : b ≤ k + 1) : M.arcWt a b ≤ 1 := by
  rw [Model.arcWt_eq]
  calc (M.arcEdges a b).ncard ≤ ({k} : Set ℕ).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.finite_singleton k)
        rintro p ⟨-, -, t, ht0, ht1, hx⟩
        unfold sideInArc at hx
        rw [ite_eq_left hab] at hx
        have h1 : (p : ℝ) < k + 1 := by linarith
        have h2 : (k : ℝ) < p + 1 := by linarith
        have h1' : p < k + 1 := by exact_mod_cast h1
        have h2' : k < p + 1 := by exact_mod_cast h2
        grind
    _ = 1 := Set.ncard_singleton k

end WalkEmbed

end

end Chazelle.Core
