module

public import Chazelle.Core.OutputWalk

/-!
# WP-N, part 3: chord records of a normal form of the full interior map

For the geometry polygon `Q` (simple, distinct heights) and a valid normal form `N` of the full
visibility map of the interior model `M = interiorModel Q`, whose chord records have their
height vertex `h < n` (see the report: `IsNF` does not bound `h`):

* a chord record describes a horizontal chord of `Q` at the height of vertex `h`, from the
  point of walk position `lpos` to that of `rpos` (`rec_hchord`);
* an end of the chord is the vertex `h` exactly when its walk edge starts at `h`
  (`pos_vtx`); otherwise it lies inside the edge `inp p` of `Q` carried by its walk edge `p`
  (`pos_open`).
-/

namespace Chazelle.Core

namespace OutNF

open Set Filter Topology
open Chazelle.Visibility
open Chazelle.Mountain (TrapData)
open Chazelle.Jordan (simple_vtx_inj succIdx_lt)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext point_ext_iff)
open Chazelle.Chain (SideAttach sidePt)
open OutWalk

@[expose] public section

variable {Q : Polygon}

/-! ## Walk positions of the interior model -/

section
variable {p : ℕ} (hp : p < Q.n)
include hp
/-- The start of walk edge `p` of the interior model. -/
theorem wa_eq :
    (interiorModel Q).wa p = Q.vtx (wv (revOf Q) Q.n p) := walk_vtx Q hp

/-- The end of walk edge `p` of the interior model. -/
theorem wb_eq :
    (interiorModel Q).wb p = Q.vtx (wv (revOf Q) Q.n (nxt Q.n p)) := walk_succ Q hp


end

/-- `wv` is injective below `n`. -/
theorem wv_inj {b : Bool} {n x y : ℕ} (hx : x < n) (hy : y < n) (h : wv b n x = wv b n y) :
    x = y := by
  rw [← wv_wv (b := b) hx, ← wv_wv (b := b) hy, h]

section
variable (hQ : Q.Simple) (hdh : DistinctHeights Q) {p : ℕ} (hp : p < Q.n)
include hQ hdh hp
/-- Walk edges are not horizontal (distinct heights). -/
theorem walk_nonhoriz :
    ((interiorModel Q).wa p).2 ≠ ((interiorModel Q).wb p).2 := by
  rw [wa_eq hp, wb_eq hp]
  have hn3 : 3 ≤ Q.n := hQ.1
  refine hdh _ _ (wv_lt hp) (wv_lt (nxt_lt hp)) fun h => ?_
  have := wv_inj hp (nxt_lt hp) h
  grind [nxt]

/-- The parameter of a walk position at the height of a vertex. -/
theorem param_eq (h : ℕ) :
    (interiorModel Q).param Q ⟨p, h + 1⟩ =
      ((Q.vtx h).2 - ((interiorModel Q).wa p).2) /
        (((interiorModel Q).wb p).2 - ((interiorModel Q).wa p).2) := by
  simp only [Model.param, Setup.iteF (walk_nonhoriz hQ hdh hp)]

/-- A walk position at the height of vertex `h` is at that height. -/
theorem pos_snd (h : ℕ) :
    ((interiorModel Q).pos Q ⟨p, h + 1⟩).2 = (Q.vtx h).2 := by
  have hne := walk_nonhoriz hQ hdh hp
  have hne' : ((interiorModel Q).wb p).2 - ((interiorModel Q).wa p).2 ≠ 0 :=
    sub_ne_zero.2 (Ne.symm hne)
  simp only [Model.pos, lerp_snd]
  rw [param_eq hQ hdh hp]
  simp_all


end

section
variable (hQ : Q.Simple) (hdh : DistinctHeights Q) {p h : ℕ} (hp : p < Q.n)
include hQ hdh hp
/-- **A walk position at the height of the start vertex of its walk edge is that vertex.** -/
theorem pos_vtx
    (hh : wv (revOf Q) Q.n p = h) : (interiorModel Q).pos Q ⟨p, h + 1⟩ = Q.vtx h := by
  have h0 : (interiorModel Q).param Q ⟨p, h + 1⟩ = 0 := by
    rw [param_eq hQ hdh hp, wa_eq hp, hh, sub_self, zero_div]
  simp only [Model.pos, h0, Geometry.lerp_zero]
  rw [wa_eq hp, hh]

/-- Otherwise the parameter is not zero. -/
theorem param_ne_zero
    (hh : h < Q.n) (hne : wv (revOf Q) Q.n p ≠ h) : (interiorModel Q).param Q ⟨p, h + 1⟩ ≠ 0 := by
  rw [param_eq hQ hdh hp]
  have hne' : ((interiorModel Q).wb p).2 - ((interiorModel Q).wa p).2 ≠ 0 :=
    sub_ne_zero.2 (Ne.symm (walk_nonhoriz hQ hdh hp))
  refine div_ne_zero (sub_ne_zero.2 ?_) hne'
  rw [wa_eq hp]
  exact hdh h _ hh (wv_lt hp) (Ne.symm hne)


end

/-- **A walk position with parameter in `(0, 1)` lies inside the edge of `Q` carried by its walk
edge.** -/
theorem pos_open {p : ℕ} (hp : p < Q.n) {x : WPos} (hx : x.edge = p)
    (ht : (interiorModel Q).param Q x ∈ Ioo (0 : ℝ) 1) :
    ∃ t ∈ Ioo (0 : ℝ) 1, (interiorModel Q).pos Q x =
      lerp (Q.vtx (inp (revOf Q) Q.n p)) (Q.vtx ((inp (revOf Q) Q.n p + 1) % Q.n)) t := by
  have he := inp_lt (b := revOf Q) hp
  simp only [Model.pos]
  rw [hx, wa_eq hp, wb_eq hp, ← nxt_eq he]
  rcases wv_inp (b := revOf Q) hp with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  all_goals (grind [Geometry.lerp_symm])

/-! ## Chord records -/

variable {N : NF}

/-- A chord record in range is a member of the chord list. -/
theorem chord_mem {k : ℕ} (hk : k < N.nChords) : N.chord k ∈ N.chords := by
  unfold NF.chord
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  grind

/-- The chord of a record is a chord of `Q`. -/
theorem rec_chords (hfull : N.F (interiorModel Q) Q = (interiorModel Q).Full) {k : ℕ}
    (hk : k < N.nChords) : (N.chord k).toSet (interiorModel Q) Q ∈ chords Q := by
  have : (N.chord k).toSet (interiorModel Q) Q ∈ N.F (interiorModel Q) Q :=
    ⟨N.chord k, chord_mem hk, rfl⟩
  aesop

/-- The walk edges of a record are walk edges and its parameters are in `[0, 1)`. -/
theorem rec_attach (hN : IsNF (interiorModel Q) Q N) {k : ℕ} (hk : k < N.nChords) :
    (N.chord k).lp < Q.n ∧ (N.chord k).rp < Q.n ∧
      0 ≤ (interiorModel Q).param Q (N.chord k).lpos ∧
      (interiorModel Q).param Q (N.chord k).lpos < 1 ∧
      0 ≤ (interiorModel Q).param Q (N.chord k).rpos ∧
      (interiorModel Q).param Q (N.chord k).rpos < 1 := by
  obtain ⟨hl, hr⟩ := hN.2.2.1 k hk
  have hn : (interiorModel Q).W.n = Q.n := walk_n Q
  exact ⟨hn ▸ hl.1, hn ▸ hr.1, hl.2.1, hl.2.2.1, hr.2.1, hr.2.2.1⟩

/-- **The chord of a record is a horizontal chord** at the height of its vertex, between the
points of its two walk positions. -/
theorem rec_hchord (hQ : Q.Simple) (hfull : N.F (interiorModel Q) Q = (interiorModel Q).Full)
    {k : ℕ} (hk : k < N.nChords) :
    IsHChord Q (Q.vtx (N.chord k).h).2 ((interiorModel Q).pos Q (N.chord k).lpos).1
      ((interiorModel Q).pos Q (N.chord k).rpos).1 := by
  have hc := rec_chords hfull hk
  obtain ⟨v, σ, hv, hσ, hdir, hS, hch⟩ := chords_spec hQ hc
  have e : hseg (Q.vtx v).2 (min (Q.vtx v).1 (chordEnd Q v σ).1) (max (Q.vtx v).1 (chordEnd Q v σ).1)
      = hseg (Q.vtx (N.chord k).h).2 ((interiorModel Q).pos Q (N.chord k).lpos).1
        ((interiorModel Q).pos Q (N.chord k).rpos).1 := by
    rw [← chordSet_eq_hseg, ← hS]; rfl
  obtain ⟨e1, e2, e3⟩ := Merge.hseg_inj hch.lt.le e
  grind

/-- The chord of a record as a horizontal segment. -/
theorem rec_toSet (k : ℕ) : (N.chord k).toSet (interiorModel Q) Q =
    hseg (Q.vtx (N.chord k).h).2 ((interiorModel Q).pos Q (N.chord k).lpos).1
      ((interiorModel Q).pos Q (N.chord k).rpos).1 := rfl

/-! ## Regions of the full interior map -/

/-- The regions of the full interior map are the regions of the visibility map. -/
theorem model_regions (hfull : N.F (interiorModel Q) Q = (interiorModel Q).Full) :
    (interiorModel Q).regions (N.F (interiorModel Q) Q) = regions Q := by
  aesop

/-- Just below a point of the open top side, the points are in the region. -/
theorem below_top (D : TrapData Q) {x : ℝ} (hx1 : edgeX Q D.i D.y₂ < x)
    (hx2 : x < edgeX Q D.j D.y₂) :
    ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ → ((x, D.y₂ - ε) : Point) ∈ D.region := by
  obtain ⟨ε₁, hε₁, h⟩ := Metric.eventually_nhds_iff.1 (D.isTrap.near_top hx1 hx2)
  refine ⟨ε₁, hε₁, fun ε hε hε' => h ?_ (by simp_all)⟩
  grind [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero, abs_neg]

section
variable (hQ : Q.Simple)
include hQ
/-- The end of a record at walk position `(p, h + 1)` whose walk edge does not start at `h`
lies inside the edge `inp p` of `Q`, hence is not a vertex. -/
theorem rec_end_open (hdh : DistinctHeights Q) {p h : ℕ} (hp : p < Q.n)
    (hh : h < Q.n) (hne : wv (revOf Q) Q.n p ≠ h)
    (ht0 : 0 ≤ (interiorModel Q).param Q ⟨p, h + 1⟩)
    (ht1 : (interiorModel Q).param Q ⟨p, h + 1⟩ < 1) :
    ∃ t ∈ Ioo (0 : ℝ) 1, (interiorModel Q).pos Q ⟨p, h + 1⟩ =
      lerp (Q.vtx (inp (revOf Q) Q.n p)) (Q.vtx ((inp (revOf Q) Q.n p + 1) % Q.n)) t :=
  pos_open hp rfl ⟨lt_of_le_of_ne ht0 (Ne.symm (param_ne_zero hQ hdh hp hh hne)), ht1⟩

/-- An end of a record inside an edge `e` of `Q`, lying on edge `f`, forces `e = f`. -/
theorem edge_eq_of_open {e f : ℕ} (he : e < Q.n) (hf : f < Q.n) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hmem : lerp (Q.vtx e) (Q.vtx ((e + 1) % Q.n)) t ∈ Q.edge f) :
    e = f := by
  by_contra hne
  exact Chazelle.Jordan.simple_openEdge_not_mem_other hQ he ht hf (Ne.symm hne) hmem

/-- **The chord records of a region.**  Every exit chord of the region `reg r = D.region` is at
its top (`dn = r`, vertex `top`) or at its bottom (`dn ≠ r`, vertex `bot`); an end of it whose
walk edge does not start at its vertex lies on the left side edge (left end) or on the right
side edge (right end). -/
theorem chord_facts (hdh : DistinctHeights Q) (hN : IsNF (interiorModel Q) Q N)
    (hfull : N.F (interiorModel Q) Q = (interiorModel Q).Full)
    (hh : ∀ k, k < N.nChords → (N.chord k).h < Q.n) {reg : ℕ → Set Point}
    (hcorr : RegionCorr (interiorModel Q) Q N reg)
    (hsides : ChordSidesOK (interiorModel Q) Q N reg) (hregs : RegionsOK (interiorModel Q) Q N reg)
    {r : ℕ} (hr : r < N.nRegions) (D : TrapData Q) (hD : D.region = reg r) {k : ℕ}
    (hk : k ∈ (N.region r).chords) :
    ((N.chord k).dn = r → (N.chord k).h = D.top) ∧ ((N.chord k).dn ≠ r → (N.chord k).h = D.bot) ∧
      (wv (revOf Q) Q.n (N.chord k).lp ≠ (N.chord k).h →
        inp (revOf Q) Q.n (N.chord k).lp = D.i) ∧
      (wv (revOf Q) Q.n (N.chord k).rp ≠ (N.chord k).h →
        inp (revOf Q) Q.n (N.chord k).rp = D.j) := by
  obtain ⟨hkN, z, ⟨hzc, hzD⟩, hzU⟩ := ((hregs r hr).1 k).1 hk
  rw [← hD] at hzU
  have hc := rec_chords hfull hkN
  have hhk := hh k hkN
  obtain ⟨hlp, hrp, hl0, hl1, hr0, hr1⟩ := rec_attach hN hkN
  have hch := rec_hchord hQ hfull hkN
  have hzc' := hzc
  rw [rec_toSet] at hzc'
  obtain ⟨hup, hdn, hside⟩ := hsides k hkN
  obtain ⟨ε₀, hε₀, hε⟩ := hside z hzc hzD
  have hregQ : ∀ s, s < N.nRegions → reg s ∈ regions Q := fun s hs => by
    rw [← model_regions hfull]; exact hcorr.1 s hs
  have hy12 : D.y₁ ≤ D.y₂ := (D.isTrap.bot_lt.trans D.isTrap.lt_top).le
  have hposl : ((interiorModel Q).pos Q (N.chord k).lpos).2 = (Q.vtx (N.chord k).h).2 :=
    pos_snd hQ hdh hlp _
  have hposr : ((interiorModel Q).pos Q (N.chord k).rpos).2 = (Q.vtx (N.chord k).h).2 :=
    pos_snd hQ hdh hrp _
  rcases OutGeom.touch_cases hQ D hc hzc hzD hzU with ⟨hz2, hz1, hz3⟩ | ⟨hz2, hz1, hz3⟩
  · -- a top chord
    have hhy : (Q.vtx (N.chord k).h).2 = D.y₂ := hzc'.1.symm.trans hz2
    have htop : (N.chord k).h = D.top := OutGeom.vtx_eq_top hdh D hQ hhk hhy
    have hdnr : (N.chord k).dn = r := by
      obtain ⟨ε₁, hε₁, hbelow⟩ := below_top D hz1 hz3
      set ε := min ε₀ ε₁ / 2 with hεd
      have hε0 : 0 < ε := by grind
      have e1 : ((z.1, z.2 - ε) : Point) ∈ reg (N.chord k).dn :=
        (hε ε hε0 (by grind)).2
      have e2 : ((z.1, z.2 - ε) : Point) ∈ reg r := by
        grind
      rcases regions_eq_or_disjoint (hregQ _ hdn) (hregQ _ hr) with he | he
      · exact hcorr.2.1 _ _ hdn hr he
      grind
    rw [hhy] at hch
    have hzs : z ∈ hseg D.y₂ ((interiorModel Q).pos Q (N.chord k).lpos).1
        ((interiorModel Q).pos Q (N.chord k).rpos).1 := by
      grind
    obtain ⟨-, hl, -, hr'⟩ := OutGeom.top_chord_ends hQ hdh D hch hzs hzD hz1 hz3
    refine ⟨fun _ => htop, fun h' => absurd hdnr h', fun hne => ?_, fun hne => ?_⟩
    · obtain ⟨t, ht, hpt⟩ := rec_end_open hQ hdh hlp hhk hne hl0 hl1
      have he := inp_lt (b := revOf Q) hlp
      rcases hl with hl | hl
      · refine edge_eq_of_open hQ he D.isTrap.hi ht ?_
        rw [← hpt]
        change (interiorModel Q).pos Q (N.chord k).lpos ∈ _
        exact D.isTrap.mem_edgeL (by grind) (by grind)
          (by grind)
      · exfalso
        refine Chazelle.Jordan.simple_openEdge_ne_vtx hQ he ht (D.top_lt hQ) ?_
        rw [← hpt]
        change (interiorModel Q).pos Q (N.chord k).lpos = _
        grind
    · obtain ⟨t, ht, hpt⟩ := rec_end_open hQ hdh hrp hhk hne hr0 hr1
      have he := inp_lt (b := revOf Q) hrp
      rcases hr' with hr' | hr'
      · refine edge_eq_of_open hQ he D.isTrap.hj ht ?_
        rw [← hpt]
        change (interiorModel Q).pos Q (N.chord k).rpos ∈ _
        exact D.isTrap.mem_edgeR (by grind) (by grind)
          (by grind)
      · exfalso
        refine Chazelle.Jordan.simple_openEdge_ne_vtx hQ he ht (D.top_lt hQ) ?_
        rw [← hpt]
        change (interiorModel Q).pos Q (N.chord k).rpos = _
        grind
  · -- a bottom chord
    have hhy : (Q.vtx (N.chord k).h).2 = D.y₁ := hzc'.1.symm.trans hz2
    have hbot : (N.chord k).h = D.bot := OutGeom.vtx_eq_bot hdh D hQ hhk hhy
    have hdnr : (N.chord k).dn ≠ r := by
      intro hdr
      have e1 : ((z.1, z.2 - ε₀ / 2) : Point) ∈ reg (N.chord k).dn :=
        (hε (ε₀ / 2) (half_pos hε₀) (by linarith)).2
      rw [hdr, ← hD] at e1
      have := e1.1
      grind
    rw [hhy] at hch
    have hzs : z ∈ hseg D.y₁ ((interiorModel Q).pos Q (N.chord k).lpos).1
        ((interiorModel Q).pos Q (N.chord k).rpos).1 := by
      grind
    obtain ⟨-, hl, -, hr'⟩ := OutGeom.bot_chord_ends hQ hdh D hch hzs hzD hz1 hz3
    refine ⟨fun h' => absurd h' hdnr, fun _ => hbot, fun hne => ?_, fun hne => ?_⟩
    · obtain ⟨t, ht, hpt⟩ := rec_end_open hQ hdh hlp hhk hne hl0 hl1
      have he := inp_lt (b := revOf Q) hlp
      rcases hl with hl | hl
      · refine edge_eq_of_open hQ he D.isTrap.hi ht ?_
        rw [← hpt]
        change (interiorModel Q).pos Q (N.chord k).lpos ∈ _
        exact D.isTrap.mem_edgeL (by grind) (by grind)
          (by grind)
      · exfalso
        refine Chazelle.Jordan.simple_openEdge_ne_vtx hQ he ht (D.bot_lt hQ) ?_
        rw [← hpt]
        change (interiorModel Q).pos Q (N.chord k).lpos = _
        grind
    · obtain ⟨t, ht, hpt⟩ := rec_end_open hQ hdh hrp hhk hne hr0 hr1
      have he := inp_lt (b := revOf Q) hrp
      rcases hr' with hr' | hr'
      · refine edge_eq_of_open hQ he D.isTrap.hj ht ?_
        rw [← hpt]
        change (interiorModel Q).pos Q (N.chord k).rpos ∈ _
        exact D.isTrap.mem_edgeR (by grind) (by grind)
          (by grind)
      · exfalso
        refine Chazelle.Jordan.simple_openEdge_ne_vtx hQ he ht (D.bot_lt hQ) ?_
        rw [← hpt]
        change (interiorModel Q).pos Q (N.chord k).rpos = _
        grind


end

/-- A chord of `Q` touching the region `reg r` is the chord of a record listed by the region. -/
theorem exists_rec (hfull : N.F (interiorModel Q) Q = (interiorModel Q).Full) {reg : ℕ → Set Point}
    (hregs : RegionsOK (interiorModel Q) Q N reg) {r : ℕ} (hr : r < N.nRegions)
    {c : Set Point} (hc : c ∈ chords Q) {z : Point} (hzc : z ∈ c)
    (hzD : z ∈ Q.filled \ Q.boundary) (hzU : z ∈ closure (reg r)) :
    ∃ k ∈ (N.region r).chords, (N.chord k).toSet (interiorModel Q) Q = c := by
  have hcF : c ∈ N.F (interiorModel Q) Q := by aesop
  obtain ⟨rc, hrc, rfl⟩ := hcF
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hrc
  have hck : N.chord k = N.chords[k] := by
    grind [NF.chord, List.getD_eq_getElem?_getD, Option.getD_some]
  refine ⟨k, ((hregs r hr).1 k).2 ⟨hk, z, ⟨?_, hzD⟩, hzU⟩, by rw [hck]⟩
  simp_all

section
variable (hQ : Q.Simple) (hdh : DistinctHeights Q) (hN : IsNF (interiorModel Q) Q N) (hfull : N.F (interiorModel Q) Q = (interiorModel Q).Full) (hh : ∀ k, k < N.nChords → (N.chord k).h < Q.n) {reg : ℕ → Set Point} (hcorr : RegionCorr (interiorModel Q) Q N reg) (hsides : ChordSidesOK (interiorModel Q) Q N reg) (hregs : RegionsOK (interiorModel Q) Q N reg) {r : ℕ} (hr : r < N.nRegions) (D : TrapData Q) (hD : D.region = reg r) {c : Set Point} (hc : c ∈ chords Q) {a b : ℝ}
include hQ hdh hN hfull hh reg hcorr hsides hregs hr hD hc
/-- A chord at the top height touching the region is the chord of a top record of it. -/
theorem top_chord_rec (hab : IsHChord Q D.y₂ a b)
    (hcab : c = hseg D.y₂ a b) {z : Point} (hzc : z ∈ c)
    (hzD : z ∈ Q.filled \ Q.boundary) (hzU : z ∈ closure D.region) :
    ∃ k ∈ (N.region r).chords, (N.chord k).dn = r ∧ (N.chord k).h = D.top ∧
      ((interiorModel Q).pos Q (N.chord k).lpos).1 = a ∧
      ((interiorModel Q).pos Q (N.chord k).rpos).1 = b := by
  rw [hD] at hzU
  obtain ⟨k, hk, hkc⟩ := exists_rec hfull hregs hr hc hzc hzD hzU
  obtain ⟨h1, h2, -, -⟩ := chord_facts hQ hdh hN hfull hh hcorr hsides hregs hr D hD hk
  
  rw [hcab, rec_toSet] at hkc
  obtain ⟨e1, e2, e3⟩ := Merge.hseg_inj hab.lt.le hkc.symm
  by_cases hdn : (N.chord k).dn = r
  · grind
  · exfalso
    have := h2 hdn
    rw [this, D.bot_snd hQ] at e1
    exact absurd e1.symm (D.isTrap.bot_lt.trans D.isTrap.lt_top).ne

/-- A chord at the bottom height touching the region is the chord of a bottom record of it. -/
theorem bot_chord_rec (hab : IsHChord Q D.y₁ a b)
    (hcab : c = hseg D.y₁ a b) {z : Point} (hzc : z ∈ c)
    (hzD : z ∈ Q.filled \ Q.boundary) (hzU : z ∈ closure D.region) :
    ∃ k ∈ (N.region r).chords, (N.chord k).dn ≠ r ∧ (N.chord k).h = D.bot ∧
      ((interiorModel Q).pos Q (N.chord k).lpos).1 = a ∧
      ((interiorModel Q).pos Q (N.chord k).rpos).1 = b := by
  rw [hD] at hzU
  obtain ⟨k, hk, hkc⟩ := exists_rec hfull hregs hr hc hzc hzD hzU
  obtain ⟨h1, h2, -, -⟩ := chord_facts hQ hdh hN hfull hh hcorr hsides hregs hr D hD hk
  rw [hcab, rec_toSet] at hkc
  obtain ⟨e1, e2, e3⟩ := Merge.hseg_inj hab.lt.le hkc.symm
  by_cases hdn : (N.chord k).dn = r
  · exfalso
    have := h1 hdn
    rw [this, D.top_snd hQ] at e1
    exact absurd e1 (D.isTrap.bot_lt.trans D.isTrap.lt_top).ne
  grind

/-! ## Region summaries -/


end

/-- The hypotheses on the geometry polygon, the normal form and its region correspondence. -/
structure RegCtx (Q : Polygon) (N : NF) (reg : ℕ → Set Point) : Prop where
  simple : Q.Simple
  dh : DistinctHeights Q
  nf : IsNF (interiorModel Q) Q N
  full : N.F (interiorModel Q) Q = (interiorModel Q).Full
  hlt : ∀ k, k < N.nChords → (N.chord k).h < Q.n
  corr : RegionCorr (interiorModel Q) Q N reg
  sides : ChordSidesOK (interiorModel Q) Q N reg
  regs : RegionsOK (interiorModel Q) Q N reg

variable {reg : ℕ → Set Point}

section
variable (H : RegCtx Q N reg) {r : ℕ} (hr : r < N.nRegions) (D : TrapData Q) (hD : D.region = reg r)
include H hr hD
/-- `chord_facts` under the bundled hypotheses. -/
theorem RegCtx.facts {k : ℕ} (hk : k ∈ (N.region r).chords) :
    ((N.chord k).dn = r → (N.chord k).h = D.top) ∧ ((N.chord k).dn ≠ r → (N.chord k).h = D.bot) ∧
      (wv (revOf Q) Q.n (N.chord k).lp ≠ (N.chord k).h →
        inp (revOf Q) Q.n (N.chord k).lp = D.i) ∧
      (wv (revOf Q) Q.n (N.chord k).rp ≠ (N.chord k).h →
        inp (revOf Q) Q.n (N.chord k).rp = D.j) :=
  chord_facts H.simple H.dh H.nf H.full H.hlt H.corr H.sides H.regs hr D hD hk

/-- **No top record: the top side is empty.** -/
theorem RegCtx.no_top (hno : ∀ k ∈ (N.region r).chords, (N.chord k).dn ≠ r) :
    edgeX Q D.j D.y₂ ≤ edgeX Q D.i D.y₂ := by
  by_contra hlt; push Not at hlt
  by_cases hL : (Q.vtx D.top).1 ≠ edgeX Q D.i D.y₂
  · obtain ⟨c, hc, b, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_top_chord_left H.simple H.dh D hL
    obtain ⟨k, hk, hdn, -⟩ := top_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides H.regs
      hr D hD hc hab hcab hzc hzD hzU
    simp_all
  · push Not at hL
    obtain ⟨c, hc, a, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_top_chord_right H.simple H.dh D (by grind)
    obtain ⟨k, hk, hdn, -⟩ := top_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides H.regs
      hr D hD hc hab hcab hzc hzD hzU
    simp_all

/-- **No bottom record: the bottom side is empty.** -/
theorem RegCtx.no_bot (hno : ∀ k ∈ (N.region r).chords, (N.chord k).dn = r) :
    edgeX Q D.j D.y₁ ≤ edgeX Q D.i D.y₁ := by
  by_contra hlt; push Not at hlt
  by_cases hL : (Q.vtx D.bot).1 ≠ edgeX Q D.i D.y₁
  · obtain ⟨c, hc, b, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_bot_chord_left H.simple H.dh D hL
    obtain ⟨k, hk, hdn, -⟩ := bot_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides H.regs
      hr D hD hc hab hcab hzc hzD hzU
    simp_all
  · push Not at hL
    obtain ⟨c, hc, a, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_bot_chord_right H.simple H.dh D (by grind)
    obtain ⟨k, hk, hdn, -⟩ := bot_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides H.regs
      hr D hD hc hab hcab hzc hzD hzU
    simp_all

/-- **All left ends at vertices: the top and bottom vertices are at the left corners.** -/
theorem RegCtx.all_left
    (hall : ∀ k ∈ (N.region r).chords, wv (revOf Q) Q.n (N.chord k).lp = (N.chord k).h) :
    (Q.vtx D.top).1 = edgeX Q D.i D.y₂ ∧ (Q.vtx D.bot).1 = edgeX Q D.i D.y₁ := by
  constructor
  · by_contra hL
    obtain ⟨c, hc, b, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_top_chord_left H.simple H.dh D hL
    obtain ⟨k, hk, -, hh, hl, -⟩ := top_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides
      H.regs hr D hD hc hab hcab hzc hzD hzU
    have hkN : k < N.nChords := (((H.regs r hr).1 k).1 hk).1
    have hp := pos_vtx H.simple H.dh (rec_attach H.nf hkN).1 (hall k hk)
    apply hL
    rw [← hl, ← hh]
    exact (congrArg Prod.fst hp).symm
  · by_contra hL
    obtain ⟨c, hc, b, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_bot_chord_left H.simple H.dh D hL
    obtain ⟨k, hk, -, hh, hl, -⟩ := bot_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides
      H.regs hr D hD hc hab hcab hzc hzD hzU
    have hkN : k < N.nChords := (((H.regs r hr).1 k).1 hk).1
    have hp := pos_vtx H.simple H.dh (rec_attach H.nf hkN).1 (hall k hk)
    apply hL
    rw [← hl, ← hh]
    exact (congrArg Prod.fst hp).symm

/-- **All right ends at vertices: the top and bottom vertices are at the right corners.** -/
theorem RegCtx.all_right
    (hall : ∀ k ∈ (N.region r).chords, wv (revOf Q) Q.n (N.chord k).rp = (N.chord k).h) :
    (Q.vtx D.top).1 = edgeX Q D.j D.y₂ ∧ (Q.vtx D.bot).1 = edgeX Q D.j D.y₁ := by
  constructor
  · by_contra hL
    obtain ⟨c, hc, a, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_top_chord_right H.simple H.dh D hL
    obtain ⟨k, hk, -, hh, -, hl⟩ := top_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides
      H.regs hr D hD hc hab hcab hzc hzD hzU
    have hkN : k < N.nChords := (((H.regs r hr).1 k).1 hk).1
    have hp := pos_vtx H.simple H.dh (rec_attach H.nf hkN).2.1 (hall k hk)
    apply hL
    rw [← hl, ← hh]
    exact (congrArg Prod.fst hp).symm
  · by_contra hL
    obtain ⟨c, hc, a, hab, hcab, z, hzc, hzD, hzU⟩ :=
      OutGeom.exists_bot_chord_right H.simple H.dh D hL
    obtain ⟨k, hk, -, hh, -, hl⟩ := bot_chord_rec H.simple H.dh H.nf H.full H.hlt H.corr H.sides
      H.regs hr D hD hc hab hcab hzc hzD hzU
    have hkN : k < N.nChords := (((H.regs r hr).1 k).1 hk).1
    have hp := pos_vtx H.simple H.dh (rec_attach H.nf hkN).2.1 (hall k hk)
    apply hL
    rw [← hl, ← hh]
    exact (congrArg Prod.fst hp).symm


end

/-- The two ends of a record are not both at its vertex. -/
theorem RegCtx.not_both (H : RegCtx Q N reg) {k : ℕ} (hkN : k < N.nChords)
    (hl : wv (revOf Q) Q.n (N.chord k).lp = (N.chord k).h)
    (hr : wv (revOf Q) Q.n (N.chord k).rp = (N.chord k).h) : False := by
  have hpl := pos_vtx H.simple H.dh (rec_attach H.nf hkN).1 hl
  have hpr := pos_vtx H.simple H.dh (rec_attach H.nf hkN).2.1 hr
  have hch := rec_hchord H.simple H.full hkN
  have e1 : ((interiorModel Q).pos Q (N.chord k).lpos).1 = (Q.vtx (N.chord k).h).1 :=
    congrArg Prod.fst hpl
  have e2 : ((interiorModel Q).pos Q (N.chord k).rpos).1 = (Q.vtx (N.chord k).h).1 :=
    congrArg Prod.fst hpr
  have := hch.lt
  simp_all

end

end OutNF

end Chazelle.Core
