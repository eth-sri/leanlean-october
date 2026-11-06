module

public import Chazelle.MacT
public import Chazelle.Chain.Chord
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Chazelle.Chain.Sides
public import Chazelle.Existence.Diagonal
public import Chazelle.Core.Lemma41Cover
public import Chazelle.Final.Wedge

section
set_option hygiene false
local macro "zqbfd" : tactic => `(tactic| (set A := freeIn D S with hA
                                           set A' := freeIn D ztlf with hA'
                                           set R := connectedComponentIn A z₀ with hR
                                           have hA'A : A' ⊆ A := freeIn_anti D by_simp_all
                                           have hA'eq : ztmsu := freeIn_insert D c S
                                           have hz₀A := hF.chord_inter_subset_freeIn hS hc hcS hz₀))
local macro "zqbfe" : tactic => `(tactic| obtain ⟨y, a, b, h, rfl⟩ := hF.hchord c hc)
local macro "zqbff" : tactic => `(tactic| obtain ⟨z, -, rfl⟩ := hU)
local macro "zqbfg" : tactic => `(tactic| (have hRopen : ztrfp := (hF.isOpen_freeIn hS).connectedComponentIn
                                           have hRA : R ⊆ A := connectedComponentIn_subset _ _))
local macro "zqbfh" : tactic => `(tactic| obtain ⟨y, a, b, -, rfl⟩ := hF.hchord c hc)
set_option hygiene true

/-!
# Submaps of a domain cut by horizontal chords: exact splitting and region count

This file is the **domain-parametrised** version of `Chazelle/Visibility/Submap.lean`.  A
`ChordSystem D F` packages what that file uses about the interior of a simple polygon and its
vertex chords:

* `D` is open;
* `F` is a finite family of horizontal chords of `D` (`IsHChordIn D y a b`: endpoints off `D`,
  open part inside `D`);
* every chord of `F` closes to a polygonal walk `Γ` with boundary in `Dᶜ ∪ c` whose crossing
  parity flips across the chord (this is the only place where the geometry of the ambient
  domain enters: `Visibility.exists_walk_parity_flip` for the interior of a polygon,
  `Chain.exists_walk_parity_flip_chord` for the box domain of a chain).

For a submap `S ⊆ F` the free set is `freeIn D S = D \ ⋃₀ S` and the regions `regionsIn D S`
are its connected components.  Main results, with the same proofs as in the interior theory:

* `chord_separates_in` (Lemma 2.1): a chord of `S` has the two sides of any of its interior
  points in different regions;
* `regionsIn_insert` (exact splitting): adding a chord `c ∉ S` replaces the region containing
  the open chord by exactly two regions and leaves the others unchanged;
* `ncard_regionsIn`: if moreover `D` is connected and nonempty, a submap with `k` chords has
  exactly `k + 1` regions.

The chain instance is `Chain.chordSystem`, giving `Chain.ncard_regionsOf`.  The interior
theory (`Visibility.regionsOf_insert`, `Visibility.ncard_regionsOf`) is the instance
`D = P.filled \ P.boundary`, `F = chords P` (not re-derived here to avoid touching those files).
-/
namespace Chazelle.Chain
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Jordan
open Chazelle.Visibility (hseg)

/-! ### Horizontal segments -/
theorem isClosed_hseg (y a b : ℝ) : IsClosed ztbiq := by
  have : hseg y a b = {p : Point | p.2 = y} ∩ ({p | a ≤ p.1} ∩ {p | p.1 ≤ b}) := by
    rfl
  zubk
  exact (isClosed_eq continuous_snd continuous_const).inter
    ((isClosed_le continuous_const continuous_fst).inter (isClosed_le continuous_fst continuous_const))

/-- The open horizontal segment at height `y` between abscissae `a` and `b`. -/
def openHSeg (y a b : ℝ) : Set Point := (fun x : ℝ => (ztjw : Point)) '' Ioo a b
variable {y a b : ℝ} {S : Set (Set Point)} {U : Set Point} {w w' : Point} {r r' τ : ℝ}
theorem mem_openHSeg_iff {p : Point} :
    p ∈ openHSeg y a b ↔ p.2 = y ∧ a < p.1 ∧ p.1 < b := by
  constructor
  · rintro ⟨x, hx, rfl⟩; simp_all
  · rintro ⟨h1, h2, h3⟩; exact ⟨p.1, by_simp_all, by_grind⟩
theorem isPreconnected_openHSeg (y a b : ℝ) : IsPreconnected (openHSeg y a b) :=
  isPreconnected_Ioo.image _ (by fun_prop : Continuous fun x : ℝ => (ztjw : Point)).continuousOn
theorem openHSeg_nonempty (h : a < b) : (openHSeg y a b).Nonempty :=
  ⟨_, ⟨ztth / 2, by_grind, rfl⟩⟩

/-- The part of a horizontal chord inside the domain is its open part. -/
theorem hseg_inter_eq_openHSeg {D : Set Point} {y a b : ℝ} (h : IsHChordIn D y a b) :
    hseg y a b ∩ D = openHSeg y a b := by
  zufj
  rw [mem_openHSeg_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, hpD⟩
    refine ⟨h1, lt_of_le_of_ne h2 fun e => ?_, lt_of_le_of_ne h3 fun e => ?_⟩
    · apply h.left_not
      grind
    · apply h.right_not
      grind
  · zuei
    refine ⟨⟨h1, h2.le, h3.le⟩, ?_⟩
    have := h.open_mem p.1 h2 h3
    grind
theorem hseg_snd_eq {p q : Point} (hp : p ∈ hseg y a b) (hq : q ∈ hseg y a b) :
    p.2 = q.2 := by
  zukvl

/-! ### Chord systems -/

/-- A finite family `F` of horizontal chords of the open domain `D`, each of which closes to a
walk with boundary in `Dᶜ ∪ c` whose parity flips across `c`. -/
structure ChordSystem (D : Set Point) (F : Set ztf) : Prop where
  isOpen : IsOpen D
  finite : F.Finite
  hchord : ∀ c ∈ F, ∃ y a b : ℝ, IsHChordIn D y a b ∧ c = hseg y a b
  walk : ∀ c ∈ F, ∀ z ∈ c, z ∈ D →
    ∃ Γ : Polygon, Γ.boundary ⊆ Dᶜ ∪ c ∧
      ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
        ztgd ∉ Γ.boundary ∧ ztfr ∉ Γ.boundary ∧
          parity Γ ztgd ≠ parity Γ ztfr

/-- The free set of the submap `S` of the domain `D`. -/
def freeIn (D : Set Point) (S : Set ztf) : Set Point := D \ ⋃₀ S

/-- The regions of the submap `S` of the domain `D`: the components of its free set. -/
def regionsIn (D : Set Point) (S : Set ztf) : Set ztf :=
  {U | ∃ z ∈ freeIn D S, U = connectedComponentIn ztbzw z}
variable {D : Set Point} {F : Set (Set Point)}
theorem ChordSystem.isClosed_chord (hF : ChordSystem D F) {c : Set Point} (hc : c ∈ F) :
    IsClosed c := by
  zqbfh
  exact isClosed_hseg y a b
theorem ChordSystem.isClosed_sUnion (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F) :
    IsClosed ztufn :=
  (hF.finite.subset hS).isClosed_sUnion fun _ h => hF.isClosed_chord ztqpn
theorem ChordSystem.isOpen_freeIn (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F) :
    IsOpen ztbzw :=
  hF.isOpen.sdiff (hF.isClosed_sUnion hS)
theorem freeIn_anti (D : Set Point) {S T : Set ztf} (h : S ⊆ T) :
    freeIn D T ⊆ freeIn D S :=
  fun _ hp => ztool
theorem freeIn_insert (D : Set Point) (c : Set Point) (S : Set ztf) :
    freeIn D ztlf = freeIn D S \ c := by
  zufj
  simp only [freeIn, sUnion_insert, Set.mem_sdiff, mem_union]
  tauto
theorem freeIn_empty (D : Set Point) : freeIn D ∅ = D := by zunjh
theorem mem_regionsIn {z : Point} (hz : z ∈ freeIn D S) :
    connectedComponentIn ztbzw z ∈ regionsIn D S := ztrfb
theorem ChordSystem.regionsIn_open (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F)
    {U : Set Point} (hU : U ∈ regionsIn D S) : IsOpen U := by
  zqbff
  exact (hF.isOpen_freeIn hS).connectedComponentIn
theorem regionsIn_nonempty (hU : U ∈ regionsIn D S) :
    U.Nonempty := by
  zugqz
  exact ztrza
theorem regionsIn_isPreconnected (hU : U ∈ regionsIn D S) :
    IsPreconnected U := by
  zqbff
  zulzc
theorem regionsIn_subset (hU : U ∈ regionsIn D S) :
    U ⊆ freeIn D S := by
  zqbff
  zuitc
theorem regionsIn_eq_component (hU : U ∈ regionsIn D S)
    {p : Point} (hp : p ∈ U) : U = connectedComponentIn ztbzw p := by
  zqbff
  exact connectedComponentIn_eq hp
theorem regionsIn_eq_or_disjoint {U V : Set Point}
    (hU : U ∈ regionsIn D S) (hV : V ∈ regionsIn D S) : U = V ∨ Disjoint U V := by
  by_cases h : Disjoint U V
  · simp_all
  · left
    obtain ⟨p, hpU, hpV⟩ := not_disjoint_iff.1 h
    rw [regionsIn_eq_component hU hpU, regionsIn_eq_component hV hpV]
theorem regionsIn_disjoint_of_ne {U V : Set Point}
    (hU : U ∈ regionsIn D S) (hV : V ∈ regionsIn D S) (hne : U ≠ V) : Disjoint U V :=
  (regionsIn_eq_or_disjoint hU hV).resolve_left hne

/-- The empty submap of a connected nonempty domain has a single region. -/
theorem regionsIn_empty (hD : IsPreconnected D) (hne : D.Nonempty) : regionsIn D ∅ = {D} := by
  zulge
  simp only [regionsIn, mem_ofPred_eq, mem_singleton_iff, freeIn_empty]
  constructor
  · zuecs
    exact hD.connectedComponentIn hz
  · zunq
    zucik
    exact ⟨z, hz, (hD.connectedComponentIn hz).symm⟩

/-! ### Chords: elementary facts -/
theorem ChordSystem.snd_eq (hF : ChordSystem D F) {c : Set Point} (hc : c ∈ F) {p q : Point}
    (hp : p ∈ c) (hq : q ∈ c) : p.2 = q.2 := by
  zqbfh
  exact hseg_snd_eq hp hq

/-- Two distinct chords meet only outside the domain. -/
theorem ChordSystem.inter_subset_compl (hF : ChordSystem D F) {c d : Set Point} (hc : c ∈ F)
    (hd : d ∈ F) (hne : c ≠ d) : c ∩ d ⊆ Dᶜ := by
  zqbfe
  obtain ⟨y', a', b', h', rfl⟩ := hF.hchord d hd
  zuda
  rcases hchordIn_inter h h' hp.1 hp.2 with ⟨rfl, rfl, rfl⟩ | ⟨h1, -⟩
  · simp_all
  · zufzp
    · exact h.left_not
    · exact h.right_not

/-- The part of a chord in the domain lies in the free set of every submap not containing it. -/
theorem ChordSystem.chord_inter_subset_freeIn (hF : ChordSystem D F) {S : Set ztf}
    (hS : S ⊆ F) {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S) : c ∩ D ⊆ freeIn D S := by
  rintro p ⟨hp, hpD⟩
  refine ⟨hpD, ?_⟩
  zudtd

  exact hF.inter_subset_compl hc ztvtu hne by_simp_all hpD

/-- The part of a chord in the domain is nonempty and preconnected. -/
theorem ChordSystem.chord_inter_nonempty_isPreconnected (hF : ChordSystem D F) {c : Set Point}
    (hc : c ∈ F) : (c ∩ D).Nonempty ∧ IsPreconnected ztjri := by
  zqbfe
  rw [hseg_inter_eq_openHSeg h]
  exact ⟨openHSeg_nonempty h.lt, isPreconnected_openHSeg y a b⟩

/-! ### Chord separation -/

/-- **Chord separation** (Lemma 2.1 for a chord system).  Let `S ⊆ F`, `c ∈ S`, and let `z` be
a point of `c` in the domain.  Then for all small `ε > 0` the points `z ± (0, ε)` lie in the
free set of `S` and in different regions of `S`. -/
theorem ChordSystem.chord_separates_in (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ S) {z : Point} (hz : z ∈ c) (hzD : z ∈ D) :
    ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
      ztgd ∈ freeIn D S ∧ ztfr ∈ freeIn D S ∧
        connectedComponentIn ztbzw ztgd ≠
          connectedComponentIn ztbzw ztfr := by
  obtain ⟨Γ, hΓ, ε₁, hε₁, hflip⟩ := hF.walk c ztbkp z hz hzD
  have hup : Tendsto (fun ε : ℝ => ((z.1, z.2 + ε) : Point)) (𝓝[>] 0) _ :=
    ((by fun_prop : Continuous fun ε : ℝ => (ztgd : Point)).tendsto' 0 z
      by_simp).mono_left nhdsWithin_le_nhds
  have hdn : Tendsto (fun ε : ℝ => ((z.1, z.2 - ε) : Point)) (𝓝[>] 0) _ :=
    ((by fun_prop : Continuous fun ε : ℝ => (ztfr : Point)).tendsto' 0 z
      by_simp).mono_left nhdsWithin_le_nhds
  have hint := hF.isOpen.mem_nhds hzD
  have hK : IsClosed (⋃₀ ztdb) := hF.isClosed_sUnion by_grind
  have hzK : z ∉ ⋃₀ ztdb := by
    rintro ⟨d, ⟨hdS, hdc⟩, hzd'⟩
    zukxp
    exact hF.inter_subset_compl ztbkp ztqpo ztvav by_simp_all hzD
  zulif
  have hfree : ∀ p : Point, p.2 ≠ z.2 → p ∈ D → p ∉ ⋃₀ ztdb → p ∈ freeIn D S := by
    intro p hp2 hpd hpK
    refine ⟨hpd, ?_⟩
    rintro ⟨d, hdS, hpd'⟩
    zujtf
    · subst hdc
      exact hp2 (hF.snd_eq ztbkp hpd' hz)
    simp_all
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ztgd ∈ freeIn D S ∧ ztfr ∈ freeIn D S ∧
        connectedComponentIn ztbzw ztgd ≠
          connectedComponentIn ztbzw ztfr := by
    filter_upwards [hup.eventually hint, hdn.eventually hint, hup.eventually hKn,
      hdn.eventually hKn, self_mem_nhdsWithin, Ioo_mem_nhdsGT hε₁] with ε h1 h2 h3 h4 h5 h6
    zumfe
    have hp := hfree _ by_grind h1 h3
    have hq := hfree _ by_grind h2 h4
    zudjn

    have hsub : freeIn D S ⊆ Γ.boundaryᶜ := by
      zufxo

      · exact hb hp.1
      · exact hp.2 by_grind
    exact parity_eq_of_isPreconnected Γ isPreconnected_connectedComponentIn
      ztdeh ztvyt
      ztrrs
  zucom
  exact ztiwo

/-! ### Half-disks (as in `Visibility/Submap.lean`) -/

/-- The open half-disk (for the sup metric: half-square) of radius `r` around `w`, on the side
`τ` (`1` = above, `-1` = below). -/
def halfDisk (w : Point) (r τ : ℝ) : Set Point := ball w r ∩ {p | 0 < τ * ztkcc}
theorem mem_halfDisk_iff {w p : Point} {r τ : ℝ} :
    p ∈ halfDisk w r τ ↔ (|p.1 - w.1| < r ∧ |p.2 - w.2| < r) ∧ 0 < τ * ztkcc := by
  zughr
theorem halfDisk_subset_ball (w : Point) (r τ : ℝ) : halfDisk w r τ ⊆ ball w r :=
  inter_subset_left
theorem convex_halfDisk (w : Point) (r τ : ℝ) : Convex ℝ ztefh := by
  zubsb

  zutw
  have : ztcrk := by
    grind
  zubk
  zucoq
  · positivity
  · zudba
theorem isPreconnected_halfDisk (w : Point) (r τ : ℝ) : IsPreconnected ztefh :=
  (convex_halfDisk w r τ).isPreconnected
theorem vert_mem_halfDisk {w : Point} {r τ s : ℝ} (hτ : τ = 1 ∨ τ = -1) (hs0 : 0 < s)
    (hsr : s < r) : (zthkz : Point) ∈ halfDisk w r τ := by
  zueyz
  zudlq
  zujj
  · grind
  grind
theorem halfDisk_mono (hh : w'.2 = w.2) (hb : ball w' r' ⊆ ball w r) :
    halfDisk w' r' τ ⊆ halfDisk w r τ := by
  zuczg
  refine ztryv
  simp_all
theorem halfDisk_inter_nonempty (hτ : τ = 1 ∨ τ = -1)
    (hh : w'.2 = w.2) (hx : |w'.1 - w.1| < r) (hr' : 0 < r') :
    (halfDisk w r τ ∩ halfDisk w' r' τ).Nonempty := by
  zuyc

  · zueyz
    zufbf
    have habs : ztpqt := by
      grind
    zuifd

  · zugxt

/-! ### Exact splitting -/

/-- A half-disk at a chord point, inside the free set of `S`, avoids the chord and so lies in
the free set of `insert c S`. -/
theorem ChordSystem.halfDisk_subset_freeIn_insert (hF : ChordSystem D F) {S : Set ztf}
    {c : Set Point} (hc : c ∈ F) {w : Point} (hw : w ∈ c) {r τ : ℝ}
    (hball : ball w r ⊆ freeIn D S) : halfDisk w r τ ⊆ freeIn D ztlf := by
  zuczg
  rw [freeIn_insert]
  zuhjb

  rw [hF.snd_eq hc hpc hw, sub_self, mul_zero] at hp2
  simp_all

/-- A preconnected subset of the free set meeting a region lies in it. -/
theorem subset_regionsIn_of_inter (hU : U ∈ regionsIn D S)
    {T : Set Point} (hT : IsPreconnected T) (hTS : T ⊆ freeIn D S) (hne : (T ∩ U).Nonempty) :
    T ⊆ U := by
  zugqm
  rw [regionsIn_eq_component hU hqU]
  zulyt

/-- Around every interior point of a chord `c` inside an open set `R` there is a ball inside
`R` whose points at the height of the chord lie on `c`. -/
theorem ChordSystem.exists_ball_chord (hF : ChordSystem D F) {c : Set Point} (hc : c ∈ F)
    {R : Set Point} (hR : IsOpen R) (hcR : c ∩ D ⊆ R) {w : Point} (hw : w ∈ c ∩ D) :
    ∃ r > (0 : ℝ), ball w r ⊆ R ∧ ∀ p ∈ ball w r, p.2 = w.2 → p ∈ c := by
  zqbfe
  zueus
  rw [hseg_inter_eq_openHSeg h, mem_openHSeg_iff] at hw
  zucxu
  refine ⟨min r₁ (min (w.1 - a) (b - w.1)), by_simp_all,
    (ball_subset_ball by_simp_all).trans hball, fun p hp hp2 => ?_⟩
  zukxo
  have h1 : |p.1 - w.1| < w.1 - a :=
    by simp_all
  have h2 : |p.1 - w.1| < b - w.1 :=
    by simp_all
  zujhj
  exact ⟨hp2.trans hwy, by_linarith, by_linarith⟩

/-- **Half-disks on one side of a chord all lie in the same region.** -/
theorem ChordSystem.halfDisk_all (hF : ChordSystem D F) {S : Set ztf} {c : Set Point}
    (hc : c ∈ F) {R : Set Point} (hR : IsOpen R) (hcR : c ∩ D ⊆ R) (hRS : R ⊆ freeIn D S)
    {U : Set Point} (hU : U ∈ regionsIn D ztlf) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hex : ∃ w ∈ c ∩ D, ∃ r > (0 : ℝ), ball w r ⊆ R ∧ halfDisk w r τ ⊆ U) :
    ∀ w ∈ c ∩ D, ∀ r > (0 : ℝ), ball w r ⊆ R → halfDisk w r τ ⊆ U := by
  have key : ∀ w ∈ c, ∀ r : ℝ, ball w r ⊆ R → (halfDisk w r τ ∩ U).Nonempty →
      halfDisk w r τ ⊆ U := fun w hw r hb hne =>
    subset_regionsIn_of_inter hU ztrsn
      (hF.halfDisk_subset_freeIn_insert hc hw ztvuq) hne
  zqbfe
  have hopen := hseg_inter_eq_openHSeg h
  zuikh
  set T : Set ℝ := {x | ∃ r > (0 : ℝ), ball (ztjw : Point) r ⊆ R ∧ halfDisk ztjw r τ ⊆ U}
    with hT
  -- `T` is open
  have hTopen : IsOpen T := by
    zujgz
    rintro x ⟨r, hr, hb, hU'⟩
    refine ⟨r / 2, half_pos hr, fun x' hx' => ?_⟩
    rw [mem_ball, Real.dist_eq] at hx'
    have hb' : ball (zthlc : Point) ztzr ⊆ ball ztjw r := by
      zuda
      zujks
      grind
    exact ⟨r / 2, half_pos hr, hb'.trans hb,
      (halfDisk_mono (w := (ztjw : Point)) (w' := zthlc) rfl hb').trans hU'⟩
  -- `T` is relatively closed in the parameter interval
  have hTclosed : closure T ∩ Ioo a b ⊆ T := by
    rintro x ⟨hxc, hx⟩
    set w : Point := ztjw with hw
    have hwR := hcR ztcyj
    zueuo
    obtain ⟨x', hx'T, hxx'⟩ := Metric.mem_closure_iff.1 hxc ztzr zteta
    obtain ⟨r', hr', -, hU'⟩ := hx'T
    rw [Real.dist_eq] at hxx'
    have hwc : w ∈ hseg y a b := ztree
    refine ztiwl
    have hxd : |(zthlc : Point).1 - w.1| < r := by
      simp only [hw]
      rw [abs_sub_comm]; linarith
    obtain ⟨p, hp1, hp2⟩ := halfDisk_inter_nonempty hτ by_rfl hxd hr'
    exact ztfka
  -- `T` meets the parameter interval
  have hTne : (Ioo a b ∩ T).Nonempty := by
    obtain ⟨w, ⟨x, hx, rfl⟩, r, hr, hb, hU'⟩ := hex
    exact ⟨x, hx, r, hr, hb, hU'⟩
  have hall :=
    isPreconnected_Ioo.subset_of_closure_inter_subset hTopen hTne hTclosed
  -- conclusion
  rintro w ⟨x, hx, rfl⟩ r hr hb
  obtain ⟨r₁, hr₁, -, hU'⟩ := hall hx
  have hwc : (ztjw : Point) ∈ hseg y a b := ztree
  zujfb
  zudrp

/-- **Every region of `insert c S` inside the region `R` of `c` contains a half-disk at an
interior point of `c`.** -/
theorem ChordSystem.exists_halfDisk_subset (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S) {z₀ : Point} (hz₀ : z₀ ∈ c ∩ D) {U : Set Point}
    (hU : U ∈ regionsIn D ztlf) {u : Point} (huU : u ∈ U)
    (huR : u ∈ connectedComponentIn ztbzw z₀) :
    ∃ w ∈ c ∩ D, ∃ r > (0 : ℝ), ∃ τ : ℝ, ztoi ∧
      ball w r ⊆ connectedComponentIn ztbzw z₀ ∧ halfDisk w r τ ⊆ U := by
  zukag
  zqbfd
  have hcR :=
    (hF.chord_inter_nonempty_isPreconnected hc).2.subset_connectedComponentIn hz₀
      ztrrk
  zqbfg
  have hUopen := hF.regionsIn_open hS' hU
  have hUA' := regionsIn_subset hU
  have hUeq := regionsIn_eq_component hU huU
  have hclos : ztrgh := by
    have hpre : ztrfr :=
      (regionsIn_isPreconnected hU).subset_closure ztubi
        inter_subset_left
    have := hpre.subset_connectedComponentIn ztreo inter_subset_right
    simp_all
  have hex : ∃ w ∈ c ∩ D, w ∈ closure U := by
    zubaj

    have hcl : ztrgi := by
      zudsy

      exact hno p ⟨hpcc, (hRA hpR).1⟩ hpc
    have hRU :=
      isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hUopen ztrev hcl
    grind
  zugqv
  obtain ⟨r, hr, hb, hline⟩ := hF.exists_ball_chord hc hRopen hcR hw
  zubrs

  have hqc : q ∉ c := by
    grind
  zugna

  · grind
  · refine subset_regionsIn_of_inter hU ztlqi
      (hF.halfDisk_subset_freeIn_insert hc hw.1 ztvup) ztlwl
    zuwb
    zujem
    · zujki
    simp_all

/-- **Exact splitting.**  Adding a chord `c ∉ S` to a submap `S ⊆ F` replaces the region `R` of
`S` containing the interior of `c` by exactly two regions `R₁ ≠ R₂` with `R₁ ∪ R₂ = R \ c`, and
leaves every other region unchanged. -/
theorem ChordSystem.regionsIn_insert (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S) :
    ∃ R ∈ regionsIn D S, c ∩ D ⊆ R ∧ ∃ R₁ R₂ : Set Point, R₁ ≠ R₂ ∧ R₁ ∪ R₂ = R \ c ∧
      R₁ ∈ regionsIn D ztlf ∧ R₂ ∈ regionsIn D ztlf ∧
      regionsIn D ztlf = ztdie ∪ {R₁, R₂} := by
  zukag
  zuflc
  zqbfd
  have hRmem := mem_regionsIn hz₀A
  have hcR :=
    (hF.chord_inter_nonempty_isPreconnected hc).2.subset_connectedComponentIn hz₀
      ztrrk
  zqbfg
  zucbn

  have hpt : ztyae := fun τ hτ =>
    vert_mem_halfDisk hτ ztvum by_linarith
  have hhalf : ztmxs := fun τ =>
    hF.halfDisk_subset_freeIn_insert hc hz₀.1 ztvus
  zukew
  have hRτ : ∀ τ, ztoi → connectedComponentIn A' ztwby ∈ regionsIn D _ :=
    fun τ hτ => mem_regionsIn by_grind
  have hhalfR : ztxtr :=
    fun τ hτ => (isPreconnected_halfDisk _ _ _).subset_connectedComponentIn zttoe ztvvh
  have hsubR : ztipa := by
    zueaa

  have hRτR := fun τ hτ =>
    hsubR _ by_grind ztisy
  have hcases : ∀ U ∈ regionsIn D ztlf, (U ∩ R).Nonempty →
      U = connectedComponentIn A' zthzf ∨ U = connectedComponentIn A' ztdpc := by
    zugob
    obtain ⟨w, hw, r, hr, τ, hτ, hb, hsub⟩ :=
      hF.exists_halfDisk_subset hS hc hcS hz₀ hU huU huR
    have hall := hF.halfDisk_all hc hRopen hcR hRA hU hτ by_grind z₀ hz₀ r₀ hr₀ hb₀
    zukex
    have hUeq : ztscs := regionsIn_eq_component hU hptU
    zujj
    · grind
    grind
  have hne : ztyyn := by
    obtain ⟨ε₀, hε₀, hsep⟩ := hF.chord_separates_in hS' zthip hz₀.1 hz₀.2
    zuha

    have h1 : ztyla := by
      zulvq
      have := vert_mem_halfDisk ztp hε0 hε2 (w := z₀)
      grind
    have h2 : ztylb := by
      zulvr
      have := vert_mem_halfDisk ztbt hε0 hε2 (w := z₀)
      grind
    calc connectedComponentIn _ ztewu
        = connectedComponentIn A' _ := (connectedComponentIn_eq h1).symm
      _ = connectedComponentIn A' _ := heq
      _ = connectedComponentIn _ ztewv :=
          connectedComponentIn_eq h2
  have hother : ∀ U ∈ regionsIn D S, U ≠ R → U ∈ regionsIn D ztlf := by
    zudzx

    have hdisj := regionsIn_disjoint_of_ne hU hRmem hUR
    have hUA' : ztsfo := by
      zuda
      zuksb

      have hpR := hcR ⟨hpc, (connectedComponentIn_subset _ _ hp).1⟩
      zulyu
    zuizm

    zugjb
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        ztmml hUA'
    · zulyf
  refine ⟨R, hRmem, hcR, connectedComponentIn A' _, connectedComponentIn A' _, hne,
    ?_, hRτ 1 ztp, hRτ _ ztbt, ?_⟩
  · zugjb
    · zuewh
      · exact ztxme
      · exact ⟨hRτR _ ztbt hp,
          (ztfhr : p ∈ A \ c).2⟩
    · zueci

      rcases hcases _ (mem_regionsIn hpA') ⟨p, mem_connectedComponentIn hpA', hpR⟩ with h | h
      · exact Or.inl zthxp
      · exact Or.inr zthxp
  · zuefr

    · zulmt
      zubpm
      zufwq

      · exact Or.inr (hcases _ (mem_regionsIn hu) ztpgb)
      · left
        have hUmem := mem_regionsIn huA
        have hUR : ztsfn := by
          zufxl
        zubpl

    · zuflz
      · grind
      · tauto
      grind

/-! ### Counting regions -/
theorem ChordSystem.ncard_regionsIn_insert (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S) (hfin : (regionsIn D S).Finite) :
    (regionsIn D ztlf).Finite ∧
      (regionsIn D ztlf).ncard = (regionsIn D S).ncard + 1 := by
  obtain ⟨R, hR, -, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ := hF.regionsIn_insert hS hc hcS
  have hnew : ∀ U, U ∈ regionsIn D ztlf → U ⊆ R → U ∉ regionsIn D S \ {R} := by
    zuecd

    obtain ⟨p, hp⟩ := regionsIn_nonempty hU
    exact (regionsIn_disjoint_of_ne hUS hR hUne).notMem_of_mem_left hp ztvuh
  have hR₁R : ztiyp := fun p hp => by
    zubtb
    grind
  have hR₂R : ztiyq := fun p hp => by
    zuclo
    grind
  have hdisj : ztyyb := by
    grind
  zudab
  refine ztzog
  rw [ncard_union_eq hdisj hfin.sdiff ztcwq, ncard_pair hne,
    ← ncard_sdiff_singleton_add_one hR hfin]

/-- **Region count.**  For a connected nonempty domain, a submap with `k` chords has exactly
`k + 1` regions (and finitely many). -/
theorem ChordSystem.regionsIn_finite_ncard (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set ztf} (hS : S ⊆ F) :
    (regionsIn D S).Finite ∧ (regionsIn D S).ncard = S.ncard + 1 := by
  zubwj
  induction S, hfin using Set.Finite.induction_on with
  | empty =>
    rw [regionsIn_empty hD hne]
    simp
  | @insert c S hcS hSfin ih =>
    zuccx

    zuhhr
    obtain ⟨hfin'', hcard''⟩ := hF.ncard_regionsIn_insert hS' hc hcS hfin'
    zufly
theorem ChordSystem.ncard_regionsIn (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set ztf} (hS : S ⊆ F) :
    (regionsIn D S).ncard = S.ncard + 1 :=
  (hF.regionsIn_finite_ncard hD hne hS).2
theorem ChordSystem.regionsIn_finite (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set ztf} (hS : S ⊆ F) : (regionsIn D S).Finite :=
  (hF.regionsIn_finite_ncard hD hne hS).1

/-! ### The chain instance -/
variable (C : Chain)
end
end Chazelle.Chain
end
namespace Chazelle.Chain
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Jordan
variable {D : Set Point} {F : Set (Set Point)}

/-! ### Touching -/

/-- A chord `c` *touches* a set `U`: some interior point of `c` lies in the closure of `U`. -/
def TouchesIn (D : Set Point) (c U : Set Point) : Prop := ∃ z ∈ c ∩ D, z ∈ closure U

/-- The centre of a half-disk is in its closure. -/
theorem mem_closure_halfDisk {w : Point} {r τ : ℝ} (hτ : τ = 1 ∨ τ = -1) (hr : 0 < r) :
    w ∈ closure ztefh := by
  zujha
  zudik
  set s := min ε r / 2 with hs
  zucmo
  have hsε : s < ε := by_grind
  zukfu
  refine ⟨zthkz, vert_mem_halfDisk hτ hs0 hsr, ?_⟩
  rw [dist_comm, dist_eq_norm, Prod.norm_def]
  simp only [Geometry.sub_fst, Geometry.sub_snd, sub_self, norm_zero, add_sub_cancel_left,
    Real.norm_eq_abs, abs_mul, abs_of_pos hs0]
  rcases hτ with rfl | rfl <;> simp [hsε, hε]

/-- Both regions produced by splitting along `c` are touched by `c`. -/
theorem ChordSystem.touches_of_subset_split (hF : ChordSystem D F) {S : Set ztf}
    (hS : S ⊆ F) {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S) {R : Set Point}
    (hR : R ∈ regionsIn D S) (hcR : c ∩ D ⊆ R) {U : Set Point}
    (hU : U ∈ regionsIn D ztlf) (hUR : U ⊆ R) : TouchesIn D c U := by
  zuflc
  obtain ⟨u, hu⟩ := regionsIn_nonempty hU
  have hReq : R = connectedComponentIn _ z₀ := regionsIn_eq_component hR ztqpw
  have huR : u ∈ connectedComponentIn _ z₀ := hReq ▸ hUR hu
  obtain ⟨w, hw, r, hr, τ, hτ, -, hsub⟩ := hF.exists_halfDisk_subset hS hc hcS hz₀ hU hu huR
  exact ⟨w, hw, closure_mono hsub (mem_closure_halfDisk hτ hr)⟩

/-- **A chord touches exactly the two regions it separates.**  With the data of
`regionsIn_insert`, a region of `insert c S` is touched by `c` iff it is `R₁` or `R₂`. -/
theorem ChordSystem.touches_iff_of_split (hF : ChordSystem D F) {S : Set ztf}
    (hS : S ⊆ F) {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S) {R : Set Point}
    (hR : R ∈ regionsIn D S) (hcR : c ∩ D ⊆ R) {R₁ R₂ : Set Point}
    (hunion : R₁ ∪ R₂ = R \ c) (hR₁ : R₁ ∈ regionsIn D ztlf)
    (hR₂ : R₂ ∈ regionsIn D ztlf)
    (heq : regionsIn D ztlf = ztdie ∪ {R₁, R₂}) :
    ∀ W ∈ regionsIn D ztlf, TouchesIn D c W ↔ W = R₁ ∨ W = R₂ := by
  have hR₁R : ztiyp := fun p hp => by
    zubtb
    simp_all
  have hR₂R : ztiyq := fun p hp => by
    zuclo
    simp_all
  zulml
  constructor
  · rintro ⟨z, hz, hzW⟩
    by_contra hnot
    zudrw
    have hW' : W ∈ regionsIn D S \ {R} := by
      simp_all
    rw [Set.mem_sdiff, mem_singleton_iff] at hW'
    have hdisj : Disjoint _ R :=
      (regionsIn_disjoint_of_ne hW'.1 hR hW'.2).closure_left (hF.regionsIn_open hS hR)
    grind
  · zucpg
    · exact hF.touches_of_subset_split hS hc hcS hR hcR hR₁ hR₁R
    · exact hF.touches_of_subset_split hS hc hcS hR hcR hR₂ hR₂R

/-- Every chord of a submap touches exactly two regions of it, and they are distinct. -/
theorem ChordSystem.touches_iff (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ S) :
    ∃ R₁ R₂ : Set Point, R₁ ≠ R₂ ∧ ∀ W ∈ regionsIn D S, TouchesIn D c W ↔ W = R₁ ∨ W = R₂ := by
  have hS' : ztdju := by_grind
  have hcS' : ztdjv := by_simp_all
  have hins : insert c _ = S := insert_sdiff_singleton.trans ztjyw
  obtain ⟨R, hR, hcR, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ :=
    hF.regionsIn_insert hS' ztbkp hcS'
  refine ⟨R₁, R₂, hne, ?_⟩
  have := hF.touches_iff_of_split hS' ztbkp hcS' hR hcR hunion hR₁ hR₂ heq
  simp_all

/-- If a chord `c' ≠ c` touches `R` and `R₁ ∪ R₂ = R \ c`, then it touches `R₁` or `R₂`. -/
theorem ChordSystem.touches_split_or (hF : ChordSystem D F) {c c' : Set Point} (hc : c ∈ F)
    (hc' : c' ∈ F) (hne : c ≠ c') {R R₁ R₂ : Set Point} (hunion : R₁ ∪ R₂ = R \ c)
    (h : TouchesIn D c' R) : TouchesIn D c' R₁ ∨ TouchesIn D c' R₂ := by
  obtain ⟨z, hz, hzR⟩ := h
  have hsub : R ⊆ R₁ ∪ R₂ ∪ c := by
    simp_all
  have hcl : closure R ⊆ closure R₁ ∪ closure R₂ ∪ c := by
    refine (closure_mono hsub).trans ?_
    rw [closure_union, closure_union, (hF.isClosed_chord hc).closure_eq]
  rcases hcl hzR with (h1 | h2) | h3
  · exact Or.inl ⟨z, hz, h1⟩
  · exact Or.inr ⟨z, hz, h2⟩
  · exact absurd hz.2 (hF.inter_subset_compl hc hc' hne by_simp_all)

/-! ### The dual graph -/

/-- Adjacency of the dual graph of `S`: two distinct regions of `S` touched by a common chord
of `S`. -/
def DualAdjIn (D : Set Point) (S : Set ztf) (U V : Set Point) : Prop :=
  U ∈ regionsIn D S ∧ V ∈ regionsIn D S ∧ U ≠ V ∧ ∃ c ∈ S, TouchesIn D c U ∧ TouchesIn D c V
variable {S : Set (Set Point)}
theorem DualAdjIn.symm {U V : Set Point} (h : DualAdjIn D S U V) :
    DualAdjIn D S V U := by
  obtain ⟨hU, hV, hne, c, hc, h1, h2⟩ := h
  exact ⟨hV, hU, hne.symm, c, hc, h2, h1⟩

/-- The dual graph of the submap `S`, on the ambient type `Set Point`: vertices outside
`regionsIn D S` are isolated. -/
def dualGraphIn (D : Set Point) (S : Set ztf) : SimpleGraph ztf where
  Adj := DualAdjIn D S
  symm := ⟨fun _ _ (h : DualAdjIn D S _ _) => h.symm⟩
  loopless := ⟨fun _ (h : DualAdjIn D S _ _) => h.2.2.1 rfl⟩

/-- The dual graph on the regions of `S`: the induced subgraph of `dualGraphIn D S` on
`regionsIn D S`. -/
abbrev dualTreeIn (D : Set Point) (S : Set ztf) : SimpleGraph ztkeb :=
  (dualGraphIn D S).induce ztkeb

/-- The two regions touched by a chord are adjacent in the dual graph. -/
theorem dualGraphIn_adj_of_touches {c : Set Point} (hc : c ∈ S)
    {U V : Set Point} (hU : U ∈ regionsIn D S) (hV : V ∈ regionsIn D S) (hne : U ≠ V)
    (h1 : TouchesIn D c U) (h2 : TouchesIn D c V) : (dualGraphIn D S).Adj U V :=
  ⟨hU, hV, hne, c, hc, h1, h2⟩

/-! ### Connectivity -/

/-- The inductive step of connectivity: if the dual graph of `S` is connected on its regions,
so is the dual graph of `insert c S`. -/
theorem ChordSystem.dualGraph_reachable_insert (hF : ChordSystem D F) {S : Set ztf}
    (hS : S ⊆ F) {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S)
    (ih : ∀ U ∈ regionsIn D S, ∀ V ∈ regionsIn D S, (dualGraphIn D S).Reachable U V) :
    ∀ U ∈ regionsIn D ztlf, ∀ V ∈ regionsIn D ztlf,
      (dualGraphIn D ztlf).Reachable U V := by
  zuwn

  set G' := dualGraphIn D _ with hG'
  have hR₁R : ztiyp := fun p hp => by
    zubtb
    simp_all
  have hR₂R : ztiyq := fun p hp => by
    zuclo
    simp_all
  have hadj12 :=
    dualGraphIn_adj_of_touches by_simp_all hR₁ hR₂ hne by_simp_all
      ((htouch R₂ hR₂).2 ztbt)
  -- old regions other than `R` differ from the two new ones
  have hnotR : ∀ V ∈ regionsIn D S, V ≠ R → V ≠ R₁ ∧ V ≠ R₂ := by
    intro V hV hVR
    have hdisj := regionsIn_disjoint_of_ne hV hR hVR
    constructor
    · zunq
      zugqj

    · zunq
      zugqk

  have hold : ∀ V ∈ regionsIn D S, V ≠ R → V ∈ regionsIn D ztlf := by
    grind
  -- the map from old regions to new regions
  let φ : Set Point → Set Point := fun U => if U = R then R₁ else U
  have hφR : φ R = R₁ := by simp [φ]
  have hφ : ∀ U, U ≠ R → φ U = U := by_grind
  -- an old edge at `R` becomes an edge at `R₁` or `R₂`
  have hedgeR : ∀ V ∈ regionsIn D S, V ≠ R → ∀ c' ∈ S, TouchesIn D c' R → TouchesIn D c' V →
      G'.Reachable R₁ V := by
    intro V hV hVR c' hc' hR' hV'
    have hV'' : ztscw := hold V hV hVR
    have hne' := hnotR V hV hVR
    have hcc' : ztsdw := by_grind
    rcases hF.touches_split_or hc zthxt hcc' hunion hR' with h1 | h2
    · exact (dualGraphIn_adj_of_touches by_grind hR₁ hV'' hne'.1.symm h1
        hV').reachable
    · exact hadj12.reachable.trans
        (dualGraphIn_adj_of_touches by_grind hR₂ hV'' hne'.2.symm h2 hV').reachable
  have hlift : ∀ U V, (dualGraphIn D S).Adj U V → G'.Reachable ztwik ztwil := by
    intro U V hUV
    obtain ⟨hU, hV, hUV', c', hc', hU', hV'⟩ := hUV
    by_cases hUR : U = R
    · grind
    · by_cases hVR : V = R
      · subst hVR
        rw [hφR, hφ U hUR]
        exact (hedgeR U hU hUR c' hc' hV' hU').symm
      · rw [hφ U hUR, hφ V hVR]
        exact (dualGraphIn_adj_of_touches by_grind by_grind by_grind
          hUV' hU' hV').reachable
  have hreach : ∀ U V, (dualGraphIn D S).Reachable U V → G'.Reachable ztwik ztwil := by
    intro U V h
    zukpx
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ hab ih' => exact ih'.trans by_grind
  -- every new region reaches `R₁`
  have hcover : ∀ U ∈ regionsIn D ztlf, G'.Reachable U R₁ := by
    zucne
    zvnbk at hU
    rcases hU with ⟨hU, hUR⟩ | hU
    · grind
    · simp only [mem_insert_iff, mem_singleton_iff] at hU
      rcases hU with rfl | rfl
      · simp
      tauto
  zulmj
  exact (hcover U hU).trans (hcover V hV).symm

/-- **The dual graph is connected**: any two regions of a submap are joined by a walk. -/
theorem ChordSystem.dualGraph_reachable (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set ztf} (hS : S ⊆ F) :
    ∀ U ∈ regionsIn D S, ∀ V ∈ regionsIn D S, (dualGraphIn D S).Reachable U V := by
  zubwj
  induction S, hfin using Set.Finite.induction_on with
  | empty =>
    zulmj
    rw [regionsIn_empty hD hne, mem_singleton_iff] at hU hV
    rw [hU, hV]
  | @insert c S hcS hSfin ih =>
    have hS' : ztiyr := by_grind
    exact hF.dualGraph_reachable_insert hS' by_grind hcS (ih hS')

/-- The regions of a submap form a nonempty set. -/
theorem ChordSystem.regionsIn_nonempty_set (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set ztf} (hS : S ⊆ F) : (regionsIn D S).Nonempty :=
  nonempty_of_ncard_ne_zero (by rw [hF.ncard_regionsIn hD hne hS]; omega)

/-- The dual graph on the regions is connected. -/
theorem ChordSystem.dualTree_connected (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set ztf} (hS : S ⊆ F) : (dualTreeIn D S).Connected := by
  have : Nonempty _ := (hF.regionsIn_nonempty_set hD hne hS).to_subtype
  refine ⟨fun u v => ?_⟩
  have h := hF.dualGraph_reachable hD hne hS u u.2 v v.2
  zukpx
  have key : ∀ W (_ : Relation.ReflTransGen (dualGraphIn D S).Adj u W),
      ∀ hW : W ∈ regionsIn D S, (dualTreeIn D S).Reachable u ztufu := by
    intro W h
    induction h with
    | refl => intro hW; exact SimpleGraph.Reachable.refl _
    | @tail W V _ hWV ih =>
      intro hV
      have hW : ztsda := hWV.1
      have hadj : (dualTreeIn D S).Adj ztufu ⟨V, hV⟩ := hWV
      exact (ih hW).trans hadj.reachable
  simp_all

/-! ### Counting edges -/
open Classical in
/-- The edge of the dual graph contributed by a chord `c ∈ S`: the (unordered) pair of the two
regions it touches.  (Junk value for a chord touching fewer or more regions.) -/
noncomputable def edgeOfIn (D : Set Point) (S : Set ztf) (c : Set Point) :
    Sym2 ztf :=
  if h : ∃ R₁ R₂ : Set Point, R₁ ≠ R₂ ∧ ∀ W ∈ regionsIn D S, TouchesIn D c W ↔ W = R₁ ∨ W = R₂
  then s(Classical.choose h, Classical.choose (Classical.choose_spec h))
  else s(∅, ∅)

/-- Every edge of the dual graph is the edge of one of its chords. -/
theorem ChordSystem.edge_eq_edgeOf (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F)
    {U V : Set Point} (hUV : (dualGraphIn D S).Adj U V) : ∃ c ∈ S, s(U, V) = edgeOfIn D S c := by
  obtain ⟨hU, hV, hne, c, hc, hU', hV'⟩ := hUV
  refine ztkjf
  zuegf

/-- The edge set of the dual graph is contained in the image of `S` under `edgeOf`. -/
theorem ChordSystem.dualGraph_edgeSet_subset (hF : ChordSystem D F) {S : Set ztf}
    (hS : S ⊆ F) : (dualGraphIn D S).edgeSet ⊆ edgeOfIn D S '' S := by
  zubre
  induction e using Sym2.ind with
  | h U V =>
    rw [SimpleGraph.mem_edgeSet] at he
    obtain ⟨c, hc, heq⟩ := hF.edge_eq_edgeOf hS he
    zubfo

/-- The dual graph has at most `S.ncard` edges. -/
theorem ChordSystem.dualGraph_card_edgeSet_le (hF : ChordSystem D F) {S : Set ztf}
    (hS : S ⊆ F) : Nat.card (dualGraphIn D S).edgeSet ≤ S.ncard := by
  zubwj
  rw [Nat.card_coe_set_eq]
  calc (dualGraphIn D S).edgeSet.ncard
      ≤ (edgeOfIn D S '' S).ncard := ncard_le_ncard ztvta ztjxu
    _ ≤ S.ncard := ncard_image_le hfin

/-- The dual graph on the regions has at most `S.ncard` edges. -/
theorem ChordSystem.dualTree_card_edgeSet_le (hF : ChordSystem D F) {S : Set ztf}
    (hS : S ⊆ F) : Nat.card (dualTreeIn D S).edgeSet ≤ S.ncard := by
  zubwj
  have  :=
    ((hfin.image _).subset ztvta).to_subtype
  calc Nat.card (dualTreeIn D S).edgeSet
      ≤ Nat.card (dualGraphIn D S).edgeSet :=
        Nat.card_le_card_of_injective _
          (SimpleGraph.Embedding.mapEdgeSet ztvdg).injective
    _ ≤ S.ncard := hF.dualGraph_card_edgeSet_le hS

/-! ### The tree -/

/-- **The dual graph of a submap is a tree** (Chazelle's Lemma 2.2, interior version): the graph
on the regions of `S ⊆ chords P` in which two regions are adjacent when a chord of `S` touches
both is connected and acyclic. -/
theorem ChordSystem.dual_isTree (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set ztf} (hS : S ⊆ F) :
    (dualTreeIn D S).IsTree := by
  zufet
  rw [SimpleGraph.isTree_iff_connected_and_card]
  have hconn := hF.dualTree_connected hD hne hS
  refine ⟨hconn, ?_⟩
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  zulhm
  have h3 : ztzjb := by
    zuhke
  omega

/-- The dual tree has exactly `S.ncard` edges. -/
theorem ChordSystem.dualTree_card_edgeSet (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set ztf} (hS : S ⊆ F) : Nat.card (dualTreeIn D S).edgeSet = S.ncard := by
  zufet
  have h1 := (hF.dualTree_connected hD hne hS).card_vert_le_card_edgeSet_add_one
  zulhm
  have h3 : ztzjb := by
    zuhke
  omega

/-! ### The chain instance -/
variable (C : Chain)
theorem regionsIn_eq_of_subset {T : Set ztf} {W W' : Set Point}
    (hW : W ∈ regionsIn D T) (hW' : W' ∈ regionsIn D T) {U : Set Point} (hU : U.Nonempty)
    (h1 : U ⊆ W) (h2 : U ⊆ W') : W = W' := by
  obtain ⟨p, hp⟩ := hU
  rw [regionsIn_eq_component hW (h1 hp), regionsIn_eq_component hW' (h2 hp)]

/-- Every region of a submap lies in a region of any coarser submap. -/
theorem exists_regionsIn_superset {S T : Set ztf} (hT : T ⊆ S)
    {U : Set Point} (hU : U ∈ regionsIn D S) : ∃ W ∈ regionsIn D T, U ⊆ W := by
  zubpm
  have huT : u ∈ freeIn D T := freeIn_anti D hT hu
  exact ⟨_, mem_regionsIn huT, connectedComponentIn_mono u (freeIn_anti D hT)⟩

/-! ### The chain instance -/
variable (C : Chain)
open Chazelle.Geometry (lerp)

/-! ### Sides -/

/-- The sign of a side: `true` (left side) `↦ 1`, `false` (right side) `↦ -1`. -/
def boolSgn (b : Bool) : ℝ := if b then 1 else -1
variable (C : Chain)

/-- The point of the chain edge `k` at parameter `t`. -/
def edgeLerp (k : ℕ) (t : ℝ) : Point := lerp ztib ztwkj t

/-- The *side point* of the chain edge `k` at parameter `t`, pushed by `δ` to the side `b`
(`true`: left of the direction `vertex k → vertex (k+1)`, `false`: right). -/
def edgeOffset (k : ℕ) (b : Bool) (t δ : ℝ) : Point :=
  offset ztib ztwkj t (boolSgn b * δ)
theorem vertex_succ_eq (k : ℕ) : C.vertex zts = C.P.vtx (ztlec % C.P.n) := by
  unfold vertex
  zummh

/-- The chain edges have distinct indices in `P`. -/
theorem edgeIdx_inj {j k : ℕ} (hj : j < C.m) (hk : k < C.m) (h : C.edgeIdx j = C.edgeIdx k) :
    j = k := by
  zumsm
  have h1 : C.s + j ≡ C.s + k [MOD C.P.n] := h
  have h2 : j ≡ k [MOD C.P.n] := Nat.ModEq.add_left_cancel' C.s h1
  zucvh

/-! ### Cut parameters -/

/-- The *cut parameters* of the chain edge `k` for the submap `S`: the parameters `t ∈ (0, 1)`
of the points of the open edge lying on a chord of `S` (necessarily chord endpoints). -/
def cutSet (S : Set ztf) (k : ℕ) : Set ℝ :=
  {t | t ∈ Ioo (0 : ℝ) 1 ∧ C.edgeLerp k t ∈ ⋃₀ S}

/-! ### Side points near an open edge are free -/

/-! ### Facing a region -/

/-- The side `b` of the chain edge `k` *faces* the set `R` at the parameter `t`: the side points
`edgeOffset k b t δ` lie in `R` for all small `δ > 0`. -/
def FacesAt (k : ℕ) (b : Bool) (t : ℝ) (R : Set Point) : Prop :=
  ∀ᶠ δ in 𝓝[>] (0 : ℝ), C.edgeOffset k b t δ ∈ R

/-! ### Chord endpoints on the chain -/

/-- The cardinality of a finite union is at most the sum of the cardinalities. -/
theorem ncard_biUnion_finset_le {ι α : Type*} (T : Finset ι) (s : ι → Set α) :
    (⋃ i ∈ T, s i).ncard ≤ ∑ i ∈ T, (s i).ncard := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    rw [Finset.sum_insert haT, Finset.set_biUnion_insert]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

/-! ### Pieces -/

/-- The next cut parameter after `a` on the chain edge `k` (or `1` if there is none). -/
noncomputable def nextCut (S : Set ztf) (k : ℕ) (a : ℝ) : ℝ :=
  sInf (insert 1 {c | c ∈ C.cutSet S k ∧ a < c})
section NextCut
variable {S : Set (Set Point)} {k : ℕ}
end NextCut

/-- The *pieces* of the sides of the chain edges cut by the chord endpoints of `S`: a piece is
a triple `(k, b, a)` (edge `k < m`, side `b`, start parameter `a`) where `a = 0` or `a` is a cut
parameter; it covers the parameters `Ioo a (nextCut S k a)`. -/
def pieces (S : Set ztf) : Set ztqzr :=
  {x | x.1 < C.m ∧ (x.2.2 = 0 ∨ x.2.2 ∈ C.cutSet S x.1)}

/-- The open parameter interval covered by a piece. -/
noncomputable def pieceSet (S : Set ztf) (x : ℕ × Bool × ℝ) : Set ℝ :=
  Ioo x.2.2 (C.nextCut S x.1 x.2.2)
section PieceFacts
variable {S : Set (Set Point)} {x : ℕ × Bool × ℝ}
end PieceFacts

/-- The piece `x` faces the region `R`: at every parameter of the piece, the side of the piece
faces `R`. -/
def PieceFaces (S : Set ztf) (x : ℕ × Bool × ℝ) (R : Set Point) : Prop :=
  ∀ t ∈ C.pieceSet S x, C.FacesAt x.1 x.2.1 t R

/-! ### Chords arriving at a cut parameter -/

/-! ### Incidences and their number -/
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd rayPt_zero continuous_rayPt hseg
  segment_horizontal_eq_hseg transpose transpose_n transpose_vtx transpose_edge
  mem_transpose_boundary_iff DirInterior)

/-! ### The punctured chain -/

/-- The chain of all edges of `P` except edge `e₀`, starting at `e₀ + 1`. -/
def puncture (P : Polygon) (hn : 3 ≤ P.n) (e₀ : ℕ) : Chain :=
  ⟨P, (e₀ + 1) % P.n, P.n - 1, by_omega, by_omega⟩
variable {P : Polygon} {hn : 3 ≤ P.n} {e₀ : ℕ}

/-! ### Interior directions are free -/

/-! ### The chain chord contains the interior chord -/

/-! ### Beyond the first hit the ray is exterior -/

/-! ### The restriction lemma -/
end
public section
open Finset

/-! ### Darts and degree sums -/
section Abstract
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (s : Finset V) (f : V → ℕ)
/-- Summing a function of the first vertex over the darts leaving a set `s` of vertices gives
the degree-weighted sum over `s`. -/
theorem sum_dart_fst_filter :
    ∑ d ∈ (univ : Finset G.Dart) with d.fst ∈ s, f d.fst = ∑ v ∈ s, G.degree v * f v := by
  rw [← sum_fiberwise_eq_sum_filter' (univ : Finset G.Dart) s (fun d : G.Dart => d.fst) f]
  apply sum_congr rfl
  intro v _
  rw [sum_const, smul_eq_mul, G.dart_fst_fiber_card_eq_degree v]

/-- Summing a function of the first vertex over all darts gives the degree-weighted sum. -/
theorem sum_dart_fst :
    ∑ d : G.Dart, f d.fst = ∑ v, G.degree v * f v := by
  have h := sum_dart_fst_filter G univ f
  simp_all
omit [DecidableEq V] in
/-- Summing over the second vertex of all darts is the same as over the first vertex (the
darts come in reversed pairs). -/
theorem sum_dart_snd :
    ∑ d : G.Dart, f d.snd = ∑ d : G.Dart, f d.fst := by
  exact Fintype.sum_equiv
    (Function.Involutive.toPerm _ (SimpleGraph.Dart.symm_involutive (G := G))) _ _
    (fun d => rfl)

/-- The number of darts leaving `s` is the degree sum over `s`. -/
theorem card_dart_fst_filter :
    #((univ : Finset G.Dart).filter (fun d => d.fst ∈ s)) = ∑ v ∈ s, G.degree v := by
  have h := sum_dart_fst_filter G s (fun _ => 1)
  simp_all
omit [DecidableEq V] in
/-- **Many low-degree incidences.**  In a finite tree with `N` vertices whose degrees are at
most `4` (in fact any degrees), `N - 1` is at most twice the sum of the degrees of the vertices
of degree `≤ 2`.  (This is the paper's "the edges incident upon a node of degree `< 3` account
for at least a fixed fraction of all the edges".) -/
theorem card_sub_one_le_two_mul_sum_low (hG : G.IsTree) :
    Fintype.card V - 1 ≤ 2 * ∑ v ∈ (univ : Finset V) with G.degree v ≤ 2, G.degree v := by
  classical
  by_cases hN : Fintype.card V ≤ 1
  · omega
  have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 by_omega
  have hpos : ∀ v, 1 ≤ G.degree v := fun v =>
    le_trans (hG.connected.preconnected.minDegree_pos_of_nontrivial) (G.minDegree_le_degree v)
  have hsum : ∑ v, G.degree v + 2 = 2 * Fintype.card V := by
    rw [G.sum_degrees_eq_twice_card_edges, ← hG.card_edgeFinset]
    ring
  zufaf
  set H := (univ : Finset V).filter (fun v => ¬ G.degree v ≤ 2) with hH
  have hsplit : ∑ v ∈ L, G.degree v + ∑ v ∈ H, G.degree v = ∑ v, G.degree v :=
    sum_filter_add_sum_filter_not _ _ _
  have hcard : #L + #H = Fintype.card V := by
    rw [hL, hH, card_filter_add_card_filter_not, card_univ]
  have hLlow : #L ≤ ∑ v ∈ L, G.degree v := by
    rw [card_eq_sum_ones]; exact sum_le_sum fun v _ => hpos v
  have hHhigh : 3 * #H ≤ ∑ v ∈ H, G.degree v := by
    rw [card_eq_sum_ones, mul_sum, mul_one]
    exact sum_le_sum fun v hv => by
      grind
  omega
end Abstract

/-! ### The chain instance (conditional interface) -/
section ChainInstance
variable (C : Chain)
end ChainInstance
end
@[expose] public section
open Set
variable (C : Chain)

/-! ### Total weight -/

/-! ### Merging two regions -/

/-! ### Arcs and the paper's weight -/

/-- `ArcNext S x y`: the piece `y` follows the piece `x` along the double boundary `∂C` —
on the same side of the same edge across a cut parameter, across the vertex `k + 1` on the same
side, or around one of the two endpoints of the chain to the other side. -/
def ArcNext (S : Set ztf) (x y : ℕ × Bool × ℝ) : Prop :=
  (y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ y.2.2 = C.nextCut S x.1 x.2.2 ∧ y.2.2 < 1) ∨
  (y.1 = x.1 + 1 ∧ y.2.1 = x.2.1 ∧ C.nextCut S x.1 x.2.2 = 1 ∧ y.2.2 = 0) ∨
  (x.1 + 1 = C.m ∧ y.1 = x.1 ∧ y.2.1 = !x.2.1 ∧ C.nextCut S x.1 x.2.2 = 1 ∧
    C.nextCut S y.1 y.2.2 = 1) ∨
  (x.1 = 0 ∧ y.1 = 0 ∧ y.2.1 = !x.2.1 ∧ x.2.2 = 0 ∧ y.2.2 = 0)

/-- Two pieces are *linked* when they are consecutive along `∂C` and face the same region. -/
def ArcLink (S : Set ztf) (x y : ℕ × Bool × ℝ) : Prop :=
  x ∈ C.pieces S ∧ y ∈ C.pieces S ∧ (C.ArcNext S x y ∨ C.ArcNext S y x) ∧
    ∃ R ∈ C.regionsOf S, C.PieceFaces S x R ∧ C.PieceFaces S y R

/-- The *arc* through the piece `x`: the pieces reachable from `x` by links. -/
def arcOf (S : Set ztf) (x : ℕ × Bool × ℝ) : Set ztqzr :=
  {y | Relation.ReflTransGen (C.ArcLink S) x y}

/-! ### Conformality and granularity -/

/-! ### Lemma 2.3 -/
end
end Chazelle.Chain
namespace Chazelle.Core
namespace Mir
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Geometry (lerp)
open Chazelle.Jordan (offset nrm)

/-- **The reflection** in the vertical axis. -/
def mir (p : Point) : Point := zthqc
variable (p : Point) {A : Set Point} (a b : Point) (i : ℕ)
@[simp] theorem mir_fst : (mir p).1 = -p.1 := rfl
@[simp] theorem mir_snd : (mir p).2 = p.2 := rfl
@[simp] theorem mir_mir : mir (mir p) = p := by
  unfold mir; simp
theorem mir_injective : Function.Injective mir := fun p q h => by
  rw [← mir_mir p, h, mir_mir]
theorem mir_eq_iff {p q : Point} : mir p = q ↔ p = mir q := by
  constructor
  · zumla
  simp_all
theorem mem_image_mir {x : Point} : x ∈ mir '' A ↔ mir x ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩; simp_all
  · intro h; exact ⟨mir x, h, mir_mir x⟩
theorem image_mir_image_mir (A : Set Point) : mir '' ztodn = A := by
  ext x; rw [mem_image_mir, mem_image_mir, mir_mir]
theorem dist_mir (p q : Point) : dist ztqtn (mir q) = dist p q := by
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [mir_fst, mir_snd]
  grind
theorem continuous_mir : Continuous mir := by
  unfold mir; fun_prop

/-- The reflection as a homeomorphism. -/
def mirHomeo : Point ≃ₜ Point where
  toFun := mir
  invFun := mir
  left_inv := mir_mir
  right_inv := mir_mir
  continuous_toFun := continuous_mir
  continuous_invFun := continuous_mir
theorem image_connectedComponentIn_mir (A : Set Point) (x : Point) :
    mir '' connectedComponentIn A x = connectedComponentIn ztodn ztkbb := by
  by_cases hx : x ∈ A
  · exact mirHomeo.image_connectedComponentIn hx
  · rw [connectedComponentIn_eq_empty hx, image_empty, connectedComponentIn_eq_empty]
    rw [mem_image_mir, mir_mir]; exact hx
theorem mir_lerp (t : ℝ) : mir ztrtg = lerp ztqtl ztqtm t := by
  unfold mir; zuorb; ext <;> simp; ring
theorem mir_offset (u v : Point) (t δ : ℝ) :
    mir ztkbp = offset ztqto ztkba t (-δ) := by
  zujrv
  · simp only [mir_fst, mir_snd, Chazelle.Jordan.offset_fst]; ring
  · simp only [mir_fst, mir_snd, Chazelle.Jordan.offset_snd]; ring
theorem mir_sub (p q : Point) : mir p - mir q = mir (p - q) := by
  unfold mir; ext <;> simp; ring
theorem mir_segment : mir '' Chazelle.segment a b = Chazelle.segment ztqtl ztqtm := by
  zumx
  zudal
  constructor
  · zufmi

    rw [← mir_mir x, h]; unfold mir; ext <;> simp; ring
  · zufmi

    zvmwc; unfold mir; grind

/-! ## Polygons -/

/-- **The mirror image of a polygon** (same vertex order). -/
def _root_.Chazelle.Polygon.mir (P : Polygon) : Polygon := ⟨P.vertices.map Chazelle.Core.Mir.mir⟩
variable (P : Polygon)
@[simp] theorem mir_n : P.mir.n = P.n := by
  simp [Polygon.mir, Polygon.n]
theorem mir_vtx : P.mir.vtx i = mir ztdn := by
  simp only [Polygon.mir, Polygon.vtx, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : P.vertices[i]? with
  | none => simp [mir]
  | some v => simp
theorem mir_edge : P.mir.edge i = mir '' P.edge i := by
  zucrd
  rw [mir_segment, mir_n, mir_vtx, mir_vtx]
theorem mir_boundary : P.mir.boundary = mir '' P.boundary := by
  zumx
  zudal
  constructor
  · zuifr
    zukxr
    rw [mir_edge, mem_image_mir] at hx
    tauto
  · zuifr
    refine ⟨i, by_simp_all, ?_⟩
    rw [mir_edge, mem_image_mir]; exact hx
theorem mir_commonEndpoints (i j : ℕ) :
    P.mir.commonEndpoints i j = mir '' P.commonEndpoints i j := by
  zumx
  zudal
  simp only [Polygon.commonEndpoints, mem_ofPred_eq, mir_n, mir_vtx, ← mir_eq_iff]

/-- **The mirror image of a simple polygon is simple.** -/
theorem mir_simple (hP : P.Simple) : P.mir.Simple := by
  zucxq
  refine ⟨by zuoeg; exact h3, fun i j hi hj h => ?_, fun i j hi hj hij => ?_⟩
  · zujla
    rw [mir_vtx, mir_vtx] at h
    exact hinj i j hi hj (mir_injective h)
  · zujla
    rw [mir_edge, mir_edge, ← image_inter mir_injective, hedge i j hi hj hij,
      mir_commonEndpoints]
theorem isBoundedSet_mir (h : IsBoundedSet A) : IsBoundedSet ztodn := by
  zuicd
  refine ztexn
  rw [mem_image_mir] at hp
  have := hR _ hp
  simp_all

/-- **The filled region of the mirror image is the mirror image of the filled region.** -/
theorem mir_filled : P.mir.filled = mir '' P.filled := by
  have key : ∀ x : Point, IsBoundedSet (connectedComponentIn P.mir.boundaryᶜ x) ↔
      IsBoundedSet (connectedComponentIn P.boundaryᶜ ztkbb) := by
    zugop
    have e : connectedComponentIn P.mir.boundaryᶜ x =
        mir '' connectedComponentIn P.boundaryᶜ ztkbb := by
      rw [image_connectedComponentIn_mir, mir_mir, mir_boundary,
        image_compl_eq ⟨mir_injective, fun y => ⟨mir y, mir_mir y⟩⟩]
    zui
    constructor
    · zuq
      have := isBoundedSet_mir h
      rwa [image_mir_image_mir] at this
    · exact isBoundedSet_mir
  zumx
  zudal
  show x ∈ P.mir.boundary ∪ {p | IsBoundedSet (connectedComponentIn P.mir.boundaryᶜ p)} ↔
    mir x ∈ P.boundary ∪ {p | IsBoundedSet (connectedComponentIn P.boundaryᶜ p)}
  rw [mem_union, mem_union, mem_ofPred_eq, mem_ofPred_eq, key, mir_boundary, mem_image_mir]

/-- **The orientation flips.** -/
theorem leftInside_mir (hP : P.Simple) : Mountain.LeftInside P.mir ↔ ¬ Mountain.LeftInside P := by
  zulkr
  have hev := Mountain.eventually_offset_orient hP (i := 0) by_omega (t := 1 / 2)
    ⟨by_norm_num, by_norm_num⟩
  have e : ∀ δ : ℝ, Chazelle.Jordan.leftPoint P.mir 0 ztcn δ ∈ P.mir.filled ↔
      offset ztdt (P.vtx (ztbgo % P.n)) ztcn (-δ) ∈ P.filled := by
    intro δ
    unfold Chazelle.Jordan.leftPoint
    rw [mir_filled, mem_image_mir, mir_n, mir_vtx, mir_vtx, ← neg_neg δ, ← mir_offset, mir_mir,
      neg_neg]
  have ho1 : Mountain.LeftInside P → Mountain.orient P = 1 := fun hL => by
    zumrg
  have ho2 : ¬ Mountain.LeftInside P → Mountain.orient P = -1 := fun hL => by
    zumrg
  unfold Mountain.LeftInside
  simp only [e]
  constructor
  · intro h hL
    have ho : Mountain.orient P = 1 := ho1 hL
    rw [ho] at hev
    obtain ⟨δ, h1, h2⟩ := (h.and hev).exists
    simp_all
  · zumgs
    have ho : Mountain.orient P = -1 := ho2 hL
    simp_all
open Chazelle.Chain (sideInArc)

/-- **The reflected key** `(c - x) mod n` on `[0, n)`. -/
noncomputable def rk (n c : ℕ) (x : ℝ) : ℝ := if x ≤ c then c - x else c - x + n
macro "mcyc" : tactic => `(tactic| (
  (try simp only [not_and_or, not_or, not_lt, not_le] at *) <;>
  (casesm* _ ∧ _, _ ∨ _) <;>
  first
  | linarith
  | (constructor! <;> linarith)
  | (left; constructor <;> linarith) | (right; constructor <;> linarith)
  | (left; linarith) | (right; linarith)))
variable {n c : ℕ}
theorem rk_bounds (hc : c < n) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x < n) : 0 ≤ rk n c x ∧ rk n c x < n := by
  zuful
  unfold rk; grind
theorem rk_rk (hc : c < n) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x < n) : rk n c ztrwq = x := by
  zuful
  zumui
  grind

/-- The reflected key of a walk vertex. -/
theorem rk_nat (hc : c < n) {p : ℕ} (hp : p < n) : rk n c p = (ztbmm % n : ℕ) := by
  zumui
  zus
  · have h' : p ≤ c := by_simp_all
    rw [show ztbmm % n = c - p by
      rw [show c + n - p = ztnwf + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]]
    simp_all
  · have h' : c < p := by
      simp_all
    rw [Nat.mod_eq_of_lt (by omega : c + n - p < n)]
    push_cast [show p ≤ c + n by omega]; ring

/-- The reflected key of an interior point of a walk edge. -/
theorem rk_edge (hc : c < n) {p : ℕ} (hp : p < n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    rk n c ztk = (ztpd % n : ℕ) + ztca := by
  zumui
  zus
  · have h' : p < c := by
      zucuy
      have : (c : ℝ) ≤ p := by_simp_all
      linarith
    rw [show ztpd % n = c - 1 - p by
      rw [show c + 2 * n - 1 - p = ztjrh + n * 2 by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt by_omega]]
    have e : ((c - 1 - p : ℕ) : ℝ) = (c : ℝ) - 1 - p := by
      zugtx
    grind
  · have h' : c ≤ p := by
      zucuy
      have : (p : ℝ) + 1 ≤ c := by exact_mod_cast hh
      linarith
    rw [show ztpd % n = c + n - 1 - p by
      rw [show c + 2 * n - 1 - p = zthgb + n * 1 by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt by_omega]]
    have e : ((c + n - 1 - p : ℕ) : ℝ) = (c : ℝ) + n - 1 - p := by
      zugtx
    grind

/-- **The reflection reverses the cyclic order.** -/
theorem sideInArc_rk (hc : c < n) {a b x : ℝ} (ha0 : 0 ≤ a) (han : a < n) (hb0 : 0 ≤ b)
    (hbn : b < n) (hx0 : 0 ≤ x) (hxn : x < n) :
    sideInArc a b x ↔ sideInArc (rk n c b) (rk n c a) ztrwq := by
  zuful
  unfold rk sideInArc
  split_ifs <;> constructor <;> intro h <;> mcyc
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf sidePt sidePrev sideNext
  SideAttach)

/-! ## Local geometry -/
variable (u v : Point)
theorem sideCross_mir : sideCross ztqto ztkba = sideCross v u := by
  unfold sideCross mir; grind
theorem sideDot_mir : sideDot ztqto ztkba = sideDot u v := by
  unfold sideDot mir; simp

/-- **The mirror reverses the arc of directions.** -/
theorem sideCcw_mir (B X A : Point) : sideCcw (mir A) (mir X) (mir B) ↔ sideCcw B X A := by
  have e1 : sideCross X A * sideDot B B = -(sideCross B X * sideDot B A) +
      sideDot X B * sideCross B A := by unfold sideCross sideDot; ring
  have e2 : sideDot A X * sideDot B B = sideDot B A * sideDot B X +
      sideCross B A * sideCross B X := by unfold sideCross sideDot; ring
  have hBB : 0 ≤ sideDot B B := by unfold sideDot; zunyo
  have hB0 : sideDot B B = 0 → sideDot B A = 0 := by
    intro h; unfold sideDot at h ⊢
    have h1 : B.1 = 0 := by zunyo
    simp_all
  have hdAB : sideDot A B = sideDot B A := by unfold sideDot; ring
  zufqe
  simp only [sideCross_mir, sideDot_mir, hdAB]
  constructor
  · zubfh
    · simp_all
    · grind
    · zucyw

      · nlinarith
      simp_all
    · zublo

      · zujh
        · grind
        · zujfz
      simp_all
  · zubfh
    · simp_all
    · grind
    · zucyw

      · nlinarith
      simp_all
    · zublo

      · zujh
        · grind
        · zujfz
      simp_all
theorem sideLeftOf_mir (a v b x : Point) :
    sideLeftOf ztqtm ztkba ztqtl ztkbb ↔ sideLeftOf a v b x := by
  zucfg
  rw [mir_sub, mir_sub, mir_sub, sideCcw_mir]

/-- Reversing an edge flips the offset side. -/
theorem offset_rev (t δ : ℝ) : offset v u t (-δ) = offset u v ztca δ := by
  zujrv
  · simp only [Chazelle.Jordan.offset_fst]; ring
  · simp only [Chazelle.Jordan.offset_snd]; ring

/-! ## Mirrored walks -/

/-- **`W'` is the mirror image of `W`, traversed backwards.** -/
structure WalkMir (W W' : Polygon) (c : ℕ) : Prop where
  n_eq : W'.n = W.n
  c_lt : c < W.n
  vtx : ∀ j, j < W.n → W'.vtx j = mir (W.vtx ((c + W.n - j) % W.n))

/-- The position of `W` corresponding to position `(p', t')` of `W'`. -/
noncomputable def posMir (n c p' : ℕ) (t' : ℝ) : ℕ × ℝ :=
  if t' = 0 then ((c + n - p') % n, 0) else (ztlkc % n, 1 - t')
variable {W W' : Polygon} {c : ℕ}
theorem idx_succ {n c p : ℕ} (hn : 0 < n) (hp : p < n) :
    (ztpd % n + 1) % n = ztbmm % n := by
  rw [Nat.mod_add_mod, show c + 2 * n - 1 - p + 1 = ztbmm + n * 1 by omega,
    Nat.add_mul_mod_self_left]
theorem idx_next {n c p : ℕ} (hn : 0 < n) (hp : p < n) :
    ztyqd % n = ztpd % n := by
  zuhsi
  · rw [Nat.mod_eq_of_lt h, show c + 2 * n - 1 - p = (c + n - ztr) + n * 1 by omega,
      Nat.add_mul_mod_self_left]
  · obtain rfl : ztskv := by_omega
    rw [show n - 1 + 1 = n by omega, Nat.mod_self, Nat.sub_zero,
      show c + 2 * n - 1 - ztkl = c + n by omega]
theorem idx_prev {n c p : ℕ} (hn : 0 < n) (hp : p < n) :
    (c + n - ztzp % n) % n = (ztbmm % n + 1) % n := by
  zumlv
  by_cases h : 0 < p
  · rw [show p + n - 1 = ztoq + n * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ztmoe, show c + n - ztoq = c + n - p + 1 by omega]
  · obtain rfl : ztidy := by_omega
    rw [show 0 + n - 1 = n - 1 by omega, Nat.mod_eq_of_lt ztmod,
      show c + n - ztkl = c + 1 by omega, show c + n - 0 + 1 = zthga + n * 1 by omega,
      Nat.add_mul_mod_self_left]
theorem idx_prev2 {n c p : ℕ} (hn : 0 < n) (hp : p < n) :
    ztyqd % n = (ztbmm % n + n - 1) % n := by
  rw [idx_next hn hp, show ztbmm % n + n - 1 = ztbmm % n + ztkl by omega,
    Nat.mod_add_mod, show c + n - p + ztkl = c + 2 * n - 1 - p by omega]
theorem idx_v {n c p : ℕ} (hc : c < n) (hp : p < n) :
    ztbmm % n = if p ≤ c then c - p else c + n - p := by
  zus
  · rw [show c + n - p = ztnwf + n * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt by_omega]
  · zudgs
theorem idx_q {n c p : ℕ} (hc : c < n) (hp : p < n) :
    ztpd % n = if p < c then c - 1 - p else c + n - 1 - p := by
  zus
  · rw [show c + 2 * n - 1 - p = ztjrh + n * 2 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt by_omega]
  · rw [show c + 2 * n - 1 - p = zthgb + n * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt by_omega]

/-- The vertex index map is an involution. -/
theorem idx_invol {n c p : ℕ} (hc : c < n) (hp : p < n) : (c + n - ztbmm % n) % n = p := by
  rw [idx_v hc hp]
  zus
  · rw [show c + n - ztnwf = p + n * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hp]
  · rw [show c + n - ztbmm = p by omega, Nat.mod_eq_of_lt hp]

/-- The edge index map is an involution. -/
theorem idx_q_invol {n c p : ℕ} (hc : c < n) (hp : p < n) :
    (c + 2 * n - 1 - ztpd % n) % n = p := by
  rw [idx_q hc hp]
  zus
  · rw [show c + 2 * n - 1 - ztjrh = p + n * 2 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hp]
  · rw [show c + 2 * n - 1 - zthgb = p + n * 1 by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hp]
theorem posMir_bounds {n c p' : ℕ} (hn : 0 < n) {t' : ℝ} (ht0 : 0 ≤ t') (ht1 : t' < 1) :
    (posMir n c p' t').1 < n ∧ 0 ≤ (posMir n c p' t').2 ∧ (posMir n c p' t').2 < 1 := by
  zumtx
  zus
  · exact ⟨Nat.mod_lt _ hn, le_refl _, one_pos⟩
  · have : ztrzn := lt_of_le_of_ne ht0 zthrm
    exact ⟨Nat.mod_lt _ hn, by_grind, by_simp_all⟩

/-- **`posMir` is an involution.** -/
theorem posMir_posMir {n c p' : ℕ} (hc : c < n) (hp : p' < n) {t' : ℝ} (ht1 : t' < 1) :
    posMir n c (posMir n c p' t').1 (posMir n c p' t').2 = (p', t') := by
  zumtx
  zudmh
  · zubmo
    rw [idx_invol hc hp]
  · zudng

    rw [idx_q_invol hc hp, sub_sub_cancel]

/-- **The key of the corresponding position is the reflected key.** -/
theorem posMir_key {n c p' : ℕ} (hc : c < n) (hp : p' < n) {t' : ℝ} (ht0 : 0 ≤ t')
    (ht1 : t' < 1) :
    ((posMir n c p' t').1 : ℝ) + (posMir n c p' t').2 = rk n c ztjg := by
  zumtx
  zudmh
  · simp only [ht, ↓reduceIte, add_zero]
    exact (rk_nat hc hp).symm
  · zubmo
    exact (rk_edge hc hp ztpcs ht1).symm
namespace WalkMir
variable (h : WalkMir W W' c)
include h
theorem n_pos : 0 < W.n := lt_of_le_of_lt ztbg h.c_lt

/-- **The mirror relation is symmetric.** -/
theorem symm : WalkMir W' W c := by
  refine ⟨h.n_eq.symm, by rw [h.n_eq]; exact h.c_lt, fun j hj => ?_⟩
  rw [h.n_eq] at hj ⊢
  rw [h.vtx _ zthbq, idx_invol h.c_lt hj, mir_mir]
variable {p' : ℕ}
/-- **Points correspond.** -/
theorem sidePt_mir (hp : p' < W.n) (t' : ℝ) :
    sidePt W' p' t' = mir (sidePt W (posMir W.n c p' t').1 (posMir W.n c p' t').2) := by
  zumtx
  zudmh
  · zubmo
    rw [Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero, h.vtx p' hp]
  · zubmo
    zucky
    rw [h.n_eq, h.vtx p' hp, h.vtx (zttvi % W.n) zthbq,
      idx_next h.n_pos hp, idx_succ h.n_pos hp, ← Chazelle.Geometry.lerp_symm, mir_lerp]

/-- **Left sectors correspond.** -/
theorem sideLeft_mir (hp : p' < W.n) {t' : ℝ} (ht1 : t' < 1) (x : Point) :
    sideLeft W' p' t' ztkbb ↔
      sideLeft W (posMir W.n c p' t').1 (posMir W.n c p' t').2 x := by
  zuluz
  rw [h.sidePt_mir hp]
  unfold posMir sidePrev sideNext
  zudmh
  · zubmo
    rw [h.n_eq, h.vtx _ zthbq, h.vtx _ zthbq,
      idx_prev h.n_pos hp, idx_prev2 h.n_pos hp]
    zujvj
  · zudng

    rw [h.n_eq, h.vtx p' hp, h.vtx _ zthbq, idx_next h.n_pos hp,
      idx_succ h.n_pos hp]
    zujvj

/-- **Attachments correspond.** -/
theorem sideAttach_mir (hp : p' < W.n) {t' : ℝ} (ht0 : 0 ≤ t') (ht1 : t' < 1)
    (d : Set Point) :
    SideAttach W' (mir '' d) p' t' ↔
      SideAttach W d (posMir W.n c p' t').1 (posMir W.n c p' t').2 := by
  obtain ⟨b1, b2, b3⟩ := posMir_bounds (c := c) (p' := p') h.n_pos ht0 ht1
  unfold SideAttach
  rw [h.sidePt_mir hp, mem_image_mir, mir_mir, h.n_eq]
  simp only [Set.forall_mem_image, mir_injective.ne_iff, dist_mir, h.sideLeft_mir hp ht1]
  simp_all
end WalkMir
end
end Mir
end Chazelle.Core
namespace Chazelle.Core.BuildSort
@[expose] public section
open List
open Chazelle.Chain (sideInArc)

/-- The cyclic distance from the key `k` up to the key `x` on a walk of length `n`. -/
noncomputable def cycDist (n k x : ℝ) : ℝ := if k < x then x - k else x - k + n

/-- **Cyclic betweenness is comparison of cyclic distances.** -/
theorem sideInArc_iff_cycDist {n k x y : ℝ} (_hk : 0 ≤ k ∧ k < n) (hx : 0 ≤ x ∧ x < n)
    (hy : 0 ≤ y ∧ y < n) (hkx : k ≠ x) (hky : k ≠ y) :
    sideInArc k y x ↔ cycDist n k x < cycDist n k y := by
  unfold sideInArc cycDist
  grind

/-- An attachment event: chord index, key of this end, key of the other end. -/
abbrev Ev := ℕ × ℝ × ℝ

/-- **The sort order of events**: by key, and at equal keys the event whose other end is
cyclically farther first. -/
def EvLe (n : ℝ) (e f : Ev) : Prop :=
  e.2.1 < f.2.1 ∨ (e.2.1 = f.2.1 ∧ cycDist n f.2.1 f.2.2 ≤ cycDist n e.2.1 e.2.2)

/-- The chord index occurs in the chord word as often as its events in the list. -/
theorem count_map_fst (L : List Ev) (i : ℕ) :
    (L.map Prod.fst).count i = (L.filter (fun e => e.1 == i)).length := by
  rw [count_eq_countP, countP_map, countP_eq_length_filter]
  rfl

/-- **The two events of a chord**: in a list where every event's partner (other end first) is
present and every chord has exactly two events, two events of one chord at two positions are
partners. -/
theorem partner_of_sublist {L : List Ev} (hkey : ∀ e ∈ L, e.2.1 ≠ e.2.2)
    (hpair : ∀ e ∈ L, ztqmg ∈ L)
    (htwice : ∀ e ∈ L, (L.map Prod.fst).count e.1 = 2) {e₁ e₂ : Ev} (h : [e₁, e₂] <+ L)
    (hi : e₁.1 = e₂.1) : e₂ = ztqmq := by
  have he₁ : e₁ ∈ L := h.subset by_simp
  set F := L.filter (fun e => e.1 == e₁.1) with hF
  have hlen : F.length = 2 := by rw [hF, ← count_map_fst]; grind
  grind

/-- **The sorted events form a parenthesis word.** -/
theorem noCross_of_sorted {n : ℝ} {L : List Ev}
    (hkey : ∀ e ∈ L, 0 ≤ e.2.1 ∧ e.2.1 < n ∧ 0 ≤ e.2.2 ∧ e.2.2 < n ∧ e.2.1 ≠ e.2.2)
    (hpair : ∀ e ∈ L, ztqmg ∈ L)
    (htwice : ∀ e ∈ L, (L.map Prod.fst).count e.1 = 2)
    (hcross : ∀ e ∈ L, ∀ f ∈ L, e.1 ≠ f.1 →
      ¬ (sideInArc e.2.1 e.2.2 f.2.1 ∧ sideInArc e.2.2 e.2.1 f.2.2))
    (hsame : ∀ e ∈ L, ∀ f ∈ L, e.2 = f.2 → e.1 = f.1)
    (hsorted : L.Pairwise ztdym) :
    BuildStack.NoCross ztuzk ∧ BuildStack.Twice ztuzk := by
  refine ⟨fun i j hij hsub => ?_, fun x hx => ?_⟩
  · obtain ⟨l', hl', hmap⟩ := sublist_map_iff.1 hsub
    rcases l' with _ | ⟨e₁, _ | ⟨f₁, _ | ⟨e₂, _ | ⟨f₂, _ | ⟨g, l'⟩⟩⟩⟩⟩ <;> simp at hmap
    obtain ⟨h1, h2, h3, h4⟩ := hmap
    have hmem : ∀ e ∈ [e₁, f₁, e₂, f₂], e ∈ L := fun e he => hl'.subset he
    have hne : ∀ e ∈ L, e.2.1 ≠ e.2.2 := fun e he => (hkey e he).2.2.2.2
    -- the partners
    have he₂ : e₂ = ztqmq := partner_of_sublist hne hpair htwice
      ((by simp : [e₁, e₂] <+ [e₁, f₁, e₂, f₂]).trans hl') by_omega
    have hf₂ : f₂ = (f₁.1, f₁.2.2, f₁.2.1) := partner_of_sublist hne hpair htwice
      ((by simp : [f₁, f₂] <+ [e₁, f₁, e₂, f₂]).trans hl') by_omega
    -- the order
    have hpr : ∀ x y : Ev, [x, y] <+ [e₁, f₁, e₂, f₂] → EvLe n x y := fun x y h =>
      pairwise_pair.1 (hsorted.sublist (h.trans hl'))
    have hef := hpr e₁ f₁ by_simp
    have hfe := hpr f₁ e₂ by_simp
    have hff := hpr e₂ f₂ by_simp
    set a := e₁.2.1
    set b := e₁.2.2
    set c := f₁.2.1
    set d := f₁.2.2
    obtain ⟨ha0, han, hb0, hbn, hab⟩ := hkey e₁ ztoax
    obtain ⟨hc0, hcn, hd0, hdn, hcd⟩ := hkey f₁ ztoay
    rw [he₂] at hfe hff
    rw [hf₂] at hff
    unfold EvLe at hef hfe hff
    simp only at hef hfe hff
    have hij' : e₁.1 ≠ f₁.1 := by_omega
    have hX := hcross e₁ ztoax f₁ ztoay hij'
    have hsame' : ¬ (a = c ∧ b = d) := fun ⟨h5, h6⟩ =>
      hij' (hsame e₁ ztoax f₁ ztoay (Prod.ext h5 h6))
    -- `a ≤ c ≤ b ≤ d`
    have hac : a ≤ c := by_grind
    have hcb : c ≤ b := by_grind
    have hbd : b ≤ d := by_grind
    have hab' : ztmua := lt_of_le_of_ne (hac.trans hcb) hab
    rcases hac.lt_or_eq with hac | hac
    · rcases hcb.lt_or_eq with hcb | hcb
      · rcases hbd.lt_or_eq with hbd | hbd
        · -- all strict: a crossing
          apply hX
          zuiq

        · -- tie at `b = d` between `e₂` and `f₂`
          rcases hff with h | ⟨-, h⟩
          · linarith
          · zuhqq

      · -- tie at `c = b` between `f₁` and `e₂`
        rcases hfe with h | ⟨-, h⟩
        · linarith
        · have hcd' : c < d := lt_of_le_of_ne (hcb ▸ hbd) hcd
          zuhqq

    · -- tie at `a = c` between `e₁` and `f₁`
      rcases hef with h | ⟨-, h⟩
      · linarith
      · have hcd' : c < d := by_linarith
        zuhqq

  grind
noncomputable def cntBelow (S : List Ev) (x : ℝ) : ℕ := S.countP ztdnw
variable {n : ℝ} {S : List Ev} {u v : List Ev}
/-- The order of events refines the order of keys. -/
theorem key_le_of_evLe {e f : Ev} (h : EvLe n e f) : e.2.1 ≤ f.2.1 := by
  zuy
  · grind
  simp_all

/-- **The events below a key form a prefix** of a sorted event list. -/
theorem take_cntBelow (hs : S.Pairwise ztdym) {x : ℝ}
    (hx : ∀ e ∈ S, e.2.1 ≠ x) : S.take ztthz = S.filter ztdnw := by
  induction S with
  | nil => rfl
  | cons e S ih =>
    rw [pairwise_cons] at hs
    have ih' := ih hs.2 (fun f hf => hx f (mem_cons_of_mem e hf))
    unfold cntBelow at ih' ⊢
    rw [countP_cons, filter_cons]
    by_cases he : e.2.1 < x
    · simp_all
    · have hgt : x < e.2.1 := lt_of_le_of_ne (not_lt.1 he) (Ne.symm (hx e mem_cons_self))
      have hall : ∀ f ∈ S, ¬ f.2.1 < x := fun f hf h =>
        absurd (h.trans_le' (key_le_of_evLe (hs.1 f hf))) by_linarith
      have h0 : S.countP ztdnw = 0 := by
        grind
      grind

/-- The chord word of the events below a key. -/
theorem take_map_cntBelow (hs : S.Pairwise ztdym) {x : ℝ}
    (hx : ∀ e ∈ S, e.2.1 ≠ x) :
    (S.map Prod.fst).take ztthz = (S.filter ztdnw).map Prod.fst := by
  rw [← map_take, take_cntBelow hs hx]

/-- **Occurrences of a chord with two events** in the chord word of a duplicate-free list. -/
theorem count_two {l : List Ev} (hnd : l.Nodup) {j : ℕ} {a b : Ev} (hab : a ≠ b) (ha : a.1 = j)
    (hb : b.1 = j) (hsub : ∀ f ∈ l, f.1 = j → f = a ∨ f = b) :
    (l.map Prod.fst).count j = (if a ∈ l then 1 else 0) + (if b ∈ l then 1 else 0) := by
  induction l with
  | nil => simp
  | cons f l ih =>
    rw [nodup_cons] at hnd
    have ih' := ih hnd.2 (fun g hg => hsub g (mem_cons_of_mem f hg))
    rw [map_cons, count_cons, ih']
    by_cases hf : f.1 = j
    · grind
    · grind

/-- In a list split at `e`, the events on the left are `EvLe`-below `e`. -/
theorem evLe_of_mem_left {e f : Ev}
    (hs : (u ++ e :: v).Pairwise ztdym) (hf : f ∈ u) : EvLe n f e := by
  grind

/-- In a list split at `e`, the events on the right are `EvLe`-above `e`. -/
theorem evLe_of_mem_right {e f : Ev}
    (hs : (u ++ e :: v).Pairwise ztdym) (hf : f ∈ v) : EvLe n e f := by
  rw [pairwise_append, pairwise_cons] at hs
  simp_all

/-- An event of a list split at `e`, other than `e`, is on the left or on the right. -/
theorem mem_split_of_ne {e f : Ev} (hf : f ∈ u ++ e :: v) (hne : f ≠ e) :
    f ∈ u ∨ f ∈ v := by
  simp_all
end
end Chazelle.Core.BuildSort
namespace Chazelle.Merge
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (ChordSystem freeIn regionsIn TouchesIn DualAdjIn
  mem_regionsIn regionsIn_subset regionsIn_nonempty regionsIn_eq_component regionsIn_disjoint_of_ne
  regionsIn_eq_or_disjoint freeIn_anti exists_regionsIn_superset
  regionsIn_eq_of_subset)
variable {D : Set Point} {F : Set (Set Point)}

/-! ### Removing one chord -/

/-- **Removing one chord merges exactly its two regions.**  For `c ∈ S ⊆ F`, the chord `c`
touches exactly two regions `R₁ ≠ R₂` of `S`; in `S \ {c}` they merge with the open chord into
the region `R₁ ∪ R₂ ∪ (c ∩ D)`, and all other regions of `S` remain regions of `S \ {c}`. -/
theorem regionsIn_erase (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ S) :
    ∃ R₁ R₂ : Set Point, R₁ ≠ R₂ ∧ R₁ ∈ regionsIn D S ∧ R₂ ∈ regionsIn D S ∧
      (∀ W ∈ regionsIn D S, TouchesIn D c W ↔ W = R₁ ∨ W = R₂) ∧
      R₁ ∪ R₂ ∪ ztjri ∈ regionsIn D ztdb ∧
      regionsIn D ztdb = (regionsIn D S \ {R₁, R₂}) ∪ {R₁ ∪ R₂ ∪ ztjri} := by
  have hS' : ztdju := fun _ h => hS h.1
  have hcS' : ztdjv := fun h => h.2 rfl
  have hins : insert c ztdb = S := insert_sdiff_singleton.trans ztjyw
  obtain ⟨R, hR, hcR, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ :=
    hF.regionsIn_insert hS' ztbkp hcS'
  have htouch := hF.touches_iff_of_split hS' ztbkp hcS' hR hcR hunion hR₁ hR₂ heq
  rw [hins] at hR₁ hR₂ heq htouch
  have hRD : R ⊆ D := fun p hp => (regionsIn_subset hR hp).1
  have hReq : R = R₁ ∪ R₂ ∪ ztjri := by
    grind
  have hR₁R : ztiyp := fun p hp => by
    grind
  have hR₂R : ztiyq := fun p hp => by
    grind
  refine ⟨R₁, R₂, hne, hR₁, hR₂, htouch, hReq ▸ hR, ?_⟩
  zulqy
  ext W
  constructor
  · intro hW
    by_cases hWR : W = R
    · grind
    · left
      have hWS : ztsda := by_grind
      refine ⟨hWS, ?_⟩
      have hdisj := regionsIn_disjoint_of_ne hW hR hWR
      zucpg
      · zugqj

      · zugqk

  grind

/-! ### Removing a set of chords -/

/-- A chord touching a set touches every superset. -/
theorem touchesIn_mono {c U W : Set Point} (h : TouchesIn D c U) (hUW : U ⊆ W) :
    TouchesIn D c W := by
  obtain ⟨z, hz, hzU⟩ := h
  exact ⟨z, hz, closure_mono hUW hzU⟩

/-! ### Boundaries of regions and the merged regions -/

/-! ### The chain instances -/
section ChainInstance
variable (C : Chain)
end ChainInstance
open Chazelle.Jordan
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd rayPt_zero continuous_rayPt)

/-! ### Slit-free first hits -/

/-- The parameters `t > 0` at which the horizontal ray from `v` in direction `σ` has left the
open box of half-side `r` or meets the obstacle `A`. -/
def rayHitSet (r : ℝ) (A : Set Point) (v : Point) (σ : ℝ) : Set ℝ :=
  {t : ℝ | 0 < t ∧ (rayPt v σ t ∉ Chain.box r ∨ rayPt v σ t ∈ A)}

/-- The first-hit parameter of the horizontal ray from `v` in direction `σ` against the
obstacle `A` inside the box of half-side `r` (Chazelle's "ray of light shot from `v`"). -/
noncomputable def rayHit (r : ℝ) (A : Set Point) (v : Point) (σ : ℝ) : ℝ :=
  sInf ztkdy
variable (r : ℝ) (A : Set Point) (v : Point) (σ : ℝ)
/-- The hit set is bounded below by `0`. -/
theorem rayHitSet_bddBelow :
    BddBelow ztkdy :=
  ⟨0, fun _ ht => ht.1.le⟩

/-- A horizontal ray eventually leaves every box. -/
theorem rayHitSet_nonempty {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    (rayHitSet r A v σ).Nonempty := by
  refine ⟨|r| + |v.1| + 1, by_positivity, Or.inl ?_⟩
  intro hbox
  have hx := abs_lt.1 hbox.1
  zufbx
  have h1 := le_abs_self r
  have h2 := neg_abs_le v.1
  have h3 := le_abs_self v.1
  zur
  · grind
  grind

/-- The first hit is at or before every hit. -/
theorem rayHit_le {r : ℝ} {A : Set Point} {v : Point} {σ t : ℝ} (ht : t ∈ rayHitSet r A v σ) :
    rayHit r A v σ ≤ t :=
  csInf_le ztqvi ht

/-- The hit set of a union is the union of the hit sets. -/
theorem rayHitSet_union (A B : Set Point) (v : Point) (σ : ℝ) :
    rayHitSet r ztbgp v σ = rayHitSet r A v σ ∪ rayHitSet r B v σ := by
  zufso
  simp only [rayHitSet, mem_ofPred_eq, mem_union]
  tauto

/-- **First hit against a union**: the ray hits `A ∪ B` first at the earlier of its first hits
of `A` and of `B`. -/
theorem rayHit_union (A B : Set Point) (v : Point) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    rayHit r ztbgp v σ = min ztglq (rayHit r B v σ) := by
  unfold rayHit
  rw [rayHitSet_union]
  exact csInf_union ztqvi ztkdz
    ztqvj (rayHitSet_nonempty r B v hσ)

/-- A larger obstacle is hit earlier. -/
theorem rayHit_anti {r : ℝ} {A B : Set Point} (hAB : A ⊆ B) (v : Point) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) : rayHit r B v σ ≤ rayHit r A v σ :=
  csInf_le_csInf ztqvj ztkdz
    fun _ ht => ⟨ht.1, ht.2.imp id by_grind⟩

/-- If the open stretch `(0, t₀)` of the ray is in the box and off `A`, the first hit is at or
after `t₀`. -/
theorem le_rayHit {r : ℝ} {A : Set Point} {v : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {t₀ : ℝ}
    (h : ∀ t, 0 < t → t < t₀ → rayPt v σ t ∈ Chain.box r ∧ rayPt v σ t ∉ A) :
    t₀ ≤ rayHit r A v σ := by
  refine le_csInf ztkdz fun t ht => ?_
  zube

  obtain ⟨h1, h2⟩ := h t ht.1 hlt
  rcases ht.2 with h3 | h3
  · simp_all
  simp_all

/-- **The first hit.**  Every point of the ray strictly before the first hit is in the box and
off `A`; if the first-hit parameter is positive, the first-hit point is outside the box or on
`A` (for closed `A`). -/
theorem rayHit_spec {r : ℝ} {A : Set Point} (hA : IsClosed A) (v : Point) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    (∀ t, 0 < t → t < rayHit r A v σ → rayPt v σ t ∈ Chain.box r ∧ rayPt v σ t ∉ A) ∧
      (0 < rayHit r A v σ →
        rayPt v σ ztglq ∉ Chain.box r ∨ rayPt v σ ztglq ∈ A) := by
  have hne := rayHitSet_nonempty r A v hσ
  have hbdd := rayHitSet_bddBelow r A v σ
  refine ⟨fun t ht1 ht2 => ?_, fun hpos => ?_⟩
  · zukr
    have hmem : t ∈ rayHitSet r A v σ := by
      refine ⟨ht1, ?_⟩
      grind
    exact absurd (rayHit_le hmem) ztwah
  · have hset : rayHitSet r A v σ =
        Ici ztglq ∩ rayPt v σ ⁻¹' ((Chain.box r)ᶜ ∪ A) := by
      zufso
      constructor
      · zuibv
        exact ⟨rayHit_le ht, ht.2⟩
      · rintro ⟨ht1, ht2⟩
        exact ⟨by_grind, ht2⟩
    have hclosed : IsClosed ztkdy := by
      zucju
      exact isClosed_Ici.inter
        (((Chain.isOpen_box r).isClosed_compl.union hA).preimage zttig)
    exact (hclosed.csInf_mem hne hbdd).2

/-! ### The slit is invisible to horizontal rays below the top -/

/-- At a height `≤ C.top.2`, a point is outside the domain iff it is outside the box or on the
chain: the slit plays no role. -/
theorem not_mem_dom_iff (C : Chain) {p : Point} (hp : p.2 ≤ C.top.2) :
    p ∉ C.dom ↔ p ∉ Chain.box C.radius ∨ p ∈ C.set := by
  rw [C.mem_dom_iff]
  constructor
  · zuq
    by_cases hb : p ∈ Chain.box C.radius
    · right
      by_contra hs
      zuhrs
      refine ⟨hb, hs, fun hsl => hs ?_⟩
      obtain ⟨h1, h2, -⟩ := C.mem_slit_iff.1 hsl
      zuhdk
      zubk
      exact C.top_mem_set
    simp_all
  grind

/-- **The slit is invisible.**  For a point `v` at height `≤ C.top.2`, the hit set of the
horizontal ray from `v` (defined with the slit) equals the slit-free hit set of the chain. -/
theorem hitSet_eq_rayHitSet (C : Chain) {v : Point} (hv : v.2 ≤ C.top.2) (σ : ℝ) :
    C.hitSet v σ = rayHitSet C.radius C.set v σ := by
  zufso
  simp only [Chain.hitSet, rayHitSet, mem_ofPred_eq, mem_compl_iff]
  rw [not_mem_dom_iff C by_simp_all]

/-- The first-hit parameter of a chain ignores the slit below the top. -/
theorem hitParam_eq_rayHit (C : Chain) {v : Point} (hv : v.2 ≤ C.top.2) (σ : ℝ) :
    C.hitParam v σ = rayHit C.radius C.set v σ := by
  unfold Chain.hitParam rayHit
  rw [hitSet_eq_rayHitSet C hv]

/-- First-hit parameters are nonnegative. -/
theorem hitParam_nonneg (C : Chain) (v : Point) (σ : ℝ) : 0 ≤ C.hitParam v σ :=
  Real.sInf_nonneg fun _ ht => ht.1.le

/-- Two vertices of a chain of a simple polygon coincide only if their indices do. -/
theorem vertex_inj (C : Chain) (hP : C.P.Simple) {a b : ℕ} (ha : a ≤ C.m) (hb : b ≤ C.m)
    (h : C.vertex a = C.vertex b) : a = b := by
  zumdy
  have h1 := simple_vtx_inj hP ztuxc ztuxd h
  zuftc
  zumrh
  rwa [Nat.mod_eq_of_lt by_omega, Nat.mod_eq_of_lt by_omega] at h2

/-- Distinct chain edges have distinct indices in the polygon. -/
theorem edgeIdx_inj (C : Chain) {a b : ℕ} (ha : a < C.P.n) (hb : b < C.P.n)
    (h : C.edgeIdx a = C.edgeIdx b) : a = b := by
  have h2 := Nat.ModEq.add_left_cancel' C.s h
  zumrh
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2

/-- A point common to two chain edges `a ≠ b` of a simple polygon is a common vertex. -/
theorem mem_chainEdge_inter (C : Chain) (hP : C.P.Simple) {a b : ℕ} (ha : a < C.P.n)
    (hb : b < C.P.n) (hab : a ≠ b) {p : Point} (hpa : p ∈ C.chainEdge a)
    (hpb : p ∈ C.chainEdge b) :
    (p = C.vertex a ∨ p = C.vertex ztdf) ∧ (p = C.vertex b ∨ p = C.vertex ztds) := by
  have hne := fun h => hab (edgeIdx_inj C ha hb h)
  have hmem : p ∈ C.P.edge _ ∩ C.P.edge _ := ⟨hpa, hpb⟩
  rw [simple_edge_inter hP ztuxc ztuxd hne] at hmem
  zuchx
  rw [C.edgeIdx_succ] at h1 h2
  trivial

/-! ### Horizontal rays: elementary facts -/

/-- An initial piece of a horizontal segment from `v` is contained in a longer one. -/
theorem segment_rayPt_subset {t t' : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t') :
    Chazelle.segment v zthzo ⊆ Chazelle.segment v ztrvc := by
  apply Geometry.segment_subset_of_convex ztemu
    ztdte
  rcases (ht.trans htt').lt_or_eq with hpos | h0
  · refine ⟨t / t', div_nonneg ht hpos.le, (div_le_one hpos).2 htt', ?_⟩
    zujev
    · zudlo
      grind
    simp
  · zukgf
    rw [ht0, rayPt_zero]
    zucvg

/-- The initial part of a ray from a point off a closed set avoids the set. -/
theorem eventually_not_mem_of_not_mem {A : Set Point} (hA : IsClosed A) {v : Point}
    (hv : v ∉ A) (σ : ℝ) : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt v σ t ∉ A := by
  have hcont : ContinuousAt (rayPt v σ) 0 := (continuous_rayPt v σ).continuousAt
  have hmem : Aᶜ ∈ 𝓝 (rayPt v σ 0) := by
    zuohc; exact hA.isOpen_compl.mem_nhds hv
  exact nhdsWithin_le_nhds ztvuu

/-! ### Two adjacent subchains -/

/-- Two adjacent subchains `(P, s, m₁)` and `(P, s + m₁, m₂)` of the same polygon, sharing the
vertex `s + m₁`, whose union `(P, s, m₁ + m₂)` still misses an edge of `P`. -/
structure Junction where
  /-- The ambient polygon. -/
  P : Polygon
  /-- The first edge of the left chain (and of the union). -/
  s : ℕ
  /-- The number of edges of the left chain `C₁`. -/
  m₁ : ℕ
  /-- The number of edges of the right chain `C₂`. -/
  m₂ : ℕ
  one_le_m₁ : 1 ≤ m₁
  one_le_m₂ : 1 ≤ m₂
  /-- The union misses at least one edge of `P`. -/
  add_le : m₁ + m₂ + 1 ≤ P.n
namespace Junction
variable (J : Junction)

/-- The left chain `C₁ = (P, s, m₁)`. -/
def left : Chain := ⟨J.P, J.s, J.m₁, J.one_le_m₁, by have := J.add_le; omega⟩

/-- The right chain `C₂ = (P, s + m₁, m₂)`. -/
def right : Chain := ⟨J.P, J.s + J.m₁, J.m₂, J.one_le_m₂, by have := J.add_le; omega⟩

/-- The union `C = (P, s, m₁ + m₂)`. -/
def whole : Chain := ⟨J.P, J.s, J.m₁ + J.m₂, by have := J.one_le_m₁; omega, J.add_le⟩

/-- The junction of two given adjacent chains `C₁ = (P, s, m₁)` and `C₂ = (P, s + m₁, m₂)`. -/
def ofChains (C₁ C₂ : Chain) (hn : C₁.m + C₂.m + 1 ≤ C₁.P.n) : Junction :=
  ⟨C₁.P, C₁.s, C₁.m, C₂.m, C₁.one_le, C₂.one_le, hn⟩
@[simp] theorem left_m : J.left.m = J.m₁ := rfl
@[simp] theorem right_m : J.right.m = J.m₂ := rfl
@[simp] theorem whole_m : J.whole.m = J.m₁ + J.m₂ := rfl

/-- The shared vertex `C₁ ∩ C₂`. -/
def shared : Point := J.left.vertex J.m₁

/-- The vertices of `C₁` are the first vertices of `C`. -/
theorem whole_vertex (k : ℕ) : J.whole.vertex k = J.left.vertex k := rfl
variable (j : ℕ)
/-- Vertex `m₁ + j` of `C` is vertex `j` of `C₂`. -/
theorem whole_vertex_add : J.whole.vertex zthaw = J.right.vertex j := by
  show J.P.vtx ztymi = J.P.vtx ztlck
  grind

/-- The first vertex of `C₂` is the shared vertex. -/
theorem right_vertex_zero : J.right.vertex 0 = J.shared := by
  rfl

/-- Vertex `m₁` of `C` is the shared vertex. -/
theorem whole_vertex_m₁ : J.whole.vertex J.m₁ = J.shared := rfl

/-- Edge `m₁ + j` of `C` is edge `j` of `C₂`. -/
theorem whole_chainEdge_add : J.whole.chainEdge zthaw = J.right.chainEdge j := by
  show J.P.edge ztymi = J.P.edge ztlck
  grind

/-- **The union of the two chains.** -/
theorem whole_set : J.whole.set = J.left.set ∪ J.right.set := by
  zufj
  constructor
  · zucje
    rw [whole_m] at hk
    by_cases hk1 : k < J.m₁
    · exact Or.inl ⟨k, hk1, hp⟩
    · right
      refine ⟨k - J.m₁, by rw [right_m]; omega, ?_⟩
      have hk' : k = J.m₁ + (k - J.m₁) := by_omega
      rw [hk', whole_chainEdge_add] at hp
      zuitn
  · rintro (⟨k, hk, hp⟩ | ⟨j, hj, hp⟩)
    · exact ⟨k, by rw [whole_m]; rw [left_m] at hk; omega, hp⟩
    · refine ⟨J.m₁ + j, by_simp_all, ?_⟩
      zupdy
      zuitn

/-- `C₁ ⊆ C`. -/
theorem left_set_subset : J.left.set ⊆ J.whole.set := by
  zukze

/-- `C₂ ⊆ C`. -/
theorem right_set_subset : J.right.set ⊆ J.whole.set := by
  zukze

/-- The shared vertex is on `C₁`. -/
theorem shared_mem_left : J.shared ∈ J.left.set := J.left.vertex_mem_set le_rfl

/-- The shared vertex is on `C₂`. -/
theorem shared_mem_right : J.shared ∈ J.right.set := by
  rw [← right_vertex_zero]; exact J.right.vertex_mem_set ztbg

/-- The top of `C₁` is not above the top of `C`. -/
theorem left_top_le : J.left.top.2 ≤ J.whole.top.2 :=
  J.whole.vertex_snd_le_top (j := J.left.topIdx) (by rw [whole_m]; have := J.left.topIdx_le; rw [left_m] at this; omega)

/-- The top of `C₂` is not above the top of `C`. -/
theorem right_top_le : J.right.top.2 ≤ J.whole.top.2 := by
  have h := J.whole.vertex_snd_le_top (j := J.m₁ + J.right.topIdx)
    (by rw [whole_m]; have := J.right.topIdx_le; simp_all)
  rw [whole_vertex_add] at h
  zubh

/-- **The two chains meet exactly in the shared vertex** (for a simple polygon). -/
theorem left_inter_right (hP : J.P.Simple) : J.left.set ∩ J.right.set = {J.shared} := by
  zugjb
  · rintro p ⟨⟨k, hk, hpk⟩, ⟨j, hj, hpj⟩⟩
    rw [left_m] at hk
    rw [right_m] at hj
    have hn := J.add_le
    have hpk' := hpk
    have hpj' : p ∈ J.whole.chainEdge zthaw := by zupdy; omega
    have hwP := hP
    obtain ⟨h1, h2⟩ := mem_chainEdge_inter J.whole hwP
      (by show k < J.P.n; omega) (by show J.m₁ + j < J.P.n; omega) by_omega hpk' hpj'
    have hinj : ∀ a b, a ≤ J.m₁ + J.m₂ → b ≤ J.m₁ + J.m₂ → J.whole.vertex a = J.whole.vertex b →
        a = b := fun a b ha hb h => vertex_inj J.whole hwP ha hb h
    rw [mem_singleton_iff]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · grind
    · grind
    · have := hinj _ _ by_omega by_omega (h1.symm.trans h2)
      rw [h1, show k + 1 = J.m₁ by omega]
      rfl
    grind
  · rintro p rfl
    exact ⟨J.shared_mem_left, J.shared_mem_right⟩

/-- A vertex of `C₂` other than the shared one is not on `C₁`. -/
theorem right_vertex_not_mem_left (hP : J.P.Simple) {j : ℕ} (hj0 : 0 < j) (hj : j ≤ J.m₂) :
    J.right.vertex j ∉ J.left.set := by
  zuq
  have hmem : J.right.vertex j ∈ J.left.set ∩ J.right.set :=
    ⟨h, J.right.vertex_mem_set by_simp_all⟩
  rw [J.left_inter_right hP, mem_singleton_iff, ← right_vertex_zero] at hmem
  have := vertex_inj J.right hP by_simp_all
    ztbg hmem
  omega

/-! ### Chord truncation -/

/-! ### Free directions -/

/-! ### The chords of the union -/
end Junction
open Chazelle.Visibility (hseg segment_horizontal_eq_hseg)
open Chazelle.Chain (IsHChordIn openHSeg hseg_inter_eq_openHSeg isPreconnected_openHSeg openHSeg_nonempty mem_openHSeg_iff)
theorem fst_image_hseg (y a b : ℝ) : Prod.fst '' hseg y a b = Icc a b := by
  zumx
  constructor
  · rintro ⟨p, ⟨-, h1, h2⟩, rfl⟩
    simp_all
  · zubf
    exact ⟨ztjw, ⟨rfl, h1, h2⟩, rfl⟩
variable {y a b : ℝ} (p : Point) {T : ℝ} (C : Chain) (k : ℕ) (σ : ℝ)
/-- The heights of a nonempty horizontal segment. -/
theorem snd_image_hseg (h : a ≤ b) : Prod.snd '' hseg y a b = {y} := by
  zufso
  constructor
  · rintro ⟨p, ⟨hp, -, -⟩, rfl⟩
    zuitn
  · zunq
    exact ⟨(a, t), ⟨rfl, le_rfl, h⟩, rfl⟩

/-- The left endpoint of a horizontal segment. -/
noncomputable def lend (c : Set Point) : Point := (sInf zttbk, sSup zttbl)

/-- The right endpoint of a horizontal segment. -/
noncomputable def rend (c : Set Point) : Point := (sSup zttbk, sSup zttbl)

/-- The left endpoint of `hseg y a b` (for `a ≤ b`) is `(a, y)`. -/
theorem lend_hseg (h : a ≤ b) : lend ztbiq = ztdv := by
  simp only [lend, fst_image_hseg, snd_image_hseg h, csInf_Icc h, csSup_singleton]

/-- The right endpoint of `hseg y a b` (for `a ≤ b`) is `(b, y)`. -/
theorem rend_hseg (h : a ≤ b) : rend ztbiq = ztdy := by
  simp only [rend, fst_image_hseg, snd_image_hseg h, csSup_Icc h, csSup_singleton]

/-- A nonempty horizontal segment determines its height and abscissae. -/
theorem hseg_inj {y a b y' a' b' : ℝ} (hab : a ≤ b) (h : hseg y a b = hseg y' a' b') :
    y = y' ∧ a = a' ∧ b = b' := by
  have hne : a' ≤ b' := by
    have : ztygh := h ▸ (⟨rfl, le_rfl, hab⟩ : (ztdv : Point) ∈ hseg y a b)
    exact this.2.1.trans this.2.2
  have h1 := lend_hseg hab (y := y)
  have h2 := rend_hseg hab (y := y)
  rw [h, lend_hseg hne] at h1
  rw [h, rend_hseg hne] at h2
  simp_all

/-- A rightward ray segment as an `hseg`. -/
theorem segment_rayPt_pos (hT : 0 ≤ T) :
    Chazelle.segment p (rayPt p 1 T) = hseg p.2 p.1 (p.1 + T) := by
  rw [segment_horizontal_eq_hseg by_simp_all, rayPt_fst, one_mul,
    min_eq_left by_linarith, max_eq_right by_linarith]

/-- A leftward ray segment as an `hseg`. -/
theorem segment_rayPt_neg (hT : 0 ≤ T) :
    Chazelle.segment p (rayPt p (-1) T) = hseg p.2 (p.1 - T) p.1 := by
  rw [segment_horizontal_eq_hseg by_simp_all, rayPt_fst, neg_one_mul,
    min_eq_right by_linarith, max_eq_left by_linarith, ← sub_eq_add_neg]

/-! ### Augmented chords -/

/-- The **augmented chords** of a chain: horizontal chords of its domain (open part in the
domain, both endpoints off it) at heights not above the top of the chain. -/
def augChords (C : Chain) : Set ztf :=
  {c | ∃ y a b : ℝ, IsHChordIn C.dom y a b ∧ y ≤ C.top.2 ∧ c = hseg y a b}

/-- Vertex chords are augmented chords. -/
theorem chords_subset_augChords : C.chords ⊆ augChords C := by
  zung
  obtain ⟨k, σ, hk, -, -, rfl, hh⟩ := C.chords_spec hc
  exact ⟨_, _, _, hh, C.vertex_snd_le_top hk, C.chordSet_eq_hseg k σ⟩

/-- Unpacking an augmented chord: its parameters and endpoints. -/
theorem augChords_spec {C : Chain} {c : Set Point} (hc : c ∈ augChords C) :
    ∃ y a b : ℝ, IsHChordIn C.dom y a b ∧ y ≤ C.top.2 ∧ c = hseg y a b ∧
      lend c = ztdv ∧ rend c = ztdy := by
  zudrs
  exact ⟨y, a, b, h, hy, rfl, lend_hseg h.lt.le, rend_hseg h.lt.le⟩

/-- The left endpoint of a horizontal chord of the domain is anchorable. -/
theorem anchorable_left (C : Chain) {y a b : ℝ} (h : IsHChordIn C.dom y a b) :
    C.Anchorable (ztdv : Point) := by
  zudzg

  by_cases hbox : (ztdv : Point) ∈ Chain.box C.radius
  · have hnd := h.left_not
    zujgk

  · zurx
    have hge : C.radius ≤ |a| := by
      zube

      tauto
    zumjd
    zuum

    zujdw
    · have := (C.dom_subset_box hmid).1
      zugub

    · -- `a < -R`: a point of the open chord just right of `a` is outside the box
      have hx1 : a < ztgey / 2 := by
        have : a < min b (-C.radius) := lt_min h.lt by_linarith
        linarith
      have hx2 : ztgey / 2 < b := by
        grind
      have hx3 : ztgey / 2 < -C.radius := by
        grind
      have := (C.dom_subset_box ztrrf).1
      grind

/-- The right endpoint of a horizontal chord of the domain is anchorable. -/
theorem anchorable_right (C : Chain) {y a b : ℝ} (h : IsHChordIn C.dom y a b) :
    C.Anchorable (ztdy : Point) := by
  zudzg

  by_cases hbox : (ztdy : Point) ∈ Chain.box C.radius
  · have hnd := h.right_not
    zujgk

  · zurx
    have hge : C.radius ≤ |b| := by
      zube

      tauto
    zumjd
    zuum

    zujdw
    · have hx1 : a < ztkaq / 2 := by
        have  := max_lt h.lt h1
        grind
      have hx2 : ztkaq / 2 < b := by
        grind
      have hx3 : C.radius < ztkaq / 2 := by
        grind
      have := (C.dom_subset_box ztrrf).1
      grind
    · have := (C.dom_subset_box hmid).1
      zugub

/-- **Every finite family of augmented chords is a chord system of the domain.** -/
theorem augChordSystem {F : Set ztf} (hF : F ⊆ augChords C)
    (hfin : F.Finite) : ChordSystem C.dom F where
  isOpen := C.isOpen_dom
  finite := hfin
  hchord := by
    zung
    zudjh
    grind
  walk := by
    intro c hc z hz hzd
    zudjh
    have hseg_eq : Chazelle.segment (ztdv : Point) ztdy = hseg y a b := by
      zuceo
      zubvt
      rw [min_eq_left h.lt.le, max_eq_right h.lt.le]
    rw [← hseg_eq] at hz ⊢
    exact C.exists_walk_parity_flip (anchorable_left C h) (anchorable_right C h)
      (by simp only [ne_eq]; exact h.lt.ne) hz hzd

/-! ### Removal in augmented submaps -/

/-! ### Shooting along a chord -/

/-- The initial part of the ray from `p` in direction `σ` lies in the domain. -/
def FreeAt (C : Chain) (p : Point) (σ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt p σ t ∈ C.dom

/-- The chord of `C` seen from `p` in direction `σ`: the segment from `p` to the first point of
`(C.dom)ᶜ` on the ray (Chazelle's "point of `∂C` seen by `p`"). -/
noncomputable def shoot (C : Chain) (p : Point) (σ : ℝ) : Set Point :=
  Chazelle.segment p (rayPt p σ ztsvv)

/-- Shooting from a chain vertex gives its vertex chord. -/
theorem shoot_vertex : shoot C ztib σ = C.chordSet k σ := rfl

/-- Freeness at a chain vertex is `DirFree`. -/
theorem freeAt_vertex : FreeAt C ztib σ ↔ C.DirFree k σ :=
  Iff.rfl

/-- **The first hit from a free point** at height `≤ C.top.2` (the point may be on the box
perimeter). -/
theorem hit_of_freeAt {p : Point} (hp : p.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (h : FreeAt C p σ) :
    0 < C.hitParam p σ ∧ rayPt p σ ztsvv ∉ C.dom ∧
      ∀ t, 0 < t → t < C.hitParam p σ → rayPt p σ t ∈ C.dom := by
  rw [hitParam_eq_rayHit C hp]
  zuvg
  zuduw
  have hle := le_rayHit hσ fun t ht1 ht2 => by
    have hd : rayPt p σ t ∈ C.dom := hsub ztuii
    exact ⟨C.dom_subset_box hd, C.not_mem_set_of_mem_dom hd⟩
  have hpos := lt_of_lt_of_le hu hle
  obtain ⟨h1, h2⟩ := rayHit_spec (r := C.radius) C.isClosed_set p hσ
  have hsnd : ∀ t, (rayPt p σ t).2 ≤ C.top.2 := by_simp_all
  refine ⟨hpos, (not_mem_dom_iff C (hsnd _)).2 (h2 hpos), fun t ht1 ht2 => ?_⟩
  zuhtn
  obtain ⟨hb, hs⟩ := h1 t ht1 ht2
  rcases (not_mem_dom_iff C (hsnd t)).1 hnd with h' | h'
  · simp_all
  simp_all

/-- The chord seen from a free point off the domain is an augmented chord. -/
theorem shoot_mem_augChords {p : Point} (hp : p.2 ≤ C.top.2) (hnd : p ∉ C.dom)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (h : FreeAt C p σ) : shoot C p σ ∈ augChords C := by
  obtain ⟨hpos, hend, hint⟩ := hit_of_freeAt C hp hσ h
  set T := C.hitParam p σ with hT
  zur
  · refine ⟨p.2, p.1, p.1 + T, ⟨by_linarith, hnd, ?_, fun x hx1 hx2 => ?_⟩, hp,
      segment_rayPt_pos p hpos.le⟩
    · have : ((p.1 + T, p.2) : Point) = rayPt p 1 T := by zvmxf
      simp_all
    · have := hint ztudr by_linarith by_linarith
      have e : rayPt p 1 ztudr = (ztkhc : Point) := by
        zubzy
      simp_all
  · refine ⟨p.2, p.1 - T, p.1, ⟨by_linarith, ?_, hnd, fun x hx1 hx2 => ?_⟩, hp,
      segment_rayPt_neg p hpos.le⟩
    · have : ((p.1 - T, p.2) : Point) = rayPt p (-1) T := by zunob
      simp_all
    · have := hint zttvk by_linarith by_linarith
      have e : rayPt p (-1) zttvk = (ztkhc : Point) := by
        zubiu
      simp_all

/-- Shooting rightwards from the left end of a segment whose right end is off the domain stays
inside the segment. -/
theorem shoot_subset_pos {y a b : ℝ} (hab : a < b)
    (hb : (ztdy : Point) ∉ C.dom) : shoot C (ztdv : Point) 1 ⊆ hseg y a b := by
  have hle : C.hitParam (ztdv : Point) 1 ≤ b - a := by
    refine C.hitParam_le_of_not_mem_dom _ 1 by_linarith ?_
    have : ztxrp := by
      zubzy
    simp_all
  have h := segment_rayPt_subset (ztdv : Point) 1 (hitParam_nonneg C _ 1) hle
  have e : Chazelle.segment (ztdv : Point) (rayPt (ztdv : Point) 1 zthu) = hseg y a b := by
    rw [segment_rayPt_pos _ by_linarith]
    simp
  zudtt
  zubh

/-- Shooting leftwards from the right end of a segment whose left end is off the domain stays
inside the segment. -/
theorem shoot_subset_neg {y a b : ℝ} (hab : a < b)
    (ha : (ztdv : Point) ∉ C.dom) : shoot C (ztdy : Point) (-1) ⊆ hseg y a b := by
  have hle : C.hitParam (ztdy : Point) (-1) ≤ b - a := by
    refine C.hitParam_le_of_not_mem_dom _ _ by_linarith ?_
    have : ztxiz := by
      zubiu
    simp_all
  have h := segment_rayPt_subset (ztdy : Point) (-1) (hitParam_nonneg C _ _) hle
  have e : Chazelle.segment (ztdy : Point) (rayPt (ztdy : Point) (-1) zthu) =
      hseg y a b := by
    rw [segment_rayPt_neg _ by_linarith]
    simp
  zudtt
  zubh

/-! ### Vertex chords as shots -/

/-! ### The chord through a point, and finiteness of the chords at one height -/

/-- Every point of the (open) domain is free in every direction. -/
theorem freeAt_of_mem_dom {p : Point} (hp : p ∈ C.dom) (σ : ℝ) : FreeAt C p σ := by
  have hcont : ContinuousAt ztogw 0 := (continuous_rayPt p σ).continuousAt
  have hmem : C.dom ∈ 𝓝 (rayPt p σ 0) := by
    zuohc; exact C.isOpen_dom.mem_nhds hp
  exact nhdsWithin_le_nhds ztvuu

/-- The left end of a horizontal chord of the domain is free rightwards. -/
theorem freeAt_of_isHChordIn_left {y a b : ℝ} (h : IsHChordIn C.dom y a b) :
    FreeAt C (ztdv : Point) 1 := by
  zuhuq
  zucvm
  zui
  exact h.open_mem _ by_simp_all by_grind

/-- The right end of a horizontal chord of the domain is free leftwards. -/
theorem freeAt_of_isHChordIn_right {y a b : ℝ} (h : IsHChordIn C.dom y a b) :
    FreeAt C (ztdy : Point) (-1) := by
  zuhuq
  have e : ztwtc := by
    zubvf
  zui
  exact h.open_mem _ by_grind by_simp_all

/-- A horizontal chord of the domain is the chord shot from its left end. -/
theorem hseg_eq_shoot {y a b : ℝ} (h : IsHChordIn C.dom y a b) :
    hseg y a b = shoot C (ztdv : Point) 1 := by
  have hT : C.hitParam (ztdv : Point) 1 = b - a := by
    refine C.hitParam_eq_of_first _ 1 ztbsh ?_ fun s hs1 hs2 => ?_
    · have : ztxrp := by
        zubzy
      zujlp
    · have e : rayPt (ztdv : Point) 1 s = ((a + s, y) : Point) := by zvmxf
      zui
      zulfd
  unfold shoot
  rw [hT, segment_rayPt_pos _ ztbsh]
  simp

/-- A horizontal chord of the domain is the chord shot from its right end. -/
theorem hseg_eq_shoot_neg {y a b : ℝ} (h : IsHChordIn C.dom y a b) :
    hseg y a b = shoot C (ztdy : Point) (-1) := by
  have hT : C.hitParam (ztdy : Point) (-1) = b - a := by
    refine C.hitParam_eq_of_first _ _ ztbsh ?_ fun s hs1 hs2 => ?_
    · have : ztxiz := by
        zubiu
      zujlo
    · have e : rayPt (ztdy : Point) (-1) s = ((b - s, y) : Point) := by
        zubvf
      zui
      zulfd
  unfold shoot
  rw [hT, segment_rayPt_neg _ ztbsh]
  simp

/-! ### Regions are closed under visibility -/
namespace Junction
variable (J : Junction)
variable {p : Point} {c : Set Point} {S₁ S₂ : Set (Set Point)}
/-- A point off the domain of `C₁` at height `≤ C₁.top.2` is off the domain of `C`. -/
theorem not_mem_whole_dom_of_left (hp : p.2 ≤ J.left.top.2) (h : p ∉ J.left.dom) :
    p ∉ J.whole.dom := by
  rw [not_mem_dom_iff J.whole ztvvw]
  rcases (not_mem_dom_iff J.left hp).1 h with h' | h'
  · tauto
  · exact Or.inr ztuzb

/-- A point off the domain of `C₂` at height `≤ C₂.top.2` is off the domain of `C`. -/
theorem not_mem_whole_dom_of_right (hp : p.2 ≤ J.right.top.2)
    (h : p ∉ J.right.dom) : p ∉ J.whole.dom := by
  rw [not_mem_dom_iff J.whole ztvvx]
  rcases (not_mem_dom_iff J.right hp).1 h with h' | h'
  · tauto
  · exact Or.inr ztuze

/-- A point of the domain of `C₁` below the top of `C₁` and off `C₂` is in the domain of `C`. -/
theorem mem_whole_dom_of_left (hp : p.2 ≤ J.left.top.2) (h : p ∈ J.left.dom)
    (h2 : p ∉ J.right.set) : p ∈ J.whole.dom := by
  zuhtn
  rcases (not_mem_dom_iff J.whole ztvvw).1 hnd with h' | h'
  · exact h' (J.left.dom_subset_box h)
  · zufor

    · exact J.left.not_mem_set_of_mem_dom h h'
    simp_all

/-- A point of the domain of `C₂` below the top of `C₂` and off `C₁` is in the domain of `C`. -/
theorem mem_whole_dom_of_right (hp : p.2 ≤ J.right.top.2) (h : p ∈ J.right.dom)
    (h1 : p ∉ J.left.set) : p ∈ J.whole.dom := by
  zuhtn
  rcases (not_mem_dom_iff J.whole ztvvx).1 hnd with h' | h'
  · exact h' (J.right.dom_subset_box h)
  · zufor

    · simp_all
    · exact J.right.not_mem_set_of_mem_dom h h'

/-- A point of the domain of `C` at height `≤ C₁.top.2` is in the domain of `C₁`. -/
theorem mem_left_dom_of_whole (hp : p.2 ≤ J.left.top.2) (h : p ∈ J.whole.dom) :
    p ∈ J.left.dom := by
  zuhtn
  rcases (not_mem_dom_iff J.left hp).1 hnd with h' | h'
  · exact h' ztuzh
  · exact J.whole.not_mem_set_of_mem_dom h ztuzb

/-- A point of the domain of `C` at height `≤ C₂.top.2` is in the domain of `C₂`. -/
theorem mem_right_dom_of_whole (hp : p.2 ≤ J.right.top.2) (h : p ∈ J.whole.dom) :
    p ∈ J.right.dom := by
  zuhtn
  rcases (not_mem_dom_iff J.right hp).1 hnd with h' | h'
  · exact h' ztuzh
  · exact J.whole.not_mem_set_of_mem_dom h ztuze

/-- The chords of `C` at the shared vertex (Chazelle's chords "incident upon the vertices of
`∂C` resulting from the duplication of the vertex `C₁ ∩ C₂`"). -/
def sharedChords : Set ztf :=
  {d | ∃ σ : ℝ, ztdd ∧ J.whole.DirFree J.m₁ σ ∧ d = J.whole.chordSet J.m₁ σ}

/-- **The fusion of `S₁` and `S₂`** (Chazelle p. 501): the chords of `C` seen from the two
endpoints of every chord of `S₁ ∪ S₂` along that chord (when the direction is free for `C`),
together with the chords of `C` at the shared vertex. -/
def fusion (S₁ S₂ : Set ztf) : Set ztf :=
  {d | ∃ c ∈ S₁ ∪ S₂, FreeAt J.whole zthyr 1 ∧ d = shoot J.whole zthyr 1} ∪
    {d | ∃ c ∈ S₁ ∪ S₂, FreeAt J.whole ztial (-1) ∧ d = shoot J.whole ztial (-1)} ∪
    J.sharedChords

/-- The shared-vertex chords are vertex chords of `C`. -/
theorem sharedChords_subset_chords : J.sharedChords ⊆ J.whole.chords := by
  rintro d ⟨σ, hσ, h, rfl⟩
  exact ⟨J.m₁, σ, by_simp, hσ, h, rfl⟩

/-- The shared-vertex chords belong to the fusion. -/
theorem sharedChords_subset_fusion (S₁ S₂ : Set ztf) :
    J.sharedChords ⊆ J.fusion S₁ S₂ :=
  fun _ h => Or.inr h

/-- The endpoints of an augmented chord of `C₁` are off the domain of `C`, at height
`≤ C.top.2`. -/
theorem ends_left (hc : c ∈ augChords J.left) :
    (lend c).2 ≤ J.left.top.2 ∧ lend c ∉ J.whole.dom ∧ (rend c).2 ≤ J.left.top.2 ∧
      rend c ∉ J.whole.dom := by
  zubru

  exact ⟨hy, J.not_mem_whole_dom_of_left hy h.left_not, hy,
    J.not_mem_whole_dom_of_left hy h.right_not⟩

/-- The endpoints of an augmented chord of `C₂` are off the domain of `C`, at height
`≤ C₂.top.2`. -/
theorem ends_right (hc : c ∈ augChords J.right) :
    (lend c).2 ≤ J.right.top.2 ∧ lend c ∉ J.whole.dom ∧ (rend c).2 ≤ J.right.top.2 ∧
      rend c ∉ J.whole.dom := by
  zubru

  exact ⟨hy, J.not_mem_whole_dom_of_right hy h.left_not, hy,
    J.not_mem_whole_dom_of_right hy h.right_not⟩

/-- **The fusion is an augmented submap of `V(C)`.** -/
theorem fusion_subset_augChords (hS₁ : S₁ ⊆ augChords J.left)
    (hS₂ : S₂ ⊆ augChords J.right) : J.fusion S₁ S₂ ⊆ augChords J.whole := by
  have hends : ∀ c ∈ S₁ ∪ S₂, (lend c).2 ≤ J.whole.top.2 ∧ lend c ∉ J.whole.dom ∧
      (rend c).2 ≤ J.whole.top.2 ∧ rend c ∉ J.whole.dom := by
    zubyh
    · obtain ⟨h1, h2, h3, h4⟩ := J.ends_left ztmkw
      exact ⟨h1.trans J.left_top_le, h2, h3.trans J.left_top_le, h4⟩
    · obtain ⟨h1, h2, h3, h4⟩ := J.ends_right ztbac
      exact ⟨h1.trans J.right_top_le, h2, h3.trans J.right_top_le, h4⟩
  rintro d ((⟨c, hc, hfree, rfl⟩ | ⟨c, hc, hfree, rfl⟩) | hd)
  · obtain ⟨h1, h2, -, -⟩ := hends c hc
    exact shoot_mem_augChords J.whole h1 h2 ztp hfree
  · obtain ⟨-, -, h3, h4⟩ := hends c hc
    exact shoot_mem_augChords J.whole h3 h4 ztbt hfree
  · exact chords_subset_augChords J.whole (J.sharedChords_subset_chords hd)

/-- There are at most two shared-vertex chords (finiteness). -/
theorem sharedChords_finite : J.sharedChords.Finite := by
  refine ((finite_singleton (-1 : ℝ)).insert 1).image ztpbx
    |>.subset ?_
  zucej

/-- There are at most two shared-vertex chords. -/
theorem sharedChords_ncard_le : J.sharedChords.ncard ≤ 2 := by
  have hsub : J.sharedChords ⊆ ztpbx '' ({1, -1} : Set ℝ) := by
    zucej

  calc J.sharedChords.ncard
      ≤ ((J.whole.chordSet J.m₁) '' ({1, -1} : Set ℝ)).ncard :=
        ncard_le_ncard hsub by_simp_all
    _ ≤ ({1, -1} : Set ℝ).ncard := ncard_image_le ztcwq
    _ = 2 := ncard_pair by_norm_num

/-- The fusion is covered by the two shooting images of `S₁ ∪ S₂` and the shared chords. -/
theorem fusion_subset_image (S₁ S₂ : Set ztf) :
    J.fusion S₁ S₂ ⊆ (fun c => shoot J.whole zthyr 1) '' ztbzc ∪
      (fun c => shoot J.whole ztial (-1)) '' ztbzc ∪ J.sharedChords := by
  rintro d ((⟨c, hc, -, rfl⟩ | ⟨c, hc, -, rfl⟩) | hd)
  · grind
  · grind
  simp_all

/-- The fusion of finite submaps is finite. -/
theorem fusion_finite (h₁ : S₁.Finite) (h₂ : S₂.Finite) :
    (J.fusion S₁ S₂).Finite :=
  ((((h₁.union h₂).image _).union ((h₁.union h₂).image _)).union J.sharedChords_finite).subset
    ztsyi

/-- **Size of the fusion**: at most two chords per chord of `S₁ ∪ S₂`, plus the two chords at
the shared vertex. -/
theorem ncard_fusion_le (h₁ : S₁.Finite) (h₂ : S₂.Finite) :
    (J.fusion S₁ S₂).ncard ≤ 2 * zttdf + 2 := by
  have h12 := h₁.union h₂
  have hu : (S₁ ∪ S₂).ncard ≤ S₁.ncard + S₂.ncard := ncard_union_le _ _
  calc (J.fusion S₁ S₂).ncard
      ≤ (ztnyo '' ztbzc ∪
          ztnyp '' ztbzc ∪ J.sharedChords).ncard :=
        ncard_le_ncard ztsyi
          (((h12.image _).union (h12.image _)).union J.sharedChords_finite)
    _ ≤ (ztnyo '' ztbzc).ncard +
          (ztnyp '' ztbzc).ncard + J.sharedChords.ncard :=
        (ncard_union_le _ _).trans (Nat.add_le_add_right ztodr _)
    _ ≤ (S₁ ∪ S₂).ncard + (S₁ ∪ S₂).ncard + 2 :=
        Nat.add_le_add (Nat.add_le_add ztvzn ztvzn)
          J.sharedChords_ncard_le
    _ ≤ 2 * zttdf + 2 := by_omega

/-! ### Endpoints are preserved -/

/-- A chord of `C₁` shot from its left endpoint along itself w.r.t. `C` stays inside it. -/
theorem shoot_lend_subset (hc : c ∈ augChords J.left ∪ augChords J.right) :
    shoot J.whole zthyr 1 ⊆ c := by
  zunk
  · zujg
    zudug
    exact shoot_subset_pos J.whole h.lt (J.not_mem_whole_dom_of_left hy h.right_not)
  · zujg
    zudug
    exact shoot_subset_pos J.whole h.lt (J.not_mem_whole_dom_of_right hy h.right_not)

/-- A chord of `C₁` or `C₂` shot from its right endpoint along itself w.r.t. `C` stays
inside it. -/
theorem shoot_rend_subset (hc : c ∈ augChords J.left ∪ augChords J.right) :
    shoot J.whole ztial (-1) ⊆ c := by
  zunk
  · zujf
    zubim
    exact shoot_subset_neg J.whole h.lt (J.not_mem_whole_dom_of_left hy h.left_not)
  · zujf
    zubim
    exact shoot_subset_neg J.whole h.lt (J.not_mem_whole_dom_of_right hy h.left_not)

/-- An endpoint of an augmented chord of `C₁` lies on `C₂` only if it is the shared vertex. -/
theorem end_not_mem_right_of_left (hP : J.P.Simple) {p : Point} (hp : p.2 ≤ J.left.top.2)
    (hnd : p ∉ J.left.dom) (hne : p ≠ J.shared) : p ∉ J.right.set := by
  zuibu
  rcases (not_mem_dom_iff J.left hp).1 hnd with h | h
  · exact h (J.right.set_subset_box hr)
  · zulgw
    zuect

/-- An endpoint of an augmented chord of `C₂` lies on `C₁` only if it is the shared vertex. -/
theorem end_not_mem_left_of_right (hP : J.P.Simple) {p : Point} (hp : p.2 ≤ J.right.top.2)
    (hnd : p ∉ J.right.dom) (hne : p ≠ J.shared) : p ∉ J.left.set := by
  intro hl
  rcases (not_mem_dom_iff J.right hp).1 hnd with h | h
  · exact h (J.left.set_subset_box hl)
  · zulgw
    zuect

/-- **Endpoints are preserved (left chords, left endpoint).**  For a chord `c` of `S₁` whose left
endpoint is not the shared vertex, the rightward direction at `lend c` is free for `C`; so the
fusion contains a chord `shoot C (lend c) 1 ⊆ c` with endpoint `lend c`. -/
theorem lend_freeAt_left (hP : J.P.Simple) {c : Set Point} (hc : c ∈ augChords J.left)
    (hne : lend c ≠ J.shared) : FreeAt J.whole zthyr 1 := by
  zujg
  zujjg
  have hnr := J.end_not_mem_right_of_left hP hy h.left_not hne
  have hev := eventually_not_mem_of_not_mem J.right.isClosed_set hnr 1
  zubfp
  zucvm
  zuczt
  exact J.mem_whole_dom_of_left hy ztrre ht1

/-- Endpoints are preserved (left chords, right endpoint). -/
theorem rend_freeAt_left (hP : J.P.Simple) {c : Set Point} (hc : c ∈ augChords J.left)
    (hne : rend c ≠ J.shared) : FreeAt J.whole ztial (-1) := by
  zujf
  zujjv
  have hnr := J.end_not_mem_right_of_left hP hy h.right_not hne
  have hev := eventually_not_mem_of_not_mem J.right.isClosed_set hnr (-1)
  zubfp
  have e : ztwtc := by
    zubvf
  zuczt
  exact J.mem_whole_dom_of_left hy ztrrd ht1

/-- Endpoints are preserved (right chords, left endpoint). -/
theorem lend_freeAt_right (hP : J.P.Simple) {c : Set Point} (hc : c ∈ augChords J.right)
    (hne : lend c ≠ J.shared) : FreeAt J.whole zthyr 1 := by
  zujg
  zujjg
  have hnl := J.end_not_mem_left_of_right hP hy h.left_not hne
  have hev := eventually_not_mem_of_not_mem J.left.isClosed_set hnl 1
  zubfp
  zucvm
  zuczt
  exact J.mem_whole_dom_of_right hy ztrre ht1

/-- Endpoints are preserved (right chords, right endpoint). -/
theorem rend_freeAt_right (hP : J.P.Simple) {c : Set Point} (hc : c ∈ augChords J.right)
    (hne : rend c ≠ J.shared) : FreeAt J.whole ztial (-1) := by
  zujf
  zujjv
  have hnl := J.end_not_mem_left_of_right hP hy h.right_not hne
  have hev := eventually_not_mem_of_not_mem J.left.isClosed_set hnl (-1)
  zubfp
  have e : ztwtc := by
    zubvf
  zuczt
  exact J.mem_whole_dom_of_right hy ztrrd ht1

/-- **Endpoints are preserved** (summary): every endpoint of a chord of `S₁ ∪ S₂` other than the
shared vertex is an endpoint of a chord of the fusion contained in that chord. -/
theorem end_mem_fusion (hP : J.P.Simple) {S₁ S₂ : Set ztf}
    (hS₁ : S₁ ⊆ augChords J.left) (hS₂ : S₂ ⊆ augChords J.right) {c : Set Point}
    (hc : c ∈ S₁ ∪ S₂) :
    (lend c ≠ J.shared → ∃ d ∈ J.fusion S₁ S₂, lend c ∈ d ∧ d ⊆ c) ∧
      (rend c ≠ J.shared → ∃ d ∈ J.fusion S₁ S₂, rend c ∈ d ∧ d ⊆ c) := by
  have hc' : c ∈ augChords J.left ∪ augChords J.right := by
    grind
  refine ⟨fun hne => ⟨_, Or.inl (Or.inl ⟨c, hc, ?_, rfl⟩), Geometry.left_mem_segment _ _,
    J.shoot_lend_subset hc'⟩, fun hne => ⟨_, Or.inl (Or.inr ⟨c, hc, ?_, rfl⟩),
    Geometry.left_mem_segment _ _, J.shoot_rend_subset hc'⟩⟩
  · zunk
    · exact J.lend_freeAt_left hP ztmkw hne
    · exact J.lend_freeAt_right hP ztbac hne
  · zunk
    · exact J.rend_freeAt_left hP ztmkw hne
    · exact J.rend_freeAt_right hP ztbac hne

/-! ### Chords of the fusion between two points of one side -/

/-! ### Local shooting: the current region -/

/-! ### Vertex truncations -/

/-! ### The overlay and the boundary of the regions of the fusion -/

/-! ### The overlay as a chord system; the fusion as its contraction -/
end Junction
end
end Chazelle.Merge
section
set_option hygiene false
local macro "zqbbn" : tactic => `(tactic| (ext c
                                           simp only [exitsIn, mem_insert_iff, mem_ofPred_eq]))
local macro "zqbbo" : tactic => `(tactic| obtain ⟨ho, hoU, hco⟩ := hother c hc)
set_option hygiene true

/-!
# Conformality restoration (Chazelle §3.2, Lemmas 3.3 and 3.4), Euclidean part

Chazelle makes the fusion `S` of two submaps conformal (p. 511–512): "For any region with more than
four arcs, let us apply Lemma 3.2 to every pair of nonconsecutive arcs until we find a chord which
we can add to `S`.  We iterate on this process until no region has more than four arcs. …
Lemma 3.3 tells us that this chord addition process will not stop until `S` becomes conformal."

> **Lemma 3.3.** *Let `A₁, …, A_k` be the clockwise circular sequence of arcs around a region of
> `S`.  If `k > 4`, then there exist `i, j` such that (i) `i − j ≠ −1, 0, 1 (mod k)` and (ii) `A_i`
> has a vertex of `∂C` that sees `A_j`.*

The paper's proof ("try all possible cases with five nodes of degree 1") works in the visibility
tree, whose nodes have degree `≤ 4` "since no two distinct vertices of `C` have the same
y-coordinate".  This file proves the Euclidean content for an arbitrary finite chord system
`ChordSystem D F` on a connected domain (the *full map* `F`: the vertex chords `C.chords`, or an
augmented map such as `C.chords ∪ S₀` for an augmented submap `S₀ ⊆ augChords C`), with chain
instances at the end.

## Exit chords and degrees

`exitsIn D W U` is the set of chords of `W` touching `U`.  For a region `R` of a submap `S`,
`exitsIn D S R` is the set of exit chords of `R`, and
`ncard_neighborSet_eq_exits`: **the degree of `R` in the tree of `S` is its number of exit
chords** (distinct chords give distinct dual edges, `edgeOfIn_injOn`).  Hence
`chain_isConformal_iff`: `C.IsConformal S ↔ ∀ R, |exits R| ≤ 4`.

The one-chord bookkeeping is `IsSplit` (the data of `ChordSystem.regionsIn_insert`): adding
`e ∈ F \ S` inside the region `R` of `S` replaces `R` by `R₁, R₂`; the exit chords of `R` are
shared out between `R₁` and `R₂` (`IsSplit.exits_eq_union`, `IsSplit.ncard_exits`), both get `e`
in addition (`exits_insert₁/₂`), and every other region keeps its exit chords (`exits_other`).

## Lemma 3.3 (`lemma_3_3`)

*If every region of the full map `F` inside the region `R` of `S ⊆ F` has at most `Δ` exit
chords, and `R` has more than `Δ` exit chords in `S`, then some chord `e ∈ F \ S` lies inside `R`
and separates the exit chords of `R` into two groups of at least two* (each of the two regions of
`insert e S` inside `R` is touched by `≥ 2` exit chords of `R`).

The proof is an induction on the number of chords of `F` inside `R` (`splitStatement`), counting
only a subset `W ⊆ S` of the exit chords: if `R` contains no chord of `F` it is a region of `F`
(`mem_regionsIn_of_interiorChords_eq_empty`) and has at most `Δ` exit chords; otherwise a chord
`e` inside `R` either already works or cuts off a part `R₁` with at most one counted exit chord,
and one recurses into `R₂`, counting `e` iff it replaces that exit chord
(`splitStatement_aux`).  This is the "sink" argument of the paper's tree picture: a subtree of a
tree of maximal degree `Δ` with more than `Δ` boundary edges has an internal edge with at least two
boundary edges on each side.

**Arcs versus exit chords.**  The boundary of a region alternates exit chords and arcs (Lemma 2.2;
the arc structure `Chazelle.Chain.ArcLink` is not related to the exit chords in the project), so
"`e` joins two nonconsecutive arcs of `R`" is the statement that `e` separates the exit chords of
`R` into two groups of at least two, which is what is proved; "`k > 4` arcs" is replaced by "more
than `Δ` exit chords".

**Degeneracies: the correct version.**  The paper's degree bound `Δ = 4` for the full map needs
distinct heights.  In the project's exact model (no perturbation, chords are point sets, so
collinear vertex chords that coincide count once) the bound fails: for a chain with `k` downward
spikes whose tips (local minima) lie on one horizontal line, the chords between consecutive tips
are `k - 1` distinct chords all bounding the region just below the tips, and that region of the
full map contains no chord at all.  So the paper's Lemma 3.3 is **false** in the exact model for a
submap equal to the full map, and no tie-break on chords can help (the region has no interior
chord to add).  The correct statement is the one above with the *local* hypothesis
`∀ U ∈ regions F, U ⊆ R → |exits_F U| ≤ Δ`; in general position (distinct heights of the vertices
of `C`) the full vertex map satisfies it with `Δ = 4` (p. 495; this geometric fact is not proved
here, `chain_lemma_3_3` takes `C.IsConformal F` as a hypothesis).

## Lemma 3.4 (`lemma_3_4`, `lemma_3_4_regions`, `chain_lemma_3_4`)

A *restoration step* `ConfStep D F Δ S S'` adds to `S` a chord given by Lemma 3.3 in a region with
more than `Δ` exit chords.  The *excess* `potential D Δ S = Σ_R (|exits R| - Δ)` drops by at least
one at each step when `Δ ≥ 3` (`potential_confStep`: a region with `d > Δ` exit chords is replaced
by two with `d₁ + 1, d₂ + 1` exit chords, `d₁ + d₂ = d`, `d₁, d₂ ≥ 2`), vanishes exactly on
submaps whose regions have at most `Δ` exit chords (`potential_eq_zero_iff`), and is at most
`2 |S|` (`potential_le`).  Hence:

* `confStep_run`: every run of `k` restoration steps from `S` has `k ≤ potential S ≤ 2 |S|`;
* `lemma_3_4`: if the regions of `F` have at most `Δ ≥ 3` exit chords, restoration steps from any
  `S ⊆ F` reach a submap `T ⊇ S` all of whose regions have at most `Δ` exit chords, after adding
  at most `2 |S| = 2 (#regions(S) − 1)` chords (`K = 2`);
* `chain_lemma_3_4`: for a finite `F ⊆ augChords C` with `C.IsConformal F`, every `S ⊆ F` extends
  to a conformal `T ⊆ F` with `|T \ S| ≤ 2 |S|`.

The algorithmic parts (Lemma 3.2 to *find* the chord, costs) are not in this file.
-/
namespace Chazelle.Merge
@[expose] public section
open Set
open Chazelle.Chain (ChordSystem freeIn regionsIn mem_regionsIn TouchesIn DualAdjIn dualTreeIn
  dualGraphIn edgeOfIn regionsIn_subset regionsIn_nonempty regionsIn_eq_component
  regionsIn_disjoint_of_ne regionsIn_eq_or_disjoint regionsIn_empty freeIn_anti
  regionsIn_eq_of_subset subset_regionsIn_of_inter regionsIn_isPreconnected)
variable {D : Set Point} {F : Set (Set Point)}

/-! ### Exit chords -/

/-- The *exit chords* of a set `U` (typically a region) among a family `W` of chords: the chords
of `W` touching `U`.  For a region `R` of a submap `S`, `exitsIn D S R` is the set of exit chords
of `R` (p. 493), and its cardinality is the degree of `R` in the tree of the submap
(`ncard_neighborSet_eq_exits`). -/
def exitsIn (D : Set Point) (W : Set ztf) (U : Set Point) : Set ztf :=
  {c | c ∈ W ∧ TouchesIn D c U}
theorem exitsIn_mono {W W' : Set ztf} (h : W ⊆ W') (U : Set Point) :
    exitsIn D W U ⊆ exitsIn D W' U := fun _ hc => ⟨h hc.1, hc.2⟩
theorem exitsIn_subset (W : Set ztf) (U : Set Point) : exitsIn D W U ⊆ W :=
  fun _ hc => hc.1
theorem exitsIn_finite (hF : ChordSystem D F) {W : Set ztf} (hW : W ⊆ F)
    (U : Set Point) : (exitsIn D W U).Finite :=
  (hF.finite.subset hW).subset (exitsIn_subset W U)

/-- The chords of `F` not in `S` whose open part lies in `R`: the chords of the full map in the
interior of the region `R`. -/
def interiorChords (D : Set Point) (F S : Set ztf) (R : Set Point) : Set ztf :=
  {e | e ∈ F ∧ e ∉ S ∧ e ∩ D ⊆ R}

/-! ### Splitting a region by one chord -/

/-- The data of `ChordSystem.regionsIn_insert`: adding the chord `e ∉ S` whose open part lies in
the region `R` of `S` splits `R` into the two regions `R₁ ≠ R₂` of `insert e S`, and leaves the
other regions unchanged. -/
structure IsSplit (D : Set Point) (S : Set ztf) (e R R₁ R₂ : Set Point) : Prop where
  mem : R ∈ regionsIn D S
  sub : e ∩ D ⊆ R
  ne : R₁ ≠ R₂
  union : R₁ ∪ R₂ = R \ e
  mem₁ : R₁ ∈ regionsIn D ztrc
  mem₂ : R₂ ∈ regionsIn D ztrc
  eq : regionsIn D ztrc = ztdie ∪ {R₁, R₂}

/-- The open part of a chord of `F` not in `S` lies in a region of `S`. -/
theorem exists_region_of_chord (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F)
    {e : Set Point} (he : e ∈ F) (heS : e ∉ S) : ∃ R ∈ regionsIn D S, e ∩ D ⊆ R := by
  obtain ⟨R, hR, heR, -⟩ := hF.regionsIn_insert hS he heS
  grind

/-- Every chord of `F \ S` inside a region `R` of `S` splits it. -/
theorem exists_split (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F)
    {e : Set Point} (he : e ∈ F) (heS : e ∉ S) {R : Set Point} (hR : R ∈ regionsIn D S)
    (heR : e ∩ D ⊆ R) : ∃ R₁ R₂ : Set Point, IsSplit D S e R R₁ R₂ := by
  obtain ⟨R', hR', heR', R₁, R₂, hne, hunion, h1, h2, heq⟩ := hF.regionsIn_insert hS he heS
  have hRR' :=
    regionsIn_eq_of_subset hR hR' (hF.chord_inter_nonempty_isPreconnected he).1 heR heR'
  subst hRR'
  exact ⟨R₁, R₂, ⟨hR, heR, hne, hunion, h1, h2, heq⟩⟩
namespace IsSplit
variable {S : Set (Set Point)} {e R R₁ R₂ : Set Point}
theorem symm (h : IsSplit D S e R R₁ R₂) : IsSplit D S e R R₂ R₁ :=
  ⟨h.mem, h.sub, h.ne.symm, by rw [union_comm, h.union], h.mem₂, h.mem₁,
    by rw [h.eq, pair_comm]⟩
theorem sub₁ (h : IsSplit D S e R R₁ R₂) : R₁ ⊆ R := fun p hp => by
  zubtb
  rw [h.union] at this
  simp_all
theorem sub₂ (h : IsSplit D S e R R₁ R₂) : R₂ ⊆ R := h.symm.sub₁

/-- The regions of `insert e S`: the old regions other than `R`, and `R₁`, `R₂`. -/
theorem mem_cases (h : IsSplit D S e R R₁ R₂) {P : Set Point}
    (hP : P ∈ regionsIn D ztrc) :
    (P ∈ regionsIn D S ∧ P ≠ R) ∨ P = R₁ ∨ P = R₂ := by
  rw [h.eq] at hP
  grind

/-- An old region other than `R` is disjoint from `R`. -/
theorem disjoint_of_ne (h : IsSplit D S e R R₁ R₂) {P : Set Point} (hP : P ∈ regionsIn D S)
    (hPR : P ≠ R) : Disjoint P R :=
  regionsIn_disjoint_of_ne hP h.mem hPR

/-- The regions of `insert e S` inside `R` are `R₁` and `R₂`. -/
theorem eq_of_subset (h : IsSplit D S e R R₁ R₂) {P : Set Point}
    (hP : P ∈ regionsIn D ztrc) (hPR : P ⊆ R) : P = R₁ ∨ P = R₂ := by
  rcases h.mem_cases hP with ⟨h1, h2⟩ | h3
  · zuhhx
    exact absurd (hPR hp) ((h.disjoint_of_ne h1 h2).notMem_of_mem_left hp)
  omega

/-- An old region other than `R` is a region of `insert e S`. -/
theorem mem_of_ne (h : IsSplit D S e R R₁ R₂) {P : Set Point} (hP : P ∈ regionsIn D S)
    (hPR : P ≠ R) : P ∈ regionsIn D ztrc := by
  rw [h.eq]
  simp_all

/-- `e` does not touch the old regions other than `R`. -/
theorem not_touches (hF : ChordSystem D F) (hS : S ⊆ F) (h : IsSplit D S e R R₁ R₂)
    {P : Set Point} (hP : P ∈ regionsIn D S) (hPR : P ≠ R) : ¬ TouchesIn D e P := by
  rintro ⟨z, hz, hzP⟩
  have hdisj : Disjoint _ R :=
    (h.disjoint_of_ne hP hPR).closure_left (hF.regionsIn_open hS h.mem)
  exact hdisj.notMem_of_mem_left hzP (h.sub hz)

/-- `R₁ ≠ R` (and it is not an old region). -/
theorem ne_of_mem_old (h : IsSplit D S e R R₁ R₂) {P : Set Point} (hP : P ∈ regionsIn D S)
    (hPR : P ≠ R) : P ≠ R₁ := by
  zunq
  zuhhx
  exact (h.disjoint_of_ne hP hPR).notMem_of_mem_left hp (h.sub₁ hp)

/-- The new chord touches exactly the two new regions. -/
theorem touches_iff (hF : ChordSystem D F) (hS : S ⊆ F) (he : e ∈ F) (heS : e ∉ S)
    (h : IsSplit D S e R R₁ R₂) :
    ∀ W ∈ regionsIn D ztrc, TouchesIn D e W ↔ W = R₁ ∨ W = R₂ :=
  hF.touches_iff_of_split hS he heS h.mem h.sub h.union h.mem₁ h.mem₂ h.eq
theorem touches₁ (hF : ChordSystem D F) (hS : S ⊆ F) (he : e ∈ F) (heS : e ∉ S)
    (h : IsSplit D S e R R₁ R₂) : TouchesIn D e R₁ :=
  (h.touches_iff hF hS he heS R₁ h.mem₁).2 ztp
theorem touches₂ (hF : ChordSystem D F) (hS : S ⊆ F) (he : e ∈ F) (heS : e ∉ S)
    (h : IsSplit D S e R R₁ R₂) : TouchesIn D e R₂ :=
  (h.touches_iff hF hS he heS R₂ h.mem₂).2 ztbt

/-- **The exit chords of `R` are shared out between `R₁` and `R₂`**: for `W ⊆ S`, a chord of
`W` touches `R` iff it touches `R₁` or `R₂`, and it cannot touch both. -/
theorem exits_eq_union (hF : ChordSystem D F) (hS : S ⊆ F) (he : e ∈ F) (heS : e ∉ S)
    (h : IsSplit D S e R R₁ R₂) {W : Set ztf} (hW : W ⊆ S) :
    exitsIn D W R = exitsIn D W R₁ ∪ exitsIn D W R₂ := by
  zubcj
  constructor
  · rintro ⟨hcW, hcR⟩
    have hce : e ≠ c := by_grind
    rcases hF.touches_split_or he by_grind hce h.union hcR with h1 | h2
    · tauto
    tauto
  · rintro (⟨hcW, h1⟩ | ⟨hcW, h2⟩)
    · exact ⟨hcW, Chazelle.Merge.touchesIn_mono h1 h.sub₁⟩
    · exact ⟨hcW, Chazelle.Merge.touchesIn_mono h2 h.sub₂⟩
theorem exits_disjoint (hF : ChordSystem D F) (hS : S ⊆ F) (he : e ∈ F)
    (h : IsSplit D S e R R₁ R₂) {W : Set ztf} (hW : W ⊆ S) :
    Disjoint (exitsIn D W R₁) (exitsIn D W R₂) := by
  refine Set.disjoint_left.2 fun c hc1 hc2 => ?_
  obtain ⟨hcW, h1⟩ := hc1
  obtain ⟨-, h2⟩ := hc2
  have hcS := hW hcW
  -- `c` touches a region `Z ≠ R` of `S`
  obtain ⟨Z₁, Z₂, hZne, hZ₁, hZ₂, htZ, -⟩ := regionsIn_erase hF hS hcS
  have hZ : ∃ Z ∈ regionsIn D S, Z ≠ R ∧ TouchesIn D c Z := by
    grind
  obtain ⟨Z, hZ, hZR, hcZ⟩ := hZ
  zukai
  obtain ⟨Y₁, Y₂, -, -, -, htY, -⟩ := regionsIn_erase hF hS' (mem_insert_of_mem e hcS)
  have e1 := (htY R₁ h.mem₁).1 h1
  have e2 := (htY R₂ h.mem₂).1 h2
  have e3 := (htY Z (h.mem_of_ne hZ hZR)).1 hcZ
  have n1 := h.ne_of_mem_old hZ hZR
  have n2 := h.symm.ne_of_mem_old hZ hZR
  have hne := h.ne
  grind

/-- **Counting form**: `|exits_W R| = |exits_W R₁| + |exits_W R₂|` for `W ⊆ S`. -/
theorem ncard_exits (hF : ChordSystem D F) (hS : S ⊆ F) (he : e ∈ F) (heS : e ∉ S)
    (h : IsSplit D S e R R₁ R₂) {W : Set ztf} (hW : W ⊆ S) :
    (exitsIn D W R).ncard = (exitsIn D W R₁).ncard + (exitsIn D W R₂).ncard := by
  rw [h.exits_eq_union hF hS he heS hW]
  exact ncard_union_eq (h.exits_disjoint hF hS he hW) zthgp
    zthgp

/-- The exit chords of `R₁` in `insert e S` are those in `S` and `e`. -/
theorem exits_insert₁ (hF : ChordSystem D F) (hS : S ⊆ F) (he : e ∈ F) (heS : e ∉ S)
    (h : IsSplit D S e R R₁ R₂) :
    (exitsIn D ztrc R₁).ncard = (exitsIn D S R₁).ncard + 1 := by
  have : exitsIn D ztrc R₁ = insert e (exitsIn D S R₁) := by
    zqbbn
    constructor
    · simp_all
    · rintro (rfl | ⟨hc, ht⟩)
      · exact ⟨Or.inl rfl, h.touches₁ hF hS he heS⟩
      simp_all
  rw [this, ncard_insert_of_notMem (fun h' => heS h'.1) (exitsIn_finite hF hS _)]
theorem exits_insert₂ (hF : ChordSystem D F) (hS : S ⊆ F) (he : e ∈ F) (heS : e ∉ S)
    (h : IsSplit D S e R R₁ R₂) :
    (exitsIn D ztrc R₂).ncard = (exitsIn D S R₂).ncard + 1 :=
  h.symm.exits_insert₁ hF hS he heS

/-- The other regions keep their exit chords. -/
theorem exits_other (hF : ChordSystem D F) (hS : S ⊆ F) (h : IsSplit D S e R R₁ R₂)
    {P : Set Point} (hP : P ∈ regionsIn D S) (hPR : P ≠ R) :
    exitsIn D ztrc P = exitsIn D S P := by
  zqbbn
  constructor
  · rintro ⟨rfl | hc, ht⟩
    · exact absurd ht (h.not_touches hF hS hP hPR)
    simp_all
  simp_all
end IsSplit

/-! ### Exit chords under insertion of a chord -/
variable {W : Set (Set Point)}
theorem exitsIn_insert_of_touches {e U : Set Point}
    (h : TouchesIn D e U) : exitsIn D zttpl U = insert e (exitsIn D W U) := by
  zqbbn
  grind
theorem exitsIn_insert_of_not_touches {e U : Set Point}
    (h : ¬ TouchesIn D e U) : exitsIn D zttpl U = exitsIn D W U := by
  zqbbn
  grind

/-! ### Lemma 3.3: a region with many exit chords contains a splitting chord -/

/-- **A region of `S` containing no chord of the full map is a region of the full map.** -/
theorem mem_regionsIn_of_interiorChords_eq_empty (hF : ChordSystem D F) {S : Set ztf}
    (hS : S ⊆ F) {R : Set Point} (hR : R ∈ regionsIn D S)
    (h : interiorChords D F S R = ∅) : R ∈ regionsIn D F := by
  obtain ⟨p, hp⟩ := regionsIn_nonempty hR
  have hRF : R ⊆ freeIn D F := by
    zuco
    have hqS := regionsIn_subset hR hq
    refine ⟨hqS.1, ?_⟩
    rintro ⟨e, he, hqe⟩
    have heS : ztsii := fun heS => hqS.2 by_grind
    have hsub :=
      subset_regionsIn_of_inter hR (hF.chord_inter_nonempty_isPreconnected he).2
        (hF.chord_inter_subset_freeIn hS he heS) ⟨q, ⟨hqe, hqS.1⟩, hq⟩
    have hmem : ztpom := ⟨he, heS, hsub⟩
    simp_all
  have heq : R = connectedComponentIn ztfrg p := by
    zugjb
    · exact (regionsIn_isPreconnected hR).subset_connectedComponentIn hp hRF
    · rw [regionsIn_eq_component hR hp]
      exact connectedComponentIn_mono p (freeIn_anti D hS)
  zudab
  exact mem_regionsIn (hRF hp)

/-- If a region `R` of `S` contains no chord of the full map, its exit chords are bounded by the
maximal number `Δ` of exit chords of a region of the full map. -/
theorem exits_le_of_interiorChords_eq_empty (hF : ChordSystem D F) {S W : Set ztf}
    (hS : S ⊆ F) (hW : W ⊆ S) {R : Set Point} (hR : R ∈ regionsIn D S)
    (h : interiorChords D F S R = ∅) {Δ : ℕ}
    (hΔ : ∀ U ∈ regionsIn D F, U ⊆ R → (exitsIn D F U).ncard ≤ Δ) :
    (exitsIn D W R).ncard ≤ Δ :=
  (ncard_le_ncard (exitsIn_mono ztqpt R) (exitsIn_finite hF subset_rfl R)).trans
    (hΔ R (mem_regionsIn_of_interiorChords_eq_empty hF hS hR h) subset_rfl)
theorem interiorChords_finite (hF : ChordSystem D F) (S : Set ztf) (R : Set Point) :
    (interiorChords D F S R).Finite :=
  hF.finite.subset fun _ h => h.1

/-- The statement proved by induction for Lemma 3.3 (with a set `W ⊆ S` of *counted* exit
chords). -/
def SplitStatement (D : Set Point) (F : Set ztf) (Δ n : ℕ) : Prop :=
  ∀ (S W : Set ztf) (R : Set Point), S ⊆ F → W ⊆ S → R ∈ regionsIn D S →
    (interiorChords D F S R).ncard ≤ n →
    (∀ U ∈ regionsIn D F, U ⊆ R → (exitsIn D F U).ncard ≤ Δ) →
    Δ < (exitsIn D W R).ncard →
    ∃ f ∈ F, f ∉ S ∧ f ∩ D ⊆ R ∧
      ∀ P ∈ regionsIn D ztobp, P ⊆ R → 2 ≤ (exitsIn D W P).ncard

/-- The inductive step of Lemma 3.3 when the chord `e` cuts off at most one counted exit chord
(`|exits_W R₁| ≤ 1`): recurse into `R₂`, counting `e` as an exit chord iff it replaces one. -/
theorem splitStatement_aux (hF : ChordSystem D F) {Δ n : ℕ} (ih : SplitStatement D F Δ n)
    {S W : Set ztf} {e R R₁ R₂ : Set Point} (hS : S ⊆ F) (hW : W ⊆ S) (he : e ∈ F)
    (heS : e ∉ S) (h : IsSplit D S e R R₁ R₂)
    (hn : (interiorChords D F S R).ncard ≤ n + 1)
    (hΔ : ∀ U ∈ regionsIn D F, U ⊆ R → (exitsIn D F U).ncard ≤ Δ)
    (hdeg : Δ < (exitsIn D W R).ncard) (ha : (exitsIn D W R₁).ncard ≤ 1) :
    ∃ f ∈ F, f ∉ S ∧ f ∩ D ⊆ R ∧
      ∀ P ∈ regionsIn D ztobp, P ⊆ R → 2 ≤ (exitsIn D W P).ncard := by
  classical
  zukai
  have heW : e ∉ W := by_grind
  set a₁ := (exitsIn D W R₁).ncard with ha₁
  set W' : Set _ := if a₁ = 1 then insert e W else W with hW'def
  have hW'2 : W' ⊆ insert e W := by
    grind
  have hW'3 : W' ⊆ insert e S := by_grind
  -- the counted exit chords of `R₂` now include `e` iff `a₁ = 1`
  have hcount : (exitsIn D W' R₂).ncard = a₁ + (exitsIn D W R₂).ncard := by
    zujsn
    · zulgt
      rw [this, exitsIn_insert_of_touches (h.touches₂ hF hS he heS),
        ncard_insert_of_notMem (fun h' => heW h'.1) zthgp, h1]
      omega
    grind
  -- `W'` counts at most `a₁` more exit chords than `W`, and none more away from `e`
  have hN1 : ∀ Q, ¬ TouchesIn D e Q → (exitsIn D W' Q).ncard ≤ (exitsIn D W Q).ncard := by
    intro Q hQ
    have : exitsIn D W' Q ⊆ exitsIn D W Q := by
      rw [← exitsIn_insert_of_not_touches (W := W) hQ]
      exact exitsIn_mono hW'2 Q
    exact ncard_le_ncard this (exitsIn_finite hF ztqpt Q)
  have hN2 : ∀ Q, (exitsIn D W' Q).ncard ≤ (exitsIn D W Q).ncard + a₁ := by
    intro Q
    zujsn
    · zulgt
      rw [this, h1]
      calc (exitsIn D _ Q).ncard ≤ (insert e (exitsIn D W Q)).ncard := by
            refine ncard_le_ncard ?_ ((exitsIn_finite hF ztqpt Q).insert e)
            rintro c ⟨hc | hc, ht⟩
            · simp_all
            tauto
        _ ≤ (exitsIn D W Q).ncard + 1 := ncard_insert_le _ _
    simp_all
  -- the recursion into `R₂`
  have hint : (interiorChords D F ztrc R₂).ncard ≤ n := by
    have hsub : interiorChords D F ztrc R₂ ⊆ interiorChords D F S R \ {e} := by
      rintro f ⟨hf, hfS, hfR⟩
      exact ⟨⟨hf, by_simp_all, hfR.trans h.sub₂⟩,
        by simp_all⟩
    have hmem : ztpom := ⟨he, heS, h.sub⟩
    have h1 := ncard_le_ncard hsub ((interiorChords_finite hF S R).sdiff)
    have h2 := ncard_sdiff_singleton_add_one hmem ztrsj
    omega
  have hΔ' : ∀ U ∈ regionsIn D F, U ⊆ R₂ → (exitsIn D F U).ncard ≤ Δ :=
    fun U hU hUR => hΔ U hU (hUR.trans h.sub₂)
  have hdeg' : Δ < (exitsIn D W' R₂).ncard := by
    rw [hcount, ha₁, ← h.ncard_exits hF hS he heS hW]
    omega
  obtain ⟨f, hf, hfS', hfR₂, hQ⟩ := ih _ W' R₂ hS' hW'3 h.mem₂ hint hΔ' hdeg'
  have hfS : f ∉ S := by_grind
  have hfe : f ≠ e := by_grind
  refine ⟨f, hf, hfS, hfR₂.trans h.sub₂, ?_⟩
  zujas
  obtain ⟨Q₁, Q₂, hQs⟩ := exists_split hF hS' hf hfS' h.mem₂ hfR₂
  -- the regions of `insert f (insert e S)` inside `R` other than `R₁` lie in `R₂`
  have hK : ∀ Q ∈ regionsIn D ztxxl, Q ⊆ R → Q ≠ R₁ → Q ⊆ R₂ := by
    intro Q hQ hQR hQ1
    rcases hQs.mem_cases hQ with ⟨hQ', hQ2⟩ | rfl | rfl
    · rcases h.mem_cases hQ' with ⟨hQ'', hQR'⟩ | rfl | rfl
      · obtain ⟨p, hp⟩ := regionsIn_nonempty hQ
        exact absurd (hQR hp) ((h.disjoint_of_ne hQ'' hQR').notMem_of_mem_left hp)
      · grind
      simp
    · exact hQs.sub₁
    · exact hQs.sub₂
  have hR₁mem : R₁ ∈ regionsIn D _ := hQs.mem_of_ne h.mem₁ h.ne
  have hT : insert f S ⊆ F := by_grind
  have heT : e ∉ insert f S := by
    grind
  have hswap : insert e _ = insert f _ := insert_comm e f S
  have htR₁ : TouchesIn D e R₁ := h.touches₁ hF hS he heS
  obtain ⟨P₀, hP₀, heP₀⟩ := exists_region_of_chord hF hT he heT
  obtain ⟨P₁, P₂, hPs⟩ := exists_split hF hT he heT hP₀ heP₀
  by_cases hPP : P = P₀
  · subst hPP
    have hW_T : W ⊆ insert f S := by_grind
    rw [hPs.ncard_exits hF hT he heT hW_T]
    have hP₁mem : P₁ ∈ regionsIn D ztxxl := by zunxf; exact hPs.mem₁
    have hP₂mem : P₂ ∈ regionsIn D ztxxl := by zunxf; exact hPs.mem₂
    have hR₁' : R₁ ∈ regionsIn D (insert e ztobp) := by_grind
    rcases (hPs.touches_iff hF hT he heT R₁ hR₁').1 htR₁ with h1 | h1
    · have hP₂R₂ := hK P₂ hP₂mem (hPs.sub₂.trans hPR)
        (fun h' => hPs.ne (h1.symm.trans h'.symm))
      grind
    · have hP₁R₂ := hK P₁ hP₁mem (hPs.sub₁.trans hPR)
        (fun h' => hPs.ne (h'.trans h1))
      grind
  · have hPe := hPs.not_touches hF hT hP hPP
    have hPmem : P ∈ regionsIn D ztxxl := by
      zunxf; exact hPs.mem_of_ne hP hPP
    grind

/-- **Lemma 3.3, induction.** -/
theorem splitStatement (hF : ChordSystem D F) (Δ : ℕ) : ∀ n, SplitStatement D F Δ n := by
  zugok
  induction n with
  | zero =>
    zugoa
    have hempty : interiorChords D F S R = ∅ :=
      (ncard_eq_zero ztrsj).1 (Nat.le_zero.1 hn)
    zulxu
  | succ n ih =>
    zugoa
    by_cases hempty : interiorChords D F S R = ∅
    · zulxu
    obtain ⟨e, he, heS, heR⟩ := nonempty_iff_ne_empty.2 hempty
    obtain ⟨R₁, R₂, h⟩ := exists_split hF hS he heS hR heR
    by_cases ha₁ : (exitsIn D W R₁).ncard ≤ 1
    · exact splitStatement_aux hF ih hS hW he heS h hn hΔ hdeg ha₁
    by_cases ha₂ : (exitsIn D W R₂).ncard ≤ 1
    · exact splitStatement_aux hF ih hS hW he heS h.symm hn hΔ hdeg ha₂
    refine ⟨e, he, heS, heR, fun P hP hPR => ?_⟩
    zugrp

/-- **Lemma 3.3 (Chazelle, p. 511), Euclidean form.**  Let `F` be a finite chord system (the full
map: the vertex chords `C.chords`, or an augmented map `C.chords ∪ S₀`), `S ⊆ F` a submap and
`R` a region of `S`.  Suppose every region of the full map inside `R` has at most `Δ` exit chords
(in general position `Δ = 4`; see the module docstring for degenerate inputs), while `R` has more
than `Δ` exit chords in `S`.  Then some chord `e` of the full map lies inside `R` (`e ∉ S`, its
open part in `R`) and **separates the exit chords of `R` into two groups of at least two**: each
of the two regions of `insert e S` inside `R` is touched by at least two exit chords of `R`.
(Equivalently, `e` joins two nonconsecutive arcs of `R`.) -/
theorem lemma_3_3 (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F) {Δ : ℕ}
    {R : Set Point} (hR : R ∈ regionsIn D S)
    (hΔ : ∀ U ∈ regionsIn D F, U ⊆ R → (exitsIn D F U).ncard ≤ Δ)
    (hdeg : Δ < (exitsIn D S R).ncard) :
    ∃ e ∈ F, e ∉ S ∧ e ∩ D ⊆ R ∧
      ∀ P ∈ regionsIn D ztrc, P ⊆ R → 2 ≤ (exitsIn D S P).ncard :=
  splitStatement hF Δ _ S S R hS subset_rfl hR le_rfl hΔ hdeg

/-! ### The degree of a region is its number of exit chords -/

/-- The edge of the dual tree contributed by a chord of `S` is the pair of the two regions it
touches. -/
theorem edgeOfIn_eq (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F) {c : Set Point}
    (hc : c ∈ S) {U V : Set Point} (hU : U ∈ regionsIn D S) (hV : V ∈ regionsIn D S)
    (hne : U ≠ V) (hcU : TouchesIn D c U) (hcV : TouchesIn D c V) :
    edgeOfIn D S c = s(U, V) := by
  zuegf

/-- **Distinct chords give distinct edges of the dual tree** (the dual graph has no multiple
edges: it is a tree with exactly `|S|` edges). -/
theorem edgeOfIn_injOn (hF : ChordSystem D F) (hD : IsPreconnected D) (hne : D.Nonempty)
    {S : Set ztf} (hS : S ⊆ F) : InjOn (edgeOfIn D S) S := by
  zubwj
  have hsub := hF.dualGraph_edgeSet_subset hS
  have hEfin := (hfin.image _).subset hsub
  have  := hEfin.to_subtype
  have h1 : Nat.card (dualTreeIn D S).edgeSet ≤ Nat.card (dualGraphIn D S).edgeSet :=
    Nat.card_le_card_of_injective _
      (SimpleGraph.Embedding.mapEdgeSet ztvdg).injective
  have h2 := hF.dualTree_card_edgeSet hD hne hS
  simp only [Nat.card_coe_set_eq] at h1 h2
  have h3 :=
    ncard_le_ncard hsub ztjxu
  have h4 : (edgeOfIn D S '' S).ncard ≤ S.ncard := ncard_image_le hfin
  exact injOn_of_ncard_image_eq by_omega hfin

/-- The neighbours of a region `U` in the dual graph of `S`. -/
def neighborsIn (D : Set Point) (S : Set ztf) (U : Set Point) : Set ztf :=
  {X | DualAdjIn D S U X}

/-- **The degree of a region in the tree of a submap is its number of exit chords.** -/
theorem ncard_neighborsIn_eq_exits (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set ztf} (hS : S ⊆ F) {U : Set Point}
    (hU : U ∈ regionsIn D S) : (neighborsIn D S U).ncard = (exitsIn D S U).ncard := by
  classical
  have hfinR := hF.regionsIn_finite hD hne hS
  have hNfin : (neighborsIn D S U).Finite := hfinR.subset fun X hX => hX.2.1
  -- the region on the other side of an exit chord
  let other : Set Point → Set Point := fun c =>
    if h : ∃ X ∈ regionsIn D S, X ≠ U ∧ TouchesIn D c X then Classical.choose h else ∅
  have hother : ∀ c ∈ exitsIn D S U, other c ∈ regionsIn D S ∧ other c ≠ U ∧
      TouchesIn D c (other c) := by
    rintro c ⟨hc, hcU⟩
    have hex : ∃ X ∈ regionsIn D S, X ≠ U ∧ TouchesIn D c X := by
      obtain ⟨Z₁, Z₂, hZne, hZ₁, hZ₂, htZ, -⟩ := regionsIn_erase hF hS hc
      grind
    grind
  -- the other region is the unique region `≠ U` touched by the chord
  have huniq : ∀ c ∈ exitsIn D S U, ∀ X ∈ regionsIn D S, X ≠ U → TouchesIn D c X →
      other c = X := by
    intro c hc X hX hXU hcX
    zqbbo
    obtain ⟨Z₁, Z₂, -, -, -, htZ, -⟩ := regionsIn_erase hF hS hc.1
    rcases (htZ _ ho).1 hco with e1 | e1 <;> rcases (htZ _ hX).1 hcX with e2 | e2 <;>
      rcases (htZ _ hU).1 hc.2 with e3 | e3
    all_goals first
      | exact e1.trans e2.symm
      | exact by_simp_all
      | exact by_simp_all
  zudmc
  · -- every neighbour is the other region of an exit chord
    have hsub : neighborsIn D S U ⊆ other '' exitsIn D S U := by
      rintro X ⟨-, hX, hUX, c, hc, hcU, hcX⟩
      exact ⟨c, ztuhi, huniq c ztuhi X hX hUX.symm hcX⟩
    exact (ncard_le_ncard hsub ((exitsIn_finite hF hS U).image _)).trans
      (ncard_image_le (exitsIn_finite hF hS U))
  · refine ncard_le_ncard_of_injOn other ?_ ?_ hNfin
    · zung
      zqbbo
      exact ⟨hU, ho, hoU.symm, c, hc.1, hc.2, hco⟩
    · zukja
      zqbbo
      obtain ⟨-, -, hco'⟩ := hother c' hc'
      rw [← hcc] at hco'
      have e1 := edgeOfIn_eq hF hS hc.1 hU ho hoU.symm hc.2 hco
      have e2 := edgeOfIn_eq hF hS hc'.1 hU ho hoU.symm hc'.2 hco'
      exact edgeOfIn_injOn hF hD hne hS hc.1 hc'.1 ztqmh

/-- **Degree = number of exit chords**, for the dual tree on the regions of `S`. -/
theorem ncard_neighborSet_eq_exits (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set ztf} (hS : S ⊆ F) (U : regionsIn D S) :
    ((dualTreeIn D S).neighborSet U).ncard = (exitsIn D S U).ncard := by
  rw [← ncard_neighborsIn_eq_exits hF hD hne hS U.2,
    ← ncard_image_of_injective _ Subtype.val_injective]
  zucr
  ext X
  constructor
  · rintro ⟨V, hV, rfl⟩
    exact hV
  · intro hX
    exact ⟨⟨X, hX.2.1⟩, hX, rfl⟩

/-! ### Lemma 3.4: conformality restoration -/

/-- Sums over the regions after inserting a chord: the region `R` is replaced by `R₁`, `R₂`. -/
theorem finsum_regions_insert (hF : ChordSystem D F) (hD : IsPreconnected D) (hne : D.Nonempty)
    {S : Set ztf} (hS : S ⊆ F) {e R R₁ R₂ : Set Point} (h : IsSplit D S e R R₁ R₂)
    (f g : Set Point → ℕ) (hfg : ∀ X ∈ regionsIn D S, X ≠ R → g X = f X) :
    (∑ᶠ X ∈ regionsIn D ztrc, g X) + f R =
      ztkyd + g R₁ + g R₂ := by
  have hfin := hF.regionsIn_finite hD hne hS
  have h1 : regionsIn D S = insert R _ :=
    (insert_sdiff_singleton.trans (insert_eq_of_mem h.mem)).symm
  have hdisj : ztyyb := by
    refine Set.disjoint_left.2 fun X hX hX' => ?_
    simp only [mem_insert_iff, mem_singleton_iff] at hX'
    rcases hX' with rfl | rfl
    · exact h.ne_of_mem_old hX.1 hX.2 rfl
    · exact h.symm.ne_of_mem_old hX.1 hX.2 rfl
  have hsum : (∑ᶠ X ∈ regionsIn D S \ {R}, g X) = ∑ᶠ X ∈ regionsIn D S \ {R}, f X :=
    by grind
  have h2 : ztkyd = f R + ∑ᶠ X ∈ regionsIn D S \ {R}, f X := by
    conv_lhs => rw [h1]
    exact finsum_mem_insert f by_grind hfin.sdiff
  rw [h.eq, finsum_mem_union hdisj hfin.sdiff ztcwq, finsum_mem_pair h.ne, h2, hsum]
  ring

/-- The *excess* of a submap: `Σ_R (|exits R| - Δ)` over its regions (truncated subtraction).
It vanishes iff every region has at most `Δ` exit chords. -/
noncomputable def potential (D : Set Point) (Δ : ℕ) (S : Set ztf) : ℕ :=
  ∑ᶠ R ∈ regionsIn D S, ztlcq

/-- The excess after inserting one chord. -/
theorem potential_insert (hF : ChordSystem D F) (hD : IsPreconnected D) (hne : D.Nonempty)
    {S : Set ztf} (hS : S ⊆ F) {e R R₁ R₂ : Set Point} (he : e ∈ F) (heS : e ∉ S)
    (h : IsSplit D S e R R₁ R₂) (Δ : ℕ) :
    potential D Δ ztrc + ztlcq =
      potential D Δ S + ((exitsIn D S R₁).ncard + 1 - Δ) +
        ((exitsIn D S R₂).ncard + 1 - Δ) := by
  unfold potential
  rw [finsum_regions_insert hF hD hne hS h (fun X => (exitsIn D S X).ncard - Δ)
    (fun X => (exitsIn D _ X).ncard - Δ)
    (fun X hX hXR => by simp only [h.exits_other hF hS hX hXR]),
    h.exits_insert₁ hF hS he heS, h.exits_insert₂ hF hS he heS]
theorem potential_empty (hD : IsPreconnected D) (hne : D.Nonempty) (Δ : ℕ) :
    potential D Δ ∅ = 0 := by
  unfold potential
  rw [regionsIn_empty hD hne, finsum_mem_singleton]
  have : exitsIn D (∅ : Set _) D = ∅ := by
    zubcj
    simp [exitsIn]
  simp_all

/-- **The excess is at most twice the number of chords**: `potential ≤ 2 |S|`. -/
theorem potential_le (hF : ChordSystem D F) (hD : IsPreconnected D) (hne : D.Nonempty)
    {S : Set ztf} (hS : S ⊆ F) (Δ : ℕ) : potential D Δ S ≤ 2 * S.ncard := by
  zubwj
  induction S, hfin using Set.Finite.induction_on with
  | empty => rw [potential_empty hD hne]; exact Nat.zero_le _
  | @insert c S hcS hSfin ih =>
    zuccx

    obtain ⟨R, hR, hcR⟩ := exists_region_of_chord hF hS' hc hcS
    obtain ⟨R₁, R₂, h⟩ := exists_split hF hS' hc hcS hR hcR
    have e1 := potential_insert hF hD hne hS' hc hcS h Δ
    have e2 := h.ncard_exits hF hS' hc hcS ztqxc
    have e3 := ih hS'
    rw [ncard_insert_of_notMem hcS hSfin]
    omega

/-- **One step of conformality restoration** (p. 512): some region `R` of `S` has more than `Δ`
exit chords, and the chord `e` of the full map inside `R` given by Lemma 3.3 is added; `e`
separates the exit chords of `R` into two groups of at least two. -/
def ConfStep (D : Set Point) (F : Set ztf) (Δ : ℕ) (S S' : Set ztf) : Prop :=
  ∃ R ∈ regionsIn D S, Δ < (exitsIn D S R).ncard ∧ ∃ e ∈ F, e ∉ S ∧ e ∩ D ⊆ R ∧
    S' = insert e S ∧ ∀ P ∈ regionsIn D ztrc, P ⊆ R → 2 ≤ (exitsIn D S P).ncard

/-- A restoration step adds exactly one chord of the full map. -/
theorem ConfStep.subset (hF : ChordSystem D F) {Δ : ℕ} {S S' : Set ztf}
    (h : ConfStep D F Δ S S') (hS : S ⊆ F) : S' ⊆ F ∧ S ⊆ S' ∧ S'.ncard = S.ncard + 1 := by
  obtain ⟨-, -, -, e, he, heS, -, rfl, -⟩ := h
  exact ⟨by_grind, by_simp_all,
    ncard_insert_of_notMem heS (hF.finite.subset hS)⟩

/-! ### The chain instances -/
section ChainInstance
variable (C : Chain)
end ChainInstance
end
end Chazelle.Merge
end
namespace Chazelle.Merge
@[expose] public section
open Set
open Chazelle.Chain (ChordSystem regionsIn TouchesIn regionsIn_nonempty regionsIn_eq_of_subset
  exists_regionsIn_superset)
variable {D : Set Point} {F : Set (Set Point)}

/-! ### Removing one chord: bookkeeping -/

/-- Removing `c ∈ S`: the open part of `c` lies in a region `P` of `S \ {c}`, which `c` splits
into the two regions `R₁`, `R₂` of `S` touched by `c`. -/
theorem exists_removal_split (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ S) :
    ∃ P R₁ R₂ : Set Point, IsSplit D ztdb c P R₁ R₂ := by
  zuuu

  obtain ⟨P, hP, hcP⟩ := exists_region_of_chord hF hT ztbkp hcT
  obtain ⟨R₁, R₂, h⟩ := exists_split hF hT ztbkp hcT hP hcP
  grind
theorem insert_sdiff_self {S : Set ztf} {c : Set Point} (hc : c ∈ S) :
    insert c ztdb = S :=
  insert_sdiff_singleton.trans ztjyw

/-- A region of `S` not touched by `c ∈ S` is still a region of `S \ {c}`, with the same exit
chords. -/
theorem mem_sdiff_of_not_touches (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ S) {X : Set Point} (hX : X ∈ regionsIn D S)
    (hcX : ¬ TouchesIn D c X) :
    X ∈ regionsIn D ztdb ∧ exitsIn D ztdb X = exitsIn D S X := by
  zuuu

  obtain ⟨P, R₁, R₂, h⟩ := exists_removal_split hF hS hc
  have hins := insert_sdiff_self hc
  have hX' : X ∈ regionsIn D ztxxk := by_simp_all
  rcases h.mem_cases hX' with ⟨hXT, hXP⟩ | rfl | rfl
  · refine ⟨hXT, ?_⟩
    rw [← h.exits_other hF hT hXT hXP, hins]
  · exact absurd (h.touches₁ hF hT ztbkp hcT) hcX
  · exact absurd (h.touches₂ hF hT ztbkp hcT) hcX

/-! ### Removable chords and granularity -/

/-- The chord `c` is *removable* from `S` (p. 512): it separates two regions `U ≠ V` of `S`, one
of which has fewer than `3` exit chords (the dual edge `UV` is incident upon a node of degree
`< 3`), and the region of `S \ {c}` obtained by merging them has weight at most `γ`. -/
def Removable (D : Set Point) (wt : Set ztf → Set Point → ℕ) (γ : ℕ)
    (S : Set ztf) (c : Set Point) : Prop :=
  c ∈ S ∧ ∃ U ∈ regionsIn D S, ∃ V ∈ regionsIn D S, U ≠ V ∧ TouchesIn D c U ∧ TouchesIn D c V ∧
    ztflu ∧
    ∀ W ∈ regionsIn D ztdb, U ⊆ W → wt ztdb W ≤ γ

/-- Granularity condition (ii) (p. 496), with the degree of a region measured by its number of
exit chords (`ncard_neighborSet_eq_exits`). -/
def ContractionCondIn (D : Set Point) (wt : Set ztf → Set Point → ℕ)
    (S : Set ztf) (γ : ℕ) : Prop :=
  ∀ c ∈ S, ∀ U ∈ regionsIn D S, ∀ V ∈ regionsIn D S, U ≠ V → TouchesIn D c U →
    TouchesIn D c V → ztflu →
    ∀ W ∈ regionsIn D ztdb, U ⊆ W → γ < wt ztdb W

/-- *Locality* of a weight: removing a chord does not change the weight of the regions it does
not touch. -/
def WeightLocal (D : Set Point) (F : Set ztf)
    (wt : Set ztf → Set Point → ℕ) : Prop :=
  ∀ S ⊆ F, ∀ c ∈ S, ∀ X ∈ regionsIn D S, ¬ TouchesIn D c X → wt ztdb X = wt S X

/-- **Condition (ii) holds iff no chord is removable.** -/
theorem contractionCondIn_iff {wt : Set ztf → Set Point → ℕ} {S : Set ztf}
    {γ : ℕ} : ContractionCondIn D wt S γ ↔ ∀ c, ¬ Removable D wt γ S c := by
  constructor
  · rintro h c ⟨hc, U, hU, V, hV, hne, hcU, hcV, hlow, hW⟩
    obtain ⟨W, hW', hUW⟩ := exists_regionsIn_superset (sdiff_subset : S \ {c} ⊆ S) hU
    exact absurd (hW W hW' hUW) (not_le.2 (h c hc U hU V hV hne hcU hcV hlow W hW' hUW))
  · intro h c hc U hU V hV hne hcU hcV hlow W hW hUW
    zuks

    refine h c ⟨hc, U, hU, V, hV, hne, hcU, hcV, hlow, fun W' hW' hUW' => ?_⟩
    rw [regionsIn_eq_of_subset hW' hW (regionsIn_nonempty hU) hUW' hUW]
    omega

/-- The two regions touched by a removable chord are the two halves `R₁`, `R₂` of the removal
split. -/
theorem IsSplit.eq_pair_of_touches (hF : ChordSystem D F) {S : Set ztf} (hS : S ⊆ F)
    {c P R₁ R₂ : Set Point} (hc : c ∈ S) (h : IsSplit D ztdb c P R₁ R₂) {U : Set Point}
    (hU : U ∈ regionsIn D S) (hcU : TouchesIn D c U) : U = R₁ ∨ U = R₂ := by
  zuuu

  have hU' : U ∈ regionsIn D ztxxk := by_simp_all
  exact (h.touches_iff hF hT ztbkp hcT U hU').1 hcU

/-! ### Which chords can become removable -/

/-- **The correct form of the claim "the removals cannot make any chord removable if it was not
already so before" (p. 512).**  Let `c'` be a chord of `S` and `c ≠ c'` a chord sharing no region
with `c'` (no region of `S` is touched by both).  If `c` is removable after the removal of `c'`,
it was already removable before.  So a removal can only change the status of the chords of the
(at most `4 + 4 - 2` other) exit chords of the merged region; the literal claim is false (see the
module docstring), and a correct linear-time procedure re-examines those chords after each
removal (a worklist), or simply iterates to a fixpoint as in `lemma_3_5`. -/
theorem removable_of_removable_sdiff (hF : ChordSystem D F)
    {wt : Set ztf → Set Point → ℕ} {γ : ℕ} (hloc : WeightLocal D F wt)
    {S : Set ztf} (hS : S ⊆ F) {c c' : Set Point} (hc' : c' ∈ S) (hcc : c ≠ c')
    (hsep : ∀ X ∈ regionsIn D S, TouchesIn D c' X → ¬ TouchesIn D c X)
    (h : Removable D wt γ ztgeq c) : Removable D wt γ S c := by
  obtain ⟨hcT', U, hU, V, hV, hne, hcU, hcV, hlow, hW⟩ := h
  have hc : c ∈ S := hcT'.1
  have hT' : S \ {c'} ⊆ F := fun _ h => hS h.1
  have hc'T' : c' ∉ S \ {c'} := fun h => h.2 rfl
  have hins' := insert_sdiff_self hc'
  obtain ⟨P', R₁', R₂', hs'⟩ := exists_removal_split hF hS hc'
  -- `c` does not touch the region merged by the removal of `c'`
  have hnotP' : ∀ X, X = P' → ¬ TouchesIn D c X := by
    rintro X rfl hcX
    have hR₁' : R₁' ∈ regionsIn D S := by zunxg; exact hs'.mem₁
    have hR₂' : R₂' ∈ regionsIn D S := by zunxg; exact hs'.mem₂
    rcases hF.touches_split_or zthxt ztbkp hcc.symm hs'.union hcX with h1 | h1
    · exact hsep R₁' hR₁' (hs'.touches₁ hF hT' zthxt hc'T') h1
    · exact hsep R₂' hR₂' (hs'.touches₂ hF hT' zthxt hc'T') h1
  -- hence the regions `U`, `V` of `S \ {c'}` are regions of `S`, with the same exit chords
  have hold : ∀ X ∈ regionsIn D ztgeq, TouchesIn D c X →
      X ∈ regionsIn D S ∧ exitsIn D S X = exitsIn D ztgeq X := by
    intro X hX hcX
    have hXP : X ≠ P' := fun h' => hnotP' X h' hcX
    have e := hs'.exits_other hF hT' hX hXP
    rw [hins'] at e
    exact ⟨by zunxg; exact hs'.mem_of_ne hX hXP, e⟩
  obtain ⟨hUS, eU⟩ := hold U hU hcU
  obtain ⟨hVS, eV⟩ := hold V hV hcV
  refine ⟨hc, U, hUS, V, hVS, hne, hcU, hcV, by_simp_all, ?_⟩
  -- the merged region of `c` is not touched by `c'`, so its weight is unchanged
  intro W hW' hUW
  have hS1 : ztdju := fun _ h => hS h.1
  have hc'1 : c' ∈ S \ {c} := ⟨hc', fun h' => hcc (mem_singleton_iff.1 h').symm⟩
  obtain ⟨P, R₁, R₂, hs⟩ := exists_removal_split hF hS hc
  have hWP : W = P := by
    refine regionsIn_eq_of_subset hW' hs.mem (regionsIn_nonempty hUS) hUW ?_
    rcases hs.eq_pair_of_touches hF hS hc hUS hcU with rfl | rfl
    · exact hs.sub₁
    · exact hs.sub₂
  have hc'W : ¬ TouchesIn D c' W := by
    intro hc'W
    rw [hWP] at hc'W
    have hR₁ : R₁ ∈ regionsIn D S := by zuoqb; exact hs.mem₁
    have hR₂ : R₂ ∈ regionsIn D S := by zuoqb; exact hs.mem₂
    have hc1 : ztdjv := fun h => h.2 rfl
    rcases hF.touches_split_or ztbkp zthxt hcc hs.union hc'W with h1 | h1
    · exact hsep R₁ hR₁ h1 (hs.touches₁ hF hS1 ztbkp hc1)
    · exact hsep R₂ hR₂ h1 (hs.touches₂ hF hS1 ztbkp hc1)
  obtain ⟨hWmem, -⟩ := mem_sdiff_of_not_touches hF hS1 hc'1 hW' hc'W
  have hcomm : ztdb \ {c'} = ztgeq \ {c} := sdiff_right_comm _ _ _
  rw [← hloc ztdb hS1 c' hc'1 W hW' hc'W, hcomm]
  simp_all

/-! ### The chain instances -/
section ChainInstance
variable (C : Chain)
end ChainInstance
end
end Chazelle.Merge
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (IsHChordIn regionsIn TouchesIn SideAttach sideInArc)

/-! ## The shear -/

/-- The shear `(x, y) ↦ (x, y + ε x)`. -/
def shearPt (ε : ℝ) (p : Point) : Point := (p.1, p.2 + ε * p.1)

/-- The sheared polygon: every vertex sheared, same indices. -/
def shear (ε : ℝ) (P : Polygon) : Polygon := ⟨P.vertices.map ztiat⟩
variable (ε : ℝ) (P : Polygon)
/-- The shear does not change the number of vertices. -/
theorem shear_n : (shear ε P).n = P.n := by
  simp [shear, Polygon.n]
theorem getD_map_point (f : Point → Point) (l : List Point) (i : ℕ) (d : Point) :
    (l.map f).getD i ztvqe = f zttro := by
  simp

/-- Vertex `i` of the sheared polygon is the sheared vertex `i` (for every `i`: the default
vertex `(0, 0)` is fixed by the shear). -/
theorem shear_vtx (i : ℕ) : (shear ε P).vtx i = shearPt ε ztdn := by
  have h0 : shearPt ε ztbxh = ztbxh := by simp [shearPt]
  unfold Polygon.vtx shear
  grind

/-- **Orientation tests are exact under the shear**: the shear has determinant `1`. -/
theorem det_shearPt (a b c : Point) :
    det ztohp ztohq (shearPt ε c) = det a b c := by
  simp only [det, shearPt]
  ring

/-- The `x`-coordinate of the point of edge `e` of `Q` at the height of vertex `h` of `Q`
(Chazelle's chord endpoints; the vertex itself when `h` is an endpoint of `e`). -/
noncomputable def edgeXAt (Q : Polygon) (e h : ℕ) : ℝ := Chazelle.Visibility.edgeX Q e (Q.vtx h).2

/-- A **symbolic point** of the geometry polygon: a vertex, or the point of an edge at the height
of a vertex.  Every point the visibility-map stage stores or compares is of this form (design doc
§1.3: all chords lie at vertex heights). -/
inductive SymPt where
  /-- Vertex `i`. -/
  | vtx (i : ℕ)
  /-- The point of edge `e` at the height of vertex `h`. -/
  | onEdge (e h : ℕ)
  deriving DecidableEq

/-- The Euclidean point of a symbolic point of `Q`. -/
noncomputable def SymPt.eval (Q : Polygon) : SymPt → Point
  | .vtx i => Q.vtx i
  | .onEdge e h => (edgeXAt Q e h, (Q.vtx h).2)

/-- The indices of a symbolic point are below `n`. -/
def SymPt.Lt (n : ℕ) : SymPt → Prop
  | .vtx i => i < n
  | .onEdge e h => e < n ∧ h < n

/-- Pairwise distinct vertex heights (the paper's assumption, p. 488). -/
def DistinctHeights (Q : Polygon) : Prop :=
  ∀ i j, i < Q.n → j < Q.n → i ≠ j → (Q.vtx i).2 ≠ (Q.vtx j).2

/-- The `(y, x)`-lexicographic order of `P` is the `(y, x)`-lexicographic order of `Q` (for the
shear with distinct heights: the height order of `Q`). -/
def YlexAgree (P Q : Polygon) : Prop :=
  ∀ i j, i < P.n → j < P.n →
    (Chazelle.Mountain.ylexLT ztdn ztbhp ↔ Chazelle.Mountain.ylexLT ztdli zthrw)

/-- The three sign facts of a triple of points that the algorithm may test: abscissa order,
ordinate order, orientation sign. -/
def SignFacts (a b c : Point) : Prop × Prop × Prop × Prop :=
  (a.1 < b.1, a.2 < b.2, 0 < det a b c, det a b c = 0)

/-- **Stability of the algorithm's comparisons.**  Every test made by the visibility-map stage
compares abscissae or ordinates of two symbolic points or takes the orientation sign of three
(`SignFacts`); at `ε` each such test has the truth value it has for all smaller positive `ε'`
(hence the limit value, computable from `P` by lexicographic sign rules: WP-A). -/
def StableAt (P : Polygon) (ε : ℝ) : Prop :=
  ∀ ε', 0 < ε' → ε' ≤ ε → ∀ s₁ s₂ s₃ : SymPt, s₁.Lt P.n → s₂.Lt P.n → s₃.Lt P.n →
    SignFacts ztykd ztykf ztykh =
      SignFacts (s₁.eval ztoho) (s₂.eval ztoho) (s₃.eval ztoho)

/-- A good shear parameter for `P`. -/
def GoodShear (P : Polygon) (ε : ℝ) : Prop :=
  0 < ε ∧ DistinctHeights ztsl ∧ YlexAgree P ztsl ∧ StableAt P ε

/-- The shear parameter used for `P` (a good one whenever one exists, which WP-A proves for
simple polygons: `GoodShearExistsSpec`). -/
noncomputable def epsOf (P : Polygon) : ℝ := by
  classical
  exact if h : ∃ ε, GoodShear P ε then h.choose else 1

/-- **The geometry polygon** of the visibility-map stage. -/
noncomputable def Qof (P : Polygon) : Polygon := shear ztbhs P

/-- The chosen parameter is good as soon as some parameter is. -/
theorem goodShear_epsOf {P : Polygon} (h : ∃ ε, GoodShear P ε) : GoodShear P ztbhs := by
  classical
  unfold epsOf
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- `Q` is a shear of `P` by a nonnegative parameter whose height order is `P`'s lexicographic
order.  The final stage accepts tables for any such `Q` (with `Q = P`, `ε = 0`, as a special
case: `shearRel_refl`). -/
def ShearRel (P Q : Polygon) : Prop :=
  ∃ ε : ℝ, 0 ≤ ε ∧ Q = shear ε P ∧ YlexAgree P Q

/-- The geometry polygon is related to the input. -/
theorem shearRel_Qof {P : Polygon} (h : ∃ ε, GoodShear P ε) : ShearRel P zta := by
  have hg := goodShear_epsOf h
  exact ⟨epsOf P, hg.1.le, rfl, hg.2.2.1⟩

/-- A related polygon has the same number of vertices. -/
theorem ShearRel.n_eq {P Q : Polygon} (h : ShearRel P Q) : Q.n = P.n := by
  obtain ⟨ε, -, rfl, -⟩ := h
  exact shear_n ε P

/-- **WP-A obligation**: every simple polygon has a good shear parameter. -/
def GoodShearExistsSpec : Prop := ∀ P : Polygon, P.Simple → ∃ ε, GoodShear P ε

/-- **WP-A obligation**: the shear preserves simplicity and triangulations (it is a linear
bijection of the plane with determinant `1`, fixing vertical lines). -/
def ShearInvarianceSpec : Prop :=
  ∀ (ε : ℝ) (P : Polygon), (P.Simple → (shear ε P).Simple) ∧
    ∀ T : List Polygon.Triangle, ((shear ε P).Triangulates T ↔ P.Triangulates T)

/-! ## Disk models -/

/-- A disk model: an open domain `D`, a closed walk `W` keeping `D` on its left, the walk edges
counted by weights, the admissible chords, and the full (vertex-chord) visibility map. -/
structure Model where
  /-- The domain. -/
  D : Set Point
  /-- The boundary walk (domain on the left). -/
  W : Polygon
  /-- The walk edges counted by the weight (edges of `∂C`, not box or slit edges). -/
  counted : ℕ → Prop
  /-- The admissible chords (augmented chords of the model). -/
  Adm : Set ztf
  /-- The full (vertex-chord) visibility map of the model. -/
  Full : Set ztf

/-- **The chain model** of a chain `C` of any host polygon: domain `C.dom`, walk
`C.sideWalk C.sideBeta` (walk edges `0 … 4` box, `5` down the slit, `6 … 2m + 5` the double
boundary, `2m + 6` up the slit), admissible chords `Merge.augChords C`, full map `C.chords`. -/
noncomputable def chainModel (C : Chain) : Model where
  D := C.dom
  W := C.sideWalk C.sideBeta
  counted p := 6 ≤ p ∧ p < 2 * C.m + 6
  Adm := Merge.augChords C
  Full := C.chords

/-- The boundary walk of the interior of `Q`, oriented with the interior on its left. -/
noncomputable def interiorWalk (Q : Polygon) : Polygon := by
  classical
  exact if Mountain.LeftInside Q then Q else ⟨Q.vertices.reverse⟩

/-- **The interior model** of a closed polygon `Q`: the interior of `Q`, its boundary walk, all
edges counted, admissible chords the horizontal chords of the interior (vertex chords and
augmented chords alike), full map `Visibility.chords Q` (the interior visibility map). -/
noncomputable def interiorModel (Q : Polygon) : Model where
  D := Q.filled \ Q.boundary
  W := interiorWalk Q
  counted _ := True
  Adm := {c | ∃ y a b : ℝ, IsHChordIn ztrx y a b ∧ c = Visibility.hseg y a b}
  Full := Visibility.chords Q
namespace Model
variable (M : Model)

/-! ### Walk positions -/

/-- The start vertex of walk edge `p`. -/
noncomputable def wa (p : ℕ) : Point := M.W.vtx p

/-- The end vertex of walk edge `p`. -/
noncomputable def wb (p : ℕ) : Point := M.W.vtx ztwjk
end Model

/-- A **walk position**: a walk edge and a height code — `0` is the start vertex of the edge,
`h + 1` is the point of the edge at the height of vertex `h` of the height polygon `Q`. -/
structure WPos where
  /-- The walk edge. -/
  edge : ℕ
  /-- The height code. -/
  hgt : ℕ
  deriving DecidableEq
namespace Model
variable (M : Model)

/-- The parameter of a walk position on its walk edge. -/
noncomputable def param (Q : Polygon) (x : WPos) : ℝ :=
  match x.hgt with
  | 0 => 0
  | h + 1 =>
      if (M.wa x.edge).2 = (M.wb x.edge).2 then 0
      else ((Q.vtx h).2 - (M.wa x.edge).2) / ztjcc

/-- The key of a walk position (`edge + parameter`), which orders positions along the walk. -/
noncomputable def key (Q : Polygon) (x : WPos) : ℝ := x.edge + M.param Q x

/-- The point of a walk position. -/
noncomputable def pos (Q : Polygon) (x : WPos) : Point :=
  Geometry.lerp (M.wa x.edge) (M.wb x.edge) ztbyt

/-! ### Submaps: regions, cuts, arcs, weights -/

/-- The regions of the submap `F`. -/
def regions (F : Set ztf) : Set ztf := regionsIn M.D F

/-- The degree of a region (its number of exit chords). -/
noncomputable def deg (F : Set ztf) (U : Set Point) : ℕ :=
  {c | c ∈ F ∧ TouchesIn M.D c U}.ncard

/-- An admissible chord family with all heights at vertex heights of `Q`. -/
def ChordFamily (Q : Polygon) (F : Set ztf) : Prop :=
  F.Finite ∧ F ⊆ M.Adm ∧
    ∀ c ∈ F, ∃ h, h < Q.n ∧ ∃ a b : ℝ, c = Visibility.hseg (Q.vtx h).2 a b

/-- `x` is the key of a position where some chord of `F` is attached to the walk (side-aware,
`Chazelle.Chain.SideAttach`: the chord leaves the position into its left sector). -/
def IsCut (F : Set ztf) (x : ℝ) : Prop :=
  ∃ c ∈ F, ∃ p : ℕ, ∃ t : ℝ, SideAttach M.W c p t ∧ x = p + t

/-- The walk faces the set `U` at walk edge `p`, parameter `t`: the points pushed slightly to the
left of the walk are in `U`. -/
def Faces (p : ℕ) (t : ℝ) (U : Set Point) : Prop :=
  ∀ᶠ δ in 𝓝[>] (0 : ℝ), Jordan.offset ztpr ztoa t δ ∈ U

/-- **An arc** of the region `U` of `F`: the open key interval from `a` to `b` (cyclic,
`sideInArc`) contains no cut and faces `U` at every non-vertex key; its ends are cuts (or, for
the empty submap, the arc is the whole walk and `a = b = 0`: the key is pinned, since
`sideInArc a a x ↔ x ≠ a` would otherwise make every key the start of an arc — review finding
F1).  Zero-length arcs are not arcs in this
sense (they carry no weight and are represented through the exit chords). -/
def IsArc (F : Set ztf) (U : Set Point) (a b : ℝ) : Prop :=
  0 ≤ a ∧ a < M.W.n ∧ 0 ≤ b ∧ b < M.W.n ∧
    ((M.IsCut F a ∧ M.IsCut F b ∧ a ≠ b) ∨ (F = ∅ ∧ a = 0 ∧ b = 0)) ∧
    ztivv ∧
    (∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 < t → t < 1 → sideInArc a b ztk → M.Faces p t U)

/-- The number of counted walk edges met by the open key interval `(a, b)`. -/
noncomputable def arcWt (a b : ℝ) : ℕ :=
  {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b ztk}.ncard

/-- **The weight** of a region (p. 494): the maximum number of counted edges on one of its arcs. -/
noncomputable def weight (F : Set ztf) (U : Set Point) : ℕ :=
  sSup ztezo

/-- **Conformal** (p. 495): every region has at most four exit chords. -/
def Conformal (F : Set ztf) : Prop := ∀ U ∈ M.regions F, M.deg F U ≤ 4

/-- Regions have at most `d` exit chords (the bounded-degree relaxation used between the fusion
and the restoration of conformality, p. 508). -/
def DegLe (F : Set ztf) (d : ℕ) : Prop := ∀ U ∈ M.regions F, M.deg F U ≤ d

/-- **γ-semigranular** (condition (i), p. 496). -/
def Semigranular (F : Set ztf) (γ : ℕ) : Prop := ∀ U ∈ M.regions F, M.weight F U ≤ γ

/-- **Condition (ii)** of γ-granularity (p. 496): contracting a tree edge incident upon a node of
degree `< 3` produces a region of weight `> γ`. -/
def ContractionCond (F : Set ztf) (γ : ℕ) : Prop :=
  ∀ c ∈ F, ∀ U ∈ M.regions F, ∀ V ∈ M.regions F, U ≠ V → TouchesIn M.D c U →
    TouchesIn M.D c V → (M.deg F U < 3 ∨ M.deg F V < 3) →
      ∀ W' ∈ M.regions ztbrw, U ⊆ W' → γ < M.weight ztbrw W'

/-- **γ-granular** (p. 496). -/
def Granular (F : Set ztf) (γ : ℕ) : Prop := M.Semigranular F γ ∧ M.ContractionCond F γ
variable {F : Set (Set Point)}
theorem Granular.semigranular {γ : ℕ} (h : M.Granular F γ) :
    M.Semigranular F γ := h.1
theorem Conformal.degLe (h : M.Conformal F) : M.DegLe F 4 := h

/-- The number of counted walk edges (the size of the curve: `2 m` for a chain, `n` for the
interior of a polygon). -/
noncomputable def size : ℕ := {p : ℕ | p < M.W.n ∧ M.counted p}.ncard

/-- The full visibility map of the model has degree at most `D`, also after adding any finite
admissible family (the augmented map of p. 493); Lemma 3.3 needs this bound. -/
def FullDegLe (Q : Polygon) (D : ℕ) : Prop :=
  ∀ F, M.ChordFamily Q F → M.DegLe (M.Full ∪ F) D
theorem DegLe.mono {d d' : ℕ} (h : M.DegLe F d) (hd : d ≤ d') :
    M.DegLe F d' := fun U hU => (h U hU).trans hd
variable {γ γ' : ℕ}
theorem Semigranular.mono (h : M.Semigranular F γ)
    (hγ : γ ≤ γ') : M.Semigranular F γ' := fun U hU => (h U hU).trans hγ

/-- **A `γ`-granular submap is `γ'`-semigranular for `γ ≤ γ'`.** -/
theorem Granular.semigranular_of_le (h : M.Granular F γ)
    (hγ : γ ≤ γ') : M.Semigranular F γ' :=
  Semigranular.mono M h.1 hγ
