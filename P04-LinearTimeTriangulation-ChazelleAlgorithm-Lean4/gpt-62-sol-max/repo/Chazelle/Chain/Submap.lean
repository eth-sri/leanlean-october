module

public import Chazelle.Chain.Separation

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

theorem isClosed_hseg (y a b : ℝ) : IsClosed (hseg y a b) := by
  have : hseg y a b = {p : Point | p.2 = y} ∩ ({p | a ≤ p.1} ∩ {p | p.1 ≤ b}) := by
    ext p; simp [hseg]
  rw [this]
  exact (isClosed_eq continuous_snd continuous_const).inter
    ((isClosed_le continuous_const continuous_fst).inter (isClosed_le continuous_fst continuous_const))

/-- The open horizontal segment at height `y` between abscissae `a` and `b`. -/
def openHSeg (y a b : ℝ) : Set Point := (fun x : ℝ => ((x, y) : Point)) '' Ioo a b

theorem mem_openHSeg_iff {y a b : ℝ} {p : Point} :
    p ∈ openHSeg y a b ↔ p.2 = y ∧ a < p.1 ∧ p.1 < b := by
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨rfl, hx.1, hx.2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨p.1, ⟨h2, h3⟩, Prod.ext rfl h1.symm⟩

theorem isPreconnected_openHSeg (y a b : ℝ) : IsPreconnected (openHSeg y a b) :=
  isPreconnected_Ioo.image _ (by fun_prop : Continuous fun x : ℝ => ((x, y) : Point)).continuousOn

theorem openHSeg_nonempty {y a b : ℝ} (h : a < b) : (openHSeg y a b).Nonempty :=
  ⟨_, ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, rfl⟩⟩

/-- The part of a horizontal chord inside the domain is its open part. -/
theorem hseg_inter_eq_openHSeg {D : Set Point} {y a b : ℝ} (h : IsHChordIn D y a b) :
    hseg y a b ∩ D = openHSeg y a b := by
  ext p
  rw [mem_openHSeg_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, hpD⟩
    refine ⟨h1, lt_of_le_of_ne h2 fun e => ?_, lt_of_le_of_ne h3 fun e => ?_⟩
    · apply h.left_not
      rw [show ((a, y) : Point) = p from Prod.ext e h1.symm]; exact hpD
    · apply h.right_not
      rw [show ((b, y) : Point) = p from Prod.ext e.symm h1.symm]; exact hpD
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2.le, h3.le⟩, ?_⟩
    have := h.open_mem p.1 h2 h3
    rwa [show ((p.1, y) : Point) = p from Prod.ext rfl h1.symm] at this

theorem hseg_snd_eq {y a b : ℝ} {p q : Point} (hp : p ∈ hseg y a b) (hq : q ∈ hseg y a b) :
    p.2 = q.2 := by
  rw [hp.1, hq.1]

/-! ### Chord systems -/

/-- A finite family `F` of horizontal chords of the open domain `D`, each of which closes to a
walk with boundary in `Dᶜ ∪ c` whose parity flips across `c`. -/
structure ChordSystem (D : Set Point) (F : Set (Set Point)) : Prop where
  isOpen : IsOpen D
  finite : F.Finite
  hchord : ∀ c ∈ F, ∃ y a b : ℝ, IsHChordIn D y a b ∧ c = hseg y a b
  walk : ∀ c ∈ F, ∀ z ∈ c, z ∈ D →
    ∃ Γ : Polygon, Γ.boundary ⊆ Dᶜ ∪ c ∧
      ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
        (z.1, z.2 + ε) ∉ Γ.boundary ∧ (z.1, z.2 - ε) ∉ Γ.boundary ∧
          parity Γ (z.1, z.2 + ε) ≠ parity Γ (z.1, z.2 - ε)

/-- The free set of the submap `S` of the domain `D`. -/
def freeIn (D : Set Point) (S : Set (Set Point)) : Set Point := D \ ⋃₀ S

/-- The regions of the submap `S` of the domain `D`: the components of its free set. -/
def regionsIn (D : Set Point) (S : Set (Set Point)) : Set (Set Point) :=
  {U | ∃ z ∈ freeIn D S, U = connectedComponentIn (freeIn D S) z}

variable {D : Set Point} {F : Set (Set Point)}

theorem ChordSystem.isClosed_chord (hF : ChordSystem D F) {c : Set Point} (hc : c ∈ F) :
    IsClosed c := by
  obtain ⟨y, a, b, -, rfl⟩ := hF.hchord c hc
  exact isClosed_hseg y a b

theorem ChordSystem.isClosed_sUnion (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F) :
    IsClosed (⋃₀ S) :=
  (hF.finite.subset hS).isClosed_sUnion fun _ h => hF.isClosed_chord (hS h)

theorem ChordSystem.isOpen_freeIn (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F) :
    IsOpen (freeIn D S) :=
  hF.isOpen.sdiff (hF.isClosed_sUnion hS)

theorem freeIn_anti (D : Set Point) {S T : Set (Set Point)} (h : S ⊆ T) :
    freeIn D T ⊆ freeIn D S :=
  fun _ hp => ⟨hp.1, fun hm => hp.2 (sUnion_mono h hm)⟩

theorem freeIn_insert (D : Set Point) (c : Set Point) (S : Set (Set Point)) :
    freeIn D (insert c S) = freeIn D S \ c := by
  ext p
  simp only [freeIn, sUnion_insert, Set.mem_sdiff, mem_union]
  tauto

theorem freeIn_empty (D : Set Point) : freeIn D ∅ = D := by simp [freeIn]

theorem mem_regionsIn {S : Set (Set Point)} {z : Point} (hz : z ∈ freeIn D S) :
    connectedComponentIn (freeIn D S) z ∈ regionsIn D S := ⟨z, hz, rfl⟩

theorem ChordSystem.regionsIn_open (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F)
    {U : Set Point} (hU : U ∈ regionsIn D S) : IsOpen U := by
  obtain ⟨z, -, rfl⟩ := hU
  exact (hF.isOpen_freeIn hS).connectedComponentIn

theorem regionsIn_nonempty {S : Set (Set Point)} {U : Set Point} (hU : U ∈ regionsIn D S) :
    U.Nonempty := by
  obtain ⟨z, hz, rfl⟩ := hU
  exact ⟨z, mem_connectedComponentIn hz⟩

theorem regionsIn_isPreconnected {S : Set (Set Point)} {U : Set Point} (hU : U ∈ regionsIn D S) :
    IsPreconnected U := by
  obtain ⟨z, -, rfl⟩ := hU
  exact isPreconnected_connectedComponentIn

theorem regionsIn_subset {S : Set (Set Point)} {U : Set Point} (hU : U ∈ regionsIn D S) :
    U ⊆ freeIn D S := by
  obtain ⟨z, -, rfl⟩ := hU
  exact connectedComponentIn_subset _ _

theorem regionsIn_eq_component {S : Set (Set Point)} {U : Set Point} (hU : U ∈ regionsIn D S)
    {p : Point} (hp : p ∈ U) : U = connectedComponentIn (freeIn D S) p := by
  obtain ⟨z, -, rfl⟩ := hU
  exact connectedComponentIn_eq hp

theorem regionsIn_eq_or_disjoint {S : Set (Set Point)} {U V : Set Point}
    (hU : U ∈ regionsIn D S) (hV : V ∈ regionsIn D S) : U = V ∨ Disjoint U V := by
  by_cases h : Disjoint U V
  · exact Or.inr h
  · left
    obtain ⟨p, hpU, hpV⟩ := not_disjoint_iff.1 h
    rw [regionsIn_eq_component hU hpU, regionsIn_eq_component hV hpV]

theorem regionsIn_disjoint_of_ne {S : Set (Set Point)} {U V : Set Point}
    (hU : U ∈ regionsIn D S) (hV : V ∈ regionsIn D S) (hne : U ≠ V) : Disjoint U V :=
  (regionsIn_eq_or_disjoint hU hV).resolve_left hne

/-- The empty submap of a connected nonempty domain has a single region. -/
theorem regionsIn_empty (hD : IsPreconnected D) (hne : D.Nonempty) : regionsIn D ∅ = {D} := by
  ext U
  simp only [regionsIn, mem_ofPred_eq, mem_singleton_iff, freeIn_empty]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hD.connectedComponentIn hz
  · rintro rfl
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, hz, (hD.connectedComponentIn hz).symm⟩

/-! ### Chords: elementary facts -/

theorem ChordSystem.snd_eq (hF : ChordSystem D F) {c : Set Point} (hc : c ∈ F) {p q : Point}
    (hp : p ∈ c) (hq : q ∈ c) : p.2 = q.2 := by
  obtain ⟨y, a, b, -, rfl⟩ := hF.hchord c hc
  exact hseg_snd_eq hp hq

/-- Two distinct chords meet only outside the domain. -/
theorem ChordSystem.inter_subset_compl (hF : ChordSystem D F) {c d : Set Point} (hc : c ∈ F)
    (hd : d ∈ F) (hne : c ≠ d) : c ∩ d ⊆ Dᶜ := by
  obtain ⟨y, a, b, h, rfl⟩ := hF.hchord c hc
  obtain ⟨y', a', b', h', rfl⟩ := hF.hchord d hd
  intro p hp
  rcases hchordIn_inter h h' hp.1 hp.2 with ⟨rfl, rfl, rfl⟩ | ⟨h1, -⟩
  · exact absurd rfl hne
  · rcases h1 with rfl | rfl
    · exact h.left_not
    · exact h.right_not

/-- The part of a chord in the domain lies in the free set of every submap not containing it. -/
theorem ChordSystem.chord_inter_subset_freeIn (hF : ChordSystem D F) {S : Set (Set Point)}
    (hS : S ⊆ F) {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S) : c ∩ D ⊆ freeIn D S := by
  rintro p ⟨hp, hpD⟩
  refine ⟨hpD, ?_⟩
  rintro ⟨d, hd, hpd⟩
  have hne : c ≠ d := fun h => hcS (h ▸ hd)
  exact hF.inter_subset_compl hc (hS hd) hne ⟨hp, hpd⟩ hpD

/-- The part of a chord in the domain is nonempty and preconnected. -/
theorem ChordSystem.chord_inter_nonempty_isPreconnected (hF : ChordSystem D F) {c : Set Point}
    (hc : c ∈ F) : (c ∩ D).Nonempty ∧ IsPreconnected (c ∩ D) := by
  obtain ⟨y, a, b, h, rfl⟩ := hF.hchord c hc
  rw [hseg_inter_eq_openHSeg h]
  exact ⟨openHSeg_nonempty h.lt, isPreconnected_openHSeg y a b⟩

/-! ### Chord separation -/

/-- **Chord separation** (Lemma 2.1 for a chord system).  Let `S ⊆ F`, `c ∈ S`, and let `z` be
a point of `c` in the domain.  Then for all small `ε > 0` the points `z ± (0, ε)` lie in the
free set of `S` and in different regions of `S`. -/
theorem ChordSystem.chord_separates_in (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ S) {z : Point} (hz : z ∈ c) (hzD : z ∈ D) :
    ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ →
      (z.1, z.2 + ε) ∈ freeIn D S ∧ (z.1, z.2 - ε) ∈ freeIn D S ∧
        connectedComponentIn (freeIn D S) (z.1, z.2 + ε) ≠
          connectedComponentIn (freeIn D S) (z.1, z.2 - ε) := by
  obtain ⟨Γ, hΓ, ε₁, hε₁, hflip⟩ := hF.walk c (hS hc) z hz hzD
  have hup : Tendsto (fun ε : ℝ => ((z.1, z.2 + ε) : Point)) (𝓝[>] 0) (𝓝 z) :=
    ((by fun_prop : Continuous fun ε : ℝ => ((z.1, z.2 + ε) : Point)).tendsto' 0 z
      (by simp)).mono_left nhdsWithin_le_nhds
  have hdn : Tendsto (fun ε : ℝ => ((z.1, z.2 - ε) : Point)) (𝓝[>] 0) (𝓝 z) :=
    ((by fun_prop : Continuous fun ε : ℝ => ((z.1, z.2 - ε) : Point)).tendsto' 0 z
      (by simp)).mono_left nhdsWithin_le_nhds
  have hint : D ∈ 𝓝 z := hF.isOpen.mem_nhds hzD
  have hK : IsClosed (⋃₀ (S \ {c})) := hF.isClosed_sUnion (fun _ hd => hS hd.1)
  have hzK : z ∉ ⋃₀ (S \ {c}) := by
    rintro ⟨d, ⟨hdS, hdc⟩, hzd'⟩
    rw [mem_singleton_iff] at hdc
    exact hF.inter_subset_compl (hS hc) (hS hdS) (Ne.symm hdc) ⟨hz, hzd'⟩ hzD
  have hKn : (⋃₀ (S \ {c}))ᶜ ∈ 𝓝 z := hK.isOpen_compl.mem_nhds hzK
  have hfree : ∀ p : Point, p.2 ≠ z.2 → p ∈ D → p ∉ ⋃₀ (S \ {c}) → p ∈ freeIn D S := by
    intro p hp2 hpd hpK
    refine ⟨hpd, ?_⟩
    rintro ⟨d, hdS, hpd'⟩
    by_cases hdc : d = c
    · subst hdc
      exact hp2 (hF.snd_eq (hS hc) hpd' hz)
    · exact hpK ⟨d, ⟨hdS, hdc⟩, hpd'⟩
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (z.1, z.2 + ε) ∈ freeIn D S ∧ (z.1, z.2 - ε) ∈ freeIn D S ∧
        connectedComponentIn (freeIn D S) (z.1, z.2 + ε) ≠
          connectedComponentIn (freeIn D S) (z.1, z.2 - ε) := by
    filter_upwards [hup.eventually hint, hdn.eventually hint, hup.eventually hKn,
      hdn.eventually hKn, self_mem_nhdsWithin, Ioo_mem_nhdsGT hε₁] with ε h1 h2 h3 h4 h5 h6
    have hε : 0 < ε := h5
    have hp : (z.1, z.2 + ε) ∈ freeIn D S := hfree _ (by simp; linarith) h1 h3
    have hq : (z.1, z.2 - ε) ∈ freeIn D S := hfree _ (by simp; linarith) h2 h4
    refine ⟨hp, hq, fun heq => ?_⟩
    obtain ⟨-, -, hpar⟩ := hflip ε hε h6.2
    apply hpar
    have hsub : freeIn D S ⊆ Γ.boundaryᶜ := by
      intro p hp hpΓ
      rcases hΓ hpΓ with hb | hcc
      · exact hb hp.1
      · exact hp.2 ⟨_, hc, hcc⟩
    exact parity_eq_of_isPreconnected Γ isPreconnected_connectedComponentIn
      ((connectedComponentIn_subset _ _).trans hsub) (mem_connectedComponentIn hp)
      (heq ▸ mem_connectedComponentIn hq)
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hall
  exact ⟨ε₀, mem_Ioi.1 hε₀, fun ε h1 h2 => hsub ⟨h1, h2⟩⟩

/-! ### Half-disks (as in `Visibility/Submap.lean`) -/

/-- The open half-disk (for the sup metric: half-square) of radius `r` around `w`, on the side
`τ` (`1` = above, `-1` = below). -/
def halfDisk (w : Point) (r τ : ℝ) : Set Point := ball w r ∩ {p | 0 < τ * (p.2 - w.2)}

theorem mem_halfDisk_iff {w p : Point} {r τ : ℝ} :
    p ∈ halfDisk w r τ ↔ (|p.1 - w.1| < r ∧ |p.2 - w.2| < r) ∧ 0 < τ * (p.2 - w.2) := by
  simp only [halfDisk, mem_inter_iff, mem_ofPred_eq, mem_ball_iff_abs]

theorem halfDisk_subset_ball (w : Point) (r τ : ℝ) : halfDisk w r τ ⊆ ball w r :=
  inter_subset_left

theorem convex_halfDisk (w : Point) (r τ : ℝ) : Convex ℝ (halfDisk w r τ) := by
  refine (convex_ball w r).inter ?_
  intro p hp q hq a b ha hb hab
  simp only [mem_ofPred_eq] at hp hq ⊢
  simp only [Geometry.add_snd, Geometry.smul_snd]
  have : τ * (a * p.2 + b * q.2 - w.2) = a * (τ * (p.2 - w.2)) + b * (τ * (q.2 - w.2)) := by
    linear_combination (τ * w.2) * hab
  rw [this]
  rcases ha.lt_or_eq with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' hp) (mul_nonneg hb hq.le)
  · rw [← ha', zero_add] at hab
    subst hab
    rw [← ha', zero_mul, zero_add, one_mul]
    exact hq

theorem isPreconnected_halfDisk (w : Point) (r τ : ℝ) : IsPreconnected (halfDisk w r τ) :=
  (convex_halfDisk w r τ).isPreconnected

theorem vert_mem_halfDisk {w : Point} {r τ s : ℝ} (hτ : τ = 1 ∨ τ = -1) (hs0 : 0 < s)
    (hsr : s < r) : ((w.1, w.2 + τ * s) : Point) ∈ halfDisk w r τ := by
  rw [mem_halfDisk_iff]
  simp only [sub_self, abs_zero, add_sub_cancel_left]
  rcases hτ with rfl | rfl
  · simp only [one_mul]
    exact ⟨⟨by linarith, by rw [abs_of_pos hs0]; exact hsr⟩, hs0⟩
  · simp only [neg_one_mul, abs_neg, mul_neg, neg_neg]
    exact ⟨⟨by linarith, by rw [abs_of_pos hs0]; exact hsr⟩, hs0⟩

theorem halfDisk_mono {w w' : Point} {r r' τ : ℝ} (hh : w'.2 = w.2) (hb : ball w' r' ⊆ ball w r) :
    halfDisk w' r' τ ⊆ halfDisk w r τ := by
  rintro p ⟨hp1, hp2⟩
  refine ⟨hb hp1, ?_⟩
  simp only [mem_ofPred_eq] at hp2 ⊢
  rwa [hh] at hp2

theorem halfDisk_inter_nonempty {w w' : Point} {r r' τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hh : w'.2 = w.2) (hx : |w'.1 - w.1| < r) (hr' : 0 < r') :
    (halfDisk w r τ ∩ halfDisk w' r' τ).Nonempty := by
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg _) hx
  set s := min r r' / 2 with hs
  have hs0 : 0 < s := by rw [hs]; exact half_pos (lt_min hr hr')
  have hsr : s < r := by rw [hs]; linarith [min_le_left r r']
  have hsr' : s < r' := by rw [hs]; linarith [min_le_right r r']
  refine ⟨(w'.1, w.2 + τ * s), ?_, ?_⟩
  · rw [mem_halfDisk_iff]
    simp only [add_sub_cancel_left]
    have habs : |τ * s| < r := by
      rw [abs_mul, abs_of_pos hs0]
      rcases hτ with rfl | rfl <;> simp [hsr]
    refine ⟨⟨hx, habs⟩, ?_⟩
    have : τ * (τ * s) = s := by rcases hτ with rfl | rfl <;> ring
    rw [this]; exact hs0
  · rw [← hh]
    exact vert_mem_halfDisk hτ hs0 hsr'

/-! ### Exact splitting -/

/-- A half-disk at a chord point, inside the free set of `S`, avoids the chord and so lies in
the free set of `insert c S`. -/
theorem ChordSystem.halfDisk_subset_freeIn_insert (hF : ChordSystem D F) {S : Set (Set Point)}
    {c : Set Point} (hc : c ∈ F) {w : Point} (hw : w ∈ c) {r τ : ℝ}
    (hball : ball w r ⊆ freeIn D S) : halfDisk w r τ ⊆ freeIn D (insert c S) := by
  rintro p ⟨hp1, hp2⟩
  rw [freeIn_insert]
  refine ⟨hball hp1, fun hpc => ?_⟩
  simp only [mem_ofPred_eq] at hp2
  rw [hF.snd_eq hc hpc hw, sub_self, mul_zero] at hp2
  exact lt_irrefl _ hp2

/-- A preconnected subset of the free set meeting a region lies in it. -/
theorem subset_regionsIn_of_inter {S : Set (Set Point)} {U : Set Point} (hU : U ∈ regionsIn D S)
    {T : Set Point} (hT : IsPreconnected T) (hTS : T ⊆ freeIn D S) (hne : (T ∩ U).Nonempty) :
    T ⊆ U := by
  obtain ⟨q, hqT, hqU⟩ := hne
  rw [regionsIn_eq_component hU hqU]
  exact hT.subset_connectedComponentIn hqT hTS

/-- Around every interior point of a chord `c` inside an open set `R` there is a ball inside
`R` whose points at the height of the chord lie on `c`. -/
theorem ChordSystem.exists_ball_chord (hF : ChordSystem D F) {c : Set Point} (hc : c ∈ F)
    {R : Set Point} (hR : IsOpen R) (hcR : c ∩ D ⊆ R) {w : Point} (hw : w ∈ c ∩ D) :
    ∃ r > (0 : ℝ), ball w r ⊆ R ∧ ∀ p ∈ ball w r, p.2 = w.2 → p ∈ c := by
  obtain ⟨y, a, b, h, rfl⟩ := hF.hchord c hc
  obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hR w (hcR hw)
  rw [hseg_inter_eq_openHSeg h, mem_openHSeg_iff] at hw
  obtain ⟨hwy, hwa, hwb⟩ := hw
  refine ⟨min r₁ (min (w.1 - a) (b - w.1)), lt_min hr₁ (lt_min (by linarith) (by linarith)),
    (ball_subset_ball (min_le_left _ _)).trans hball, fun p hp hp2 => ?_⟩
  rw [mem_ball_iff_abs] at hp
  have h1 : |p.1 - w.1| < w.1 - a :=
    lt_of_lt_of_le hp.1 ((min_le_right _ _).trans (min_le_left _ _))
  have h2 : |p.1 - w.1| < b - w.1 :=
    lt_of_lt_of_le hp.1 ((min_le_right _ _).trans (min_le_right _ _))
  rw [abs_lt] at h1 h2
  exact ⟨hp2.trans hwy, by linarith, by linarith⟩

/-- **Half-disks on one side of a chord all lie in the same region.** -/
theorem ChordSystem.halfDisk_all (hF : ChordSystem D F) {S : Set (Set Point)} {c : Set Point}
    (hc : c ∈ F) {R : Set Point} (hR : IsOpen R) (hcR : c ∩ D ⊆ R) (hRS : R ⊆ freeIn D S)
    {U : Set Point} (hU : U ∈ regionsIn D (insert c S)) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hex : ∃ w ∈ c ∩ D, ∃ r > (0 : ℝ), ball w r ⊆ R ∧ halfDisk w r τ ⊆ U) :
    ∀ w ∈ c ∩ D, ∀ r > (0 : ℝ), ball w r ⊆ R → halfDisk w r τ ⊆ U := by
  have key : ∀ w ∈ c, ∀ r : ℝ, ball w r ⊆ R → (halfDisk w r τ ∩ U).Nonempty →
      halfDisk w r τ ⊆ U := fun w hw r hb hne =>
    subset_regionsIn_of_inter hU (isPreconnected_halfDisk w r τ)
      (hF.halfDisk_subset_freeIn_insert hc hw (hb.trans hRS)) hne
  obtain ⟨y, a, b, h, rfl⟩ := hF.hchord c hc
  have hopen : hseg y a b ∩ D = openHSeg y a b := hseg_inter_eq_openHSeg h
  rw [hopen] at hcR hex ⊢
  set T : Set ℝ := {x | ∃ r > (0 : ℝ), ball ((x, y) : Point) r ⊆ R ∧ halfDisk (x, y) r τ ⊆ U}
    with hT
  -- `T` is open
  have hTopen : IsOpen T := by
    rw [Metric.isOpen_iff]
    rintro x ⟨r, hr, hb, hU'⟩
    refine ⟨r / 2, half_pos hr, fun x' hx' => ?_⟩
    rw [mem_ball, Real.dist_eq] at hx'
    have hb' : ball ((x', y) : Point) (r / 2) ⊆ ball (x, y) r := by
      intro p hp
      rw [mem_ball_iff_abs] at hp ⊢
      simp only at hp ⊢
      refine ⟨?_, by linarith [hp.2]⟩
      calc |p.1 - x| = |(p.1 - x') + (x' - x)| := by ring_nf
        _ ≤ |p.1 - x'| + |x' - x| := abs_add_le _ _
        _ < r / 2 + r / 2 := add_lt_add hp.1 hx'
        _ = r := by ring
    exact ⟨r / 2, half_pos hr, hb'.trans hb,
      (halfDisk_mono (w := ((x, y) : Point)) (w' := (x', y)) rfl hb').trans hU'⟩
  -- `T` is relatively closed in the parameter interval
  have hTclosed : closure T ∩ Ioo a b ⊆ T := by
    rintro x ⟨hxc, hx⟩
    set w : Point := (x, y) with hw
    have hwR : w ∈ R := hcR ⟨x, hx, rfl⟩
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 hR w hwR
    obtain ⟨x', hx'T, hxx'⟩ := Metric.mem_closure_iff.1 hxc (r / 2) (half_pos hr)
    obtain ⟨r', hr', -, hU'⟩ := hx'T
    rw [Real.dist_eq] at hxx'
    have hwc : w ∈ hseg y a b := ⟨rfl, hx.1.le, hx.2.le⟩
    refine ⟨r, hr, hb, key w hwc r hb ?_⟩
    have hxd : |((x', y) : Point).1 - w.1| < r := by
      simp only [hw]
      rw [abs_sub_comm]; linarith
    obtain ⟨p, hp1, hp2⟩ := halfDisk_inter_nonempty hτ (by simp [hw]) hxd hr'
    exact ⟨p, hp1, hU' hp2⟩
  -- `T` meets the parameter interval
  have hTne : (Ioo a b ∩ T).Nonempty := by
    obtain ⟨w, ⟨x, hx, rfl⟩, r, hr, hb, hU'⟩ := hex
    exact ⟨x, hx, r, hr, hb, hU'⟩
  have hall : Ioo a b ⊆ T :=
    isPreconnected_Ioo.subset_of_closure_inter_subset hTopen hTne hTclosed
  -- conclusion
  rintro w ⟨x, hx, rfl⟩ r hr hb
  obtain ⟨r₁, hr₁, -, hU'⟩ := hall hx
  have hwc : ((x, y) : Point) ∈ hseg y a b := ⟨rfl, hx.1.le, hx.2.le⟩
  refine key _ hwc r hb ?_
  obtain ⟨p, hp1, hp2⟩ := halfDisk_inter_nonempty hτ rfl (by simpa using hr) hr₁
  exact ⟨p, hp1, hU' hp2⟩

/-- **Every region of `insert c S` inside the region `R` of `c` contains a half-disk at an
interior point of `c`.** -/
theorem ChordSystem.exists_halfDisk_subset (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S) {z₀ : Point} (hz₀ : z₀ ∈ c ∩ D) {U : Set Point}
    (hU : U ∈ regionsIn D (insert c S)) {u : Point} (huU : u ∈ U)
    (huR : u ∈ connectedComponentIn (freeIn D S) z₀) :
    ∃ w ∈ c ∩ D, ∃ r > (0 : ℝ), ∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧
      ball w r ⊆ connectedComponentIn (freeIn D S) z₀ ∧ halfDisk w r τ ⊆ U := by
  have hS' : insert c S ⊆ F := insert_subset hc hS
  set A := freeIn D S with hA
  set A' := freeIn D (insert c S) with hA'
  set R := connectedComponentIn A z₀ with hR
  have hA'A : A' ⊆ A := freeIn_anti D (subset_insert c S)
  have hA'eq : A' = A \ c := freeIn_insert D c S
  have hz₀A : z₀ ∈ A := hF.chord_inter_subset_freeIn hS hc hcS hz₀
  have hcR : c ∩ D ⊆ R :=
    (hF.chord_inter_nonempty_isPreconnected hc).2.subset_connectedComponentIn hz₀
      (hF.chord_inter_subset_freeIn hS hc hcS)
  have hRopen : IsOpen R := (hF.isOpen_freeIn hS).connectedComponentIn
  have hRA : R ⊆ A := connectedComponentIn_subset _ _
  have hUopen : IsOpen U := hF.regionsIn_open hS' hU
  have hUA' : U ⊆ A' := regionsIn_subset hU
  have hUeq : U = connectedComponentIn A' u := regionsIn_eq_component hU huU
  have hclos : closure U ∩ A' ⊆ U := by
    have hpre : IsPreconnected (closure U ∩ A') :=
      (regionsIn_isPreconnected hU).subset_closure (subset_inter subset_closure hUA')
        inter_subset_left
    have := hpre.subset_connectedComponentIn ⟨subset_closure huU, hUA' huU⟩ inter_subset_right
    rwa [← hUeq] at this
  have hex : ∃ w ∈ c ∩ D, w ∈ closure U := by
    by_contra hno
    push Not at hno
    have hcl : closure U ∩ R ⊆ U := by
      rintro p ⟨hpc, hpR⟩
      refine hclos ⟨hpc, ?_⟩
      rw [hA'eq]
      refine ⟨hRA hpR, fun hpcc => ?_⟩
      exact hno p ⟨hpcc, (hRA hpR).1⟩ hpc
    have hRU : R ⊆ U :=
      isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hUopen ⟨u, huR, huU⟩ hcl
    have : z₀ ∈ A' := hUA' (hRU (mem_connectedComponentIn hz₀A))
    rw [hA'eq] at this
    exact this.2 hz₀.1
  obtain ⟨w, hw, hwc⟩ := hex
  obtain ⟨r, hr, hb, hline⟩ := hF.exists_ball_chord hc hRopen hcR hw
  obtain ⟨q, hqU, hdq⟩ := Metric.mem_closure_iff.1 hwc r hr
  have hqb : q ∈ ball w r := by rw [mem_ball, dist_comm]; exact hdq
  have hqc : q ∉ c := by
    intro hqc
    have := hUA' hqU
    rw [hA'eq] at this
    exact this.2 hqc
  have hq2 : q.2 ≠ w.2 := fun h => hqc (hline q hqb h)
  refine ⟨w, hw, r, hr, if w.2 < q.2 then 1 else -1, ?_, hb, ?_⟩
  · split_ifs <;> simp
  · refine subset_regionsIn_of_inter hU (isPreconnected_halfDisk _ _ _)
      (hF.halfDisk_subset_freeIn_insert hc hw.1 (hb.trans hRA)) ⟨q, ⟨hqb, ?_⟩, hqU⟩
    simp only [mem_ofPred_eq]
    rcases lt_or_gt_of_ne hq2 with hlt | hlt
    · rw [ite_eq_right (not_lt.2 hlt.le)]; linarith
    · rw [ite_eq_left hlt]; linarith

/-- **Exact splitting.**  Adding a chord `c ∉ S` to a submap `S ⊆ F` replaces the region `R` of
`S` containing the interior of `c` by exactly two regions `R₁ ≠ R₂` with `R₁ ∪ R₂ = R \ c`, and
leaves every other region unchanged. -/
theorem ChordSystem.regionsIn_insert (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S) :
    ∃ R ∈ regionsIn D S, c ∩ D ⊆ R ∧ ∃ R₁ R₂ : Set Point, R₁ ≠ R₂ ∧ R₁ ∪ R₂ = R \ c ∧
      R₁ ∈ regionsIn D (insert c S) ∧ R₂ ∈ regionsIn D (insert c S) ∧
      regionsIn D (insert c S) = (regionsIn D S \ {R}) ∪ {R₁, R₂} := by
  have hS' : insert c S ⊆ F := insert_subset hc hS
  obtain ⟨z₀, hz₀⟩ := (hF.chord_inter_nonempty_isPreconnected hc).1
  set A := freeIn D S with hA
  set A' := freeIn D (insert c S) with hA'
  set R := connectedComponentIn A z₀ with hR
  have hA'A : A' ⊆ A := freeIn_anti D (subset_insert c S)
  have hA'eq : A' = A \ c := freeIn_insert D c S
  have hz₀A : z₀ ∈ A := hF.chord_inter_subset_freeIn hS hc hcS hz₀
  have hRmem : R ∈ regionsIn D S := mem_regionsIn hz₀A
  have hcR : c ∩ D ⊆ R :=
    (hF.chord_inter_nonempty_isPreconnected hc).2.subset_connectedComponentIn hz₀
      (hF.chord_inter_subset_freeIn hS hc hcS)
  have hRopen : IsOpen R := (hF.isOpen_freeIn hS).connectedComponentIn
  have hRA : R ⊆ A := connectedComponentIn_subset _ _
  obtain ⟨r₀, hr₀, hb₀⟩ := Metric.isOpen_iff.1 hRopen z₀ (hcR hz₀)
  let pt : ℝ → Point := fun τ => (z₀.1, z₀.2 + τ * (r₀ / 2))
  have hpt : ∀ τ, (τ = 1 ∨ τ = -1) → pt τ ∈ halfDisk z₀ r₀ τ := fun τ hτ =>
    vert_mem_halfDisk hτ (half_pos hr₀) (by linarith)
  have hhalf : ∀ τ, halfDisk z₀ r₀ τ ⊆ A' := fun τ =>
    hF.halfDisk_subset_freeIn_insert hc hz₀.1 (hb₀.trans hRA)
  have hptA' : ∀ τ, (τ = 1 ∨ τ = -1) → pt τ ∈ A' := fun τ hτ => hhalf τ (hpt τ hτ)
  have hRτ : ∀ τ, (τ = 1 ∨ τ = -1) → connectedComponentIn A' (pt τ) ∈ regionsIn D (insert c S) :=
    fun τ hτ => mem_regionsIn (hptA' τ hτ)
  have hhalfR : ∀ τ, (τ = 1 ∨ τ = -1) → halfDisk z₀ r₀ τ ⊆ connectedComponentIn A' (pt τ) :=
    fun τ hτ => (isPreconnected_halfDisk _ _ _).subset_connectedComponentIn (hpt τ hτ) (hhalf τ)
  have hsubR : ∀ p ∈ A', p ∈ R → connectedComponentIn A' p ⊆ R := by
    intro p hp hpR
    rw [hR, connectedComponentIn_eq hpR]
    exact connectedComponentIn_mono p hA'A
  have hRτR : ∀ τ, (τ = 1 ∨ τ = -1) → connectedComponentIn A' (pt τ) ⊆ R := fun τ hτ =>
    hsubR _ (hptA' τ hτ) (hb₀ (halfDisk_subset_ball _ _ _ (hpt τ hτ)))
  have hcases : ∀ U ∈ regionsIn D (insert c S), (U ∩ R).Nonempty →
      U = connectedComponentIn A' (pt 1) ∨ U = connectedComponentIn A' (pt (-1)) := by
    intro U hU ⟨u, huU, huR⟩
    obtain ⟨w, hw, r, hr, τ, hτ, hb, hsub⟩ :=
      hF.exists_halfDisk_subset hS hc hcS hz₀ hU huU huR
    have hall := hF.halfDisk_all hc hRopen hcR hRA hU hτ ⟨w, hw, r, hr, hb, hsub⟩ z₀ hz₀ r₀ hr₀ hb₀
    have hptU : pt τ ∈ U := hall (hpt τ hτ)
    have hUeq : U = connectedComponentIn A' (pt τ) := regionsIn_eq_component hU hptU
    rcases hτ with rfl | rfl
    · exact Or.inl hUeq
    · exact Or.inr hUeq
  have hne : connectedComponentIn A' (pt 1) ≠ connectedComponentIn A' (pt (-1)) := by
    obtain ⟨ε₀, hε₀, hsep⟩ := hF.chord_separates_in hS' (mem_insert c S) hz₀.1 hz₀.2
    set ε := min ε₀ r₀ / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; exact half_pos (lt_min hε₀ hr₀)
    have hε1 : ε < ε₀ := by rw [hε]; linarith [min_le_left ε₀ r₀]
    have hε2 : ε < r₀ := by rw [hε]; linarith [min_le_right ε₀ r₀]
    obtain ⟨-, -, hdiff⟩ := hsep ε hε0 hε1
    intro heq
    apply hdiff
    have h1 : ((z₀.1, z₀.2 + ε) : Point) ∈ connectedComponentIn A' (pt 1) := by
      apply hhalfR 1 (Or.inl rfl)
      have := vert_mem_halfDisk (Or.inl rfl) hε0 hε2 (w := z₀)
      simpa using this
    have h2 : ((z₀.1, z₀.2 - ε) : Point) ∈ connectedComponentIn A' (pt (-1)) := by
      apply hhalfR (-1) (Or.inr rfl)
      have := vert_mem_halfDisk (Or.inr rfl) hε0 hε2 (w := z₀)
      simpa [sub_eq_add_neg] using this
    calc connectedComponentIn (freeIn D (insert c S)) (z₀.1, z₀.2 + ε)
        = connectedComponentIn A' (pt 1) := (connectedComponentIn_eq h1).symm
      _ = connectedComponentIn A' (pt (-1)) := heq
      _ = connectedComponentIn (freeIn D (insert c S)) (z₀.1, z₀.2 - ε) :=
          connectedComponentIn_eq h2
  have hother : ∀ U ∈ regionsIn D S, U ≠ R → U ∈ regionsIn D (insert c S) := by
    intro U hU hUR
    rcases id hU with ⟨u, hu, rfl⟩
    have hdisj : Disjoint (connectedComponentIn A u) R := regionsIn_disjoint_of_ne hU hRmem hUR
    have hUA' : connectedComponentIn A u ⊆ A' := by
      intro p hp
      rw [hA'eq]
      refine ⟨connectedComponentIn_subset _ _ hp, fun hpc => ?_⟩
      have hpR : p ∈ R := hcR ⟨hpc, (connectedComponentIn_subset _ _ hp).1⟩
      exact hdisj.notMem_of_mem_left hp hpR
    have huA' : u ∈ A' := hUA' (mem_connectedComponentIn hu)
    refine ⟨u, huA', ?_⟩
    apply Subset.antisymm
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hu) hUA'
    · exact connectedComponentIn_mono u hA'A
  refine ⟨R, hRmem, hcR, connectedComponentIn A' (pt 1), connectedComponentIn A' (pt (-1)), hne,
    ?_, hRτ 1 (Or.inl rfl), hRτ (-1) (Or.inr rfl), ?_⟩
  · apply Subset.antisymm
    · rintro p (hp | hp)
      · exact ⟨hRτR 1 (Or.inl rfl) hp, ((hA'eq ▸ connectedComponentIn_subset _ _ hp) : p ∈ A \ c).2⟩
      · exact ⟨hRτR (-1) (Or.inr rfl) hp,
          ((hA'eq ▸ connectedComponentIn_subset _ _ hp) : p ∈ A \ c).2⟩
    · rintro p ⟨hpR, hpc⟩
      have hpA' : p ∈ A' := by rw [hA'eq]; exact ⟨hRA hpR, hpc⟩
      rcases hcases _ (mem_regionsIn hpA') ⟨p, mem_connectedComponentIn hpA', hpR⟩ with h | h
      · exact Or.inl (h ▸ mem_connectedComponentIn hpA')
      · exact Or.inr (h ▸ mem_connectedComponentIn hpA')
  · ext U
    simp only [mem_union, Set.mem_sdiff, mem_singleton_iff, mem_insert_iff]
    constructor
    · intro hU
      obtain ⟨u, hu, rfl⟩ := hU
      have huA : u ∈ A := hA'A hu
      by_cases huR : u ∈ R
      · exact Or.inr (hcases _ (mem_regionsIn hu) ⟨u, mem_connectedComponentIn hu, huR⟩)
      · left
        have hUmem : connectedComponentIn A u ∈ regionsIn D S := mem_regionsIn huA
        have hUR : connectedComponentIn A u ≠ R := by
          intro h; exact huR (h ▸ mem_connectedComponentIn huA)
        obtain ⟨u', hu', heq⟩ := hother _ hUmem hUR
        have hu'' : u ∈ connectedComponentIn A' u' := heq ▸ mem_connectedComponentIn huA
        rw [connectedComponentIn_eq hu''] at heq
        rw [← heq]
        exact ⟨hUmem, hUR⟩
    · rintro (⟨hU, hUR⟩ | rfl | rfl)
      · exact hother U hU hUR
      · exact hRτ 1 (Or.inl rfl)
      · exact hRτ (-1) (Or.inr rfl)

/-! ### Counting regions -/

theorem ChordSystem.ncard_regionsIn_insert (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F)
    {c : Set Point} (hc : c ∈ F) (hcS : c ∉ S) (hfin : (regionsIn D S).Finite) :
    (regionsIn D (insert c S)).Finite ∧
      (regionsIn D (insert c S)).ncard = (regionsIn D S).ncard + 1 := by
  obtain ⟨R, hR, -, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ := hF.regionsIn_insert hS hc hcS
  have hnew : ∀ U, U ∈ regionsIn D (insert c S) → U ⊆ R → U ∉ regionsIn D S \ {R} := by
    rintro U hU hUR ⟨hUS, hUne⟩
    rw [mem_singleton_iff] at hUne
    obtain ⟨p, hp⟩ := regionsIn_nonempty hU
    exact (regionsIn_disjoint_of_ne hUS hR hUne).notMem_of_mem_left hp (hUR hp)
  have hR₁R : R₁ ⊆ R := fun p hp => by
    have : p ∈ R₁ ∪ R₂ := Or.inl hp
    rw [hunion] at this
    exact this.1
  have hR₂R : R₂ ⊆ R := fun p hp => by
    have : p ∈ R₁ ∪ R₂ := Or.inr hp
    rw [hunion] at this
    exact this.1
  have hdisj : Disjoint (regionsIn D S \ {R}) {R₁, R₂} := by
    rw [disjoint_iff_forall_ne]
    rintro U hU V hV rfl
    simp only [mem_insert_iff, mem_singleton_iff] at hV
    rcases hV with rfl | rfl
    · exact hnew _ hR₁ hR₁R hU
    · exact hnew _ hR₂ hR₂R hU
  rw [heq]
  refine ⟨hfin.sdiff.union (toFinite _), ?_⟩
  rw [ncard_union_eq hdisj hfin.sdiff (toFinite _), ncard_pair hne,
    ← ncard_sdiff_singleton_add_one hR hfin]

/-- **Region count.**  For a connected nonempty domain, a submap with `k` chords has exactly
`k + 1` regions (and finitely many). -/
theorem ChordSystem.regionsIn_finite_ncard (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set (Set Point)} (hS : S ⊆ F) :
    (regionsIn D S).Finite ∧ (regionsIn D S).ncard = S.ncard + 1 := by
  have hfin : S.Finite := hF.finite.subset hS
  induction S, hfin using Set.Finite.induction_on with
  | empty =>
    rw [regionsIn_empty hD hne]
    simp
  | @insert c S hcS hSfin ih =>
    have hS' : S ⊆ F := (subset_insert c S).trans hS
    have hc : c ∈ F := hS (mem_insert c S)
    obtain ⟨hfin', hcard⟩ := ih hS'
    obtain ⟨hfin'', hcard''⟩ := hF.ncard_regionsIn_insert hS' hc hcS hfin'
    refine ⟨hfin'', ?_⟩
    rw [hcard'', hcard, ncard_insert_of_notMem hcS hSfin]

theorem ChordSystem.ncard_regionsIn (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set (Set Point)} (hS : S ⊆ F) :
    (regionsIn D S).ncard = S.ncard + 1 :=
  (hF.regionsIn_finite_ncard hD hne hS).2

theorem ChordSystem.regionsIn_finite (hF : ChordSystem D F) (hD : IsPreconnected D)
    (hne : D.Nonempty) {S : Set (Set Point)} (hS : S ⊆ F) : (regionsIn D S).Finite :=
  (hF.regionsIn_finite_ncard hD hne hS).1

/-! ### The chain instance -/

variable (C : Chain)

end

end Chazelle.Chain
