module

public import Chazelle.Golf

public import Chazelle.Core.SweepLocal

/-!
# Lemma 3.6 (WP-H), part 1: the geometry of a ray-shooting query

The query of Lemma 3.6 (pp. 514–515) shoots a horizontal ray from a point `z` toward a chain `C`
whose `γ`-granular submap `F` (a chord family of the chain model) has been preprocessed: the
regions of `F` are the nodes of a planar graph `G`, a set `D*` of nodes has been removed and the
remaining nodes are labelled by clusters.  The query shoots naively at the arcs of the regions of
`D*`, then at the arcs of the regions of one cluster.  This file proves the mathematics behind
the correctness of that query (in the chain model, where arcs are subsets of the walk).

## Answers (`FirstHit` / `NoHit` on the chain)

* `noHit_of_above`: above the top of the chain the ray misses it.
* `firstHit_chain_of_hit`, `noHit_chain_of_hit`: the first hit of the ray on the complement of
  the domain (`C.hitParam`) is the answer: a first hit of `C.set` if the point is on the chain,
  otherwise (the ray reached the side of the box) the ray misses the chain.

## Regions along a ray

* `hitParam_eq_of_interval`: characterisation of `C.hitParam` by an interval of the domain.
* `arcHit_left`, `arcHit_right`: the point where a ray leaves a region (forward or backward) lies
  on an arc of that region (from `Sweep.local_shoot`).
* `CrossAdj`: two regions face each other across a point of the chain along a horizontal line;
  this is the adjacency the preprocessing must put into the graph `G` (the faces of `S*` sharing
  an edge, p. 514).
* `ray_path`: **the regions met by a ray form a `CrossAdj`-path** whose steps happen at crossings
  with the chain, where both regions have an arc through the crossing point (nondegenerate rays:
  finitely many crossings, no chord on the ray).

## The cluster argument (p. 515)

* `label_of_path`: along a path of a graph whose nodes all avoid `D*`, the cluster label is
  constant (the property guaranteed by `ClusterSpec`).
* `cluster_query`: if the arcs of the regions of `D*` are not hit before the parameter `T`, and
  `R` is the region just before `T`, then the region `U` of the start of the ray is in `D*` or in
  the cluster of `R`.
* `query_firstHit`: hence the first hit on the arcs of `D*` and of the cluster of `R` is the first
  hit of the chain; with the answer lemmas this is the correctness of the query.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sideInArc regionsIn freeIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)

namespace OracleQ

/-! ## Ray arithmetic -/

/-- Rays compose: moving `a` then `b` along the direction `σ`. -/
theorem rayPt_rayPt (z : Point) (σ a b : ℝ) : rayPt (rayPt z σ a) σ b = rayPt z σ (a + b) := by
  ϴ rayPt
  ext <;> (simp; try ring)

/-- Moving `a` along `σ`, then `b` along `-σ`. -/
theorem rayPt_rayPt_neg (z : Point) (σ a b : ℝ) :
    rayPt (rayPt z σ a) (-σ) b = rayPt z σ (a - b) := by
  ϴ rayPt
  ext <;> (simp; try ring)

/-- The parameter of a horizontal ray is determined by its point. -/
theorem rayPt_injective (z : Point) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    Function.Injective (rayPt z σ) := by
  intro a b h
  have := congrArg Prod.fst h
  simp only [rayPt_fst] at this
  rcases hσ with rfl | rfl <;> linarith

/-! ## Answers -/

/-- **Above the top of the chain, the ray misses it.** -/
theorem noHit_of_above (C : Chain) {z : Point} (hz : C.top.2 < z.2) (σ : ℝ) :
    NoHit C.set z σ := by
  intro t _ hmem
  have := C.snd_le_top_of_mem_set hmem
  rw [rayPt_snd] at this
  linarith

/-- **A hit on the chain is the answer.**  For a free direction below the top, if the first point
of the ray off the domain is on the chain, it is the first hit of the chain. -/
theorem firstHit_chain_of_hit (C : Chain) {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hfree : Merge.FreeAt C z σ)
    (hmem : rayPt z σ (C.hitParam z σ) ∈ C.set) : FirstHit C.set z σ (C.hitParam z σ) :=
  Sweep.firstHit_of_compl_dom C hz hσ hfree C.set_subset_dom_compl hmem

/-- **A hit off the chain means no hit.**  For a free direction below the top, if the first point
of the ray off the domain is not on the chain (it is on a vertical side of the box), the ray
misses the chain. -/
theorem noHit_chain_of_hit (C : Chain) {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hfree : Merge.FreeAt C z σ)
    (hmem : rayPt z σ (C.hitParam z σ) ∉ C.set) : NoHit C.set z σ := by
  obtain ⟨hT, hnd, hdom⟩ := Merge.hit_of_freeAt C hz hσ hfree
  set T := C.hitParam z σ with hTdef
  have hout : rayPt z σ T ∉ Chain.box C.radius := by
    rcases (Merge.not_mem_dom_iff C (p := rayPt z σ T) (by simpa using hz)).1 hnd with h | h
    · exact h
    · exact absurd h hmem
  have hin : rayPt z σ (T / 2) ∈ Chain.box C.radius :=
    C.dom_subset_box (hdom (T / 2) (⟡) (by linarith))
  intro t ht htC
  have hbt := C.set_subset_box htC
  rcases lt_trichotomy t T with hlt | heq | hgt
  · exact C.not_mem_set_of_mem_dom (hdom t ht hlt) htC
  · exact hmem (heq ▸ htC)
  · -- the box is convex: `T` lies between `T / 2` and `t`, both inside the box
    apply hout
    simp only [Chain.mem_box_iff, rayPt_fst, rayPt_snd] at hin hbt ⊢
    refine ⟨?_, hin.2⟩
    rw [abs_lt] at hin hbt ⊢
    rcases hσ with rfl | rfl <;> constructor <;> nlinarith [hin.1.1, hin.1.2, hbt.1.1, hbt.1.2]

/-! ## The first hit through an interval of the domain -/

/-- **Characterisation of the first-hit parameter**: if the ray is in the domain on `(0, T)` and
leaves it at `T`, then `C.hitParam z σ = T`. -/
theorem hitParam_eq_of_interval (C : Chain) {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {T : ℝ} (hT : 0 < T)
    (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ C.dom) (hend : rayPt z σ T ∉ C.dom) :
    C.hitParam z σ = T := by
  have hfree : Merge.FreeAt C z σ := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    exact hdom t ht.1 ht.2
  obtain ⟨h1, h2, h3⟩ := Merge.hit_of_freeAt C hz hσ hfree
  rcases lt_trichotomy (C.hitParam z σ) T with hlt | heq | hgt
  · exact absurd (hdom _ h1 hlt) h2
  · exact heq
  · exact absurd (h3 T hT hgt) hend

/-- A point of the ray at a parameter of the interval `(a, s)` of a region is in the domain. -/
theorem mem_dom_of_region (C : Chain) {F : Set (Set Point)} {V : Set Point}
    (hV : V ∈ (chainModel C).regions F) {x : Point} (hx : x ∈ V) : x ∈ C.dom :=
  (Chazelle.Chain.regionsIn_subset (D := C.dom) hV hx).1

/-- The ray hits the region `V` at `x`: `x` lies on (the point set of) an arc of `V`. -/
def ArcHit (C : Chain) (F : Set (Set Point)) (V : Set Point) (x : Point) : Prop :=
  ∃ a b, (chainModel C).IsArc F V a b ∧ x ∈ (chainModel C).arcSet a b

/-- **Leaving a region forward.**  If the ray is in the region `V` on `(a, s)` and off the domain
at `s`, the point at `s` lies on an arc of `V`. -/
theorem arcHit_left (C : Chain) (hP : C.P.Simple) {Q : Polygon} {F : Set (Set Point)}
    (hFam : (chainModel C).ChordFamily Q F) {V : Set Point} (hV : V ∈ (chainModel C).regions F)
    {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {a s : ℝ} (has : a < s)
    (hin : ∀ t, a < t → t < s → rayPt z σ t ∈ V) (hs : rayPt z σ s ∉ C.dom) :
    ArcHit C F V (rayPt z σ s) := by
  set z' := rayPt z σ a with hz'
  have hz'2 : z'.2 ≤ C.top.2 := by simpa [hz'] using hz
  have hini : ∀ᶠ u in 𝓝[>] (0 : ℝ), rayPt z' σ u ∈ V := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 has)] with u hu
    Ξ hz', rayPt_rayPt
    exact hin _ (by linarith [hu.1]) (by linarith [hu.2])
  obtain ⟨x, y, harc, hmem⟩ := Sweep.local_shoot C hP hFam hV hz'2 hσ hini
  have hhit : C.hitParam z' σ = s - a := by
    refine hitParam_eq_of_interval C hz'2 hσ (sub_pos.2 has) (fun u hu hus => ?_) ?_
    · Ξ hz', rayPt_rayPt
      exact mem_dom_of_region C hV (hin _ (⟡) (by linarith))
    · Ξ hz', rayPt_rayPt, add_sub_cancel
      exact hs
  rw [hhit, hz', rayPt_rayPt, add_sub_cancel] at hmem
  exact ⟨x, y, harc, hmem⟩

/-- **Leaving a region backward.**  If the ray is in the region `V` on `(s, b)` and off the domain
at `s`, the point at `s` lies on an arc of `V`. -/
theorem arcHit_right (C : Chain) (hP : C.P.Simple) {Q : Polygon} {F : Set (Set Point)}
    (hFam : (chainModel C).ChordFamily Q F) {V : Set Point} (hV : V ∈ (chainModel C).regions F)
    {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {s b : ℝ} (hsb : s < b)
    (hin : ∀ t, s < t → t < b → rayPt z σ t ∈ V) (hs : rayPt z σ s ∉ C.dom) :
    ArcHit C F V (rayPt z σ s) := by
  set z' := rayPt z σ b with hz'
  have hz'2 : z'.2 ≤ C.top.2 := by simpa [hz'] using hz
  have hnσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  have hini : ∀ᶠ u in 𝓝[>] (0 : ℝ), rayPt z' (-σ) u ∈ V := by
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hsb)] with u hu
    Ξ hz', rayPt_rayPt_neg
    exact hin _ (by linarith [hu.2]) (by linarith [hu.1])
  obtain ⟨x, y, harc, hmem⟩ := Sweep.local_shoot C hP hFam hV hz'2 hnσ hini
  have hhit : C.hitParam z' (-σ) = b - s := by
    refine hitParam_eq_of_interval C hz'2 hnσ (sub_pos.2 hsb) (fun u hu hus => ?_) ?_
    · Ξ hz', rayPt_rayPt_neg
      exact mem_dom_of_region C hV (hin _ (⟡) (by linarith))
    · Ξ hz', rayPt_rayPt_neg, sub_sub_cancel
      exact hs
  rw [hhit, hz', rayPt_rayPt_neg, sub_sub_cancel] at hmem
  exact ⟨x, y, harc, hmem⟩

/-! ## Crossing adjacency and the path of regions along a ray -/

/-- **Crossing adjacency**: the regions `A` and `B` face each other across a point `x` of the
chain along a horizontal line (the points just behind `x` are in `A`, those just after it in `B`).
These are the adjacencies of faces of `S*` through an edge of the chain (p. 514); the graph built
by the preprocessing must contain them. -/
def CrossAdj (C : Chain) (A B : Set Point) : Prop :=
  ∃ x ∈ C.set, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x (-σ) t ∈ A) ∧
    (∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt x σ t ∈ B)

/-- **A step of the ray** before the parameter `T`: the ray crosses the chain at a parameter
`s ∈ (0, T)` from the region `A` into the region `B`, and both regions have an arc through the
crossing point. -/
def RayStep (C : Chain) (F : Set (Set Point)) (z : Point) (σ T : ℝ) (A B : Set Point) : Prop :=
  A ∈ (chainModel C).regions F ∧ B ∈ (chainModel C).regions F ∧ CrossAdj C A B ∧
    ∃ s, 0 < s ∧ s < T ∧ ArcHit C F A (rayPt z σ s) ∧ ArcHit C F B (rayPt z σ s)

/-- A point of the ray in the box, off the chain and off the chords, below the top, is free. -/
theorem mem_freeIn_of_ray (C : Chain) {F : Set (Set Point)} {z : Point} (hz : z.2 ≤ C.top.2)
    {σ t : ℝ} (hbox : rayPt z σ t ∈ Chain.box C.radius) (hC : rayPt z σ t ∉ C.set)
    (hF : rayPt z σ t ∉ ⋃₀ F) : rayPt z σ t ∈ freeIn C.dom F := by
  refine ⟨?_, hF⟩
  by_contra hd
  rcases (Merge.not_mem_dom_iff C (p := rayPt z σ t) (by simpa using hz)).1 hd with h | h
  · exact h hbox
  · exact hC h

/-- A free open interval of the ray meeting a region lies in it. -/
theorem interval_subset_region (C : Chain) {F : Set (Set Point)} {V : Set Point}
    (hV : V ∈ (chainModel C).regions F) {z : Point} {σ a b : ℝ}
    (hfree : ∀ t, a < t → t < b → rayPt z σ t ∈ freeIn C.dom F) {t₀ : ℝ} (ht₀a : a < t₀)
    (ht₀b : t₀ < b) (hin : rayPt z σ t₀ ∈ V) : ∀ t, a < t → t < b → rayPt z σ t ∈ V := by
  have hV' := hV
  have hc : IsPreconnected (rayPt z σ '' Ioo a b) :=
    isPreconnected_Ioo.image _ (Chazelle.Visibility.continuous_rayPt z σ).continuousOn
  have hsub := Sweep.subset_region hV' hc (by rintro _ ⟨t, ht, rfl⟩; exact hfree t ht.1 ht.2)
    ⟨t₀, ⟨ht₀a, ht₀b⟩, rfl⟩ hin
  intro t ha hb
  exact hsub ⟨t, ⟨ha, hb⟩, rfl⟩

/-- A free open interval of the ray lies in one region. -/
theorem exists_region_of_interval (C : Chain) {F : Set (Set Point)} {z : Point} {σ a b : ℝ}
    (hab : a < b) (hfree : ∀ t, a < t → t < b → rayPt z σ t ∈ freeIn C.dom F) :
    ∃ V ∈ (chainModel C).regions F, ∀ t, a < t → t < b → rayPt z σ t ∈ V := by
  have hm : rayPt z σ ((a + b) / 2) ∈ freeIn C.dom F := hfree _ (⟡) (by linarith)
  refine ⟨_, Chazelle.Chain.mem_regionsIn hm, ?_⟩
  exact interval_subset_region C (Chazelle.Chain.mem_regionsIn hm) hfree (⟡)
    (⟡) (mem_connectedComponentIn hm)

/-- **The last crossing before `t₁`**: for a finite set `X` of parameters and `t₁ > 0` there is
`s ∈ [0, t₁)`, either `0` or a positive element of `X`, with no element of `X` in `(s, t₁)`. -/
theorem exists_gap {X : Set ℝ} (hX : X.Finite) {t₁ : ℝ} (ht₁ : 0 < t₁) :
    ∃ s, 0 ≤ s ∧ s < t₁ ∧ (s = 0 ∨ (0 < s ∧ s ∈ X)) ∧ ∀ t, s < t → t < t₁ → t ∉ X := by
  by_cases hne : (X ∩ Ioo 0 t₁).Nonempty
  · obtain ⟨s, hs, hmax⟩ := Set.exists_max_image (X ∩ Ioo 0 t₁) id (hX.inter_of_left _) hne
    refine ⟨s, hs.2.1.le, hs.2.2, Or.inr ⟨hs.2.1, hs.1⟩, fun t hst ht1 htX => ?_⟩
    have := hmax t ⟨htX, lt_trans hs.2.1 hst, ht1⟩
    simp only [id] at this
    linarith
  · refine ⟨0, le_rfl, ht₁, Or.inl rfl, fun t ht0 ht1 htX => hne ⟨t, htX, ht0, ht1⟩⟩

/-- **The regions met by a ray form a path** (nondegenerate rays).  Let the ray from `z` (below
the top of the chain) stay in the box on `(0, T)`, meet the chain at finitely many parameters and
avoid the chords of `F` on `(0, T)`.  If its initial part lies in the region `U` and its part just
before `t₁ ≤ T` in the region `R`, then `U` and `R` are joined by a chain of `RayStep`s. -/
theorem ray_path (C : Chain) (hP : C.P.Simple) {Q : Polygon} {F : Set (Set Point)}
    (hFam : (chainModel C).ChordFamily Q F) {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {T : ℝ}
    (hbox : ∀ t, 0 < t → t < T → rayPt z σ t ∈ Chain.box C.radius)
    (hfin : {t : ℝ | rayPt z σ t ∈ C.set}.Finite)
    (hnoF : ∀ t, 0 < t → t < T → rayPt z σ t ∉ ⋃₀ F)
    {U : Set Point} (hU : U ∈ (chainModel C).regions F)
    (hUi : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U) :
    ∀ (n : ℕ) (t₁ : ℝ) (R : Set Point), ({t : ℝ | rayPt z σ t ∈ C.set} ∩ Ioo 0 t₁).ncard = n →
      0 < t₁ → t₁ ≤ T → R ∈ (chainModel C).regions F →
      (∀ᶠ t in 𝓝[<] t₁, rayPt z σ t ∈ R) → Relation.ReflTransGen (RayStep C F z σ T) U R := by
  set X := {t : ℝ | rayPt z σ t ∈ C.set} with hXdef
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t₁ R hn ht₁ ht₁T hR hRi
  obtain ⟨s, hs0, hst, hsX, hgap⟩ := exists_gap hfin ht₁
  have hfree : ∀ t, s < t → t < t₁ → rayPt z σ t ∈ freeIn C.dom F := fun t h1 h2 =>
    mem_freeIn_of_ray C hz (hbox t (⟡) (by linarith)) (hgap t h1 h2)
      (hnoF t (⟡) (by linarith))
  obtain ⟨t', ht'R, ht'⟩ := (hRi.and (Ioo_mem_nhdsLT hst)).exists
  have hRall := interval_subset_region C hR hfree ht'.1 ht'.2 ht'R
  rcases hsX with rfl | ⟨hspos, hsX⟩
  · -- no crossing: the ray is in one region on `(0, t₁)`
    obtain ⟨t'', ht''U, ht''⟩ := (hUi.and (Ioo_mem_nhdsGT ht₁)).exists
    have hU' := hU
    have hR' := hR
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hU' hR' with e | hdis
    · Ξ e
    · exact absurd (hRall t'' ht''.1 ht''.2) (Set.disjoint_left.1 hdis ht''U)
  · -- the last crossing `s`: the region `A` just before it
    obtain ⟨s', hs'0, hs's, -, hgap'⟩ := exists_gap hfin hspos
    have hfree' : ∀ t, s' < t → t < s → rayPt z σ t ∈ freeIn C.dom F := fun t h1 h2 =>
      mem_freeIn_of_ray C hz (hbox t (⟡) (by linarith)) (hgap' t h1 h2)
        (hnoF t (⟡) (by linarith))
    obtain ⟨A, hA, hAall⟩ := exists_region_of_interval C hs's hfree'
    have hfinI : (X ∩ Ioo 0 t₁).Finite := hfin.inter_of_left _
    have hlt : (X ∩ Ioo 0 s).ncard < n := by
      Ξ ← hn
      refine Set.ncard_lt_ncard ⟨fun t ht => ⟨ht.1, ht.2.1, lt_trans ht.2.2 hst⟩, fun hsub => ?_⟩
        hfinI
      exact lt_irrefl s (hsub ⟨hsX, hspos, hst⟩).2.2
    have hpath := ih _ hlt s A rfl hspos (⟡) hA
      (by filter_upwards [Ioo_mem_nhdsLT hs's] with t ht; exact hAall t ht.1 ht.2)
    have hsdom : rayPt z σ s ∉ C.dom := fun h => C.set_subset_dom_compl hsX h
    refine hpath.tail ⟨hA, hR, ⟨rayPt z σ s, hsX, σ, hσ, ?_, ?_⟩, s, hspos, ⟡,
      arcHit_left C hP hFam hA hz hσ hs's hAall hsdom,
      arcHit_right C hP hFam hR hz hσ hst hRall hsdom⟩
    · filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hs's)] with u hu
      Ξ rayPt_rayPt_neg
      exact hAall _ (by linarith [hu.2]) (by linarith [hu.1])
    · filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hst)] with u hu
      Ξ rayPt_rayPt
      exact hRall _ (by linarith [hu.1]) (by linarith [hu.2])

/-- The initial part of a free ray avoiding the chords lies in a region. -/
theorem exists_initial_region (C : Chain) {F : Set (Set Point)} {z : Point} {σ : ℝ}
    (hfree : Merge.FreeAt C z σ) (hnoF : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∉ ⋃₀ F) :
    ∃ U ∈ (chainModel C).regions F, ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hfree.and hnoF)
  obtain ⟨U, hU, hall⟩ := exists_region_of_interval C (z := z) (σ := σ) (F := F) hu
    fun t h1 h2 => ⟨(hsub ⟨h1, h2⟩).1, (hsub ⟨h1, h2⟩).2⟩
  refine ⟨U, hU, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hu] with t ht
  exact hall t ht.1 ht.2

/-- The part of a nondegenerate ray just before `T` lies in a region (the region `R` of the query,
which the implementation finds by double identification at the hit point, or on the side of the
box). -/
theorem exists_final_region (C : Chain) {F : Set (Set Point)} {z : Point} (hz : z.2 ≤ C.top.2)
    {σ T : ℝ} (hT : 0 < T) (hbox : ∀ t, 0 < t → t < T → rayPt z σ t ∈ Chain.box C.radius)
    (hfin : {t : ℝ | rayPt z σ t ∈ C.set}.Finite)
    (hnoF : ∀ t, 0 < t → t < T → rayPt z σ t ∉ ⋃₀ F) :
    ∃ R ∈ (chainModel C).regions F, ∀ᶠ t in 𝓝[<] T, rayPt z σ t ∈ R := by
  obtain ⟨s, hs0, hsT, -, hgap⟩ := exists_gap hfin hT
  obtain ⟨R, hR, hall⟩ := exists_region_of_interval C hsT fun t h1 h2 =>
    mem_freeIn_of_ray C hz (hbox t (⟡) h2) (hgap t h1 h2) (hnoF t (by linarith) h2)
  refine ⟨R, hR, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT hsT] with t ht
  exact hall t ht.1 ht.2

/-! ## Nondegeneracy -/

/-- **Finitely many crossings**: if no edge of the chain is horizontal, a horizontal ray meets the
chain at finitely many parameters. -/
theorem finite_crossings (C : Chain)
    (hne : ∀ k, k < C.m → (C.vertex k).2 ≠ (C.vertex (k + 1)).2) (z : Point) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) : {t : ℝ | rayPt z σ t ∈ C.set}.Finite := by
  have hsub : {t : ℝ | rayPt z σ t ∈ C.set} ⊆
      ⋃ k ∈ Finset.range C.m, {t : ℝ | rayPt z σ t ∈ C.chainEdge k} := by
    rintro t ⟨k, hk, hmem⟩
    ϴ Finset.mem_range, mem_iUnion, mem_ofPred_eq
    exact ⟨k, hk, hmem⟩
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.range C.m).finite_toSet fun k hk => ?_) hsub
  refine Set.Subsingleton.finite fun a ha b hb => ?_
  have hk : k < C.m := Finset.mem_range.1 hk
  simp only [mem_ofPred_eq, C.chainEdge_eq] at ha hb
  obtain ⟨s₁, -, -, h₁⟩ := ha
  obtain ⟨s₂, -, -, h₂⟩ := hb
  have hy1 := congrArg Prod.snd h₁
  have hy2 := congrArg Prod.snd h₂
  simp only [rayPt_snd] at hy1 hy2
  have hd : (C.vertex (k + 1)).2 - (C.vertex k).2 ≠ 0 := sub_ne_zero.2 (hne k hk).symm
  have hs : s₁ = s₂ := by
    have : s₁ * ((C.vertex (k + 1)).2 - (C.vertex k).2) =
        s₂ * ((C.vertex (k + 1)).2 - (C.vertex k).2) := ⟡
    exact mul_right_cancel₀ hd this
  apply rayPt_injective z hσ
  Ξ h₁, h₂, hs

/-- Distinct vertex heights of the ambient polygon: no edge of the chain is horizontal. -/
theorem vertex_snd_ne (C : Chain) (hD : DistinctHeights C.P) {k : ℕ} :
    (C.vertex k).2 ≠ (C.vertex (k + 1)).2 := by
  unfold Chain.vertex
  have hn : 2 ≤ C.P.n := by have := C.add_one_le; have := C.one_le; omega
  refine hD _ _ (C.edgeIdx_lt k) (C.edgeIdx_lt (k + 1)) ?_
  unfold Chain.edgeIdx
  intro h
  have h1 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  rw [show C.s + (k + 1) - (C.s + k) = 1 by omega, Nat.one_mod_eq_one.2 (by omega)] at h1
  exact absurd h1 (by norm_num)

/-! ## The cluster argument (p. 515) -/

/-- **Labels along a path avoiding `D*`**: if the label is constant along the walks of `G` that
avoid `D*`, and every step of a path joins equal or adjacent nodes outside `D*`, then the ends of
the path are equal, or both outside `D*` with the same label. -/
theorem label_of_path {ι : Type*} (G : SimpleGraph ι) (Dm : ι → Prop) (ℓ : ι → ℕ)
    (hlab : ∀ u v (w : G.Walk u v), (∀ x ∈ w.support, ¬ Dm x) → ℓ u = ℓ v)
    {r : ι → ι → Prop} (hr : ∀ a b, r a b → ¬ Dm a ∧ ¬ Dm b ∧ (a = b ∨ G.Adj a b))
    {i j : ι} (h : Relation.ReflTransGen r i j) : i = j ∨ (¬ Dm i ∧ ¬ Dm j ∧ ℓ i = ℓ j) := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hc, hbc'⟩ := hr _ _ hbc
    have hℓ : ℓ b = ℓ c := by
      rcases hbc' with e | hadj
      · Ξ e
      · refine hlab _ _ (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil) ?_
        intro x hx
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact hb
        · exact hc
    rcases ih with e | ⟨hi, -, hl⟩
    · subst e
      exact Or.inr ⟨hb, hc, hℓ⟩
    · exact Or.inr ⟨hi, hc, hl.trans hℓ⟩

/-! ## Degenerate starts: along a chord, and from the box -/

/-- The ray from a point of the closed box at a height inside the box stays in the box until it
reaches the side of the box in its direction (parameter `r - σ z.1`). -/
theorem rayPt_mem_box (C : Chain) {z : Point} (hz1 : |z.1| ≤ C.radius) (hz2 : |z.2| < C.radius)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {t : ℝ} (ht : 0 < t) (htT : t < C.radius - σ * z.1) :
    rayPt z σ t ∈ Chain.box C.radius := by
  refine ⟨?_, by simpa using hz2⟩
  ϴ rayPt_fst
  rw [abs_le] at hz1
  Ξ abs_lt
  rcases hσ with rfl | rfl <;> constructor <;> linarith [hz1.1, hz1.2]

/-- The walk of the chain model has `2 m + 7` edges. -/
theorem walk_n (C : Chain) : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n C.sideBeta

/-- The key of the box position of a rightward query from the height of vertex `h`. -/
theorem key_box_left (C : Chain) (Q : Polygon) (h : ℕ) :
    (chainModel C).key Q ⟨1, h + 1⟩ = 1 + (C.radius - (Q.vtx h).2) / (2 * C.radius) := by
  have hR := C.radius_pos
  have h2 : (1 + 1) % (chainModel C).W.n = 2 := by rw [walk_n]; exact Nat.mod_eq_of_lt (⋄)
  unfold Model.key Model.param Model.wa Model.wb
  ϴ h2
  show ((1 : ℕ) : ℝ) + (if ((C.sideWalk C.sideBeta).vtx 1).2 = ((C.sideWalk C.sideBeta).vtx 2).2
    then 0 else ((Q.vtx h).2 - ((C.sideWalk C.sideBeta).vtx 1).2) /
      (((C.sideWalk C.sideBeta).vtx 2).2 - ((C.sideWalk C.sideBeta).vtx 1).2)) = _
  Ξ C.sideWalk_vtx_one, C.sideWalk_vtx_two
  simp only
  rw [ite_eq_right (⟡)]
  push_cast
  congr 1
  field_simp
  ring

/-- The key of the box position of a leftward query from the height of vertex `h`. -/
theorem key_box_right (C : Chain) (Q : Polygon) (h : ℕ) :
    (chainModel C).key Q ⟨3, h + 1⟩ = 3 + ((Q.vtx h).2 + C.radius) / (2 * C.radius) := by
  have hR := C.radius_pos
  have h4 : (3 + 1) % (chainModel C).W.n = 4 := by rw [walk_n]; exact Nat.mod_eq_of_lt (⋄)
  unfold Model.key Model.param Model.wa Model.wb
  ϴ h4
  show ((3 : ℕ) : ℝ) + (if ((C.sideWalk C.sideBeta).vtx 3).2 = ((C.sideWalk C.sideBeta).vtx 4).2
    then 0 else ((Q.vtx h).2 - ((C.sideWalk C.sideBeta).vtx 3).2) /
      (((C.sideWalk C.sideBeta).vtx 4).2 - ((C.sideWalk C.sideBeta).vtx 3).2)) = _
  Ξ C.sideWalk_vtx_three, C.sideWalk_vtx_four
  simp only
  rw [ite_eq_right (⟡)]
  push_cast
  congr 1
  field_simp
  ring

/-! ## The first naive scan -/

/-- The scan bound from a first hit: before the first hit on a set, the ray avoids it. -/
theorem avoid_of_firstHitOpt {A : Set Point} {z : Point} {σ : ℝ} {o : Option ℝ}
    (h : Sweep.FirstHitOpt A z σ o) {T : ℝ} (hT : ∀ t, o = some t → T ≤ t) :
    ∀ s, 0 < s → s < T → rayPt z σ s ∉ A := by
  intro s hs0 hsT hmem
  cases o with
  | none => exact h s hs0 hmem
  | some t => exact h.2.2 s hs0 (lt_of_lt_of_le hsT (hT t rfl)) hmem

/-! ## The cluster argument with nodes (arcs) instead of regions -/

/-- **The cluster argument, node version.**  The nodes `ι` of the graph `G` carry regions `rg`
(several nodes per region, e.g. the arcs of the region; scanning a node means scanning its whole
region, so `hD` speaks of the region of a node of `D*`).  The nodes of one region are connected
inside the region (`hconn`), and two regions facing each other across the chain have adjacent
nodes (`hG`).  If the ray starts in `U`, ends just before `T` in the region of the node `iR`, and
hits no region of a node of `D*` before `T`, then `U` has a node in `D*` or in the cluster of
`iR`. -/
theorem cluster_query_nodes (C : Chain) (hP : C.P.Simple) {Q : Polygon} {F : Set (Set Point)}
    (hFam : (chainModel C).ChordFamily Q F) {ι : Type*} (rg : ι → Set Point)
    (G : SimpleGraph ι)
    (hconn : ∀ a b, rg a = rg b →
      Relation.ReflTransGen (fun u v => G.Adj u v ∧ rg u = rg a ∧ rg v = rg a) a b)
    (hG : ∀ A B, A ∈ (chainModel C).regions F → B ∈ (chainModel C).regions F → A ≠ B →
      CrossAdj C A B → ∃ a b, rg a = A ∧ rg b = B ∧ G.Adj a b)
    (Dm : ι → Prop) (ℓ : ι → ℕ)
    (hlab : ∀ u v (w : G.Walk u v), (∀ x ∈ w.support, ¬ Dm x) → ℓ u = ℓ v)
    {z : Point} (hz : z.2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {T : ℝ} (hT : 0 < T)
    (hbox : ∀ t, 0 < t → t < T → rayPt z σ t ∈ Chain.box C.radius)
    (hfin : {t : ℝ | rayPt z σ t ∈ C.set}.Finite)
    (hnoF : ∀ t, 0 < t → t < T → rayPt z σ t ∉ ⋃₀ F)
    (hD : ∀ i, Dm i → ∀ s, 0 < s → s < T → ¬ ArcHit C F (rg i) (rayPt z σ s))
    {U : Set Point} (hU : U ∈ (chainModel C).regions F)
    (hUi : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt z σ t ∈ U) {iR : ι}
    (hR : rg iR ∈ (chainModel C).regions F) (hRi : ∀ᶠ t in 𝓝[<] T, rayPt z σ t ∈ rg iR) :
    ∃ iU, rg iU = U ∧ (Dm iU ∨ (¬ Dm iU ∧ ℓ iU = ℓ iR)) := by
  have hpath := ray_path C hP hFam hz hσ hbox hfin hnoF hU hUi _ T (rg iR) rfl hT le_rfl hR hRi
  -- the node relation along the ray
  let S : ι → ι → Prop := fun a b => (a = b ∨ G.Adj a b) ∧ ¬ Dm a ∧ ¬ Dm b
  -- nodes of a region hit before `T` are not in `D*`
  have hnotD : ∀ V, (∃ s, 0 < s ∧ s < T ∧ ArcHit C F V (rayPt z σ s)) →
      ∀ v, rg v = V → ¬ Dm v := by
    rintro V ⟨s, hs0, hsT, hh⟩ v hv hDv
    exact hD v hDv s hs0 hsT (hv ▸ hh)
  -- inside a region hit before `T`, nodes are joined by `S`-paths
  have hinside : ∀ V, (∃ s, 0 < s ∧ s < T ∧ ArcHit C F V (rayPt z σ s)) →
      ∀ a b, rg a = V → rg b = V → Relation.ReflTransGen S a b := by
    intro V hV a b ha hb
    have hc := hconn a b (ha.trans hb.symm)
    refine Relation.ReflTransGen.mono (fun u v huv => ?_) _ _ hc
    obtain ⟨hadj, hu, hv⟩ := huv
    exact ⟨Or.inr hadj, hnotD V hV u (hu.trans ha), hnotD V hV v (hv.trans ha)⟩
  have key : ∀ V, Relation.ReflTransGen (RayStep C F z σ T) U V →
      V = U ∨ ∀ v, rg v = V → ∃ u, rg u = U ∧ Relation.ReflTransGen S u v := by
    intro V hUV
    induction hUV with
    | refl => exact Or.inl rfl
    | @tail W X _ hWX ih =>
      obtain ⟨hWr, hXr, hcr, s, hs0, hsT, hWa, hXa⟩ := hWX
      have hWhit : ∃ s, 0 < s ∧ s < T ∧ ArcHit C F W (rayPt z σ s) := ⟨s, hs0, hsT, hWa⟩
      have hXhit : ∃ s, 0 < s ∧ s < T ∧ ArcHit C F X (rayPt z σ s) := ⟨s, hs0, hsT, hXa⟩
      by_cases hWX : W = X
      · subst hWX; exact ih
      · right
        obtain ⟨a, b, ha, hb, hab⟩ := hG W X hWr hXr hWX hcr
        have hstep : S a b := ⟨Or.inr hab, hnotD W hWhit a ha, hnotD X hXhit b hb⟩
        intro v hv
        have hbv := hinside X hXhit b v hb hv
        rcases ih with e | ih
        · subst e
          exact ⟨a, ha, (Relation.ReflTransGen.single hstep).trans hbv⟩
        · obtain ⟨u, hu, hua⟩ := ih a ha
          exact ⟨u, hu, (hua.tail hstep).trans hbv⟩
  rcases key _ hpath with e | h
  · refine ⟨iR, e, ?_⟩
    by_cases hDR : Dm iR
    · exact Or.inl hDR
    · exact Or.inr ⟨hDR, rfl⟩
  · obtain ⟨u, hu, hpu⟩ := h iR rfl
    refine ⟨u, hu, ?_⟩
    rcases label_of_path G Dm ℓ hlab (r := S) (fun a b hab => ⟨hab.2.1, hab.2.2, hab.1⟩) hpu with
      e | ⟨h1, -, h3⟩
    · subst e
      by_cases hDR : Dm u
      · exact Or.inl hDR
      · exact Or.inr ⟨hDR, rfl⟩
    · exact Or.inr ⟨h1, h3⟩

end OracleQ

end

end Chazelle.Core
