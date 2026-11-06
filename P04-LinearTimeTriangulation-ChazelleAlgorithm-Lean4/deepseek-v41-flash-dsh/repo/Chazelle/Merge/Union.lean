module

public import Chazelle.Golf

public import Chazelle.Chain.Chord

/-!
# The union of two adjacent subchains (the setting of Chazelle §3)

Chazelle merges the submaps of two polygonal curves `C₁`, `C₂` "whose union `C` forms a connected
vertex-to-vertex piece of the input" with `C₁ ∩ C₂` a vertex (p. 500).  In the subchain model
(`docs/design-subchain-model.md`) this is a `Junction`: a polygon `P`, a start index `s` and two
lengths `m₁, m₂ ≥ 1` with `m₁ + m₂ + 1 ≤ n`; the three chains are

* `J.left  = (P, s, m₁)`       (Chazelle's `C₁`),
* `J.right = (P, s + m₁, m₂)`  (Chazelle's `C₂`),
* `J.whole = (P, s, m₁ + m₂)`  (Chazelle's `C`),

sharing the vertex `J.shared = left.vertex m₁ = right.vertex 0 = whole.vertex m₁`.  All three
chains have the same box (`radius = coordBound P + 1` depends only on `P`) but in general
different slits.

## Main results

* `whole_set : whole.set = left.set ∪ right.set`; with a simple polygon,
  `left_inter_right : left.set ∩ right.set = {shared}`.
* **The slit is invisible to chords.**  For a point `v` at height `≤ C.top.2` (in particular for
  every chain vertex) the hit set of the horizontal ray from `v` does not see the slit:
  `hitSet_eq_rayHitSet : C.hitSet v σ = rayHitSet C.radius C.set v σ`, where `rayHitSet r A v σ`
  is the slit-free hit set of the obstacle `A` inside the open box of half-side `r`
  (`chordParam_eq_rayHit`).  So chord sets do not depend on which topmost vertex carries the
  slit.
* **Chord truncation** (`whole_chordParam_left`, `whole_chordParam_right`): for a vertex `k` of
  `C₁`,
  `whole.chordParam k σ = min (left.chordParam k σ) (rayHit R right.set (left.vertex k) σ)` —
  the chord of `C` from `v` is the chord of `C₁` from `v` truncated at its first point on `C₂`
  (`whole_chordSet_left`, `whole_chordSet_subset_left`, `whole_chordSet_eq_left`,
  `whole_chordEnd_mem_right`).  Symmetrically for the vertices of `C₂`.
* **Free directions** (`whole_dirFree_left_iff`): a direction is free for `C` at a vertex of
  `C₁` iff it is free for `C₁` and the ray does not start along `C₂`; the second condition is
  automatic except at the shared vertex (`whole_dirFree_left_iff_of_lt`), where it is freeness
  for `C₂` (`whole_dirFree_shared_iff`).
* **The chords of the union** (`whole_chords_eq`): `C.chords` is the set of truncations of the
  `C₁`-chords at `C₂` together with the truncations of the `C₂`-chords at `C₁`, over the
  directions that are free for `C`.
-/

namespace Chazelle.Merge

@[expose] public section

open Set Filter Topology
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
  sInf (rayHitSet r A v σ)

/-- The hit set is bounded below by `0`. -/
theorem rayHitSet_bddBelow (r : ℝ) (A : Set Point) (v : Point) (σ : ℝ) :
    BddBelow (rayHitSet r A v σ) :=
  ⟨0, fun _ ht => ht.1.le⟩

/-- A horizontal ray eventually leaves every box. -/
theorem rayHitSet_nonempty (r : ℝ) (A : Set Point) (v : Point) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    (rayHitSet r A v σ).Nonempty := by
  refine ⟨|r| + |v.1| + 1, ⟢, Or.inl ?_⟩
  intro hbox
  have hx := abs_lt.1 hbox.1
  simp only [rayPt_fst] at hx
  have h1 := le_abs_self r
  have h2 := neg_abs_le v.1
  have h3 := le_abs_self v.1
  rcases hσ with rfl | rfl
  · linarith [hx.2]
  · linarith [hx.1]

/-- The first hit is at or before every hit. -/
theorem rayHit_le {r : ℝ} {A : Set Point} {v : Point} {σ t : ℝ} (ht : t ∈ rayHitSet r A v σ) :
    rayHit r A v σ ≤ t :=
  csInf_le (rayHitSet_bddBelow r A v σ) ht

/-- The hit set of a union is the union of the hit sets. -/
theorem rayHitSet_union (r : ℝ) (A B : Set Point) (v : Point) (σ : ℝ) :
    rayHitSet r (A ∪ B) v σ = rayHitSet r A v σ ∪ rayHitSet r B v σ := by
  ext t
  ϴ rayHitSet, mem_ofPred_eq, mem_union
  tauto

/-- **First hit against a union**: the ray hits `A ∪ B` first at the earlier of its first hits
of `A` and of `B`. -/
theorem rayHit_union (r : ℝ) (A B : Set Point) (v : Point) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    rayHit r (A ∪ B) v σ = min (rayHit r A v σ) (rayHit r B v σ) := by
  unfold rayHit
  Ξ rayHitSet_union
  exact csInf_union (rayHitSet_bddBelow r A v σ) (rayHitSet_nonempty r A v hσ)
    (rayHitSet_bddBelow r B v σ) (rayHitSet_nonempty r B v hσ)

/-- A larger obstacle is hit earlier. -/
theorem rayHit_anti {r : ℝ} {A B : Set Point} (hAB : A ⊆ B) (v : Point) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) : rayHit r B v σ ≤ rayHit r A v σ :=
  csInf_le_csInf (rayHitSet_bddBelow r B v σ) (rayHitSet_nonempty r A v hσ)
    fun _ ht => ⟨ht.1, ht.2.imp id fun h => hAB h⟩

/-- If the open stretch `(0, t₀)` of the ray is in the box and off `A`, the first hit is at or
after `t₀`. -/
theorem le_rayHit {r : ℝ} {A : Set Point} {v : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {t₀ : ℝ}
    (h : ∀ t, 0 < t → t < t₀ → rayPt v σ t ∈ Chain.box r ∧ rayPt v σ t ∉ A) :
    t₀ ≤ rayHit r A v σ := by
  refine le_csInf (rayHitSet_nonempty r A v hσ) fun t ht => ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨h1, h2⟩ := h t ht.1 hlt
  rcases ht.2 with h3 | h3
  · exact h3 h1
  · exact h2 h3

/-- **The first hit.**  Every point of the ray strictly before the first hit is in the box and
off `A`; if the first-hit parameter is positive, the first-hit point is outside the box or on
`A` (for closed `A`). -/
theorem rayHit_spec {r : ℝ} {A : Set Point} (hA : IsClosed A) (v : Point) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    (∀ t, 0 < t → t < rayHit r A v σ → rayPt v σ t ∈ Chain.box r ∧ rayPt v σ t ∉ A) ∧
      (0 < rayHit r A v σ →
        rayPt v σ (rayHit r A v σ) ∉ Chain.box r ∨ rayPt v σ (rayHit r A v σ) ∈ A) := by
  have hne := rayHitSet_nonempty r A v hσ
  have hbdd := rayHitSet_bddBelow r A v σ
  refine ⟨fun t ht1 ht2 => ?_, fun hpos => ?_⟩
  · by_contra hc
    have hmem : t ∈ rayHitSet r A v σ := by
      refine ⟨ht1, ?_⟩
      by_cases hb : rayPt v σ t ∈ Chain.box r
      · right
        by_contra hA'
        exact hc ⟨hb, hA'⟩
      · exact Or.inl hb
    exact absurd (rayHit_le hmem) (not_le.2 ht2)
  · have hset : rayHitSet r A v σ =
        Ici (rayHit r A v σ) ∩ rayPt v σ ⁻¹' ((Chain.box r)ᶜ ∪ A) := by
      ext t
      constructor
      · intro ht
        exact ⟨rayHit_le ht, ht.2⟩
      · rintro ⟨ht1, ht2⟩
        exact ⟨lt_of_lt_of_le hpos ht1, ht2⟩
    have hclosed : IsClosed (rayHitSet r A v σ) := by
      Ξ hset
      exact isClosed_Ici.inter
        (((Chain.isOpen_box r).isClosed_compl.union hA).preimage (continuous_rayPt v σ))
    exact (hclosed.csInf_mem hne hbdd).2

/-! ### The slit is invisible to horizontal rays below the top -/

/-- At a height `≤ C.top.2`, a point is outside the domain iff it is outside the box or on the
chain: the slit plays no role. -/
theorem not_mem_dom_iff (C : Chain) {p : Point} (hp : p.2 ≤ C.top.2) :
    p ∉ C.dom ↔ p ∉ Chain.box C.radius ∨ p ∈ C.set := by
  Ξ C.mem_dom_iff
  constructor
  · intro h
    by_cases hb : p ∈ Chain.box C.radius
    · right
      by_contra hs
      apply h
      refine ⟨hb, hs, fun hsl => hs ?_⟩
      obtain ⟨h1, h2, -⟩ := C.mem_slit_iff.1 hsl
      have : p = C.top := Prod.ext h1 (le_antisymm hp h2)
      Ξ this
      exact C.top_mem_set
    · exact Or.inl hb
  · rintro (h | h) ⟨h1, h2, -⟩
    · exact h h1
    · exact h2 h

/-- **The slit is invisible.**  For a point `v` at height `≤ C.top.2`, the hit set of the
horizontal ray from `v` (defined with the slit) equals the slit-free hit set of the chain. -/
theorem hitSet_eq_rayHitSet (C : Chain) {v : Point} (hv : v.2 ≤ C.top.2) (σ : ℝ) :
    C.hitSet v σ = rayHitSet C.radius C.set v σ := by
  ext t
  ϴ Chain.hitSet, rayHitSet, mem_ofPred_eq, mem_compl_iff
  Ξ not_mem_dom_iff C (by rw [rayPt_snd]; exact hv)

/-- The first-hit parameter of a chain ignores the slit below the top. -/
theorem hitParam_eq_rayHit (C : Chain) {v : Point} (hv : v.2 ≤ C.top.2) (σ : ℝ) :
    C.hitParam v σ = rayHit C.radius C.set v σ := by
  unfold Chain.hitParam rayHit
  Ξ hitSet_eq_rayHitSet C hv

/-- First-hit parameters are nonnegative. -/
theorem hitParam_nonneg (C : Chain) (v : Point) (σ : ℝ) : 0 ≤ C.hitParam v σ :=
  Real.sInf_nonneg fun _ ht => ht.1.le

/-- Two vertices of a chain of a simple polygon coincide only if their indices do. -/
theorem vertex_inj (C : Chain) (hP : C.P.Simple) {a b : ℕ} (ha : a ≤ C.m) (hb : b ≤ C.m)
    (h : C.vertex a = C.vertex b) : a = b := by
  have hm := C.m_lt
  have h1 := simple_vtx_inj hP (C.edgeIdx_lt a) (C.edgeIdx_lt b) h
  have h2 : a ≡ b [MOD C.P.n] := Nat.ModEq.add_left_cancel' C.s h1
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt (⋄), Nat.mod_eq_of_lt (by omega)] at h2

/-- Distinct chain edges have distinct indices in the polygon. -/
theorem edgeIdx_inj (C : Chain) {a b : ℕ} (ha : a < C.P.n) (hb : b < C.P.n)
    (h : C.edgeIdx a = C.edgeIdx b) : a = b := by
  have h2 : a ≡ b [MOD C.P.n] := Nat.ModEq.add_left_cancel' C.s h
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2

/-- A point common to two chain edges `a ≠ b` of a simple polygon is a common vertex. -/
theorem mem_chainEdge_inter (C : Chain) (hP : C.P.Simple) {a b : ℕ} (ha : a < C.P.n)
    (hb : b < C.P.n) (hab : a ≠ b) {p : Point} (hpa : p ∈ C.chainEdge a)
    (hpb : p ∈ C.chainEdge b) :
    (p = C.vertex a ∨ p = C.vertex (a + 1)) ∧ (p = C.vertex b ∨ p = C.vertex (b + 1)) := by
  have hne : C.edgeIdx a ≠ C.edgeIdx b := fun h => hab (edgeIdx_inj C ha hb h)
  have hmem : p ∈ C.P.edge (C.edgeIdx a) ∩ C.P.edge (C.edgeIdx b) := ⟨hpa, hpb⟩
  rw [simple_edge_inter hP (C.edgeIdx_lt a) (C.edgeIdx_lt b) hne] at hmem
  obtain ⟨h1, h2⟩ := hmem
  rw [C.edgeIdx_succ] at h1 h2
  exact ⟨h1, h2⟩

/-! ### Horizontal rays: elementary facts -/

/-- An initial piece of a horizontal segment from `v` is contained in a longer one. -/
theorem segment_rayPt_subset (v : Point) (σ : ℝ) {t t' : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t') :
    Chazelle.segment v (rayPt v σ t) ⊆ Chazelle.segment v (rayPt v σ t') := by
  apply Geometry.segment_subset_of_convex (Geometry.segment_convex _ _)
    (Geometry.left_mem_segment _ _)
  rcases (ht.trans htt').lt_or_eq with hpos | h0
  · refine ⟨t / t', div_nonneg ht hpos.le, (div_le_one hpos).2 htt', ?_⟩
    refine Prod.ext ?_ ?_
    · ϴ rayPt_fst
      field_simp
      ring
    · ϴ rayPt_snd, sub_self, mul_zero, add_zero
  · have ht0 : t = 0 := le_antisymm (h0 ▸ htt') ht
    Ξ ht0, rayPt_zero
    exact Geometry.left_mem_segment _ _

/-- The initial part of a ray from a point off a closed set avoids the set. -/
theorem eventually_not_mem_of_not_mem {A : Set Point} (hA : IsClosed A) {v : Point}
    (hv : v ∉ A) (σ : ℝ) : ∀ᶠ t in 𝓝[>] (0 : ℝ), rayPt v σ t ∉ A := by
  have hcont : ContinuousAt (rayPt v σ) 0 := (continuous_rayPt v σ).continuousAt
  have hmem : Aᶜ ∈ 𝓝 (rayPt v σ 0) := by
    rw [rayPt_zero]; exact hA.isOpen_compl.mem_nhds hv
  exact nhdsWithin_le_nhds (hcont.preimage_mem_nhds hmem)

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

@[simp] theorem left_P : J.left.P = J.P := rfl
@[simp] theorem right_P : J.right.P = J.P := rfl
@[simp] theorem whole_P : J.whole.P = J.P := rfl
@[simp] theorem left_m : J.left.m = J.m₁ := rfl
@[simp] theorem right_m : J.right.m = J.m₂ := rfl
@[simp] theorem whole_m : J.whole.m = J.m₁ + J.m₂ := rfl

/-- The shared vertex `C₁ ∩ C₂`. -/
def shared : Point := J.left.vertex J.m₁

/-- The vertices of `C₁` are the first vertices of `C`. -/
theorem whole_vertex (k : ℕ) : J.whole.vertex k = J.left.vertex k := rfl

/-- Vertex `m₁ + j` of `C` is vertex `j` of `C₂`. -/
theorem whole_vertex_add (j : ℕ) : J.whole.vertex (J.m₁ + j) = J.right.vertex j := by
  show J.P.vtx ((J.s + (J.m₁ + j)) % J.P.n) = J.P.vtx ((J.s + J.m₁ + j) % J.P.n)
  Ξ Nat.add_assoc

/-- The first vertex of `C₂` is the shared vertex. -/
theorem right_vertex_zero : J.right.vertex 0 = J.shared := by
  show J.P.vtx ((J.s + J.m₁ + 0) % J.P.n) = J.P.vtx ((J.s + J.m₁) % J.P.n)
  Ξ Nat.add_zero

/-- Vertex `m₁` of `C` is the shared vertex. -/
theorem whole_vertex_m₁ : J.whole.vertex J.m₁ = J.shared := rfl

/-- Edge `m₁ + j` of `C` is edge `j` of `C₂`. -/
theorem whole_chainEdge_add (j : ℕ) : J.whole.chainEdge (J.m₁ + j) = J.right.chainEdge j := by
  show J.P.edge ((J.s + (J.m₁ + j)) % J.P.n) = J.P.edge ((J.s + J.m₁ + j) % J.P.n)
  Ξ Nat.add_assoc

/-- **The union of the two chains.** -/
theorem whole_set : J.whole.set = J.left.set ∪ J.right.set := by
  ext p
  constructor
  · rintro ⟨k, hk, hp⟩
    rw [whole_m] at hk
    by_cases hk1 : k < J.m₁
    · exact Or.inl ⟨k, hk1, hp⟩
    · right
      refine ⟨k - J.m₁, by rw [right_m]; omega, ?_⟩
      have hk' : k = J.m₁ + (k - J.m₁) := ⋄
      rw [hk', whole_chainEdge_add] at hp
      exact hp
  · rintro (⟨k, hk, hp⟩ | ⟨j, hj, hp⟩)
    · exact ⟨k, by rw [whole_m]; rw [left_m] at hk; omega, hp⟩
    · refine ⟨J.m₁ + j, by rw [whole_m]; rw [right_m] at hj; omega, ?_⟩
      Ξ whole_chainEdge_add
      exact hp

/-- `C₁ ⊆ C`. -/
theorem left_set_subset : J.left.set ⊆ J.whole.set := by
  rw [whole_set]; exact subset_union_left

/-- `C₂ ⊆ C`. -/
theorem right_set_subset : J.right.set ⊆ J.whole.set := by
  rw [whole_set]; exact subset_union_right

/-- The shared vertex is on `C₁`. -/
theorem shared_mem_left : J.shared ∈ J.left.set := J.left.vertex_mem_set le_rfl

/-- The shared vertex is on `C₂`. -/
theorem shared_mem_right : J.shared ∈ J.right.set := by
  rw [← right_vertex_zero]; exact J.right.vertex_mem_set (Nat.zero_le _)

/-- The top of `C₁` is not above the top of `C`. -/
theorem left_top_le : J.left.top.2 ≤ J.whole.top.2 :=
  J.whole.vertex_snd_le_top (j := J.left.topIdx) (by rw [whole_m]; have := J.left.topIdx_le; rw [left_m] at this; omega)

/-- The top of `C₂` is not above the top of `C`. -/
theorem right_top_le : J.right.top.2 ≤ J.whole.top.2 := by
  have h := J.whole.vertex_snd_le_top (j := J.m₁ + J.right.topIdx)
    (by rw [whole_m]; have := J.right.topIdx_le; rw [right_m] at this; omega)
  rw [whole_vertex_add] at h
  exact h

/-- **The two chains meet exactly in the shared vertex** (for a simple polygon). -/
theorem left_inter_right (hP : J.P.Simple) : J.left.set ∩ J.right.set = {J.shared} := by
  apply Subset.antisymm
  · rintro p ⟨⟨k, hk, hpk⟩, ⟨j, hj, hpj⟩⟩
    rw [left_m] at hk
    rw [right_m] at hj
    have hn := J.add_le
    have hpk' : p ∈ J.whole.chainEdge k := hpk
    have hpj' : p ∈ J.whole.chainEdge (J.m₁ + j) := by rw [whole_chainEdge_add]; exact hpj
    have hwP : J.whole.P.Simple := hP
    obtain ⟨h1, h2⟩ := mem_chainEdge_inter J.whole hwP (a := k) (b := J.m₁ + j)
      (by show k < J.P.n; omega) (by show J.m₁ + j < J.P.n; omega) (by omega) hpk' hpj'
    have hinj : ∀ a b, a ≤ J.m₁ + J.m₂ → b ≤ J.m₁ + J.m₂ → J.whole.vertex a = J.whole.vertex b →
        a = b := fun a b ha hb h => vertex_inj J.whole hwP ha hb h
    rw [mem_singleton_iff]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · have := hinj _ _ (by omega) (by omega) (h1.symm.trans h2); omega
    · have := hinj _ _ (by omega) (by omega) (h1.symm.trans h2); omega
    · have := hinj _ _ (by omega) (by omega) (h1.symm.trans h2)
      rw [h1, show k + 1 = J.m₁ by omega]
      rfl
    · have := hinj _ _ (by omega) (by omega) (h1.symm.trans h2); omega
  · rintro p rfl
    exact ⟨J.shared_mem_left, J.shared_mem_right⟩

/-- A vertex of `C₂` other than the shared one is not on `C₁`. -/
theorem right_vertex_not_mem_left (hP : J.P.Simple) {j : ℕ} (hj0 : 0 < j) (hj : j ≤ J.m₂) :
    J.right.vertex j ∉ J.left.set := by
  intro h
  have hmem : J.right.vertex j ∈ J.left.set ∩ J.right.set :=
    ⟨h, J.right.vertex_mem_set (by rw [right_m]; omega)⟩
  rw [J.left_inter_right hP, mem_singleton_iff, ← right_vertex_zero] at hmem
  have := vertex_inj J.right hP (a := j) (b := 0) (by rw [right_m]; omega)
    (Nat.zero_le _) hmem
  omega

/-! ### Chord truncation -/

/-! ### Free directions -/

/-! ### The chords of the union -/

end Junction

end

end Chazelle.Merge
