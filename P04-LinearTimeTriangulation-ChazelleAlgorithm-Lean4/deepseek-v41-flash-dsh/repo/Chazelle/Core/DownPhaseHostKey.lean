module

public import Chazelle.Golf

public import Chazelle.Core.FactsInterior

/-!
# WP-M (H1, part 1): a simplicity criterion for polygons inscribed in a simple walk by keys

The down phase merges on host polygons `R*`, the boundaries of the regions of an interior submap
(design `docs/design-downphase.md` §2.3 (a)).  Their simplicity (obligation H1) is reduced here to
bookkeeping on **keys** of the boundary walk `W` of `Q` (`key = edge + parameter`):

* every vertex `V i` of the host lies on the walk `W`, at position `(pp i, tt i)`, and the keys
  `κ i = pp i + tt i` are **strictly increasing** in `i` (the host starts at its smallest key);
* every edge `[V i, V (i+1)]` is either an **arc edge** (all its points are walk points whose key
  lies in the closed key interval `[κ i, κ (i+1)]`, wrapping around for the last edge), or a
  **chord edge** (its open part lies in a set `D` disjoint from the walk);
* the open parts of two distinct chord edges are disjoint.

`simple_of_keys`: such a polygon is simple.  The proof: a common point of two edges off `D` is a
walk point, at a single position (`FactsInterior.pos_unique`), whose key lies in both closed key
intervals; strictly increasing keys make two such intervals meet only in a shared end key, hence
the point is a shared vertex.  A common point in `D` would lie in the open parts of two chord
edges.
-/

namespace Chazelle.Core

namespace DownHost

@[expose] public section

open Set
open Chazelle.Chain (sidePt)
open Chazelle.Geometry (lerp lerp_zero lerp_one lerp_mem_segment)

/-- **Keys determine positions**: `p + t = p' + t'` with `t, t' ∈ [0, 1)` forces `p = p'` and
`t = t'`. -/
theorem key_inj {p p' : ℕ} {t t' : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (h : (p : ℝ) + t = p' + t') : p = p' ∧ t = t' := by
  have h1 : (p : ℝ) < p' + 1 := ⟡
  have h2 : (p' : ℝ) < p + 1 := ⟡
  have h1' : p < p' + 1 := by exact_mod_cast h1
  have h2' : p' < p + 1 := by exact_mod_cast h2
  have hpp : p = p' := ⋄
  subst hpp
  exact ⟨rfl, ⟡⟩

/-- The closed key interval of host edge `i` (of `N` edges, keys `κ`): `[κ i, κ (i+1)]`, and for
the last edge the wrapped interval `[κ (N-1), ∞) ∪ (-∞, κ 0]`. -/
def InKeyIv (κ : ℕ → ℝ) (N i : ℕ) (x : ℝ) : Prop :=
  if i + 1 < N then κ i ≤ x ∧ x ≤ κ (i + 1) else κ i ≤ x ∨ x ≤ κ 0

/-- **Two closed key intervals of distinct edges meet only in a shared end key.** -/
theorem inKeyIv_inter {κ : ℕ → ℝ} {N i j : ℕ} (hmono : ∀ a b, a < b → b < N → κ a < κ b)
    (hi : i < N) (hj : j < N) (hij : i ≠ j) {x : ℝ} (hxi : InKeyIv κ N i x)
    (hxj : InKeyIv κ N j x) :
    ∃ k, k < N ∧ (k = i ∨ k = (i + 1) % N) ∧ (k = j ∨ k = (j + 1) % N) ∧ x = κ k := by
  -- strict monotonicity turns key comparisons into index comparisons
  have hle : ∀ a b, a < N → b < N → κ a ≤ κ b → a ≤ b := by
    intro a b ha hb hab
    by_contra h
    have := hmono b a (by omega) ha
    linarith
  have hN0 : 0 < N := by omega
  unfold InKeyIv at hxi hxj
  -- wlog-free case analysis
  by_cases hi1 : i + 1 < N <;> by_cases hj1 : j + 1 < N <;>
    simp only [hi1, hj1, ↓reduceIte] at hxi hxj
  · -- both unwrapped
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · -- i < j: κ i ≤ x ≤ κ (i+1) ≤ κ j ≤ x
      have h1 := hle j (i + 1) hj hi1 (le_trans hxj.1 hxi.2)
      have hji : j = i + 1 := by omega
      subst hji
      refine ⟨i + 1, hi1, Or.inr (Nat.mod_eq_of_lt hi1).symm, Or.inl rfl, ?_⟩
      exact le_antisymm hxi.2 hxj.1
    · have h1 := hle i (j + 1) hi hj1 (le_trans hxi.1 hxj.2)
      have hji : i = j + 1 := by omega
      subst hji
      refine ⟨j + 1, hj1, Or.inl rfl, Or.inr (Nat.mod_eq_of_lt hj1).symm, ?_⟩
      exact le_antisymm hxj.2 hxi.1
  · -- j is the last edge
    have hjN : j = N - 1 := by omega
    have hsj : (j + 1) % N = 0 := by rw [show j + 1 = N by omega, Nat.mod_self]
    rcases hxj with h | h
    · have h1 := hle j (i + 1) hj hi1 (le_trans h hxi.2)
      have hji : j = i + 1 := by omega
      refine ⟨j, hj, Or.inr ?_, Or.inl rfl, le_antisymm (hji ▸ hxi.2) h⟩
      rw [hji, Nat.mod_eq_of_lt hi1]
    · have h1 := hle i 0 hi hN0 (le_trans hxi.1 h)
      have hi0 : i = 0 := by omega
      subst hi0
      exact ⟨0, hN0, Or.inl rfl, Or.inr hsj.symm, le_antisymm h hxi.1⟩
  · -- i is the last edge
    have hsi : (i + 1) % N = 0 := by rw [show i + 1 = N by omega, Nat.mod_self]
    rcases hxi with h | h
    · have h1 := hle i (j + 1) hi hj1 (le_trans h hxj.2)
      have hij' : i = j + 1 := by omega
      refine ⟨i, hi, Or.inl rfl, Or.inr ?_, le_antisymm (hij' ▸ hxj.2) h⟩
      rw [hij', Nat.mod_eq_of_lt hj1]
    · have h1 := hle j 0 hj hN0 (le_trans hxj.1 h)
      have hj0 : j = 0 := by omega
      subst hj0
      exact ⟨0, hN0, Or.inr hsi.symm, Or.inl rfl, le_antisymm h hxj.1⟩
  · exact absurd (by omega : i = j) hij

variable (W : Polygon) (D : Set Point) (V : List Point) (pp : ℕ → ℕ) (tt : ℕ → ℝ)

/-- The key of host vertex `i`. -/
def keyOf (i : ℕ) : ℝ := (pp i : ℝ) + tt i

/-- Host edge `i` is an **arc edge**: all its points are walk points with keys in the closed
key interval of the edge. -/
def ArcEdge (i : ℕ) : Prop :=
  ∀ z ∈ Chazelle.segment (V.getD i (0, 0)) (V.getD ((i + 1) % V.length) (0, 0)),
    ∃ p, p < W.n ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ z = sidePt W p t ∧
      InKeyIv (keyOf pp tt) V.length i ((p : ℝ) + t)

/-- Host edge `i` is a **chord edge**: its open part lies in `D`. -/
def ChordEdge (i : ℕ) : Prop :=
  ∀ s : ℝ, 0 < s → s < 1 → lerp (V.getD i (0, 0)) (V.getD ((i + 1) % V.length) (0, 0)) s ∈ D

/-- **The data of a host polygon inscribed by keys** (see the module docstring). -/
structure KeyHost : Prop where
  three : 3 ≤ V.length
  wsimple : W.Simple
  pos_lt : ∀ i, i < V.length → pp i < W.n
  t_nonneg : ∀ i, i < V.length → 0 ≤ tt i
  t_lt : ∀ i, i < V.length → tt i < 1
  vtx_eq : ∀ i, i < V.length → V.getD i (0, 0) = sidePt W (pp i) (tt i)
  mono : ∀ i j, i < j → j < V.length → keyOf pp tt i < keyOf pp tt j
  disj : ∀ z ∈ D, z ∉ W.boundary
  edges : ∀ i, i < V.length → ArcEdge W V pp tt i ∨ ChordEdge D V i
  chord_disj : ∀ i j, i < V.length → j < V.length → i ≠ j → ChordEdge D V i →
    ChordEdge D V j → ∀ s s' : ℝ, 0 < s → s < 1 → 0 < s' → s' < 1 →
      lerp (V.getD i (0, 0)) (V.getD ((i + 1) % V.length) (0, 0)) s ≠
        lerp (V.getD j (0, 0)) (V.getD ((j + 1) % V.length) (0, 0)) s'

variable {W D V pp tt}

/-- A walk point lies on the walk's boundary. -/
theorem sidePt_mem_boundary {p : ℕ} (hp : p < W.n) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    sidePt W p t ∈ W.boundary :=
  ⟨p, hp, lerp_mem_segment _ _ h0 h1⟩

namespace KeyHost

variable (h : KeyHost W D V pp tt)
include h

theorem vtx_mem_boundary {i : ℕ} (hi : i < V.length) : V.getD i (0, 0) ∈ W.boundary := by
  Ξ h.vtx_eq i hi
  exact sidePt_mem_boundary (h.pos_lt i hi) (h.t_nonneg i hi) (h.t_lt i hi).le

theorem succ_lt {i : ℕ} : (i + 1) % V.length < V.length :=
  Nat.mod_lt _ (by have := h.three; omega)

/-- The key of a vertex lies in the key interval of each edge it ends. -/
theorem inKeyIv_self {i : ℕ} (_hi : i < V.length) :
    InKeyIv (keyOf pp tt) V.length i (keyOf pp tt i) := by
  unfold InKeyIv
  split_ifs with h1
  · exact ⟨le_rfl, (h.mono i (i + 1) (⋄) h1).le⟩
  · exact Or.inl le_rfl

theorem inKeyIv_succ {i : ℕ} (hi : i < V.length) :
    InKeyIv (keyOf pp tt) V.length i (keyOf pp tt ((i + 1) % V.length)) := by
  unfold InKeyIv
  split_ifs with h1
  · rw [Nat.mod_eq_of_lt h1]
    exact ⟨(h.mono i (i + 1) (by omega) h1).le, le_rfl⟩
  · rw [show i + 1 = V.length by omega, Nat.mod_self]
    exact Or.inr le_rfl

/-- **A point of an edge off `D`** is a walk point whose key lies in the edge's interval. -/
theorem pt_key {i : ℕ} (hi : i < V.length) {z : Point}
    (hz : z ∈ Chazelle.segment (V.getD i (0, 0)) (V.getD ((i + 1) % V.length) (0, 0)))
    (hzD : z ∉ D) :
    ∃ p, p < W.n ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ z = sidePt W p t ∧
      InKeyIv (keyOf pp tt) V.length i ((p : ℝ) + t) := by
  rcases h.edges i hi with ha | hc
  · exact ha z hz
  · obtain ⟨s, hs0, hs1, rfl⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hz
    rcases hs0.lt_or_eq with hs0 | hs0
    · rcases hs1.lt_or_eq with hs1 | hs1
      · exact absurd (hc s hs0 hs1) hzD
      · subst hs1
        have hk := h.succ_lt (i := i)
        refine ⟨pp ((i + 1) % V.length), h.pos_lt _ hk, tt ((i + 1) % V.length),
          h.t_nonneg _ hk, h.t_lt _ hk, ?_, h.inKeyIv_succ hi⟩
        Ξ lerp_one, h.vtx_eq _ hk
    · subst hs0
      refine ⟨pp i, h.pos_lt i hi, tt i, h.t_nonneg i hi, h.t_lt i hi, ?_, h.inKeyIv_self hi⟩
      Ξ lerp_zero, h.vtx_eq i hi

/-- A walk point at the key of vertex `k` is vertex `k`. -/
theorem eq_vtx_of_key {k : ℕ} (hk : k < V.length) {p : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hkey : (p : ℝ) + t = keyOf pp tt k) : sidePt W p t = V.getD k (0, 0) := by
  obtain ⟨rfl, rfl⟩ := key_inj ht ht1 (h.t_nonneg k hk) (h.t_lt k hk) hkey
  exact (h.vtx_eq k hk).symm

/-- **The simplicity criterion.** -/
theorem simple : (⟨V⟩ : Polygon).Simple := by
  have hn : (⟨V⟩ : Polygon).n = V.length := rfl
  have hv : ∀ i, (⟨V⟩ : Polygon).vtx i = V.getD i (0, 0) := fun _ => rfl
  refine ⟨h.three, ?_, ?_⟩
  · intro i j hi hj hij
    rw [hv, hv, h.vtx_eq i hi, h.vtx_eq j hj] at hij
    obtain ⟨hp, ht⟩ := FactsInterior.pos_unique h.wsimple (h.pos_lt i hi) (h.pos_lt j hj)
      (h.t_nonneg i hi) (h.t_lt i hi) (h.t_nonneg j hj) (h.t_lt j hj) hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := h.mono i j hlt hj
      unfold keyOf at this; rw [hp, ht] at this; exact lt_irrefl _ this
    · have := h.mono j i hlt hi
      unfold keyOf at this; rw [hp, ht] at this; exact lt_irrefl _ this
  · intro i j hi hj hij
    apply Set.Subset.antisymm
    · rintro z ⟨hzi, hzj⟩
      simp only [Polygon.edge, hn, hv] at hzi hzj
      by_cases hzD : z ∈ D
      · -- both edges are chord edges, and `z` is in both open parts
        exfalso
        have hopen : ∀ k, k < V.length → z ∈ Chazelle.segment (V.getD k (0, 0))
            (V.getD ((k + 1) % V.length) (0, 0)) →
            ChordEdge D V k ∧ ∃ s : ℝ, 0 < s ∧ s < 1 ∧
              z = lerp (V.getD k (0, 0)) (V.getD ((k + 1) % V.length) (0, 0)) s := by
          intro k hk hzk
          have hzb : z ∉ W.boundary := h.disj z hzD
          obtain ⟨s, hs0, hs1, hzs⟩ := Chazelle.Geometry.mem_segment_iff_lerp.1 hzk
          have hs0' : 0 < s := by
            rcases hs0.lt_or_eq with h' | h'
            · exact h'
            · subst h'; rw [lerp_zero] at hzs
              exact absurd (hzs ▸ h.vtx_mem_boundary hk) hzb
          have hs1' : s < 1 := by
            rcases hs1.lt_or_eq with h' | h'
            · exact h'
            · subst h'; rw [lerp_one] at hzs
              exact absurd (hzs ▸ h.vtx_mem_boundary h.succ_lt) hzb
          refine ⟨?_, s, hs0', hs1', hzs⟩
          rcases h.edges k hk with ha | hc
          · obtain ⟨p, hp, t, ht0, ht1, hzp, -⟩ := ha z hzk
            exact absurd (hzp ▸ sidePt_mem_boundary hp ht0 ht1.le) hzb
          · exact hc
        obtain ⟨hci, s, hs0, hs1, hzs⟩ := hopen i hi hzi
        obtain ⟨hcj, s', hs0', hs1', hzs'⟩ := hopen j hj hzj
        exact h.chord_disj i j hi hj hij hci hcj s s' hs0 hs1 hs0' hs1' (hzs.symm.trans hzs')
      · obtain ⟨p, hp, t, ht0, ht1, hzp, hki⟩ := h.pt_key hi hzi hzD
        obtain ⟨p', hp', t', ht0', ht1', hzp', hkj⟩ := h.pt_key hj hzj hzD
        obtain ⟨rfl, rfl⟩ := FactsInterior.pos_unique h.wsimple hp hp' ht0 ht1 ht0' ht1'
          (hzp.symm.trans hzp')
        obtain ⟨k, hk, hki', hkj', hx⟩ := inKeyIv_inter h.mono hi hj hij hki hkj
        have hzk : z = V.getD k (0, 0) := hzp.trans (h.eq_vtx_of_key hk ht0 ht1 hx)
        ϴ Polygon.commonEndpoints, hn, hv
        refine ⟨?_, ?_⟩
        · rcases hki' with rfl | rfl
          · exact Or.inl hzk
          · exact Or.inr hzk
        · rcases hkj' with rfl | rfl
          · exact Or.inl hzk
          · exact Or.inr hzk
    · rintro z ⟨hz1, hz2⟩
      ϴ Polygon.edge, hn, hv
      refine ⟨?_, ?_⟩
      · rcases hz1 with rfl | rfl
        · exact Chazelle.Geometry.left_mem_segment _ _
        · exact Chazelle.Geometry.right_mem_segment _ _
      · rcases hz2 with rfl | rfl
        · exact Chazelle.Geometry.left_mem_segment _ _
        · exact Chazelle.Geometry.right_mem_segment _ _

end KeyHost

end

end DownHost

end Chazelle.Core
