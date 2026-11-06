module

public import Chazelle.Core.FactsAttach
public import Chazelle.Core.ShearInv
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# WP-B: degree `≤ 4` of the full augmented map of the interior (distinct heights)

For a simple polygon `Q` with pairwise distinct vertex heights, every region of the interior
visibility map augmented by any finite family of horizontal interior chords has at most four
exit chords (`FullDegInt.deg_le_four`, `fullDeg_interior`): this is the second conjunct of
`FullDegSpec`.

Proof.  A region `U` lies in a trapezoid `T` of the (vertex-chord) visibility map
(`Visibility.exists_isTrap`, `IsTrap.region_eq`).  A chord touching `U` is at the top height of
`T`, at its bottom height, or crosses `T` (then it contains the whole slice of `T` at its height,
so `U` is entirely above or below it).  At most one crossing chord lies above `U`, and if there is
one no chord at the top height touches `U`; at the top height at most two chords touch `U`,
because two of them on the same side of the unique vertex at that height would be separated by a
boundary point of the open top side, which must be a vertex (a non-vertex boundary point of an
edge crossing the top height would put points of the edge inside `T`).  Symmetrically below.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (IsHChordIn freeIn regionsIn TouchesIn)
open Chazelle.Jordan (exists_openEdge_of_mem_boundary simple_three_le succIdx_ne)
open Chazelle.Visibility (hseg trapSet closedTrap IsTrap edgeX chords freeRegion chordUnion)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext lerp_mem_segment)

namespace FullDegInt

variable {Q : Polygon}

/-- A horizontal chord of the interior of `Q`. -/
def HC (Q : Polygon) (c : Set Point) : Prop :=
  ∃ y a b : ℝ, IsHChordIn (Q.filled \ Q.boundary) y a b ∧ c = hseg y a b

theorem hc_full (hQ : Q.Simple) {c : Set Point} (hc : c ∈ chords Q) : HC Q c := by
  obtain ⟨i, σ, -, -, -, rfl, h⟩ := Visibility.chords_spec hQ hc
  exact ⟨_, _, _, ⟨h.lt, fun hm => hm.2 h.left_mem, fun hm => hm.2 h.right_mem, h.open_int⟩,
    Visibility.chordSet_eq_hseg _ _ _⟩

/-- A point of a chord in the domain is strictly inside it. -/
theorem open_of_mem {y a b : ℝ} (h : IsHChordIn (Q.filled \ Q.boundary) y a b) {z : Point}
    (hz : z ∈ hseg y a b) (hzD : z ∈ Q.filled \ Q.boundary) : a < z.1 ∧ z.1 < b := by
  obtain ⟨hzy, hza, hzb⟩ := hz
  refine ⟨lt_of_le_of_ne hza fun e => h.left_not ?_, lt_of_le_of_ne hzb fun e => h.right_not ?_⟩
  · have : ((a, y) : Point) = z := point_ext e hzy.symm
    rwx [this]
  · have : ((b, y) : Point) = z := point_ext e.symm hzy.symm
    rwx [this]

/-- Two chords sharing a point of the domain are equal. -/
theorem eq_of_common {c c' : Set Point} (hc : HC Q c) (hc' : HC Q c') {z : Point} (hz : z ∈ c)
    (hz' : z ∈ c') (hzD : z ∈ Q.filled \ Q.boundary) : c = c' := by
  obtain ⟨y, a, b, h, rfl⟩ := hc
  obtain ⟨y', a', b', h', rfl⟩ := hc'
  rcases Chazelle.Chain.hchordIn_inter h h' hz hz' with ⟨rfl, rfl, rfl⟩ | ⟨h1 | h1, -⟩
  · rfl
  · exact absurd (h1 ▸ hzD) h.left_not
  · exact absurd (h1 ▸ hzD) h.right_not

/-- **A chord contains every point of its line joined to it inside the domain.** -/
theorem mem_of_joined {y a b : ℝ} (h : IsHChordIn (Q.filled \ Q.boundary) y a b) {z : Point}
    (hz : z ∈ hseg y a b) (hzD : z ∈ Q.filled \ Q.boundary) {w : Point} (hw : w.2 = y)
    (hj : ∀ s : ℝ, min z.1 w.1 ≤ s → s ≤ max z.1 w.1 → ((s, y) : Point) ∈ Q.filled \ Q.boundary) :
    w ∈ hseg y a b := by
  obtain ⟨hza, hzb⟩ := open_of_mem h hz hzD
  refine ⟨hw, ?_, ?_⟩
  · by_contra hwa
    push Not at hwa
    exact h.left_not (hj a (by have := min_le_right z.1 w.1; linarith) (by
      have := le_max_left z.1 w.1; linarith))
  · by_contra hwb
    push Not at hwb
    exact h.right_not (hj b (by have := min_le_left z.1 w.1; linarith) (by
      have := le_max_right z.1 w.1; linarith))

/-- The points of a chord between two of its domain points are in the domain. -/
theorem between_mem {y a b : ℝ} (h : IsHChordIn (Q.filled \ Q.boundary) y a b) {z z' : Point}
    (hz : z ∈ hseg y a b) (hzD : z ∈ Q.filled \ Q.boundary) (hz' : z' ∈ hseg y a b)
    (hz'D : z' ∈ Q.filled \ Q.boundary) {s : ℝ} (h1 : z.1 ≤ s) (h2 : s ≤ z'.1) :
    ((s, y) : Point) ∈ Q.filled \ Q.boundary :=
  h.open_mem s (by linarith [(open_of_mem h hz hzD).1]) (by linarith [(open_of_mem h hz' hz'D).2])

/-- **A boundary point near which the points on one side (`τ = ±1`) are in the domain is a
vertex**, for a polygon with distinct heights. -/
theorem vertex_of_side (hQ : Q.Simple) (hDH : DistinctHeights Q) {w : Point}
    (hw : w ∈ Q.boundary) {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hnear : ∀ᶠ p' in 𝓝 w, 0 < τ * (p'.2 - w.2) → p' ∈ Q.filled \ Q.boundary) :
    ∃ m < Q.n, w = Q.vtx m := by
  by_contra hno
  push Not at hno
  obtain ⟨e, he, t, ht, rfl⟩ := exists_openEdge_of_mem_boundary Q hw hno
  set u := Q.vtx e
  set v := Q.vtx ((e + 1) % Q.n)
  have hn := simple_three_le hQ
  have huv : u.2 ≠ v.2 := hDH e _ he (Nat.mod_lt _ (by omega)) (succIdx_ne Q hn he).symm
  have hd  := sub_ne_zero.2 (Ne.symm huv)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hnear
  set L := dist u v + 1 with hL
  have hL0 : 0 < L := by positivity
  set δ := min (min t (1 - t)) (ε / L) / 2 with hδ
  have hδ0 : 0 < δ := by
    rw [hδ]; have := lt_min (lt_min ht.1 (sub_pos.2 ht.2)) (div_pos hε hL0); linarith
  have hδm : δ < min (min t (1 - t)) (ε / L) := by
    rw [hδ]; have := lt_min (lt_min ht.1 (sub_pos.2 ht.2)) (div_pos hε hL0); linarith
  have hδt : δ < t := hδm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδt' : δ < 1 - t := hδm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδε : δ * L < ε := by
    have := hδm.trans_le (min_le_right _ _); rwa [lt_div_iff₀ hL0] at this
  -- the direction along the edge that moves to the side `τ`
  set σ : ℝ := if 0 < τ * (v.2 - u.2) then 1 else -1 with hσ
  have hσ1 : σ = 1 ∨ σ = -1 := by rw [hσ]; split_ifs <;> simp
  have hσpos : 0 < τ * (σ * (v.2 - u.2)) := by
    rw [hσ]
    have hτd : τ * (v.2 - u.2) ≠ 0 := mul_ne_zero (by rcases hτ with rfl | rfl <;> norm_num) hd
    split_ifs with h
    · linarith
    · have : τ * (v.2 - u.2) < 0 := lt_of_le_of_ne (not_lt.1 h) hτd
      nlinarith
  set s := t + σ * δ with hs
  have hs0 : 0 ≤ s := by rcases hσ1 with h | h <;> rw [hs, h] <;> linarith
  have hs1 : s ≤ 1 := by rcases hσ1 with h | h <;> rw [hs, h] <;> linarith
  have hpt : lerp u v s ∈ Q.boundary := ⟨e, he, lerp_mem_segment _ _ hs0 hs1⟩
  apply (hball ?_ ?_).2 hpt
  · rw [dist_eq_norm]
    have : lerp u v s - lerp u v t = (σ * δ) • (v - u) := by
      apply point_ext <;> simp [lerp, hs] <;> ring
    rw [this, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hδ0, ← dist_eq_norm, dist_comm]
    have : |σ| = 1 := by rcases hσ1 with h | h <;> rw [h] <;> norm_num
    rw [this, one_mul]
    calc δ * dist u v ≤ δ * L := by rwnl [hL]
      _ < ε := hδε
  · simp only [lerp_snd, hs]
    have : u.2 + (t + σ * δ) * (v.2 - u.2) - (u.2 + t * (v.2 - u.2)) =
        δ * (σ * (v.2 - u.2)) := by ring
    rw [this]
    nlinarith

/-- A vertex at a given height is unique. -/
theorem vtx_eq_of_height (hDH : DistinctHeights Q) {m k : ℕ} (hm : m < Q.n) (hk : k < Q.n)
    (h : (Q.vtx m).2 = (Q.vtx k).2) : m = k := by
  by_contra hne; exact hDH m k hm hk hne h

/-- **Two chords touching a region from one horizontal side of a trapezoid, on the same side of
the vertex at that height, are equal.** -/
theorem side_chords_eq (hQ : Q.Simple) (hDH : DistinctHeights Q) {T : Set Point}
    (hT : T ⊆ Q.filled \ Q.boundary) {y₀ xl xr : ℝ} {τ : ℝ} (hτ : τ = 1 ∨ τ = -1)
    (hcl : ∀ x, xl < x → x < xr → ((x, y₀) : Point) ∈ Q.filled)
    (hnear : ∀ x, xl < x → x < xr →
      ∀ᶠ p' in 𝓝 ((x, y₀) : Point), 0 < τ * (p'.2 - y₀) → p' ∈ T)
    {k₀ : ℕ} (hk₀ : k₀ < Q.n) (hk₀y : (Q.vtx k₀).2 = y₀)
    {c c' : Set Point} (hc : HC Q c) (hc' : HC Q c') {z z' : Point} (hz : z ∈ c) (hz' : z' ∈ c')
    (hzD : z ∈ Q.filled \ Q.boundary) (hz'D : z' ∈ Q.filled \ Q.boundary)
    (hzy : z.2 = y₀) (hz'y : z'.2 = y₀) (hzx : xl ≤ z.1 ∧ z.1 ≤ xr) (hz'x : xl ≤ z'.1 ∧ z'.1 ≤ xr)
    (hside : z.1 < (Q.vtx k₀).1 ↔ z'.1 < (Q.vtx k₀).1) : c = c' := by
  -- ordered version
  have key : ∀ {c c' : Set Point} {z z' : Point}, HC Q c → HC Q c' → z ∈ c → z' ∈ c' →
      z ∈ Q.filled \ Q.boundary → z' ∈ Q.filled \ Q.boundary → z.2 = y₀ → z'.2 = y₀ →
      xl ≤ z.1 → z'.1 ≤ xr → z.1 ≤ z'.1 →
      (z.1 < (Q.vtx k₀).1 ↔ z'.1 < (Q.vtx k₀).1) → c = c' := by
    intro c c' z z' hc hc' hz hz' hzD hz'D hzy hz'y hzl hz'r hle hside
    obtain ⟨y, a, b, h, rfl⟩ := hc
    have hy : y = y₀ := by rw [← hzy, hz.1]
    by_cases hall : ∀ s : ℝ, z.1 ≤ s → s ≤ z'.1 → ((s, y₀) : Point) ∈ Q.filled \ Q.boundary
    · have hz'c : z' ∈ hseg y a b := mem_of_joined h hz hzD (by rw [hz'y, hy]) (fun s h1 h2 => by
        rw [min_eq_left hle] at h1; rw [max_eq_right hle] at h2
        rw [hy]; exact hall s h1 h2)
      exact eq_of_common ⟨y, a, b, h, rfl⟩ hc' hz'c hz' hz'D
    · exfalso
      push Not at hall
      obtain ⟨s, hs1, hs2, hsD⟩ := hall
      have hs1' : z.1 < s := lt_of_le_of_ne hs1 fun e => hsD (by
        rwx [← e, ← hzy])
      have hs2' : s < z'.1 := lt_of_le_of_ne hs2 fun e => hsD (by
        rwx [e, ← hz'y])
      have hsl : xl < s := by linarith
      have hsr : s < xr := by linarith
      have hb : ((s, y₀) : Point) ∈ Q.boundary := by
        by_contra hb; exact hsD ⟨hcl s hsl hsr, hb⟩
      obtain ⟨m, hm, hwm⟩ := vertex_of_side hQ hDH hb hτ
        ((hnear s hsl hsr).mono fun p' hp' hpos => hT (hp' hpos))
      have hmk : m = k₀ := vtx_eq_of_height hDH hm hk₀ (by rw [← hwm, hk₀y])
      subst hmk
      have hsx : s = (Q.vtx m).1 := by rw [← hwm]
      rw [hsx] at hs1' hs2'
      by_cases h1 : z.1 < (Q.vtx m).1
      · have := hside.1 h1; linarith
      · exact h1 hs1'
  rcases le_total z.1 z'.1 with h | h
  · exact key hc hc' hz hz' hzD hz'D hzy hz'y hzx.1 hz'x.2 h hside
  · exact (key hc' hc hz' hz hz'D hzD hz'y hzy hz'x.1 hzx.2 h hside.symm).symm

/-- The side of a chord point relative to a vertex, read off from the chord. -/
theorem side_iff {c : Set Point} (hc : HC Q c) {y₀ : ℝ} {w₀ : Point}
    (hw₀ : w₀ ∉ Q.filled \ Q.boundary) (hw₀y : w₀.2 = y₀) {z : Point} (hz : z ∈ c)
    (hzD : z ∈ Q.filled \ Q.boundary) (hzy : z.2 = y₀) :
    (∃ z' ∈ c, z' ∈ Q.filled \ Q.boundary ∧ z'.2 = y₀ ∧ z'.1 < w₀.1) ↔ z.1 < w₀.1 := by
  obtain ⟨y, a, b, h, rfl⟩ := hc
  have hy : y = y₀ := by rw [← hzy, hz.1]
  constructor
  · rintro ⟨z', hz', hz'D, -, hlt⟩
    by_contra hge
    push Not at hge
    have hne : z.1 ≠ w₀.1 := fun e => hw₀ (by
      have : w₀ = z := point_ext e.symm (hw₀y.trans hzy.symm); rwx [this])
    have := between_mem h hz' hz'D hz hzD hlt.le (lt_of_le_of_ne hge (Ne.symm hne)).le
    apply hw₀
    have e : ((w₀.1, y) : Point) = w₀ := point_ext rfl (by rw [hy, hw₀y])
    rwx [← e]
  · intro hlt; exact ⟨z, hz, hzD, hzy, hlt⟩

/-- **Degree `≤ 4`** in the interior visibility map augmented by finitely many horizontal chords,
for a simple polygon with distinct vertex heights. -/
theorem deg_le_four (hQ : Q.Simple) (hDH : DistinctHeights Q) {G : Set (Set Point)}
    (hG : ∀ c ∈ G, HC Q c) (hGfin : G.Finite) (hfull : chords Q ⊆ G) {U : Set Point}
    (hU : U ∈ regionsIn (Q.filled \ Q.boundary) G) :
    {c | c ∈ G ∧ TouchesIn (Q.filled \ Q.boundary) c U}.ncard ≤ 4 := by
  classical
  set D := Q.filled \ Q.boundary with hD
  obtain ⟨q, hqf, rfl⟩ := hU
  have hfreeR : freeIn D G ⊆ freeRegion Q := fun p hp =>
    ⟨hp.1, fun ⟨c, hc, hpc⟩ => hp.2 ⟨c, hfull hc, hpc⟩⟩
  have hqR := hfreeR hqf
  obtain ⟨i, j, y₁, y₂, h⟩ := Visibility.exists_isTrap hQ hqR
  set T := trapSet Q i j y₁ y₂ with hTdef
  set U := connectedComponentIn (freeIn D G) q with hUdef
  have hUT : U ⊆ T := by
    rw [hTdef, ← h.region_eq hQ hqR]
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hqf) ((connectedComponentIn_subset _ _).trans hfreeR)
  have hTD  := h.trapSet_subset_interior hQ hqR
  have hqT  := hUT (mem_connectedComponentIn hqf)
  have hfreeU : U ⊆ freeIn D G := connectedComponentIn_subset _ _
  have hcl : closure U ⊆ closedTrap Q i j y₁ y₂ :=
    (closure_mono hUT).trans (Visibility.closure_trapSet_subset _ _ _ _ _)
  have hqy₁  := hqT.1
  have hqy₂  := hqT.2.1
  -- a domain point of the closed trapezoid at a middle height is inside
  have hmid : ∀ z ∈ D, z ∈ closedTrap Q i j y₁ y₂ → y₁ < z.2 → z.2 < y₂ → z ∈ T := by
    intro z hzD hzC hz1 hz2
    obtain ⟨h1, h2, h3, h4⟩ := hzC
    exact ⟨hz1, hz2, lt_of_le_of_ne h3 fun e => hzD.2 ⟨i, h.hi, h.mem_edgeL h1 h2 e.symm⟩,
      lt_of_le_of_ne h4 fun e => hzD.2 ⟨j, h.hj, h.mem_edgeR h1 h2 e⟩⟩
  -- a chord meeting `T` contains its whole slice
  have hslice : ∀ c ∈ G, ∀ z ∈ c, z ∈ T → ∀ w ∈ T, w.2 = z.2 → w ∈ c := by
    intro c hc z hz hzT w hwT hwz
    obtain ⟨y, a, b, hh, rfl⟩ := hG c hc
    have hzy  := hz.1
    refine mem_of_joined hh hz (hTD hzT) (hwz.trans hzy) fun s h1 h2 => hTD ?_
    have hseg : Chazelle.segment z w ⊆ T :=
      Geometry.segment_subset_of_convex (Visibility.convex_trapSet _ _ _ _ _) hzT hwT
    apply hseg
    rw [Visibility.segment_horizontal_eq_hseg hwz.symm]
    exact ⟨hzy.symm, h1, h2⟩
  -- `U` is on one side of a chord crossing `T`
  have hno : ∀ c ∈ G, ∀ z ∈ c, z ∈ T → ∀ p ∈ U, p.2 ≠ z.2 := fun c hc z hz hzT p hp he =>
    (hfreeU hp).2 ⟨c, hc, hslice c hc z hz hzT p (hUT hp) he⟩
  have hUc := (isPreconnected_connectedComponentIn : IsPreconnected U)
  have hbelow : ∀ c ∈ G, ∀ z ∈ c, z ∈ T → q.2 < z.2 → ∀ p ∈ U, p.2 < z.2 := by
    intro c hc z hz hzT hqz
    have := hUc.subset_left_of_subset_union (u := {p : Point | p.2 < z.2})
      (v := {p : Point | z.2 < p.2}) (isOpen_lt continuous_snd continuous_const)
      (isOpen_lt continuous_const continuous_snd)
      (Set.disjoint_left.2 fun p (h1 : _ < _) (h2 : _ < _) => lt_asymm h1 h2)
      (fun p hp => (lt_or_gt_of_ne (hno c hc z hz hzT p hp)).elim Or.inl Or.inr)
      ⟨q, mem_connectedComponentIn hqf, hqz⟩
    exact fun p hp => this hp
  have habove : ∀ c ∈ G, ∀ z ∈ c, z ∈ T → z.2 < q.2 → ∀ p ∈ U, z.2 < p.2 := by
    intro c hc z hz hzT hqz
    have := hUc.subset_left_of_subset_union (u := {p : Point | z.2 < p.2})
      (v := {p : Point | p.2 < z.2}) (isOpen_lt continuous_const continuous_snd)
      (isOpen_lt continuous_snd continuous_const)
      (Set.disjoint_left.2 fun p (h1 : _ < _) (h2 : _ < _) => lt_asymm h1 h2)
      (fun p hp => (lt_or_gt_of_ne (hno c hc z hz hzT p hp)).elim Or.inr Or.inl)
      ⟨q, mem_connectedComponentIn hqf, hqz⟩
    exact fun p hp => this hp
  have hclle : ∀ y : ℝ, (∀ p ∈ U, p.2 < y) → ∀ p ∈ closure U, p.2 ≤ y := fun y hy =>
    fun p hp => closure_minimal (fun x hx => (hy x hx).le)
      (isClosed_le continuous_snd continuous_const) hp
  have hclge : ∀ y : ℝ, (∀ p ∈ U, y < p.2) → ∀ p ∈ closure U, y ≤ p.2 := fun y hy =>
    fun p hp => closure_minimal (fun x hx => (hy x hx).le)
      (isClosed_le continuous_const continuous_snd) hp
  -- the two classes of exit chords
  set E₁ := {c | c ∈ G ∧ ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ (z.2 = y₂ ∨ (q.2 < z.2 ∧ z.2 < y₂))}
    with hE₁
  set E₂ := {c | c ∈ G ∧ ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ (z.2 = y₁ ∨ (y₁ < z.2 ∧ z.2 < q.2))}
    with hE₂
  have hsub : {c | c ∈ G ∧ TouchesIn D c U} ⊆ E₁ ∪ E₂ := by
    rintro c ⟨hc, z, ⟨hz, hzD⟩, hzU⟩
    obtain ⟨h1, h2, -, -⟩ := hcl hzU
    rcases h2.lt_or_eq with h2 | h2
    · rcases h1.lt_or_eq with h1 | h1
      · have hzT := hmid z hzD (hcl hzU) h1 h2
        rcases lt_or_gt_of_ne (hno c hc z hz hzT q (mem_connectedComponentIn hqf)) with h3 | h3
        · exact Or.inl ⟨hc, z, hz, hzD, hzU, Or.inr ⟨h3, h2⟩⟩
        · exact Or.inr ⟨hc, z, hz, hzD, hzU, Or.inr ⟨h1, h3⟩⟩
      · exact Or.inr ⟨hc, z, hz, hzD, hzU, Or.inl h1.symm⟩
    · exact Or.inl ⟨hc, z, hz, hzD, hzU, Or.inl h2⟩
  have hBool : (Set.univ : Set Bool).ncard = 2 := by
    rwr [ncard_univ, Nat.card_eq_fintype_card]
  -- at most two chords above
  have hE₁ : E₁.ncard ≤ 2 := by
    by_cases hA : ∃ c₀ ∈ E₁, ∃ z₀ ∈ c₀, z₀ ∈ D ∧ z₀ ∈ closure U ∧ q.2 < z₀.2 ∧ z₀.2 < y₂
    · obtain ⟨c₀, hc₀, z₀, hz₀, hz₀D, hz₀U, hq0, h0⟩ := hA
      have hz₀T := hmid z₀ hz₀D (hcl hz₀U) (hqy₁.trans hq0) h0
      have hU0 := hbelow c₀ hc₀.1 z₀ hz₀ hz₀T hq0
      have hsub1 : E₁ ⊆ {c₀} := by
        rintro c ⟨hc, z, hz, hzD, hzU, hzc⟩
        have hz0 := hclle _ hU0 z hzU
        have hmz : q.2 < z.2 ∧ z.2 < y₂ := by
          rcases hzc with e | e
          · rwli [e] at hz0
          · exact e
        have hzT := hmid z hzD (hcl hzU) (hqy₁.trans hmz.1) hmz.2
        have hUz := hbelow c hc z hz hzT hmz.1
        have hz0' := hclle _ hUz z₀ hz₀U
        have heq  := le_antisymm hz0' hz0
        have hz₀c := hslice c hc z hz hzT z₀ hz₀T heq
        exact eq_of_common (hG c hc) (hG c₀ hc₀.1) hz₀c hz₀ hz₀D
      calc E₁.ncard ≤ ({c₀} : Set (Set Point)).ncard := ncard_le_ncard hsub1 (finite_singleton _)
        _ ≤ 2 := by rwn [ncard_singleton]
    · push Not at hA
      obtain ⟨k₀, hk₀, hk₀y, -⟩ := h.top_vertex
      set w₀ := Q.vtx k₀ with hw₀
      have hw₀D : w₀ ∉ D := fun hm => hm.2 (Existence.vtx_mem_boundary Q hk₀)
      have htop : ∀ c ∈ E₁, ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ z.2 = y₂ := by
        rintro c hc
        obtain ⟨hcG, z, hz, hzD, hzU, hzc⟩ := hc
        rcases hzc with e | e
        · exact ⟨z, hz, hzD, hzU, e⟩
        · exact absurd e.2 (not_lt.2 (hA c ⟨hcG, z, hz, hzD, hzU, Or.inr e⟩ z hz hzD hzU e.1))
      let f : Set Point → Bool := fun c => decide (∃ z ∈ c, z ∈ D ∧ z.2 = y₂ ∧ z.1 < w₀.1)
      have hinj : InjOn f E₁ := by
        intro c hc c' hc' hff
        obtain ⟨z, hz, hzD, hzU, hzy⟩ := htop c hc
        obtain ⟨z', hz', hz'D, hz'U, hz'y⟩ := htop c' hc'
        have h1 := side_iff (hG c hc.1) hw₀D hk₀y hz hzD hzy
        have h2 := side_iff (hG c' hc'.1) hw₀D hk₀y hz' hz'D hz'y
        have hside : z.1 < w₀.1 ↔ z'.1 < w₀.1 := by
          rw [← h1, ← h2]
          simp only [f, decide_eq_decide] at hff
          exact hff
        obtain ⟨-, -, hzl, hzr⟩ := hcl hzU
        obtain ⟨-, -, hz'l, hz'r⟩ := hcl hz'U
        rw [hzy] at hzl hzr
        rw [hz'y] at hz'l hz'r
        exact side_chords_eq hQ hDH hTD (Or.inr rfl)
          (fun x hx1 hx2 => h.closure_subset_filled hQ hqR (h.top_mem_closure hx1 hx2))
          (fun x hx1 hx2 => h.near_top hx1 hx2) hk₀ hk₀y (hG c hc.1) (hG c' hc'.1) hz hz' hzD
          hz'D hzy hz'y ⟨hzl, hzr⟩ ⟨hz'l, hz'r⟩ hside
      calc E₁.ncard ≤ (Set.univ : Set Bool).ncard :=
            ncard_le_ncard_of_injOn f (fun _ _ => mem_univ _) hinj
        _ = 2 := hBool
  -- at most two chords below
  have hE₂ : E₂.ncard ≤ 2 := by
    by_cases hA : ∃ c₀ ∈ E₂, ∃ z₀ ∈ c₀, z₀ ∈ D ∧ z₀ ∈ closure U ∧ y₁ < z₀.2 ∧ z₀.2 < q.2
    · obtain ⟨c₀, hc₀, z₀, hz₀, hz₀D, hz₀U, h0, hq0⟩ := hA
      have hz₀T := hmid z₀ hz₀D (hcl hz₀U) h0 (hq0.trans hqy₂)
      have hU0 := habove c₀ hc₀.1 z₀ hz₀ hz₀T hq0
      have hsub1 : E₂ ⊆ {c₀} := by
        rintro c ⟨hc, z, hz, hzD, hzU, hzc⟩
        have hz0 := hclge _ hU0 z hzU
        have hmz : y₁ < z.2 ∧ z.2 < q.2 := by
          rcases hzc with e | e
          · rwli [e] at hz0
          · exact e
        have hzT := hmid z hzD (hcl hzU) hmz.1 (hmz.2.trans hqy₂)
        have hUz := habove c hc z hz hzT hmz.2
        have hz0' := hclge _ hUz z₀ hz₀U
        have heq  := le_antisymm hz0 hz0'
        have hz₀c := hslice c hc z hz hzT z₀ hz₀T heq
        exact eq_of_common (hG c hc) (hG c₀ hc₀.1) hz₀c hz₀ hz₀D
      calc E₂.ncard ≤ ({c₀} : Set (Set Point)).ncard := ncard_le_ncard hsub1 (finite_singleton _)
        _ ≤ 2 := by rwn [ncard_singleton]
    · push Not at hA
      obtain ⟨k₀, hk₀, hk₀y, -⟩ := h.bot_vertex
      set w₀ := Q.vtx k₀ with hw₀
      have hw₀D : w₀ ∉ D := fun hm => hm.2 (Existence.vtx_mem_boundary Q hk₀)
      have hbot : ∀ c ∈ E₂, ∃ z ∈ c, z ∈ D ∧ z ∈ closure U ∧ z.2 = y₁ := by
        rintro c hc
        obtain ⟨hcG, z, hz, hzD, hzU, hzc⟩ := hc
        rcases hzc with e | e
        · exact ⟨z, hz, hzD, hzU, e⟩
        · exact absurd e.2 (not_lt.2 (hA c ⟨hcG, z, hz, hzD, hzU, Or.inr e⟩ z hz hzD hzU e.1))
      let f : Set Point → Bool := fun c => decide (∃ z ∈ c, z ∈ D ∧ z.2 = y₁ ∧ z.1 < w₀.1)
      have hinj : InjOn f E₂ := by
        intro c hc c' hc' hff
        obtain ⟨z, hz, hzD, hzU, hzy⟩ := hbot c hc
        obtain ⟨z', hz', hz'D, hz'U, hz'y⟩ := hbot c' hc'
        have h1 := side_iff (hG c hc.1) hw₀D hk₀y hz hzD hzy
        have h2 := side_iff (hG c' hc'.1) hw₀D hk₀y hz' hz'D hz'y
        have hside : z.1 < w₀.1 ↔ z'.1 < w₀.1 := by
          rw [← h1, ← h2]
          simp only [f, decide_eq_decide] at hff
          exact hff
        obtain ⟨-, -, hzl, hzr⟩ := hcl hzU
        obtain ⟨-, -, hz'l, hz'r⟩ := hcl hz'U
        rw [hzy] at hzl hzr
        rw [hz'y] at hz'l hz'r
        exact side_chords_eq hQ hDH hTD (Or.inl rfl)
          (fun x hx1 hx2 => h.closure_subset_filled hQ hqR (h.bot_mem_closure hx1 hx2))
          (fun x hx1 hx2 => h.near_bot hx1 hx2) hk₀ hk₀y (hG c hc.1) (hG c' hc'.1) hz hz' hzD
          hz'D hzy hz'y ⟨hzl, hzr⟩ ⟨hz'l, hz'r⟩ hside
      calc E₂.ncard ≤ (Set.univ : Set Bool).ncard :=
            ncard_le_ncard_of_injOn f (fun _ _ => mem_univ _) hinj
        _ = 2 := hBool
  have hfin12 : (E₁ ∪ E₂).Finite :=
    (hGfin.subset fun c hc => hc.1).union (hGfin.subset fun c hc => hc.1)
  calc {c | c ∈ G ∧ TouchesIn D c U}.ncard ≤ (E₁ ∪ E₂).ncard := ncard_le_ncard hsub hfin12
    _ ≤ E₁.ncard + E₂.ncard := ncard_union_le _ _
    _ ≤ 4 := by omega

end FullDegInt

/-- **The interior half of `FullDegSpec`**: for a simple polygon with distinct vertex heights,
the full augmented map of the interior model has degree at most `4`. -/
theorem fullDegLe_interior {Q : Polygon} (hQ : Q.Simple) (hDH : DistinctHeights Q) :
    (interiorModel Q).FullDegLe Q 4 := by
  intro F hF U hU
  refine FullDegInt.deg_le_four hQ hDH (G := chords Q ∪ F) ?_
    ((Visibility.chords_finite Q).union hF.1) subset_union_left hU
  rintro c (hc | hc)
  · exact FullDegInt.hc_full hQ hc
  · exact hF.2.1 hc

end

end Chazelle.Core

namespace Chazelle.Core

@[expose] public section

/-- **WP-B: the interior conjunct of `FullDegSpec`**: for a simple input polygon with a good
shear, the full augmented map of the interior model of the geometry polygon `Qof P` has degree at
most `4`. -/
theorem fullDeg_interior (P : Polygon) (hP : P.Simple) (hε : ∃ ε, GoodShear P ε) :
    (interiorModel (Qof P)).FullDegLe (Qof P) 4 :=
  fullDegLe_interior ((shearInvariance (epsOf P) P).1 hP) (goodShear_epsOf hε).2.1

end

end Chazelle.Core
