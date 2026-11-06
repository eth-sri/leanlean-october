module

public import Chazelle.Core.FactsArcs
public import Chazelle.Chain.Granular
public import Chazelle.Merge.Conformal
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# WP-B: Lemma 2.3 (region count) for the good models

`lemma23 : Lemma23Spec`: for every good model, finite admissible family `F` with regions of
degree `≤ D` and γ-granular, `|F| (γ + 1) ≤ 140 (D + 2) (size + 1)`.

## Proof

* **Weights by walk vertices.**  For a region `U` let `A U` be the set of walk vertices (integer
  keys) strictly inside the arcs of `U`; distinct regions have disjoint sets (a key inside an arc
  determines the region faced just after it), so `∑ |A U| ≤ n` (`n` = number of walk edges).  An
  arc meets at most one more walk edge than the walk vertices inside it (`arcWt_le`).
* **Contraction.**  Removing an exit chord `c` between `U` and `V` merges them into the region
  `W` of `F \ {c}`; a walk vertex inside an arc of `W` is an attachment of `c` or lies inside an
  arc of `U` or of `V` (`merged_vertices`), so the weight of `W` is at most
  `|A U| + |A V| + |E c| + 1`, where `E c` are the walk vertices at which `c` is attached.
* **Counting.**  With the node weight `ω U = |A U| + |Z U|` (`Z U`: walk vertices at which an exit
  chord of `U` is attached; `∑ |Z U| ≤ 4 n`, since at most two chords of `F` are attached at a
  walk vertex and each touches two regions), granularity condition (ii) gives `γ ≤ ω U + ω V` for
  every dual edge at a node of degree `< 3`, and the counting core of Lemma 2.3 for trees of
  degree `≤ D` (`card_mul_le_of_granular_deg`) gives `|F| γ ≤ 2 (D + 2) ∑ ω ≤ 10 (D + 2) n`.
* **γ = 0**: a nonempty family has a region whose arc meets a counted walk edge, so it is not
  `0`-semigranular (`eq_empty_of_granular_zero`).
* `n ≤ 7 (size + 1)` for both models (`walk_n_le`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric Finset
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn
  sideKey_inj)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext)

/-! ## The counting core for trees of bounded degree -/

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Counting core of Lemma 2.3, degree `≤ Δ`.**  In a finite tree of maximum degree `≤ Δ`
with node weights `w` such that every edge at a node of degree `< 3` has total weight `≥ γ`,
`(N - 1) γ ≤ 2 (Δ + 2) ∑ w`. -/
theorem card_mul_le_of_granular_deg (hG : G.IsTree) (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (w : V → ℕ) (γ : ℕ)
    (hgran : ∀ u v, G.Adj u v → (G.degree u < 3 ∨ G.degree v < 3) → γ ≤ w u + w v) :
    (Fintype.card V - 1) * γ ≤ 2 * (Δ + 2) * ∑ v, w v := by
  classical
  set L := (univ : Finset V).filter (fun v => G.degree v ≤ 2)
  set DL := (univ : Finset G.Dart).filter (fun d => d.fst ∈ L) with hDL
  have h1 : Fintype.card V - 1 ≤ 2 * #DL := by
    rw [hDL, Chazelle.Chain.card_dart_fst_filter G L]
    exact Chazelle.Chain.card_sub_one_le_two_mul_sum_low G hG
  have h2 : #DL * γ ≤ ∑ d ∈ DL, (w d.fst + w d.snd) := by
    rw [card_eq_sum_ones, sum_mul, one_mul]
    apply sum_le_sum
    intro d hd
    have hdL : G.degree d.fst ≤ 2 := (mem_filter.1 (mem_filter.1 hd).2).2
    exact hgran d.fst d.snd d.adj (Or.inl (by omega))
  have h3 : ∑ d ∈ DL, w d.fst ≤ 2 * ∑ v, w v := by
    rw [hDL, Chazelle.Chain.sum_dart_fst_filter G L w, mul_sum]
    calc ∑ v ∈ L, G.degree v * w v ≤ ∑ v ∈ L, 2 * w v :=
          sum_le_sum fun v hv => Nat.mul_le_mul_right _ (mem_filter.1 hv).2
      _ ≤ ∑ v, 2 * w v := sum_le_sum_of_subset (subset_univ _)
  have h4 : ∑ d ∈ DL, w d.snd ≤ Δ * ∑ v, w v := by
    calc ∑ d ∈ DL, w d.snd ≤ ∑ d : G.Dart, w d.snd := sum_le_sum_of_subset (subset_univ _)
      _ = ∑ v, G.degree v * w v := by
          rw [Chazelle.Chain.sum_dart_snd G, Chazelle.Chain.sum_dart_fst G]
      _ ≤ ∑ v, Δ * w v := sum_le_sum fun v _ => Nat.mul_le_mul_right _ (hdeg v)
      _ = Δ * ∑ v, w v := by rw [mul_sum]
  have h5 : ∑ d ∈ DL, (w d.fst + w d.snd) = ∑ d ∈ DL, w d.fst + ∑ d ∈ DL, w d.snd :=
    sum_add_distrib
  calc (Fintype.card V - 1) * γ ≤ 2 * #DL * γ := Nat.mul_le_mul_right _ h1
    _ = 2 * (#DL * γ) := by ring
    _ ≤ 2 * (2 * ∑ v, w v + Δ * ∑ v, w v) := by omega
    _ = 2 * (Δ + 2) * ∑ v, w v := by ring

end Counting

/-! ## Cyclic order facts -/

/-- Two keys in an interval `(l, r)` free of `A` and `B` are on the same side of `A, B`. -/
theorem cyc_same {l r y z A B : ℝ} (hy : sideInArc l r y) (hz : sideInArc l r z)
    (hA : ¬ sideInArc l r A) (hB : ¬ sideInArc l r B) (hAB : A ≠ B) :
    sideInArc A B y ↔ sideInArc A B z := by
  have := lt_or_gt_of_ne hAB
  unfold sideInArc at *
  split_ifs at * <;> constructor <;> intro h <;> cyc_close

/-- If a position `p + t` is inside an interval and `p` is not, the interval starts in
`[p, p + t)`. -/
theorem cyc_floor {a b p t : ℝ} (h : sideInArc a b (p + t)) (hp : ¬ sideInArc a b p)
    (ht : 0 < t) : p ≤ a ∧ a < p + t := by
  unfold sideInArc at *
  split_ifs at * <;> cyc_close

/-- An open interval contains the keys just after each of its keys. -/
theorem cyc_open {a b x : ℝ} (h : sideInArc a b x) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc a b (x + ε) := by
  unfold sideInArc at *
  split_ifs at * with hab
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < b - x by linarith [h.2])]
      with ε hε hε'
    have : (0 : ℝ) < ε := hε
    exact ⟨by linarith [h.1], by linarith [hε'.2]⟩
  · rcases h with h | h
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have : (0 : ℝ) < ε := hε
      left; linarith
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < b - x by linarith)] with ε hε
      right; linarith [hε.2]

/-- **A gap around a point.**  For a finite set `K` of at least two reals and `x ∉ K`, there are
`l ≠ r` in `K` with `x` strictly between them and no point of `K` strictly between them. -/
theorem exists_gap {K : Set ℝ} (hK : K.Finite) {k₁ k₂ : ℝ} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K)
    (hk : k₁ ≠ k₂) {x : ℝ} (hx : x ∉ K) :
    ∃ l ∈ K, ∃ r ∈ K, l ≠ r ∧ sideInArc l r x ∧ ∀ k ∈ K, ¬ sideInArc l r k := by
  have hKne : K.Nonempty := ⟨k₁, hk₁⟩
  obtain ⟨m₀, hm₀, hmin⟩ := Set.exists_min_image K id hK hKne
  obtain ⟨M₀, hM₀, hmax⟩ := Set.exists_max_image K id hK hKne
  simp only [id] at hmin hmax
  have hmM : m₀ < M₀ := by
    rcases lt_or_gt_of_ne hk with h | h
    · linarith [hmin k₁ hk₁, hmax k₂ hk₂]
    · linarith [hmin k₂ hk₂, hmax k₁ hk₁]
  -- the successor of `x`
  obtain ⟨r, hr, hrx, hrmin⟩ : ∃ r ∈ K, (x < r ∨ (∀ k ∈ K, k < x) ∧ r = m₀) ∧
      ∀ k ∈ K, x < k → (x < r ∧ r ≤ k) := by
    by_cases hA : ∃ k ∈ K, x < k
    · obtain ⟨r, ⟨hr, hxr⟩, hrm⟩ := Set.exists_min_image {k | k ∈ K ∧ x < k} id
        (hK.subset fun k hk => hk.1) (by obtain ⟨k, hk, hxk⟩ := hA; exact ⟨k, hk, hxk⟩)
      exact ⟨r, hr, Or.inl hxr, fun k hk hxk => ⟨hxr, hrm k ⟨hk, hxk⟩⟩⟩
    · push Not at hA
      refine ⟨m₀, hm₀, Or.inr ⟨fun k hk => lt_of_le_of_ne (hA k hk) (fun h => hx (h ▸ hk)),
        rfl⟩, fun k hk hxk => absurd (hA k hk) (not_le.2 hxk)⟩
  -- the predecessor of `x`
  obtain ⟨l, hl, hlx, hlmax⟩ : ∃ l ∈ K, (l < x ∨ (∀ k ∈ K, x < k) ∧ l = M₀) ∧
      ∀ k ∈ K, k < x → (l < x ∧ k ≤ l) := by
    by_cases hB : ∃ k ∈ K, k < x
    · obtain ⟨l, ⟨hl, hlx⟩, hlm⟩ := Set.exists_max_image {k | k ∈ K ∧ k < x} id
        (hK.subset fun k hk => hk.1) (by obtain ⟨k, hk, hkx⟩ := hB; exact ⟨k, hk, hkx⟩)
      exact ⟨l, hl, Or.inl hlx, fun k hk hkx => ⟨hlx, hlm k ⟨hk, hkx⟩⟩⟩
    · push Not at hB
      refine ⟨M₀, hM₀, Or.inr ⟨fun k hk => lt_of_le_of_ne (hB k hk) (fun h => hx (h ▸ hk)),
        rfl⟩, fun k hk hkx => absurd (hB k hk) (not_le.2 hkx)⟩
  have hxK : ∀ k ∈ K, k ≠ x := fun k hk h => hx (h ▸ hk)
  refine ⟨l, hl, r, hr, ?_, ?_, fun k hk => ?_⟩
  · rcases hrx with h1 | ⟨h1, rfl⟩ <;> rcases hlx with h2 | ⟨h2, rfl⟩
    · exact ne_of_lt (h2.trans h1)
    · have := (hrmin m₀ hm₀ (h2 m₀ hm₀)).2
      exact ne_of_gt (lt_of_le_of_lt this hmM)
    · have := (hlmax M₀ hM₀ (h1 M₀ hM₀)).2
      exact ne_of_gt (lt_of_lt_of_le hmM this)
    · exact absurd (h1 k₁ hk₁) (not_lt.2 (le_of_lt (h2 k₁ hk₁)))
  · unfold sideInArc
    rcases hrx with h1 | ⟨h1, rfl⟩ <;> rcases hlx with h2 | ⟨h2, rfl⟩
    · split_ifs with h
      · exact ⟨h2, h1⟩
      · exact Or.inr h1
    · split_ifs with h
      · have := hmax r hr; linarith
      · exact Or.inr h1
    · split_ifs with h
      · have := hmin l hl; linarith
      · exact Or.inl h2
    · exact absurd (h1 k₁ hk₁) (not_lt.2 (le_of_lt (h2 k₁ hk₁)))
  · have hkx := hxK k hk
    unfold sideInArc
    rcases lt_or_gt_of_ne hkx with hkx | hkx
    · obtain ⟨-, hkl⟩ := hlmax k hk hkx
      split_ifs with hlr
      · rintro ⟨h1, -⟩; linarith
      · rintro (h1 | h1)
        · linarith
        · rcases hrx with h2 | ⟨h2, rfl⟩
          · rcases hlx with h3 | ⟨h3, rfl⟩
            · exact hlr (h3.trans h2)
            · linarith [h3 k hk]
          · linarith [hmin k hk]
    · obtain ⟨-, hrk⟩ := hrmin k hk hkx
      split_ifs with hlr
      · rintro ⟨-, h1⟩; linarith
      · rintro (h1 | h1)
        · rcases hlx with h3 | ⟨h3, rfl⟩
          · rcases hrx with h2 | ⟨h2, rfl⟩
            · exact hlr (h3.trans h2)
            · linarith [h2 k hk]
          · linarith [hmax k hk]
        · linarith

namespace WalkAx

variable {M : Model}

/-! ## Cut keys -/

/-- A cut key lies in `[0, n)`. -/
theorem cut_bounds {F : Set (Set Point)} {k : ℝ} (h : M.IsCut F k) : 0 ≤ k ∧ k < M.W.n := by
  obtain ⟨c, -, p, t, hA, rfl⟩ := h
  have hp : (p : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hA.1
  exact ⟨by have := hA.2.1; positivity, by linarith [hA.2.2.1]⟩

/-- A nonempty admissible family has two distinct cut keys. -/
theorem two_cuts (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hne : F.Nonempty) :
    ∃ k₁ k₂ : ℝ, M.IsCut F k₁ ∧ M.IsCut F k₂ ∧ k₁ ≠ k₂ := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨a, b, hab, -, -, -, ⟨⟨pa, ta, hA, hAa⟩, -⟩, ⟨⟨pb, tb, hB, hBb⟩, -⟩⟩ := hM.ends c (hF hc)
  exact ⟨pa + ta, pb + tb, ⟨c, hc, pa, ta, hA, rfl⟩, ⟨c, hc, pb, tb, hB, rfl⟩,
    key_ne_of_pt_ne hA hB (by rwa [hAa, hBb])⟩

/-- Positions just after a key `p + t` of `[0, n)` are inside the walk edge `p`. -/
theorem exists_pos_after {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), t + ε ∈ Ioo (0 : ℝ) 1 := by
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 - t by linarith)]
    with ε hε hε'
  have : (0 : ℝ) < ε := hε
  exact ⟨by linarith, by linarith [hε'.2]⟩

/-- The keys just after the start of an interval are inside it. -/
theorem eventually_after_start {l r : ℝ} (_hlr : l ≠ r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc l r (l + ε) := by
  unfold sideInArc
  split_ifs with h
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < r - l by linarith)]
      with ε hε hε'
    have : (0 : ℝ) < ε := hε
    exact ⟨by linarith, by linarith [hε'.2]⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have : (0 : ℝ) < ε := hε
    left; linarith

/-- **The arc of a gap**: an interval `(l, r)` between two distinct cuts containing no cut is an
arc of the region faced by all its positions. -/
theorem arc_of_gap (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {l r : ℝ} (hl : M.IsCut F l) (hr : M.IsCut F r) (hlr : l ≠ r)
    (hfree : ∀ k, sideInArc l r k → ¬ M.IsCut F k) :
    ∃ X ∈ M.regions F, M.IsArc F X l r := by
  obtain ⟨c₁, hc₁, p₁, t₁, hA₁, hl₁⟩ := hl
  -- a position just after `l`
  obtain ⟨ε, hε1, hε2⟩ := ((exists_pos_after hA₁.2.1 hA₁.2.2.1).and
    (eventually_after_start hlr)).exists
  have hy : sideInArc l r (p₁ + (t₁ + ε)) := by rwa [← add_assoc, ← hl₁]
  obtain ⟨X, hX, hfX⟩ := hM.exists_faces_of_not_cut hF hfin hA₁.1 hε1 (hfree _ hy)
  refine ⟨X, hX, (cut_bounds ⟨c₁, hc₁, p₁, t₁, hA₁, hl₁⟩).1,
    (cut_bounds ⟨c₁, hc₁, p₁, t₁, hA₁, hl₁⟩).2, (cut_bounds hr).1, (cut_bounds hr).2,
    Or.inl ⟨⟨c₁, hc₁, p₁, t₁, hA₁, hl₁⟩, hr, hlr⟩, hfree, ?_⟩
  intro p t hp ht0 ht1 hin
  obtain ⟨U, hU, hfU⟩ := hM.exists_faces_of_not_cut hF hfin hp ⟨ht0, ht1⟩ (hfree _ hin)
  have heq : X = U := by
    refine (hM.eq_iff_not_separates hF hfin hX hU hA₁.1 hp hε1 ⟨ht0, ht1⟩ (hfree _ hy)
      (hfree _ hin) hfX hfU).2 ?_
    rintro c hc ⟨pa, pb, ta, tb, hA, hB, hAB, hiff⟩
    have hsame := cyc_same hy hin (hfree _ · ⟨c, hc, pa, ta, hA, rfl⟩)
      (hfree _ · ⟨c, hc, pb, tb, hB, rfl⟩) (key_ne_of_pt_ne hA hB hAB)
    exact (iff_not_self (hiff.trans (not_congr hsame.symm))).elim
  rwa [heq]

/-- **The arc around a non-cut key**: a non-cut key of `[0, n)` of a nonempty family lies inside
an arc of some region. -/
theorem arc_around (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    (hne : F.Nonempty) {x : ℝ} (hx : ¬ M.IsCut F x) :
    ∃ X ∈ M.regions F, ∃ l r : ℝ, M.IsArc F X l r ∧ sideInArc l r x := by
  obtain ⟨k₁, k₂, h₁, h₂, hk⟩ := hM.two_cuts hF hne
  obtain ⟨l, hl, r, hr, hlr, hxin, hno⟩ := exists_gap (hM.finite_cuts hF hfin) h₁ h₂ hk hx
  obtain ⟨X, hX, harc⟩ := hM.arc_of_gap hF hfin hl hr hlr (fun k hk hc => hno k hc hk)
  exact ⟨X, hX, l, r, harc, hxin⟩

/-! ## Weights by walk vertices -/

/-- The walk vertices (integer keys) strictly inside the arcs of `U`. -/
def arcVerts (M : Model) (F : Set (Set Point)) (U : Set Point) : Set ℕ :=
  {p | p < M.W.n ∧ ∃ a b : ℝ, M.IsArc F U a b ∧ sideInArc a b p}

/-- The walk vertices strictly inside the interval `(a, b)`. -/
def vertsIn (M : Model) (a b : ℝ) : Set ℕ := {p | p < M.W.n ∧ sideInArc a b p}

/-- **An interval meets at most one more walk edge than walk vertices inside it.** -/
theorem arcWt_le (a b : ℝ) : M.arcWt a b ≤ (vertsIn M a b).ncard + 1 := by
  have hsub : {p : ℕ | p < M.W.n ∧ M.counted p ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b (p + t)}
      ⊆ vertsIn M a b ∪ {⌊a⌋₊} := by
    rintro p ⟨hp, -, t, ht0, ht1, hin⟩
    by_cases hpin : sideInArc a b p
    · exact Or.inl ⟨hp, hpin⟩
    · right
      obtain ⟨h1, h2⟩ := cyc_floor hin hpin ht0
      rw [mem_singleton_iff, eq_comm, Nat.floor_eq_iff (le_trans (Nat.cast_nonneg p) h1)]
      exact ⟨h1, by linarith⟩
  have hfin : (vertsIn M a b).Finite := (finite_Iio M.W.n).subset fun p hp => hp.1
  calc M.arcWt a b ≤ (vertsIn M a b ∪ {⌊a⌋₊}).ncard :=
        ncard_le_ncard hsub (hfin.union (finite_singleton _))
    _ ≤ (vertsIn M a b).ncard + ({⌊a⌋₊} : Set ℕ).ncard := ncard_union_le _ _
    _ = (vertsIn M a b).ncard + 1 := by rw [ncard_singleton]

/-- **Distinct regions have disjoint arc vertices.** -/
theorem arcVerts_disjoint {F : Set (Set Point)} {U U' : Set Point}
    (hU : U ∈ M.regions F) (hU' : U' ∈ M.regions F) {p : ℕ} (hp : p ∈ arcVerts M F U)
    (hp' : p ∈ arcVerts M F U') : U = U' := by
  obtain ⟨hpn, a, b, harc, hin⟩ := hp
  obtain ⟨-, a', b', harc', hin'⟩ := hp'
  obtain ⟨ε, ⟨h1, h2⟩, h3⟩ := (((cyc_open hin).and (cyc_open hin')).and
    (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
  exact faces_unique hU hU' (harc.2.2.2.2.2.2 p ε hpn h3.1 h3.2 h1)
    (harc'.2.2.2.2.2.2 p ε hpn h3.1 h3.2 h2)

/-! ## Contraction -/

/-- **The regions inside a merged region.**  If `c ∈ F` separates the regions `U ≠ V` of `F`
and `W` is the region of `F \ {c}` containing `U`, the regions of `F` inside `W` are `U` and
`V`. -/
theorem merged_regions {F : Set (Set Point)} (hsys : ChordSystem M.D F) {c : Set Point}
    (hc : c ∈ F) {U V : Set Point} (hU : U ∈ M.regions F) (hV : V ∈ M.regions F) (hUV : U ≠ V)
    (hcU : TouchesIn M.D c U) (hcV : TouchesIn M.D c V) {W : Set Point}
    (hW : W ∈ M.regions (F \ {c})) (hUW : U ⊆ W) {X : Set Point} (hX : X ∈ M.regions F)
    (hXW : X ⊆ W) : X = U ∨ X = V := by
  have hS : F \ {c} ⊆ F := fun d hd => hd.1
  have hcS : c ∉ F \ {c} := fun h => h.2 rfl
  have hins : insert c (F \ {c}) = F := insert_sdiff_singleton.trans (insert_eq_of_mem hc)
  obtain ⟨R, hR, hcR, R₁, R₂, hne, hunion, hR₁, hR₂, heq⟩ := hsys.regionsIn_insert hS hc hcS
  have htouch := hsys.touches_iff_of_split hS hc hcS hR hcR hunion hR₁ hR₂ heq
  rw [hins] at htouch heq
  have hU12 := (htouch U hU).1 hcU
  have hV12 := (htouch V hV).1 hcV
  have hR₁R : R₁ ⊆ R := fun p hp => by
    have : p ∈ R₁ ∪ R₂ := Or.inl hp
    rw [hunion] at this; exact this.1
  have hR₂R : R₂ ⊆ R := fun p hp => by
    have : p ∈ R₁ ∪ R₂ := Or.inr hp
    rw [hunion] at this; exact this.1
  have hUR : U ⊆ R := by rcases hU12 with rfl | rfl <;> assumption
  have hX' : X ∈ regionsIn M.D F := hX
  rw [heq] at hX'
  rcases hX' with ⟨hXS, hXR⟩ | hX12
  · exfalso
    obtain ⟨x, hx⟩ := Chazelle.Chain.regionsIn_nonempty hXS
    have hXeqW : X = W := by
      rcases Chazelle.Chain.regionsIn_eq_or_disjoint hXS hW with h | h
      · exact h
      · exact absurd (h.le_bot ⟨hx, hXW hx⟩) (fun h => h)
    obtain ⟨u, hu⟩ := Chazelle.Chain.regionsIn_nonempty hU
    have huX : u ∈ X := hXeqW ▸ hUW hu
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hXS hR with h | h
    · exact hXR h
    · exact h.le_bot ⟨huX, hUR hu⟩
  · simp only [mem_insert_iff, mem_singleton_iff] at hX12
    rcases hU12 with rfl | rfl <;> rcases hV12 with rfl | rfl
    · exact absurd rfl hUV
    · rcases hX12 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rcases hX12 with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
    · exact absurd rfl hUV

/-- The walk vertices at which a chord is attached. -/
def chordVerts (M : Model) (c : Set Point) : Set ℕ := {p | p < M.W.n ∧ SideAttach M.W c p 0}

/-- **The walk vertices inside an arc of a merged region** are attachments of the removed chord or
arc vertices of one of the two merged regions. -/
theorem merged_vertices (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {U V : Set Point} (hU : U ∈ M.regions F)
    (hV : V ∈ M.regions F) (hUV : U ≠ V) (hcU : TouchesIn M.D c U) (hcV : TouchesIn M.D c V)
    {W : Set Point} (hW : W ∈ M.regions (F \ {c})) (hUW : U ⊆ W) {a b : ℝ}
    (harc : M.IsArc (F \ {c}) W a b) :
    vertsIn M a b ⊆ chordVerts M c ∪ arcVerts M F U ∪ arcVerts M F V := by
  have hsys := hM.sys F hF hfin
  rintro p ⟨hpn, hpin⟩
  by_cases hcut : M.IsCut F p
  · -- an attachment of `c`
    obtain ⟨d, hd, q, t, hA, hpq⟩ := hcut
    have hq : q = p ∧ t = 0 := by
      have := sideKey_inj hA.2.1 hA.2.2.1 le_rfl one_pos (show (q : ℝ) + t = p + 0 by
        rw [add_zero]; exact hpq.symm)
      exact ⟨this.1, this.2⟩
    obtain ⟨rfl, rfl⟩ := hq
    by_cases hdc : d = c
    · subst hdc; exact Or.inl (Or.inl ⟨hpn, hA⟩)
    · exact absurd ⟨d, ⟨hd, hdc⟩, q, 0, hA, hpq⟩ (harc.2.2.2.2.2.1 _ hpin)
  · obtain ⟨X, hX, l, r, harcX, hinX⟩ := hM.arc_around hF hfin ⟨c, hc⟩ hcut
    have hpX : p ∈ arcVerts M F X := ⟨hpn, l, r, harcX, hinX⟩
    -- `X` lies in `W`
    obtain ⟨ε, ⟨h1, h2⟩, h3⟩ := (((cyc_open hinX).and (cyc_open hpin)).and
      (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
    have hfX := harcX.2.2.2.2.2.2 p ε hpn h3.1 h3.2 h1
    have hfW := harc.2.2.2.2.2.2 p ε hpn h3.1 h3.2 h2
    obtain ⟨δ, hδX, hδW⟩ := (hfX.and hfW).exists
    have hXW : X ⊆ W := by
      have hXf : X ⊆ freeIn M.D (F \ {c}) :=
        (Chazelle.Chain.regionsIn_subset hX).trans
          (Chazelle.Chain.freeIn_anti M.D (fun d hd => hd.1))
      rw [Chazelle.Chain.regionsIn_eq_component hW hδW]
      exact (Chazelle.Chain.regionsIn_isPreconnected hX).subset_connectedComponentIn hδX hXf
    rcases merged_regions hsys hc hU hV hUV hcU hcV hW hUW hX hXW with rfl | rfl
    · exact Or.inl (Or.inr hpX)
    · exact Or.inr hpX

/-- **The weight of a merged region** is at most the arc vertices of the two merged regions plus
the attachments of the removed chord, plus one. -/
theorem weight_merged_le (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {c : Set Point} (hc : c ∈ F) {U V : Set Point} (hU : U ∈ M.regions F)
    (hV : V ∈ M.regions F) (hUV : U ≠ V) (hcU : TouchesIn M.D c U) (hcV : TouchesIn M.D c V)
    {W : Set Point} (hW : W ∈ M.regions (F \ {c})) (hUW : U ⊆ W) :
    M.weight (F \ {c}) W ≤ (chordVerts M c).ncard + (arcVerts M F U).ncard +
      (arcVerts M F V).ncard + 1 := by
  have hfn : ∀ S : Set ℕ, S ⊆ Set.Iio M.W.n → S.Finite := fun S h => (Set.finite_Iio _).subset h
  apply csSup_le'
  rintro _ ⟨⟨a, b⟩, harc, rfl⟩
  simp only
  refine (arcWt_le a b).trans (Nat.add_le_add_right ?_ 1)
  calc (vertsIn M a b).ncard ≤ (chordVerts M c ∪ arcVerts M F U ∪ arcVerts M F V).ncard :=
        ncard_le_ncard (hM.merged_vertices hF hfin hc hU hV hUV hcU hcV hW hUW harc)
          (((hfn _ fun p hp => hp.1).union (hfn _ fun p hp => hp.1)).union
            (hfn _ fun p hp => hp.1))
    _ ≤ (chordVerts M c ∪ arcVerts M F U).ncard + (arcVerts M F V).ncard := ncard_union_le _ _
    _ ≤ (chordVerts M c).ncard + (arcVerts M F U).ncard + (arcVerts M F V).ncard := by
        have := ncard_union_le (chordVerts M c) (arcVerts M F U); omega

/-! ## Chords at a walk vertex -/

/-- An attached admissible chord is the segment from its attachment point to its other endpoint,
which is off the domain, at the same height. -/
theorem chord_from (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W c p t) :
    ∃ e', c = Chazelle.segment (sidePt M.W p t) e' ∧ e' ≠ sidePt M.W p t ∧
      e'.2 = (sidePt M.W p t).2 ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp (sidePt M.W p t) e' s ∈ M.D) ∧ e' ∉ M.D := by
  obtain ⟨a, b, hab, hcab, hy, hopen, ⟨⟨pa, ta, hAa, hAa'⟩, -⟩, ⟨⟨pb, tb, hBb, hBb'⟩, -⟩⟩ :=
    hM.ends c hc
  have haD : a ∉ M.D := hAa' ▸ hM.trace pa hAa.1 ta hAa.2.1 hAa.2.2.1.le
  have hbD : b ∉ M.D := hBb' ▸ hM.trace pb hBb.1 tb hBb.2.1 hBb.2.2.1.le
  have hA' := hA
  rw [hcab] at hA'
  rcases hM.attach_endpoint hopen hA' with h | h
  · rw [h]; exact ⟨b, hcab, hab.symm, hy.symm, hopen, hbD⟩
  · rw [h]
    exact ⟨a, hcab.trans (Geometry.segment_comm _ _), hab, hy, open_rev hopen, haD⟩

/-- **At most two chords of `F` are attached at a walk vertex** (one to the east, one to the
west). -/
theorem ncard_chords_at_le (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (_hfin : F.Finite) (p : ℕ) : {c | c ∈ F ∧ SideAttach M.W c p 0}.ncard ≤ 2 := by
  classical
  let dir : Set Point → Bool := fun c => decide (∃ x ∈ c, (sidePt M.W p 0).1 < x.1)
  have hdir : ∀ c : Set Point, ∀ e', c = Chazelle.segment (sidePt M.W p 0) e' →
      (dir c = true ↔ (sidePt M.W p 0).1 < e'.1) := by
    intro c e' hce
    simp only [dir, decide_eq_true_eq]
    constructor
    · rintro ⟨x, hx, hlt⟩
      rw [hce] at hx
      obtain ⟨s, hs0, hs1, rfl⟩ := Geometry.mem_segment_iff_lerp.1 hx
      simp only [lerp_fst] at hlt
      by_contra hle; push Not at hle; nlinarith
    · intro hlt
      exact ⟨e', by rw [hce]; exact Geometry.right_mem_segment _ _, hlt⟩
  -- the far endpoint of one chord is not strictly inside another
  have key : ∀ {f f' : Point},
      (∀ s ∈ Ioo (0 : ℝ) 1, lerp (sidePt M.W p 0) f s ∈ M.D) → f' ∉ M.D →
      f.2 = (sidePt M.W p 0).2 → f'.2 = (sidePt M.W p 0).2 →
      ((sidePt M.W p 0).1 < f'.1 ∧ f'.1 < f.1 ∨ f.1 < f'.1 ∧ f'.1 < (sidePt M.W p 0).1) →
      False := by
    intro f f' hop hD hf hf' hbtw
    apply hD
    have hfe : f.1 - (sidePt M.W p 0).1 ≠ 0 := by
      rcases hbtw with h | h <;> intro h' <;> linarith [h.1, h.2]
    have e1 : f' = lerp (sidePt M.W p 0) f ((f'.1 - (sidePt M.W p 0).1) /
        (f.1 - (sidePt M.W p 0).1)) := by
      apply point_ext
      · simp only [lerp_fst]; field_simp; ring
      · simp only [lerp_snd]; rw [hf, hf']; ring
    rw [e1]
    apply hop
    rcases hbtw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
    · exact ⟨div_pos_of_neg_of_neg (by linarith) (by linarith),
        (div_lt_one_of_neg (by linarith)).2 (by linarith)⟩
  have hinj : InjOn dir {c | c ∈ F ∧ SideAttach M.W c p 0} := by
    intro c hc c' hc' hdd
    obtain ⟨e₁, hce₁, hne₁, hy₁, hop₁, hD₁⟩ := hM.chord_from (hF hc.1) hc.2
    obtain ⟨e₂, hce₂, hne₂, hy₂, hop₂, hD₂⟩ := hM.chord_from (hF hc'.1) hc'.2
    have hsame : (sidePt M.W p 0).1 < e₁.1 ↔ (sidePt M.W p 0).1 < e₂.1 := by
      rw [← hdir c e₁ hce₁, ← hdir c' e₂ hce₂, hdd]
    have hx₁ : e₁.1 ≠ (sidePt M.W p 0).1 := fun h => hne₁ (point_ext h hy₁)
    have hx₂ : e₂.1 ≠ (sidePt M.W p 0).1 := fun h => hne₂ (point_ext h hy₂)
    have heq : e₁ = e₂ := by
      apply point_ext _ (hy₁.trans hy₂.symm)
      rcases lt_or_gt_of_ne hx₁ with h₁ | h₁
      · have h₂ : e₂.1 < (sidePt M.W p 0).1 := by
          rcases lt_or_gt_of_ne hx₂ with h | h
          · exact h
          · exact absurd (hsame.2 h) (not_lt.2 h₁.le)
        rcases lt_trichotomy e₁.1 e₂.1 with h | h | h
        · exact (key hop₁ hD₂ hy₁ hy₂ (Or.inr ⟨h, h₂⟩)).elim
        · exact h
        · exact (key hop₂ hD₁ hy₂ hy₁ (Or.inr ⟨h, h₁⟩)).elim
      · have h₂ : (sidePt M.W p 0).1 < e₂.1 := hsame.1 h₁
        rcases lt_trichotomy e₁.1 e₂.1 with h | h | h
        · exact (key hop₂ hD₁ hy₂ hy₁ (Or.inl ⟨h₁, h⟩)).elim
        · exact h
        · exact (key hop₁ hD₂ hy₁ hy₂ (Or.inl ⟨h₂, h⟩)).elim
    rw [hce₁, hce₂, heq]
  calc {c | c ∈ F ∧ SideAttach M.W c p 0}.ncard ≤ (Set.univ : Set Bool).ncard :=
        ncard_le_ncard_of_injOn dir (fun _ _ => mem_univ _) hinj
    _ = 2 := by rw [ncard_univ, Nat.card_eq_fintype_card]; rfl

/-! ## The node weights and their sums -/

/-- The walk vertices at which an exit chord of `U` is attached. -/
def exitVerts (M : Model) (F : Set (Set Point)) (U : Set Point) : Set ℕ :=
  {p | p < M.W.n ∧ ∃ c ∈ F, TouchesIn M.D c U ∧ SideAttach M.W c p 0}

theorem chordVerts_subset_exitVerts {F : Set (Set Point)} {c : Set Point} (hc : c ∈ F)
    {U : Set Point} (hcU : TouchesIn M.D c U) : chordVerts M c ⊆ exitVerts M F U :=
  fun _p hp => ⟨hp.1, c, hc, hcU, hp.2⟩

/-- **The arc vertices of distinct regions add up to at most `n`.** -/
theorem sum_arcVerts_le {F : Set (Set Point)} (R : Finset (Set Point))
    (hR : ∀ U ∈ R, U ∈ M.regions F) : ∑ U ∈ R, (arcVerts M F U).ncard ≤ M.W.n := by
  classical
  let A : Set Point → Finset ℕ := fun U => (Finset.range M.W.n).filter (· ∈ arcVerts M F U)
  have hA : ∀ U, (arcVerts M F U).ncard = (A U).card := by
    intro U
    rw [← Set.ncard_coe_finset]
    congr 1
    ext p
    simp only [A, coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩
  have hdisj : (R : Set (Set Point)).PairwiseDisjoint A := by
    intro U hU U' hU' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    simp only [A, mem_filter] at hp hp'
    exact hne (arcVerts_disjoint (hR U hU) (hR U' hU') hp.2 hp'.2)
  calc ∑ U ∈ R, (arcVerts M F U).ncard = ∑ U ∈ R, (A U).card := by simp only [hA]
    _ = (R.biUnion A).card := (card_biUnion hdisj).symm
    _ ≤ (Finset.range M.W.n).card := card_le_card fun p hp => by
        obtain ⟨U, -, hpU⟩ := mem_biUnion.1 hp
        exact (mem_filter.1 hpU).1
    _ = M.W.n := card_range _

/-- **The exit vertices of the regions add up to at most `4 n`.** -/
theorem sum_exitVerts_le (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (R : Finset (Set Point)) (hR : ∀ U ∈ R, U ∈ M.regions F) :
    ∑ U ∈ R, (exitVerts M F U).ncard ≤ 4 * M.W.n := by
  classical
  have hsys := hM.sys F hF hfin
  have hZ : ∀ U, (exitVerts M F U).ncard =
      ∑ p ∈ Finset.range M.W.n, if p ∈ exitVerts M F U then 1 else 0 := by
    intro U
    rw [Finset.sum_boole, Nat.cast_id, ← Set.ncard_coe_finset]
    congr 1
    ext p
    simp only [coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩
  -- the regions with an exit chord attached at `p`
  have hp4 : ∀ p, (R.filter fun U => p ∈ exitVerts M F U).card ≤ 4 := by
    intro p
    set Cp := {c | c ∈ F ∧ SideAttach M.W c p 0}
    have hCp2 : Cp.ncard ≤ 2 := hM.ncard_chords_at_le hF hfin p
    have hCpf : Cp.Finite := hfin.subset fun c hc => hc.1
    -- the two regions touched by each chord
    have htwo : ∀ c ∈ F, ∃ R₁ R₂ : Set Point,
        ∀ W ∈ regionsIn M.D F, TouchesIn M.D c W → W = R₁ ∨ W = R₂ := by
      intro c hc
      obtain ⟨R₁, R₂, -, h⟩ := hsys.touches_iff subset_rfl hc
      exact ⟨R₁, R₂, fun W hW hcW => (h W hW).1 hcW⟩
    choose! r₁ r₂ hr using htwo
    let g : Set Point × Bool → Set Point := fun cb => if cb.2 then r₁ cb.1 else r₂ cb.1
    have hsub : ((R.filter fun U => p ∈ exitVerts M F U : Finset (Set Point)) : Set (Set Point))
        ⊆ g '' (Cp ×ˢ Set.univ) := by
      intro U hU
      simp only [coe_filter, Set.mem_ofPred_eq] at hU
      obtain ⟨hUR, -, c, hc, hcU, hA⟩ := hU
      rcases hr c hc U (hR U hUR) hcU with h | h
      · exact ⟨(c, true), ⟨⟨hc, hA⟩, mem_univ _⟩, by simp [g, h]⟩
      · exact ⟨(c, false), ⟨⟨hc, hA⟩, mem_univ _⟩, by simp [g, h]⟩
    calc (R.filter fun U => p ∈ exitVerts M F U).card
        = ((R.filter fun U => p ∈ exitVerts M F U : Finset (Set Point)) : Set (Set Point)).ncard :=
          (Set.ncard_coe_finset _).symm
      _ ≤ (g '' (Cp ×ˢ Set.univ)).ncard :=
          ncard_le_ncard hsub ((hCpf.prod Set.finite_univ).image _)
      _ ≤ (Cp ×ˢ (Set.univ : Set Bool)).ncard := ncard_image_le (hCpf.prod Set.finite_univ)
      _ = Cp.ncard * (Set.univ : Set Bool).ncard := ncard_prod
      _ ≤ 2 * 2 := Nat.mul_le_mul hCp2 (by rw [ncard_univ, Nat.card_eq_fintype_card]; rfl)
      _ = 4 := rfl
  calc ∑ U ∈ R, (exitVerts M F U).ncard
      = ∑ U ∈ R, ∑ p ∈ Finset.range M.W.n, if p ∈ exitVerts M F U then 1 else 0 := by
        simp only [hZ]
    _ = ∑ p ∈ Finset.range M.W.n, ∑ U ∈ R, if p ∈ exitVerts M F U then 1 else 0 :=
        Finset.sum_comm
    _ = ∑ p ∈ Finset.range M.W.n, (R.filter fun U => p ∈ exitVerts M F U).card := by
        simp only [Finset.sum_boole, Nat.cast_id]
    _ ≤ ∑ p ∈ Finset.range M.W.n, 4 := sum_le_sum fun p _ => hp4 p
    _ = 4 * M.W.n := by rw [sum_const, card_range, smul_eq_mul, mul_comm]

/-! ## γ = 0 -/

/-- **A nonempty family is not `0`-semigranular** when the walk has a counted edge: the arc
through a non-cut position of that edge meets it. -/
theorem not_semigranular_zero (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) (hne : F.Nonempty) {p₀ : ℕ} (hp₀ : p₀ < M.W.n) (hc₀ : M.counted p₀) :
    ¬ M.Semigranular F 0 := by
  intro hsg
  have hK := hM.finite_cuts hF hfin
  have hT : {t : ℝ | M.IsCut F (p₀ + t)}.Finite :=
    Set.Finite.preimage (f := fun t : ℝ => (p₀ : ℝ) + t)
      (fun t _ t' _ h => by simpa using h) hK
  obtain ⟨t, ht, htc⟩ := ((Set.Ioo_infinite (zero_lt_one' ℝ)).sdiff hT).nonempty
  obtain ⟨X, hX, l, r, harc, hin⟩ := hM.arc_around hF hfin hne htc
  have hwt : 1 ≤ M.arcWt l r := by
    apply Nat.one_le_iff_ne_zero.2
    intro h0
    rw [Model.arcWt, Set.ncard_eq_zero ((Set.finite_Iio M.W.n).subset fun p hp => hp.1)] at h0
    have : p₀ ∈ ({p : ℕ | p < M.W.n ∧ M.counted p ∧
        ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc l r (p + t)} : Set ℕ) :=
      ⟨hp₀, hc₀, t, ht.1, ht.2, hin⟩
    rwa [h0] at this
  have hbdd : BddAbove ((fun ab : ℝ × ℝ => M.arcWt ab.1 ab.2) '' {ab | M.IsArc F X ab.1 ab.2}) :=
    ((hM.arcs_bound hF hfin hX).1.image _).bddAbove
  have hle : M.arcWt l r ≤ M.weight F X := le_csSup hbdd ⟨(l, r), harc, rfl⟩
  have := hsg X hX
  omega

/-! ## Lemma 2.3 -/

/-- **Lemma 2.3 for a model with the walk axioms**: `|F| γ ≤ 10 (D + 2) n`. -/
theorem lemma23_walk (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {γ D : ℕ} (hdeg : M.DegLe F D) (hgran : M.Granular F γ) :
    F.ncard * γ ≤ 2 * (D + 2) * (5 * M.W.n) := by
  classical
  have hsys := hM.sys F hF hfin
  have hD := hM.preconn
  have hDne := hM.nonempty
  have hRfin := hsys.regionsIn_finite hD hDne subset_rfl
  let _ : Fintype (regionsIn M.D F) := hRfin.fintype
  set G := Chazelle.Chain.dualTreeIn M.D F
  have hTree : G.IsTree := hsys.dual_isTree hD hDne subset_rfl
  have hdegG : ∀ U : regionsIn M.D F, G.degree U = M.deg F U := by
    intro U
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, Merge.ncard_neighborSet_eq_exits hsys hD hDne subset_rfl U]
    rfl
  let w : regionsIn M.D F → ℕ := fun U => (arcVerts M F U).ncard + (exitVerts M F U).ncard
  have hfinN : ∀ S : Set ℕ, S ⊆ Set.Iio M.W.n → S.Finite := fun S h => (Set.finite_Iio _).subset h
  have hgran' : ∀ u v, G.Adj u v → (G.degree u < 3 ∨ G.degree v < 3) → γ ≤ w u + w v := by
    intro u v hadj hlow
    have hadj' : Chazelle.Chain.DualAdjIn M.D F u v := hadj
    obtain ⟨hu, hv, hne', c, hc, hcu, hcv⟩ := hadj'
    obtain ⟨x₀, hx₀⟩ := Chazelle.Chain.regionsIn_nonempty hu
    have hufree : (u : Set Point) ⊆ freeIn M.D (F \ {c}) :=
      (Chazelle.Chain.regionsIn_subset hu).trans
        (Chazelle.Chain.freeIn_anti M.D (fun d hd => hd.1))
    set W' := connectedComponentIn (freeIn M.D (F \ {c})) x₀
    have hW'r : W' ∈ M.regions (F \ {c}) := ⟨x₀, hufree hx₀, rfl⟩
    have huW : (u : Set Point) ⊆ W' :=
      (Chazelle.Chain.regionsIn_isPreconnected hu).subset_connectedComponentIn hx₀ hufree
    have hlow' : M.deg F u < 3 ∨ M.deg F v < 3 := by rwa [← hdegG, ← hdegG]
    have hγ := hgran.2 c hc u hu v hv hne' hcu hcv hlow' W' hW'r huW
    have hwt := hM.weight_merged_le hF hfin hc hu hv hne' hcu hcv hW'r huW
    have hE : (chordVerts M c).ncard ≤ (exitVerts M F u).ncard :=
      ncard_le_ncard (chordVerts_subset_exitVerts hc hcu) (hfinN _ fun p hp => hp.1)
    have : γ ≤ (chordVerts M c).ncard + (arcVerts M F u).ncard + (arcVerts M F v).ncard := by
      omega
    simp only [w]
    omega
  have hcore := card_mul_le_of_granular_deg G hTree D
    (fun U => (hdegG U).trans_le (hdeg U U.2)) w γ hgran'
  have hcard : Fintype.card (regionsIn M.D F) = F.ncard + 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hsys.ncard_regionsIn hD hDne subset_rfl]
  have hsum : ∑ U, w U ≤ 5 * M.W.n := by
    have e : ∑ U, w U = ∑ U ∈ (regionsIn M.D F).toFinset,
        ((arcVerts M F U).ncard + (exitVerts M F U).ncard) :=
      Finset.sum_set_coe (f := fun U => (arcVerts M F U).ncard + (exitVerts M F U).ncard)
        (regionsIn M.D F)
    rw [e, Finset.sum_add_distrib]
    have hR : ∀ U ∈ (regionsIn M.D F).toFinset, U ∈ M.regions F := fun U hU =>
      (Set.mem_toFinset (s := regionsIn M.D F)).1 hU
    have h1 := sum_arcVerts_le (M := M) (F := F) _ hR
    have h2 := hM.sum_exitVerts_le hF hfin _ hR
    omega
  rw [hcard, Nat.add_sub_cancel] at hcore
  exact hcore.trans (Nat.mul_le_mul_left _ hsum)

end WalkAx

/-! ## The good models -/

/-- The walk of a good model has at most `7 (size + 1)` edges, and a counted edge. -/
theorem goodModel_walk (M : Model) (h : GoodModel M) :
    M.W.n ≤ 7 * (M.size + 1) ∧ ∃ p < M.W.n, M.counted p := by
  rcases h with ⟨C, hC, rfl⟩ | ⟨Q, hQ, rfl⟩
  · have hm := C.one_le
    have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
    have hsize : (chainModel C).size = 2 * C.m := by
      unfold Model.size
      have : {p : ℕ | p < (chainModel C).W.n ∧ (chainModel C).counted p} = Set.Ico 6 (2 * C.m + 6) := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_Ico, hn]
        change p < 2 * C.m + 7 ∧ (6 ≤ p ∧ p < 2 * C.m + 6) ↔ _
        omega
      rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_Ico, Nat.card_Ico]
      omega
    refine ⟨by rw [hn, hsize]; omega, 6, by rw [hn]; omega, ?_⟩
    change 6 ≤ 6 ∧ 6 < 2 * C.m + 6
    omega
  · have hs := (FactsInterior.interiorWalk_spec hQ).1
    have hn3 := Chazelle.Jordan.simple_three_le hs
    have hsize : (interiorModel Q).size = (interiorModel Q).W.n := by
      unfold Model.size
      have : {p : ℕ | p < (interiorModel Q).W.n ∧ (interiorModel Q).counted p} =
          Set.Iio (interiorModel Q).W.n := by
        ext p; simp only [Set.mem_ofPred_eq, Set.mem_Iio]; exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
      rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_Iio, Nat.card_Iio]
    refine ⟨by rw [hsize]; omega, 0, by change 0 < (interiorWalk Q).n; omega, trivial⟩

/-- **WP-B: Lemma 2.3** (region count) for every good model, admissible family, degree cap `D`:
`|F| (γ + 1) ≤ 140 (D + 2) (size + 1)`. -/
theorem lemma23 : Lemma23Spec := by
  refine ⟨fun D => 140 * (D + 2), ?_⟩
  intro M Q F γ D hM hF hdeg hgran
  have hW := walkAx_of_goodModel hM
  obtain ⟨hfin, hAdm, -⟩ := hF
  obtain ⟨hn, p₀, hp₀, hc₀⟩ := goodModel_walk M hM
  rcases Nat.eq_zero_or_pos γ with rfl | hγ
  · rcases F.eq_empty_or_nonempty with rfl | hne
    · simp
    · exact absurd hgran.1 (hW.not_semigranular_zero hAdm hfin hne hp₀ hc₀)
  · have h := hW.lemma23_walk hAdm hfin hdeg hgran
    calc F.ncard * (γ + 1) ≤ 2 * (F.ncard * γ) := by nlinarith
      _ ≤ 2 * (2 * (D + 2) * (5 * M.W.n)) := Nat.mul_le_mul_left _ h
      _ ≤ 2 * (2 * (D + 2) * (5 * (7 * (M.size + 1)))) := by gcongr
      _ = 140 * (D + 2) * (M.size + 1) := by ring

end

end Chazelle.Core
