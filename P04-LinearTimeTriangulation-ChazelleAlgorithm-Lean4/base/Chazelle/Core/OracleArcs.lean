module

public import Chazelle.Core.OracleFold
public import Chazelle.Core.NFLocateMath
public import Chazelle.Core.FactsArcs
public import Chazelle.Core.OracleBook

/-!
# Lemma 3.6 (WP-H), part 5: the arcs of a normal form on the spine

The graph handed to `ClusterSpec` is a two-page book (`OracleBook`) whose spine is the list of
arcs of the normal form in the order of the arc-sequence table (sorted by start key).  This file
proves the order facts behind the non-crossing of its two pages.

* `interleave_absurd`, `sideInArc_interleave`: a chord of the walk (a cyclic interval) cannot
  separate two interleaved pairs of keys.
* `mirror_noncross`: two pairs of keys of chain points (`OracleQ.mirror_sum`: the sums are
  congruent modulo `2 m`, or the pair is the slit pair `6, 2 m + 6`) do not interleave.
* `starts_lt`, `interior_lt_start`, `start_lt_interior`, `order4`: the interiors of the arcs
  follow the order of the table, except the last arc, which may wrap around the start of the
  walk.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)

namespace OracleQ

/-! ## Interleaving keys -/

/-- **A convex predicate cannot separate interleaved pairs.**  If `P` is convex on the line and
the four keys are in cyclic order (`x₁ < x₂ < x₃ < x₄` or `x₄ < x₁ < x₂ < x₃`), then `P` cannot
hold on one pair `{x₁, x₃}` and fail on the other pair `{x₂, x₄}` or conversely. -/
theorem interleave_absurd (P : ℝ → Prop) (hconv : ∀ x y z, x < y → y < z → P x → P z → P y)
    {x₁ x₂ x₃ x₄ : ℝ}
    (hord : (x₁ < x₂ ∧ x₂ < x₃ ∧ x₃ < x₄) ∨ (x₄ < x₁ ∧ x₁ < x₂ ∧ x₂ < x₃))
    (h13 : P x₁ ↔ P x₃) (h24 : P x₂ ↔ P x₄) (h12 : P x₁ ↔ ¬ P x₂) : False := by
  by_cases h1 : P x₁
  · have h3 := h13.1 h1
    have h2 := h12.1 h1
    rcases hord with ⟨a, b, -⟩ | ⟨-, a, b⟩ <;> exact h2 (hconv _ _ _ a b h1 h3)
  · have h3 : ¬ P x₃ := fun h => h1 (h13.2 h)
    have h2 : P x₂ := by by_contra h; exact h1 (h12.2 h)
    have h4 := h24.1 h2
    rcases hord with ⟨-, b, c⟩ | ⟨a, b, -⟩
    · exact h3 (hconv _ _ _ b c h2 h4)
    · exact h1 (hconv _ _ _ a b h4 h2)

/-- **A chord of the walk cannot separate interleaved pairs of keys** (none of the keys at its
ends). -/
theorem sideInArc_interleave {a b x₁ x₂ x₃ x₄ : ℝ}
    (_hne : ∀ x ∈ ({x₁, x₂, x₃, x₄} : Set ℝ), x ≠ a ∧ x ≠ b)
    (hord : (x₁ < x₂ ∧ x₂ < x₃ ∧ x₃ < x₄) ∨ (x₄ < x₁ ∧ x₁ < x₂ ∧ x₂ < x₃))
    (h13 : sideInArc a b x₁ ↔ sideInArc a b x₃) (h24 : sideInArc a b x₂ ↔ sideInArc a b x₄)
    (h12 : sideInArc a b x₁ ↔ ¬ sideInArc a b x₂) : False := by
  by_cases hab : a < b
  · refine interleave_absurd (sideInArc a b) (fun x y z hxy hyz hx hz => ?_) hord h13 h24 h12
    unfold sideInArc at *
    rw [ite_eq_left hab] at hx hz ⊢
    exact ⟨by linarith [hx.1], by linarith [hz.2]⟩
  · -- the complement of the arc is the convex set `[b, a]` (away from the ends)
    let P : ℝ → Prop := fun x => ¬ sideInArc a b x
    have hP : ∀ x ∈ ({x₁, x₂, x₃, x₄} : Set ℝ), P x ↔ (b ≤ x ∧ x ≤ a) := by
      intro x hx
      simp only [P, sideInArc, ite_eq_right hab, not_or, not_lt]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    have m1 : x₁ ∈ ({x₁, x₂, x₃, x₄} : Set ℝ) := by simp
    have m2 : x₂ ∈ ({x₁, x₂, x₃, x₄} : Set ℝ) := by simp
    have m3 : x₃ ∈ ({x₁, x₂, x₃, x₄} : Set ℝ) := by simp
    have m4 : x₄ ∈ ({x₁, x₂, x₃, x₄} : Set ℝ) := by simp
    refine interleave_absurd (fun x => b ≤ x ∧ x ≤ a)
      (fun x y z hxy hyz hx hz => ⟨by linarith [hx.1], by linarith [hz.2]⟩) hord ?_ ?_ ?_
    · rw [← hP _ m1, ← hP _ m3]; exact not_congr h13
    · rw [← hP _ m2, ← hP _ m4]; exact not_congr h24
    · rw [← hP _ m1, ← hP _ m2]
      simp only [P]
      tauto

/-- **Pairs of keys of chain points do not interleave.**  Keys lie in `[lo, lo + L]`; each pair
has its sum congruent to `K` modulo `L`, or is the pair of the two ends `lo`, `lo + L`. -/
theorem mirror_noncross {L K lo : ℝ} (hL : 0 < L) {k₁ k₂ k₃ k₄ : ℝ}
    (hr : ∀ k ∈ ({k₁, k₂, k₃, k₄} : Set ℝ), lo ≤ k ∧ k ≤ lo + L)
    (P13 : (∃ n : ℤ, k₁ + k₃ = K + L * n) ∨ (k₁ = lo ∧ k₃ = lo + L) ∨ (k₁ = lo + L ∧ k₃ = lo))
    (P24 : (∃ n : ℤ, k₂ + k₄ = K + L * n) ∨ (k₂ = lo ∧ k₄ = lo + L) ∨ (k₂ = lo + L ∧ k₄ = lo))
    (hord : (k₁ < k₂ ∧ k₂ < k₃ ∧ k₃ < k₄) ∨ (k₄ < k₁ ∧ k₁ < k₂ ∧ k₂ < k₃)) : False := by
  have r1 := hr k₁ (by simp)
  have r2 := hr k₂ (by simp)
  have r3 := hr k₃ (by simp)
  have r4 := hr k₄ (by simp)
  rcases P13 with ⟨n, hn⟩ | ⟨e1, e3⟩ | ⟨e1, e3⟩
  · rcases P24 with ⟨n', hn'⟩ | ⟨e2, e4⟩ | ⟨e2, e4⟩
    · -- the two sums differ by a multiple of `L` strictly between `-L` and `L`, and not by `0`
      have hdiff : (k₂ + k₄) - (k₁ + k₃) = L * ((n' : ℝ) - n) := by rw [hn, hn']; ring
      have key : ∀ z : ℤ, 0 < L * (z : ℝ) → L * (z : ℝ) < L → False := by
        intro z h1 h2
        have h3 : (0 : ℝ) < z := by
          by_contra hc; push Not at hc; nlinarith
        have h4 : (z : ℝ) < 1 := by
          by_contra hc; push Not at hc; nlinarith
        have h5 : (0 : ℤ) < z := by exact_mod_cast h3
        have h6 : z < (1 : ℤ) := by exact_mod_cast h4
        omega
      rcases hord with ⟨a, b, c⟩ | ⟨a, b, c⟩
      · exact key (n' - n) (by push_cast; rw [← hdiff]; linarith) (by push_cast; rw [← hdiff]; linarith)
      · exact key (n - n') (by push_cast; nlinarith [hdiff]) (by push_cast; nlinarith [hdiff])
    · rcases hord with ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> linarith
    · rcases hord with ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> linarith
  · rcases hord with ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> linarith
  · rcases hord with ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> linarith

/-! ## The arcs of a normal form in the order of the table -/

section ArcOrder

variable {M : Model} {Q : Polygon} {N : NF}

/-- The arc at spine position `p`. -/
def sj (N : NF) (p : ℕ) : ℕ := N.seq.getD p 0

/-- The start key of the arc at spine position `p`. -/
noncomputable def sk (M : Model) (Q : Polygon) (N : NF) (p : ℕ) : ℝ :=
  M.key Q (N.arc (sj N p)).s

/-- The end key of the arc at spine position `p`. -/
noncomputable def ek (M : Model) (Q : Polygon) (N : NF) (p : ℕ) : ℝ :=
  M.key Q (N.arc (sj N p)).e

/-- The arc at a spine position is an arc of the region it records. -/
theorem isArc_sj (hN : IsNF M Q N) {p : ℕ} (hp : p < N.arcs.length) :
    ∃ reg : ℕ → Set Point, RegionCorr M Q N reg ∧ ArcsOK M Q N reg ∧
      M.IsArc (N.F M Q) (reg (N.arc (sj N p)).reg) (sk M Q N p) (ek M Q N p) := by
  obtain ⟨reg, hR, hA, -⟩ := NFLoc.isNF_arcs hN
  exact ⟨reg, hR, hA, (hA.1 _ (NFLoc.seq_lt hN hp)).2⟩

/-- The table has no repetition. -/
theorem seq_nodup (hN : IsNF M Q N) : N.seq.Nodup := by
  obtain ⟨-, -, -, hS⟩ := NFLoc.isNF_arcs hN
  exact hS.1.nodup_iff.2 List.nodup_range

theorem sj_inj (hN : IsNF M Q N) {p q : ℕ} (hp : p < N.arcs.length) (hq : q < N.arcs.length)
    (h : sj N p = sj N q) : p = q := by
  have hl := NFLoc.seq_length hN
  unfold sj at h
  rw [NFLoc.getD_of_lt 0 (by omega), NFLoc.getD_of_lt 0 (by omega)] at h
  exact (seq_nodup hN).getElem_inj_iff.1 h

/-- **Start keys strictly increase along the table** (nonempty family). -/
theorem starts_lt (hN : IsNF M Q N) (_hGM : GoodModel M) (hne : (N.F M Q).Nonempty) {p q : ℕ}
    (hpq : p < q) (hq : q < N.arcs.length) : sk M Q N p < sk M Q N q := by
  have hle : sk M Q N p ≤ sk M Q N q := NFLoc.seq_sorted hN hpq.le hq
  refine lt_of_le_of_ne hle fun heq => ?_
  obtain ⟨reg, hR, hA, harc⟩ := isArc_sj hN (hpq.trans hq)
  have harc' : M.IsArc (N.F M Q) (reg (N.arc (sj N q)).reg) (sk M Q N q) (ek M Q N q) :=
    (hA.1 _ (NFLoc.seq_lt hN hq)).2
  set a := sk M Q N p
  set b := ek M Q N p
  set b' := ek M Q N q
  rw [← heq] at harc'
  obtain ⟨hca, hcb, hab⟩ := WalkAx.arc_cuts hne harc
  obtain ⟨-, hcb', hab'⟩ := WalkAx.arc_cuts hne harc'
  have hfree := harc.2.2.2.2.2.1
  have hfree' := harc'.2.2.2.2.2.1
  -- the two ends coincide
  have hbb : b = b' := by
    by_contra hbb
    by_cases h1 : sideInArc a b b'
    · exact hfree b' h1 hcb'
    · exact hfree' b (NFLoc.sideInArc_swap hab hab' hbb h1) hcb
  rw [← hbb] at harc'
  -- a common position faced by both regions
  obtain ⟨pp, hpp, t, ht, hin, -, hfac⟩ := WalkAx.exists_pos_in_arc hne harc
  have hfac' := harc'.2.2.2.2.2.2 pp t hpp ht.1 ht.2 hin
  have hRp := hR.1 _ (hA.1 _ (NFLoc.seq_lt hN (hpq.trans hq))).1
  have hRq := hR.1 _ (hA.1 _ (NFLoc.seq_lt hN hq)).1
  have hU := WalkAx.faces_unique hRp hRq hfac hfac'
  have hreg := hR.2.1 _ _ (hA.1 _ (NFLoc.seq_lt hN (hpq.trans hq))).1
    (hA.1 _ (NFLoc.seq_lt hN hq)).1 hU
  have hj := hA.2.1 _ _ (NFLoc.seq_lt hN (hpq.trans hq)) (NFLoc.seq_lt hN hq) hreg heq
  exact absurd (sj_inj hN (hpq.trans hq) hq hj) hpq.ne

/-- **The interior of an arc lies before the starts of later arcs.** -/
theorem interior_lt_start (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {p q : ℕ} (hpq : p < q) (hq : q < N.arcs.length) {κ : ℝ}
    (hκ : sideInArc (sk M Q N p) (ek M Q N p) κ) : κ < sk M Q N q := by
  obtain ⟨reg, -, -, harc⟩ := isArc_sj hN (hpq.trans hq)
  obtain ⟨reg', -, -, harc'⟩ := isArc_sj hN hq
  have hfree := harc.2.2.2.2.2.1
  have hcq := (WalkAx.arc_cuts hne harc').1
  have hlt := starts_lt hN hGM hne hpq hq
  by_contra hge
  push Not at hge
  rcases eq_or_lt_of_le hge with he | hlt'
  · exact hfree κ hκ (he ▸ hcq)
  · apply hfree _ _ hcq
    unfold sideInArc at hκ ⊢
    split_ifs at hκ ⊢ with h
    · exact ⟨hlt, by linarith [hκ.2]⟩
    · exact Or.inl hlt

/-- **The interior of an arc that is not the last lies after its start.** -/
theorem start_lt_interior (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {p q : ℕ} (hpq : p < q) (hq : q < N.arcs.length) {κ : ℝ}
    (hκ : sideInArc (sk M Q N p) (ek M Q N p) κ) (_hκn : κ < M.W.n) : sk M Q N p < κ := by
  obtain ⟨reg, -, -, harc⟩ := isArc_sj hN (hpq.trans hq)
  obtain ⟨reg', -, -, harc'⟩ := isArc_sj hN hq
  have hfree := harc.2.2.2.2.2.1
  have hcq := (WalkAx.arc_cuts hne harc').1
  have hlt := starts_lt hN hGM hne hpq hq
  unfold sideInArc at hκ
  split_ifs at hκ with h
  · exact hκ.1
  · rcases hκ with h1 | h1
    · exact h1
    · exfalso
      apply hfree _ _ hcq
      unfold sideInArc
      rw [ite_eq_right h]
      exact Or.inl hlt

/-- **The last arc**: its interior lies after its start or before every start. -/
theorem last_interior (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {p q : ℕ} (hpq : p < q) (hq : q < N.arcs.length) {κ : ℝ}
    (hκ : sideInArc (sk M Q N q) (ek M Q N q) κ) : sk M Q N q < κ ∨ κ < sk M Q N p := by
  obtain ⟨reg, -, -, harc⟩ := isArc_sj hN hq
  obtain ⟨reg', -, -, harc'⟩ := isArc_sj hN (hpq.trans hq)
  have hfree := harc.2.2.2.2.2.1
  have hcp := (WalkAx.arc_cuts hne harc').1
  have hlt := starts_lt hN hGM hne hpq hq
  unfold sideInArc at hκ
  split_ifs at hκ with h
  · exact Or.inl hκ.1
  · rcases hκ with h1 | h1
    · exact Or.inl h1
    · right
      by_contra hge
      push Not at hge
      apply hfree _ _ hcp
      unfold sideInArc
      rw [ite_eq_right h]
      right
      linarith

/-- **Four arcs in the order of the table**: their interior keys are in cyclic order. -/
theorem order4 (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {p₁ p₂ p₃ p₄ : ℕ} (h12 : p₁ < p₂) (h23 : p₂ < p₃) (h34 : p₃ < p₄)
    (h4 : p₄ < N.arcs.length) {κ₁ κ₂ κ₃ κ₄ : ℝ}
    (hκ₁ : sideInArc (sk M Q N p₁) (ek M Q N p₁) κ₁) (hκ₂ : sideInArc (sk M Q N p₂) (ek M Q N p₂) κ₂)
    (hκ₃ : sideInArc (sk M Q N p₃) (ek M Q N p₃) κ₃) (hκ₄ : sideInArc (sk M Q N p₄) (ek M Q N p₄) κ₄)
    (hn₁ : κ₁ < M.W.n) (hn₂ : κ₂ < M.W.n) (hn₃ : κ₃ < M.W.n) :
    (κ₁ < κ₂ ∧ κ₂ < κ₃ ∧ κ₃ < κ₄) ∨ (κ₄ < κ₁ ∧ κ₁ < κ₂ ∧ κ₂ < κ₃) := by
  have a1 := start_lt_interior hN hGM hne h12 (by omega) hκ₁ hn₁
  have b1 := interior_lt_start hN hGM hne h12 (by omega) hκ₁
  have a2 := start_lt_interior hN hGM hne h23 (by omega) hκ₂ hn₂
  have b2 := interior_lt_start hN hGM hne h23 (by omega) hκ₂
  have a3 := start_lt_interior hN hGM hne h34 h4 hκ₃ hn₃
  have b3 := interior_lt_start hN hGM hne h34 h4 hκ₃
  rcases last_interior hN hGM hne (h12.trans (h23.trans h34)) h4 hκ₄ with c | c
  · left; exact ⟨by linarith, by linarith, by linarith⟩
  · right; exact ⟨by linarith, by linarith, by linarith⟩

end ArcOrder

/-! ## The two pages do not cross -/

section Pages

variable {M : Model} {Q : Polygon} {N : NF}

/-- The region index of the arc at spine position `p`. -/
def rgi (N : NF) (p : ℕ) : ℕ := (N.arc (sj N p)).reg

/-- **An inner (star) chord**: two spine positions of arcs of the same region, the first being
the first arc of the region on the spine. -/
def StarOK (N : NF) (c : ℕ × ℕ) : Prop :=
  c.1 < c.2 ∧ c.2 < N.arcs.length ∧ rgi N c.1 = rgi N c.2 ∧
    ∀ q, q < N.arcs.length → rgi N q = rgi N c.1 → c.1 ≤ q

theorem key_lt_n {M : Model} {pp : ℕ} (hpp : pp < M.W.n) {t : ℝ} (ht : t < 1) :
    (pp : ℝ) + t < M.W.n := by
  have : (pp : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hpp
  linarith

/-- **The regions of the arcs do not interleave on the spine** (non-crossing partition, from the
cut structure: a chord separating two regions separates their keys). -/
theorem regions_noninterleave (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {p₁ p₂ p₃ p₄ : ℕ} (h12 : p₁ < p₂) (h23 : p₂ < p₃) (h34 : p₃ < p₄)
    (h4 : p₄ < N.arcs.length) (hr13 : rgi N p₁ = rgi N p₃) (hr24 : rgi N p₂ = rgi N p₄) :
    rgi N p₁ = rgi N p₂ := by
  have hp1 : p₁ < N.arcs.length := by omega
  have hp2 : p₂ < N.arcs.length := by omega
  have hp3 : p₃ < N.arcs.length := by omega
  obtain ⟨reg, hR, hA, -⟩ := NFLoc.isNF_arcs hN
  -- interior positions of the four arcs (facing the regions of the common witness `reg`)
  have pick : ∀ p, p < N.arcs.length → ∃ pp < M.W.n, ∃ t ∈ Ioo (0 : ℝ) 1,
      sideInArc (sk M Q N p) (ek M Q N p) (pp + t) ∧ ¬ M.IsCut (N.F M Q) (pp + t) ∧
        M.Faces pp t (reg (rgi N p)) := by
    intro p hp
    have harc := (hA.1 _ (NFLoc.seq_lt hN hp)).2
    obtain ⟨pp, hpp, t, ht, h1, h2, h3⟩ := WalkAx.exists_pos_in_arc hne harc
    exact ⟨pp, hpp, t, ht, h1, h2, h3⟩
  obtain ⟨q₁, hq₁, t₁, ht₁, i₁, c₁, f₁⟩ := pick p₁ hp1
  obtain ⟨q₂, hq₂, t₂, ht₂, i₂, c₂, f₂⟩ := pick p₂ hp2
  obtain ⟨q₃, hq₃, t₃, ht₃, i₃, c₃, f₃⟩ := pick p₃ hp3
  obtain ⟨q₄, hq₄, t₄, ht₄, i₄, c₄, f₄⟩ := pick p₄ h4
  have hord := order4 hN hGM hne h12 h23 h34 h4 i₁ i₂ i₃ i₄ (key_lt_n hq₁ ht₁.2)
    (key_lt_n hq₂ ht₂.2) (key_lt_n hq₃ ht₃.2)
  by_contra hne12
  have hRg : ∀ p, p < N.arcs.length → reg (rgi N p) ∈ M.regions (N.F M Q) := fun p hp =>
    hR.1 _ (hA.1 _ (NFLoc.seq_lt hN hp)).1
  have hlt : ∀ p, p < N.arcs.length → rgi N p < N.nRegions := fun p hp =>
    (hA.1 _ (NFLoc.seq_lt hN hp)).1
  have hCS := (cutStructure M Q (N.F M Q) hGM hN.1).2.2
  -- the regions of the first two arcs differ
  have hdiff : reg (rgi N p₁) ≠ reg (rgi N p₂) := fun h =>
    hne12 (hR.2.1 _ _ (hlt p₁ hp1) (hlt p₂ hp2) h)
  have hsep := mt (hCS q₁ q₂ t₁ t₂ _ _ (hRg p₁ hp1) (hRg p₂ hp2) hq₁ hq₂ ht₁.1 ht₁.2 ht₂.1 ht₂.2
    c₁ c₂ f₁ f₂).2 hdiff
  push Not at hsep
  obtain ⟨c, hc, pa, pb, ta, tb, hAa, hAb, hpt, hiff⟩ := hsep
  have h13 := (hCS q₁ q₃ t₁ t₃ _ _ (hRg p₁ hp1) (hRg p₃ hp3) hq₁ hq₃ ht₁.1 ht₁.2 ht₃.1 ht₃.2
    c₁ c₃ f₁ f₃).1 (by rw [hr13]) c hc
  have h24 := (hCS q₂ q₄ t₂ t₄ _ _ (hRg p₂ hp2) (hRg p₄ h4) hq₂ hq₄ ht₂.1 ht₂.2 ht₄.1 ht₄.2
    c₂ c₄ f₂ f₄).1 (by rw [hr24]) c hc
  have e13 : sideInArc (pa + ta) (pb + tb) (q₁ + t₁) ↔ sideInArc (pa + ta) (pb + tb) (q₃ + t₃) := by
    by_contra h
    exact h13 ⟨pa, pb, ta, tb, hAa, hAb, hpt, by tauto⟩
  have e24 : sideInArc (pa + ta) (pb + tb) (q₂ + t₂) ↔ sideInArc (pa + ta) (pb + tb) (q₄ + t₄) := by
    by_contra h
    exact h24 ⟨pa, pb, ta, tb, hAa, hAb, hpt, by tauto⟩
  have hcutA : M.IsCut (N.F M Q) (pa + ta) := ⟨c, hc, pa, ta, hAa, rfl⟩
  have hcutB : M.IsCut (N.F M Q) (pb + tb) := ⟨c, hc, pb, tb, hAb, rfl⟩
  refine sideInArc_interleave (a := pa + ta) (b := pb + tb) ?_ hord e13 e24 hiff
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨fun h => c₁ (h ▸ hcutA), fun h => c₁ (h ▸ hcutB)⟩
  · exact ⟨fun h => c₂ (h ▸ hcutA), fun h => c₂ (h ▸ hcutB)⟩
  · exact ⟨fun h => c₃ (h ▸ hcutA), fun h => c₃ (h ▸ hcutB)⟩
  · exact ⟨fun h => c₄ (h ▸ hcutA), fun h => c₄ (h ▸ hcutB)⟩

/-- **The inner (star) page does not cross.** -/
theorem stars_nonCross (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {L : List (ℕ × ℕ)} (hL : ∀ c ∈ L, StarOK N c) : OracleBook.NonCross L := by
  intro c hc c' hc' ⟨h1, h2, h3⟩
  obtain ⟨hc12, hc2, hcr, hcmin⟩ := hL c hc
  obtain ⟨hc'12, hc'2, hc'r, hc'min⟩ := hL c' hc'
  have hreg := regions_noninterleave hN hGM hne h1 h2 h3 hc'2 hcr hc'r
  have := hc'min c.1 (by omega) hreg
  omega

/-- **An outer (zipper) chord**: two spine positions whose arcs contain, in their interiors, keys
of two positions at the same point of the chain. -/
def ZipOK (C : Chain) (Q : Polygon) (N : NF) (c : ℕ × ℕ) : Prop :=
  c.1 < c.2 ∧ c.2 < N.arcs.length ∧
    ∃ p₁ p₂ : ℕ, ∃ t₁ t₂ : ℝ, p₁ < (chainModel C).W.n ∧ p₂ < (chainModel C).W.n ∧
      0 ≤ t₁ ∧ t₁ < 1 ∧ 0 ≤ t₂ ∧ t₂ < 1 ∧
      Chazelle.Chain.sidePt (chainModel C).W p₁ t₁ ∈ C.set ∧
      Chazelle.Chain.sidePt (chainModel C).W p₁ t₁ = Chazelle.Chain.sidePt (chainModel C).W p₂ t₂ ∧
      sideInArc (sk (chainModel C) Q N c.1) (ek (chainModel C) Q N c.1) (p₁ + t₁) ∧
      sideInArc (sk (chainModel C) Q N c.2) (ek (chainModel C) Q N c.2) (p₂ + t₂)

/-- The keys of positions at a point of the chain lie in `[6, 2 m + 6]`. -/
theorem key_range (C : Chain) {p : ℕ} (hp : p < 2 * C.m + 7) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hx : Chazelle.Chain.sidePt (C.sideWalk C.sideBeta) p t ∈ C.set) :
    6 ≤ (p : ℝ) + t ∧ (p : ℝ) + t ≤ 6 + 2 * C.m := by
  rcases pos_on_chain C hp ht ht1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have a : (6 : ℝ) ≤ p := by exact_mod_cast h1
    have b : (p : ℝ) + 1 ≤ 2 * C.m + 6 := by exact_mod_cast h2
    constructor <;> linarith
  · subst h1; subst h2; push_cast; constructor <;> linarith

/-- **The outer (zipper) page does not cross.** -/
theorem zips_nonCross (C : Chain) (hP : C.P.Simple) {Q : Polygon} {N : NF}
    (hN : IsNF (chainModel C) Q N) (hne : (N.F (chainModel C) Q).Nonempty)
    {L : List (ℕ × ℕ)} (hL : ∀ c ∈ L, ZipOK C Q N c) : OracleBook.NonCross L := by
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  have hn : (chainModel C).W.n = 2 * C.m + 7 := walk_n C
  intro c hc c' hc' ⟨h1, h2, h3⟩
  obtain ⟨hc12, hc2, pa, pb, ta, tb, hpa, hpb, hta, hta1, htb, htb1, hxa, hab, ia, ib⟩ := hL c hc
  obtain ⟨hc'12, hc'2, pc, pd, tc, td, hpc, hpd, htc, htc1, htd, htd1, hxc, hcd, ic, id⟩ :=
    hL c' hc'
  have hord := order4 hN hGM hne h1 h2 h3 hc'2 ia ic ib id (key_lt_n hpa hta1)
    (key_lt_n hpc htc1) (key_lt_n hpb htb1)
  rw [hn] at hpa hpb hpc hpd
  have hxb : Chazelle.Chain.sidePt (chainModel C).W pb tb ∈ C.set := hab ▸ hxa
  have hxd : Chazelle.Chain.sidePt (chainModel C).W pd td ∈ C.set := hcd ▸ hxc
  have ra := key_range C hpa hta hta1 hxa
  have rb := key_range C hpb htb htb1 hxb
  have rc := key_range C hpc htc htc1 hxc
  have rd := key_range C hpd htd htd1 hxd
  have hneab : (pa : ℝ) + ta ≠ pb + tb := by
    rcases hord with ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> exact ne_of_lt (by linarith)
  have hnecd : (pc : ℝ) + tc ≠ pd + td := by
    rcases hord with ⟨a, b, c⟩ | ⟨a, b, c⟩
    · exact ne_of_lt (by linarith)
    · exact ne_of_gt (by linarith)
  have m1 := mirror_sum C hP hpa hpb hta hta1 htb htb1 hxa hab hneab
  have m2 := mirror_sum C hP hpc hpd htc htc1 htd htd1 hxc hcd hnecd
  refine mirror_noncross (L := 2 * C.m) (K := 12 - 2 * C.sideS C.sideBeta) (lo := 6)
    (by have := C.one_le; positivity) (k₁ := pa + ta) (k₂ := pc + tc) (k₃ := pb + tb)
    (k₄ := pd + td) ?_ ?_ ?_ hord
  · intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> constructor <;> linarith
  · rcases m1 with ⟨n, hn'⟩ | h | h
    · exact Or.inl ⟨n, by rw [hn']⟩
    · exact Or.inr (Or.inl ⟨h.1, by rw [h.2]; ring⟩)
    · exact Or.inr (Or.inr ⟨by rw [h.1]; ring, h.2⟩)
  · rcases m2 with ⟨n, hn'⟩ | h | h
    · exact Or.inl ⟨n, by rw [hn']⟩
    · exact Or.inr (Or.inl ⟨h.1, by rw [h.2]; ring⟩)
    · exact Or.inr (Or.inr ⟨by rw [h.1]; ring, h.2⟩)

end Pages

end OracleQ

end

end Chazelle.Core
