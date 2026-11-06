module

public import Chazelle.Core.SpecNF

/-!
# Tree decomposition (WP-C), part 1: rooted trees, components and the edge separator

The region–chord tree of a normal form, once rooted by a breadth-first search, is described by
index functions: `ord` (the search order, a bijection of `[0, R)` with inverse `pos`), `prg` (the
parent region) and `pch` (the parent chord) of every region other than the root `0`.  `Rooted`
collects the facts the search establishes.

For a set of **removed chords** (`rem e = 1`), `ChX` is the child relation avoiding removed
chords and `AncX` its reflexive-transitive closure; a **top** is the root or a region whose parent
chord is removed; the **component** of a top is the set of its `AncX`-descendants; `sz rem u` is
the number of `AncX`-descendants of `u`.

* `AncX.chain`, `top_unique`, `exists_top`: ancestors form a chain, every region has a unique top.
* `sz_rec`: `sz u = 1 + Σ sz c` over the children of `u` in its component.
* `exists_good`: **the edge separator of a tree of maximum degree `D`** — in a component of
  `n ≥ 2` regions there is a non-top region `c` with `n - 1 ≤ D · min (sz c) (n - sz c)`, so
  cutting the parent chord of `c` leaves components with at most `(D - 1)(n - 1) / D` edges each.
-/

namespace Chazelle.Core.Dec

@[expose] public section

open Relation Finset

/-- The facts a breadth-first search from region `0` establishes on the region–chord tree with
`R` regions and `K` chords (chord `i` joins `up i` and `dn i`). -/
structure Rooted (R K : ℕ) (up dn ord pos prg pch : ℕ → ℕ) : Prop where
  hR : R = K + 1
  ord_lt : ∀ i, i < R → ord i < R
  pos_lt : ∀ r, r < R → pos r < R
  ord_pos : ∀ r, r < R → ord (pos r) = r
  pos_ord : ∀ i, i < R → pos (ord i) = i
  root : ord 0 = 0
  prg_lt : ∀ s, s < R → s ≠ 0 → prg s < R
  pos_prg : ∀ s, s < R → s ≠ 0 → pos (prg s) < pos s
  pch_lt : ∀ s, s < R → s ≠ 0 → pch s < K
  ends : ∀ s, s < R → s ≠ 0 →
    (up (pch s) = prg s ∧ dn (pch s) = s) ∨ (up (pch s) = s ∧ dn (pch s) = prg s)
  pch_surj : ∀ i, i < K → ∃ s, s < R ∧ s ≠ 0 ∧ pch s = i
  ends_lt : ∀ i, i < K → up i < R ∧ dn i < R

/-- `y` is a child of `x` (not through a removed chord). -/
def ChX (R : ℕ) (prg pch rem : ℕ → ℕ) (x y : ℕ) : Prop :=
  y < R ∧ y ≠ 0 ∧ prg y = x ∧ rem (pch y) ≠ 1

/-- `a` is an ancestor of `u` in its component (not through a removed chord). -/
def AncX (R : ℕ) (prg pch rem : ℕ → ℕ) : ℕ → ℕ → Prop := ReflTransGen (ChX R prg pch rem)

/-- A top: the root, or a region whose parent chord is removed. -/
def IsTop (pch rem : ℕ → ℕ) (t : ℕ) : Prop := t = 0 ∨ rem (pch t) = 1

instance (pch rem : ℕ → ℕ) (t : ℕ) : Decidable (IsTop pch rem t) :=
  inferInstanceAs (Decidable (t = 0 ∨ rem (pch t) = 1))

/-- No chord removed. -/
def rem0 : ℕ → ℕ := fun _ => 0

section rooted

variable {R K : ℕ} {up dn ord pos prg pch : ℕ → ℕ} (h : Rooted R K up dn ord pos prg pch)
include h

theorem Rooted.pos_inj {r s : ℕ} (hr : r < R) (hs : s < R) (he : pos r = pos s) : r = s := by
  rw [← h.ord_pos r hr, ← h.ord_pos s hs, he]

theorem Rooted.R_pos : 0 < R := by rw [h.hR]; omega

variable {rem : ℕ → ℕ}

/-- An ancestor precedes its descendants in the search order. -/
theorem AncX.pos_le {a b : ℕ} (hab : AncX R prg pch rem a b) (hb : b < R) :
    a < R ∧ pos a ≤ pos b ∧ (a ≠ b → pos a < pos b) := by
  induction hab with
  | refl => exact ⟨hb, le_rfl, fun h => (h rfl).elim⟩
  | tail hax hxc ih =>
    rename_i x c
    obtain ⟨hc, hc0, hpc, -⟩ := hxc
    have hxR : x < R := hpc ▸ h.prg_lt c hc hc0
    have hlt : pos x < pos c := hpc ▸ h.pos_prg c hc hc0
    obtain ⟨ha, hle, -⟩ := ih hxR
    exact ⟨ha, by omega, fun _ => by omega⟩

theorem AncX.antisymm {a b : ℕ} (hab : AncX R prg pch rem a b) (hba : AncX R prg pch rem b a)
    (hb : b < R) : a = b := by
  by_contra hne
  have h1 := (hab.pos_le h hb).2.2 hne
  have ha := (hab.pos_le h hb).1
  have h2 := (hba.pos_le h ha).2.1
  omega

omit h in
/-- The last step of an ancestor path. -/
theorem AncX.back_iff (_h : Rooted R K up dn ord pos prg pch) {a s : ℕ} :
    AncX R prg pch rem a s ↔ a = s ∨ (s < R ∧ s ≠ 0 ∧ rem (pch s) ≠ 1 ∧ AncX R prg pch rem a (prg s)) := by
  constructor
  · intro hs
    rcases hs.cases_tail with e | ⟨x, hax, hx⟩
    · exact Or.inl e.symm
    · obtain ⟨hsR, hs0, hp, hr⟩ := hx
      exact Or.inr ⟨hsR, hs0, hr, hp ▸ hax⟩
  · rintro (rfl | ⟨hsR, hs0, hr, hax⟩)
    · exact ReflTransGen.refl
    · exact hax.tail ⟨hsR, hs0, rfl, hr⟩

/-- Ancestors of a region form a chain. -/
theorem AncX.chain {a b u : ℕ} (hau : AncX R prg pch rem a u) (hbu : AncX R prg pch rem b u) :
    AncX R prg pch rem a b ∨ AncX R prg pch rem b a := by
  induction hau generalizing b with
  | refl => exact Or.inr hbu
  | tail hax hxc ih =>
    rename_i x c
    rcases (AncX.back_iff h).1 hbu with rfl | ⟨-, -, -, hbx⟩
    · exact Or.inl (hax.tail hxc)
    · obtain ⟨-, -, hpc, -⟩ := hxc
      rw [hpc] at hbx
      exact ih hbx

omit h in
/-- A proper descendant is not a top. -/
theorem AncX.not_top {a b : ℕ} (hab : AncX R prg pch rem a b) (hne : a ≠ b) : ¬ IsTop pch rem b := by
  rcases hab.cases_tail with e | ⟨x, -, hx⟩
  · exact (hne e.symm).elim
  · obtain ⟨-, hb0, -, hr⟩ := hx
    rintro (h0 | h1)
    · exact hb0 h0
    · exact hr h1

/-- The top of a region is unique. -/
theorem top_unique {t t' u : ℕ} (ht : IsTop pch rem t) (ht' : IsTop pch rem t')
    (hu : AncX R prg pch rem t u) (hu' : AncX R prg pch rem t' u) : t = t' := by
  rcases AncX.chain h hu hu' with h1 | h1
  · by_contra hne
    exact h1.not_top hne ht'
  · by_contra hne
    exact h1.not_top (Ne.symm hne) ht

/-- Every region has a top. -/
theorem exists_top {u : ℕ} (hu : u < R) : ∃ t, IsTop pch rem t ∧ AncX R prg pch rem t u := by
  induction hp : pos u using Nat.strong_induction_on generalizing u with
  | _ n ih =>
    by_cases ht : IsTop pch rem u
    · exact ⟨u, ht, ReflTransGen.refl⟩
    · simp only [IsTop, not_or] at ht
      have hpR := h.prg_lt u hu ht.1
      obtain ⟨t, htt, hta⟩ := ih (pos (prg u)) (hp ▸ h.pos_prg u hu ht.1) hpR rfl
      exact ⟨t, htt, hta.tail ⟨hu, ht.1, rfl, ht.2⟩⟩

/-- Every region descends from the root (no chord removed). -/
theorem anc_root {u : ℕ} (hu : u < R) : AncX R prg pch rem0 0 u := by
  obtain ⟨t, ht, hta⟩ := exists_top h (rem := rem0) hu
  rcases ht with rfl | h1
  · exact hta
  · simp [rem0] at h1

omit h in
/-- Removing more chords shrinks the ancestor relation. -/
theorem AncX.mono {rem' : ℕ → ℕ} (hrem : ∀ e, rem e = 1 → rem' e = 1) {a b : ℕ}
    (hab : AncX R prg pch rem' a b) : AncX R prg pch rem a b := by
  induction hab with
  | refl => exact ReflTransGen.refl
  | tail _ hxc ih =>
    obtain ⟨h1, h2, h3, h4⟩ := hxc
    exact ih.tail ⟨h1, h2, h3, fun e => h4 (hrem _ e)⟩

omit h in
theorem AncX.to0 {a b : ℕ} (hab : AncX R prg pch rem a b) : AncX R prg pch rem0 a b :=
  AncX.mono (rem := rem0) (fun e he => by simp [rem0] at he) hab

/-- A path whose chords are all kept by `rem'` survives. -/
theorem AncX.of_keep {rem' : ℕ → ℕ} {a b : ℕ} (hab : AncX R prg pch rem a b)
    (hkeep : ∀ w, AncX R prg pch rem a w → AncX R prg pch rem w b → w ≠ a → rem' (pch w) ≠ 1) :
    AncX R prg pch rem' a b := by
  induction hab with
  | refl => exact ReflTransGen.refl
  | tail hax hxc ih =>
    rename_i x c
    have hc : AncX R prg pch rem a c := hax.tail hxc
    refine (ih fun w hw1 hw2 hw3 => hkeep w hw1 (hw2.tail hxc) hw3).tail ?_
    obtain ⟨h1, h2, h3, _⟩ := hxc
    refine ⟨h1, h2, h3, hkeep c hc ReflTransGen.refl ?_⟩
    intro hca
    have hxR : x < R := h3 ▸ h.prg_lt c h1 h2
    have h5 := (AncX.pos_le h hax hxR).2.1
    have h6 := h.pos_prg c h1 h2
    rw [h3, hca] at h6
    omega

/-- The part of a component below one of its regions. -/
theorem AncX.of_anc0 {a b v : ℕ} (hav : AncX R prg pch rem a v) (hbv : AncX R prg pch rem0 b v)
    (hab : AncX R prg pch rem0 a b) (hv : v < R) : AncX R prg pch rem b v := by
  induction hav generalizing b with
  | refl =>
    have hb := (hbv.pos_le h hv).1
    have := AncX.antisymm h hab hbv hb
    subst this
    exact ReflTransGen.refl
  | tail hax hxc ih =>
    rename_i x c
    rcases (AncX.back_iff h).1 hbv with rfl | ⟨-, -, -, hbx⟩
    · exact ReflTransGen.refl
    · have hpc := hxc.2.2.1
      rw [hpc] at hbx
      exact (ih hbx hab (hpc ▸ h.prg_lt c hv hxc.2.1)).tail hxc

/-- The upper part of a component path. -/
theorem AncX.upper {a v w : ℕ} (hav : AncX R prg pch rem a v) (hwv : AncX R prg pch rem0 w v)
    (haw : AncX R prg pch rem0 a w) (hv : v < R) : AncX R prg pch rem a w := by
  induction hav generalizing w with
  | refl =>
    have := AncX.antisymm h hwv haw hv
    rw [this]
    exact ReflTransGen.refl
  | tail hax hxc ih =>
    rename_i x c
    rcases (AncX.back_iff h).1 hwv with rfl | ⟨-, -, -, hwx⟩
    · exact hax.tail hxc
    · have hpc := hxc.2.2.1
      rw [hpc] at hwx
      exact ih hwx haw (hpc ▸ h.prg_lt c hv hxc.2.1)

/-- The parent chords of distinct regions are distinct. -/
theorem Rooted.pch_inj {s s' : ℕ} (hs : s < R) (hs' : s' < R) (h0 : s ≠ 0) (h0' : s' ≠ 0)
    (he : pch s = pch s') : s = s' := by
  by_contra hne
  have p1 := h.pos_prg s hs h0
  have p2 := h.pos_prg s' hs' h0'
  rcases h.ends s hs h0 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases h.ends s' hs' h0' with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> rw [he] at a1 a2
  · exact hne (a2.symm.trans b2)
  · -- `s = prg s'` and `s' = prg s`
    have e1 : s = prg s' := a2.symm.trans b2
    have e2 : s' = prg s := b1.symm.trans a1
    rw [← e1] at p2; rw [← e2] at p1; omega
  · have e1 : s = prg s' := a1.symm.trans b1
    have e2 : s' = prg s := b2.symm.trans a2
    rw [← e1] at p2; rw [← e2] at p1; omega
  · exact hne (a1.symm.trans b1)

/-- With no chord removed below `K`, every region is in the component of the root. -/
theorem anc_root_of {u : ℕ} (hu : u < R) (hrem : ∀ e, e < K → rem e ≠ 1) :
    AncX R prg pch rem 0 u :=
  (anc_root h hu).of_keep h fun w _ hw hw0 =>
    hrem _ (h.pch_lt w (AncX.pos_le h hw hu).1 hw0)

/-- The part of a component below a member `c`. -/
theorem anc_member {t c v : ℕ} (htc : AncX R prg pch rem t c) (hv : v < R) :
    AncX R prg pch rem c v ↔ AncX R prg pch rem t v ∧ AncX R prg pch rem0 c v :=
  ⟨fun hcv => ⟨htc.trans hcv, hcv.to0⟩, fun ⟨htv, hcv⟩ => htv.of_anc0 h hcv htc.to0 hv⟩

end rooted

/-! ## Sizes -/

section sizes

variable (R : ℕ) (prg pch : ℕ → ℕ)

open Classical in
/-- The `AncX`-descendants of `u` (below `R`). -/
noncomputable def sub (rem : ℕ → ℕ) (u : ℕ) : Finset ℕ :=
  (range R).filter (AncX R prg pch rem u)

/-- The number of `AncX`-descendants of `u`: the size of the part of its component below it. -/
noncomputable def sz (rem : ℕ → ℕ) (u : ℕ) : ℕ := (sub R prg pch rem u).card

open Classical in
/-- The children of `u` in its component. -/
noncomputable def kids (rem : ℕ → ℕ) (u : ℕ) : Finset ℕ :=
  (range R).filter (ChX R prg pch rem u)

end sizes

section sizes2

variable {R K : ℕ} {up dn ord pos prg pch : ℕ → ℕ} (h : Rooted R K up dn ord pos prg pch)
include h

variable {rem : ℕ → ℕ}

omit h in
theorem mem_sub {u v : ℕ} : v ∈ sub R prg pch rem u ↔ v < R ∧ AncX R prg pch rem u v := by
  classical
  simp [sub]

omit h in
theorem mem_kids {u c : ℕ} : c ∈ kids R prg pch rem u ↔ ChX R prg pch rem u c := by
  classical
  simp only [kids, mem_filter, mem_range, and_iff_right_iff_imp]
  exact fun hc => hc.1

omit h in
theorem self_mem_sub {u : ℕ} (hu : u < R) : u ∈ sub R prg pch rem u :=
  mem_sub.2 ⟨hu, ReflTransGen.refl⟩

omit h in
theorem sz_pos (_h : Rooted R K up dn ord pos prg pch) {u : ℕ}
    (hu : u < R) : 1 ≤ sz R prg pch rem u :=
  Finset.card_pos.2 ⟨u, self_mem_sub hu⟩

/-- **The size recurrence**: `sz u = 1 + Σ sz c` over the children `c` of `u` in its component. -/
theorem sz_rec {u : ℕ} (hu : u < R) :
    sz R prg pch rem u = 1 + ∑ c ∈ kids R prg pch rem u, sz R prg pch rem c := by
  classical
  have hdisj : (↑(kids R prg pch rem u) : Set ℕ).PairwiseDisjoint (sub R prg pch rem) := by
    intro c hc c' hc' hne
    rw [Finset.mem_coe, mem_kids] at hc hc'
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    rw [mem_sub] at hv hv'
    rcases AncX.chain h hv.2 hv'.2 with h1 | h1
    · rcases (AncX.back_iff h).1 h1 with e | ⟨-, -, -, h2⟩
      · exact hne e
      · rw [hc'.2.2.1] at h2
        have h3 := (h2.pos_le h hu).2.1
        have h4 := h.pos_prg c hc.1 hc.2.1
        rw [hc.2.2.1] at h4
        omega
    · rcases (AncX.back_iff h).1 h1 with e | ⟨-, -, -, h2⟩
      · exact hne e.symm
      · rw [hc.2.2.1] at h2
        have h3 := (h2.pos_le h hu).2.1
        have h4 := h.pos_prg c' hc'.1 hc'.2.1
        rw [hc'.2.2.1] at h4
        omega
  have hnot : u ∉ (kids R prg pch rem u).biUnion (sub R prg pch rem) := by
    rw [Finset.mem_biUnion]
    rintro ⟨c, hc, hu'⟩
    rw [mem_kids] at hc
    rw [mem_sub] at hu'
    have h3 := (hu'.2.pos_le h hu).2.1
    have h4 := h.pos_prg c hc.1 hc.2.1
    rw [hc.2.2.1] at h4
    omega
  have heq : sub R prg pch rem u = insert u ((kids R prg pch rem u).biUnion (sub R prg pch rem)) := by
    ext v
    rw [Finset.mem_insert, Finset.mem_biUnion, mem_sub]
    constructor
    · rintro ⟨hv, hav⟩
      rcases hav.cases_head with e | ⟨c, huc, hcv⟩
      · exact Or.inl e.symm
      · exact Or.inr ⟨c, mem_kids.2 huc, mem_sub.2 ⟨hv, hcv⟩⟩
    · rintro (rfl | ⟨c, hc, hv⟩)
      · exact ⟨hu, ReflTransGen.refl⟩
      · rw [mem_kids] at hc
        rw [mem_sub] at hv
        exact ⟨hv.1, ReflTransGen.head hc hv.2⟩
  unfold sz
  rw [heq, Finset.card_insert_of_notMem hnot, Finset.card_biUnion hdisj]
  omega

/-- A proper descendant has a strictly smaller subtree. -/
theorem sz_lt {a c : ℕ} (hac : AncX R prg pch rem a c) (hne : a ≠ c) (hc : c < R) :
    sz R prg pch rem c + 1 ≤ sz R prg pch rem a := by
  classical
  have ha := (hac.pos_le h hc).1
  have hsub : insert a (sub R prg pch rem c) ⊆ sub R prg pch rem a := by
    intro v hv
    rw [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact self_mem_sub ha
    · rw [mem_sub] at hv ⊢
      exact ⟨hv.1, hac.trans hv.2⟩
  have hna : a ∉ sub R prg pch rem c := by
    rw [mem_sub]
    rintro ⟨-, hca⟩
    exact hne (AncX.antisymm h hac hca hc)
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem hna] at this

end sizes2

/-! ## The edge separator -/

/-- A sum of `card s ≤ D` terms (plus an optional extra term, present iff `e`) equal to `m ≥ 1`
has a term `x` with `m ≤ D x`. -/
theorem pigeon {s : Finset ℕ} (f : ℕ → ℕ) (u m D : ℕ) (e : Prop) [Decidable e]
    (hsum : ∑ c ∈ s, f c + u = m) (hcard : s.card + (if e then 1 else 0) ≤ D)
    (hu : ¬ e → u = 0) (hm : 1 ≤ m) :
    (∃ c ∈ s, m ≤ D * f c) ∨ (e ∧ m ≤ D * u) := by
  classical
  by_contra hno
  simp only [not_or, not_exists, not_and, not_le] at hno
  obtain ⟨h1, h2⟩ := hno
  have hs : ∑ c ∈ s, D * f c ≤ ∑ c ∈ s, m := Finset.sum_le_sum fun c hc => (h1 c hc).le
  rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hs
  by_cases he : e
  · have h2' := h2 he
    rw [ite_eq_left he] at hcard
    have : D * m = D * (∑ c ∈ s, f c) + D * u := by rw [← hsum]; ring
    have h3 : D * m < (s.card + 1) * m := by nlinarith
    have h4 : (s.card + 1) * m ≤ D * m := Nat.mul_le_mul_right _ hcard
    omega
  · have hu0 := hu he
    rw [ite_eq_right he, add_zero] at hcard
    rw [hu0, add_zero] at hsum
    have hne : s.Nonempty := by
      rcases Finset.eq_empty_or_nonempty s with h0 | h0
      · rw [h0, Finset.sum_empty] at hsum; omega
      · exact h0
    have hs' : ∑ c ∈ s, D * f c < ∑ c ∈ s, m := Finset.sum_lt_sum_of_nonempty hne h1
    rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul, hsum] at hs'
    have h4 : s.card * m ≤ D * m := Nat.mul_le_mul_right _ hcard
    omega

section sep

variable {R K : ℕ} {up dn ord pos prg pch : ℕ → ℕ} (h : Rooted R K up dn ord pos prg pch)
include h

variable {rem : ℕ → ℕ} {D : ℕ}

/-- **The edge separator.**  In the component of a top `t` with `n = sz t ≥ 2` regions, if every
region has at most `D` tree neighbours, there is a non-top region `c` of the component with
`n - 1 ≤ D · min (sz c) (n - sz c)`. -/
theorem exists_good
    (hdeg : ∀ v, v < R → (kids R prg pch rem0 v).card + (if v = 0 then 0 else 1) ≤ D)
    {t : ℕ} (ht : t < R) (_htop : IsTop pch rem t) (hn : 2 ≤ sz R prg pch rem t) :
    ∃ c, c < R ∧ AncX R prg pch rem t c ∧ c ≠ t ∧
      sz R prg pch rem t - 1 ≤ D * min (sz R prg pch rem c) (sz R prg pch rem t - sz R prg pch rem c) := by
  classical
  set n := sz R prg pch rem t with hn_def
  set V := (range R).filter (fun v => AncX R prg pch rem t v ∧ n < 2 * sz R prg pch rem v) with hV
  have htV : t ∈ V := by
    rw [hV, Finset.mem_filter, Finset.mem_range]
    exact ⟨ht, ReflTransGen.refl, by omega⟩
  obtain ⟨v, hvV, hvmax⟩ := Finset.exists_max_image V pos ⟨t, htV⟩
  rw [hV, Finset.mem_filter, Finset.mem_range] at hvV
  obtain ⟨hvR, htv, hvbig⟩ := hvV
  -- the children of `v` are small
  have hsmall : ∀ c ∈ kids R prg pch rem v, 2 * sz R prg pch rem c ≤ n := by
    intro c hc
    rw [mem_kids] at hc
    by_contra hbig
    have hcV : c ∈ V := by
      rw [hV, Finset.mem_filter, Finset.mem_range]
      exact ⟨hc.1, htv.tail hc, by omega⟩
    have := hvmax c hcV
    have h4 := h.pos_prg c hc.1 hc.2.1
    rw [hc.2.2.1] at h4
    omega
  -- the kids in the component are tree kids
  have hkids : (kids R prg pch rem v).card ≤ (kids R prg pch rem0 v).card := by
    apply Finset.card_le_card
    intro c hc
    rw [mem_kids] at hc ⊢
    exact ⟨hc.1, hc.2.1, hc.2.2.1, by simp [rem0]⟩
  have hrec := sz_rec h (rem := rem) hvR
  have hvt : v ≠ t → v ≠ 0 := by
    intro hne h0
    exact AncX.not_top htv (Ne.symm hne) (Or.inl h0)
  have hsv : sz R prg pch rem v ≤ n := by
    by_cases e : t = v
    · rw [hn_def, e]
    · have := sz_lt h htv e hvR; omega
  have hcard : (kids R prg pch rem v).card + (if v ≠ t then 1 else 0) ≤ D := by
    have hd := hdeg v hvR
    by_cases e : v = t
    · rw [ite_eq_right (not_not.2 e)]
      have : 0 ≤ (if v = 0 then 0 else 1) := Nat.zero_le _
      omega
    · rw [ite_eq_left e]
      rw [ite_eq_right (hvt e)] at hd
      omega
  have hsum : ∑ c ∈ kids R prg pch rem v, sz R prg pch rem c +
      (if v ≠ t then n - sz R prg pch rem v else 0) = n - 1 := by
    by_cases e : v = t
    · rw [ite_eq_right (not_not.2 e), add_zero]
      rw [e] at hrec ⊢; omega
    · rw [ite_eq_left e]
      omega
  rcases pigeon (fun c => sz R prg pch rem c) _ (n - 1) D (v ≠ t) hsum hcard
    (fun hh => ite_eq_right hh) (by omega) with
    ⟨c, hc, hc'⟩ | ⟨hne, hu⟩
  · have hc2 := hsmall c hc
    rw [mem_kids] at hc
    refine ⟨c, hc.1, htv.tail hc, ?_, ?_⟩
    · intro e
      rw [e] at hc
      have h4 := h.pos_prg t hc.1 hc.2.1
      rw [hc.2.2.1] at h4
      have := (htv.pos_le h hvR).2.1
      omega
    · have : min (sz R prg pch rem c) (n - sz R prg pch rem c) = sz R prg pch rem c :=
        min_eq_left (by omega)
      rw [this]; exact hc'
  · rw [ite_eq_left hne] at hu
    refine ⟨v, hvR, htv, hne, ?_⟩
    have : min (sz R prg pch rem v) (n - sz R prg pch rem v) = n - sz R prg pch rem v :=
      min_eq_right (by omega)
    rw [this]; exact hu

end sep

end

end Chazelle.Core.Dec
