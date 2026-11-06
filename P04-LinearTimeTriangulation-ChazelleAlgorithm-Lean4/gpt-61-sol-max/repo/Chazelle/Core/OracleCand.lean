module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OracleGraph
public import Chazelle.Core.Facts2

/-!
# Lemma 3.6 (WP-H), part 8: candidate arcs, scanned edges, the empty family

Three facts used by the query program.

* **Candidate arcs** (`candidate`): if the closed key interval of the arc at spine position `t`
  contains the key `κ`, and `j` is an answer of double identification for `κ` (`LocateSpec`: an
  arc containing `κ` in its interior, or, at a cut, starting or ending at `κ`), then `t` is `j`,
  its successor or its predecessor on the spine.  Built on `interior_unique`, `start_unique`,
  `end_start_adj` (the arc ending at a cut is followed by the arc starting there) and `end_unique`.
* **Scanned edges** (`mem_scan`): every point of the chain on (the closed point set of) an arc
  lies on a tour edge whose walk index is among `scanIdx p k`, `k ≤ scanLen p` (the walk edges
  from the one before the start edge to the one after the end edge).
* **The empty family** (`valid_of_graphOK'`): the book data is valid without assuming the family
  nonempty.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideInArc sidePt)

namespace OracleQ

/-! ## Candidate arcs -/

section Cand

variable {M : Model} {Q : Polygon} {N : NF}

/-- The next spine position (cyclically). -/
def succP (A p : ℕ) : ℕ := if p + 1 < A then p + 1 else 0

/-- The previous spine position (cyclically). -/
def predP (A p : ℕ) : ℕ := if p = 0 then A - 1 else p - 1

section
variable {A p : ℕ} (hp : p < A)
include hp
theorem predP_succP : predP A (succP A p) = p := by
  core_grind

theorem succP_lt : succP A p < A := by core_grind

theorem predP_lt : predP A p < A := by core_grind


end

theorem succP_inj {A p q : ℕ} (hp : p < A) (hq : q < A) (h : succP A p = succP A q) : p = q := by
  have := congrArg (predP A) h
  rwa [predP_succP hp, predP_succP hq] at this

variable (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
include hN hGM hne

omit hGM hne in
theorem sk_mono {p q : ℕ} (hpq : p ≤ q) (hq : q < N.arcs.length) : sk M Q N p ≤ sk M Q N q :=
  NFLoc.seq_sorted hN hpq hq

omit hGM in
/-- The arc at a spine position is an arc of a nonempty family: its ends are distinct cuts. -/
theorem arc_facts {p : ℕ} (hp : p < N.arcs.length) :
    M.IsCut (N.F M Q) (sk M Q N p) ∧ M.IsCut (N.F M Q) (ek M Q N p) ∧ sk M Q N p ≠ ek M Q N p ∧
      (∀ x, sideInArc (sk M Q N p) (ek M Q N p) x → ¬ M.IsCut (N.F M Q) x) := by
  obtain ⟨reg, -, -, harc⟩ := isArc_sj hN hp
  obtain ⟨h1, h2, h3⟩ := WalkAx.arc_cuts hne harc
  exact ⟨h1, h2, h3, harc.2.2.2.2.2.1⟩

section
variable {p q : ℕ} (hp : p < N.arcs.length) (hq : q < N.arcs.length)
include hp hq
/-- **Distinct arcs have disjoint interiors.** -/
theorem interior_unique {κ : ℝ}
    (h1 : sideInArc (sk M Q N p) (ek M Q N p) κ) (h2 : sideInArc (sk M Q N q) (ek M Q N q) κ) :
    p = q := by
  by_contra hpq
  rcases lt_or_gt_of_ne hpq with hlt | hlt
  · have a := interior_lt_start hN hGM hne hlt hq h1
    have b := start_lt_interior hN hGM hne hlt hq h1 (by
      linarith [a, (isArc_sj hN hq).choose_spec.2.2.2.1])
    rcases last_interior hN hGM hne hlt hq h2 with c | c <;> linarith
  · have a := interior_lt_start hN hGM hne hlt hp h2
    have b := start_lt_interior hN hGM hne hlt hp h2 (by
      linarith [a, (isArc_sj hN hp).choose_spec.2.2.2.1])
    rcases last_interior hN hGM hne hlt hp h1 with c | c <;> linarith

/-- **Distinct arcs have distinct starts.** -/
theorem start_unique
    (h : sk M Q N p = sk M Q N q) : p = q := by
  by_contra hpq
  rcases lt_or_gt_of_ne hpq with hlt | hlt
  · exact absurd h (starts_lt hN hGM hne hlt hq).ne
  · exact absurd h (starts_lt hN hGM hne hlt hp).ne'

/-- **The arc ending at a cut is followed by the arc starting there.** -/
theorem end_start_adj
    (h : ek M Q N p = sk M Q N q) : q = succP N.arcs.length p := by
  set A := N.arcs.length
  obtain ⟨-, -, hne', hfree⟩ := arc_facts hN hne hp
  unfold succP
  split_ifs with hr
  · set r := p + 1
    have hpr := starts_lt hN hGM hne (show p < r by omega) hr
    have hcr := (arc_facts hN hne hr).1
    -- the arc `p` does not wrap
    have hnw : sk M Q N p < ek M Q N p := by
      grind [sideInArc]
    have hge : ek M Q N p ≤ sk M Q N r := by
      grind [sideInArc]
    rcases eq_or_lt_of_le hge with e | e
    · exact (start_unique hN hGM hne hq hr (h.symm.trans e)).trans rfl
    · exfalso
      rcases le_or_gt q p with hqp | hqp
      · have := sk_mono hN hqp hp; linarith
      · have := sk_mono hN (show r ≤ q by omega) hq; linarith
  · 
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · omega
    · have h0 : 0 < A := by omega
      have hcr := (arc_facts hN hne h0).1
      
      have hqp := sk_mono hN (show q ≤ p by omega) hp
      have hwr : ¬ sk M Q N p < ek M Q N p := by simp_all
      
      have hle : ek M Q N p ≤ sk M Q N 0 := by
        grind [sideInArc]
      have h0q := sk_mono hN (Nat.zero_le q) hq
      exact start_unique hN hGM hne hq h0 (by linarith)

/-- **Distinct arcs have distinct ends** (every cut starts an arc, `arcCover`). -/
theorem end_unique
    (h : ek M Q N p = ek M Q N q) : p = q := by
  obtain ⟨-, hc, -, -⟩ := arc_facts hN hne hp
  obtain ⟨U, hU, b, hab⟩ := (arcCover M Q (N.F M Q) hGM hN.1).2 _ hc
  obtain ⟨j, hj, hjs, -⟩ := NFLoc.listed_of_isArc hN hU hab
  obtain ⟨r, hr, hrj⟩ := NFLoc.seq_surj hN hj
  have hsr : sk M Q N r = ek M Q N p := by
    aesop
  have e1 := end_start_adj hN hGM hne hp hr hsr.symm
  have e2 := end_start_adj hN hGM hne hq hr (h ▸ hsr.symm)
  exact succP_inj hp hq (e1.symm.trans e2)


end

/-- **Candidate arcs.**  If the key `κ` is in the closed arc at spine position `t`, and `j` is an
answer of double identification for `κ`, then `t` is `j`, its successor or its predecessor. -/
theorem candidate {t j : ℕ} (ht : t < N.arcs.length) (hj : j < N.arcs.length) {κ : ℝ}
    (hin : sideInArc (sk M Q N t) (ek M Q N t) κ ∨ κ = sk M Q N t ∨ κ = ek M Q N t)
    (hloc1 : ¬ M.IsCut (N.F M Q) κ → N.F M Q = ∅ ∨ sideInArc (sk M Q N j) (ek M Q N j) κ)
    (hloc2 : M.IsCut (N.F M Q) κ → sk M Q N j = κ ∨ ek M Q N j = κ) :
    t = j ∨ t = succP N.arcs.length j ∨ t = predP N.arcs.length j := by
  obtain ⟨hct, hcte, -, hfree⟩ := arc_facts hN hne ht
  rcases hin with h | h | h
  · have hnc := hfree κ h
    rcases hloc1 hnc with h' | h'
    · simp_all
    · exact Or.inl (interior_unique hN hGM hne ht hj h h')
  · rcases hloc2 (h ▸ hct) with h' | h'
    · exact Or.inl (start_unique hN hGM hne ht hj (h ▸ h'.symm))
    · exact Or.inr (Or.inl (end_start_adj hN hGM hne hj ht (h'.trans h)))
  · rcases hloc2 (h ▸ hcte) with h' | h'
    · have := end_start_adj hN hGM hne ht hj (h.symm.trans h'.symm)
      right; right
      rw [this, predP_succP ht]
    · exact Or.inl (end_unique hN hGM hne ht hj (h.symm.trans h'.symm))

end Cand

/-! ## Scanned edges -/

section Scan

variable (C : Chain) (Q : Polygon) (N : NF)

/-- The number of walk edges scanned for the arc at spine position `p`, minus one: from the edge
before the start edge to the edge after the end edge (the whole walk for a wrapping arc). -/
noncomputable def scanLen (p : ℕ) : ℕ :=
  (if sk (chainModel C) Q N p < ek (chainModel C) Q N p
    then (N.arc (sj N p)).e.edge - (N.arc (sj N p)).s.edge
    else (N.arc (sj N p)).e.edge + (chainModel C).W.n - (N.arc (sj N p)).s.edge) + 2

/-- The `k`-th scanned walk edge of the arc at spine position `p`. -/
def scanIdx (n : ℕ) (N : NF) (p k : ℕ) : ℕ := ((N.arc (sj N p)).s.edge + n - 1 + k) % n

/-- **The scanned points** of the arc at spine position `p`: the tour edges among the scanned
walk edges. -/
noncomputable def scanSet (p : ℕ) : Set Point :=
  {x | ∃ k, k ≤ scanLen C Q N p ∧ ∃ i, i < 2 * C.m ∧
    scanIdx (chainModel C).W.n N p k = i + 6 ∧
    x ∈ Chazelle.segment (C.sideTour C.sideBeta i) (C.sideTour C.sideBeta (i + 1))}

theorem scanSet_subset (p : ℕ) : scanSet C Q N p ⊆ C.set := by
  rintro x ⟨k, -, i, hi, -, hx⟩
  unfold Chain.sideTour at hx
  rcases C.sideTour_step C.sideBeta i with h | h
  · have hk : C.sideIdx C.sideBeta i < C.m := by
      have := C.sideIdx_le C.sideBeta (i + 1); omega
    refine ⟨_, hk, ?_⟩
    rw [C.chainEdge_eq]
    simp_all
  · have hk : C.sideIdx C.sideBeta (i + 1) < C.m := by
      have := C.sideIdx_le C.sideBeta i; omega
    refine ⟨_, hk, ?_⟩
    rw [C.chainEdge_eq, h]
    obtain ⟨s, hs0, hs1, rfl⟩ := hx
    exact ⟨1 - s, by linarith, by linarith, by grind⟩

/-- **The scanned edges cover the chain points of an arc**: a point of the chain on the closed
point set of the arc at spine position `p` (whose ends are proper positions) lies on a scanned
tour edge. -/
theorem mem_scan {p : ℕ}
    (hs : ProperPos (chainModel C) Q Q.n (N.arc (sj N p)).s)
    (he : ProperPos (chainModel C) Q Q.n (N.arc (sj N p)).e)
    (hse : (N.arc (sj N p)).s.edge < (chainModel C).W.n)
    (hee : (N.arc (sj N p)).e.edge < (chainModel C).W.n)
    {x : Point} (hxC : x ∈ C.set)
    (hx : x ∈ (chainModel C).arcSet (sk (chainModel C) Q N p) (ek (chainModel C) Q N p)) :
    x ∈ scanSet C Q N p := by
  set n := (chainModel C).W.n with hn
  have hn7 : n = 2 * C.m + 7 := walk_n C
  set se := (N.arc (sj N p)).s.edge
  set ee := (N.arc (sj N p)).e.edge
  set a := sk (chainModel C) Q N p with ha
  set b := ek (chainModel C) Q N p with hb
  have hak : a = se + (chainModel C).param Q (N.arc (sj N p)).s := rfl
  have hbk : b = ee + (chainModel C).param Q (N.arc (sj N p)).e := rfl
  obtain ⟨hs0, hs1, -⟩ := hs
  obtain ⟨he0, he1, -⟩ := he
  obtain ⟨q, t, hq, ht0, ht1, hkey, rfl⟩ := hx
  -- normalise to a parameter in `[0, 1)`
  obtain ⟨q', t', hq', ht0', ht1', hpt, hkey'⟩ : ∃ q' t', q' < n ∧ 0 ≤ t' ∧ t' < 1 ∧
      sidePt (chainModel C).W q' t' = Geometry.lerp ((chainModel C).wa q) ((chainModel C).wb q) t ∧
      (q' : ℝ) + t' = q + t := by
    rcases eq_or_lt_of_le ht1 with h1 | h1
    · subst h1
      by_cases hlast : q + 1 < n
      · refine ⟨q + 1, 0, hlast, le_rfl, one_pos, ?_, by simp_all⟩
        rw [Chazelle.Chain.sidePt_zero, Geometry.lerp_one]
        show (chainModel C).W.vtx (q + 1) = (chainModel C).W.vtx ((q + 1) % n)
        rw [Nat.mod_eq_of_lt hlast]
      · exfalso
        have hq1 : q + 1 = n := by omega
        have hv : Geometry.lerp ((chainModel C).wa q) ((chainModel C).wb q) 1 = C.slitTop := by
          rw [Geometry.lerp_one]
          show (C.sideWalk C.sideBeta).vtx ((q + 1) % (C.sideWalk C.sideBeta).n) = C.slitTop
          have : (q + 1) % (C.sideWalk C.sideBeta).n = 0 := by
            show (q + 1) % n = 0
            simp_all
          rw [this, C.sideWalk_vtx_zero]
        rw [hv] at hxC
        have := C.snd_le_top_of_mem_set hxC
        simp only [Chain.slitTop] at this
        linarith [C.top_snd_lt_radius]
    · exact ⟨q, t, hq, ht0, h1, rfl, rfl⟩
  rw [← hkey'] at hkey
  rw [← hpt] at hxC ⊢
  -- the edge `q'` is among the scanned ones, at index `k ≥ 1`
  have hq'R : (q' : ℝ) ≤ q' + t' := by linarith
  have hfl : ∀ (e : ℕ) (u : ℝ) (v : ℕ) (w : ℝ), 0 ≤ u → u < 1 → 0 ≤ w → w < 1 →
      (e : ℝ) + u ≤ v + w → e ≤ v := by
    intro e u v w hu hu1 hw hw1 h
    by_contra hc
    push Not at hc
    have : (v : ℝ) + 1 ≤ e := by exact_mod_cast hc
    linarith
  obtain ⟨k, hk1, hkl, hidx⟩ : ∃ k, 1 ≤ k ∧ k + 1 ≤ scanLen C Q N p ∧
      scanIdx n N p k = q' := by
    unfold scanLen scanIdx
    
    by_cases hab : a < b
    · rw [ite_eq_left hab]
      have hk' : a ≤ q' + t' ∧ (q' : ℝ) + t' ≤ b := by
        grind [sideInArc]
      have h1 := hfl se _ q' t' hs0 hs1 ht0' ht1' (hak ▸ hk'.1)
      have h2 := hfl q' t' ee _ ht0' ht1' he0 he1 (hbk ▸ hk'.2)
      refine ⟨q' - se + 1, by omega, by omega, ?_⟩
      rw [show se + n - 1 + (q' - se + 1) = q' + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hq']
    · rw [ite_eq_right hab]
      have hk' : a ≤ q' + t' ∨ (q' : ℝ) + t' ≤ b := by
        grind [sideInArc]
      rcases hk' with h | h
      · have h1 := hfl se _ q' t' hs0 hs1 ht0' ht1' (hak ▸ h)
        refine ⟨q' - se + 1, by omega, by omega, ?_⟩
        rw [show se + n - 1 + (q' - se + 1) = q' + n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hq']
      · have h2 := hfl q' t' ee _ ht0' ht1' he0 he1 (hbk ▸ h)
        refine ⟨q' + n - se + 1, by omega, by omega, ?_⟩
        rw [show se + n - 1 + (q' + n - se + 1) = q' + n + n by omega, Nat.add_mod_right,
          Nat.add_mod_right, Nat.mod_eq_of_lt hq']
  -- the edge is a tour edge (or the closing vertex, the top)
  rw [hn7] at hq'
  rcases pos_on_chain C hq' ht0' ht1' hxC with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨k, by omega, q' - 6, by omega, by grind, ?_⟩
    have := C.sidePt_tour C.sideBeta (i := q' - 6) (by omega) t'
    rw [show q' - 6 + 6 = q' by omega] at this
    show sidePt (C.sideWalk C.sideBeta) q' t' ∈ _
    rw [this]
    exact Geometry.lerp_mem_segment _ _ ht0' ht1'.le
  · subst h1; subst h2
    refine ⟨k - 1, by omega, 2 * C.m - 1, by have := C.one_le; omega, ?_, ?_⟩
    · unfold scanIdx at hidx ⊢
      have hkn : (se + n - 1 + (k - 1)) % n = (se + n - 1 + k + n - 1) % n := by
        rw [show se + n - 1 + k + n - 1 = se + n - 1 + (k - 1) + n by omega, Nat.add_mod_right]
      rw [hkn, Nat.add_sub_assoc (by omega), Nat.add_mod, hidx, hn7]
      have := C.one_le
      rw [Nat.mod_eq_of_lt (show 2 * C.m + 7 - 1 < 2 * C.m + 7 by omega),
        show 2 * C.m + 6 + (2 * C.m + 7 - 1) = (2 * C.m - 1 + 6) + (2 * C.m + 7) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · show sidePt (C.sideWalk C.sideBeta) (2 * C.m + 6) 0 ∈ _
      rw [Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour C.sideBeta le_rfl,
        show 2 * C.m - 1 + 1 = 2 * C.m by have := C.one_le; omega]
      exact Geometry.right_mem_segment _ _

end Scan

/-! ## The empty family -/

/-- With the empty family, a normal form has at most one arc. -/
theorem arcs_le_one_of_empty {M : Model} {Q : Polygon} {N : NF} (hN : IsNF M Q N)
    (hGM : GoodModel M) (hF : N.F M Q = ∅) : N.arcs.length ≤ 1 := by
  obtain ⟨reg, hR, hA, -⟩ := NFLoc.isNF_arcs hN
  obtain ⟨-, hcard, -⟩ := regionTree M Q (N.F M Q) hGM hN.1
  rw [hF, Set.ncard_empty, zero_add] at hcard
  obtain ⟨U, hU⟩ := Set.ncard_eq_one.1 hcard
  by_contra hc
  push Not at hc
  have h0 := hA.1 0 (by omega)
  have h1 := hA.1 1 (by omega)
  have hr0 : reg (N.arc 0).reg = U := by
    have := hR.1 _ h0.1; simp_all
  have hr1 : reg (N.arc 1).reg = U := by
    have := hR.1 _ h1.1; simp_all
  have hreg := hR.2.1 _ _ h0.1 h1.1 (hr0.trans hr1.symm)
  have hk : ∀ j, j < N.arcs.length → M.key Q (N.arc j).s = 0 := by
    intro j hj
    rcases (hA.1 j hj).2.2.2.2.2.1 with ⟨hc, -⟩ | ⟨-, h, -⟩
    · obtain ⟨c, hc, -⟩ := hc; simp_all
    · exact h
  have := hA.2.1 0 1 (by omega) (by omega) hreg (by grind)
  omega

end OracleQ

end

end Chazelle.Core
