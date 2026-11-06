module

public import Chazelle.Core.OraclePrepStar

/-!
# Lemma 3.6 (WP-H), preprocessing part 8: the raw zipper pairs

The zipper pairs the preprocessing generates, as a list `zipRaw` of normalised pairs: for every
arc, the arc just before the mirror of its start (`zipSk`) and the arc just after the mirror of
its end (`zipEk`), and five special pairs at the top of the tour (`zipSp`).  Every raw pair is a
chord of the outer page (`zipRaw_sound`), and every pair of arcs meeting at a point of the chain
that is not a spine edge is raw (`zipRaw_complete`).
-/

namespace Chazelle.Core

@[expose] public section

open Chazelle.Chain (sideInArc)

namespace OracleQ

variable (C : Chain) (Q : Polygon) (N : NF)

/-- The normalised pair of two spine positions, if it is not a spine edge or a loop. -/
def normP (a b : ℕ) : Option (ℕ × ℕ) :=
  if min a b + 2 ≤ max a b then some (min a b, max a b) else none

theorem normP_comm (a b : ℕ) : normP a b = normP b a := by
  unfold normP; rw [min_comm, max_comm]

theorem normP_some {a b : ℕ} {c : ℕ × ℕ} (h : normP a b = some c) :
    c.1 + 2 ≤ c.2 ∧ ((c.1 = a ∧ c.2 = b) ∨ (c.1 = b ∧ c.2 = a)) := by
  unfold normP at h
  split_ifs at h with h'
  cases h
  simp only
  refine ⟨h', ?_⟩
  rcases le_total a b with hab | hab
  · left; exact ⟨min_eq_left hab, max_eq_right hab⟩
  · right; exact ⟨min_eq_right hab, max_eq_left hab⟩

theorem normP_of_lt {a b : ℕ} (h : a + 2 ≤ b) : normP a b = some (a, b) := by
  unfold normP; rw [min_eq_left (by omega), max_eq_right (by omega), ite_eq_left h]

theorem normP_none_of_le_one {A a b : ℕ} (hA : A ≤ 1) (ha : a < max A 1) (hb : b < max A 1) :
    normP a b = none := by
  unfold normP; rw [ite_eq_right]; omega

open Classical in
/-- The arc containing the keys just before `y`. -/
noncomputable def befArc (y : ℝ) : ℕ :=
  if h : ∃ q, q < N.arcs.length ∧ Before C Q N q y then h.choose else 0

open Classical in
/-- The arc containing the keys just after `y`. -/
noncomputable def aftArc (y : ℝ) : ℕ :=
  if h : ∃ q, q < N.arcs.length ∧ After C Q N q y then h.choose else 0

/-- Some arc contains `y` in its interior. -/
def InArc (y : ℝ) : Prop :=
  ∃ q, q < N.arcs.length ∧
    sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) y

open Classical in
/-- The arc containing `y` in its interior. -/
noncomputable def inArcIdx (y : ℝ) : ℕ := if h : InArc C Q N y then h.choose else 0

theorem befArc_spec {y : ℝ} (h : ∃ q, q < N.arcs.length ∧ Before C Q N q y) :
    befArc C Q N y < N.arcs.length ∧ Before C Q N (befArc C Q N y) y := by
  unfold befArc; rw [dite_eq_left h]; exact h.choose_spec

theorem aftArc_spec {y : ℝ} (h : ∃ q, q < N.arcs.length ∧ After C Q N q y) :
    aftArc C Q N y < N.arcs.length ∧ After C Q N (aftArc C Q N y) y := by
  unfold aftArc; rw [dite_eq_left h]; exact h.choose_spec

theorem inArcIdx_spec {y : ℝ} (h : InArc C Q N y) :
    inArcIdx C Q N y < N.arcs.length ∧
      sideInArc (sk (chainModel C) Q N (inArcIdx C Q N y)) (ek (chainModel C) Q N (inArcIdx C Q N y)) y := by
  unfold inArcIdx; rw [dite_eq_left h]; exact h.choose_spec

theorem befArc_lt (y : ℝ) : befArc C Q N y < max N.arcs.length 1 := by
  unfold befArc; split_ifs with h
  · exact lt_max_of_lt_left h.choose_spec.1
  · exact lt_max_of_lt_right one_pos

theorem aftArc_lt (y : ℝ) : aftArc C Q N y < max N.arcs.length 1 := by
  unfold aftArc; split_ifs with h
  · exact lt_max_of_lt_left h.choose_spec.1
  · exact lt_max_of_lt_right one_pos

theorem inArcIdx_lt (y : ℝ) : inArcIdx C Q N y < max N.arcs.length 1 := by
  unfold inArcIdx; split_ifs with h
  · exact lt_max_of_lt_left h.choose_spec.1
  · exact lt_max_of_lt_right one_pos

open Classical in
/-- The pair of the start of arc `x`. -/
noncomputable def zipSk (x : ℕ) : Option (ℕ × ℕ) :=
  if InI C (sk (chainModel C) Q N x) ∧
      ∃ q, q < N.arcs.length ∧ Before C Q N q (mk C (sk (chainModel C) Q N x))
  then normP x (befArc C Q N (mk C (sk (chainModel C) Q N x))) else none

open Classical in
/-- The pair of the end of arc `x`. -/
noncomputable def zipEk (x : ℕ) : Option (ℕ × ℕ) :=
  if InI C (ek (chainModel C) Q N x) ∧
      ∃ q, q < N.arcs.length ∧ After C Q N q (mk C (ek (chainModel C) Q N x))
  then normP (aftArc C Q N (mk C (ek (chainModel C) Q N x))) x else none

open Classical in
/-- The special pair after `6` and before `κT`. -/
noncomputable def sp1 : Option (ℕ × ℕ) :=
  if 0 < rT C ∧ (∃ p, p < N.arcs.length ∧ After C Q N p 6) ∧
      (∃ q, q < N.arcs.length ∧ Before C Q N q (κT C))
    then normP (aftArc C Q N 6) (befArc C Q N (κT C)) else none

open Classical in
/-- The special pair after `κT` and before `2 m + 6`. -/
noncomputable def sp2 : Option (ℕ × ℕ) :=
  if (∃ p, p < N.arcs.length ∧ After C Q N p (κT C)) ∧
      (∃ q, q < N.arcs.length ∧ Before C Q N q (2 * C.m + 6))
    then normP (aftArc C Q N (κT C)) (befArc C Q N (2 * C.m + 6)) else none

open Classical in
/-- The top pair at `6` and `κT`. -/
noncomputable def sp3 : Option (ℕ × ℕ) :=
  if 0 < rT C ∧ InArc C Q N 6 ∧ InArc C Q N (κT C)
    then normP (inArcIdx C Q N 6) (inArcIdx C Q N (κT C)) else none

open Classical in
/-- The top pair at `κT` and `2 m + 6`. -/
noncomputable def sp4 : Option (ℕ × ℕ) :=
  if InArc C Q N (κT C) ∧ InArc C Q N (2 * C.m + 6)
    then normP (inArcIdx C Q N (κT C)) (inArcIdx C Q N (2 * C.m + 6)) else none

open Classical in
/-- The top pair at `6` and `2 m + 6`. -/
noncomputable def sp5 : Option (ℕ × ℕ) :=
  if InArc C Q N 6 ∧ InArc C Q N (2 * C.m + 6)
    then normP (inArcIdx C Q N 6) (inArcIdx C Q N (2 * C.m + 6)) else none

/-- The five special pairs at the top of the tour. -/
noncomputable def zipSpO : List (Option (ℕ × ℕ)) :=
  [sp1 C Q N, sp2 C Q N, sp3 C Q N, sp4 C Q N, sp5 C Q N]

/-- The special pairs. -/
noncomputable def zipSp : List (ℕ × ℕ) := (zipSpO C Q N).filterMap id

/-- **The raw zipper pairs.** -/
noncomputable def zipRaw : List (ℕ × ℕ) :=
  OracleR.emitted (zipSk C Q N) N.arcs.length ++ OracleR.emitted (zipEk C Q N) N.arcs.length ++
    zipSp C Q N

variable {C Q N}

/-- The pair of a generating case is a zipper pair, in both orders. -/
theorem pair_of_gen (hN : IsNF (chainModel C) Q N) (hP : C.P.Simple)
    (hne : (N.F (chainModel C) Q).Nonempty) {a b : ℕ} {c : ℕ × ℕ} (ha : a < N.arcs.length)
    (hb : b < N.arcs.length) (hG : ZipGen C Q N a b) (h : normP a b = some c) :
    c.1 + 2 ≤ c.2 ∧ c.2 < N.arcs.length ∧ ZipRel C Q N c.1 c.2 := by
  obtain ⟨h1, h2⟩ := normP_some h
  have hZ := zipRel_of_gen hN hP hne ha hb hG
  rcases h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]; exact ⟨by omega, hb, hZ⟩
  · rw [e1, e2]; exact ⟨by omega, ha, hZ.symm⟩

/-- **Every raw pair is a zipper chord**: not a spine edge, in range, and a zipper pair. -/
theorem zipRaw_sound (hN : IsNF (chainModel C) Q N) (hP : C.P.Simple) {c : ℕ × ℕ}
    (hc : c ∈ zipRaw C Q N) : c.1 + 2 ≤ c.2 ∧ c.2 < N.arcs.length ∧ ZipRel C Q N c.1 c.2 := by
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  by_cases hne : (N.F (chainModel C) Q).Nonempty
  swap
  · -- the empty family: at most one arc, so no pair
    exfalso
    have hA := arcs_le_one_of_empty hN hGM (Set.not_nonempty_iff_eq_empty.1 hne)
    unfold zipRaw zipSp zipSpO at hc
    simp only [List.mem_append, OracleR.mem_emitted, List.mem_filterMap, List.mem_cons,
      List.mem_nil_iff, or_false, id] at hc
    rcases hc with (⟨j, hj, hφ⟩ | ⟨j, hj, hφ⟩) | ⟨o, ho, ho'⟩
    · unfold zipSk at hφ; split_ifs at hφ
      rw [normP_none_of_le_one hA (by omega) (befArc_lt C Q N _)] at hφ; cases hφ
    · unfold zipEk at hφ; split_ifs at hφ
      rw [normP_none_of_le_one hA (aftArc_lt C Q N _) (by omega)] at hφ; cases hφ
    · have n1 := normP_none_of_le_one hA (aftArc_lt C Q N 6) (befArc_lt C Q N (κT C))
      have n2 := normP_none_of_le_one hA (aftArc_lt C Q N (κT C)) (befArc_lt C Q N (2 * C.m + 6))
      have n3 := normP_none_of_le_one hA (inArcIdx_lt C Q N 6) (inArcIdx_lt C Q N (κT C))
      have n4 := normP_none_of_le_one hA (inArcIdx_lt C Q N (κT C))
        (inArcIdx_lt C Q N (2 * C.m + 6))
      have n5 := normP_none_of_le_one hA (inArcIdx_lt C Q N 6) (inArcIdx_lt C Q N (2 * C.m + 6))
      rcases ho with rfl | rfl | rfl | rfl | rfl
      · unfold sp1 at ho'; split_ifs at ho'; simp_all
      · unfold sp2 at ho'; split_ifs at ho'; simp_all
      · unfold sp3 at ho'; split_ifs at ho'; simp_all
      · unfold sp4 at ho'; split_ifs at ho'; simp_all
      · unfold sp5 at ho'; split_ifs at ho'; simp_all
  unfold zipRaw zipSp zipSpO at hc
  simp only [List.mem_append, OracleR.mem_emitted, List.mem_filterMap, List.mem_cons,
    List.mem_nil_iff, or_false, id] at hc
  rcases hc with (⟨j, hj, hφ⟩ | ⟨j, hj, hφ⟩) | ⟨o, ho, ho'⟩
  · unfold zipSk at hφ; split_ifs at hφ with h
    obtain ⟨hI, hex⟩ := h
    obtain ⟨hb, hB⟩ := befArc_spec C Q N hex
    exact pair_of_gen hN hP hne hj hb (Or.inr (Or.inl ⟨hI, hB⟩)) hφ
  · unfold zipEk at hφ; split_ifs at hφ with h
    obtain ⟨hI, hex⟩ := h
    obtain ⟨ha, hA'⟩ := aftArc_spec C Q N hex
    exact pair_of_gen hN hP hne ha hj (Or.inr (Or.inr (Or.inl ⟨hI, hA'⟩))) hφ
  · have hT6 := κT_ge C
    have hT7 := κT_lt C
    have hTdef := rT_def C
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · unfold sp1 at ho'; split_ifs at ho' with h
      obtain ⟨hr, e1, e2⟩ := h
      obtain ⟨ha, hA'⟩ := aftArc_spec C Q N e1
      obtain ⟨hb, hB⟩ := befArc_spec C Q N e2
      have : (6 : ℝ) < κT C := by
        rw [← hTdef]; have : (0 : ℝ) < rT C := by exact_mod_cast hr
        linarith
      exact pair_of_gen hN hP hne ha hb (Or.inr (Or.inr (Or.inr (Or.inl ⟨this, hA', hB⟩)))) ho'
    · unfold sp2 at ho'; split_ifs at ho' with h
      obtain ⟨e1, e2⟩ := h
      obtain ⟨ha, hA'⟩ := aftArc_spec C Q N e1
      obtain ⟨hb, hB⟩ := befArc_spec C Q N e2
      exact pair_of_gen hN hP hne ha hb (Or.inr (Or.inr (Or.inr (Or.inr ⟨hA', hB⟩)))) ho'
    · unfold sp3 at ho'; split_ifs at ho' with h
      obtain ⟨hr, e1, e2⟩ := h
      obtain ⟨ha, hA'⟩ := inArcIdx_spec C Q N e1
      obtain ⟨hb, hB⟩ := inArcIdx_spec C Q N e2
      have : (6 : ℝ) ≠ κT C := by
        rw [← hTdef]; have : (0 : ℝ) < rT C := by exact_mod_cast hr
        intro h; linarith
      exact pair_of_gen hN hP hne ha hb (Or.inl ⟨6, κT C, Or.inl rfl, Or.inr (Or.inl rfl), this,
        hA', hB⟩) ho'
    · unfold sp4 at ho'; split_ifs at ho' with h
      obtain ⟨e1, e2⟩ := h
      obtain ⟨ha, hA'⟩ := inArcIdx_spec C Q N e1
      obtain ⟨hb, hB⟩ := inArcIdx_spec C Q N e2
      exact pair_of_gen hN hP hne ha hb (Or.inl ⟨κT C, 2 * C.m + 6, Or.inr (Or.inl rfl),
        Or.inr (Or.inr rfl), by intro h; linarith, hA', hB⟩) ho'
    · unfold sp5 at ho'; split_ifs at ho' with h
      obtain ⟨e1, e2⟩ := h
      obtain ⟨ha, hA'⟩ := inArcIdx_spec C Q N e1
      obtain ⟨hb, hB⟩ := inArcIdx_spec C Q N e2
      have hm : (0 : ℝ) < C.m := by exact_mod_cast C.one_le
      exact pair_of_gen hN hP hne ha hb (Or.inl ⟨6, 2 * C.m + 6, Or.inl rfl,
        Or.inr (Or.inr rfl), by intro h; linarith, hA', hB⟩) ho'

theorem mem_zipSp {o : Option (ℕ × ℕ)} (ho : o ∈ zipSpO C Q N) {c : ℕ × ℕ} (h : o = some c) :
    c ∈ zipSp C Q N := by
  unfold zipSp; rw [List.mem_filterMap]; exact ⟨o, ho, by rw [h]; rfl⟩

/-- **Every zipper pair that is not a spine edge is raw.** -/
theorem zipRaw_complete (hN : IsNF (chainModel C) Q N) (hP : C.P.Simple) {p q : ℕ} (hpq : p < q)
    (hq : q < N.arcs.length) (hZ : ZipRel C Q N p q) : q = p + 1 ∨ (p, q) ∈ zipRaw C Q N := by
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  by_cases hq1 : q = p + 1
  · exact Or.inl hq1
  right
  have h2 : p + 2 ≤ q := by omega
  have hp : p < N.arcs.length := by omega
  have hne : (N.F (chainModel C) Q).Nonempty := by
    by_contra hF
    have := arcs_le_one_of_empty hN hGM (Set.not_nonempty_iff_eq_empty.1 hF)
    omega
  have hn : normP p q = some (p, q) := normP_of_lt h2
  have hn' : normP q p = some (p, q) := by rw [normP_comm]; exact hn
  have hT6 := κT_ge C
  have hT7 := κT_lt C
  have hTdef := rT_def C
  have hm : (0 : ℝ) < C.m := by exact_mod_cast C.one_le
  have inIdx : ∀ {r : ℕ} {y : ℝ}, r < N.arcs.length →
      sideInArc (sk (chainModel C) Q N r) (ek (chainModel C) Q N r) y →
      InArc C Q N y ∧ inArcIdx C Q N y = r := fun {r y} hr h => by
    have hin : InArc C Q N y := ⟨r, hr, h⟩
    obtain ⟨a, b⟩ := inArcIdx_spec C Q N hin
    exact ⟨hin, interior_unique hN hGM hne a hr b h⟩
  have hr0 : ∀ {x : ℝ}, x ≠ κT C → x = 6 → 0 < rT C := fun {x} h1 h2 => by
    subst h2
    by_contra h0
    have : rT C = 0 := by omega
    apply h1; rw [← hTdef, this]; norm_num
  unfold zipRaw
  simp only [List.mem_append, OracleR.mem_emitted]
  rcases zip_cases hN hP hne hp hq (by omega) hZ with
    ⟨x, y, hx, hy, hxy, h1, h2'⟩ | ⟨hI, hB⟩ | ⟨hI, hA⟩ | ⟨h6, hA, hB⟩ | ⟨hA, hB⟩
  · right
    obtain ⟨ix, ex⟩ := inIdx hp h1
    obtain ⟨iy, ey⟩ := inIdx hq h2'
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact mem_zipSp (o := sp3 C Q N) (by simp [zipSpO]) (by
        unfold sp3; rw [ite_eq_left ⟨hr0 hxy rfl, ix, iy⟩, ex, ey, hn])
    · exact mem_zipSp (o := sp5 C Q N) (by simp [zipSpO]) (by
        unfold sp5; rw [ite_eq_left ⟨ix, iy⟩, ex, ey, hn])
    · exact mem_zipSp (o := sp3 C Q N) (by simp [zipSpO]) (by
        unfold sp3; rw [ite_eq_left ⟨hr0 (Ne.symm hxy) rfl, iy, ix⟩, ex, ey, hn'])
    · exact absurd rfl hxy
    · exact mem_zipSp (o := sp4 C Q N) (by simp [zipSpO]) (by
        unfold sp4; rw [ite_eq_left ⟨ix, iy⟩, ex, ey, hn])
    · exact mem_zipSp (o := sp5 C Q N) (by simp [zipSpO]) (by
        unfold sp5; rw [ite_eq_left ⟨iy, ix⟩, ex, ey, hn'])
    · exact mem_zipSp (o := sp4 C Q N) (by simp [zipSpO]) (by
        unfold sp4; rw [ite_eq_left ⟨iy, ix⟩, ex, ey, hn'])
    · exact absurd rfl hxy
  · left; left
    refine ⟨p, hp, ?_⟩
    have hex : ∃ q', q' < N.arcs.length ∧ Before C Q N q' (mk C (sk (chainModel C) Q N p)) :=
      ⟨q, hq, hB⟩
    obtain ⟨hb, hB'⟩ := befArc_spec C Q N hex
    unfold zipSk
    rw [ite_eq_left ⟨hI, hex⟩, before_unique hN hP hne hb hq hB' hB, hn]
  · left; right
    refine ⟨q, hq, ?_⟩
    have hex : ∃ p', p' < N.arcs.length ∧ After C Q N p' (mk C (ek (chainModel C) Q N q)) :=
      ⟨p, hp, hA⟩
    obtain ⟨ha, hA'⟩ := aftArc_spec C Q N hex
    unfold zipEk
    rw [ite_eq_left ⟨hI, hex⟩, after_unique hN hP hne ha hp hA' hA, hn]
  · right
    have e1 : ∃ p', p' < N.arcs.length ∧ After C Q N p' 6 := ⟨p, hp, hA⟩
    have e2 : ∃ q', q' < N.arcs.length ∧ Before C Q N q' (κT C) := ⟨q, hq, hB⟩
    have hr : 0 < rT C := by
      by_contra h0
      have : rT C = 0 := by omega
      rw [← hTdef, this] at h6; norm_num at h6
    obtain ⟨ha, hA'⟩ := aftArc_spec C Q N e1
    obtain ⟨hb, hB'⟩ := befArc_spec C Q N e2
    exact mem_zipSp (o := sp1 C Q N) (by simp [zipSpO]) (by
      unfold sp1; rw [ite_eq_left ⟨hr, e1, e2⟩, after_unique hN hP hne ha hp hA' hA,
        before_unique hN hP hne hb hq hB' hB, hn])
  · right
    have e1 : ∃ p', p' < N.arcs.length ∧ After C Q N p' (κT C) := ⟨p, hp, hA⟩
    have e2 : ∃ q', q' < N.arcs.length ∧ Before C Q N q' (2 * C.m + 6) := ⟨q, hq, hB⟩
    obtain ⟨ha, hA'⟩ := aftArc_spec C Q N e1
    obtain ⟨hb, hB'⟩ := befArc_spec C Q N e2
    exact mem_zipSp (o := sp2 C Q N) (by simp [zipSpO]) (by
      unfold sp2; rw [ite_eq_left ⟨e1, e2⟩, after_unique hN hP hne ha hp hA' hA,
        before_unique hN hP hne hb hq hB' hB, hn])

end OracleQ

end

end Chazelle.Core
