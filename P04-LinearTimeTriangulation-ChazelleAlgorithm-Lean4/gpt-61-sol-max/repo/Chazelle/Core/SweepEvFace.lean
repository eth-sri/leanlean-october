module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoLocal
public import Chazelle.Core.SweepMachine10
public import Chazelle.Core.RestoreTArcs
public import Chazelle.Core.RestoreTNorm
public import Chazelle.Core.Facts2

/-!
# The sweep (WP-D), stages 2–3: the region faced at a walk vertex (task D1, mathematics)

For a walk vertex `fe` of a chain model (key `fe`, position `(fe, 0)`) and an answer `j` of
double identification for its key (`locJ`: inside the arc at spine position `j` if the key is not
a cut, at its start or its end if it is), the regions of the normal form faced just before and
just after the vertex are recorded by the arcs at the spine positions `j - 1`, `j`, `j + 1`:

* just after: the arc at `j + 1` if the arc at `j` ends at the key (`face_after_eq`), else the
  arc at `j` (`face_after_ne`);
* just before: the arc at `j - 1` if the arc at `j` starts at the key (`face_before_eq`), else
  the arc at `j` (`face_before_ne`).

`key_eq_nat_iff`: the key of a proper position is the walk vertex `fe` iff its edge is `fe` and
its normalised height code is `0` (the RAM test).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideInArc)
open OracleQ (sj sk ek succP predP)

namespace Sweep

section FaceMath

/-- **The interior of an arc is open.** -/
theorem sideInArc_nhds {a b x : ℝ} (h : sideInArc a b x) :
    ∃ δ > (0 : ℝ), ∀ s, 0 < s → s < δ → sideInArc a b (x - s) ∧ sideInArc a b (x + s) := by
  unfold sideInArc at h ⊢
  split_ifs at h ⊢ with hab
  · refine ⟨min (x - a) (b - x), lt_min (by simp_all) (by simp_all),
      fun s hs0 hs => ?_⟩
    grind
  · rcases h with h | h
    · exact ⟨x - a, by linarith, fun s hs0 hs => ⟨Or.inl (by linarith), Or.inl (by linarith)⟩⟩
    · exact ⟨b - x, by linarith, fun s hs0 hs => ⟨Or.inr (by linarith), Or.inr (by linarith)⟩⟩

variable {M : Model}

section
variable {F : Set (Set Point)} {U : Set Point} {a b : ℝ} (harc : M.IsArc F U a b) {p : ℕ} (hp : p < M.W.n) (hin : sideInArc a b p)
include F a b harc hp hin
/-- **A walk vertex strictly inside an arc**: its region is faced just after it. -/
theorem afterFaces_of_inArc :
    AfterFaces M p 0 U := by
  obtain ⟨δ, hδ, h⟩ := sideInArc_nhds hin
  refine ⟨δ, hδ, fun s hs0 hs1 hs2 => ?_⟩
  exact harc.2.2.2.2.2.2 p (0 + s) hp (by linarith) hs2 (by simp_all)

/-- **A walk vertex strictly inside an arc**: its region is faced just before it. -/
theorem beforeFaces_of_inArc :
    BeforeFaces M p 0 U := by
  obtain ⟨δ, hδ, h⟩ := sideInArc_nhds hin
  have hn : 0 < M.W.n := by omega
  rcases Nat.eq_zero_or_pos p with rfl | hp1
  · -- the arc wraps around the start of the walk
    have ha0 := harc.1
    have han := harc.2.1
    have hb : ¬ a < b := by
      grind [sideInArc]
    have hnr : (0 : ℝ) < (M.W.n : ℝ) - a := by linarith
    refine ⟨min 1 ((M.W.n : ℝ) - a), lt_min one_pos hnr, fun h0 => absurd h0 (lt_irrefl 0),
      fun _ s hs0 hs1 => ?_⟩
    have h1 := min_le_left 1 ((M.W.n : ℝ) - a)
    have h2 := min_le_right 1 ((M.W.n : ℝ) - a)
    have e : (0 + M.W.n - 1) % M.W.n = M.W.n - 1 := by
      rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [e]
    refine harc.2.2.2.2.2.2 (M.W.n - 1) (1 - s) (by omega) (by linarith) (by linarith) ?_
    have e2 : ((M.W.n - 1 : ℕ) : ℝ) + (1 - s) = (M.W.n : ℝ) - s := by
      rw [Nat.cast_sub (by omega)]; grind
    rw [e2]
    unfold sideInArc
    grind
  · refine ⟨min δ 1, lt_min hδ one_pos, fun h0 => absurd h0 (lt_irrefl 0), fun _ s hs0 hs1 => ?_⟩
    
    have h2 := min_le_right δ 1
    rw [prev_mod hp hp1]
    refine harc.2.2.2.2.2.2 (p - 1) (1 - s) (by omega) (by linarith) (by linarith) ?_
    simp_all


end

section
variable {F : Set (Set Point)} {U : Set Point} {a b : ℝ} (harc : M.IsArc F U a b) (hF : F = ∅) {p : ℕ} (hp : p < M.W.n)
include F a b harc hF hp
/-- **The empty family**: the region of any arc is faced at every position inside a walk edge. -/
theorem faces_of_empty {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : M.Faces p t U := by
  have hab : a = 0 ∧ b = 0 := by
    rcases harc.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, h1, h2⟩
    all_goals simp_all
  refine harc.2.2.2.2.2.2 p t hp ht0 ht1 ?_
  core_grind

theorem afterFaces_of_empty : AfterFaces M p 0 U :=
  ⟨1, one_pos, fun s hs0 _ hs2 => faces_of_empty harc hF hp (by linarith) hs2⟩

theorem beforeFaces_of_empty : BeforeFaces M p 0 U := by
  have hn : 0 < M.W.n := by omega
  exact ⟨1, one_pos, fun h0 => absurd h0 (lt_irrefl 0), fun _ s hs0 hs1 =>
    faces_of_empty harc hF (Nat.mod_lt _ hn) (by linarith) (by linarith)⟩


end

/-- **The key test**: the key of a proper position is the walk vertex `fe` iff its edge is `fe`
and its normalised height code is `0`. -/
theorem key_eq_nat_iff {Q : Polygon} {n : ℕ} {x : WPos} (hx : ProperPos M Q n x) (fe : ℕ) :
    M.key Q x = fe ↔ x.edge = fe ∧ (Restore.normOf M Q x).hgt = 0 := by
  have hk : M.key Q x = x.edge + M.param Q x := rfl
  have hp0 : x.hgt = 0 → M.param Q x = 0 := fun h => by grind [Model.param]
  constructor
  · intro h
    have h1 : (x.edge : ℝ) ≤ fe := by linarith [hx.1]
    have h2 : (fe : ℝ) < x.edge + 1 := by linarith [hx.2.1]
    have e1 : x.edge ≤ fe := by exact_mod_cast h1
    have e2 : fe < x.edge + 1 := by exact_mod_cast h2
    grind [Restore.normOf]
  aesop (add simp [Restore.normOf, add_zero]) (add safe (by omega))

/-- The key of the walk vertex `(p, 0)`. -/
theorem key_vertex (Q : Polygon) (p : ℕ) : M.key Q ⟨p, 0⟩ = p := by
  simp [Model.key, Model.param]

end FaceMath

section FaceNF

variable {C : Chain} {P : Polygon} {N : NF}

/-- The arc at a spine position is an arc of its recorded region. -/
theorem arc_regOf {M : Model} {Q : Polygon} (hN : IsNF M Q N) {p : ℕ}
    (hp : p < N.arcs.length) :
    (N.arc (sj N p)).reg < N.nRegions ∧
      M.IsArc (N.F M Q) (regOf M Q N (N.arc (sj N p)).reg) (sk M Q N p) (ek M Q N p) :=
  (regOf_spec hN).2.2.1.1 _ (NFLoc.seq_lt hN hp)

/-- **A cut at a walk vertex** is not the top of the slit: an arc end at the key `fe` has
`1 ≤ fe`. -/
theorem one_le_of_arc_end (hP : C.P.Simple) (hN : IsNF (chainModel C) (Qof P) N)
    (hne : (N.F (chainModel C) (Qof P)).Nonempty) {p fe : ℕ} (hp : p < N.arcs.length)
    (h : sk (chainModel C) (Qof P) N p = fe ∨ ek (chainModel C) (Qof P) N p = fe) : 1 ≤ fe := by
  have hi := NFLoc.seq_lt hN hp
  obtain ⟨hs, he⟩ := Restore.arc_abs_lt hP hN hne hi
  obtain ⟨pps, ppe⟩ := (regOf_spec hN).2.2.2.2.2.2 _ hi
  have go : ∀ x : WPos, ProperPos (chainModel C) (Qof P) (Qof P).n x →
      |((chainModel C).pos (Qof P) x).2| < C.radius → (chainModel C).key (Qof P) x = fe →
      1 ≤ fe := by
    intro x hx hb hk
    obtain ⟨he', hh⟩ := (key_eq_nat_iff hx fe).1 hk
    have hpar : (chainModel C).param (Qof P) x = 0 := by
      have hk' : (chainModel C).key (Qof P) x = x.edge + (chainModel C).param (Qof P) x := rfl
      simp_all
    have := key_pos_of_band C hb hpar
    omega
  rcases h with h | h
  · exact go _ pps hs h
  · exact go _ ppe he h

variable (hP : C.P.Simple) (hN : IsNF (chainModel C) (Qof P) N) {fe j : ℕ}
  (hfe : fe < (chainModel C).W.n) (hj : j < N.arcs.length)
  (hl1 : ¬ (chainModel C).IsCut (N.F (chainModel C) (Qof P)) fe →
    N.F (chainModel C) (Qof P) = ∅ ∨
      sideInArc (sk (chainModel C) (Qof P) N j) (ek (chainModel C) (Qof P) N j) fe)
  (hl2 : (chainModel C).IsCut (N.F (chainModel C) (Qof P)) fe →
    sk (chainModel C) (Qof P) N j = fe ∨ ek (chainModel C) (Qof P) N j = fe)
include hP hN hfe hj

/-- **Just after, the arc at `j` ends at the vertex**: the region of the arc at `j + 1`. -/
theorem face_after_eq (hE : ek (chainModel C) (Qof P) N j = fe) :
    AfterFaces (chainModel C) fe 0
      (regOf (chainModel C) (Qof P) N (N.arc (sj N (succP N.arcs.length j))).reg) := by
  obtain ⟨-, harcN⟩ := arc_regOf hN (OracleQ.succP_lt hj)
  by_cases hF : N.F (chainModel C) (Qof P) = ∅
  · exact afterFaces_of_empty harcN hF hfe
  have hne : (N.F (chainModel C) (Qof P)).Nonempty := Set.nonempty_iff_ne_empty.2 hF
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  obtain ⟨-, hce, -, -⟩ := OracleQ.arc_facts hN hne hj
  rw [hE] at hce
  obtain ⟨U, hU, b, hab⟩ := (arcCover _ _ _ hGM hN.1).2 _ hce
  obtain ⟨i, hi, his, -⟩ := NFLoc.listed_of_isArc hN hU hab
  obtain ⟨q, hq, hqi⟩ := NFLoc.seq_surj hN hi
  have hsq : sk (chainModel C) (Qof P) N q = fe := by
    show (chainModel C).key (Qof P) (N.arc (N.seq.getD q 0)).s = _
    simp_all
  have hq' := OracleQ.end_start_adj hN hGM hne hj hq (hE.trans hsq.symm)
  subst hq'
  obtain ⟨-, harc⟩ := arc_regOf hN hq
  obtain ⟨-, -, hne', -⟩ := OracleQ.arc_facts hN hne hq
  rw [hsq] at harc hne'
  refine afterFaces_of_arc harc hfe le_rfl ?_
  filter_upwards [WalkAx.eventually_after_start hne'] with s hs
  simp_all

include hl1 hl2 in
omit hP hN hfe hj hl1 hl2 in
/-- **Just after, the arc at `j` does not end at the vertex**: the region of the arc at `j`. -/
theorem face_after_ne (_hP : C.P.Simple) (hN : IsNF (chainModel C) (Qof P) N)
    (hfe : fe < (chainModel C).W.n) (hj : j < N.arcs.length)
    (hl1 : ¬ (chainModel C).IsCut (N.F (chainModel C) (Qof P)) fe → N.F (chainModel C)
    (Qof P) = ∅ ∨ sideInArc (sk (chainModel C) (Qof P) N j) (ek (chainModel C) (Qof P) N j) fe)
    (hl2 : (chainModel C).IsCut (N.F (chainModel C) (Qof P)) fe → sk (chainModel C)
    (Qof P) N j = fe ∨ ek (chainModel C) (Qof P) N j = fe) (hE : ek (chainModel C)
    (Qof P) N j ≠ fe) :
    AfterFaces (chainModel C) fe 0 (regOf (chainModel C) (Qof P) N (N.arc (sj N j)).reg) := by
  obtain ⟨-, harc⟩ := arc_regOf hN hj
  by_cases hF : N.F (chainModel C) (Qof P) = ∅
  · exact afterFaces_of_empty harc hF hfe
  have hne : (N.F (chainModel C) (Qof P)).Nonempty := Set.nonempty_iff_ne_empty.2 hF
  by_cases hc : (chainModel C).IsCut (N.F (chainModel C) (Qof P)) fe
  · rcases hl2 hc with hs | he
    · obtain ⟨-, -, hne', -⟩ := OracleQ.arc_facts hN hne hj
      rw [hs] at harc hne'
      refine afterFaces_of_arc harc hfe le_rfl ?_
      filter_upwards [WalkAx.eventually_after_start hne'] with s hs
      simp_all
    simp_all
  · rcases hl1 hc with h | h
    · simp_all
    · exact afterFaces_of_inArc harc hfe h

/-- **Just before, the arc at `j` starts at the vertex**: the region of the arc at `j - 1`. -/
theorem face_before_eq (hS : sk (chainModel C) (Qof P) N j = fe) :
    BeforeFaces (chainModel C) fe 0
      (regOf (chainModel C) (Qof P) N (N.arc (sj N (predP N.arcs.length j))).reg) := by
  obtain ⟨-, harcP⟩ := arc_regOf hN (OracleQ.predP_lt hj)
  by_cases hF : N.F (chainModel C) (Qof P) = ∅
  · exact beforeFaces_of_empty harcP hF hfe
  have hne : (N.F (chainModel C) (Qof P)).Nonempty := Set.nonempty_iff_ne_empty.2 hF
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  have hM := walkAx_chainModel hP
  have h1 := one_le_of_arc_end hP hN hne hj (Or.inl hS)
  obtain ⟨hcs, -, -, -⟩ := OracleQ.arc_facts hN hne hj
  rw [hS] at hcs
  obtain ⟨c, hc, p', t', hA, hkey⟩ := hcs
  obtain ⟨-, V, l, -, -, hV, -, -, harcV, -⟩ := hM.attach_face hN.1.2.1 hN.1.1 hc hA
  rw [← hkey] at harcV
  obtain ⟨i, hi, -, hie⟩ := NFLoc.listed_of_isArc hN hV harcV
  obtain ⟨q, hq, hqi⟩ := NFLoc.seq_surj hN hi
  have heq : ek (chainModel C) (Qof P) N q = fe := by
    show (chainModel C).key (Qof P) (N.arc (N.seq.getD q 0)).e = _
    simp_all
  have hjq := OracleQ.end_start_adj hN hGM hne hq hj (heq.trans hS.symm)
  have hqP : q = predP N.arcs.length j := by rw [hjq, OracleQ.predP_succP hq]
  subst hqP
  obtain ⟨-, harc⟩ := arc_regOf hN hq
  obtain ⟨-, -, hne', -⟩ := OracleQ.arc_facts hN hne hq
  rw [heq] at harc hne'
  refine beforeFaces_of_arc_end hfe h1 (by rw [add_zero]; exact harc) (by grind)

include hl1 hl2 in
/-- **Just before, the arc at `j` does not start at the vertex**: the region of the arc at `j`. -/
theorem face_before_ne (hS : sk (chainModel C) (Qof P) N j ≠ fe) :
    BeforeFaces (chainModel C) fe 0 (regOf (chainModel C) (Qof P) N (N.arc (sj N j)).reg) := by
  obtain ⟨-, harc⟩ := arc_regOf hN hj
  by_cases hF : N.F (chainModel C) (Qof P) = ∅
  · exact beforeFaces_of_empty harc hF hfe
  have hne : (N.F (chainModel C) (Qof P)).Nonempty := Set.nonempty_iff_ne_empty.2 hF
  by_cases hc : (chainModel C).IsCut (N.F (chainModel C) (Qof P)) fe
  · rcases hl2 hc with hs | he
    · simp_all
    · have h1 := one_le_of_arc_end hP hN hne hj (Or.inr he)
      obtain ⟨-, -, hne', -⟩ := OracleQ.arc_facts hN hne hj
      rw [he] at harc hne'
      exact beforeFaces_of_arc_end hfe h1 (by rw [add_zero]; exact harc)
        (by simp_all)
  · rcases hl1 hc with h | h
    · simp_all
    · exact beforeFaces_of_inArc harc hfe h

end FaceNF

end Sweep

end

end Chazelle.Core
