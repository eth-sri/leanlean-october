module

public import Chazelle.Core.Lemma41Ram8
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
set_option maxHeartbeats 16000000

/-!
# WP-J, part 17: the shapes of the next level, and the carry

* `pairUp ns t`: the shapes of the next level (neighbours merged with target `t`, an odd last node
  carried); its length, entries, consecutiveness and total length (`pairUp_length`,
  `nd_pairUp_merge`, `nd_pairUp_carry`, `consec_pairUp`, `pairUp_sum`);
* `CellSt`: the nodes of the next level as a back-linked list of cells `[descriptor, NF, prev]`;
* `carryS`: after the pair loop, an odd last node gets a cell too (`carryS_exec`).
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs Chazelle.Merge Finset

@[expose] public section

/-- **The shapes of the next level.** -/
def pairUp : List Shp → ℕ → List Shp
  | a :: b :: rest, t => (a.1, a.2.1 + b.2.1, t) :: pairUp rest t
  | l, _ => l

theorem pairUp_length : ∀ (l : List Shp) (t : ℕ), (pairUp l t).length = (l.length + 1) / 2
  | [], _ => by simp [pairUp]
  | [_], _ => by simp [pairUp]
  | a :: b :: rest, t => by
    sio only [pairUp, List.length_cons, pairUp_length rest t]

theorem nd_cons_succ (a : Shp) (l : List Shp) (k : ℕ) : nd (a :: l) (k + 1) = nd l k := by
  simp [nd]

theorem nd_cons_zero (a : Shp) (l : List Shp) : nd (a :: l) 0 = a := by simp [nd]

theorem nd_pairUp_merge : ∀ (l : List Shp) (t q : ℕ), q < l.length / 2 →
    nd (pairUp l t) q = ((nd l (2 * q)).1, (nd l (2 * q)).2.1 + (nd l (2 * q + 1)).2.1, t)
  | [], _, q, h => by simp at h
  | [_], _, q, h => by simp at h
  | a :: b :: rest, t, 0, _ => by
    simp only [pairUp, Nat.mul_zero, Nat.zero_add, nd_cons_zero, nd_cons_succ]
  | a :: b :: rest, t, q + 1, h => by
    have ih := nd_pairUp_merge rest t q (by sio only [List.length_cons] at h)
    have e1 : nd (a :: b :: rest) (2 * (q + 1)) = nd rest (2 * q) := by
      rw [show 2 * (q + 1) = 2 * q + 1 + 1 by ring, nd_cons_succ, nd_cons_succ]
    have e2 : nd (a :: b :: rest) (2 * (q + 1) + 1) = nd rest (2 * q + 1) := by
      rw [show 2 * (q + 1) + 1 = 2 * q + 1 + 1 + 1 by ring, nd_cons_succ, nd_cons_succ]
    rw [e1, e2]
    simp only [pairUp]
    rw [nd_cons_succ]
    exact ih

theorem nd_pairUp_carry : ∀ (l : List Shp) (t : ℕ), l.length % 2 = 1 →
    nd (pairUp l t) (l.length / 2) = nd l (l.length - 1)
  | [], _, h => by simp at h
  | [_], _, _ => by simp [pairUp]
  | a :: b :: rest, t, h => by
    simp only [List.length_cons] at h ⊢
    have ih := nd_pairUp_carry rest t (by omega)
    have h1 : 1 ≤ rest.length := by omega
    simp only [pairUp]
    rw [show (rest.length + 1 + 1) / 2 = rest.length / 2 + 1 by omega, nd_cons_succ,
      show rest.length + 1 + 1 - 1 = rest.length - 1 + 1 + 1 by omega, nd_cons_succ,
      nd_cons_succ]
    exact ih

theorem nd_pairUp_zero (l : List Shp) (t : ℕ) (h : 1 ≤ l.length) :
    (nd (pairUp l t) 0).1 = (nd l 0).1 := by
  rcases Nat.lt_or_ge 1 l.length with h2 | h2
  · rw [nd_pairUp_merge l t 0 (by omega)]
  · have : l.length = 1 := by omega
    have := nd_pairUp_carry l t (by omega)
    rw [show l.length / 2 = 0 by omega, show l.length - 1 = 0 by omega] at this
    rw [this]

/-- **The next level is consecutive.** -/
theorem consec_pairUp {l : List Shp} (t : ℕ) (h : Consec l) : Consec (pairUp l t) := by
  intro q hq
  rw [pairUp_length] at hq
  have hq0 : q < l.length / 2 := by omega
  rw [nd_pairUp_merge l t q hq0]
  have e1 : (nd (pairUp l t) (q + 1)).1 = (nd l (2 * q + 2)).1 := by
    rcases Nat.lt_or_ge (q + 1) (l.length / 2) with h1 | h1
    · rwr [nd_pairUp_merge l t (q + 1) h1]
    · have hodd : l.length % 2 = 1 := by omega
      have := nd_pairUp_carry l t hodd
      rw [show l.length / 2 = q + 1 by omega, show l.length - 1 = 2 * q + 2 by omega] at this
      rw [this]
  rw [e1, h (2 * q + 1) (by omega), h (2 * q) (by omega)]
  sir only

theorem pairUp_sum : ∀ (l : List Shp) (t : ℕ),
    ((pairUp l t).map fun x => x.2.1).sum = (l.map fun x => x.2.1).sum
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, t => by
    sir only [pairUp, List.map_cons, List.sum_cons, pairUp_sum rest t]

/-- The granularities of the next level are at most the target. -/
theorem pairUp_gran {l : List Shp} {t γ₀ : ℕ} (hγ : ∀ k, k < l.length → (nd l k).2.2 ≤ γ₀)
    (ht : γ₀ ≤ t) : ∀ k, k < (pairUp l t).length → (nd (pairUp l t) k).2.2 ≤ t := by
  intro k hk
  rw [pairUp_length] at hk
  rcases Nat.lt_or_ge k (l.length / 2) with h1 | h1
  · rw [nd_pairUp_merge l t k h1]
  · have hodd : l.length % 2 = 1 := by omega
    have := nd_pairUp_carry l t hodd
    rw [show k = l.length / 2 by omega, this]
    exact (hγ _ (by omega)).trans ht

theorem pairUp_gran_pos {l : List Shp} {t : ℕ} (hγ : ∀ k, k < l.length → 1 ≤ (nd l k).2.2)
    (ht : 1 ≤ t) : ∀ k, k < (pairUp l t).length → 1 ≤ (nd (pairUp l t) k).2.2 := by
  intro k hk
  rw [pairUp_length] at hk
  rcases Nat.lt_or_ge k (l.length / 2) with h1 | h1
  · rwx [nd_pairUp_merge l t k h1]
  · have hodd : l.length % 2 = 1 := by omega
    have := nd_pairUp_carry l t hodd
    rw [show k = l.length / 2 by omega, this]
    exact hγ _ (by omega)

/-- **The nodes of the next level as back-linked cells** `[descriptor, NF, prev]`. -/
def CellSt (P : Polygon) (m : ℕ → ℕ) (A hp : ℕ) (ns : List Shp) (e : ℕ → ℕ) : Prop :=
  ∀ q, q < ns.length → e q + 3 ≤ A ∧ (1 ≤ q → m (e q + 2) = e (q - 1)) ∧
    ∃ C : Chain, C.s = (nd ns q).1 ∧ C.m = (nd ns q).2.1 ∧
      NodeOK P m A hp (m (e q)) (m (e q + 1)) C (nd ns q).2.2

/-- The cell of a carried node. -/
def carryB : Stmt := block [.loadN 160035 160065, .addN 160093 160065 160024,
  .loadN 160090 160093, .copyN 160092 9999, .storeN 160092 160035, .addN 160093 160092 160024,
  .storeN 160093 160090, .addN 160093 160093 160024, .storeN 160093 160063, .copyN 160063 160092,
  .addN 9999 9999 160083, .addN 160064 160064 160024]

/-- **The carry** of an odd last node. -/
def carryS : Stmt := .ifLtN 160062 160014 carryB .skip

section proofs

variable {P : Polygon} {W : ℕ}

theorem carryB_exec {c : Config} (hw : WordsBounded W c) {E ptr prev j : ℕ}
    (hA : c.nreg ALLOC = E) (h65 : c.nreg 160065 = ptr) (h63 : c.nreg 160063 = prev)
    (h64 : c.nreg 160064 = j) (h24 : c.nreg 160024 = 1) (h83 : c.nreg 160083 = 3)
    (hW : E + 3 ≤ W) (hWp : ptr + 1 ≤ W) (hWj : j + 1 ≤ W) :
    ∃ c' k, Exec P W carryB c c' k ∧ k = 12 ∧ WordsBounded W c' ∧
      c'.nmem E = c.nmem ptr ∧ c'.nmem (E + 1) = c.nmem (ptr + 1) ∧ c'.nmem (E + 2) = prev ∧
      (∀ a, (a < E ∨ E + 3 ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.nreg ALLOC = E + 3 ∧ c'.nreg 160063 = E ∧ c'.nreg 160064 = j + 1 ∧
      (∀ r, r ≠ 160035 → r ≠ 160090 → r ≠ 160092 → r ≠ 160093 → r ≠ 160063 → r ≠ 160064 →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold carryB
  exec_block
  all_goals try (config_simp; (try simp only [hA, h65, h64, h24, h83]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, fun a ha => ?_, ?_, ?_, ?_,
    fun r a1 a2 a3 a4 a5 a6 a7 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [hA, h65, h24, Machine.upd_apply]; splao
  · config_simp; simp only [hA, h65, h24, Machine.upd_apply]; splao
  · config_simp; simp only [hA, h63, h24, Machine.upd_apply]; splao
  · config_simp; simp only [hA, h24, Machine.upd_apply]; split_ifs <;> first | omega
  · config_simp; simp only [hA, h83]
  · config_simp; simp only [hA]
  · config_simp; simp only [h64, h24]
  · simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

/-- **The carry.** -/
theorem carryS_exec {X : MemCtx} {c0 c : Config} {A0 B hp hX tgt : ℕ} {ns : List Shp}
    {pcs : ℕ → ℕ} (hj : 1 ≤ ns.length)
    (hst : PairSt P W X c0 A0 B hp hX tgt ns pcs (ns.length / 2) c)
    (h14 : c0.nreg 160014 = ns.length) (h24 : c0.nreg 160024 = 1) (h83 : c0.nreg 160083 = 3)
    (hL : LevelAt P c0.nmem A0 B hp ns) (hB : B + 2 * ns.length ≤ A0)
    (hW : c.nreg ALLOC + 3 ≤ W) :
    ∃ c' k, Exec P W carryS c c' k ∧ k ≤ 14 ∧ WordsBounded W c' ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + 3 ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output ∧ c'.rreg = c.rreg ∧
      (∀ r, ¬ PairRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nreg 160064 = (pairUp ns tgt).length ∧
      ∃ e : ℕ → ℕ, CellSt P c'.nmem (c'.nreg ALLOC) hp (pairUp ns tgt) e ∧
        c'.nreg 160063 = e ((pairUp ns tgt).length - 1) ∧
        (∀ q, q < (pairUp ns tgt).length → A0 ≤ e q) := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨hwc, c62, c65, c64, cA0, -, cm, -, -, cr, -, -, -, ee, hee, hprev⟩ := hst
  set j := ns.length with hjdef
  set np := j / 2 with hnp
  have hlen' : (pairUp ns tgt).length = (j + 1) / 2 := pairUp_length ns tgt
  have c14 : c.nreg 160014 = j := by
    rw [cr _ (bandOK_l41 (by omega) (by omega)) (not_pairRG (by omega)) (by rwo [hAl])]
    exact h14
  have c24 : c.nreg 160024 = 1 := by
    rw [cr _ (bandOK_l41 (by omega) (by omega)) (not_pairRG (by omega)) (by rwo [hAl])]
    exact h24
  have c83 : c.nreg 160083 = 3 := by
    rw [cr _ (bandOK_l41 (by omega) (by omega)) (not_pairRG (by omega)) (by rwo [hAl])]
    exact h83
  -- the merged nodes as cells
  have merged : ∀ (m : ℕ → ℕ) (A : ℕ), c.nreg ALLOC ≤ A →
      (∀ a, a < c.nreg ALLOC → m a = c.nmem a) → ∀ q, q < np →
      ee q + 3 ≤ A ∧ (1 ≤ q → m (ee q + 2) = ee (q - 1)) ∧
      ∃ C : Chain, C.s = (nd (pairUp ns tgt) q).1 ∧ C.m = (nd (pairUp ns tgt) q).2.1 ∧
        NodeOK P m A hp (m (ee q)) (m (ee q + 1)) C (nd (pairUp ns tgt) q).2.2 := by
    intro m A hA he q hq
    obtain ⟨a1, a2, a3, C, b1, b2, b3⟩ := hee q hq
    rw [nd_pairUp_merge ns tgt q hq]
    refine ⟨by omega, fun h => by rw [he _ (by omega)]; exact a3 h, C, b1, b2, ?_⟩
    rw [he _ (by omega), he _ (by omega)]
    exact (b3.agree he).mono hA
  by_cases hodd : 2 * np < j
  · -- the carry
    have hj1 : j - 1 = 2 * np := by omega
    obtain ⟨C, s1, m1, n1⟩ := hL (j - 1) (by omega)
    obtain ⟨c', k, e, hk, hw', w0, w1, w2, hm', hA', q63, q64, fr', hrr', hrm', ho'⟩ :=
      carryB_exec (P := P) hwc rfl c65 rfl c64 c24 c83 hW (by omega) (by omega)
    have hptr : B + 4 * np = B + 2 * (j - 1) := by omega
    refine ⟨c', k + 1, .ifLtN_true (by rwx [c62, c14]) e, by omega, hw',
      by omega, by omega, by omega, fun a ha => hm' a (Or.inl ha), hrm', ho', hrr',
      fun r h1 h2 => fr' r (by ufo PairRG at h1) (by ufo PairRG at h1)
        (by ufo PairRG at h1) (by ufo PairRG at h1)
        (by ufo PairRG at h1) (by ufo PairRG at h1) h2,
      by rwo [q64, hlen'], fun q => if q = np then c.nreg ALLOC else ee q,
      fun q hq => ?_, ?_, fun q hq => ?_⟩
    · rw [hlen'] at hq
      rcases Nat.lt_or_ge q np with hq1 | hq1
      · simp only [show q ≠ np by omega, ite_false]
        obtain ⟨a1, a2, C', b1, b2, b3⟩ := merged c'.nmem (c'.nreg ALLOC) (by omega)
          (fun a ha => hm' a (Or.inl ha)) q hq1
        exact ⟨a1, fun h => by rw [a2 h]; simp [show q - 1 ≠ np by omega], C', b1, b2, b3⟩
      · have hq2 : q = np := by omega
        subst hq2
        simp only [ite_true]
        have hcarry := nd_pairUp_carry ns tgt (by omega)
        rw [← hnp] at hcarry
        refine ⟨by omega, fun h => ?_, C, ?_, ?_, ?_⟩
        · simp only [show np - 1 ≠ np by omega, ite_false]
          rw [w2, hprev (by omega)]
        · rw [hcarry, s1]
        · rw [hcarry, m1]
        · rw [hcarry, w0, w1, hA', hptr, cm _ (by omega), cm _ (by omega)]
          have n1c := (n1.agree cm).mono cA0
          exact (n1c.agree fun a ha => hm' a (Or.inl ha)).mono (by omega)
    · rw [q63, hlen']; simp [show (j + 1) / 2 - 1 = np by omega]
    · rw [hlen'] at hq
      rcases Nat.lt_or_ge q np with hq1 | hq1
      · simp only [show q ≠ np by omega, ite_false]; exact (hee q hq1).1
      · simp only [show q = np by omega, ite_true]; exact cA0
  · -- nothing to carry
    have heven : 2 * np = j := by omega
    refine ⟨c, 2, .ifLtN_false (by rwx [c62, c14]) (.skip hwc), by omega, hwc,
      le_rfl, by omega, by omega, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ _ => rfl,
      by rwo [c64, hlen'], ee, fun q hq => ?_, ?_, fun q hq => ?_⟩
    · rw [hlen'] at hq
      exact merged c.nmem (c.nreg ALLOC) le_rfl (fun _ _ => rfl) q (by omega)
    · rw [hprev (by omega), hlen']; congr 1; omega
    · rw [hlen'] at hq; exact (hee q (by omega)).1

end proofs

end

end Chazelle.Core.L41
