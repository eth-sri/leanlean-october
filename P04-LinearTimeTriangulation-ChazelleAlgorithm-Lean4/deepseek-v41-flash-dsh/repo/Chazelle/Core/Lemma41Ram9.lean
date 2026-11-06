module

public import Chazelle.Golf

public import Chazelle.Core.Lemma41Ram8

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
  | [], _ => ⊚ pairUp
  | [_], _ => ⊚ pairUp
  | a :: b :: rest, t => by
    simp only [pairUp, List.length_cons, pairUp_length rest t]; omega

theorem nd_cons_succ (a : Shp) (l : List Shp) (k : ℕ) : nd (a :: l) (k + 1) = nd l k := by
  Θ nd

theorem nd_cons_zero (a : Shp) (l : List Shp) : nd (a :: l) 0 = a := ⊚ nd

theorem nd_pairUp_merge : ∀ (l : List Shp) (t q : ℕ), q < l.length / 2 →
    nd (pairUp l t) q = ((nd l (2 * q)).1, (nd l (2 * q)).2.1 + (nd l (2 * q + 1)).2.1, t)
  | [], _, q, h => by simp at h
  | [_], _, q, h => by simp at h
  | a :: b :: rest, t, 0, _ => by
    ϴ pairUp, Nat.mul_zero, Nat.zero_add, nd_cons_zero, nd_cons_succ
  | a :: b :: rest, t, q + 1, h => by
    have ih := nd_pairUp_merge rest t q (by simp only [List.length_cons] at h; omega)
    have e1 : nd (a :: b :: rest) (2 * (q + 1)) = nd rest (2 * q) := by
      Ξ show 2 * (q + 1) = 2 * q + 1 + 1 by ring, nd_cons_succ, nd_cons_succ
    have e2 : nd (a :: b :: rest) (2 * (q + 1) + 1) = nd rest (2 * q + 1) := by
      Ξ show 2 * (q + 1) + 1 = 2 * q + 1 + 1 + 1 by ring, nd_cons_succ, nd_cons_succ
    Ξ e1, e2
    ϴ pairUp
    Ξ nd_cons_succ
    exact ih

theorem nd_pairUp_carry : ∀ (l : List Shp) (t : ℕ), l.length % 2 = 1 →
    nd (pairUp l t) (l.length / 2) = nd l (l.length - 1)
  | [], _, h => by simp at h
  | [_], _, _ => ⊚ pairUp
  | a :: b :: rest, t, h => by
    ϴ' List.length_cons at h ⊢
    have ih := nd_pairUp_carry rest t (⋄)
    have h1 : 1 ≤ rest.length := ⋄
    ϴ pairUp
    rw [show (rest.length + 1 + 1) / 2 = rest.length / 2 + 1 by omega, nd_cons_succ,
      show rest.length + 1 + 1 - 1 = rest.length - 1 + 1 + 1 by omega, nd_cons_succ,
      nd_cons_succ]
    exact ih

theorem nd_pairUp_zero (l : List Shp) (t : ℕ) (h : 1 ≤ l.length) :
    (nd (pairUp l t) 0).1 = (nd l 0).1 := by
  rcases Nat.lt_or_ge 1 l.length with h2 | h2
  · Ξ nd_pairUp_merge l t 0 (⋄)
  · have : l.length = 1 := ⋄
    have := nd_pairUp_carry l t (⋄)
    Ξ' show l.length / 2 = 0 by omega, show l.length - 1 = 0 by omega at this
    Ξ this

/-- **The next level is consecutive.** -/
theorem consec_pairUp {l : List Shp} (t : ℕ) (h : Consec l) : Consec (pairUp l t) := by
  intro q hq
  Ξ' pairUp_length at hq
  have hq0 : q < l.length / 2 := ⋄
  Ξ nd_pairUp_merge l t q hq0
  have e1 : (nd (pairUp l t) (q + 1)).1 = (nd l (2 * q + 2)).1 := by
    rcases Nat.lt_or_ge (q + 1) (l.length / 2) with h1 | h1
    · rw [nd_pairUp_merge l t (q + 1) h1]; rfl
    · have hodd : l.length % 2 = 1 := ⋄
      have := nd_pairUp_carry l t hodd
      Ξ' show l.length / 2 = q + 1 by omega, show l.length - 1 = 2 * q + 2 by omega at this
      Ξ this
  Ξ e1, h (2 * q + 1) (⋄), h (2 * q) (⋄)
  simp only; ring

theorem pairUp_sum : ∀ (l : List Shp) (t : ℕ),
    ((pairUp l t).map fun x => x.2.1).sum = (l.map fun x => x.2.1).sum
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, t => by
    simp only [pairUp, List.map_cons, List.sum_cons, pairUp_sum rest t]; ring

/-- The granularities of the next level are at most the target. -/
theorem pairUp_gran {l : List Shp} {t γ₀ : ℕ} (hγ : ∀ k, k < l.length → (nd l k).2.2 ≤ γ₀)
    (ht : γ₀ ≤ t) : ∀ k, k < (pairUp l t).length → (nd (pairUp l t) k).2.2 ≤ t := by
  intro k hk
  Ξ' pairUp_length at hk
  rcases Nat.lt_or_ge k (l.length / 2) with h1 | h1
  · Ξ nd_pairUp_merge l t k h1
  · have hodd : l.length % 2 = 1 := ⋄
    have := nd_pairUp_carry l t hodd
    Ξ show k = l.length / 2 by omega, this
    exact (hγ _ (⋄)).trans ht

theorem pairUp_gran_pos {l : List Shp} {t : ℕ} (hγ : ∀ k, k < l.length → 1 ≤ (nd l k).2.2)
    (ht : 1 ≤ t) : ∀ k, k < (pairUp l t).length → 1 ≤ (nd (pairUp l t) k).2.2 := by
  intro k hk
  Ξ' pairUp_length at hk
  rcases Nat.lt_or_ge k (l.length / 2) with h1 | h1
  · rw [nd_pairUp_merge l t k h1]; exact ht
  · have hodd : l.length % 2 = 1 := ⋄
    have := nd_pairUp_carry l t hodd
    Ξ show k = l.length / 2 by omega, this
    exact hγ _ (⋄)

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
  Ξ' hAl at hA ⊢
  unfold carryB
  exec_block
  all_goals try (config_simp; (try simp only [hA, h65, h64, h24, h83]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, fun a ha => ?_, ?_, ?_, ?_,
    fun r a1 a2 a3 a4 a5 a6 a7 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [hA, h65, h24, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [hA, h65, h24, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [hA, h63, h24, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [hA, h24, Machine.upd_apply]; split_ifs <;> first | omega
  · config_simp; ϴ hA, h83
  · config_simp; ϴ hA
  · config_simp; ϴ h64, h24
  · simp only
    repeat (rw [Machine.upd_other _ _ _ (⋄)])


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
    Ξ cr _ (bandOK_l41 (⋄) (⋄)) (not_pairRG (⋄)) (by rw [hAl]; omega)
    exact h14
  have c24 : c.nreg 160024 = 1 := by
    Ξ cr _ (bandOK_l41 (⋄) (⋄)) (not_pairRG (⋄)) (by rw [hAl]; omega)
    exact h24
  have c83 : c.nreg 160083 = 3 := by
    Ξ cr _ (bandOK_l41 (⋄) (⋄)) (not_pairRG (⋄)) (by rw [hAl]; omega)
    exact h83
  -- the merged nodes as cells
  have merged : ∀ (m : ℕ → ℕ) (A : ℕ), c.nreg ALLOC ≤ A →
      (∀ a, a < c.nreg ALLOC → m a = c.nmem a) → ∀ q, q < np →
      ee q + 3 ≤ A ∧ (1 ≤ q → m (ee q + 2) = ee (q - 1)) ∧
      ∃ C : Chain, C.s = (nd (pairUp ns tgt) q).1 ∧ C.m = (nd (pairUp ns tgt) q).2.1 ∧
        NodeOK P m A hp (m (ee q)) (m (ee q + 1)) C (nd (pairUp ns tgt) q).2.2 := by
    intro m A hA he q hq
    obtain ⟨a1, a2, a3, C, b1, b2, b3⟩ := hee q hq
    Ξ nd_pairUp_merge ns tgt q hq
    refine ⟨⋄, fun h => by rw [he _ (⋄)]; exact a3 h, C, b1, b2, ?_⟩
    Ξ he _ (⋄), he _ (⋄)
    exact (b3.agree he).mono hA
  by_cases hodd : 2 * np < j
  · -- the carry
    have hj1 : j - 1 = 2 * np := ⋄
    obtain ⟨C, s1, m1, n1⟩ := hL (j - 1) (⋄)
    obtain ⟨c', k, e, hk, hw', w0, w1, w2, hm', hA', q63, q64, fr', hrr', hrm', ho'⟩ :=
      carryB_exec (P := P) hwc rfl c65 rfl c64 c24 c83 hW (⋄) (⋄)
    have hptr : B + 4 * np = B + 2 * (j - 1) := ⋄
    refine ⟨c', k + 1, .ifLtN_true (by rw [c62, c14]; exact hodd) e, ⋄, hw',
      ⋄, ⋄, ⋄, fun a ha => hm' a (Or.inl ha), hrm', ho', hrr',
      fun r h1 h2 => fr' r (by unfold PairRG at h1; omega) (by unfold PairRG at h1; omega)
        (by unfold PairRG at h1; omega) (by unfold PairRG at h1; omega)
        (by unfold PairRG at h1; omega) (by unfold PairRG at h1; omega) h2,
      by rw [q64, hlen']; omega, fun q => if q = np then c.nreg ALLOC else ee q,
      fun q hq => ?_, ?_, fun q hq => ?_⟩
    · Ξ' hlen' at hq
      rcases Nat.lt_or_ge q np with hq1 | hq1
      · ϴ show q ≠ np by omega, ite_false
        obtain ⟨a1, a2, C', b1, b2, b3⟩ := merged c'.nmem (c'.nreg ALLOC) (⋄)
          (fun a ha => hm' a (Or.inl ha)) q hq1
        exact ⟨a1, fun h => by rw [a2 h]; simp [show q - 1 ≠ np by omega], C', b1, b2, b3⟩
      · have hq2 : q = np := ⋄
        subst hq2
        ϴ ite_true
        have hcarry := nd_pairUp_carry ns tgt (⋄)
        Ξ' ← hnp at hcarry
        refine ⟨⋄, fun h => ?_, C, ?_, ?_, ?_⟩
        · ϴ show np - 1 ≠ np by omega, ite_false
          Ξ w2, hprev (⋄)
        · Ξ hcarry, s1
        · Ξ hcarry, m1
        · Ξ hcarry, w0, w1, hA', hptr, cm _ (⋄), cm _ (⋄)
          have n1c := (n1.agree cm).mono cA0
          exact (n1c.agree fun a ha => hm' a (Or.inl ha)).mono (⋄)
    · rw [q63, hlen']; Θ show (j + 1) / 2 - 1 = np by omega
    · Ξ' hlen' at hq
      rcases Nat.lt_or_ge q np with hq1 | hq1
      · simp only [show q ≠ np by omega, ite_false]; exact (hee q hq1).1
      · simp only [show q = np by omega, ite_true]; exact cA0
  · -- nothing to carry
    have heven : 2 * np = j := ⋄
    refine ⟨c, 2, .ifLtN_false (by rw [c62, c14]; exact hodd) (.skip hwc), ⋄, hwc,
      le_rfl, ⋄, ⋄, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ _ => rfl,
      by rw [c64, hlen']; omega, ee, fun q hq => ?_, ?_, fun q hq => ?_⟩
    · Ξ' hlen' at hq
      exact merged c.nmem (c.nreg ALLOC) le_rfl (fun _ _ => rfl) q (⋄)
    · rw [hprev (⋄), hlen']; congr 1; omega
    · Ξ' hlen' at hq; exact (hee q (⋄)).1

end proofs

end

end Chazelle.Core.L41
