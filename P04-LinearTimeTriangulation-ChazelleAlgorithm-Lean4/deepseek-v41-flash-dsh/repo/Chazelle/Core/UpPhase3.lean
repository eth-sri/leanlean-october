module

public import Chazelle.Golf

public import Chazelle.Core.UpPhase2

/-!
# WP-J up phase, part 3: the descriptor of a merged chain

`unionS`: reserve five words at the allocator and write there the descriptor of the union of the
two consecutive chains described at `160035` and `160036` (Lemma 4.1's `descS`) (`unionS_exec`).
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41 SweepPrim SignK WalkKey

@[expose] public section

/-- Reserve the descriptor. -/
def unionB : Stmt := block [.copyN 160037 9999, .addN 9999 9999 170023, .constN 160024 1]

/-- **The descriptor of the union of two consecutive chains.** -/
def unionS : Stmt := .seq unionB descS

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
theorem unionB_exec {c : Config} (hw : WordsBounded W c) {TD : ℕ} (hA : c.nreg ALLOC = TD)
    (h23 : c.nreg 170023 = 5) (hW : TD + 5 ≤ W) :
    ∃ c' k, Exec P W unionB c c' k ∧ k = 3 ∧ WordsBounded W c' ∧
      c'.nreg 160037 = TD ∧ c'.nreg ALLOC = TD + 5 ∧ c'.nreg 160024 = 1 ∧
      (∀ r, r ≠ 160037 → r ≠ 160024 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold unionB
  exec_block
  all_goals try (config_simp; (try simp only [hA, h23]); omega)
  refine ⟨rfl, ‹_›, by config_simp; simp only [hA], by config_simp; simp only [hA, h23],
    by config_simp, fun r a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩
  simp only
  repeat (rw [Machine.upd_other _ _ _ (⋄)])

set_option maxHeartbeats 16000000 in
/-- **The descriptor of the union on the RAM** (whole host). -/
theorem unionS_exec (hG : GoodEnv P) (hWn : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {pl pr TD hp : ℕ} {C₁ C₂ : Chain} (hA : c.nreg ALLOC = TD)
    (h35 : c.nreg 160035 = pl) (h36 : c.nreg 160036 = pr) (h23 : c.nreg 170023 = 5)
    (hd1 : ChainDescAt c.nmem pl (Qof P) (Host.whole P.n) C₁)
    (hd2 : ChainDescAt c.nmem pr (Qof P) (Host.whole P.n) C₂)
    (hh1 : c.nmem pl = hp) (hh2 : c.nmem pr = hp) (hhp : hp + 7 ≤ TD)
    (hP1 : C₁.P = Qof P) (hP2 : C₂.P = Qof P) (hs : C₂.s = C₁.s + C₁.m)
    (hn : C₁.s + C₁.m + C₂.m + 1 ≤ P.n) (hlo : pl + 5 ≤ TD) (hlo' : pr + 5 ≤ TD)
    (hW : TD + 5 ≤ W) :
    ∃ c' k, Exec P W unionS c c' k ∧ k ≤ 303 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = TD + 5 ∧ c'.nreg 160037 = TD ∧ c'.nmem TD = hp ∧
      (∀ C : Chain, C.P = Qof P → C.s = C₁.s → C.m = C₁.m + C₂.m →
        ChainDescAt c'.nmem TD (Qof P) (Host.whole P.n) C) ∧
      (∀ a, (a < TD ∨ TD + 5 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ DescRG r → Bk r = false → r ≠ 160037 → r ≠ 160024 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ r, Bk r = false → r ≠ 160049 → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨c1, k1, e1, hk1, hw1, u37, uA, u24, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    unionB_exec (P := P) hw hA h23 hW
  have hd1' : ChainDescAt c1.nmem pl (Qof P) (Host.whole P.n) C₁ := by rw [hm1]; exact hd1
  have hd2' : ChainDescAt c1.nmem pr (Qof P) (Host.whole P.n) C₂ := by rw [hm1]; exact hd2
  obtain ⟨c2, k2, e2, hk2, hw2, -, t0, t1, t2, t3, t4, hm2, fr2, frr2, hrm2, ho2⟩ :=
    descS_exec hG hWn hw1 (by rw [fr1 _ (by decide) (by decide) (by decide)]; exact h35)
      (by rw [fr1 _ (by decide) (by decide) (by decide)]; exact h36) u37 u24 hd1' hd2' hP1 hP2 hs
      hn hlo hlo' hW
  have hlen : C₁.m + C₂.m + 1 ≤ C₁.P.n := by
    rw [hP1, show (Qof P).n = P.n from shear_n _ _]; omega
  have mem2 : ∀ a, a < TD → c2.nmem a = c1.nmem a := fun a ha => hm2 a (Or.inl ha)
  have g1 := chainDescAt_agree hd1' hlo (by rw [hm1]; exact hh1) hhp mem2
  have g2 := chainDescAt_agree hd2' hlo' (by rw [hm1]; exact hh2) hhp mem2
  have hTD : ChainDescAt c2.nmem TD (Qof P) (Host.whole P.n) (jOf C₁ C₂ hlen).whole := by
    refine descWhole hlen (by rw [hP2, hP1]) hs g1 g2 ?_ t1 t2 t3 ?_
    · rw [t0, mem2 _ (by omega)]
    · rw [t4, mem2 _ (by omega), mem2 _ (by omega)]
  refine ⟨c2, k1 + k2, .seq e1 e2, by omega, hw2,
    by rw [fr2 _ (by rw [hAl]; unfold DescRG; omega) (by simp [Bk, hAl])]; exact uA,
    by rw [fr2 _ (by unfold DescRG; omega) (by simp [Bk])]; exact u37,
    by rw [t0, hm1]; exact hh1, fun C hCP hCs hCm => ?_,
    fun a ha => by rw [hm2 a ha, hm1], fun r h1 h2 h3 h4 h5 => by
      rw [fr2 r h1 h2]; exact fr1 r h3 h4 h5,
    fun r h1 h2 => by rw [frr2 r h1 h2, hrr1], by rw [hrm2, hrm1], by rw [ho2, ho1]⟩
  have hC : C = (jOf C₁ C₂ hlen).whole :=
    chain_eq (by rw [hCP, jOf_whole_P, hP1]) (by rw [hCs, jOf_whole_s])
      (by rw [hCm, jOf_whole_m])
  rw [hC]; exact hTD

end proofs

end

end Chazelle.Core.Up
