module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoLoopM

/-!
# The sweep RAM (WP-D), answers: the query loop (piece H)

`loopS qry sh`: allocate the `4 L` result words at `sw 11` (the allocator of `c₀`; `allocB`, four
words per step of four instructions), then for `j < L.length` (registers `pJ = j`,
`pA = sw 8 + 3 j`, `pR = sw 11 + 4 j`) the per-query procedure `qry sh` (`QrySpec`) and the step
(`incB`).

**`loopSpec_of : QrySpec Aux → TopCountSpec → LoopSpec Aux`**: the result list at `sw 11`, cost
`loopCost (5 κq + 21)` (at most five brute-force queries, `qCost_sum`).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep

@[expose] public section

/-! ## The program -/

/-- Allocate four words (four instructions). -/
def allocB : Stmt :=
  block [.addN ALLOC ALLOC K4, .addN pJ pJ K1, .constN (sw 5003) 0, .constN (sw 5004) 0]

/-- The step of the query loop. -/
def incB : Stmt := block [.addN pJ pJ K1, .addN pA pA K3, .addN pR pR K4]

/-- **The query loop.** -/
def loopS (qry : Stmt → Stmt) (sh : Stmt) : Stmt :=
  .seq (block [.constN pJ 0]) (.seq (.whileLtN pJ (sw 9) allocB)
    (.seq (block [.constN pJ 0, .copyN pA (sw 8), .copyN pR (sw 11)])
      (.whileLtN pJ (sw 9) (.seq (qry sh) incB))))

/-! ## Lemmas -/

section
variable {α : Type} {R : List α} {r d : α}
include α
theorem getD_snoc_lt {k : ℕ} (hk : k < R.length) :
    (R ++ [r]).getD k d = R.getD k d := by
  grind

theorem getD_snoc_eq : (R ++ [r]).getD R.length d = r := by
  simp_all


end

theorem loop_cost_le {n A₁ Fg T κ S : ℕ}
    (hS : S ≤ n * (κ * (Fg + T + 1)) + 5 * (κ * (A₁ + 1) * (Fg + 1)) + 5 * n) :
    1 + (6 * n + 2 + (3 + (S + 2))) ≤
      (5 * κ + 21) * (n + 1) * (Fg + T + 1) + (5 * κ + 21) * (A₁ + 1) * (Fg + 1) := by
  grind

section exec

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

section
variable (hI : IInv W c₀ c) (hK : Consts c)
include hI hK
theorem allocB_irs (hroom : c.nreg ALLOC + 4 ≤ W)
    (hj : c.nreg pJ + 1 ≤ W) :
    IRS P W c₀ allocB c 4 (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 4 ∧
      c'.nreg pJ = c.nreg pJ + 1 ∧
      (∀ r, r ≠ ALLOC → r ≠ pJ → r ≠ sw 5003 → r ≠ sw 5004 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem) := by
  have k1 : c.nreg 240611 = 1 := hK.2.1
  have k4 : c.nreg 240613 = 4 := hK.2.2.2.1
  have hw := hI.hw
  have hroom' : c.nreg 9999 + 4 ≤ W := hroom
  have hj' : c.nreg 245000 + 1 ≤ W := hj
  have ex : ∃ c' k, Exec P W (block [.addN 9999 9999 240613, .addN 245000 245000 240611,
      .constN 245003 0, .constN 245004 0]) c c' k ∧ k = 4 ∧ c'.nreg 9999 = c.nreg 9999 + 4 ∧
      c'.nreg 245000 = c.nreg 245000 + 1 ∧
      (∀ r, r ≠ 9999 → r ≠ 245000 → r ≠ 245003 → r ≠ 245004 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals (grind [upd])
  obtain ⟨c', k, ex, hk, h1, h2, h3, h4, h5, h6, h7⟩ := ex
  refine IRS.ofExec hI ex (by omega) (fun r hr hra => h3 r hra ?_ ?_ ?_) h5
    (fun a _ => by rw [h4]) h6 h7 (by omega_nf)
    (by omega_nf) ⟨h1, h2, fun r a b d e => h3 r a b d e, h4⟩
  · intro h; subst h; exact hr (iscr_sw (by norm_num) (by norm_num))
  · intro h; subst h; exact hr (iscr_sw (by norm_num) (by norm_num))
  · intro h; subst h; exact hr (iscr_sw (by norm_num) (by norm_num))

theorem incB_irs (h1 : c.nreg pJ + 1 ≤ W)
    (h2 : c.nreg pA + 3 ≤ W) (h3 : c.nreg pR + 4 ≤ W) :
    IRS P W c₀ incB c 3 (fun c' => c'.nreg pJ = c.nreg pJ + 1 ∧ c'.nreg pA = c.nreg pA + 3 ∧
      c'.nreg pR = c.nreg pR + 4 ∧
      (∀ r, r ≠ pJ → r ≠ pA → r ≠ pR → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  have k1 : c.nreg 240611 = 1 := hK.2.1
  have k3 : c.nreg 240616 = 3 := hK.2.2.2.2.2.2
  have k4 : c.nreg 240613 = 4 := hK.2.2.2.1
  have hw := hI.hw
  have h1' : c.nreg 245000 + 1 ≤ W := h1
  have h2' : c.nreg 245001 + 3 ≤ W := h2
  have h3' : c.nreg 245002 + 4 ≤ W := h3
  have ex : ∃ c' k, Exec P W (block [.addN 245000 245000 240611, .addN 245001 245001 240616,
      .addN 245002 245002 240613]) c c' k ∧ k = 3 ∧ c'.nreg 245000 = c.nreg 245000 + 1 ∧
      c'.nreg 245001 = c.nreg 245001 + 3 ∧ c'.nreg 245002 = c.nreg 245002 + 4 ∧
      (∀ r, r ≠ 245000 → r ≠ 245001 → r ≠ 245002 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals (grind [upd])
  obtain ⟨c', k, ex, hk, e1, e2, e3, e4, e5, e6, e7, e8⟩ := ex
  refine IRS.ofExec hI ex (by omega) (fun r hr hra => e4 r ?_ ?_ ?_) e6
    (fun a _ => by rw [e5]) e7 e8 (by grind)
    (by ram_grind)
    ⟨e1, e2, e3, fun r a b d => e4 r a b d, e5⟩
  · intro h; subst h; exact hr (iscr_sw (by norm_num) (by norm_num))
  · intro h; subst h; exact hr (iscr_sw (by norm_num) (by norm_num))
  · intro h; subst h; exact hr (iscr_sw (by norm_num) (by norm_num))


end

end exec

/-! ## The loop -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 40000 in
open Classical in
/-- **The query loop** from the per-query procedure (piece H). -/
theorem loopSpec_of {Aux : Polygon → Merge.Junction → NF → Config → Prop} (hq : QrySpec Aux)
    (hT : TopCountSpec) : LoopSpec Aux := by
  obtain ⟨qry, κq, hqry⟩ := hq
  refine ⟨loopS qry, fun D => 5 * κq D + 21, ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ J H N₁ N₂ E L i hB hroom
  have hI₀ : IInv W c₀ c₀ := ⟨hB.hw, fun _ _ => rfl, le_rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  set n := L.length with hn
  set f : ℕ → ℕ := fun j => qCost κq F c₀ J P N₁ N₂ L i j with hf
  have hsum := qCost_sum (κ := κq) (F := F) (c₀ := c₀) (N₁ := N₁) hT hB.hA.hG hB.hA.hP
    hB.hA.hNF₂ hB.hend (i := i)
  have hS : ∑ j ∈ Finset.range n, (f j + 5) ≤
      n * (κq (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1)) +
        5 * (κq (c₀.nreg (sw 6)) * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1)) + 5 * n := by
    have hsum' : ∑ j ∈ Finset.range n, f j ≤
        n * (κq (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1)) +
          5 * (κq (c₀.nreg (sw 6)) * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1)) := hsum
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  have hcost := loop_cost_le hS
  unfold loopCost at hroom ⊢
  beta_reduce at hroom ⊢
  rw [← hn] at hroom ⊢
  have hK₀ := hB.hA.hK
  have hn9 : c₀.nreg (sw 9) = n := hB.hLn
  have hnW : n ≤ W := by omega
  have hAW : c₀.nreg ALLOC ≤ W := hB.hw.1 _
  have hLm := hB.hLm
  have h11 := hB.hres
  -- the cost of the whole loop
  refine (IRS.seq (K₁ := 1) (K₂ := 6 * n + 2 + (3 + (∑ j ∈ Finset.range n, (f j + 5) + 2)))
    ((IRS.block [.constN pJ 0] hI₀ ⟨⟨iscr_sw (by omega_nf) (by omega_nf),
      Nat.zero_le _⟩, trivial⟩).mono le_rfl (fun _ h => h)) ?_).mono hcost (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' hc₁
  have j1 : c₁.nreg pJ = 0 := by rw [hc₁]; simp [regB, regI]
  -- 1. the allocation
  let Ia : Config → Prop := fun c => c.nreg pJ ≤ n ∧ c.nreg ALLOC = c₀.nreg ALLOC + 4 * c.nreg pJ
  have hA1e : c₁.nreg ALLOC = c₀.nreg ALLOC := by
    rw [hc₁]; simp only [regB, regI]
    omega_nf
  refine IRS.seq (K₁ := 6 * n + 2) (K₂ := 3 + (∑ j ∈ Finset.range n, (f j + 5) + 2))
    ((IRS.whileP (a := pJ) (b := sw 9) (body := allocB) Ia (fun c => 6 * (n - c.nreg pJ))
      (fun c hI hc hlt hrm => ⟨4, (allocB_irs hI (hK₀.fix hI)
        (by omega)
        (by omega)).mono le_rfl
        (fun c' h => by
          obtain ⟨a1, a2, -, -⟩ := h
          rw [hI.hin (sw 9) (by omega_nf), hn9] at hlt
          omega)⟩)
      hI₁ ⟨by omega, by omega⟩ (by omega)).mono (by omega)
      (fun _ h => h))
    ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨⟨ja, ha⟩, hex⟩
  rw [hI₂.hin (sw 9) (by omega_nf), hn9] at hex
  
  
  -- 2. the loop registers
  
  refine IRS.seq (K₁ := 3) (K₂ := ∑ j ∈ Finset.range n, (f j + 5) + 2)
    ((IRS.block [.constN pJ 0, .copyN pA (sw 8), .copyN pR (sw 11)] hI₂
      ⟨⟨iscr_sw (by omega_nf) (by omega_nf), Nat.zero_le _⟩,
        iscr_sw (by omega_nf) (by omega_nf),
        iscr_sw (by omega_nf) (by omega_nf), trivial⟩).mono le_rfl
      (fun _ h => h)) ?_
  rintro c₃ hI₃ hA₃ hA₃' hc₃
  have v3 : c₃.nreg pJ = 0 ∧ c₃.nreg pA = c₀.nreg (sw 8) ∧ c₃.nreg pR = c₀.nreg (sw 11) ∧
      c₃.nreg ALLOC = c₂.nreg ALLOC ∧ c₃.nmem = c₂.nmem := by
    rw [hc₃]
    simp only [regB, regI, upd, pJ, pA, pR, sw,
      ALLOC]
    refine ⟨by simp, by simp; exact hI₂.hin (sw 8) (by omega_nf),
      by simp; exact hI₂.hin (sw 11) (by omega_nf), by simp, trivial⟩
  obtain ⟨j3, p3, r3, a3, m3⟩ := v3
  -- 3. the queries
  let Iq : Config → Prop := fun c => ∃ j, c.nreg pJ = j ∧ j ≤ n ∧ c.nreg (sw 9) = n ∧
    c.nreg pA = c₀.nreg (sw 8) + 3 * j ∧ c.nreg pR = c₀.nreg (sw 11) + 4 * j ∧
    c₀.nreg (sw 11) + 4 * n ≤ c.nreg ALLOC ∧
    ∃ R : List (ℕ × ℕ × ℕ × ℕ), R.length = j ∧ ResultListAt c.nmem (c₀.nreg (sw 11)) R ∧
      ∀ j', j' < j → SeesInWhole J (Qof P) i (L.getD j' (0, 0, 0)) (R.getD j' (0, 0, 0, 0))
  have hIq₃ : Iq c₃ := ⟨0, j3, Nat.zero_le _, by rw [hI₃.hin (sw 9) (by omega_nf), hn9],
    by omega, by omega,
    by omega, [], rfl, fun k hk => by simp at hk, fun k hk => by omega⟩
  have hΦ₃ : ∑ k ∈ Finset.Ico (c₃.nreg pJ) n, (f k + 5) = ∑ j ∈ Finset.range n, (f j + 5) := by
    rw [j3, Finset.range_eq_Ico]
  refine (IRS.whileP (a := pJ) (b := sw 9) (body := .seq (qry sh) incB) Iq
    (fun c => ∑ k ∈ Finset.Ico (c.nreg pJ) n, (f k + 5)) ?_ hI₃ hIq₃
    (by omega)).mono (by rw [hΦ₃]) ?_
  · -- one query
    rintro c hI ⟨j, hj, hjn, h9, hpA, hpR, hAl, R, hRl, hRat, hRs⟩ hlt hrm
    rw [h9, hj] at hlt
    have hsplit : ∑ k ∈ Finset.Ico (c.nreg pJ) n, (f k + 5) =
        (f j + 5) + ∑ k ∈ Finset.Ico (j + 1) n, (f k + 5) := by
      rw [hj, Finset.sum_eq_sum_Ico_succ_bot hlt]
    have hrq : c.nreg ALLOC + qCost κq F c₀ J P N₁ N₂ L i j ≤ W := by
      rw [hsplit] at hrm
      have : f j = qCost κq F c₀ J P N₁ N₂ L i j := rfl
      omega
    refine ⟨f j + 3, (IRS.seq (K₁ := f j) (K₂ := 3) (hqry sh Bs F X Ok hsh hBs hXl P W c₀ c J H
      N₁ N₂ E L i j hB hI hj hlt hpA hpR (by omega) hrq) ?_).mono le_rfl
      (fun _ h => h)⟩
    rintro c' hI' hA' hA'' ⟨⟨r, q0, q1, q2, q3, hsee⟩, hmem, hreg, hAm⟩
    have kreg : ∀ r, sw 5000 ≤ r → r < sw 6000 → c'.nreg r = c.nreg r := hreg
    have cJ : c'.nreg pJ = j := (kreg pJ (by omega_nf) (by omega_nf)).trans hj
    have cA : c'.nreg pA = c₀.nreg (sw 8) + 3 * j :=
      (kreg pA (by omega_nf) (by omega_nf)).trans hpA
    have cR : c'.nreg pR = c₀.nreg (sw 11) + 4 * j :=
      (kreg pR (by omega_nf) (by omega_nf)).trans hpR
    
    refine (incB_irs hI' (hK₀.fix hI') (by omega) (by rw [cA]; omega)
      (by rw [cR]; omega)).mono le_rfl ?_
    rintro c'' ⟨e1, e2, e3, e4, e5⟩
    have hAc : c''.nreg ALLOC = c'.nreg ALLOC :=
      e4 _ (by omega_nf) (by omega_nf)
        (by omega_nf)
    have c9 : c''.nreg (sw 9) = n := by
      rw [e4 _ (by omega_nf) (by omega_nf) (by omega_nf),
        hI'.hin (sw 9) (by omega_nf), hn9]
    refine ⟨⟨j + 1, by rw [e1, cJ], by omega, c9, by omega, by rw [e3, cR]; ring,
      by rw [hAc]; omega, R ++ [r], by simp [hRl], fun k hk => ?_, fun k hk => ?_⟩, ?_⟩
    · rw [e5]
      simp only [List.length_append, List.length_singleton] at hk
      rcases (show k < R.length ∨ k = R.length by omega) with hk' | hk'
      · rw [getD_snoc_lt hk']
        obtain ⟨b0, b1, b2, b3⟩ := hRat k hk'
        have hb : c₀.nreg (sw 11) + 4 * k + 3 < c.nreg pR := by omega
        have hb' : c₀.nreg (sw 11) + 4 * k + 3 < c.nreg ALLOC := by omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hmem _ (by omega) (Or.inl (by omega))]; exact b0
        · rw [hmem _ (by omega) (Or.inl (by omega))]; exact b1
        · rw [hmem _ (by omega) (Or.inl (by omega))]; exact b2
        · rw [hmem _ (by omega) (Or.inl (by omega))]; exact b3
      · subst hk'
        rw [getD_snoc_eq]
        have hpos : c₀.nreg (sw 11) + 4 * R.length = c.nreg pR := by omega
        rw [hpos]
        omega
    · rcases (show k < j ∨ k = j by omega) with hk' | hk'
      · rw [getD_snoc_lt (by omega)]; exact hRs k hk'
      · subst hk'
        rw [← hRl, getD_snoc_eq]; rw [hRl]; exact hsee
    · rw [e1, cJ, hsplit]; omega
  · -- the end
    rintro c' ⟨⟨j, hj, hjn, h9, -, -, hAl, R, hRl, hRat, hRs⟩, hex⟩
    rw [h9, hj] at hex
    have hjn' : j = n := by omega
    subst hjn'
    exact ⟨R, hRl, hAl, hRat, hRs⟩

end

end SweepIo

end Chazelle.Core
