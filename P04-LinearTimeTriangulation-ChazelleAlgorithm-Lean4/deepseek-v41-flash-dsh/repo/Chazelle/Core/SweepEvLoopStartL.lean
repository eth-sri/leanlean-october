module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvLoopStartF

/-!
# The sweep (WP-D), stage 3: the start of the event loop (task L0, RAM part 4)

* `stLab`: when no stop at the start key is anchored (`aF = 0`), the label list is `[V]` for the
  region faced before the end of the right stretch (`vEnd`);
* `stGap`: the gap regions (`GapLab`, case `rδ > 0`);
* `stLog`: the first log record at `lB`, `lC := 1`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-! ## The end of the right stretch -/

theorem dq_end (J : Merge.Junction) :
    dq (rL1 J) (rδ J) (rL1 J + rL2 J - 1) + 1 = rL1 J + rL2 J + rδ J := by
  have hL := Lst_pos J
  have hL' : 0 < rL1 J + rL2 J := by unfold Lst at hL; exact_mod_cast hL
  have h20 : rL2 J = 0 → rδ J = 0 := by
    unfold rL2 rδ
    have := tpos_lt J.right 0
    split_ifs <;> omega
  unfold dq
  split_ifs with h
  · have : rL2 J = 0 := ⋄
    rw [this, h20 this]; omega
  · omega

theorem vEnd_eq (J : Merge.Junction) :
    vEnd J = (6 + tpos J.right 0 + rL1 J + rL2 J + rδ J) % (chainModel J.right).W.n := by
  unfold vEnd
  Ξ dq_end
  congr 1
  ring

/-- The position of the end of the right stretch. -/
def vEndL : List Instr := [.addN zT (sw 41) (sw 42), .addN zT zT (sw 43), .addN zT zT (sw 44)]

def gap1L : List Instr := [.addN zT (sw 41) (sw 42)]

def gap2L : List Instr := [.addN zT (sw 41) (sw 42), .addN zT zT (sw 44)]

/-- **The label `V` at the start** (no anchored stop). -/
def stLab : Stmt :=
  .ifLtN aF K1 (.seq (fpos vEndL 0) (block [.copyN kL fR, .constN kN 1])) .skip

/-- **The gap regions.** -/
def stGap : Stmt :=
  .ifLtN K0 (sw 44) (.seq (fpos gap1L 1) (.seq (block [.copyN gR fR])
    (.seq (fpos gap2L 0) (block [.copyN (gR + 1) fR, .constN gN 2])))) (block [.constN gN 0])

section Prog

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-- The bounds of the right correspondence. -/
theorem corr_bounds (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) :
    6 + tpos J.right 0 < (chainModel J.right).W.n ∧
      rL1 J + rδ J + rL2 J ≤ (chainModel J.right).W.n ∧
      2 * (chainModel J.right).W.n ≤ W := by
  have hC := corr_right0 J E.hP E.hNF₂.1.2.1 E.hNF₂.1.1
  refine ⟨hC.hg', hC.hL₂, ?_⟩
  have h1 := E.hWn
  have e1 : (chainModel J.right).W.n = 2 * J.right.m + 7 := cm_n _
  have e2 : (chainModel J.whole).W.n = 2 * J.whole.m + 7 := cm_n _
  have : J.right.m ≤ J.whole.m := by show J.m₂ ≤ J.m₁ + J.m₂; omega
  omega

theorem iscrT : IScr zT := iscr_sw (⊚ zT, sw) (⊚ zT, sw)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem stLab_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (haF : c.nreg aF ≤ 1) (hroom : c.nreg ALLOC + (fposK 3 (c₀.nreg TLR) + 4) ≤ W) :
    IRS P W c₀ stLab c (fposK 3 (c₀.nreg TLR) + 4) (fun c' =>
      (c.nreg aF = 1 → ∀ q, LblR kN kL q → c'.nreg q = c.nreg q) ∧
      (c.nreg aF ≠ 1 → c'.nreg kN = 1 ∧ c'.nreg kL < N₂.nRegions ∧
        BeforeFaces (chainModel J.right) (vEnd J) 0
          (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg kL))) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ FPR r → ¬ LblR kN kL r → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hK₀ := E.hK.fix hI
  obtain ⟨g1, g2, g3, g4, g34⟩ := cst_regs E hI
  obtain ⟨hg', hL2, hW2⟩ := corr_bounds E
  unfold stLab
  refine IRS.ite (K := fposK 3 (c₀.nreg TLR) + 2) (fun h => ?_) (fun h => ?_)
  · have h0 : c.nreg aF = 0 := by rw [hK₀.2.1] at h; omega
    have hok : okB W c.nmem vEndL c.nreg := by
      ϴ vEndL, okB, okI, regI, upd, zT, sw
      ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false
      have e1 : c.nreg 240041 = 6 + tpos J.right 0 := g1
      have e2 : c.nreg 240042 = rL1 J := g2
      have e3 : c.nreg 240043 = rL2 J := g3
      have e4 : c.nreg 240044 = rδ J := g4
      Ξ e1, e2, e3, e4
      exact ⟨⟨iscrT, ⋄⟩, ⟨iscrT, ⋄⟩, ⟨iscrT, ⋄⟩, trivial⟩
    have hv : regB c.nmem vEndL c.nreg zT = 6 + tpos J.right 0 + rL1 J + rL2 J + rδ J := by
      ϴ vEndL, regB, regI, upd, zT, sw
      ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false
      have e1 : c.nreg 240041 = 6 + tpos J.right 0 := g1
      have e2 : c.nreg 240042 = rL1 J := g2
      have e3 : c.nreg 240043 = rL2 J := g3
      have e4 : c.nreg 240044 = rδ J := g4
      Ξ e1, e2, e3, e4
    have hl : ∀ q, q ≠ zT → regB c.nmem vEndL c.nreg q = c.nreg q := fun q hq =>
      regB_other _ _ _ (fun i hi => by
        ϴ' vEndL, List.mem_cons, List.not_mem_nil, or_false at hi
        rcases hi with rfl | rfl | rfl <;> exact fun h => hq h.symm)
    refine IRS.seq (K₁ := fposK 3 (c₀.nreg TLR)) (K₂ := 2) (fpos_irs E hI hok hv hl (⋄)
      (le_refl _ |>.trans (⊛)) (by simp [vEndL]; omega)) ?_
    rintro c₁ hI₁ hA₁ - ⟨r1, hb1, -, k1, A1, m1⟩
    have hb1' := hb1 rfl
    Ξ' ← vEnd_eq at hb1'
    refine (IRS.block [.copyN kL fR, .constN kN 1] hI₁ ⟨iscr_sw (⊚ kL, sw)
      (⊚ kL, sw), ⟨iscr_sw (⊚ kN, sw) (⊚ kN, sw),
        by have := E.hWh; unfold hostWords at this; omega⟩, trivial⟩).mono (✓) ?_
    rintro c' rfl
    have vL : regB c₁.nmem [.copyN kL fR, .constN kN 1] c₁.nreg kL = c₁.nreg fR := by
      Θ regB, regI, upd, kL, kN, fR, sw
    have vN : regB c₁.nmem [.copyN kL fR, .constN kN 1] c₁.nreg kN = 1 := by
      Θ regB, regI, upd, kN
    have vo : ∀ q, q ≠ kL → q ≠ kN → regB c₁.nmem [.copyN kL fR, .constN kN 1] c₁.nreg q =
        c₁.nreg q := fun q h1 h2 => ⊚ regB, regI, upd_other _ _ _ h1, upd_other _ _ _ h2
    refine ⟨fun h1 => ⋄, fun _ => ⟨vN, by show regB _ _ _ kL < _; rw [vL]; exact r1,
      by show BeforeFaces _ _ _ (regOf _ _ _ (regB _ _ _ kL)); rw [vL]; exact hb1'⟩,
      fun r hr hfp hlb hra => ?_, ?_, fun a ha => m1 a ha⟩
    · show regB _ _ _ r = _
      Ξ vo r (fun h => hlb (Or.inr (by subst h; omega))) (fun h => hlb (Or.inl h))
      exact k1 r hr hfp hra
    · show c.nreg ALLOC ≤ regB _ _ _ ALLOC
      rw [vo ALLOC (⊚ ALLOC, kL, sw) (⊚ ALLOC, kN, sw)]; exact A1
  · exact IRS.skip hI ⟨fun _ _ _ => rfl, fun h' => absurd (by rw [hK₀.2.1] at h; omega) h',
      fun _ _ _ _ _ => rfl, le_rfl, fun _ _ => rfl⟩

/-- The registers of the gap regions. -/
def GapR (r : ℕ) : Prop := r = gN ∨ r = gR ∨ r = gR + 1

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
theorem stGap_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hroom : c.nreg ALLOC + (fposK 1 (c₀.nreg TLR) + fposK 2 (c₀.nreg TLR) + 5) ≤ W) :
    IRS P W c₀ stGap c (fposK 1 (c₀.nreg TLR) + fposK 2 (c₀.nreg TLR) + 5) (fun c' =>
      c'.nreg gN ≤ 2 ∧ (∀ i, i < c'.nreg gN → c'.nreg (gR + i) < N₂.nRegions) ∧
      (∀ V, GapLab J (N₂.F (chainModel J.right) (Qof P)) V →
        ∃ i, i < c'.nreg gN ∧ regOf (chainModel J.right) (Qof P) N₂ (c'.nreg (gR + i)) = V) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ FPR r → ¬ GapR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hK₀ := E.hK.fix hI
  obtain ⟨g1, g2, g3, g4, g34⟩ := cst_regs E hI
  obtain ⟨hg', hL2, hW2⟩ := corr_bounds E
  have hNF := E.hNF₂
  obtain ⟨hRC, -⟩ := regOf_spec hNF
  have hW1 : 2 ≤ W := by have := E.hWh; unfold hostWords at this; omega
  unfold stGap
  refine IRS.ite (K := fposK 1 (c₀.nreg TLR) + fposK 2 (c₀.nreg TLR) + 3) (fun h => ?_) (fun h => ?_)
  · have hδ : 0 < rδ J := by rw [hK₀.1, g4] at h; exact h
    -- the first gap region
    have hok1 : okB W c.nmem gap1L c.nreg := by
      simp only [gap1L, okB, okI]
      exact ⟨⟨iscrT, by rw [g1, g2]; omega⟩, trivial⟩
    have hv1 : regB c.nmem gap1L c.nreg zT = 6 + tpos J.right 0 + rL1 J := by
      simp only [gap1L, regB, regI, upd_same]; rw [g1, g2]
    have hl1 : ∀ q, q ≠ zT → regB c.nmem gap1L c.nreg q = c.nreg q := fun q hq =>
      regB_other _ _ _ (fun i hi => by
        simp only [gap1L, List.mem_cons, List.not_mem_nil, or_false] at hi
        subst hi; exact fun h => hq h.symm)
    refine IRS.seq (K₁ := fposK 1 (c₀.nreg TLR)) (K₂ := 1 + (fposK 2 (c₀.nreg TLR) + 2))
      (fpos_irs E hI (side := 1) hok1 hv1 hl1 (by omega) le_rfl (by
        show c.nreg ALLOC + fposK 1 (c₀.nreg TLR) ≤ W; omega)) ?_ |>.mono
      (by omega) (fun _ h => h)
    rintro c₁ hI₁ hA₁ hA₁' ⟨r1, -, ha1, k1, A1, m1⟩
    have ha1' := ha1 rfl
    refine IRS.seq (K₁ := 1) (IRS.block [.copyN gR fR] hI₁
      ⟨iscr_sw (by simp [gR, sw]) (by simp [gR, sw]), trivial⟩) ?_
    rintro c₂ hI₂ hA₂ - rfl
    have vR2 : regB c₁.nmem [.copyN gR fR] c₁.nreg gR = c₁.nreg fR := by simp [regB, regI]
    have vo2 : ∀ q, q ≠ gR → regB c₁.nmem [.copyN gR fR] c₁.nreg q = c₁.nreg q := fun q h =>
      by simp [regB, regI, upd_other _ _ _ h]
    set c₂ : Config := { c₁ with nreg := regB c₁.nmem [.copyN gR fR] c₁.nreg } with hc₂
    have kk2 : ∀ q, q ≠ gR → bandOf q ∉ oracleBands → ¬ FPR q → q ≠ ALLOC →
        c₂.nreg q = c.nreg q := fun q h1 h2 h3 h4 => (vo2 q h1).trans (k1 q h2 h3 h4)
    have cst : ∀ k, (k = 41 ∨ k = 42 ∨ k = 44) → c₂.nreg (sw k) = c.nreg (sw k) := by
      rintro k (rfl | rfl | rfl) <;>
        exact kk2 _ (by simp [gR, sw]) (not_oracle_sw (by simp [sw]) (by simp [sw]))
          (by simp [FPR, FR, zT, fE, fA, fR, sw]) (by simp [ALLOC, sw])
    -- the second gap region
    have hok2 : okB W c₂.nmem gap2L c₂.nreg := by
      simp only [gap2L, okB, okI, regI, upd, zT, sw]
      simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
      have e1 : c₂.nreg 240041 = 6 + tpos J.right 0 := (cst 41 (Or.inl rfl)).trans g1
      have e2 : c₂.nreg 240042 = rL1 J := (cst 42 (Or.inr (Or.inl rfl))).trans g2
      have e4 : c₂.nreg 240044 = rδ J := (cst 44 (Or.inr (Or.inr rfl))).trans g4
      rw [e1, e2, e4]
      exact ⟨⟨iscrT, by omega⟩, ⟨iscrT, by omega⟩, trivial⟩
    have hv2 : regB c₂.nmem gap2L c₂.nreg zT = 6 + tpos J.right 0 + rL1 J + rδ J := by
      simp only [gap2L, regB, regI, upd, zT, sw]
      simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
      have e1 : c₂.nreg 240041 = 6 + tpos J.right 0 := (cst 41 (Or.inl rfl)).trans g1
      have e2 : c₂.nreg 240042 = rL1 J := (cst 42 (Or.inr (Or.inl rfl))).trans g2
      have e4 : c₂.nreg 240044 = rδ J := (cst 44 (Or.inr (Or.inr rfl))).trans g4
      rw [e1, e2, e4]
    have hl2 : ∀ q, q ≠ zT → regB c₂.nmem gap2L c₂.nreg q = c₂.nreg q := fun q hq =>
      regB_other _ _ _ (fun i hi => by
        simp only [gap2L, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> exact fun h => hq h.symm)
    have hA2' : c₂.nreg ALLOC = c₁.nreg ALLOC := vo2 ALLOC (by simp [ALLOC, gR, sw])
    refine IRS.seq (K₁ := fposK 2 (c₀.nreg TLR)) (K₂ := 2)
      (fpos_irs E hI₂ (side := 0) hok2 hv2 hl2 (by omega) (by norm_num) (by
        show c₂.nreg ALLOC + fposK 2 (c₀.nreg TLR) ≤ W; rw [hA2']; omega)) ?_
    rintro c₃ hI₃ hA₃ - ⟨r3, hb3, -, k3, A3, m3⟩
    have hb3' := hb3 rfl
    refine (IRS.block [.copyN (gR + 1) fR, .constN gN 2] hI₃
      ⟨iscr_sw (by simp [gR, sw]) (by simp [gR, sw]),
        ⟨iscr_sw (by simp [gN, sw]) (by simp [gN, sw]), hW1⟩, trivial⟩).mono (by simp) ?_
    rintro c' rfl
    have vR3 : regB c₃.nmem [.copyN (gR + 1) fR, .constN gN 2] c₃.nreg (gR + 1) = c₃.nreg fR := by
      simp [regB, regI, upd, gR, gN, sw]
    have vN3 : regB c₃.nmem [.copyN (gR + 1) fR, .constN gN 2] c₃.nreg gN = 2 := by
      simp [regB, regI, upd, gN]
    have vo3 : ∀ q, q ≠ gR + 1 → q ≠ gN →
        regB c₃.nmem [.copyN (gR + 1) fR, .constN gN 2] c₃.nreg q = c₃.nreg q := fun q h1 h2 => by
      simp [regB, regI, upd_other _ _ _ h1, upd_other _ _ _ h2]
    have gR3 : c₃.nreg gR = c₁.nreg fR := by
      rw [k3 gR (not_oracle_sw (by simp [gR, sw]) (by simp [gR, sw]))
        (by simp [FPR, FR, zT, fE, fA, fR, gR, sw]) (by simp [ALLOC, gR, sw])]
      exact vR2
    have eR0 : regB c₃.nmem [.copyN (gR + 1) fR, .constN gN 2] c₃.nreg (gR + 0) = c₁.nreg fR := by
      rw [vo3 (gR + 0) (by simp [gR, sw]) (by simp [gR, gN, sw]), Nat.add_zero, gR3]
    have ev : (6 + tpos J.right 0 + rL1 J + rδ J) % (chainModel J.right).W.n =
        (6 + tpos J.right 0 + rL1 J + rδ J) % (chainModel J.right).W.n := rfl
    refine ⟨by rw [show ({ c₃ with nreg := _ } : Config).nreg gN = 2 from vN3], fun i hi => ?_,
      fun V hV => ?_, fun r hr hfp hgr hra => ?_, ?_, fun a ha => ?_⟩
    · have hi' : i < 2 := by rw [show ({ c₃ with nreg := _ } : Config).nreg gN = 2 from vN3] at hi; exact hi
      interval_cases i
      · show regB _ _ _ (gR + 0) < _; rw [eR0]; exact r1
      · show regB _ _ _ (gR + 1) < _; rw [vR3]; exact r3
    · obtain ⟨-, hVr, hfac⟩ := hV
      have e1 := hRC.1 _ r1
      have e3 := hRC.1 _ r3
      rcases hfac with hfac | hfac
      · exact ⟨0, by rw [show ({ c₃ with nreg := _ } : Config).nreg gN = 2 from vN3]; norm_num,
          by show regOf _ _ _ (regB _ _ _ (gR + 0)) = V; rw [eR0]
             exact after_unique one_pos e1 hVr ha1' hfac⟩
      · exact ⟨1, by rw [show ({ c₃ with nreg := _ } : Config).nreg gN = 2 from vN3]; norm_num,
          by show regOf _ _ _ (regB _ _ _ (gR + 1)) = V; rw [vR3]
             exact before_unique le_rfl e3 hVr hb3' hfac⟩
    · show regB _ _ _ r = _
      rw [vo3 r (fun h => hgr (Or.inr (Or.inr h))) (fun h => hgr (Or.inl h)), k3 r hr hfp hra,
        kk2 r (fun h => hgr (Or.inr (Or.inl h))) hr hfp hra]
    · show c.nreg ALLOC ≤ regB _ _ _ ALLOC
      rw [vo3 _ (by simp [ALLOC, gR, sw]) (by simp [ALLOC, gN, sw])]
      have := A1; have := A3; omega
    · rw [m3 a (by have := A1; omega)]
      show c₁.nmem a = _
      exact m1 a ha
  · -- no gap
    have hδ : rδ J = 0 := by rw [hK₀.1, g4] at h; omega
    refine (IRS.block [.constN gN 0] hI ⟨⟨iscr_sw (by simp [gN, sw]) (by simp [gN, sw]),
      Nat.zero_le _⟩, trivial⟩).mono (by unfold fposK; simp) ?_
    rintro c' rfl
    have v0 : regB c.nmem [.constN gN 0] c.nreg gN = 0 := by simp [regB, regI]
    have vo : ∀ q, q ≠ gN → regB c.nmem [.constN gN 0] c.nreg q = c.nreg q := fun q h => by
      simp [regB, regI, upd_other _ _ _ h]
    refine ⟨by show regB _ _ _ gN ≤ 2; rw [v0]; norm_num, fun i hi => ?_, fun V hV => ?_,
      fun r hr hfp hgr hra => ?_, ?_, fun _ _ => rfl⟩
    · exact absurd hi (by show ¬ i < regB _ _ _ gN; rw [v0]; omega)
    · exact absurd hV.1 (by omega)
    · show regB _ _ _ r = _; exact vo r (fun h => hgr (Or.inl h))
    · show c.nreg ALLOC ≤ regB _ _ _ ALLOC; rw [vo _ (by simp [ALLOC, gN, sw])]

end Prog

end

end SweepEv

end Chazelle.Core
