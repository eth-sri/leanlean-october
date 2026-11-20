module

meta import Chazelle.Programs.RegisterGuard

public import Chazelle.Core.SweepEvLoopStartS
public import Chazelle.Core.SweepEvFace3

/-!
# The sweep (WP-D), stage 3: the start of the event loop (task L0, RAM part 3: faced regions)

`face_irs`: the run step of the procedure `face` of `SweepEvFace3` (the proof of `faceTask`, for the
concrete program).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sideInArc)
open OracleQ (sj sk ek succP predP)

@[expose] public section

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The region of `N₂` faced at a walk vertex of `C₂`** (the run step of `face`). -/
theorem face_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction}
    {N₁ N₂ : NF} (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hfe : c.nreg fE < J.rightModel.W.n) (_hfa : c.nreg fA ≤ 1)
    (hroom : c.nreg ALLOC + 30000 * (c₀.nreg TLR + 1) ≤ W) :
    IRS P W c₀ face c (30000 * (c₀.nreg TLR + 1)) (FaceOut P J N₂ c) := by
  have hP₂ := E.hP
  have hNF := E.hNF₂
  unfold face
  refine IRS.mono (K := faceLocK (c₀.nreg TLR) + (11015 + (11015 + 10))) ?_
    (face_cost _) (fun _ h => h)
  -- 1. the prefix
  refine IRS.seq (faceLoc_irs E hI hfe (face_room1 hroom)) ?_
  rintro c₁ hI₁ - - ⟨j, hj, hl1, hl2, r0, r1, r2, vSE, vSH, vEE, vEH, hm1, hAl1, hk1⟩
  have hK₁ := E.hK.fix hI₁
  have hfe1 : c₁.nreg fE = c.nreg fE :=
    hk1 _ (by register_guard)
      (Or.inr (by decide))
  have hfa1 : c₁.nreg fA = c.nreg fA :=
    hk1 _ (by register_guard)
      (Or.inr (by decide))
  have hsj := NFLoc.seq_lt hNF hj
  obtain ⟨⟨pps, hse, hsy⟩, ⟨ppe, hee, hey⟩⟩ := arc_end_facts hP₂ hNF hsj
  
  -- 2. normalise the start of the arc
  refine IRS.seq (normS_irs (dsc := sw 21) (pe := fSE) (ph := fSH) (o := fO) (C := J.right) hI₁ hK₁
    (E.ctx2' hI₁) (by decide)
    (by decide)
    (by rwa [vSE]) (by rwa [vSE, vSH]) (by rwa [vSE, vSH])
    (by rw [hAl1]; exact face_room2 hroom)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨v2SE, v2SH, k2, hA2, hm2⟩
  have hK₂ := E.hK.fix hI₂
  have n2 := k2
  have n2' : ∀ q, (q = fEE ∨ q = fEH ∨ q = fE ∨ q = fA ∨ q = lR0 ∨ q = lR1 ∨ q = lR2) →
      c₂.nreg q = c₁.nreg q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact n2 _ (by register_guard)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  -- 3. normalise the end of the arc
  refine IRS.seq (normS_irs (dsc := sw 21) (pe := fEE) (ph := fEH) (o := fO) (C := J.right) hI₂ hK₂
    (E.ctx2' hI₂) (by decide)
    (by decide)
    (by ram_rw assumption [n2' fEE, vEE])
    (by ram_simp [n2', vEE, vEH] <;> reg_omega)
    (by ram_simp [n2', vEE, vEH] <;> reg_omega)
    (by have := hA₂'; rw [hAl1] at this; exact face_room3 hroom this)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨v3EE, v3EH, k3, hA3, hm3⟩
  have n3 := k3
  have n3' : ∀ q, (q = fSE ∨ q = fSH ∨ q = fE ∨ q = fA ∨ q = lR0 ∨ q = lR1 ∨ q = lR2 ∨
      q = K0 ∨ q = K1) → c₃.nreg q = c₂.nreg q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact n3 _ (by register_guard)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  have hK₃ := E.hK.fix hI₃
  -- 4. the selection
  refine (faceSel_irs hI₃ hK₃.1).mono le_rfl ?_
  rintro c₄ ⟨v4R, k4, hm4⟩
  -- the values at the selection
  have eA : c₃.nreg fA = c.nreg fA := by ram_rw [n3' fA, n2' fA, hfa1]
  have eE : c₃.nreg fE = c.nreg fE := by ram_rw [n3' fE, n2' fE, hfe1]
  have eK1 := hK₃.2.1
  have eSE : c₃.nreg fSE = (N₂.arc (sj N₂ j)).s.edge := by ram_rw [n3' fSE, v2SE, vSE]
  have eSH : c₃.nreg fSH = nhgt J.rightModel (Qof P) (N₂.arc (sj N₂ j)).s := by
    ram_rw [n3' fSH, v2SH, vSE, vSH]
  have eEE : c₃.nreg fEE = (N₂.arc (sj N₂ j)).e.edge := by ram_rw [v3EE, n2' fEE, vEE]
  have eEH : c₃.nreg fEH = nhgt J.rightModel (Qof P) (N₂.arc (sj N₂ j)).e := by
    ram_finish [v3EH, n2', vEE, vEH]
  have eR0 : c₃.nreg lR0 = (N₂.arc (sj N₂ (predP N₂.arcs.length j))).reg := by
    ram_rw [n3' lR0, n2' lR0, r0]
  have eR1 : c₃.nreg lR1 = (N₂.arc (sj N₂ j)).reg := by
    ram_rw [n3' lR1, n2' lR1, r1]
  have eR2 : c₃.nreg lR2 = (N₂.arc (sj N₂ (succP N₂.arcs.length j))).reg := by
    ram_rw [n3' lR2, n2' lR2, r2]
  rw [eA, eE, eK1, eSE, eSH, eEE, eEH, eR0, eR1, eR2] at v4R
  -- the key tests
  have hS : (N₂.arc (sj N₂ j)).s.edge = c.nreg fE ∧
      nhgt J.rightModel (Qof P) (N₂.arc (sj N₂ j)).s = 0 ↔
      sk J.rightModel (Qof P) N₂ j = c.nreg fE :=
    (key_eq_nat_iff pps (c.nreg fE)).symm
  have hE : (N₂.arc (sj N₂ j)).e.edge = c.nreg fE ∧
      nhgt J.rightModel (Qof P) (N₂.arc (sj N₂ j)).e = 0 ↔
      ek J.rightModel (Qof P) N₂ j = c.nreg fE :=
    (key_eq_nat_iff ppe (c.nreg fE)).symm
  have hjP := OracleQ.predP_lt hj
  have hjN := OracleQ.succP_lt hj
  refine ⟨?_, fun h0 => ?_, fun h1 => ?_, ?_, ?_, ?_⟩
  · rw [v4R]
    split_ifs
    · exact (arc_regOf hNF hjP).1
    · exact (arc_regOf hNF hj).1
    · exact (arc_regOf hNF hjN).1
    · exact (arc_regOf hNF hj).1
  · ram_rw [v4R, ite_eq_left]
    split_ifs with h
    · exact face_before_eq hP₂ hNF hfe hj (hS.1 h)
    · exact face_before_ne hP₂ hNF hfe hj hl1 hl2 (fun h' => h (hS.2 h'))
  · ram_rw [v4R, ite_eq_right]
    split_ifs with h
    · exact face_after_eq hP₂ hNF hfe hj (hE.1 h)
    · exact face_after_ne hP₂ hNF hfe hj hl1 hl2 (fun h' => h (hE.2 h'))
  · intro a ha
    ram_rw [hm4, hm3 a, hm2 a, hm1]
  · ram_simp [k4] <;> omega
  · intro r hr hFR hra
    have hout' : ¬ (sw 700 ≤ r ∧ r < sw 2200) := fun h => hFR (Or.inl h)
    unfold sw at hout'
    have hout : r < sw 1102 ∨ sw 1203 < r := by reg_omega
    have hrR : r ≠ fR := fun h => hFR (Or.inr (Or.inl h))
    have h1 : r ≠ fEH := fun h => by subst h; unfold fEH sw at hout'; omega
    have h2 : r ≠ fSH := fun h => by subst h; unfold fSH sw at hout'; omega
    have h3 : r ≠ fO := fun h => by subst h; unfold fO sw at hout'; omega
    have h4 : r ≠ fO + 1 := fun h => by subst h; unfold fO sw at hout'; omega
    rw [k4 r hrR, n3 r hr h1 h3 h4 hra, n2 r hr h2 h3 h4 hra]
    exact hk1 r hr hout


/-! ## The constants of the right correspondence -/

section Consts

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

theorem cst_regs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    c.nreg (sw 41) = 6 + tpos J.right 0 ∧ c.nreg (sw 42) = rL1 J ∧ c.nreg (sw 43) = rL2 J ∧
      c.nreg (sw 44) = rδ J ∧ c.nreg (sw 34) = J.rightModel.W.n := by
  obtain ⟨H, -, hst⟩ := E.hst
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, -, -, h34, -⟩ := hst
  have fx : ∀ k, k < 700 → c.nreg (sw k) = c₀.nreg (sw k) := fun k hk =>
    hI.hin _ (by reg_omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [fx, show sw 41 = sw (40 + 1) from rfl, h40, cstR]
  · simp [fx, show sw 42 = sw (40 + 2) from rfl, h40, cstR]
  · simp [fx, show sw 43 = sw (40 + 3) from rfl, h40, cstR]
  · simp [fx, show sw 44 = sw (40 + 4) from rfl, h40, cstR]
  simp [fx, h34, cm_n]

end Consts

/-! ## Reduction modulo -/

/-- `dst := a mod b` for `a < 2 b`. -/
def modR (dst a b : ℕ) : Stmt := .ifLtN a b (.instr (.copyN dst a)) (.instr (.subN dst a b))

theorem modR_irs {P : Polygon} {W : ℕ} {c₀ c : Config} {dst a b : ℕ} (hI : IInv W c₀ c)
    (hd : IScr dst) (h2 : c.nreg a < 2 * c.nreg b) :
    IRS P W c₀ (modR dst a b) c 3 (fun c' => c'.nreg dst = c.nreg a % c.nreg b ∧
      (∀ q, q ≠ dst → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  unfold modR
  refine IRS.ite (K := 1) (fun h => ?_) (fun h => ?_)
  · refine (IRS.instr1 (i := .copyN dst a) hI hd).mono le_rfl ?_
    rintro c' rfl
    refine ⟨by simp [regI, Nat.mod_eq_of_lt h], fun q hq => by ram_finish, rfl⟩
  · refine (IRS.instr1 (i := .subN dst a b) hI hd).mono le_rfl ?_
    rintro c' rfl
    refine ⟨?_, fun q hq => by ram_finish, rfl⟩
    ram_finish [regI, Nat.mod_eq_sub_mod, Nat.mod_eq_of_lt]

/-! ## A faced region at a computed vertex -/

/-- Compute `zT` (block `l`), `fE := zT mod n₂`, `fA := side`, run `face`. -/
def fpos (l : List Instr) (side : ℕ) : Stmt :=
  .seq (block l) (.seq (modR fE zT (sw 34)) (.seq (.instr (.constN fA side)) face))

/-- The cost of `fpos`. -/
def fposK (L T : ℕ) : ℕ := L + (3 + (1 + 30000 * (T + 1)))

/-- The registers `fpos` may write besides `FR`. -/
def FPR (r : ℕ) : Prop := FR r ∨ r = zT ∨ r = fE ∨ r = fA

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The region faced at a computed vertex.** -/
theorem fpos_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction}
    {N₁ N₂ : NF} (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) {l : List Instr}
    {side v : ℕ} (hok : okB W c.nmem l c.nreg) (hv : regB c.nmem l c.nreg zT = v)
    (hl : ∀ q, q ≠ zT → regB c.nmem l c.nreg q = c.nreg q)
    (hv2 : v < 2 * J.rightModel.W.n) (hs : side ≤ 1)
    (hroom : c.nreg ALLOC + fposK l.length (c₀.nreg TLR) ≤ W) :
    IRS P W c₀ (fpos l side) c (fposK l.length (c₀.nreg TLR)) (fun c' =>
      c'.nreg fR < N₂.nRegions ∧
      (side = 0 → BeforeFaces J.rightModel (v % J.rightModel.W.n) 0
        (regOf J.rightModel (Qof P) N₂ (c'.nreg fR))) ∧
      (side = 1 → AfterFaces J.rightModel (v % J.rightModel.W.n) 0
        (regOf J.rightModel (Qof P) N₂ (c'.nreg fR))) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ FPR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (MemEqBelow (c.nreg ALLOC) c'.nmem c.nmem)) := by
  unfold fpos fposK
  unfold fposK at hroom
  have h34c := (cst_regs E hI).2.2.2.2
  refine IRS.seq (IRS.block l hI hok) ?_
  rintro c₁ hI₁ - - rfl
  have h34 := (cst_regs E hI₁).2.2.2.2
  refine IRS.seq (modR_irs (dst := fE) (a := zT) (b := sw 34) hI₁
    (by register_guard) (by
      simp_all)) ?_
  rintro c₂ hI₂ - - ⟨e2, f2, m2⟩
  have e2' : c₂.nreg fE = v % J.rightModel.W.n := by
    simp_all
  refine IRS.seq (K₁ := 1) (IRS.instr1 (i := .constN fA side) hI₂
    ⟨iscr_sw (by decide) (by decide), by have := E.hWh; unfold hostWords at this; omega⟩) ?_
  rintro c₃ hI₃ hA₃ - hc₃
  have e3E : c₃.nreg fE = v % J.rightModel.W.n := by
    ram_finish
  have e3A : c₃.nreg fA = side := by rw [hc₃]; simp [regI]
  have hA2 : c₂.nreg ALLOC = c.nreg ALLOC := by
    ram_finish
  have hA3 : c₃.nreg ALLOC = c.nreg ALLOC := by
    ram_finish
  refine (face_irs E hI₃ (by rw [e3E]; exact Nat.mod_lt _ (by have := hv2; omega))
    (by rwa [e3A]) (by
      rw [hA3]; generalize 30000 * (c₀.nreg TLR + 1) = Y at hroom ⊢; omega)).mono le_rfl ?_
  rintro c₄ ⟨r4, hb4, ha4, m4, A4, k4⟩
  rw [e3A, e3E] at hb4 ha4
  refine ⟨r4, hb4, ha4, fun r hr hfp hra => ?_, by omega, fun a ha => ?_⟩
  · rw [k4 r hr (fun h => hfp (Or.inl h)) hra]
    rw [hc₃]
    simp only [regI]
    rw [upd_other _ _ _ (fun h => hfp (Or.inr (Or.inr (Or.inr h)))),
      f2 r (fun h => hfp (Or.inr (Or.inr (Or.inl h))))]
    exact hl r (fun h => hfp (Or.inr (Or.inl h)))
  · simp_all 

end

end SweepEv

end Chazelle.Core
