module

public meta import Chazelle.Arithmetic

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
    (hfe : c.nreg fE < (chainModel J.right).W.n) (_hfa : c.nreg fA ≤ 1)
    (hroom : c.nreg ALLOC + 30000 * (c₀.nreg TLR + 1) ≤ W) :
    IRS P W c₀ face c (30000 * (c₀.nreg TLR + 1)) (FaceOut P J N₂ c) := by
  have hP₂ : J.right.P.Simple := E.hP
  have hNF := E.hNF₂
  unfold face
  refine IRS.mono (K := faceLocK (c₀.nreg TLR) + (11015 + (11015 + 10))) ?_
    (face_cost _) (fun _ h => h)
  -- 1. the prefix
  refine IRS.seq (faceLoc_irs E hI hfe (face_room1 hroom)) ?_
  rintro c₁ hI₁ - - ⟨j, hj, hl1, hl2, r0, r1, r2, vSE, vSH, vEE, vEH, hm1, hAl1, hk1⟩
  have hK₁ := E.hK.fix hI₁
  have hfe1 : c₁.nreg fE = c.nreg fE :=
    hk1 _ (not_oracle_sw (by omega_nf) (by omega_nf))
      (Or.inr (by omega_nf))
  have hfa1 : c₁.nreg fA = c.nreg fA :=
    hk1 _ (not_oracle_sw (by omega_nf) (by omega_nf))
      (Or.inr (by omega_nf))
  have hsj := NFLoc.seq_lt hNF hj
  obtain ⟨⟨pps, hse, hsy⟩, ⟨ppe, hee, hey⟩⟩ := arc_end_facts hP₂ hNF hsj
  
  -- 2. normalise the start of the arc
  refine IRS.seq (normS_irs (dsc := sw 21) (pe := fSE) (ph := fSH) (o := fO) (C := J.right) hI₁ hK₁
    (E.ctx2' hI₁) ⟨by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf, by omega_nf⟩
    ⟨by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf, by omega_nf,
      by omega_nf⟩
    (by rw [vSE]; exact hse) (by rw [vSE, vSH]; exact pps) (by rw [vSE, vSH]; exact hsy)
    (by grind)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨v2SE, v2SH, k2, hA2, hm2⟩
  have hK₂ := E.hK.fix hI₂
  have n2 : ∀ q, bandOf q ∉ oracleBands → q ≠ fSH → q ≠ fO → q ≠ fO + 1 → q ≠ ALLOC →
      c₂.nreg q = c₁.nreg q := k2
  have n2' : ∀ q, (q = fEE ∨ q = fEH ∨ q = fE ∨ q = fA ∨ q = lR0 ∨ q = lR1 ∨ q = lR2) →
      c₂.nreg q = c₁.nreg q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact n2 _ (not_oracle_sw (by omega_nf)
        (by omega_nf))
        (by omega_nf)
        (by omega_nf)
        (by omega_nf)
        (by omega_nf)
  -- 3. normalise the end of the arc
  refine IRS.seq (normS_irs (dsc := sw 21) (pe := fEE) (ph := fEH) (o := fO) (C := J.right) hI₂ hK₂
    (E.ctx2' hI₂) ⟨by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf, by omega_nf⟩
    ⟨by omega_nf, by omega_nf, by omega_nf,
      by omega_nf, by omega_nf, by omega_nf,
      by omega_nf⟩
    (by rw [n2' fEE (by simp), vEE]; exact hee)
    (by rw [n2' fEE (by simp), n2' fEH (by simp), vEE, vEH]; exact ppe)
    (by rw [n2' fEE (by simp), n2' fEH (by simp), vEE, vEH]; exact hey)
    (by grind)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨v3EE, v3EH, k3, hA3, hm3⟩
  have n3 : ∀ q, bandOf q ∉ oracleBands → q ≠ fEH → q ≠ fO → q ≠ fO + 1 → q ≠ ALLOC →
      c₃.nreg q = c₂.nreg q := k3
  have n3' : ∀ q, (q = fSE ∨ q = fSH ∨ q = fE ∨ q = fA ∨ q = lR0 ∨ q = lR1 ∨ q = lR2 ∨
      q = K0 ∨ q = K1) → c₃.nreg q = c₂.nreg q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact n3 _ (not_oracle_sw (by omega_nf)
        (by omega_nf))
        (by omega_nf)
        (by omega_nf)
        (by omega_nf)
        (by omega_nf)
  have hK₃ := E.hK.fix hI₃
  -- 4. the selection
  refine (faceSel_irs hI₃ hK₃.1).mono le_rfl ?_
  rintro c₄ ⟨v4R, k4, hm4⟩
  -- the values at the selection
  have eA : c₃.nreg fA = c.nreg fA := by grind
  have eE : c₃.nreg fE = c.nreg fE := by grind
  have eK1 : c₃.nreg K1 = 1 := hK₃.2.1
  have eSE : c₃.nreg fSE = (N₂.arc (sj N₂ j)).s.edge := by grind
  have eSH : c₃.nreg fSH = nhgt (chainModel J.right) (Qof P) (N₂.arc (sj N₂ j)).s := by
    rw [n3' fSH (by simp), v2SH, vSE, vSH]
  have eEE : c₃.nreg fEE = (N₂.arc (sj N₂ j)).e.edge := by grind
  have eEH : c₃.nreg fEH = nhgt (chainModel J.right) (Qof P) (N₂.arc (sj N₂ j)).e := by
    rw [v3EH, n2' fEE (by simp), n2' fEH (by simp), vEE, vEH]
  have eR0 : c₃.nreg lR0 = (N₂.arc (sj N₂ (predP N₂.arcs.length j))).reg := by
    grind
  have eR1 : c₃.nreg lR1 = (N₂.arc (sj N₂ j)).reg := by
    grind
  have eR2 : c₃.nreg lR2 = (N₂.arc (sj N₂ (succP N₂.arcs.length j))).reg := by
    grind
  rw [eA, eE, eK1, eSE, eSH, eEE, eEH, eR0, eR1, eR2] at v4R
  -- the key tests
  have hS : (N₂.arc (sj N₂ j)).s.edge = c.nreg fE ∧
      nhgt (chainModel J.right) (Qof P) (N₂.arc (sj N₂ j)).s = 0 ↔
      sk (chainModel J.right) (Qof P) N₂ j = c.nreg fE :=
    (key_eq_nat_iff pps (c.nreg fE)).symm
  have hE : (N₂.arc (sj N₂ j)).e.edge = c.nreg fE ∧
      nhgt (chainModel J.right) (Qof P) (N₂.arc (sj N₂ j)).e = 0 ↔
      ek (chainModel J.right) (Qof P) N₂ j = c.nreg fE :=
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
  · rw [v4R, ite_eq_left (by omega)]
    split_ifs with h
    · exact face_before_eq hP₂ hNF hfe hj (hS.1 h)
    · exact face_before_ne hP₂ hNF hfe hj hl1 hl2 (fun h' => h (hS.2 h'))
  · rw [v4R, ite_eq_right (by omega)]
    split_ifs with h
    · exact face_after_eq hP₂ hNF hfe hj (hE.1 h)
    · exact face_after_ne hP₂ hNF hfe hj hl1 hl2 (fun h' => h (hE.2 h'))
  · ram_simp
  · rw [k4 ALLOC (by omega_nf)]; omega
  · intro r hr hFR hra
    have hout' : ¬ (sw 700 ≤ r ∧ r < sw 2200) := fun h => hFR (Or.inl h)
    unfold sw at hout'
    have hout : r < sw 1102 ∨ sw 1203 < r := by omega_nf
    have hrR : r ≠ fR := fun h => hFR (Or.inr (Or.inl h))
    have h1 : r ≠ fEH := fun h => by grind [fEH, sw]
    have h2 : r ≠ fSH := fun h => by subst h; unfold fSH sw at hout'; omega
    have h3 : r ≠ fO := fun h => by subst h; unfold fO sw at hout'; omega
    have h4 : r ≠ fO + 1 := fun h => by subst h; unfold fO sw at hout'; omega
    rw [k4 r hrR, n3 r hr h1 h3 h4 hra, n2 r hr h2 h3 h4 hra]
    grind


/-! ## The constants of the right correspondence -/

section Consts

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

theorem cst_regs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    c.nreg (sw 41) = 6 + tpos J.right 0 ∧ c.nreg (sw 42) = rL1 J ∧ c.nreg (sw 43) = rL2 J ∧
      c.nreg (sw 44) = rδ J ∧ c.nreg (sw 34) = (chainModel J.right).W.n := by
  obtain ⟨H, -, hst⟩ := E.hst
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, -, -, h34, -⟩ := hst
  have fx : ∀ k, k < 700 → c.nreg (sw k) = c₀.nreg (sw k) := fun k hk =>
    hI.hin _ (by omega_nf)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · grind [cstR]
  · grind [cstR]
  · grind [cstR]
  all_goals (grind [cstR, cm_n])

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
    refine ⟨by simp [regI, Nat.mod_eq_of_lt h], fun q hq => by simp_all [regI] , rfl⟩
  · refine (IRS.instr1 (i := .subN dst a b) hI hd).mono le_rfl ?_
    rintro c' rfl
    refine ⟨?_, fun q hq => by simp_all [regI] , rfl⟩
    simp only [regI, upd_same]
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

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
    (hv2 : v < 2 * (chainModel J.right).W.n) (hs : side ≤ 1)
    (hroom : c.nreg ALLOC + fposK l.length (c₀.nreg TLR) ≤ W) :
    IRS P W c₀ (fpos l side) c (fposK l.length (c₀.nreg TLR)) (fun c' =>
      c'.nreg fR < N₂.nRegions ∧
      (side = 0 → BeforeFaces (chainModel J.right) (v % (chainModel J.right).W.n) 0
        (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg fR))) ∧
      (side = 1 → AfterFaces (chainModel J.right) (v % (chainModel J.right).W.n) 0
        (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg fR))) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ FPR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  unfold fpos fposK
  unfold fposK at hroom
  have h34c := (cst_regs E hI).2.2.2.2
  refine IRS.seq (IRS.block l hI hok) ?_
  rintro c₁ hI₁ - - rfl
  have h34 := (cst_regs E hI₁).2.2.2.2
  refine IRS.seq (modR_irs (dst := fE) (a := zT) (b := sw 34) hI₁
    (iscr_sw (by omega_nf) (by omega_nf)) (by
      omega_nf)) ?_
  rintro c₂ hI₂ - - ⟨e2, f2, m2⟩
  
  refine IRS.seq (K₁ := 1) (IRS.instr1 (i := .constN fA side) hI₂
    ⟨iscr_sw (by omega_nf) (by omega_nf), by omega⟩) ?_
  rintro c₃ hI₃ hA₃ - hc₃
  have e3E : c₃.nreg fE = v % (chainModel J.right).W.n := by
    simp_all [regI, fE, fA, sw] <;> omega_nf
  have e3A : c₃.nreg fA = side := by simp_all [regI] <;> omega_nf
  have hA2 : c₂.nreg ALLOC = c.nreg ALLOC := by
    simp_all [ALLOC, fE, sw, zT] <;> omega_nf
  have hA3 : c₃.nreg ALLOC = c.nreg ALLOC := by
    simp_all [regI, ALLOC, fA, sw] <;> omega_nf
  refine (face_irs E hI₃ (by rw [e3E]; exact Nat.mod_lt _ (by  omega))
    (by omega) (by
      grind)).mono le_rfl ?_
  rintro c₄ ⟨r4, hb4, ha4, m4, A4, k4⟩
  rw [e3A, e3E] at hb4 ha4
  refine ⟨r4, hb4, ha4, fun r hr hfp hra => ?_, by omega, fun a ha => ?_⟩
  · rw [k4 r hr (fun h => hfp (Or.inl h)) hra]
    rw [hc₃]
    simp only [regI]
    rw [upd_other _ _ _ (fun h => hfp (Or.inr (Or.inr (Or.inr h)))),
      f2 r (fun h => hfp (Or.inr (Or.inr (Or.inl h))))]
    exact hl r (fun h => hfp (Or.inr (Or.inl h)))
  · ram_simp

end

end SweepEv

end Chazelle.Core
