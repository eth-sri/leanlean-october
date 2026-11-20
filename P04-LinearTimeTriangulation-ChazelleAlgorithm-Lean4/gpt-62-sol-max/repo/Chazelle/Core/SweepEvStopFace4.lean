module

public import Chazelle.Core.SweepEvStopFace3

/-!
# The sweep (WP-D), stage 2: the regions faced at a position of the walk of `C₂` (task F)

`frProg`: side A (`frA`, the region faced just after `(fpE, fpH)`) and side B (`frB`, the region
faced just before `(fqE, fqH)`), each `frLoc` + `frTail`.  **`faceRTask : FaceRTask`**, cost
`60000 (TLR + 1)`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (sideInArc)
open OracleQ (sj sk ek succP predP)

@[expose] public section

/-- Register slots for the face after (`true`) or before (`false`) a position. -/
structure FrSlots where
  pe : ℕ
  ph : ℕ
  dst : ℕ
  ye : ℕ
  yh : ℕ
  src : ℕ

def frSlots : Bool → FrSlots
  | true => ⟨fpE, fpH, frA, fEE, fEH, lR2⟩
  | false => ⟨fqE, fqH, frB, fSE, fSH, lR0⟩

def frSide (after : Bool) : Stmt :=
  let l := frSlots after
  .seq (frLoc l.pe l.ph) (frTail l.pe l.ph l.dst l.ye l.yh l.src)

def frProg : Stmt := .seq (frSide true) (frSide false)

variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

/-- The frame of one side. -/
def FrSideFr (dst : ℕ) (c c' : Config) : Prop :=
  (MemEqBelow (c.nreg ALLOC) c'.nmem c.nmem) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
    (∀ r, bandOf r ∉ oracleBands → r ≠ dst → (r < sw 1100 ∨ sw 1207 < r) → r ≠ ALLOC →
      c'.nreg r = c.nreg r)

theorem fr_rA {r : ℕ} (h : r < sw 1100 ∨ sw 1207 < r) : r < sw 1200 ∨ sw 1207 < r := by
  reg_omega

theorem fr_rB {r : ℕ} (h : r < sw 1100 ∨ sw 1207 < r) : r < sw 1102 ∨ sw 1203 < r := by
  reg_omega

theorem fr_rD {r : ℕ} (h : ¬ (sw 700 ≤ r ∧ r < sw 2200)) : r < sw 1100 ∨ sw 1207 < r := by
  reg_omega

theorem fr_rC {q : ℕ} (h : sw 4110 ≤ q ∧ q ≤ sw 4113) :
    bandOf q ∉ oracleBands ∧ q ≠ frA ∧ (q < sw 1100 ∨ sw 1207 < q) ∧ q ≠ ALLOC := by
  unfold sw at h
  exact ⟨not_oracle_sw (by omega) (by omega), by reg_omega,
    (by reg_omega), by unfold ALLOC; omega⟩

theorem fr_le1 {a K W : ℕ} (h : a + (K + 22100) ≤ W) : a + K ≤ W :=
  le_trans (Nat.add_le_add_left (Nat.le_add_right _ _) a) h

theorem fr_le2 {a K W : ℕ} (h : a + (K + 22100) ≤ W) : a + 22100 ≤ W :=
  le_trans (Nat.add_le_add_left (Nat.le_add_left _ _) a) h

/-- The key of a position is its edge plus its parameter. -/
theorem fr_key (M : Model) (Q : Polygon) (x : WPos) : M.key Q x = (x.edge : ℝ) + M.param Q x :=
  rfl

/-- **Non-cut**: a position that is a vertex on the box, or not a vertex, is not a cut. -/
theorem fr_noncut {C : Chain} {N : NF} (hP : C.P.Simple)
    (hN : IsNF (chainModel C) (Qof P) N) {x : WPos}
    (hpre : (chainModel C).param (Qof P) x = 0 ∨
      ¬ (chainModel C).IsCut (N.F (chainModel C) (Qof P)) ((chainModel C).key (Qof P) x))
    (hv : ¬ (6 ≤ x.edge ∧ nhgt (chainModel C) (Qof P) x = 0)) :
    ¬ (chainModel C).IsCut (N.F (chainModel C) (Qof P)) ((chainModel C).key (Qof P) x) := by
  rcases hpre with h0 | h
  · have hn := (nhgt_zero_iff x).2 h0
    have he : x.edge < 6 := by
      simp_all <;> omega
    rw [fr_key, h0, add_zero]
    exact frc_box_noncut hP hN he
  · exact h

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- Read the arc and choose its region or the neighboring region on the requested side. -/
theorem frSide_irs (after : Bool) (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hfe : c.nreg (frSlots after).pe < J.rightModel.W.n)
    (hpp : ProperPos J.rightModel (Qof P) P.n
      ⟨c.nreg (frSlots after).pe, c.nreg (frSlots after).ph⟩)
    (hpre : J.rightModel.param (Qof P) ⟨c.nreg (frSlots after).pe, c.nreg (frSlots after).ph⟩ = 0 ∨
      ¬ J.rightModel.IsCut (N₂.F J.rightModel (Qof P))
        (J.rightModel.key (Qof P) ⟨c.nreg (frSlots after).pe, c.nreg (frSlots after).ph⟩))
    (hroom : c.nreg ALLOC + (faceLocK (c₀.nreg TLR) + 22100) ≤ W) :
    IRS P W c₀ (frSide after) c (faceLocK (c₀.nreg TLR) + 22100) (fun c' =>
      let l := frSlots after
      c'.nreg l.dst < N₂.nRegions ∧
      (if after then AfterFaces else BeforeFaces) J.rightModel (c.nreg l.pe)
        (J.rightModel.param (Qof P) ⟨c.nreg l.pe, c.nreg l.ph⟩)
        (regOf J.rightModel (Qof P) N₂ (c'.nreg l.dst)) ∧ FrSideFr l.dst c c') := by
  let l := frSlots after
  have hP₂ := E.hP
  have hNF := E.hNF₂
  have hpr : ∀ r, (r = l.pe ∨ r = l.ph) → sw 4110 ≤ r ∧ r ≤ sw 4113 := by
    rintro r (rfl | rfl) <;> cases after <;> decide
  have hkeep : ∀ r, (r = l.pe ∨ r = l.ph) →
      bandOf r ∉ oracleBands ∧ (r < sw 1102 ∨ sw 1203 < r) := by
    rintro r (rfl | rfl) <;> cases after <;> decide
  have hband : 240000 ≤ l.pe ∧ l.pe < 250000 ∧ 240000 ≤ l.ph ∧ l.ph < 250000 := by
    cases after <;> decide
  unfold frSide
  refine IRS.seq (frLoc_irs E hI hband hfe hpp (fr_le1 hroom)) ?_
  rintro c₁ hI₁ - - ⟨j, hj, hl1, hl2, r0, r1, r2, vSE, vSH, vEE, vEH, hm1, hAl1, hk1⟩
  obtain ⟨⟨pps, hse, hsy⟩, ⟨ppe, hee, hey⟩⟩ := arc_end_facts hP₂ hNF (NFLoc.seq_lt hNF hj)
  let Y := if after then (N₂.arc (sj N₂ j)).e else (N₂.arc (sj N₂ j)).s
  have vye : c₁.nreg l.ye = Y.edge := by cases after <;> assumption
  have vyh : c₁.nreg l.yh = Y.hgt := by cases after <;> assumption
  have ypp : ProperPos J.rightModel (Qof P) P.n Y := by cases after <;> assumption
  have hYe : Y.edge < J.rightModel.W.n := by cases after <;> assumption
  have hYy : Y.edge < 6 → Y.edge ≠ 0 → Y.edge ≠ 2 → Y.edge ≠ 4 →
      |(J.rightModel.pos (Qof P) Y).2| < J.right.radius := by cases after <;> assumption
  have k1e := hk1 l.pe (hkeep _ (Or.inl rfl)).1 (hkeep _ (Or.inl rfl)).2
  have k1h := hk1 l.ph (hkeep _ (Or.inr rfl)).1 (hkeep _ (Or.inr rfl)).2
  refine (frTail_irs E hI₁ (dst := l.dst) (src := l.src)
    (hpr _ (Or.inl rfl)) (hpr _ (Or.inr rfl))
    (by cases after <;> decide) (by cases after <;> decide) (by cases after <;> decide)
    (by cases after <;> decide) (by cases after <;> decide)
    vye vyh ypp hYe hYy (by rwa [k1e]) (by rwa [k1e, k1h])
    (by rw [hAl1]; exact fr_le2 hroom)).mono le_rfl ?_
  rintro c₂ ⟨vd, fr2, hA2, hm2⟩
  let j' := if after then succP N₂.arcs.length j else predP N₂.arcs.length j
  have hj' : j' < N₂.arcs.length := by
    cases after
    · exact OracleQ.predP_lt hj
    · exact OracleQ.succP_lt hj
  have r' : c₁.nreg l.src = (N₂.arc (sj N₂ j')).reg := by cases after <;> assumption
  rw [k1e, k1h, r1, r'] at vd
  set x : WPos := ⟨c.nreg l.pe, c.nreg l.ph⟩
  let cut : Prop := 6 ≤ x.edge ∧ nhgt J.rightModel (Qof P) x = 0 ∧
    Y.edge = x.edge ∧ nhgt J.rightModel (Qof P) Y = 0
  have vd' : c₂.nreg l.dst = ite cut (N₂.arc (sj N₂ j')).reg (N₂.arc (sj N₂ j)).reg := vd
  refine ⟨?_, ?_, fun a ha => ?_, hAl1 ▸ hA2, fun r h1 h2 h3 h4 => ?_⟩
  · rw [vd']; split_ifs
    · exact (arc_regOf hNF hj').1
    · exact (arc_regOf hNF hj).1
  · by_cases hv : 6 ≤ x.edge ∧ nhgt J.rightModel (Qof P) x = 0
    · have ht := (nhgt_zero_iff x).1 hv.2
      have hk : J.rightModel.key (Qof P) x = (x.edge : ℝ) := by rw [fr_key, ht, add_zero]
      rw [ht]
      rw [hk] at hl1 hl2
      by_cases hY : Y.edge = x.edge ∧ nhgt J.rightModel (Qof P) Y = 0
      · have hcut : cut := ⟨hv.1, hv.2, hY⟩
        rw [vd', ite_eq_left hcut]
        have hkey := (key_eq_nat_iff ypp x.edge).2 hY
        cases after
        · exact face_before_eq hP₂ hNF hfe hj hkey
        · exact face_after_eq hP₂ hNF hfe hj hkey
      · have hcut : ¬cut := fun h => hY h.2.2
        rw [vd', ite_eq_right hcut]
        have hkey : J.rightModel.key (Qof P) Y ≠ (x.edge : ℝ) := fun h =>
          hY ((key_eq_nat_iff ypp x.edge).1 h)
        cases after
        · exact face_before_ne hP₂ hNF hfe hj hl1 hl2 hkey
        · exact face_after_ne hP₂ hNF hfe hj hl1 hl2 hkey
    · have hc := fr_noncut hP₂ hNF hpre hv
      have hcut : ¬cut := fun h => hv ⟨h.1, h.2.1⟩
      rw [vd', ite_eq_right hcut]
      cases after
      · exact frc_before hNF hj hfe hpp.1 hpp.2.1 (hl1 hc)
      · exact frc_after hNF hj hfe hpp.1 hpp.2.1 (hl1 hc)
  · rw [hm2 a (hAl1 ▸ ha), hm1]
  · rw [fr2 r h1 h2 (fr_rA h3) h4, hk1 r h1 (fr_rB h3)]

set_option maxRecDepth 20000 in
theorem fr_cost (L : ℕ) : (faceLocK L + 22100) + (faceLocK L + 22100) ≤ 60000 * (L + 1) := by
  unfold faceLocK
  have h1 : 5500 * (L + 1) + 9 + 60 + 22100 + (5500 * (L + 1) + 9 + 60 + 22100) =
      11000 * (L + 1) + 44338 := by ring
  rw [h1]
  have h2 : 60000 * (L + 1) = 11000 * (L + 1) + 49000 * (L + 1) := by ring
  rw [h2]
  have h3 : 49000 ≤ 49000 * (L + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos L)
  generalize 11000 * (L + 1) = A at *
  generalize 49000 * (L + 1) = B at *
  omega

set_option maxRecDepth 20000 in
theorem fr_room {a L W : ℕ} (h : a + 60000 * (L + 1) ≤ W) :
    a + (faceLocK L + 22100) + (faceLocK L + 22100) ≤ W := by
  rw [Nat.add_assoc]
  exact le_trans (Nat.add_le_add_left (fr_cost L) a) h

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **Task F: the regions of `N₂` faced at two positions of the walk of `C₂`.** -/
theorem faceRTask : FaceRTask := by
  refine ⟨frProg, fun _ => 60000, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hpe hppp hprep hqe hppq hpreq hroom
  replace hroom : c.nreg ALLOC + 60000 * (c₀.nreg TLR + 1) ≤ W := hroom
  have hr := fr_room hroom
  show IRS P W c₀ frProg c (60000 * (c₀.nreg TLR + 1)) (FaceROut P J N₂ c)
  unfold frProg
  refine IRS.mono (IRS.seq (frSide_irs true E hI hpe hppp hprep
      (le_trans (Nat.le_add_right _ _) hr)) ?_) (fr_cost _)
    (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨vA, hAf, hm1, hAl1, hk1⟩
  have keep := fun q hq => by
    obtain ⟨a, b, d, e⟩ := fr_rC hq
    exact hk1 q a b d e
  have e1 := keep fqE (by reg_omega)
  have e2 := keep fqH (by reg_omega)
  refine (frSide_irs false E hI₁ (by dsimp only [frSlots]; rwa [e1]) (by dsimp only [frSlots]; rwa [e1, e2])
    (by dsimp only [frSlots]; rwa [e1, e2]) (le_trans (Nat.add_le_add_right hA₁' _) hr)).mono
    le_rfl ?_
  rintro c₂ ⟨vB, hBf, hm2, hAl2, hk2⟩
  dsimp only [frSlots] at vA vB hAf hBf hk1 hk2
  rw [e1, e2] at hBf
  have hAA : c₂.nreg frA = c₁.nreg frA := hk2 _ (not_oracle_sw (by decide)
    (by decide)) (by decide)
    ((by reg_omega)) (by simp [ram_layout])
  refine ⟨by rwa [hAA], vB, by rwa [hAA], hBf, fun a ha => ?_,
    le_trans hAl1 hAl2, fun r h1 h2 h3 => ?_⟩
  · rw [hm2 a (lt_of_lt_of_le ha hAl1), hm1 a ha]
  · have hFR := fun h => h2 (Or.inl h)
    have hrA := fun h => h2 (Or.inr (Or.inl h))
    have hrB := fun h => h2 (Or.inr (Or.inr (Or.inl h)))
    rw [hk2 r h1 hrB (fr_rD hFR) h3, hk1 r h1 hrA (fr_rD hFR) h3]

end

end SweepEv

end Chazelle.Core
