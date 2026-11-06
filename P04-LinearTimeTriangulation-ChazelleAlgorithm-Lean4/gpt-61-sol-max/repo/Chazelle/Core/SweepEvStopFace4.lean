module

public meta import Chazelle.Arithmetic

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

/-- One side. -/
def frSide (pe ph dst ye yh src : ℕ) : Stmt := .seq (frLoc pe ph) (frTail pe ph dst ye yh src)

/-- **The procedure of task F.** -/
def frProg : Stmt :=
  .seq (frSide fpE fpH frA fEE fEH lR2) (frSide fqE fqH frB fSE fSH lR0)

variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

/-- The frame of one side. -/
def FrSideFr (dst : ℕ) (c c' : Config) : Prop :=
  (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
    (∀ r, bandOf r ∉ oracleBands → r ≠ dst → (r < sw 1100 ∨ sw 1207 < r) → r ≠ ALLOC →
      c'.nreg r = c.nreg r)

section
variable {r : ℕ} (h : r < sw 1100 ∨ sw 1207 < r)
include h
theorem fr_rA : r < sw 1200 ∨ sw 1207 < r := by
  omega_nf



end

theorem fr_rD {r : ℕ} (h : ¬ (sw 700 ≤ r ∧ r < sw 2200)) : r < sw 1100 ∨ sw 1207 < r := by
  omega_nf

theorem fr_rC {q : ℕ} (h : sw 4110 ≤ q ∧ q ≤ sw 4113) :
    bandOf q ∉ oracleBands ∧ q ≠ frA ∧ (q < sw 1100 ∨ sw 1207 < q) ∧ q ≠ ALLOC := by
  unfold sw at h
  exact ⟨not_oracle_sw (by omega) (by omega), by omega_nf,
    Or.inr (by omega_nf), by omega_nf⟩

theorem fr_le1 {a K W : ℕ} (h : a + (K + 22100) ≤ W) : a + K ≤ W :=
  le_trans (Nat.add_le_add_left (Nat.le_add_right _ _) a) h


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
  · have hn : nhgt (chainModel C) (Qof P) x = 0 := (nhgt_zero_iff x).2 h0
    have he : x.edge < 6 := by
      omega
    rw [fr_key, h0, add_zero]
    exact frc_box_noncut hP hN he
  · exact h

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **Side A**: the region faced just after `(fpE, fpH)`. -/
theorem frSideA_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hfe : c.nreg fpE < (chainModel J.right).W.n)
    (hpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg fpE, c.nreg fpH⟩)
    (hpre : (chainModel J.right).param (Qof P) ⟨c.nreg fpE, c.nreg fpH⟩ = 0 ∨
      ¬ (chainModel J.right).IsCut (N₂.F (chainModel J.right) (Qof P))
        ((chainModel J.right).key (Qof P) ⟨c.nreg fpE, c.nreg fpH⟩))
    (hroom : c.nreg ALLOC + (faceLocK (c₀.nreg TLR) + 22100) ≤ W) :
    IRS P W c₀ (frSide fpE fpH frA fEE fEH lR2) c (faceLocK (c₀.nreg TLR) + 22100) (fun c' =>
      c'.nreg frA < N₂.nRegions ∧
      AfterFaces (chainModel J.right) (c.nreg fpE)
        ((chainModel J.right).param (Qof P) ⟨c.nreg fpE, c.nreg fpH⟩)
        (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg frA)) ∧ FrSideFr frA c c') := by
  have hP₂ : J.right.P.Simple := E.hP
  have hNF := E.hNF₂
  unfold frSide
  refine IRS.seq (frLoc_irs E hI (pe := fpE) (ph := fpH)
    ⟨by omega_nf, by omega_nf, by omega_nf, by omega_nf⟩ hfe hpp
    (fr_le1 hroom)) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨j, hj, hl1, hl2, r0, r1, r2, vSE, vSH, vEE, vEH, hm1, hAl1, hk1⟩
  have hsj := NFLoc.seq_lt hNF hj
  obtain ⟨-, ⟨ppe, hee, hey⟩⟩ := arc_end_facts hP₂ hNF hsj
  have k1e : c₁.nreg fpE = c.nreg fpE := hk1 _ (not_oracle_sw (by omega_nf)
    (by omega_nf)) (Or.inr (by omega_nf))
  have k1h : c₁.nreg fpH = c.nreg fpH := hk1 _ (not_oracle_sw (by omega_nf)
    (by omega_nf)) (Or.inr (by omega_nf))
  refine (frTail_irs E hI₁ (pe := fpE) (ph := fpH) (dst := frA) (ye := fEE) (yh := fEH) (src := lR2)
    ⟨by omega_nf, by omega_nf⟩ ⟨by omega_nf, by omega_nf⟩
    (Or.inl rfl) ⟨by omega_nf, by omega_nf⟩
    ⟨by omega_nf, by omega_nf⟩ (by omega_nf) (Or.inr rfl)
    vEE vEH ppe hee hey (by omega) (by grind)
    (by grind)).mono le_rfl ?_
  rintro c₂ ⟨vd, fr2, hA2, hm2⟩
  rw [k1e, k1h, r1, r2] at vd
  set x : WPos := ⟨c.nreg fpE, c.nreg fpH⟩ with hx
  have ht0 := hpp.1
  have ht1 := hpp.2.1
  have hR : ∀ p, p < N₂.arcs.length → (N₂.arc (sj N₂ p)).reg < N₂.nRegions := fun p hp =>
    (arc_regOf hNF hp).1
  refine ⟨?_, ?_, fun a ha => ?_, hAl1 ▸ hA2, fun r h1 h2 h3 h4 => ?_⟩
  · rw [vd]; split_ifs
    · exact hR _ (OracleQ.succP_lt hj)
    grind
  · by_cases hv : 6 ≤ x.edge ∧ nhgt (chainModel J.right) (Qof P) x = 0
    · have ht : (chainModel J.right).param (Qof P) x = 0 := (nhgt_zero_iff x).1 hv.2
      have hk : (chainModel J.right).key (Qof P) x = (c.nreg fpE : ℝ) := by
        grind [fr_key, add_zero]
      rw [hk] at hl1 hl2
      rw [ht]
      by_cases hY : (N₂.arc (sj N₂ j)).e.edge = c.nreg fpE ∧
          nhgt (chainModel J.right) (Qof P) (N₂.arc (sj N₂ j)).e = 0
      · rw [vd, ite_eq_left ⟨hv.1, hv.2, hY⟩]
        exact face_after_eq hP₂ hNF hfe hj ((key_eq_nat_iff ppe _).2 hY)
      · rw [vd, ite_eq_right (fun h => hY h.2.2)]
        exact face_after_ne hP₂ hNF hfe hj hl1 hl2 (fun h => hY ((key_eq_nat_iff ppe _).1 h))
    · have hc := fr_noncut hP₂ hNF hpre hv
      rw [vd, ite_eq_right (fun h => hv ⟨h.1, h.2.1⟩)]
      exact frc_after hNF hj hfe ht0 ht1 (hl1 hc)
  · grind
  · rw [fr2 r h1 h2 (fr_rA h3) h4]
    ram_grind

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **Side B**: the region faced just before `(fqE, fqH)`. -/
theorem frSideB_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hfe : c.nreg fqE < (chainModel J.right).W.n)
    (hpp : ProperPos (chainModel J.right) (Qof P) P.n ⟨c.nreg fqE, c.nreg fqH⟩)
    (hpre : (chainModel J.right).param (Qof P) ⟨c.nreg fqE, c.nreg fqH⟩ = 0 ∨
      ¬ (chainModel J.right).IsCut (N₂.F (chainModel J.right) (Qof P))
        ((chainModel J.right).key (Qof P) ⟨c.nreg fqE, c.nreg fqH⟩))
    (hroom : c.nreg ALLOC + (faceLocK (c₀.nreg TLR) + 22100) ≤ W) :
    IRS P W c₀ (frSide fqE fqH frB fSE fSH lR0) c (faceLocK (c₀.nreg TLR) + 22100) (fun c' =>
      c'.nreg frB < N₂.nRegions ∧
      BeforeFaces (chainModel J.right) (c.nreg fqE)
        ((chainModel J.right).param (Qof P) ⟨c.nreg fqE, c.nreg fqH⟩)
        (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg frB)) ∧ FrSideFr frB c c') := by
  have hP₂ : J.right.P.Simple := E.hP
  have hNF := E.hNF₂
  unfold frSide
  refine IRS.seq (frLoc_irs E hI (pe := fqE) (ph := fqH)
    ⟨by omega_nf, by omega_nf, by omega_nf, by omega_nf⟩ hfe hpp
    (fr_le1 hroom)) ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨j, hj, hl1, hl2, r0, r1, r2, vSE, vSH, vEE, vEH, hm1, hAl1, hk1⟩
  have hsj := NFLoc.seq_lt hNF hj
  obtain ⟨⟨pps, hse, hsy⟩, -⟩ := arc_end_facts hP₂ hNF hsj
  have k1e : c₁.nreg fqE = c.nreg fqE := hk1 _ (not_oracle_sw (by omega_nf)
    (by omega_nf)) (Or.inr (by omega_nf))
  have k1h : c₁.nreg fqH = c.nreg fqH := hk1 _ (not_oracle_sw (by omega_nf)
    (by omega_nf)) (Or.inr (by omega_nf))
  refine (frTail_irs E hI₁ (pe := fqE) (ph := fqH) (dst := frB) (ye := fSE) (yh := fSH) (src := lR0)
    ⟨by omega_nf, by omega_nf⟩ ⟨by omega_nf, by omega_nf⟩
    (Or.inr rfl) ⟨by omega_nf, by omega_nf⟩
    ⟨by omega_nf, by omega_nf⟩ (by omega_nf) (Or.inl rfl)
    vSE vSH pps hse hsy (by omega) (by grind)
    (by grind)).mono le_rfl ?_
  rintro c₂ ⟨vd, fr2, hA2, hm2⟩
  rw [k1e, k1h, r1, r0] at vd
  set x : WPos := ⟨c.nreg fqE, c.nreg fqH⟩ with hx
  have ht0 := hpp.1
  have ht1 := hpp.2.1
  have hR : ∀ p, p < N₂.arcs.length → (N₂.arc (sj N₂ p)).reg < N₂.nRegions := fun p hp =>
    (arc_regOf hNF hp).1
  refine ⟨?_, ?_, fun a ha => ?_, hAl1 ▸ hA2, fun r h1 h2 h3 h4 => ?_⟩
  · rw [vd]; split_ifs
    · exact hR _ (OracleQ.predP_lt hj)
    grind
  · by_cases hv : 6 ≤ x.edge ∧ nhgt (chainModel J.right) (Qof P) x = 0
    · have ht : (chainModel J.right).param (Qof P) x = 0 := (nhgt_zero_iff x).1 hv.2
      have hk : (chainModel J.right).key (Qof P) x = (c.nreg fqE : ℝ) := by
        grind [fr_key, add_zero]
      rw [hk] at hl1 hl2
      rw [ht]
      by_cases hY : (N₂.arc (sj N₂ j)).s.edge = c.nreg fqE ∧
          nhgt (chainModel J.right) (Qof P) (N₂.arc (sj N₂ j)).s = 0
      · rw [vd, ite_eq_left ⟨hv.1, hv.2, hY⟩]
        exact face_before_eq hP₂ hNF hfe hj ((key_eq_nat_iff pps _).2 hY)
      · rw [vd, ite_eq_right (fun h => hY h.2.2)]
        exact face_before_ne hP₂ hNF hfe hj hl1 hl2 (fun h => hY ((key_eq_nat_iff pps _).1 h))
    · have hc := fr_noncut hP₂ hNF hpre hv
      rw [vd, ite_eq_right (fun h => hv ⟨h.1, h.2.1⟩)]
      exact frc_before hNF hj hfe ht0 ht1 (hl1 hc)
  · grind
  · rw [fr2 r h1 h2 (fr_rA h3) h4]
    ram_grind

set_option maxRecDepth 20000 in
theorem fr_cost (L : ℕ) : (faceLocK L + 22100) + (faceLocK L + 22100) ≤ 60000 * (L + 1) := by
  omega_nf

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
  refine IRS.mono (IRS.seq (frSideA_irs E hI hpe hppp hprep
      (le_trans (Nat.le_add_right _ _) hr)) ?_) (fr_cost _)
    (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨vA, hAf, hm1, hAl1, hk1⟩
  have keep : ∀ q, (sw 4110 ≤ q ∧ q ≤ sw 4113) → c₁.nreg q = c.nreg q := fun q hq => by
    obtain ⟨a, b, d, e⟩ := fr_rC hq
    grind
  have e1 := keep fqE ⟨by omega_nf, by omega_nf⟩
  have e2 := keep fqH ⟨by omega_nf, by omega_nf⟩
  refine (frSideB_irs E hI₁ (by omega) (by grind)
    (by grind) (le_trans (Nat.add_le_add_right hA₁' _) hr)).mono
    le_rfl ?_
  rintro c₂ ⟨vB, hBf, hm2, hAl2, hk2⟩
  rw [e1, e2] at hBf
  have hAA : c₂.nreg frA = c₁.nreg frA := hk2 _ (not_oracle_sw (by omega_nf)
    (by omega_nf)) (by omega_nf)
    (Or.inr (by omega_nf)) (by omega_nf)
  refine ⟨by omega, vB, by grind, hBf, fun a ha => ?_,
    le_trans hAl1 hAl2, fun r h1 h2 h3 => ?_⟩
  · grind
  · have hFR : ¬ (sw 700 ≤ r ∧ r < sw 2200) := fun h => h2 (Or.inl h)
    have hrA : r ≠ frA := fun h => h2 (Or.inr (Or.inl h))
    have hrB : r ≠ frB := fun h => h2 (Or.inr (Or.inr (Or.inl h)))
    rw [hk2 r h1 hrB (fr_rD hFR) h3, hk1 r h1 hrA (fr_rD hFR) h3]

end

end SweepEv

end Chazelle.Core
