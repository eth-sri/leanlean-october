module

public import Chazelle.Core.SweepEvStopM1C3

/-!
# The sweep (WP-D), stage 2: the candidate of `C₁` of a stop origin, the top code
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

theorem efr_regs {S Z : ℕ → Prop} {c c' : Config} (hS : ∀ r, S r → Z r)
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ S r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (ha : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    EFr Z c c' :=
  ⟨fun r a b d => h r a (fun x => b (hS r x)) d, ha, hm⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The top code.** -/
theorem m1cK2_irs {br : Stmt → Stmt} {κB : ℕ} (hBr : StbBody br κB)
    (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hD : OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
    (hk : c.nreg oKd = 2) {K : ℕ}
    (hK : 16970 + κB * (N₁.nChords + 1) * (F (c₀.nreg (sw 5)) + 1) ≤ K)
    (hroom : c.nreg ALLOC + K ≤ W) :
    IRS P W c₀ (m1cK2 br sh) c K (M1Post P J N₂ c) := by
  have hb : c.nreg oB ≤ 1 := hD.ok.2.1
  have hok : StOK P J N₂ 2 (c.nreg oKk) (c.nreg oB) := hk ▸ hD.ok
  have htop0 : J.right.topIdx ≠ 0 := hok.2.2.2 rfl
  have hK0 := E.hK.fix hI
  have htopR : J.right.top ∈ J.right.set := J.right.top_mem_set
  have hpos6 : (chainModel J.right).pos (Qof P) ⟨6, 0⟩ = J.right.top := SweepStop.right_top_pos _
  have hW3 : P.n + 3 ≤ W := by have := E.hWh; unfold hostWords at this; omega
  have hm2 := J.right.one_le
  obtain ⟨KB, hKBd⟩ : ∃ KB, KB = κB * (N₁.nChords + 1) * (F (c₀.nreg (sw 5)) + 1) :=
    ⟨_, rfl⟩
  rw [← hKBd] at hK
  unfold m1cK2 M1Post
  rw [hk, stOrig_two]
  refine (IRS.seq (K₁ := 16707) (K₂ := 251 + (KB + 12))
    (SweepIo.callSym_irs (P := P) (dsc := sw 21) (re := K6) (rh := K0) (o := m1s) (C := J.right) hI
      (E.ctx2' hI) (by unfold K6 K0 sw; omega) (by unfold m1s sw; omega)
      (by rw [hK0.2.2.1, cm_n]; omega)
      (by rw [hK0.2.2.1, hK0.1]; exact ⟨le_refl _, by
          rw [show (chainModel J.right).param (Qof P) ⟨6, 0⟩ = 0 from rfl]; norm_num,
        Nat.zero_le _⟩)
      (by rw [hK0.2.2.1, hK0.1, hpos6]; exact absy_lt J.right htopR)
      (Or.inl ⟨by rw [hK0.2.2.1], by rw [hK0.2.2.1]; omega⟩) (by omega)) ?_).mono
    (show 16707 + (251 + (KB + 12)) ≤ K by omega) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨sp, hsp, hlt, hev, hfr1, hal1, hm1⟩
  rw [hK0.2.2.1, hK0.1, hpos6] at hev
  have fr1 : EFr M1R c c₁ := efr_regs (S := fun r => m1s ≤ r ∧ r ≤ m1s + 3)
    (fun r h => by unfold m1s at h; unfold M1R; unfold sw at h ⊢; omega)
    (fun r a b d => hfr1 r a (by omega) d) hal1 hm1
  obtain ⟨t1, ht1, ht1l, ht1e⟩ := (E.hO.fix hI₁).t1
  have hsp' : SymPtIn c₁ brOS sp := hsp
  refine IRS.seq (K₁ := 251) (K₂ := KB + 12)
    (callKb_irs (a := cT1) (b := brOS) (op := 1) (o := m1o) (by norm_num) hI₁ E.hG hW3
      (by unfold cT1 sw; omega) (by unfold brOS sw; omega) (by unfold m1o sw; omega) ht1 hsp'
      ht1l hlt (by omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hf2, hiff2, hfr2, hal2, hm2'⟩
  rw [ht1e, hev] at hiff2
  have fr2 : EFr M1R c₁ c₂ := efr_regs (S := fun r => r = m1o)
    (fun r h => by rw [h]; unfold m1o M1R sw; omega) (fun r a b d => hfr2 r a b d) hal2 hm2'
  have hK2 := E.hK.fix hI₂
  have kB : ∀ r, 240000 ≤ r → r < 250000 → r ≠ m1o → (r < m1s ∨ m1s + 3 < r) → r ≠ ALLOC →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 =>
    (hfr2 r (not_oracle_sw h1 h2) h3 h5).trans (hfr1 r (not_oracle_sw h1 h2) h4 h5)
  have eB : c₂.nreg oB = c.nreg oB := kB _ (by unfold oB sw; omega) (by unfold oB sw; omega)
    (by unfold oB m1o sw; omega) (by unfold oB m1s sw; omega) (by unfold oB ALLOC sw; omega)
  refine (IRS.ite (K := KB + 10) (fun h1 => ?_) (fun h1 => ?_)).mono
    (show KB + 10 + 2 ≤ KB + 12 by omega) (fun _ h => h)
  · -- above the top of `C₁`: no result
    rw [hK2.1] at h1
    have hab : J.left.top.2 < J.right.top.2 := (hiff2.1 (by omega))
    have hng : ¬ (FreeAt J.left J.right.top (dirOf (c.nreg oB)) ∧
        J.right.top.2 ≤ J.left.top.2) := fun g => by linarith [g.2]
    refine (m1c_noRes (C := J.left) (a := J.right.top) (σ := dirOf (c.nreg oB)) hI₂ hng).mono
      (by omega) ?_
    rintro c' ⟨hres, hk', hm'⟩
    exact ⟨hres, m1c_efr (m1c_efr fr1 fr2 (fun r h => h) (fun r h => h)) (efr_noRes hk' hm')
      (fun r h => h) (fun r h => h)⟩
  · rw [hK2.1] at h1
    have hle : J.right.top.2 ≤ J.left.top.2 := by
      by_contra hc
      have := hiff2.2 (by push Not at hc; exact hc)
      omega
    -- the direction
    have hokB : okB W c₂.nmem [Instr.copyN brOD oB] c₂.nreg :=
      ⟨iscr_sw (by unfold brOD sw; omega) (by unfold brOD sw; omega), trivial⟩
    refine (IRS.seq (K₁ := 1) (K₂ := KB + 7)
      ((IRS.block [Instr.copyN brOD oB] hI₂ hokB).mono (by simp) (fun _ h => h)) ?_).mono
      (show 1 + (KB + 7) ≤ KB + 10 by omega) (fun _ h => h)
    rintro c₃ hI₃ hA₃ hA₃' hc3
    have v3 : c₃.nreg brOD = c.nreg oB := by
      rw [hc3]; simp only [regB, regI, upd_same]; exact eB
    have vo3 : ∀ q, q ≠ brOD → c₃.nreg q = c₂.nreg q :=
      fun q hq => by rw [hc3]; simp only [regB, regI]; exact upd_other _ _ _ hq
    have hm3 : c₃.nmem = c₂.nmem := by rw [hc3]
    have hA3eq : c₃.nreg ALLOC = c₂.nreg ALLOC := vo3 _ (by unfold brOD ALLOC sw; omega)
    have fr3 : EFr M1R c₂ c₃ :=
      efr_regs (S := fun r => r = brOD) (fun r h => by rw [h]; unfold brOD M1R sw; omega)
        (fun r _ b _ => vo3 r b) (by rw [hA3eq]) (fun _ _ => by rw [hm3])
    -- the symbolic point is still at `brOS`
    have kS : ∀ i, i < 3 → c₃.nreg (brOS + i) = c₁.nreg (brOS + i) := fun i hi => by
      rw [vo3 _ (by unfold brOS brOD sw; omega)]
      exact hfr2 _ (not_oracle_sw (by unfold brOS sw; omega) (by unfold brOS sw; omega))
        (by unfold brOS m1o sw; omega) (by unfold brOS ALLOC sw; omega)
    have hsp3 : SymPtIn c₃ brOS sp :=
      symPtIn_copy hsp' (kS 0 (by norm_num)) (kS 1 (by norm_num)) (kS 2 (by norm_num))
    have hab := Cand1.abs_lt_whole (J := J) htopR
    have hbr := hBr sh Bs F X Ok P W c₀ c₃ J N₁ N₂ E hI₃ sp hsp3 hlt
      (by rw [hev]; exact top_not_left E.hP htop0) (by rw [hev]; exact hab.1)
      (by rw [hev]; exact hab.2) (by rwa [hev])
      (by rwa [v3])
      (by rw [hA3eq]; omega)
    rw [← hKBd] at hbr
    refine IRS.seq (K₁ := KB) (K₂ := 7) hbr ?_
    rintro c₄ hI₄ hA₄ hA₄' ⟨g1, gs, gf, gm, ga, gr⟩
    have e4 : dirOf (c₃.nreg brOD) = dirOf (c.nreg oB) := by rw [v3]
    rw [e4, hev] at gs gf
    have fr4 : EFr M1R c₃ c₄ :=
      efr_regs (S := BrR) (fun r h => by unfold BrR at h; unfold M1R; unfold sw at h ⊢; omega)
        gr ga gm
    obtain ⟨cv, co⟩ := m1cCp_val c₄.nmem c₄.nreg
    refine (IRS.block m1cCp hI₄ (m1cCp_ok _ _)).mono (by simp [m1cCp]) ?_
    rintro c' rfl
    have fr5 : EFr M1R c₄ { c₄ with nreg := regB c₄.nmem m1cCp c₄.nreg } :=
      efr_regs (S := fun r => r1F ≤ r ∧ r ≤ r1F + 6)
        (fun r h => by unfold r1F at h; unfold M1R; unfold sw at h ⊢; omega)
        (fun r _ b _ => co r (by omega))
        (by rw [show ({ c₄ with nreg := regB c₄.nmem m1cCp c₄.nreg } : Config).nreg ALLOC =
          c₄.nreg ALLOC from co ALLOC (by unfold r1F ALLOC sw; omega)]) (fun _ _ => rfl)
    have c0 : ({ c₄ with nreg := regB c₄.nmem m1cCp c₄.nreg } : Config).nreg r1F =
        c₄.nreg brF := by have := cv 0 (by norm_num); simpa using this
    refine ⟨⟨by rwa [c0], fun h1 => ?_, fun g => by rw [c0]; exact gf g.1⟩,
      m1c_efr (m1c_efr (m1c_efr fr1 fr2 (fun r h => h) (fun r h => h)) (m1c_efr fr3 fr4
        (fun r h => h) (fun r h => h)) (fun r h => h) (fun r h => h)) fr5 (fun r h => h)
        (fun r h => h)⟩
    rw [c0] at h1
    obtain ⟨τ, a1, a2, a3, a4, a5, a6, a7⟩ := gs h1
    have c1 : ({ c₄ with nreg := regB c₄.nmem m1cCp c₄.nreg } : Config).nreg (r1F + 1) =
        c₄.nreg (brF + 1) := cv 1 (by norm_num)
    have c2 : ({ c₄ with nreg := regB c₄.nmem m1cCp c₄.nreg } : Config).nreg (r1F + 2) =
        c₄.nreg (brF + 2) := cv 2 (by norm_num)
    refine ⟨τ, a1, a2, by rwa [c1], by rwa [c1, c2], by rwa [c1, c2],
      absRec_transport a6 (cv 3 (by norm_num)) (cv 4 (by norm_num)) (cv 5 (by norm_num))
        (cv 6 (by norm_num)), fun g => a7 g.1⟩

end

end SweepEv

end Chazelle.Core
