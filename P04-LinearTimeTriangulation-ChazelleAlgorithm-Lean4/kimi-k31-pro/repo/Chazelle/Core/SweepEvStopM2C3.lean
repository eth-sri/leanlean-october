module

public import Chazelle.Core.SweepEvStopM2C2
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/-!
# The sweep (WP-D), stage 2: the candidate of `C₂` of a stop origin (task M2, part 3)

The two branches (`m2cS_irs`: shared and top codes; `m2cW_irs`: wall codes) and
**`m2Task : M2Task`** (`κ D = κGen D + 40000`).
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

theorem m2c_regs {r : ℕ} (h : r = m2F ∨ r = m2F + 1 ∨ r = m2F + 2 ∨ r = r2F) : M2R r := by
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl ⟨by simp [m2F, sw], by simp [m2F, sw]⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨by simp [m2F, sw], by simp [m2F, sw]⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨by simp [m2F, sw], by simp [m2F, sw]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [r2F, sw], by simp [r2F, sw]⟩)))

/-- **Shared and top codes.** -/
theorem m2cS_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hM : MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c)
    (hD : OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
    (hpos : OrgPos P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) (c.nreg oPE) (c.nreg oPH))
    (hk : c.nreg oKd ≠ 1)
    (hroom : c.nreg ALLOC + m2cK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) ≤ W) :
    IRS P W c₀ (m2cS sh) c (m2cK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)))
      (fun c' => M2Out P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c' ∧ EFr M2R c c') := by
  set a := stOrig J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) with ha
  have hok := hD.ok
  obtain ⟨-, ha2, hay, haR, -⟩ := stOrig_facts E.hP E.hNF₂ hok
  have haR' := haR hk
  have hb : c.nreg oB ≤ 1 := hok.2.1
  have hσ := SweepStop.dirOf_cases' (c.nreg oB)
  obtain ⟨hpe, hpp, -, hpt, -, -⟩ := hpos
  have hay' : |a.2| < J.right.radius := hay
  have noArr : FreeAt J.right a (dirOf (c.nreg oB)) → ∃ p t,
      Arrival (chainModel J.right).W a (-dirOf (c.nreg oB)) p t :=
    fun hf => arrival_of_freeC J.right E.hP hσ (Or.inl haR') hf
  unfold m2cS m2cK
  unfold m2cK at hroom
  -- 1. the arrival position
  refine IRS.seq (callArr_irs (dsc := sw 21) (re := oPE) (rh := oPH) (rd := oB) (o := m2F)
    (C := J.right) hI (E.ctx2' hI)
    ⟨by simp [sw], by simp [sw], by simp [oPE, sw], by simp [oPE, sw], by simp [oPH, sw],
      by simp [oPH, sw], by simp [oB, sw], by simp [oB, sw]⟩
    ⟨by simp [m2F, sw], by simp [m2F, sw]⟩ hpe hpp (by rwx [hpt]) (by omega)) ?_
  rintro c₁ hI₁ - hA₁' ⟨hArr, k1, hA1, hm1⟩
  have k1' : ∀ r, bandOf r ∉ oracleBands → ¬ M2R r → r ≠ ALLOC → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 => k1 r h1 (fun e => h2 (m2c_regs (Or.inl e)))
      (fun e => h2 (m2c_regs (Or.inr (Or.inl e)))) (fun e => h2 (m2c_regs (Or.inr (Or.inr
        (Or.inl e))))) h3
  have kq : ∀ q, (sw 4000 ≤ q ∧ q < sw 4024) ∨ (sw 0 ≤ q ∧ q < sw 700) → c₁.nreg q = c.nreg q :=
    fun q hq => k1' q (not_oracle_sw (by ufo sw at hq) (by ufo sw at hq))
      (by unfold M2R; ufo sw at hq ⊢) (by unfold ALLOC; ufo sw at hq)
  have eB : c₁.nreg oB = c.nreg oB := kq _ (Or.inl ⟨by simp [oB, sw], by simp [oB, sw]⟩)
  have hK1 : c₁.nreg K1 = 1 := (E.hK.fix hI₁).2.1
  have hM₁ : MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c₁ :=
    MCtx.transport hM (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact kq _ (Or.inl ⟨by simp [gMD2, sw], by simp [gMD2, sw]⟩)
      · exact kq _ (Or.inl ⟨by simp [gCD2, sw], by simp [gCD2, sw]⟩)
      · exact kq _ (Or.inr ⟨by simp [sw], by simp [sw]⟩)
      · exact kq _ (Or.inr ⟨by simp [TBR, sw], by simp [TBR, sw]⟩)
      · exact kq _ (Or.inr ⟨by simp [TLR, sw], by simp [TLR, sw]⟩)) hm1 hA1
  have efr1 : EFr M2R c c₁ := ⟨k1', hA1, hm1⟩
  obtain ⟨hf1, hf2, hf3⟩ := hArr
  rw [hpt] at hf2 hf3
  by_cases hfl : c₁.nreg m2F < c₁.nreg K1
  · -- no arrival: the empty result
    rw [hK1] at hfl
    have hne : c₁.nreg m2F ≠ 1 := by omega
    have hnf : ¬ FreeAt J.right a (dirOf (c.nreg oB)) := fun hf => by
      obtain ⟨p, t, hpt'⟩ := noArr hf
      exact hf3 hne p t hpt'
    refine (IRS.ifT (by rwx [hK1]) (IRS.reg (r := r2F) (v := 0) hI₁
      (iscr_sw (by simp [r2F, sw]) (by simp [r2F, sw]))
      (Exec.constN hI₁.hw r2F 0 (Nat.zero_le _)))).mono (by omega) ?_
    rintro c₂ rfl
    refine ⟨⟨⟨?_, fun h => ?_, fun hg => absurd hg hnf⟩, fun _ hg => absurd hg hnf⟩,
      EFr.trans efr1 ⟨fun r h1 h2 h3 => ?_, le_of_eq ?_, fun _ _ => rfl⟩⟩
    · simp [upd]
    · simp [upd] at h
    · show upd c₁.nreg r2F 0 r = c₁.nreg r
      rw [upd_other _ _ _ (fun e => h2 (m2c_regs (Or.inr (Or.inr (Or.inr e)))))]
    · show c₁.nreg ALLOC = upd c₁.nreg r2F 0 ALLOC
      rw [upd_other _ _ _ (by simp [r2F, ALLOC, sw])]
  · -- the local hit from the arrival
    rw [hK1] at hfl
    have h1 : c₁.nreg m2F = 1 := by omega
    obtain ⟨hpe2, hpp2, harr⟩ := hf2 h1
    set x : WPos := ⟨c₁.nreg pE2, c₁.nreg pH2⟩ with hx
    have hxa : (chainModel J.right).pos (Qof P) x = a := harr.2.2.2.1
    have hsl : sideLeft (chainModel J.right).W (c₁.nreg pE2)
        ((chainModel J.right).param (Qof P) x)
        (rayPt ((chainModel J.right).pos (Qof P) x) (dirOf (c₁.nreg oB)) 1) := by
      have := harr.2.2.2.2
      rw [neg_neg] at this
      rwx [hxa, eB]
    refine (IRS.ifF (by rwx [hK1]) (m2c_lh_irs E hI₁ hM₁ (e := pE2) (h := pH2)
      ⟨by simp [pE2, lE, sw], by simp [pE2, lH, sw]⟩ (by simp [pH2, lE, sw]) (by rwx [eB])
      hpe2 hpp2
      (posClass_of hpe2 hpp2.1 hpp2.2.1 (by rwx [hxa]) (Or.inl (by rwx [hxa])))
      (by rwx [hxa]) (Or.inl (by rwx [hxa]))
      (Gd := FreeAt J.right a (dirOf (c.nreg oB)))
      (fun _ => ⟨hsl, by rwx [hxa]⟩) (by omega))).mono le_rfl ?_
    rintro c₂ ⟨hres, hfr⟩
    rw [hxa, eB] at hres
    have k2 : ∀ q, q = pE2 ∨ q = pH2 → c₂.nreg q = c₁.nreg q := by
      intro q hq
      refine hfr.1 q (not_oracle_sw (by rcases hq with rfl | rfl <;> simp [pE2, pH2, sw])
        (by rcases hq with rfl | rfl <;> simp [pE2, pH2, sw])) ?_
        (by rcases hq with rfl | rfl <;> simp [pE2, pH2, ALLOC, sw])
      rintro (h | h)
      · rcases hq with rfl | rfl <;> rcases h with h | h | h <;>
          simp [pE2, pH2, lE, lH, lD, sw] at h
      · rcases hq with rfl | rfl <;> rcases h with (h | h) | h <;>
          simp [pE2, pH2, r2F, sw] at h
    refine ⟨⟨hres, fun _ _ => ⟨by rwx [k2 pE2 (Or.inl rfl)],
      by rwx [k2 pE2 (Or.inl rfl), k2 pH2 (Or.inr rfl)],
      by rwx [k2 pE2 (Or.inl rfl), k2 pH2 (Or.inr rfl)]⟩⟩,
      EFr.trans efr1 (hfr.mono fun r hr => m2c_M2R_lh' hr)⟩

/-- **Wall codes.** -/
theorem m2cW_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hM : MCtx P W J.right N₂ (c₀.nreg TBR) gMD2 gCD2 (sw 4) c)
    (hD : OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
    (hpos : OrgPos P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) (c.nreg oPE) (c.nreg oPH))
    (hk : c.nreg oKd = 1)
    (hroom : c.nreg ALLOC +
      (3 + (lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) + 7)) ≤ W) :
    IRS P W c₀ (m2cW sh) c
      (3 + (lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) + 7))
      (fun c' => M2Out P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c' ∧ EFr M2R c c') := by
  set a := stOrig J (Qof P) N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) with ha
  have hok := hD.ok
  obtain ⟨-, ha2, hay, -, hax⟩ := stOrig_facts E.hP E.hNF₂ hok
  have hb  := hok.2.1
  have hkk  := (hok.2.2.1 hk).1
  obtain ⟨hpe, hpp, hcl, hpt, -, hend⟩ := hpos
  have hxe  := hend hk
  have hay'  := hay
  have hsl := m2c_wall_left E.hNF₂ hkk hb
  rw [← hxe] at hsl
  unfold m2cW
  refine (m2c_lh_irs E hI hM (e := oPE) (h := oPH) ⟨by simp [oPE, lE, sw], by simp [oPE, lH, sw]⟩
    (by simp [oPH, lE, sw]) hb hpe hpp hcl (by rwx [hpt])
    (Or.inr (by rw [hpt]; exact hax hk)) (Gd := FreeAt J.right a (dirOf (c.nreg oB)))
    (fun _ => ⟨hsl, by rwx [hpt]⟩) hroom).mono le_rfl ?_
  rintro c' ⟨hres, hfr⟩
  rw [hpt] at hres
  exact ⟨⟨hres, fun h => absurd hk h⟩, hfr.mono fun r hr => m2c_M2R_lh' hr⟩

/-- **Task M2: the candidate of `C₂`.** -/
theorem m2Task : M2Task := by
  refine ⟨m2c, fun D => κGen D + 40000, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hM hD hpos hroom
  have hK := m2cK_le (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))
  have hK1  := (E.hK.fix hI).2.1
  have hr : c.nreg ALLOC + (m2cK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) + 4) ≤ W :=
    le_trans (Nat.add_le_add_left hK _) hroom
  have hr' : c.nreg ALLOC + m2cK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) ≤ W :=
    le_trans (Nat.add_le_add_left (Nat.le_add_right _ _) _) hr
  unfold m2c
  by_cases h0 : c.nreg oKd < c.nreg K1
  · refine (IRS.ifT h0 (m2cS_irs E hI hM hD hpos (by rwo [hK1] at h0) hr')).mono ?_
      (fun _ => id)
    exact le_trans (Nat.add_le_add_left (by norm_num) _) hK
  · have hin : IRS P W c₀ (.ifLtN K1 oKd (m2cS sh) (m2cW sh)) c
        (m2cK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) + 2)
        (fun c' => M2Out P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) c' ∧ EFr M2R c c') := by
      by_cases h2 : c.nreg K1 < c.nreg oKd
      · exact IRS.ifT (K := m2cK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) h2
          (m2cS_irs E hI hM hD hpos (by rwo [hK1] at h2) hr')
      · have hk1 : c.nreg oKd = 1 := by rwo [hK1] at h0 h2
        have hle : 3 + (lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) + 7) ≤
            m2cK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) := by
          unfold m2cK; generalize lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) = x
          omega
        exact (IRS.ifF (K := m2cK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) h2
          ((m2cW_irs E hI hM hD hpos hk1 (le_trans (Nat.add_le_add_left hle _) hr')).mono hle
            (fun _ => id)))
    refine (IRS.ifF h0 hin).mono ?_ (fun _ => id)
    exact le_trans (le_of_eq (by ring)) hK
end

end SweepEv

end Chazelle.Core
