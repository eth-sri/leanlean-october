module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvStopM1C2

/-!
# The sweep (WP-D), stage 2: the candidate of `C₁` of a stop origin, the wall and shared codes
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

/-- The post of the candidate of `C₁`. -/
def M1Post (P : Polygon) (J : Merge.Junction) (N : NF) (c c' : Config) : Prop :=
  ResOK P J.left (stOrig J (Qof P) N (c.nreg oKd) (c.nreg oKk) (c.nreg oB)) (dirOf (c.nreg oB))
    (FreeAt J.left (stOrig J (Qof P) N (c.nreg oKd) (c.nreg oKk) (c.nreg oB)) (dirOf (c.nreg oB)) ∧
      (stOrig J (Qof P) N (c.nreg oKd) (c.nreg oKk) (c.nreg oB)).2 ≤ J.left.top.2) r1F c' ∧
    EFr M1R c c'

theorem m1c_efr {X Y Z : ℕ → Prop} {c₁ c₂ : Config} (h₁ : EFr X c c₁) (h₂ : EFr Y c₁ c₂)
    (hX : ∀ r, X r → Z r) (hY : ∀ r, Y r → Z r) : EFr Z c c₂ :=
  by core_grind

/-- The local-hit registers, the save registers `r1F …` lie in `M1R`. -/
theorem lhsw_m1r (r : ℕ) (h : LHSW r1F r) : M1R r := by
  simp_all [LHSW, LHR, r1F, M1R, sw] <;> omega_nf

/-- The local-hit inputs lie in `M1R`. -/
theorem lin_m1r (r : ℕ) (h : r = lE ∨ r = lH ∨ r = lD) : M1R r := by
  simp_all [lE, lH, lD, M1R, sw] <;> omega_nf

theorem efr_lin (c : Config) (l : List Instr)
    (h : ∀ q, q ≠ lE → q ≠ lH → q ≠ lD → regB c.nmem l c.nreg q = c.nreg q) :
    EFr (fun r => r = lE ∨ r = lH ∨ r = lD) c { c with nreg := regB c.nmem l c.nreg } := by
  grind [Chazelle.Core.SweepEv.EFr, lE, ALLOC, sw, lH, lD]

theorem dr_m1 : DR MD₁ ∧ DR CD₁ ∧ DR (sw 3) ∧ DR (sw 33) := by
  omega_nf

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {N₁ N₂ : NF}

/-- The walk length of `C₁` at `sw 33`. -/
theorem m1c_n33 (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    c.nreg (sw 33) = 2 * J.left.m + 7 := by
  obtain ⟨H₀, -, hst⟩ := E.hst
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h33, -⟩ := hst
  rw [hI.hin _ (by omega_nf)]; exact h33

set_option maxRecDepth 20000 in
/-- **The wall code.** -/
theorem m1cK1_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hD : OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
    (hpos : OrgPos P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB) (c.nreg oPE) (c.nreg oPH))
    (hk : c.nreg oKd = 1) {K : ℕ}
    (hK : lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) + 10 ≤ K)
    (hroom : c.nreg ALLOC + K ≤ W) :
    IRS P W c₀ (m1cK1 sh) c K (M1Post P J N₂ c) := by
  have hok : StOK P J N₂ 1 (c.nreg oKk) (c.nreg oB) := hk ▸ hD.ok
  have hps : OrgPos P J N₂ 1 (c.nreg oKk) (c.nreg oB) (c.nreg oPE) (c.nreg oPH) := hk ▸ hpos
  obtain ⟨hbx, hlt, hpp, hz, hy, hx1, hsl⟩ := m1c_wall E.hP E.hNF₂ hok hps
  have hb : c.nreg oB ≤ 1 := hok.2.1
  obtain ⟨v1, v2, v3, vo⟩ := m1cL1_val c.nmem c.nreg
  obtain ⟨d1, d2, d3, d4⟩ := dr_m1
  unfold m1cK1 M1Post
  rw [hk]
  refine (IRS.seq (K₁ := 3) (K₂ := lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) + 7)
    ((IRS.block m1cL1 hI (m1cL_ok _ _).2).mono (by simp [m1cL1]) (fun _ h => h)) ?_).mono
    (by omega) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' rfl
  have eA : regB c.nmem m1cL1 c.nreg ALLOC = c.nreg ALLOC :=
    vo _ (by omega_nf) (by omega_nf)
      (by omega_nf)
  have h33 : regB c.nmem m1cL1 c.nreg (sw 33) = 2 * J.left.m + 7 := by
    have := m1c_n33 E hI₁; exact this
  refine (lhSave_irs (x := ⟨c.nreg oPE, c.nreg oPH⟩)
    (Gd := FreeAt J.left (stOrig J (Qof P) N₂ 1 (c.nreg oKk) (c.nreg oB)) (dirOf (c.nreg oB)) ∧
      (stOrig J (Qof P) N₂ 1 (c.nreg oKk) (c.nreg oB)).2 ≤ J.left.top.2)
    E.hsh E.hBs E.hXl d1 d2 d3 d4 (by omega_nf) hI₁ E.hK E.hG E.hWh (mctx1 E hI₁)
    E.hP E.hNF₁ E.hX E.hcap E.hOk₁ E.hsg₁ E.hdeg₁ h33 v1 v2 (by ram_grind)
    hlt hpp (Or.inl hbx) (by ram_simp) (Or.inr (by ram_simp)) ?_
    (by omega)).mono le_rfl ?_
  all_goals (grind [Chazelle.Core.SweepEv.efr_lin, Chazelle.Core.SweepEv.lhsw_m1r, Chazelle.Core.SweepEv.lin_m1r, Chazelle.Core.SweepEv.m1c_efr])

theorem efr_noRes {c c' : Config} (h : ∀ r, r ≠ r1F → c'.nreg r = c.nreg r)
    (hm : c'.nmem = c.nmem) : EFr M1R c c' :=
  by grind [Chazelle.Core.SweepEv.EFr, M1R, r1F, sw, ALLOC]

set_option maxRecDepth 20000 in
/-- **The shared code.** -/
theorem m1cK0_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hD : OrgD P J N₂ (c.nreg oKd) (c.nreg oKk) (c.nreg oB))
    (hk : c.nreg oKd = 0) {K : ℕ}
    (hK : lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) + 35020 ≤ K)
    (hroom : c.nreg ALLOC + K ≤ W) :
    IRS P W c₀ (m1cK0 sh) c K (M1Post P J N₂ c) := by
  have hb : c.nreg oB ≤ 1 := hD.ok.2.1
  have hσ := SweepStop.dirOf_cases' (c.nreg oB)
  obtain ⟨H₀, -, hst⟩ := E.hst
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h45, -⟩ := hst
  have e46 : c.nreg (sw 46) = cstL J 1 := by
    rw [hI.hin _ (by omega_nf)]; ram_grind
  obtain ⟨sl, spp, spos⟩ := Cand1.shared_posL E.hP (Qof P) P.n
  have k0 : c.nreg K0 = 0 := (E.hK.fix hI).1
  have hshL : J.shared ∈ J.left.set := J.shared_mem_left
  have hsy : |J.shared.2| < J.left.radius := absy_lt J.left hshL
  have hst1 : J.shared.2 ≤ J.left.top.2 := J.left.snd_le_top_of_mem_set hshL
  obtain ⟨d1, d2, d3, d4⟩ := dr_m1
  obtain ⟨R, hRd⟩ : ∃ R, R = lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) := ⟨_, rfl⟩
  rw [← hRd] at hK
  unfold m1cK0 M1Post
  rw [hk, stOrig_zero]
  refine (IRS.seq (K₁ := 35007)
    (K₂ := R + 12)
    (callArr_irs (P := P) (dsc := CD₁) (re := sw 46) (rh := K0) (rd := oB) (o := m1o)
      (C := J.left) hI (E.ctx1' hI) (by omega_nf) (by omega_nf)
      (by omega) (by ram_simp) (by ram_simp)
      (by omega)) ?_).mono (by omega) (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨hf1, harr, hnarr⟩, hfr1, hal1, hm1⟩
  rw [e46, k0, spos] at harr hnarr
  have fr1 : EFr (fun r => r = m1o ∨ r = m1o + 1 ∨ r = m1o + 2) c c₁ :=
    ⟨fun r a b d => hfr1 r a (fun e => b (Or.inl e)) (fun e => b (Or.inr (Or.inl e)))
      (fun e => b (Or.inr (Or.inr e))) d, hal1, hm1⟩
  have m1o_m1r : ∀ r, (r = m1o ∨ r = m1o + 1 ∨ r = m1o + 2) → M1R r := by
    omega_nf
  have eB : c₁.nreg oB = c.nreg oB := hfr1 _ (not_oracle_sw (by omega_nf)
    (by omega_nf)) (by omega_nf) (by omega_nf)
    (by omega_nf) (by omega_nf)
  have hK1 := E.hK.fix hI₁
  refine (IRS.ite (K := R + 10) (fun h1 => ?_) (fun h1 => ?_)).mono
    (show R + 10 + 2 ≤ R + 12 by omega) (fun _ h => h)
  · rw [hK1.1] at h1
    have hf : c₁.nreg m1o = 1 := by omega
    obtain ⟨hpn, hppA, hA⟩ := harr hf
    obtain ⟨v1, v2, v3, vo⟩ := m1cL0_val c₁.nmem c₁.nreg
    refine (IRS.seq (K₁ := 3)
      (K₂ := R + 7)
      ((IRS.block m1cL0 hI₁ (m1cL_ok _ _).1).mono (by simp [m1cL0]) (fun _ h => h)) ?_).mono
      (by omega) (fun _ h => h)
    rintro c₂ hI₂ - - rfl
    have eA : regB c₁.nmem m1cL0 c₁.nreg ALLOC = c₁.nreg ALLOC :=
      vo _ (by omega_nf) (by omega_nf)
        (by omega_nf)
    have h33 : regB c₁.nmem m1cL0 c₁.nreg (sw 33) = 2 * J.left.m + 7 := by
      have := m1c_n33 E hI₂; exact this
    have hpt : (chainModel J.left).pos (Qof P) ⟨c₁.nreg (m1o + 1), c₁.nreg (m1o + 2)⟩ =
        J.shared := hA.2.2.2.1
    have hcl : PosClass J.left (Qof P) ⟨c₁.nreg (m1o + 1), c₁.nreg (m1o + 2)⟩ :=
      posClass_of hpn hppA.1 hppA.2.1 (by ram_grind) (Or.inl (by ram_grind))
    have hsec := hA.2.2.2.2
    rw [neg_neg] at hsec
    refine (lhSave_irs (x := ⟨c₁.nreg (m1o + 1), c₁.nreg (m1o + 2)⟩)
      (Gd := FreeAt J.left J.shared (dirOf (c.nreg oB)) ∧ J.shared.2 ≤ J.left.top.2)
      E.hsh E.hBs E.hXl d1 d2 d3 d4 (by omega_nf) hI₂ E.hK E.hG E.hWh (mctx1 E hI₂)
      E.hP E.hNF₁ E.hX E.hcap E.hOk₁ E.hsg₁ E.hdeg₁ h33 v1 v2
      (by ram_grind)
      hpn hppA hcl (by ram_grind) (Or.inl (by ram_grind)) ?_
      (by ram_grind)).mono (by omega) ?_
    · ram_grind
    · rintro c' ⟨hres, hfr⟩
      have e3 : ({ c₁ with nreg := regB c₁.nmem m1cL0 c₁.nreg } : Config).nreg lD =
          c.nreg oB := by ram_grind
      rw [e3, hpt] at hres
      exact ⟨hres, m1c_efr fr1 (m1c_efr (efr_lin c₁ m1cL0 vo) hfr lin_m1r lhsw_m1r) m1o_m1r
        (fun r h => h)⟩
  · rw [hK1.1] at h1
    have hng : ¬ (FreeAt J.left J.shared (dirOf (c.nreg oB)) ∧ J.shared.2 ≤ J.left.top.2) := by
      intro g
      obtain ⟨p, t, hA⟩ := (freeAt_iff_arr J.left E.hP hσ (Or.inl hshL)).1 g.1
      grind
    refine (m1c_noRes (C := J.left) (a := J.shared) (σ := dirOf (c.nreg oB)) hI₁ hng).mono
      (by omega) ?_
    rintro c' ⟨hres, hk', hm'⟩
    exact ⟨hres, m1c_efr fr1 (efr_noRes hk' hm') m1o_m1r (fun r h => h)⟩

end

end SweepEv

end Chazelle.Core
