module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvWinR

/-!
# The sweep (WP-D), stage 3: the window of the event loop (RAM, part 2)

Double identification of the key (`locS`), the comparison of the key with an arc end (`cmpS`),
the step to the successor arc (`eqS`) and the gather of the region (`gatherS`).
-/

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep ShotList
open Chazelle.Chain (sideInArc sidePt SideAttach)

@[expose] public section

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

/-! ## Environment facts at a run configuration -/

theorem win_nt (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    NFWithin c.nmem (c.nreg (sw 3)) (c.nreg TBR) N₁ := by
  rw [hI.hin _ (show IFix (sw 3) by unfold IFix sw; omega),
    hI.hin _ (show IFix TBR by unfold IFix TBR sw; omega)]
  have h := E.hTBR
  exact Robust.transport E.hNT₁ (fun a ha => hI.hm a (⋄))

theorem win_tab (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    (∀ j, j < c.nreg TLR → c.nmem (c.nreg TBR + j) = 2 ^ j) ∧ N₁.arcs.length < 2 ^ c.nreg TLR ∧
      c.nreg TBR + c.nreg TLR ≤ c₀.nreg ALLOC ∧ c.nreg TLR = c₀.nreg TLR := by
  have eB : c.nreg TBR = c₀.nreg TBR := hI.hin _ (by unfold IFix TBR sw; omega)
  have eL : c.nreg TLR = c₀.nreg TLR := hI.hin _ (by unfold IFix TLR sw; omega)
  have h := E.hTBR
  refine ⟨fun j hj => ?_, by rw [eL]; exact E.hbig₁, by rw [eB, eL]; exact h, eL⟩
  rw [eL] at hj
  rw [eB, hI.hm _ (⋄)]
  exact E.htab j hj

theorem chain_vtx_abs_snd_lt (C : Chain) {p : ℕ} (h6 : 6 ≤ p) (hp : p < (chainModel C).W.n) :
    |((chainModel C).W.vtx p).2| < C.radius := by
  obtain ⟨i, rfl⟩ : ∃ i, p = i + 6 := ⟨p - 6, ⋄⟩
  have hn := cm_n C
  rw [cm_W, C.sideWalk_vtx_tour _ (⋄), Chain.sideTour]
  exact lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set (C.vertex_mem_set (C.sideIdx_le _ _))).2
    C.coordBound_lt_radius

/-- The key position in the walk of `C₁` is a vertex only on the tour. -/
theorem key6 (hP : J.P.Simple) {e h : ℕ} (hpw : PosW P J e h) (hL : (Lst J : ℝ) ≤ offK P J e h)
    (h0 : h = 0) : 6 ≤ ke₁ J e := by
  obtain ⟨-, -, -, -, -, -, -, hpt⟩ := key_map hP hpw hL
  have h6 := hpw.2.2 h0
  have hv := hpt 0
  rw [Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero] at hv
  by_contra hlt
  have a1 := chain_vtx_abs_snd_lt J.whole h6 hpw.1
  have a2 := Restore.chain_box_vtx_abs J.left (p := ke₁ J e) (⋄)
  rw [hv, a2] at a1
  exact lt_irrefl _ a1

/-- An arc end of a nonempty family is a vertex only on the tour. -/
theorem end6 {C : Chain} (hP : C.P.Simple) {N : NF} (hNF : IsNF (chainModel C) (Qof P) N)
    (hne : (N.F (chainModel C) (Qof P)).Nonempty) {j : ℕ} (hj : j < N.arcs.length)
    (h0 : (N.arc j).e.hgt = 0) : 6 ≤ (N.arc j).e.edge := by
  have hab := (Restore.arc_abs_lt hP hNF hne hj).2
  by_contra hlt
  have hpos : (chainModel C).pos (Qof P) (N.arc j).e = (chainModel C).W.vtx (N.arc j).e.edge := by
    have hp0 : (chainModel C).param (Qof P) (N.arc j).e = 0 := by
      unfold Model.param; rw [h0]
    Ξ win_pos_eq_sidePt, hp0
    exact Chazelle.Chain.sidePt_zero _ _
  rw [hpos, Restore.chain_box_vtx_abs C (⋄)] at hab
  exact lt_irrefl _ hab


/-! ## Double identification of the key -/

def locS : Stmt := locJ MD₁ (sw 3) wE1 kH wO

/-- The post of `locJ` at the key. -/
def LocPost (P : Polygon) (J : Merge.Junction) (N₁ : NF) (c c' : Config) : Prop :=
  c'.nreg wO < N₁.arcs.length ∧
    (¬ (chainModel J.left).IsCut (N₁.F (chainModel J.left) (Qof P))
        ((chainModel J.left).key (Qof P) ⟨c.nreg wE1, c.nreg kH⟩) →
      N₁.F (chainModel J.left) (Qof P) = ∅ ∨
        sideInArc (OracleQ.sk (chainModel J.left) (Qof P) N₁ (c'.nreg wO))
          (OracleQ.ek (chainModel J.left) (Qof P) N₁ (c'.nreg wO))
          ((chainModel J.left).key (Qof P) ⟨c.nreg wE1, c.nreg kH⟩)) ∧
    ((chainModel J.left).IsCut (N₁.F (chainModel J.left) (Qof P))
        ((chainModel J.left).key (Qof P) ⟨c.nreg wE1, c.nreg kH⟩) →
      OracleQ.sk (chainModel J.left) (Qof P) N₁ (c'.nreg wO) =
          (chainModel J.left).key (Qof P) ⟨c.nreg wE1, c.nreg kH⟩ ∨
        OracleQ.ek (chainModel J.left) (Qof P) N₁ (c'.nreg wO) =
          (chainModel J.left).key (Qof P) ⟨c.nreg wE1, c.nreg kH⟩) ∧
    (∀ r, bandOf r ∉ oracleBands → r ≠ wO → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem


theorem locS_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (he : c.nreg wE1 < (chainModel J.left).W.n)
    (hpp : ProperPos (chainModel J.left) (Qof P) P.n ⟨c.nreg wE1, c.nreg kH⟩)
    (hroom : c.nreg ALLOC + (5500 * (c₀.nreg TLR + 1) + 9) ≤ W) :
    IRS P W c₀ locS c (5500 * (c₀.nreg TLR + 1) + 9) (LocPost P J N₁ c) := by
  obtain ⟨hmd, hmwf, -, -⟩ := E.md hI
  have hNT := win_nt E hI
  have hNA := hNT.nfAt
  obtain ⟨htab, hbig, hTB, eL⟩ := win_tab E hI
  have hP₁ : J.left.P.Simple := E.hP
  have hA0 := arcs_pos hP₁ E.hNF₁
  obtain ⟨b7, b4A, b6A⟩ := NFLoc.nfWithin_bounds hNT E.hNF₁ hA0
  have hAW : c.nreg ALLOC ≤ W := hI.hw.1 _
  have hAc := hI.hA
  unfold locS
  refine (locJ_irs (md := MD₁) (nf := sw 3) (pe := wE1) (ph := kH) (o := wO) hI E.hG E.hWh
    ⟨by unfold MD₁ sw; norm_num, by unfold MD₁ sw; norm_num, by unfold sw; norm_num,
      by unfold sw; norm_num, by unfold wE1 sw; norm_num, by unfold wE1 sw; norm_num,
      by unfold kH sw; norm_num, by unfold kH sw; norm_num⟩
    ⟨by unfold wO sw; norm_num, by unfold wO sw; norm_num⟩ hmd hmwf hP₁ hNA E.hNF₁
    he hpp htab hbig (⋄) (by omega) (by omega) (by omega)
    (by rw [eL]; exact hroom)).mono (Ρ eL) ?_
  rintro c' ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨h1, h2, h3, fun r hr hro => ?_, h6⟩
  by_cases hra : r = ALLOC
  · rw [hra]; exact h5
  · exact h4 r hr hro hra


/-! ## The comparison of the key with an arc end -/

def cmpS : Stmt := callOff CD₁ wE1 kH wEE wEH cB1 wC

/-- The registers `callOff` may write. -/
def BcO (o : ℕ) (r : ℕ) : Bool :=
  Bprim r || decide (50200 ≤ r ∧ r < 50210) || decide (r = o) || decide (r = o + 1)

theorem callOff_wr (dsc ex hx ey hy g o : ℕ) : SignK.wr (BcO o) (callOff dsc ex hx ey hy g o) = true := by
  have hoff : SignK.wr (BcO o) offCmp = true :=
    wr_mono wr_offCmp (fun r h => ⊚ BcO, h)
  Θ callOff, callP, cps, block, SignK.wr, SignK.wrOK, BcO, hoff

/-- The `b₁`-offset of a position of the walk of `C₁`. -/
noncomputable def U₁ (P : Polygon) (J : Merge.Junction) (x : WPos) : ℝ :=
  off (chainModel J.left).W.n (b₁ J) ((chainModel J.left).key (Qof P) x)


theorem cmpS_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (he : c.nreg wE1 < (chainModel J.left).W.n) (hee : c.nreg wEE < (chainModel J.left).W.n)
    (hpx : ProperPos (chainModel J.left) (Qof P) P.n ⟨c.nreg wE1, c.nreg kH⟩)
    (hpy : ProperPos (chainModel J.left) (Qof P) P.n ⟨c.nreg wEE, c.nreg wEH⟩)
    (h6x : c.nreg kH = 0 → 6 ≤ c.nreg wE1) (h6y : c.nreg wEH = 0 → 6 ≤ c.nreg wEE)
    (hroom : c.nreg ALLOC + 11008 ≤ W) :
    IRS P W c₀ cmpS c 11008 (fun c' =>
      BitIs c' wC (U₁ P J ⟨c.nreg wE1, c.nreg kH⟩ < U₁ P J ⟨c.nreg wEE, c.nreg wEH⟩) ∧
      BitIs c' (sw 3011) (U₁ P J ⟨c.nreg wEE, c.nreg wEH⟩ < U₁ P J ⟨c.nreg wE1, c.nreg kH⟩) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ wC → r ≠ sw 3011 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.nreg ALLOC = c.nreg ALLOC) := by
  have hctx := E.ctx1' hI
  have hM := E.hM.fix hI
  have hg : c.nreg cB1 < (chainModel J.left).W.n := by rw [hM.b1]; exact b₁_lt
  unfold cmpS
  refine (IRS.addFrameB (callOff_wr _ _ _ _ _ _ _) (callOff_irs (P := P) hI hctx
    ⟨by unfold CD₁ sw; norm_num, by unfold CD₁ sw; norm_num, by unfold wE1 sw; norm_num,
      by unfold wE1 sw; norm_num, by unfold kH sw; norm_num, by unfold kH sw; norm_num,
      by unfold wEE sw; norm_num, by unfold wEE sw; norm_num, by unfold wEH sw; norm_num,
      by unfold wEH sw; norm_num, by unfold cB1 sw; norm_num, by unfold cB1 sw; norm_num⟩
    ⟨by unfold wC sw; norm_num, by unfold wC sw; norm_num⟩ he hee hg hpx hpy h6x h6y hroom)).mono
    le_rfl ?_
  rintro c' ⟨⟨b1, b2, k, -, -⟩, hf⟩
  rw [hM.b1] at b1 b2
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hf.1 _ (by unfold BcO Bprim ALLOC wC sw; simp)
  refine ⟨b1, b2, fun r hr h1 h2 => ?_, hf.2.2.1, hA⟩
  by_cases hra : r = ALLOC
  · rw [hra]; exact hA
  · exact k r hr h1 h2 hra


/-! ## The arc after the key -/

/-- The arc registers hold the arc at spine position `o`. -/
def ArcRegs (N : NF) (c : Config) (o : ℕ) : Prop :=
  c.nreg wA = OracleQ.sj N o ∧ c.nreg wR = (N.arc (OracleQ.sj N o)).reg ∧
    c.nreg wEE = (N.arc (OracleQ.sj N o)).e.edge ∧ c.nreg wEH = (N.arc (OracleQ.sj N o)).e.hgt

def swS : Stmt :=
  .seq (.instr (.addN wT (sw 3) K1)) (.seq (.instr (.loadN wL wT)) (.seq (.instr (.addN wO wO K1))
    (.seq (.ifLtN wO wL .skip (.instr (.constN wO 0))) arcS)))

def eqS : Stmt := .ifLtN K0 wC .skip (.ifLtN K0 (sw 3011) .skip swS)

/-- The registers of the arc step. -/
def ArcW (q : ℕ) : Prop := q = wT ∨ q = wA ∨ q = wR ∨ q = wEE ∨ q = wEH ∨ q = wL ∨ q = wO


theorem eqS_irs {M : Model} {Q : Polygon} {N : NF} (hI : IInv W c₀ c) (hK₀ : Consts c₀)
    (hNF : IsNF M Q N) (hNA : NFAt c.nmem (c.nreg (sw 3)) N)
    (hB1 : c.nreg (sw 3) + 7 ≤ W) (hB2 : c.nmem (c.nreg (sw 3) + 4) + 5 * N.arcs.length ≤ W)
    (hB3 : c.nmem (c.nreg (sw 3) + 6) + N.arcs.length ≤ W) (ho : c.nreg wO < N.arcs.length)
    {p1 p2 : Prop} (hb1 : BitIs c wC p1) (hb2 : BitIs c (sw 3011) p2) (har : ArcRegs N c (c.nreg wO)) :
    IRS P W c₀ eqS c 30 (fun c' =>
      (p1 ∨ p2 → c'.nreg wO = c.nreg wO) ∧
      (¬ p1 → ¬ p2 → c'.nreg wO = OracleQ.succP N.arcs.length (c.nreg wO)) ∧
      ArcRegs N c' (c'.nreg wO) ∧ (∀ q, ¬ ArcW q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  have hK := hK₀.fix hI
  have k0 := hK.1
  unfold eqS
  by_cases h1 : c.nreg K0 < c.nreg wC
  · have hp : p1 := hb1.2.1 (by have := hb1.1; omega)
    refine (IRS.ifT h1 (IRS.skip (K := 28) hI ⟨fun _ => rfl, fun h _ => absurd hp h, har,
      fun _ _ => rfl, rfl⟩)).mono le_rfl (fun _ h => h)
  have hn1 : ¬ p1 := fun hp => h1 (by rw [k0, hb1.2.2 hp]; norm_num)
  refine IRS.mono (K := 28 + 2) (IRS.ifF h1 ?_) le_rfl (fun _ h => h)
  by_cases h2 : c.nreg K0 < c.nreg (sw 3011)
  · have hp : p2 := hb2.2.1 (by have := hb2.1; omega)
    exact (IRS.ifT h2 (IRS.skip (K := 26) hI ⟨fun _ => rfl, fun _ h => absurd hp h, har,
      fun _ _ => rfl, rfl⟩)).mono le_rfl (fun _ h => h)
  have hn2 : ¬ p2 := fun hp => h2 (by rw [k0, hb2.2.2 hp]; norm_num)
  refine IRS.mono (K := 26 + 2) (IRS.ifF h2 ?_) le_rfl (fun _ h => h)
  have sT : IScr wT := iscr_sw' (⊛) (by norm_num)
  have sL : IScr wL := iscr_sw' (⊛) (by norm_num)
  have sO : IScr wO := iscr_sw' (⊛) (by norm_num)
  unfold swS
  refine IRS.seq (K₂ := 25) (win_irs_add hI sT (by rw [hK.2.1]; omega)) ?_ |>.mono (⊛)
    (fun _ h => h)
  rintro c₁ hI₁ - - ⟨v1, o1, m1⟩
  refine IRS.seq (K₂ := 24) (win_irs_load hI₁ sL) ?_ |>.mono (⊛) (fun _ h => h)
  rintro c₂ hI₂ - - ⟨v2, o2, m2⟩
  rw [v1, m1, hK.2.1, hNA.2.1] at v2
  refine IRS.seq (K₂ := 23) (win_irs_add hI₂ sO (by
    rw [o2 _ (by rne), o1 _ (by rne), (hK₀.fix hI₂).2.1]; omega)) ?_ |>.mono (⊛)
    (fun _ h => h)
  rintro c₃ hI₃ - - ⟨v3, o3, m3⟩
  rw [o2 _ (by rne), o1 _ (by rne), (hK₀.fix hI₂).2.1] at v3
  have hsucc : IRS P W c₀ (.ifLtN wO wL .skip (.instr (.constN wO 0))) c₃ 3
      (fun c' => win_Upd c₃ c' wO (OracleQ.succP N.arcs.length (c.nreg wO))) := by
    by_cases h : c₃.nreg wO < c₃.nreg wL
    · refine (IRS.ifT h (IRS.skip (K := 1) hI₃ ⟨?_, fun _ _ => rfl, rfl⟩)).mono
        (⊛) (fun _ h => h)
      rw [o3 wL (by rne), v2, v3] at h
      rw [v3]; unfold OracleQ.succP; rw [ite_eq_left h]
    · refine (IRS.ifF h (win_irs_const' hI₃ sO (Nat.zero_le W))).mono (⊛) ?_
      rintro c' ⟨a, b, d⟩
      refine ⟨?_, b, d⟩
      rw [o3 wL (by rne), v2, v3] at h
      rw [a]; unfold OracleQ.succP; rw [ite_eq_right h]
  refine IRS.seq (K₂ := 16) hsucc ?_ |>.mono (⊛) (fun _ h => h)
  rintro c₄ hI₄ - - ⟨v4, o4, m4⟩
  have hm4 : c₄.nmem = c.nmem := Ρ m4, m3, m2, m1
  have e3 : c₄.nreg (sw 3) = c.nreg (sw 3) := by
    Ξ o4 _ (by rne), o3 _ (by rne), o2 _ (by rne), o1 _ (by rne)
  have hs := OracleQ.succP_lt ho
  refine (arcS_irs hI₄ (hK₀.fix hI₄) hNF (by rw [hm4, e3]; exact hNA) (by rw [e3]; exact hB1)
    (by rw [hm4, e3]; exact hB2) (by rw [hm4, e3]; exact hB3) (by rw [v4]; exact hs)).mono
    le_rfl ?_
  rintro c' ⟨a1, a2, a3, a4, a5, a6⟩
  have eo : c'.nreg wO = OracleQ.succP N.arcs.length (c.nreg wO) := by
    Ξ a5 _ (by rne) (by rne) (by rne) (by rne) (by rne), v4
  refine ⟨fun h => absurd h (by tauto), fun _ _ => eo, ?_, fun q hq => ?_, Ρ a6, hm4⟩
  · rw [eo]; rw [v4] at a1 a2 a3 a4; exact ⟨a1, a2, a3, a4⟩
  · unfold ArcW at hq
    push Not at hq
    obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
    Ξ a5 q q1 q2 q3 q4 q5, o4 q q7, o3 q q7, o2 q q6, o1 q q1


/-! ## The gather of the region -/

/-- Store `wR` at the allocator, raising it by one. -/
def win_put1 : Stmt := block [.storeN ALLOC wR, .addN ALLOC ALLOC K1]

theorem win_put1_irs (hI : IInv W c₀ c) (hK : Consts c) (hroom : c.nreg ALLOC + 1 ≤ W) :
    IRS P W c₀ win_put1 c 2 (fun c' => c'.nreg ALLOC = c.nreg ALLOC + 1 ∧
      (∀ r, r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (c.nreg ALLOC) (c.nreg wR)) := by
  have k1 : c.nreg 240611 = 1 := hK.2.1
  have hw := hI.hw
  have hroom' : c.nreg 9999 + 1 ≤ W := hroom
  have ex : ∃ c' k, Exec P W (block [.storeN 9999 243005, .addN 9999 9999 240611]) c c' k ∧
      k = 2 ∧ c'.nreg 9999 = c.nreg 9999 + 1 ∧ (∀ r, r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      c'.nmem = upd c.nmem (c.nreg 9999) (c.nreg 243005) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
    · config_simp; omega
    · config_simp
      ϴ upd, ite_eq_right hr
    · config_simp
  obtain ⟨c', k, ex, hk, h1, h2, h3, h4, h5, h6⟩ := ex
  refine IRS.ofExec hI ex (⋄) (fun r _ hr => h2 r hr) h4 (fun a ha => ?_) h5 h6
    (by show c.nreg 9999 ≤ c'.nreg 9999; omega) (by show c'.nreg 9999 ≤ c.nreg 9999 + k; omega)
    ⟨h1, h2, h3⟩
  Ξ h3
  have h0 : c₀.nreg 9999 ≤ c.nreg 9999 := hI.hA
  have ha' : a < c₀.nreg 9999 := ha
  ϴ upd
  rw [ite_eq_right (⋄)]


def gatherS : Stmt :=
  .seq (.instr (.copyN gL ALLOC)) (.seq (.instr (.constN gC 1)) (.seq (.instr (.copyN gNF (sw 3)))
    (.seq win_put1 (.seq (gather CD₁) (.seq (.instr (.copyN wGB gBase)) (.instr (.copyN wGK gK)))))))

/-- The registers the gather tail writes (besides the oracle bands and the allocator). -/
def GathW (q : ℕ) : Prop := GSet q ∨ q = gL ∨ q = gC ∨ q = gNF ∨ q = wGB ∨ q = wGK



theorem gatherS_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hR : c.nreg wR < N₁.nRegions)
    (hroom : c.nreg ALLOC + (gatherK N₁ [c.nreg wR] + 10) ≤ W) :
    IRS P W c₀ gatherS c (gatherK N₁ [c.nreg wR] + 10) (fun c' =>
      c.nreg ALLOC ≤ c'.nreg wGB ∧ c'.nreg wGK = (regArcs N₁ [c.nreg wR]).length ∧
      c'.nreg wGB + 4 * (regArcs N₁ [c.nreg wR]).length ≤ c'.nreg ALLOC ∧
      Gath (chainModel J.left) (Qof P) N₁ c'.nmem (c'.nreg wGB) (regArcs N₁ [c.nreg wR]) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ GathW r → r ≠ ALLOC → c'.nreg r = c.nreg r)) := by
  have hK := E.hK.fix hI
  have sL : IScr gL := iscr_sw' (⊛) (by norm_num)
  have sC : IScr gC := iscr_sw' (⊛) (by norm_num)
  have sN : IScr gNF := iscr_sw' (⊛) (by norm_num)
  have sB : IScr wGB := iscr_sw' (⊛) (by norm_num)
  have sK : IScr wGK := iscr_sw' (⊛) (by norm_num)
  have hAW : c.nreg ALLOC ≤ W := hI.hw.1 _
  set R := c.nreg wR with hRd
  unfold gatherS
  refine IRS.seq (K₂ := gatherK N₁ [R] + 9) (win_irs_copy hI sL) ?_ |>.mono (⋄) (fun _ h => h)
  rintro c₁ hI₁ - - ⟨v1, o1, m1⟩
  refine IRS.seq (K₂ := gatherK N₁ [R] + 8) (win_irs_const' hI₁ sC (⋄)) ?_ |>.mono (by omega)
    (fun _ h => h)
  rintro c₂ hI₂ - - ⟨v2, o2, m2⟩
  refine IRS.seq (K₂ := gatherK N₁ [R] + 7) (win_irs_copy hI₂ sN) ?_ |>.mono (⋄) (fun _ h => h)
  rintro c₃ hI₃ - - ⟨v3, o3, m3⟩
  have a3 : c₃.nreg ALLOC = c.nreg ALLOC := by
    Ξ o3 _ (by rne), o2 _ (by rne), o1 _ (by rne)
  refine IRS.seq (K₂ := gatherK N₁ [R] + 5) (win_put1_irs hI₃ (E.hK.fix hI₃) (⋄)) ?_ |>.mono
    (⋄) (fun _ h => h)
  rintro c₄ hI₄ - - ⟨a4, o4, m4⟩
  have r3 : c₃.nreg wR = R := Ρ o3 _ (by rne), o2 _ (by rne), o1 _ (by rne)
  rw [a3, r3] at m4
  rw [a3] at a4
  have l4 : c₄.nreg gL = c.nreg ALLOC := by
    Ξ o4 _ (by rne), o3 _ (by rne), o2 _ (by rne), v1
  have c4 : c₄.nreg gC = 1 := Ρ o4 _ (by rne), o3 _ (by rne), v2
  have n4 : c₄.nreg gNF = c₀.nreg (sw 3) := by
    Ξ o4 _ (by rne), v3, o2 _ (by rne), o1 _ (by rne)
    exact hI.hin _ (by unfold IFix sw; omega)
  have hNW : NFWithin c₄.nmem (c₀.nreg (sw 3)) (c₀.nreg ALLOC) N₁ :=
    E.hNW₁.transport (fun a ha => hI₄.hm a ha)
  have hP₁ : J.left.P.Simple := E.hP
  refine IRS.seq (K₂ := 2) (gather_irs (dsc := CD₁) (rs := [R]) hI₄ E.hK (E.ctx1' hI₄)
    ⟨by unfold CD₁ sw; norm_num, by unfold CD₁ sw; norm_num, by unfold GSet CD₁ sw; omega⟩
    hP₁ E.hNF₁ hNW n4 hI₄.hA (fun r hr => by rw [List.mem_singleton.1 hr]; exact hR)
    (fun j hj => by
      simp only [List.length_singleton] at hj
      have : j = 0 := ⋄
      subst this; rw [l4, m4, Nat.add_zero, upd_same]; rfl)
    (by rw [l4, a4]; simp) (by rw [c4]; simp) (by rw [a4]; omega)) ?_ |>.mono (⋄)
    (fun _ h => h)
  rintro c₅ hI₅ - - ⟨⟨g1, g2, g3, g4, g5, g6, -⟩, -⟩
  refine IRS.seq (K₂ := 1) (win_irs_copy hI₅ sB) ?_ |>.mono le_rfl (fun _ h => h)
  rintro c₆ hI₆ - - ⟨v6, o6, m6⟩
  refine (win_irs_copy hI₆ sK).mono le_rfl ?_
  rintro c₇ ⟨v7, o7, m7⟩
  have e7B : c₇.nreg wGB = c.nreg ALLOC + 1 := Ρ o7 _ (by rne), v6, g1, a4
  have e7A : c₇.nreg ALLOC = c.nreg ALLOC + 1 + 4 * (regArcs N₁ [R]).length := by
    Ξ o7 _ (by rne), o6 _ (by rne), g3, a4
  refine ⟨⋄, by rw [v7, o6 _ (by rne), g2], by omega, fun k hk => ?_, fun a ha => ?_,
    fun r hr hg hra => ?_⟩
  · rw [m7, m6, e7B, ← a4]; exact g4 k hk
  · rw [m7, m6, g5 a (⋄), m4, upd_other _ _ _ (by omega), m3, m2, m1]
  · have hG : ¬ GSet r := fun h => hg (Or.inl h)
    rw [o7 r (fun h => hg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))),
      o6 r (fun h => hg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))), g6 r hr hG hra,
      o4 r hra, o3 r (fun h => hg (Or.inr (Or.inr (Or.inr (Or.inl h))))),
      o2 r (fun h => hg (Or.inr (Or.inr (Or.inl h)))), o1 r (fun h => hg (Or.inr (Or.inl h)))]


end

end SweepEv

end Chazelle.Core
