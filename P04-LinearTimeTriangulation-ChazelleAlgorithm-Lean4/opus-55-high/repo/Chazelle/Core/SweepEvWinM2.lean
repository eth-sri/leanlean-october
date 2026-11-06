module

public import Chazelle.MacT
public import Chazelle.Core.SweepEvPrep
public import Chazelle.Core.RestoreFKind1
public import Chazelle.Core.SweepEvEnv
public import Chazelle.Core.SweepEvOrg
public import Chazelle.Core.FuseAsmMain
public import Chazelle.Core.SweepEvBatch

namespace Chazelle.Core
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep ShotList
open Chazelle.Chain (sideInArc sidePt SideAttach)
@[expose] public section
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}
theorem regArcs_single (N : NF) (r : ℕ) : regArcs N [r] = (N.region r).arcs := by
  zupch
set_option maxHeartbeats 8000000 in
/-- **The mathematics of the window.** -/
theorem win_math (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) {e h : ℕ} (hpw : PosW P J e h)
    (hL : (Lst J : ℝ) ≤ offK P J e h) {o' : ℕ} (ho' : o' < N₁.arcs.length) {c' : Config}
    (hne : (N₁.F ztbw zta).Nonempty →
      (sideInArc ztzcv
          ztzcs ztymy ∨
        OracleQ.sk ztbw zta N₁ o' = (chainModel J.left).key zta ztcjv) ∧
      DecOut J (U₁ P J (N₁.arc ztdfy).e < U₁ P J ztcjv) ztcvy
        (N₁.arc ztdfy).e.edge (N₁.arc ztdfy).e.hgt c')
    (hemp : N₁.F ztbw zta = ∅ → c'.nreg wX = 1)
    (hg : Gath ztbw zta N₁ c'.nmem zthug
      (regArcs N₁ [(N₁.arc ztdfy).reg])) :
    c'.nreg wX ≤ 1 ∧
    (c'.nreg wX = 0 → PosW P J ztfgk ztfgl ∧
      offK P J e h < offK P J ztfgk ztfgl ∧
      (offK P J ztfgk ztfgl = (Lst J : ℝ) + lL1 J ∨
        ∃ (d : ℕ) (t : ℝ), MValid J d t ∧ 0 ≤ t ∧ t ≤ 1 ∧
          offK P J ztfgk ztfgl = (Lst J : ℝ) + ψ J d + t ∧
          (chainModel J.left).IsCut ztwjx
            ztwms)) ∧
    (∀ (d : ℕ) (t : ℝ), MValid J d t → 0 ≤ t → t < 1 →
      offK P J e h < (Lst J : ℝ) + ψ J d + t →
      ztdmo →
      sidePt (chainModel J.left).W ztwjw t ∈
        ShotList.loSet ztbw zta c'.nmem zthug
          (regArcs N₁ [(N₁.arc ztdfy).reg]).length []) := by
  zujmp
  zujzu
  zucwa

  set x₀ := M.key zta ztcjv with hx₀
  zucdy
  set t₀ := (chainModel J.whole).param zta ztcq with ht₀
  have ht00 : 0 ≤ t₀ := hpw.2.1.1
  have ht01 : t₀ < 1 := hpw.2.1.2.1
  have hu0 : off M.W.n ztbsn x₀ = (kd J e : ℝ) + t₀ := key₁_off hP hpw hL
  have hoL : offK P J e h = (Lst J : ℝ) + ψ J ztcvy + t₀ := by_simp_all
  have hn₁ : ztbiy := by rw [hMd, win_n₁_eq]; omega
  have hke : ke₁ J e < M.W.n := Nat.mod_lt _ hn₁
  have hppx : ProperPos M zta P.n ztcjv := by
    refine ⟨?_, ?_, hpw.2.1.2.2⟩ <;> zvokb <;> [exact ht00; exact ht01]
  have hxr := key₁_range (Q := Qof P) hke hppx
  set a := OracleQ.sj N₁ o' with ha
  have hal : a < N₁.arcs.length := NFLoc.seq_lt hNF ho'
  set l := regArcs N₁ [(N₁.arc a).reg] with hl
  obtain ⟨hreg, hmem⟩ := arc_mem_region hNF hal
  have hll : ∀ j ∈ l, j < N₁.arcs.length := by
    zun
    rw [hl, regArcs_single] at hj
    obtain ⟨-, -, -, reg, -, -, hA, -⟩ := hNF
    exact ((hA.2.2.2 _ hreg j).1 hj).1
  have hol : a ∈ l := by rw [hl, regArcs_single]; omega
  -- the valid offsets beyond the key are beyond it in the walk of `C₁`
  have hbeyond : ∀ (d : ℕ) (t : ℝ), MValid J d t → 0 ≤ t → t < 1 →
      offK P J e h < (Lst J : ℝ) + ψ J d + t → off M.W.n ztbsn x₀ < d + t := by
    intro d t hv ht0 ht1 hlt
    zupda
    rw [hoL] at hlt
    exact lex_lt hgap0 hv.2.1 hv.2.2.1 ht0 ht1 ht00 ht01 by_linarith
  have hpp : ∀ j, j < N₁.arcs.length → ProperPos M zta (Qof P).n (N₁.arc j).s ∧
      ProperPos M zta (Qof P).n (N₁.arc j).e := fun j hj => by
    obtain ⟨-, -, -, reg, -, -, -, -, -, -, h⟩ := hNF; grind
  have hdn : ∀ d, d < E₁ J → d < M.W.n := fun d hd => lt_of_lt_of_le hd ztjip
  by_cases hF : N₁.F M zta = ∅
  · -- the empty family: the arc covers the whole walk
    have hX := hemp hF
    refine ⟨by_omega, fun h0 => by_omega, fun d t hv ht0 ht1 _ _ => ?_⟩
    obtain ⟨reg, -, -, harc⟩ := OracleQ.isArc_sj hNF ho'
    have hab0 : OracleQ.sk M zta N₁ o' = 0 ∧ OracleQ.ek M zta N₁ o' = 0 := by
      zutm
      · grind
      grind
    refine mem_loSet hg hll hpp hol (Nat.mod_lt _ hn₁) ht0 ht1.le ?_
    show CIn ztzcu ztwzo _
    rw [hab0.1, hab0.2]
    unfold CIn sideInArc
    grind
  have hFne : ztziw := Set.nonempty_iff_ne_empty.2 hF
  obtain ⟨hin, hdec⟩ := hne hFne
  have hab := (OracleQ.arc_facts hNF hFne ho').2.2.1
  have hcutE := (OracleQ.arc_facts hNF hFne ho').2.1
  obtain ⟨-, ⟨hpe, hee, -⟩⟩ := arc_end_facts hP₁ hNF hal
  set eE := (N₁.arc a).e.edge with heEd
  set tE := M.param zta (N₁.arc a).e with htEd
  have htE0 : 0 ≤ tE := hpe.1
  have htE1 : tE < 1 := hpe.2.1
  set dE := dOf M.W.n ztbsn eE with hdEd
  have hUE : off M.W.n ztbsn ztwzo = (dE : ℝ) + tE :=
    off_key' b₁_lt hee htE0 htE1
  have hUE' : U₁ P J (N₁.arc a).e = (dE : ℝ) + tE := hUE
  have hUx : U₁ P J ztcjv = (kd J e : ℝ) + t₀ := hu0
  have cov : ∀ (d : ℕ) (t : ℝ), d < E₁ J → 0 ≤ t → t < 1 → (kd J e : ℝ) + t₀ < d + t →
      ((d : ℝ) + t ≤ dE + tE ∨ (dE : ℝ) + tE < kd J e + t₀) →
      sidePt M.W (zthm % M.W.n) t ∈ ShotList.loSet M zta c'.nmem zthug l.length [] :=
    fun d t hd ht0 ht1 hlt hup => cover_arc hP hNF hg hll ho' hol hxr.1 hxr.2 hab hin hd ht0 ht1
      by_grind by_grind
  rw [hUE', hUx] at hdec
  rcases hdec with ⟨hX, hc⟩ | ⟨hX, hnp, hδ, hd0, hl1d, hdE, hwE, hwH⟩ |
      ⟨hX, hnp, hncl, hdE, hwE, hwH⟩
  · -- part end
    rw [← hMd] at hc
    refine ⟨by_omega, fun h0 => by_omega, fun d t hv ht0 ht1 hlt _ => ?_⟩
    refine cov d t hv.1 ht0 ht1 by_grind ?_
    rcases hc with hp | hE
    · grind
    · left
      have : d + 1 ≤ dE := by have := hv.1; omega
      have : ((d + 1 : ℕ) : ℝ) ≤ dE := by exact_mod_cast this
      grind
  · -- the gap start
    rw [← hMd] at hl1d hdE
    obtain ⟨hPW, hoffG⟩ := wend_gap (P := P) hP hδ
    have hψk : ψ J ztcvy = kd J e := by unfold ψ; grind
    have hkl : (kd J e : ℝ) + t₀ < lL1 J := by
      have : ((kd J e + 1 : ℕ) : ℝ) ≤ lL1 J := by exact_mod_cast hd0
      grind
    have hlE : (lL1 J : ℝ) ≤ dE + tE := by
      have : (lL1 J : ℝ) ≤ dE := by exact_mod_cast hl1d
      linarith
    refine ztgof
    · grind
    · zulki
      rw [hwE, hwH, hoffG] at hle'
      zudoi

      rcases lex_le_gap hδ hv.2.1 hv.2.2.1 ht0 ht1 by_linarith with h1 | ⟨h1, h2⟩
      · exact cov d t hv.1 ht0 ht1 hb (Or.inl by_linarith)
      · zufcz
        rw [gap_pt hP hδ]
        exact cov ztdov 0 (lt_of_le_of_lt hl1d hdE) le_rfl one_pos by_grind
          ztzz
  · -- an arc end
    rw [← hMd] at hncl hdE hwE
    have hne' : ¬ ((dE : ℝ) + tE = kd J e + t₀) := by
      zudii
      have hk : M.key zta (N₁.arc a).e = x₀ := by
        have := key₁_range (Q := Qof P) hee hpe
        refine win_off_inj (g := (b₁ J : ℝ)) this.1 this.2 hxr.1 hxr.2 ?_
        zupda; exact hUE.trans heq
      rcases hin with h1 | h1
      · exact not_sia_end _ _ (show sideInArc _ ztwzo ztwzo by
          rw [show OracleQ.ek M zta N₁ o' = x₀ from hk] at h1 ⊢; exact h1)
      · exact hab (h1.trans hk.symm)
    have hlt0 : (kd J e : ℝ) + t₀ < dE + tE := lt_of_le_of_ne ztwaj ztvbj
    have hkdE : kd J e ≤ dE := by
      have : (kd J e : ℝ) < dE + 1 := by_linarith
      zulfy
    have hgE : GapOut J dE := by
      intro hδ
      omega
    have hψE : (if dE < lL1 J + lδ J then dE else dE - lδ J) = ψ J dE := by
      unfold ψ
      rcases win_lδ_cases (J := J) with h7 | h7
      · zuwd
      · have := hgE by_omega
        zuwd
    have hwE' : c'.nreg wE = mEdge J dE := by
      rw [hwE, hψE]; unfold mEdge; grind
    have heE : ztljz % M.W.n = eE := add_dOf b₁_lt hee
    have hy := (Restore.arc_abs_lt hP₁ hNF hFne hal).2
    obtain ⟨hPW, hoffE⟩ := wend_map (P := P) hP hdE hgE heE hpe hy
    refine ztgof
    · rw [hwE', hwH]
      refine ⟨hPW, ?_, Or.inr ?_⟩
      · rw [hoffE, hoL]
        rcases eq_or_lt_of_le hkdE with h1 | h1
        · zvmwp at hlt0 ⊢; linarith
        · have := ψ_step h1 hgap0
          have : (ψ J ztcvy : ℝ) + 1 ≤ ψ J dE := by exact_mod_cast this
          linarith
      · rw [hoffE]
        refine wend_cut hdE heE htE0 htE1.le hcutE hgE (fun h0' => have h0 : tE = 0 := h0'; ztcg) (hdn _ hdE)
        · have : (kd J e : ℝ) + t₀ < dE := by_grind
          have : (0 : ℝ) < dE := by_grind
          zufc
        · intro he0
          have hpos : M.pos zta (N₁.arc a).e = M.W.vtx eE := by
            rw [win_pos_eq_sidePt, ← htEd, h0]; exact Chazelle.Chain.sidePt_zero _ _
          rw [hpos, he0, Restore.chain_box_vtx_abs J.left by_norm_num] at hy
          grind
        · intro hδ
          by_cases h1 : dE < lL1 J
          · omega
          · right
            have : ¬ kd J e < lL1 J := fun h2 => hncl ⟨hδ, h2, by_omega⟩
            grind
    · zulki
      rw [hwE', hwH, hoffE] at hle'
      zudoi

      exact cov d t hv.1 ht0 ht1 hb (Or.inl (lex_le hgE ht0 ht1 htE0 htE1 by_linarith))
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep ShotList
open Chazelle.Chain (sideInArc sidePt SideAttach)
@[expose] public section
def cntS : Stmt := .instr (.loadN wCh ztea)

/-- **The window computation.** -/
def win : Stmt := .seq wKeyS (.seq locS (.seq arcS (.seq cntS (.seq bodyS gatherS))))

/-- The cost factor of the window (`D` the degree bound of `N₁`). -/
def κW (D : ℕ) : ℕ := 30000 + 22062 * ztef
theorem DecOut.congr {J : Merge.Junction} {Pw : Prop} {d₀ eE hE : ℕ} {c c' : Config}
    (h : DecOut J Pw d₀ eE hE c) (hX : c'.nreg wX = c.nreg wX) (hE' : c'.nreg wE = c.nreg wE)
    (hH : c'.nreg wH = c.nreg wH) : DecOut J Pw d₀ eE hE c' := by
  unfold DecOut at *; simp_all
theorem gatherK_single_le {M : Model} {Q : Polygon} {N : NF} (hM : WalkAx M) (hNF : IsNF M Q N)
    {D : ℕ} (hD : M.DegLe ztdu D) {r : ℕ} (hr : r < N.nRegions) :
    gatherK N [r] ≤ 33 + 22062 * ztef := by
  have := Restore.region_arcs_le hM hNF hD hr
  simp only [gatherK, SweepIo.regK, arcK, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  nlinarith
theorem cost_aux (T A : ℕ) (hAT : A ≤ A * ztxz) : 12 + (ztxur + (16 + (1 +
    (22100 + ((33 + A) + 10))))) ≤ 30000 * (T + 1) + A * (T + 1) := by_omega
theorem win_cost (T D : ℕ) : 12 + (ztxur + (16 + (1 + (22100 +
    ((33 + 22062 * ztef) + 10))))) ≤ κW D * (T + 1) := by
  unfold κW; grind
theorem win_room_body {a a' W K T G : ℕ} (hroom : a + K ≤ W)
    (hc : 12 + (ztxur + (16 + (1 + (22100 + G)))) ≤ K) (ha : a' = a) :
    a' + 22100 ≤ W := by_omega
theorem wr_of_gathW {q : ℕ} (h : GathW q) : WR q := by
  unfold GathW GSet at h; unfold WR
  have e1 : sw 1004 = 241004 := rfl
  have e2 : sw 1021 = 241021 := rfl
  have e3 : sw 700 = 240700 := rfl
  have e4 : sw 2200 = 242200 := rfl
  have e5 : sw 2420 = 242420 := rfl
  have e6 : sw 2425 = 242425 := rfl
  have e7 : gL = 241001 := rfl
  have e8 : gC = 241002 := rfl
  have e9 : gNF = 241000 := rfl
  have e10 : wGB = 242420 := rfl
  have e11 : wGK = 242421 := rfl
  omega
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **Task C1: the window.** -/
theorem winTask : WinTask := by
  refine ⟨win, κW, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hpw hL hroom
  zujzu
  zucwa

  zucdy
  zuc
  have hcost0 := win_cost ztdg zto
  generalize hKdef : κW zto * ztgf = K at hroom hcost0 ⊢
  have hcost : 12 + (ztxuq + (16 + (1 + (22100 +
      ((33 + 22062 * ztyem) + 10))))) ≤ K := hcost0
  have hn₁ : ztixq := by rw [win_n₁_eq]; omega
  refine IRS.mono (IRS.seq (wKeyS_irs (P := P) hI E.hM hpw.1 hP E.hWn hkdE) ?_) hcost ztb
  rintro c₁ hI₁ - - ⟨v1D, v1E, o1, m1⟩
  have a1 : c₁.nreg ALLOC = c.nreg ALLOC := o1 _ (by rne) (by rne)
  have k1H : c₁.nreg kH = c.nreg kH := o1 _ (by rne) (by rne)
  have hpx1 : ProperPos ztbw zta P.n ztrbu := by
    rw [v1E, k1H]
    exact ⟨by zvokb; exact hpw.2.1.1, by zvokb; exact hpw.2.1.2.1, hpw.2.1.2.2⟩
  -- double identification
  refine IRS.seq (locS_irs E hI₁ (by rw [v1E]; exact Nat.mod_lt _ hn₁) hpx1 by_omega) ?_
  rintro c₂ hI₂ - - ⟨ho2, hl1, hl2, k2, m2⟩
  have e2 : ∀ q, 240000 ≤ q → q < 250000 → q ≠ wO → c₂.nreg q = c₁.nreg q := fun q h1 h2 h3 =>
    k2 q ztsg h3
  have a2 : ztbae := by
    rw [k2 _ by_decide (by rne), a1]
  -- the located arc
  have hNT := win_nt E hI₂
  have hNA : NFAt c₂.nmem (c₂.nreg ztea) N₁ := hNT.nfAt
  zucvt

  obtain ⟨-, -, hTB, -⟩ := win_tab E hI₂
  have hAW : c₂.nreg ALLOC ≤ W := hI₂.hw.1 _
  have hAc := hI₂.hA
  refine IRS.seq (arcS_irs hI₂ (E.hK.fix hI₂) hNF hNA by_omega by_omega by_omega ho2) ?_
  rintro c₃ hI₃ - - ⟨r1, r2, r3, r4, k3, m3⟩
  have e3 : ∀ q, 240000 ≤ q → q < 250000 → q ≠ wO → q ≠ wT → q ≠ wA → q ≠ wR → q ≠ wEE →
      q ≠ wEH → c₃.nreg q = c₁.nreg q := fun q h1 h2 h3 h4 h5 h6 h7 h8 => by
    grind
  have eO3 : c₃.nreg wO = c₂.nreg wO := k3 _ (by rne) (by rne) (by rne) (by rne) (by rne)
  -- the chord count
  refine IRS.seq (win_irs_load hI₃ (iscr_sw' (i := 3012) by_norm_num by_norm_num)) ?_
  zufmc
  have e4 : ∀ q, (q = wE1 ∨ q = kH ∨ q = wD) → c₄.nreg q = c₁.nreg q := by
    zuco
    have hq' : 240000 ≤ q ∧ q < 250000 ∧ q ≠ wO ∧ q ≠ wT ∧ q ≠ wA ∧ q ≠ wR ∧ q ≠ wEE ∧
        q ≠ wEH ∧ q ≠ wCh := by
      rcases hq with h | h | h <;> subst h <;>
        simp only [sw, wE1, kH, wD, wO, wT, wA, wR, wEE, wEH, wCh] <;> omega
    grind
  have hE4 : c₄.nreg wE1 = ke₁ J ztwe := by_grind
  have hH4 : c₄.nreg kH = c.nreg kH := by_grind
  have hD4 : c₄.nreg wD = kd J ztwe := by_grind
  have hO4 : c₄.nreg wO = c₂.nreg wO := by rw [k4 _ (by rne), eO3]
  have s3 : c₃.nreg ztea = c₂.nreg ztea :=
    k3 _ (by rne) (by rne) (by rne) (by rne) (by rne)
  have hch : c₄.nreg wCh = N₁.chords.length := by rw [v4, s3, m3]; exact hNA.1
  have a4 : ztgul := by
    rw [k4 _ (by rne), k3 _ (by rne) (by rne) (by rne) (by rne) (by rne), a2]
  zudor
  -- the body
  have hpx4 : ProperPos ztbw zta P.n ztgot := by
    grind
  have h6x : c₄.nreg kH = 0 → 6 ≤ c₄.nreg wE1 := by
    rw [hE4, hH4]; exact key6 hP hpw hL
  have hkey : (ztgot : WPos) = ztrbu := by
    grind
  have hl1' := hl1
  have hl2' := hl2
  rw [← hkey, ← hO4] at hl1' hl2'
  have har4 : ArcRegs N₁ c₄ (c₄.nreg wO) := by
    rw [hO4]
    zudfi
    · rw [k4 _ (by rne), r1]
    · rw [k4 _ (by rne), r2]
    · rw [k4 _ (by rne), r3]
    · rw [k4 _ (by rne), r4]
  have hnoA : bandOf ALLOC ∉ oracleBands := fun h => alloc_not_io ztwbd
  have hwA : ¬ WR ALLOC := by unfold WR ALLOC sw; omega
  refine IRS.seq (bodyS_irs E hI₄ (by rw [hE4]; exact Nat.mod_lt _ hn₁) hpx4 h6x
    by_omega har4 hl1' hl2' hch (win_room_body hroom hcost a4)) ?_
  rintro c₅ hI₅ - - ⟨o', ho', ⟨w1, w2, w3, w4⟩, hne5, hemp5, k5, m5⟩
  have hR : c₅.nreg wR < N₁.nRegions := by
    rw [w2]; exact (arc_mem_region hNF (NFLoc.seq_lt hNF ho')).1
  have a5 : ztizp := by rw [k5 _ hnoA hwA, a4]
  have hGM : GoodModel ztbw := Or.inl ⟨J.left, hP₁, rfl⟩
  have hgk := gatherK_single_le ztqyo hNF E.hdeg₁ hR
  refine (gatherS_irs E hI₅ hR by_omega).mono by_omega ?_
  rintro c₆ ⟨g1, g2, g3, g4, g5, g6⟩
  have ng : ∀ q, ztkcu → ¬ GathW q := by
    intro q hq h'
    unfold GathW GSet at h'
    rcases hq with h | h | h <;> subst h <;>
      simp only [wX, wE, wH, gL, gC, gNF, wGB, wGK, sw] at h' <;> omega
  have kg : ∀ q, ztkcu → c₆.nreg q = c₅.nreg q := by
    zuco
    have h1 : 240000 ≤ q ∧ q < 250000 ∧ q ≠ ALLOC := by
      rcases hq with h | h | h <;> subst h <;> simp only [wX, wE, wH, ALLOC, sw] <;> omega
    exact g6 q (not_oracle_sw h1.1 h1.2.1) (ng q hq) h1.2.2
  have hx4 : (chainModel J.left).key zta ztgot =
      (chainModel J.left).key zta ztyxu := by_grind
  have hu4 : (ztgot : WPos) = ztyxu := by
    grind
  rw [hx4, hu4, hD4] at hne5
  obtain ⟨wm1, wm2, wm3⟩ := win_math E hpw hL ho' (c' := c₆)
    (fun hF => ⟨(hne5 hF).1, (hne5 hF).2.congr ztocg ztocg ztocg⟩)
    (fun hF => by rw [kg _ by_simp]; grind)
    by_grind
  rw [← w2] at wm3
  refine ⟨[c₅.nreg wR], by_simp, fun r hr => by rw [List.mem_singleton.1 hr]; exact hR, g2,
    by omega, g3, g4, wm1, wm2, wm3, fun a ha => ?_, fun r hr hw hra => ?_⟩
  · rw [g5 a by_omega, m5, hm4]
  · rw [g6 r hr (fun h => hw (wr_of_gathW h)) hra, k5 r hr hw,
      k4 r ztbjq,
      k3 r ztbjq ztbjq
        ztbjq ztbjq
        ztbjq,
      k2 r hr ztbjq,
      o1 r ztbjq ztbjq]
end
end SweepEv
@[expose] public section
open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Merge (FreeAt)
open WalkEmbed
namespace Sweep
section Origin
variable {J : Merge.Junction}

/-- **The point of the start key** (offset `Lst`) is the shared vertex. -/
theorem start_key_pt (hP : J.P.Simple) :
    sidePt (chainModel J.whole).W ztwks 0 = J.shared := by
  zumh
  zucz
  zudpt
  zuhte
  · obtain ⟨hv, -, hτ, hL⟩ := caseB_facts J hlt
    have e : ztxtn := by
      zufqd

    rw [e, (sidePt_top_copies J.whole).2, shared_eq_top J hv]
  · have hlo : ztflb := by
      zuhbs
      · zuilj
      · zuhtx
    have := start_pt J hP
    rw [add_zero, Nat.mod_eq_of_lt by_omega, ← gL_eq J, hlo] at this
    omega

/-- **A position whose point is in the domain of `C₂` is strictly beyond the start.** -/
theorem Lst_lt_of_dom (hP : J.P.Simple) {p : ℕ} {t : ℝ} (hp : p < (chainModel J.whole).W.n)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hD : sidePt (chainModel J.whole).W p t ∈ J.right.dom) :
    (Lst J : ℝ) < oW J ztk := by
  zumh
  zudpu
  zucwh
  have hvD := fun h =>
    J.right.not_mem_set_of_mem_dom h J.shared_mem_right
  zufae
  zudoy
  zumnv
  zuks

  rcases (show (0 : ℝ) ≤ (D : ℝ) + t by positivity).lt_or_eq with h0 | h0
  · rcases hle.lt_or_eq with hL | hL
    · -- in the open right stretch: not in the domain of `C₂`
      have e : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) _ =
          (D : ℝ) + t := hoW
      exact stretch_not_dom₂ J hP ztzi finite_empty hp ht0 ht1
        ⟨by_simp_all, by zvmwe; exact hL⟩ hD
    · -- at the start key: the shared vertex
      have hDL : D = Lst J := by
        have h1 : (D : ℝ) ≤ Lst J := by_linarith
        have h2 : ztlwv := by_linarith
        have h1' : D ≤ Lst J := by_simp_all
        have h2' : Lst J < D + 1 := by exact_mod_cast h2
        omega
      have ht : ztbhh := by_simp_all
      have hpD : p = ztit % (chainModel J.whole).W.n := by
        rw [← hDL, hDdef, add_dOf hg hp]
      rw [hpD, ht, start_key_pt hP] at hD
      simp_all
  · -- at the base: the shared vertex
    have := sidePt_off_zero J hP ztzi finite_empty hp ht0 ht1
      (show off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) _ = 0
        from hoW.trans h0.symm)
    grind

/-- **The first hit from a valid origin**: the direction is free for `C`, the hit parameter is
positive, the hit point is off the domain of `C` and in the domain of `C₂`, and the points before
it are in the domain of `C`. -/
theorem origin_hit (hP : J.P.Simple) {c : Set Point} (hc : c ∈ Merge.augChords J.right)
    {a : Point} {σ : ℝ} (ha : ztla ∨ ztjm)
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared)
    (hlt : J.whole.hitParam a σ < J.right.hitParam a σ) :
    ztdd ∧ FreeAt J.whole a σ ∧ 0 < J.whole.hitParam a σ ∧
      rayPt a σ zton ∉ J.whole.dom ∧
      (∀ s, 0 < s → s < J.whole.hitParam a σ → rayPt a σ s ∈ J.whole.dom) ∧
      rayPt a σ zton ∈ J.right.dom := by
  zune
  obtain ⟨hfr, ha₂, -, -, -, -⟩ := right_hit_end hc ha
  zuhyp
  obtain ⟨hτ, hwD, hint⟩ := Merge.hit_of_freeAt J.whole ztoct hσ hfree
  obtain ⟨-, -, hint₂⟩ := Merge.hit_of_freeAt J.right ha₂ hσ hfr
  simp_all

/-- A point of the chord from a valid origin, off the domain of `C` and other than the origin, is
the hit point. -/
theorem origin_end (hP : J.P.Simple) {c : Set Point} (hc : c ∈ Merge.augChords J.right)
    {a : Point} {σ : ℝ} (ha : ztla ∨ ztjm)
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared)
    (hlt : J.whole.hitParam a σ < J.right.hitParam a σ) {b : Point}
    (hb : b ∈ Merge.shoot J.whole a σ) (hbD : b ∉ J.whole.dom) (hba : b ≠ a) :
    b = rayPt a σ zton := by
  obtain ⟨-, -, hτ, -, hint, -⟩ := origin_hit hP hc ha haR hav hlt
  unfold Merge.shoot at hb
  refine seg_end hb hbD ztjwm hba
  zugwa
  simp_all

/-- **The chord from a valid origin is not a stop chord.** -/
theorem origin_not_stop (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {c : Set Point} (hc : c ∈ Merge.augChords J.right)
    {a : Point} {σ : ℝ} (ha : ztla ∨ ztjm)
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared) (hat : a ≠ J.right.top)
    (hlt : J.whole.hitParam a σ < J.right.hitParam a σ) :
    ¬ StopChord2 J S₂ ztxc := by
  obtain ⟨-, -, -, -, -, hwR⟩ := origin_hit hP hc ha haR hav hlt
  have key : ∀ b, b ∈ Merge.shoot J.whole a σ → b ∉ J.whole.dom → b ≠ a → b ∈ J.right.dom :=
    fun b hb hbD hba => by rw [origin_end hP hc ha haR hav hlt hb hbD hba]; omega
  have hset : ∀ b, b ∈ J.right.set → b ∉ J.whole.dom := fun b hb hd =>
    J.whole.not_mem_set_of_mem_dom hd (J.right_set_subset hb)
  rintro ((⟨σ', -, -, he⟩ | ⟨c', hc', b, σ', hb, hbR, -, he⟩) | ⟨σ', -, -, he⟩)
  · have hm : J.shared ∈ Merge.shoot J.whole a σ := by zvmxm; exact origin_mem J
    exact J.right.not_mem_set_of_mem_dom
      (key _ hm (hset _ J.shared_mem_right) (Ne.symm hav)) J.shared_mem_right
  · have hm : ztrfx := by zvmxm; exact origin_mem J
    have hbD : b ∉ J.whole.dom := by
      zuejt
      · exact (end_not_mem_dom J hS₂ hc').1
      · exact (end_not_mem_dom J hS₂ hc').2
    have hbR' := key b hm hbD by_grind
    obtain ⟨y, l, r, hH, -, -, hl, hr⟩ := Merge.augChords_spec zthxv
    zuejt
    · zvnen at hbR'; exact hH.left_not hbR'
    · zvnel at hbR'; exact hH.right_not hbR'
  · have hm : J.right.top ∈ Merge.shoot J.whole a σ := by zvmxm; exact origin_mem J
    exact J.right.not_mem_set_of_mem_dom
      (key _ hm (hset _ J.right.top_mem_set) (Ne.symm hat)) J.right.top_mem_set

/-- **The attachment of the chord from a valid origin at its hit point**, beyond the start, not
at the shared vertex. -/
theorem origin_attach (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) {c : Set Point} (hc : c ∈ S₂)
    {a : Point} {σ : ℝ} (ha : ztla ∨ ztjm)
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared)
    (hlt : J.whole.hitParam a σ < J.right.hitParam a σ) :
    ∃ (p : ℕ) (t : ℝ), p < (chainModel J.whole).W.n ∧ 0 ≤ t ∧ t < 1 ∧
      SideAttach (chainModel J.whole).W ztxc p t ∧
      sidePt (chainModel J.whole).W p t = rayPt a σ zton ∧
      (Lst J : ℝ) < oW J ztk ∧ sidePt (chainModel J.whole).W p t ≠ J.shared := by
  obtain ⟨-, hfree, -, hwD, -, hwR⟩ := origin_hit hP ztbac ha haR hav hlt
  zunw
  zuixw
  have hadm := F₂plus_subset J hS₂ he
  have hw : rayPt a σ _ ∈ Merge.shoot J.whole a σ :=
    Geometry.right_mem_segment _ _
  obtain ⟨p, t, hA, hpt⟩ := endpoint_attach hM hadm hw hwD
  refine ⟨p, t, hA.1, hA.2.1, hA.2.2.1, hA, hpt,
    Lst_lt_of_dom hP hA.1 hA.2.1 hA.2.2.1 by_simp_all, fun h => ?_⟩
  zukvs
  zvmwc at hwR
  exact J.right.not_mem_set_of_mem_dom hwR J.shared_mem_right

/-- **A chord of `C₂` is determined by an end and the direction along it.** -/
theorem chord_of_end {c c' : Set Point} (hc : c ∈ Merge.augChords J.right)
    (hc' : c' ∈ Merge.augChords J.right) {a : Point} {σ : ℝ}
    (ha : ztla ∨ ztjm)
    (ha' : (σ = 1 ∧ a = Merge.lend c') ∨ (σ = -1 ∧ a = Merge.rend c')) : c = c' := by
  obtain ⟨-, -, -, hR, -, -⟩ := right_hit_end hc ha
  obtain ⟨-, -, -, hR', -, -⟩ := right_hit_end hc' ha'
  obtain ⟨y, l, r, -, -, rfl, hl, hr⟩ := Merge.augChords_spec hc
  obtain ⟨y', l', r', -, -, rfl, hl', hr'⟩ := Merge.augChords_spec hc'
  grind

/-- **The chord from a valid origin determines the origin, the direction and the chord of `C₂`.** -/
theorem origin_inj (hP : J.P.Simple) {c c' : Set Point} (hc : c ∈ Merge.augChords J.right)
    (hc' : c' ∈ Merge.augChords J.right) {a a' : Point} {σ σ' : ℝ}
    (ha : ztla ∨ ztjm)
    (ha' : (σ' = 1 ∧ a' = Merge.lend c') ∨ (σ' = -1 ∧ a' = Merge.rend c'))
    (haR : a ∈ J.right.set) (hav : a ≠ J.shared)
    (hlt : J.whole.hitParam a σ < J.right.hitParam a σ)
    (ha'R : a' ∈ J.right.set) (ha'v : a' ≠ J.shared)
    (hlt' : J.whole.hitParam a' σ' < J.right.hitParam a' σ')
    (heq : Merge.shoot J.whole a σ = Merge.shoot J.whole a' σ') :
    a = a' ∧ σ = σ' ∧ c = c' := by
  obtain ⟨hσ, -, hτ, hwD, -, hwR⟩ := origin_hit hP hc ha haR hav hlt
  obtain ⟨hσ', -, hτ', -, -, hwR'⟩ := origin_hit hP hc' ha' ha'R ha'v hlt'
  have haD := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd ztmbj
  -- the origins
  have haa : ztsdh := by
    zuct
    have hm : a ∈ Merge.shoot J.whole a' σ' := by zvnbo; exact origin_mem J
    have := origin_end hP hc' ha' ha'R ha'v hlt' hm haD hne
    zvnnr at hwR'
    exact J.right.not_mem_set_of_mem_dom hwR' haR
  subst haa
  -- the directions: the hit points coincide
  have hwa : rayPt a σ _ ≠ a := fun h => by
    zvmwc at hwR; exact J.right.not_mem_set_of_mem_dom hwR haR
  have hm : rayPt a σ zton ∈ Merge.shoot J.whole a σ' := by
    zvnbo; exact Geometry.right_mem_segment _ _
  have hww := origin_end hP hc' ha' ha'R ha'v hlt' hm hwD hwa
  have h1 := congrArg Prod.fst hww
  zuimk
  have hσσ : σ = σ' := by
    zuzq
    · rfl
    · nlinarith
    · nlinarith
    · rfl
  subst hσσ
  exact ⟨rfl, rfl, chord_of_end hc hc' ha ha'⟩

/-- The chord of an endpoint query and the position of its origin on it. -/
theorem query_chord {Q : Polygon} {N : NF} {j : ℕ} (hj : j < 2 * N.nChords) :
    (N.chord ztwm).toSet ztj Q ∈ N.F ztj Q ∧
      ((endDir j = 1 ∧ endOrigin J Q N j =
          Merge.lend ztwqa) ∨
        (endDir j = -1 ∧ endOrigin J Q N j =
          Merge.rend ztwqa)) := by
  zufux
  refine ⟨⟨N.chord _, ?_, rfl⟩, ?_⟩
  · zudly
    zukpu
    grind
  · unfold endDir endOrigin
    grind
end Origin

/-- **Task O: the chord seen from a valid origin.** -/
theorem originTask : SweepEv.OriginTask := by
  intro J Q N hP hN _hF
  have hS₂ : N.F _ Q ⊆ Merge.augChords J.right := hN.1.2.1
  refine ⟨fun j hj haR hav hat hlt => ?_, fun j j' hj hj' haR hav _hat hlt haR' hav' _hat' hlt'
    heq => ?_⟩
  · zuhhq
    exact ⟨origin_not_stop hP hS₂ ztbac ha haR hav hat hlt,
      origin_attach hP hS₂ hc ha haR hav hlt⟩
  · zuhhq
    obtain ⟨hc', ha'⟩ := query_chord hj'
    obtain ⟨-, hσ, hcc⟩ := origin_inj hP ztbac zthxv ha ha' haR hav hlt haR' hav' hlt' heq
    have hk := hN.2.1 _ _ by_omega by_omega hcc
    have hpar : j % 2 = j' % 2 := by
      have e1 := (endOrigin_eq J hN hj).2
      have e2 := (endOrigin_eq J hN hj').2
      grind
    omega
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
theorem fin_rd (c : Config) : rd ztgiq bSweep 200 = c.nreg sB ∧
    rd ztgiq bSweep 201 = c.nreg sC ∧ rd ztgiq bSweep 300 = c.nreg lB ∧
    rd ztgiq bSweep 301 = c.nreg lC ∧ rd ztgiq bSweep 302 = c.nreg cTB ∧
    (finCfg c).nmem = c.nmem := by
  tauto
section done
variable {P : Polygon} {J : Merge.Junction} {N₁ N₂ : NF} {c₀ c cw cs co c' : Config}

/-- **The registers kept by the iteration** (window, reset, batch; the next key in its
no-candidate case is handled by the caller). -/
theorem done_iter_keep (hIt : IterRel P J N₁ N₂ c cw cs co c') {r : ℕ} (hr : 240000 ≤ r ∧ r < 250000)
    (hW : ¬ WR r) (hb : r ≠ bF ∧ r ≠ bN) (hO : ¬ OrgR r) (hL : ¬ LR r) :
    co.nreg r = c.nreg r := by
  obtain ⟨⟨rs, -, -, -, -, -, -, -, -, -, -, hWr⟩, -, ⟨-, -, -, hRr⟩, ⟨hBr, -, -⟩, -⟩ := hIt
  zucvq
  rw [hBr r ztqdw hO hL hA, hRr r hb.1 hb.2, hWr r ztqdw hW hA]

/-- **The memory kept by the iteration**, below the allocator of `c` and outside the table. -/
theorem done_iter_mem (hIt : IterRel P J N₁ N₂ c cw cs co c')
    (hT : c.nreg cTB = c₀.nreg cTB) (hT' : cs.nreg cTB = c₀.nreg cTB) {x : ℕ}
    (hx : x < c.nreg ALLOC) (hxT : x < c.nreg cTB ∨ c.nreg cTB + 6 * N₂.nChords ≤ x) :
    co.nmem x = c.nmem x := by
  obtain ⟨⟨rs, -, -, -, -, -, -, -, -, -, hWm, hWr⟩, hAw, ⟨hRm, -, -, hRr⟩, ⟨-, -, A, hB⟩, -⟩ :=
    hIt
  have hAs : ztfkw := hRr ALLOC by_decide
    by_decide
  rw [hB.memT x by_omega by_omega, hRm, hWm x hx]
end done
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)
@[expose] public section
section done
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {J : Merge.Junction} {N₁ N₂ : NF} {c₀ c cw cs co c' : Config}
set_option maxHeartbeats 8000000 in
/-- **The outputs of the last iteration.** -/
theorem done_out (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hL : LoopInv P J N₁ N₂ c₀ c)
    (hIt : IterRel P J N₁ N₂ c cw cs co c') (hd : c'.nreg dF = 1)
    (hnc : NoCutIn J ztwis ztbnc
      (chainModel J.whole).W.n) :
    Out P J N₂ ztjvd ∧ c'.nreg lC ≤ logCap N₁ N₂ := by
  set S₂ := N₂.F ztj zta with hS₂def
  have hIt' := hIt
  obtain ⟨⟨rs₀, -, -, -, -, -, -, -, -, -, hWm, hWr⟩, hAw, ⟨hRm, -, -, hRr⟩,
    ⟨hBfr, hBA, A, hB⟩, hK⟩ := hIt'
  -- the no-candidate case of the next key
  have hnone : co.nreg bF ≠ 1 ∧ ¬ co.nreg sP < co.nreg sC ∧ co.nreg wX ≠ 0 := by
    zumv
    have h' : co.nreg bF = 1 ∨ co.nreg sP < co.nreg sC ∨ co.nreg wX = 0 := by_tauto
    have := (hK.2.2.2 h').1
    omega
  obtain ⟨-, hlC, hmK⟩ := hK.2.2.1 hnone
  -- registers
  have keepK : ∀ r, 240000 ≤ r ∧ r < 250000 → ¬ KR r → c'.nreg r = co.nreg r := fun r hr hk =>
    hK.1 r ztqdw hk ztu
  have eSB : ztiyz := by
    rw [keepK _ by_decide zthub]
    exact done_iter_keep hIt by_decide (by unfold WR sB sw; omega)
      ⟨by_decide, by_decide⟩
      (by unfold OrgR CandR BestR LblR sB bF bE bH bN bL sw; omega) (by unfold LR oK oS sB sw; omega)
  have eSC : ztmum := by
    rw [keepK _ by_decide zthuc]
    exact done_iter_keep hIt by_decide (by unfold WR sC sw; omega)
      ⟨by_decide, by_decide⟩
      zthfs (by unfold LR oK oS sC sw; omega)
  have eLB : ztgue := by
    rw [keepK _ by_decide zthua]
    exact done_iter_keep hIt by_decide (by unfold WR lB sw; omega)
      ⟨by_decide, by_decide⟩
      (by unfold OrgR CandR BestR LblR lB bF bE bH bN bL sw; omega) (by unfold LR oK oS lB sw; omega)
  have eTB : ztgud := by
    rw [keepK _ by_decide zthtz]
    exact done_iter_keep hIt by_decide ztnvm
      ⟨by_decide, by_decide⟩
      ztdgz
      (by unfold LR oK oS cTB sw; omega)
  have eLC : c'.nreg lC = c.nreg lC := by
    rw [hlC]
    exact done_iter_keep hIt by_decide (by unfold WR lC sw; omega)
      ⟨by_decide, by_decide⟩
      (by unfold OrgR CandR BestR LblR lC bF bE bH bN bL sw; omega) (by unfold LR oK oS lC sw; omega)
  have eTBs : ztguj := by
    rw [hRr _ by_decide by_decide,
      hWr _ ztbur ztnvm
        by_decide]
  have hT0 : ztsfb := by rw [hL.tab0, E.hTA]
  -- the allocators
  have hAs : ztfkw := hRr ALLOC by_decide
    by_decide
  have hAco : c.nreg ALLOC ≤ co.nreg ALLOC := by_omega
  -- the memory outside the table
  have memC : ∀ x, x < c.nreg ALLOC → (x < c.nreg cTB ∨ c.nreg cTB + 6 * N₂.nChords ≤ x) →
      c'.nmem x = c.nmem x := fun x hx hxT => by
    rw [hmK x by_omega]
    exact done_iter_mem hIt hT0 by_omega hx hxT
  -- the layout
  have l1 := hL.lay1
  have l2 := hL.lay2
  have l4 := hL.lay4
  -- the size of the log
  obtain ⟨-, hcnt⟩ := countTask P J N₁ N₂ E.hP E.hNF₁ E.hNF₂
  have hmeas := hL.meas
  have hcap : c.nreg lC ≤ logCap N₁ N₂ := by
    have : ztdap := hcnt
    unfold logCap; omega
  -- the table
  set T := c.nreg cTB with hTdef
  have tabF : ∀ j, j < 2 * N₂.nChords →
      c'.nmem ztctp ≤ 1 ∧
      (c'.nmem ztctp = 1 → CandOK P J S₂ ztwka ztri
        (c'.nmem zteog) (c'.nmem zteoh)) ∧
      (c.nmem ztctp = 1 → c'.nmem ztctp = 1) := by
    zun
    have hTA : T + 3 * j + 2 < c.nreg ALLOC := by_omega
    have mc : ∀ x, x ≤ T + 3 * j + 2 → c'.nmem x = co.nmem x := fun x hx => hmK x by_omega
    have ms : ∀ x, x ≤ T + 3 * j + 2 → cs.nmem x = c.nmem x := fun x hx => by
      grind
    obtain ⟨t0, t1, -⟩ := hL.tab j hj
    rcases hB.slot j hj with ⟨s0, s1, s2⟩ | ⟨e, h, hA, s0, s1, s2⟩
    · grind
    · rw [eTBs] at s0 s1 s2
      rw [mc _ by_omega, s0, mc _ by_omega, s1, mc _ by_omega, s2]
      exact ⟨le_rfl, fun _ => (hB.acc _ hA).2.2, fun _ => rfl⟩
  -- the parts of the output
  obtain ⟨rs, ax, hrl, -, hsr, -, hsok, hsw, -, -⟩ := hL.stops
  obtain ⟨ls, hll, hlr, hlw, hlp, hlast⟩ := hL.log
  obtain ⟨f200, f201, f300, f301, f302, fm⟩ := fin_rd c'
  refine ⟨⟨rs, ls, ?_, ?_, hsok, hsw, ?_, ?_, ?_, hlw, ?_, ?_⟩, by_omega⟩
  · omega
  · rw [fm, f200, eSB]
    zug
    have hiS : ztizv := by_omega
    obtain ⟨a0, a1, a2, a3, a4⟩ := hsr i hi
    zuflw
    · zugwf
    · zugwg
    · zugwh
    · zugwi
    · zugwj
  · omega
  · rw [fm, f300, eLB]
    zug
    have hiL : i < c.nreg lC := by_omega
    have hlog : c.nreg lB + 7 * c.nreg lC ≤ c.nreg ALLOC := by_omega
    obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := hlr i hi
    refine ztuv
    · zugwf
    · zugwg
    · zugwh
    · zugwi
    · zugwj
    · zuogi; exact a5
    · zuogi; exact a6
  · -- the log
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hlp
    refine ⟨p1, p2, p3, p4, p5, fun x hx => ?_, p6⟩
    unfold logOf at hx
    rw [List.getLast?_map, hlast] at hx
    simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hx
    zultk
    tauto
  · -- the table
    zuihy
    intro j hj haR hav hat
    obtain ⟨hc, ha⟩ := query_chord (J := J) (Q := Qof P) (N := N₂) hj
    have hS₂sub : ztgap := E.hNF₂.1.2.1
    obtain ⟨hfr, ha₂, -, -, -, -⟩ := right_hit_end (hS₂sub hc) ha
    have hfree := whole_free_end E.hP haR hav hfr
    obtain ⟨g0, g1, g2⟩ := tabF j hj
    zuknu
    unfold tabOf
    split_ifs with hf
    · obtain ⟨-, -, hatt, hpt, hLst, -, -⟩ := g1 hf
      grind
    · have hσ : endDir j = 1 ∨ endDir j = -1 := by
        grind
      have haw : (endOrigin J zta N₂ j).2 ≤ J.whole.top.2 := le_trans ha₂ J.right_top_le
      have hle : J.whole.hitParam ztwka ztri ≤
          J.right.hitParam ztwka ztri := by
        rw [whole_hitParam_eq_min J haw hσ, ← right_hitParam_eq J ha₂]
        simp
      refine le_antisymm hle (not_lt.1 fun hlt => ?_)
      obtain ⟨-, p, t, hp, ht0, ht1, hatt, hpt, hLst, -⟩ :=
        (originTask J zta N₂ E.hP E.hNF₂ ztpza).1 j hj haR hav hat hlt
      by_cases ho : oW J ztk ≤ keyOff P J c
      · exact hf (g2 ((hL.tab j hj).2.2 ztrcv hlt p t hatt hpt hLst ho))
      · have hpn : (p : ℝ) + t < (chainModel J.whole).W.n := by
          have : (p : ℝ) + 1 ≤ (chainModel J.whole).W.n := by exact_mod_cast hp
          linarith
        refine hnc ztk ⟨_, shoot_end_mem hc ha hfree, p, t, hatt, rfl⟩ by_positivity hpn
          ⟨lt_of_not_ge ho, ?_⟩
        exact off_lt hpn ztdlc
  · -- the table words
    zuihy
    zun
    obtain ⟨g0, g1, -⟩ := tabF j hj
    exact ⟨g0, fun h => (g1 h).2.2.2.2.2.1⟩
end done
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
def DoneNoCut : Prop :=
  ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (P : Polygon) (W : ℕ) (c₀ : Config) (J : Merge.Junction) (N₁ N₂ : NF)
    (c cw cs co c' : Config), EvEnv sh Bs F X Ok P W c₀ J N₁ N₂ →
    LoopInv P J N₁ N₂ c₀ c → IterRel P J N₁ N₂ c cw cs co c' → c'.nreg dF = 1 →
    NoCutIn J ztwis ztbnc (chainModel J.whole).W.n

/-- **Task L2 from the absence of cuts after the last key.** -/
theorem doneTask_of (h : DoneNoCut) : DoneTask := by
  zucnj
  exact done_out E hL hIt hd (h sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' E hL hIt hd)
open Chazelle.Chain (SideAttach sidePt)
theorem start_key_ge_six (J : Merge.Junction) :
    6 ≤ ztit % (chainModel J.whole).W.n := by
  zuhf
  zudpt
  zuhte
  · obtain ⟨-, -, hτ, hL⟩ := caseB_facts J hlt
    zudpu
    have e : ztxtn := by
      zufqd

    omega
  · have hlo : ztflb := by
      zuhbs
      · zuilj
      · zuhtx
    rw [← hlo, gL_eq]
    omega

/-- **Task S (mathematics): the start key.** -/
theorem startMathTask : StartMathTask := by
  intro P J N hP hN
  have hS₂ : N.F ztj zta ⊆ Merge.augChords J.right := hN.1.2.1
  refine ⟨⟨Nat.mod_lt _ (by have := Lst_lt_n J; omega), ShootCut.proper_vtx _ _ _ _,
    fun _ => start_key_ge_six J⟩, oW_start J hP (S₂ := ∅) (empty_subset _) finite_empty, ?_⟩
  zumgq
  have hvD : ztpkm := fun hd =>
    J.whole.not_mem_set_of_mem_dom hd ztffl
  have hmem : J.shared ∈ e := by
    have := hA.2.2.2.1
    rwa [start_key_pt hP] at this
  obtain ⟨σ, hσ, hfree, heq⟩ :=
    chord_eq_shoot_of_end J.whole ztfnm hmem hvD
  exact Or.inl ztkqg
open Chazelle.Visibility (hseg)
noncomputable def hPolyS (F : Set ztf) (hfin : F.Finite) : Polygon :=
  ⟨hfin.toFinset.toList.map fun c => ztblh⟩
theorem hPolyS_vtx {F : Set ztf} (hfin : F.Finite) {C : Chain} {c : Set Point}
    (hc : c ∈ F) (hcC : c ∈ Merge.augChords C) :
    ∃ h, h < (hPolyS F hfin).n ∧ ∃ a b : ℝ, c = hseg ((hPolyS F hfin).vtx h).2 a b := by
  have hmem : ztblh ∈ (hPolyS F hfin).vertices := by
    simp only [hPolyS]
    exact List.mem_map.2 ztrbe
  zufxx
  obtain ⟨y, a, b, -, -, hcd, hl, -⟩ := Merge.augChords_spec hcC
  refine ztlwd
  have hv : (hPolyS F hfin).vtx h = ztblh := by
    unfold Polygon.vtx
    simp_all
  simp_all

/-- **One polygon for the families `S₂` and `F₂⁺`.** -/
theorem chordFamily_pair (J : Merge.Junction) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) :
    ∃ Q : Polygon, (chainModel J.right).ChordFamily Q S₂ ∧
      (chainModel J.whole).ChordFamily Q ztbi := by
  have hfin := hS₂f.union ztnld
  refine ⟨hPolyS _ hfin, ⟨hS₂f, hS₂, fun c hc => hPolyS_vtx hfin ztjkr ztbac⟩,
    ⟨by_simp_all, F₂plus_subset J hS₂, fun c hc =>
      hPolyS_vtx hfin ztdlf (F₂plus_subset J hS₂ hc)⟩⟩

/-! ## The stop records -/
section Stops
variable {P : Polygon} {J : Merge.Junction} {N₂ : NF}

/-- The offset of a stop record. -/
noncomputable def soff (P : Polygon) (J : Merge.Junction) (r : ℕ × ℕ × ℕ × ℕ × ℕ) : ℝ :=
  oW J (r.1 + (chainModel J.whole).param zta ztbhg)
variable {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
theorem stopsOf_getElem {i : ℕ} (hi : i < rs.length) :
    ztwoy[i]'(by zuook) =
      ((rs[i]).1, (chainModel J.whole).param zta zthlw,
        stopSet J zta N₂ (rs[i]).2.2.1 (rs[i]).2.2.2.1 (rs[i]).2.2.2.2) := by
  zumpo

/-- The facts of the stop `i`: its chord, attached at its position, on the `C₁` part. -/
theorem stop_facts
    (hst : StopsOK J ztwis ztwoy) {i : ℕ}
    (hi : i < rs.length) :
    stopSet J zta N₂ (rs[i]).2.2.1 (rs[i]).2.2.2.1 (rs[i]).2.2.2.2 ∈
        F₂plus J ztwis ∧
      StopChord2 J ztwis
        ztwld ∧
      SideAttach (chainModel J.whole).W
        ztwld (rs[i]).1
        ((chainModel J.whole).param zta zthlw) ∧
      (Lst J : ℝ) ≤ soff P J rs[i] := by
  have hi' : i < (stopsOf J zta N₂ rs).length := by zuook
  have h := hst.1 _ (List.getElem_mem hi')
  rw [stopsOf_getElem hi] at h
  zubh

/-- **The stops are sorted by offset.** -/
theorem stops_sorted
    (hst : StopsOK J ztwis ztwoy) {i i' : ℕ}
    (hii : i ≤ i') (hi' : i' < rs.length) :
    soff P J ztfij ≤ soff P J rs[i'] := by
  rcases hii.lt_or_eq with h | rfl
  · zucwj
    have := List.pairwise_iff_getElem.1 hst.2.2.1 i i' by_omega by_omega h
    rw [stopsOf_getElem, stopsOf_getElem] at this
    zufep
  simp

/-- **At most two stops share an offset.** -/
theorem stops_two (hP : J.P.Simple) (hN : IsNF ztj zta N₂)
    {rs : List ztcf}
    (hst : StopsOK J ztwis ztwoy) {i : ℕ}
    (hi : i + 2 < rs.length) :
    soff P J ztfij < soff P J rs[i + 2] := by
  zuinz
  zuhxn

  zuv
  have h01 := stops_sorted hst (i := i) (i' := i + 1) by_omega by_omega
  have h12 := stops_sorted hst (i := i + 1) (i' := i + 2) by_omega by_omega
  zube

  have e01 : soff P J ztfij = soff P J (rs[i + 1]' by_omega) := by_linarith
  have e02 : soff P J ztfij = soff P J rs[i + 2] := by_linarith
  obtain ⟨f0, -, a0, -⟩ := stop_facts hst (i := i) by_omega
  obtain ⟨f1, -, a1, -⟩ := stop_facts hst (i := i + 1) by_omega
  obtain ⟨f2, -, a2, -⟩ := stop_facts hst (i := i + 2) by_omega
  obtain ⟨p01, t01⟩ := pos_eq_of_oW hP hS₂ hS₂f a0.1 a1.1 a0.2.1 a0.2.2.1 a1.2.1 a1.2.2.1 e01
  obtain ⟨p02, t02⟩ := pos_eq_of_oW hP hS₂ hS₂f a0.1 a2.1 a0.2.1 a0.2.2.1 a2.2.1 a2.2.2.1 e02
  -- the chords are pairwise distinct (no duplicate stops)
  zucwj
  have hnd := hst.2.2.2
  have dist : ∀ a b (ha : a < rs.length) (hb : b < rs.length), a ≠ b →
      (rs[a]).1 = (rs[b]).1 →
      (chainModel J.whole).param zta ⟨(rs[a]).1, (rs[a]).2.1⟩ =
        (chainModel J.whole).param zta ⟨(rs[b]).1, (rs[b]).2.1⟩ →
      stopSet J zta N₂ (rs[a]).2.2.1 (rs[a]).2.2.2.1 (rs[a]).2.2.2.2 ≠
        stopSet J zta N₂ (rs[b]).2.2.1 (rs[b]).2.2.2.1 (rs[b]).2.2.2.2 := by
    intro a b ha hb hab h1 h2 h3
    apply hab
    have := (List.Nodup.getElem_inj_iff hnd (hj := by zvnen; exact hb)).1 (by
      rw [stopsOf_getElem ha, stopsOf_getElem hb, h2, h1, h3])
    omega
  have d01 := dist i _ by_omega by_omega by_omega p01 t01
  have d02 := dist i _ by_omega by_omega by_omega p02 t02
  have d12 := dist _ _ by_omega by_omega by_omega (p01.symm.trans p02)
    (t01.symm.trans t02)
  rw [← t01, ← p01] at a1
  rw [← t02, ← p02] at a2
  rcases tie_third hC.hM hC.hF f0 f1 f2 d01 a0 a1 a2 with h | h
  · grind
  grind
end Stops

/-! ## Labels -/
theorem evSideLab_mono {J : Merge.Junction} {S₂ : Set ztf} {Λ Λ' : Set ztf}
    {Z : Set Point} (h : Λ ⊆ Λ') (hl : EvSideLab J S₂ Λ Z) : EvSideLab J S₂ Λ' Z :=
  fun G hG ρ hρ hS => by
    obtain ⟨L, hL, h2, h3⟩ := hl G hG ρ hρ hS
    exact ⟨L, by_grind, h2, h3⟩

/-- The walk edge of the vertex at the end of the right stretch in the walk of `C₂`. -/
noncomputable def vEnd (J : Merge.Junction) : ℕ :=
  ztwug %
    (chainModel J.right).W.n

/-- The start key. -/
noncomputable def pK0 (J : Merge.Junction) : ℕ := ztit % (chainModel J.whole).W.n

/-! ## The invariant at the start -/
set_option maxHeartbeats 4000000 in
/-- **The invariant at the start key.**  The label set contains the labels of every anchored stop
at the start key; if there is none, it is `{V}` for the region `V` faced before the end of the
right stretch. -/
theorem evInv_start {P : Polygon} {J : Merge.Junction} {N₂ : NF} (hP : J.P.Simple)
    (hN : IsNF ztj zta N₂) {rs ax : List ztcf}
    (hlen : ax.length = rs.length)
    (hst : StopsOK J ztwis ztwoy)
    (haux : ∀ i (hi : i < rs.length), AuxOK P J N₂
      ztwld (ax[i]' by_omega))
    {Λ : Set ztf}
    (hΛ : ∀ i (hi : i < rs.length), soff P J rs[i] = Lst J → (ax[i]' by_omega).1 = 1 →
      labSet J zta N₂ (ax[i]' by_omega).2.1 (ax[i]' by_omega).2.2.1
        (ax[i]' by_omega).2.2.2.1 0 0 ⊆ Λ)
    (hB : (∀ i (hi : i < rs.length), soff P J rs[i] = Lst J → (ax[i]' by_omega).1 ≠ 1) →
      ∃ V ∈ (chainModel J.right).regions ztwis,
        BeforeFaces ztj ztqyg 0 V ∧ Λ = {V}) :
    EvInv J ztwis ztmbm Λ := by
  zueef
  zuhxn

  zuv
  obtain ⟨Q', hQ₂, hQF⟩ := chordFamily_pair J hS₂ hS₂f
  obtain ⟨⟨hpKn, -, -⟩, hoK, hstop⟩ := startMathTask P J N₂ hP hN
  set pK := ztit % (chainModel J.whole).W.n with hpKd
  have hoK' : oW J ztgwf = Lst J := by_omega
  zulin
  -- every chord at the start key is a stop at the start key
  have atKey : ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK 0 →
      ∃ i, ∃ hi : i < rs.length, soff P J rs[i] = Lst J ∧
        stopSet J zta N₂ (rs[i]).2.2.1 (rs[i]).2.2.2.1 (rs[i]).2.2.2.2 = e := by
    zumgq
    have hmem := hst.2.1 e he (hstop e he hA) pK 0 hA by_grind
    obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.1 hmem
    have hk' : k < rs.length := by simpa [stopsOf] using hk
    rw [stopsOf_getElem hk'] at hkx
    simp only [Prod.mk.injEq] at hkx
    obtain ⟨h1, h2, h3⟩ := hkx
    refine ⟨k, hk', ?_, h3⟩
    unfold soff
    grind
  -- a stop at the start key is attached at the start key
  have stopAt : ∀ i (hi : i < rs.length), soff P J rs[i] = Lst J →
      SideAttach (chainModel J.whole).W
        ztwld pK 0 := by
    intro i hi ho
    obtain ⟨-, -, hA, -⟩ := stop_facts hst hi
    have e : soff P J rs[i] = oW J ztgwf := by_grind
    obtain ⟨h1, h2⟩ := pos_eq_of_oW hP hS₂ hS₂f hA.1 hpKn hA.2.1 hA.2.2.1 le_rfl one_pos e
    grind
  by_cases hanc : ∃ i, ∃ hi : i < rs.length, soff P J rs[i] = Lst J ∧ (ax[i]' by_omega).1 = 1
  · obtain ⟨i₀, hi₀, ho₀, ha₀⟩ := hanc
    have hZ := (stop_facts hst hi₀).1
    have hZK := stopAt i₀ hi₀ ho₀
    have hZb : ¬ EvBrk J _ := ((haux i₀ hi₀).2.1).1 ha₀
    rw [← hoK']
    by_cases hpock : ∃ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK 0 ∧
        ∃ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s ∧ oW J ztej = 0
    · zudeh
      have hne : sidePt (chainModel J.whole).W pK 0 ≠ sidePt (chainModel J.whole).W q s := by
        zuq
        zufkp
        grind
      exact evInv_pocket he heK hQ hne by_grind hQ0 Λ
    zujce
    zucuk

    exact evInv_anchor hP hQ₂ hQF (noTieV hP hS₂) hpKn le_rfl one_pos by_grind hZ hZK hZz
      hzL by_omega (fun e he heK hnb _ => by
        obtain ⟨j, hj, hoj, rfl⟩ := atKey e he heK
        have haj := ((haux j hj).2.1).2 hnb
        exact evSideLab_mono (hΛ j hj hoj haj)
          ((haux j hj).2.2.2.2.2.1 haj (hpock _ he heK)))
  · push Not at hanc
    obtain ⟨V, hV, hW, rfl⟩ := hB hanc
    refine startTask J Q' S₂ hP hQ₂ hQF (fun e he hA => ?_) V hV hW
    obtain ⟨j, hj, hoj, rfl⟩ := atKey e he hA
    zuldq
    exact hanc j hj hoj (((haux j hj).2.1).2 hb)
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
@[expose] public section
def zE : ℕ := sw 2480
def zH : ℕ := sw 2481
def zO : ℕ := sw 2482
def aF : ℕ := sw 2484
def zX : ℕ := sw 2485
def zA : ℕ := sw 2486
def zN : ℕ := sw 2487
def zL : ℕ := sw 2488
def zM : ℕ := sw 2489
def zT : ℕ := sw 2490

/-! ## The code -/

/-- Load the position of stop `sP`. -/
def lsStLoad : List Instr :=
  [.addN zX sP sP, .addN zX zX zX, .addN zX zX sP, .addN zX zX sB, .loadN zE zX,
    .addN zX zX K1, .loadN zH zX]

/-- Load the auxiliary record of stop `sP`: anchored flag, count, two labels. -/
def stAux : List Instr :=
  [.addN zX sP sP, .addN zX zX zX, .addN zX zX sP, .addN zX zX aB, .loadN zA zX,
    .addN zX zX K1, .loadN zN zX, .addN zX zX K1, .loadN zL zX, .addN zX zX K1, .loadN zM zX]

/-- The labels of an anchored stop. -/
def stLabs : Stmt :=
  .ifLtN zA K1 .skip (.seq (.instr (.constN aF 1))
    (.seq (.ifLtN K0 zN (addLab kN kL zL) .skip) (.ifLtN K1 zN (addLab kN kL zM) .skip)))

/-- Take the stop `sP`. -/
def stTake : Stmt := .seq (block stAux) (.seq stLabs (.instr (.addN sP sP K1)))

/-- **One stop step.** -/
def stStep : Stmt :=
  .ifLtN sP sC (.seq (block lsStLoad) (.seq (callOff ztjl kE kH zE zH cGW zO)
    (.ifLtN K0 zO .skip stTake))) .skip

/-- The cost of a stop step. -/
def stStepK : ℕ := 12000

/-! ## The blocks -/
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable (m f : ℕ → ℕ) {q : ℕ} {l : List ℕ} {n a b x : ℕ}
theorem stLoad_val (hk1 : f K1 = 1) :
    regB m lsStLoad f zE = m (f sB + 5 * f sP) ∧ regB m lsStLoad f zH = m (f sB + 5 * f sP + 1) := by
  zubx
  simp only [lsStLoad, regB, regI, upd, zX, zE, zH, sP, sB, K1, sw]
  grind
theorem stLoad_other (h1 : q ≠ zX) (h2 : q ≠ zE) (h3 : q ≠ zH) :
    regB m lsStLoad f q = f q :=
  regB_other m lsStLoad f (fun i hi => by
    simp only [lsStLoad, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zvmwd <;> intro h <;> subst h <;> simp_all)
theorem stLoad_ok (hk1 : f K1 = 1) (hb : f sB + 5 * f sP + 1 ≤ W) :
    okB W m lsStLoad f := by
  zubx
  have hb' : f 242600 + 5 * f 242450 + 1 ≤ W := hb
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  simp only [lsStLoad, okB, okI, regI, upd, zX, zE, zH, sP, sB, K1, sw]
  grind
theorem stAux_val (hk1 : f K1 = 1) :
    regB m stAux f zA = m (f aB + 5 * f sP) ∧ regB m stAux f zN = m (f aB + 5 * f sP + 1) ∧
    regB m stAux f zL = m (f aB + 5 * f sP + 2) ∧ regB m stAux f zM = m (f aB + 5 * f sP + 3) := by
  zubx
  simp only [stAux, regB, regI, upd, zX, zA, zN, zL, zM, sP, aB, K1, sw]
  grind
theorem stAux_other (h1 : q ≠ zX) (h2 : q ≠ zA) (h3 : q ≠ zN)
    (h4 : q ≠ zL) (h5 : q ≠ zM) : regB m stAux f q = f q :=
  regB_other m stAux f (fun i hi => by
    simp only [stAux, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      zvmwd <;> intro h <;> subst h <;> simp_all)
theorem stAux_ok (hk1 : f K1 = 1) (hb : f aB + 5 * f sP + 3 ≤ W) :
    okB W m stAux f := by
  zubx
  have hb' : f 242602 + 5 * f 242450 + 3 ≤ W := hb
  have s : ztfu := fun j h1 h2 =>
    iscr_sw by_omega by_omega
  simp only [stAux, okB, okI, regI, upd, zX, zA, zN, zL, zM, sP, aB, K1, sw]
  grind

/-! ## Label lists -/

/-- The labels appended for an anchored stop with `n` labels `a`, `b`. -/
def labAdd (l : List ℕ) (n a b : ℕ) : List ℕ :=
  if 1 < n then addL ztkwk b else ztkwk

/-- The labels of an auxiliary record (if anchored). -/
def axLabs (x : ℕ × ℕ × ℕ × ℕ × ℕ) : List ℕ :=
  if x.1 = 1 then (if 0 < x.2.1 then [x.2.2.1] else []) ++ (if 1 < x.2.1 then [x.2.2.2.1] else [])
  else []
theorem st_addL_self (h : l.length < 4) (v : ℕ) : v ∈ addL l v := by
  zuckx
theorem st_addL_len (l : List ℕ) (v : ℕ) : (addL l v).length ≤ l.length + 1 := by
  zuckx
theorem labAdd_len (l : List ℕ) (n a b : ℕ) : (labAdd l n a b).length ≤ l.length + 2 := by
  unfold labAdd
  have h1 := st_addL_len l a
  split_ifs with h2 h3
  · have := st_addL_len (addL l a) b; omega
  · simp_all
  · omega
  · omega
theorem labAdd_old (h : x ∈ l) : x ∈ labAdd l n a b := by
  unfold labAdd
  split_ifs <;> first | exact mem_addL_of_mem ztvys | exact mem_addL_of_mem h | exact h
theorem labAdd_mem (h : x ∈ labAdd l n a b) :
    x ∈ l ∨ ztndh ∨ ztndp := by
  unfold labAdd at h
  by_cases h1 : 1 < n
  · rw [ite_eq_left h1, ite_eq_left by_omega] at h
    zuevq
    · zuevq
      · simp_all
      omega
    omega
  · rw [ite_eq_right h1] at h
    by_cases h0 : 0 < n
    · rw [ite_eq_left h0] at h
      zuevq
      · simp_all
      omega
    simp_all
theorem labAdd_new (hl : l.length ≤ 2) {n a b x : ℕ}
    (h : ztndh ∨ ztndp) : x ∈ labAdd l n a b := by
  unfold labAdd
  have hla := st_addL_len l a
  rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · zubel
    split_ifs
    · exact mem_addL_of_mem (st_addL_self by_omega x)
    · zulzw
  · rw [ite_eq_left h1, ite_eq_left by_omega]
    zulzw
theorem lblR_facts : IScr kN ∧ (∀ i, i < 4 → IScr ztbuc) ∧ (∀ i, i < 4 → kN ≠ kL + i) ∧
    (∀ k, k = K1 ∨ k = K2 ∨ k = K3 ∨ k = K4 → ¬ LblR kN kL k) :=
  ⟨iscr_sw by_decide by_decide,
    fun i hi => iscr_sw ztiix ztiix,
    fun i hi => by unfold kN kL sw; omega,
    by rintro k (rfl | rfl | rfl | rfl) <;> simp [LblR, kN, kL, K1, K2, K3, K4, sw]⟩
set_option maxHeartbeats 4000000 in
/-- A conditional label: append the value of `r` if `g < zN`. -/
theorem condLab_irs (hI : IInv W c₀ c) (hK : Consts c₀) (hN : c.nreg kN ≤ 4) {g r : ℕ}
    (hrN : r ≠ kN) (hrL : ∀ i, i < 4 → r ≠ kL + i) (hW : 4 ≤ W) :
    IRS P W c₀ (.ifLtN g zN (addLab kN kL r) .skip) c 32 (fun c' => c'.nreg kN ≤ 4 ∧
      lblOf c' kN kL = (if c.nreg g < c.nreg zN then addL ztlqp ztfgx
        else lblOf c kN kL) ∧
      (∀ q, ¬ LblR kN kL q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  obtain ⟨hsN, hsL, hNL, hKN⟩ := lblR_facts
  zura
  · refine (addLab_irs hI ztvti hsN hsL hNL hrN hrL hKN hN hW).mono le_rfl ?_
    simp_all
  · zugkc
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The labels of the loaded auxiliary record.** -/
theorem stLabs_irs (hI : IInv W c₀ c) (hK : Consts c₀) (hN : c.nreg kN ≤ 4)
    (hA1 : c.nreg zA ≤ 1) (hW : 4 ≤ W) :
    IRS P W c₀ stLabs c 70 (fun c' => c'.nreg kN ≤ 4 ∧
      lblOf c' kN kL = (if c.nreg zA = 1 then
        labAdd ztlqp (c.nreg zN) (c.nreg zL) (c.nreg zM) else lblOf c kN kL) ∧
      c'.nreg aF = (if c.nreg zA = 1 then 1 else c.nreg aF) ∧
      (∀ q, ¬ LblR kN kL q → q ≠ aF → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  zuibe
  unfold stLabs
  by_cases hz : c.nreg zA < c.nreg K1
  · refine (IRS.ifT hz (IRS.skip (K := 68) hI ⟨hN, ?_, ?_, by_omega, rfl⟩)).mono
      by_omega ztb
    · simp_all
    simp_all
  · have hz1 : c.nreg zA = 1 := by_omega
    refine (IRS.ifF hz ?_).mono le_rfl ztb
    simp only [hz1, ite_true]
    -- set the flag
    refine IRS.seq (K₂ := 67) (IRS.instr1 hI
      ⟨iscr_sw by_decide by_decide, by_omega⟩) ?_
    zukny
    have f1 : ∀ q, q ≠ aF → c₁.nreg q = c.nreg q := fun q hq => by
      zvmxj; zumzd
    have v1 : c₁.nreg aF = 1 := by zvmxj; rfl
    zucwy
    have nN : kN ≠ aF := by_decide
    have hlbl1 : lblOf c₁ kN kL = lblOf c kN kL := by
      zujqo
      rw [f1 _ nN]
      refine List.map_congr_left fun i hi => f1 _ ?_
      simp only [List.mem_range] at hi
      unfold kL aF sw; omega
    have zN1 : c₁.nreg zN = c.nreg zN := f1 _ by_decide
    have zL1 : c₁.nreg zL = c.nreg zL := f1 _ by_decide
    have zM1 : c₁.nreg zM = c.nreg zM := f1 _ by_decide
    zuibd
    -- the first label
    refine IRS.seq (K₂ := 32 + 3) (condLab_irs hI₁ hK
      by_simp_all by_decide
      (fun i hi => by unfold zL kL sw; omega) hW) ?_ |>.mono by_omega (fun _ h => h)
    rintro c₂ hI₂ - - ⟨n2, l2, f2, m2⟩
    have nL : ∀ q, (q = zN ∨ q = zM ∨ q = aF ∨ q = K1) → ¬ LblR kN kL q := by
      rintro q (rfl | rfl | rfl | rfl) <;> simp [LblR, kN, kL, zN, zM, aF, K1, sw]
    have k1₂ := (hK.fix hI₂).2.1
    refine (condLab_irs hI₂ hK n2 by_decide
      (fun i hi => by unfold zM kL sw; omega) hW).mono by_omega ?_
    rintro c₃ ⟨n3, l3, f3, m3⟩
    refine ⟨n3, ?_, ?_, fun q hq hqa => ?_, by_simp_all⟩
    · rw [l3, l2, hlbl1, f2 _ (nL _ ztp), f2 _ (nL _ ztwiz), k1₂, k0₁,
        zN1, zL1, zM1]
      rfl
    · simp_all
    simp_all

/-! ## The state of the stop steps -/

/-- The default record. -/
def d5 : ℕ × ℕ × ℕ × ℕ × ℕ := ztip

/-- **The state of the stop steps**: the stops before `sP` lie at the start key, the label list
holds the labels of the anchored ones (at most two per stop), `aF` says whether one is anchored. -/
def StI (P : Polygon) (J : Merge.Junction) (N₂ : NF) (rs ax : List ztcf)
    (c : Config) : Prop :=
  c.nreg kN ≤ 4 ∧ c.nreg sP ≤ 2 ∧ c.nreg sP ≤ rs.length ∧
    (∀ i (hi : i < rs.length), i < c.nreg sP → soff P J rs[i] = Lst J) ∧
    (lblOf c kN kL).length ≤ 2 * c.nreg sP ∧
    (∀ i, i < c.nreg sP → ∀ v ∈ axLabs ztnrj, v ∈ lblOf c kN kL) ∧
    (∀ v ∈ lblOf c kN kL, v < N₂.nRegions) ∧
    c.nreg aF ≤ 1 ∧ (c.nreg aF = 1 ↔ ∃ i, i < c.nreg sP ∧ (ax.getD i d5).1 = 1)

/-- The registers written by a stop step. -/
def WS (q : ℕ) : Prop :=
  q = zX ∨ q = zE ∨ q = zH ∨ q = zO ∨ q = zO + 1 ∨ q = zA ∨ q = zN ∨ q = zL ∨ q = zM ∨
    LblR kN kL q ∨ q = aF ∨ q = sP
theorem ws_stR (h : WS q) : StR q := by
  unfold WS LblR at h
  unfold StR
  simp only [zX, zE, zH, zO, zA, zN, zL, zM, aF, sP, kE, kH, kN, kL, gN, gR, dF, lC, sw] at h ⊢
  omega
theorem lblOf_congrK {c c' : Config} (h : ∀ q, LblR kN kL q → c'.nreg q = c.nreg q) :
    lblOf c' kN kL = lblOf c kN kL := by
  zujqo
  rw [h kN ztp]
  refine List.map_congr_left fun i hi => h _ ztgej
  simp_all
theorem stI_congr {P : Polygon} {J : Merge.Junction} {N₂ : NF} {rs ax : List ztcf}
    {c c' : Config} (h : StI P J N₂ rs ax c)
    (hr : ∀ q, ztebu → c'.nreg q = c.nreg q) : StI P J N₂ rs ax c' := by
  have hl := lblOf_congrK fun q hq => hr q ztjks
  have hN := hr kN ztxvr
  have hA := hr aF by_omega
  have hP := hr sP by_omega
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨by_omega, by_omega, by_omega,
    by simp_all, by_simp_all,
    fun i hi v hv => by_grind,
    by simp_all, by_omega, by_simp_all⟩
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
variable {l : List (ℕ × ℕ × ℕ × ℕ × ℕ)} {i : ℕ}
theorem getD_d5 (h : i < l.length) :
    l.getD i ztip = l[i] := by_simp_all
theorem getD_d5' (h : i < l.length) :
    l.getD i d5 = l[i] := by_simp_all
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **One stop step.** -/
theorem stStep_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {J : Merge.Junction} {N₁ N₂ : NF}
    (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    {rs ax : List ztcf} (hSD : StopData P J N₂ c rs ax)
    (hlay : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC ∧ c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC)
    (hS : StI P J N₂ rs ax c) (hkE : c.nreg kE = pK0 J) (hkH : c.nreg kH = 0)
    (hroom : c.nreg ALLOC + stStepK ≤ W) :
    IRS P W c₀ stStep c stStepK (fun c' => StI P J N₂ rs ax c' ∧
      (∀ hi : c.nreg sP < rs.length, soff P J rs[c.nreg sP] = Lst J →
        c'.nreg sP = c.nreg sP + 1) ∧
      ((∀ hi : c.nreg sP < rs.length, soff P J rs[c.nreg sP] ≠ Lst J) →
        c'.nreg sP = c.nreg sP) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ WS r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  obtain ⟨hl, hlax, hSR, hAR, hst, hw, haux, -⟩ := hSD
  obtain ⟨sN, sP2, sPl, sAt, sLen, sLab, sReg, aF1, aFi⟩ := hS
  zulig
  zubns
  zueqn
  zuki
  have hW4 : ztpil := by have := E.hWh; unfold hostWords at this; omega
  obtain ⟨⟨hpKn, hpKp, hpK6⟩, hoK, -⟩ := startMathTask P J N₂ hP hNF
  have hoK' : offK P J (pK0 J) 0 = Lst J := by
    tauto
  set i := c.nreg sP with hid
  have nob : ztxdc := fun j hj => not_oracle_sw ztce ztce
  unfold stStep
  refine (IRS.ite (K := 11990) ztyr ztrqe).mono
    by_decide ztb
  swap
  · refine IRS.skip hI ⟨ztgpn,
      by grind, by_omega, by_omega, le_rfl, by_omega⟩
  zukcm
  have hr1 := hSR i hi
  rw [getD_d5 hi] at hr1
  obtain ⟨ra, rb, -, -, -⟩ := hr1
  obtain ⟨hpw, -, -, -⟩ := hw rs[i] ztdyp
  obtain ⟨-, -, -, hsL⟩ := stop_facts hst hi
  -- 1. load the stop
  have hok1 : okB W c.nmem lsStLoad c.nreg := stLoad_ok _ _ hK₀.2.1 by_omega
  refine IRS.seq (K₁ := 7) (K₂ := 11008 + 84) (IRS.block lsStLoad hI hok1) ?_ |>.mono
    by_simp ztb
  rintro c₁ hI₁ hA₁ - hc₁
  obtain ⟨v1E, v1H⟩ := stLoad_val c.nmem c.nreg hK₀.2.1
  have hm1 : ztwh := by zvmxj
  have k1 : ∀ q, q ≠ zX → q ≠ zE → q ≠ zH → c₁.nreg q = c.nreg q := fun q h1 h2 h3 => by
    zvmxj; exact stLoad_other _ _ h1 h2 h3
  have e1E : c₁.nreg zE = rs[i].1 := by zvmxj; grind
  have e1H : c₁.nreg zH = rs[i].2.1 := by zvmxj; grind
  have e1kE : c₁.nreg kE = pK0 J := by
    zugvy
  have e1kH : c₁.nreg kH = 0 := by
    zugvy
  have hA1 : ztdc :=
    k1 _ by_decide by_decide by_decide
  have hgw := E.gw' hI₁
  have hC := corr_right0 J hP hNF.1.2.1 hNF.1.1
  -- 2. compare the offsets
  refine IRS.seq (callOff_irs hI₁ ztpxi
    by_decide by_decide
    (by rw [e1kE]; exact hpKn) (by rw [e1E]; exact hpw.1) (by rw [hgw]; exact hC.hg)
    (by zuoom; exact hpKp) (by zuoon; exact hpw.2.1)
    (by zuoom; exact fun _ => hpK6 rfl) (by zuoon; exact hpw.2.2)
    (by zvnhf; unfold stStepK at hroom; omega)) ?_
  rintro c₂ hI₂ hA₂ - ⟨b2, -, k2, hal2, hm2⟩
  rw [hgw, e1kE, e1kH, e1E, e1H] at b2
  have hb2 : BitIs c₂ zO (Lst J < soff P J rs[i]) := by
    have e : off (chainModel J.whole).W.n (gW J : ℝ) _
        = Lst J := hoK'
    zvmwe at b2
    exact b2
  have k12 : ∀ q, bandOf q ∉ oracleBands → q ≠ zX → q ≠ zE → q ≠ zH → q ≠ zO → q ≠ zO + 1 →
      q ≠ ALLOC → c₂.nreg q = c.nreg q := fun q hq h1 h2 h3 h4 h5 h6 => by
    rw [k2 q hq h4 h5 h6, k1 q h1 h2 h3]
  have k0₂ := (E.hK.fix hI₂).1
  have hm12 : ztux := fun a ha => by
    zucjp
  -- the registers of the state, kept so far
  have keepS : ∀ q, ztebu → c₂.nreg q = c.nreg q := by
    zuco
    have hq' : ztpii := by
      zucul

    refine k12 q ztbet ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | (simp only [ALLOC]; omega) | (intro h; subst h; unfold LblR at hq; simp [kN, kL, aF, sP, zX, zE, zH, zO, sw] at hq)
  have fr12 : ∀ r, bandOf r ∉ oracleBands → ¬ WS r → r ≠ ALLOC → c₂.nreg r = c.nreg r :=
    fun r hr hws hra => k12 r hr (fun h => hws zteg) (fun h => hws ztwkb)
      ztxww ztxww
      ztxww hra
  -- 3. the test
  zura
  · -- the stop lies beyond the key
    zukxa
    have hgt := hb2.2.1 (by have := hb2.1; omega)
    exact IRS.skip hI₂ ⟨stI_congr ztgpn keepS,
      by grind, fun _ => keepS sP by_omega, fr12,
      by omega, hm12⟩
  · -- the stop lies at the key
    zukxa
    have hat : soff P J rs[i] = Lst J := by
      have : ¬ Lst J < soff P J rs[i] := fun hh => h (by have := hb2.2.2 hh; omega)
      linarith
    have hi1 : i ≤ 1 := by
      by_contra h2
      have hi2 : i = 2 := by_omega
      have h0 := sAt 0 by_omega by_omega
      have := stops_two hP hNF hst (i := 0) by_omega
      grind
    have hax := hAR i by_omega
    rw [getD_d5 by_omega] at hax
    obtain ⟨xa, xn, xl, xm, -⟩ := hax
    have haux' := haux i hi
    rw [getD_d5 hi, getD_d5 by_omega] at haux'
    obtain ⟨ax1, -, axn, axl, axm, -⟩ := haux'
    -- the auxiliary record
    have sP2' := keepS sP by_omega
    have aB2 : ztshf := k12 _ (nob _ by_norm_num) by_decide
      by_decide by_decide by_decide by_decide
      by_decide
    have hok3 : okB W c₂.nmem stAux c₂.nreg := stAux_ok _ _ (E.hK.fix hI₂).2.1 (by
      omega)
    refine IRS.seq (K₁ := 11) (K₂ := 70 + 1) (IRS.block stAux hI₂ hok3) ?_ |>.mono
      by_simp ztb
    rintro c₃ hI₃ - - hc₃
    obtain ⟨v3A, v3N, v3L, v3M⟩ := stAux_val c₂.nmem c₂.nreg (E.hK.fix hI₂).2.1
    have mm : ∀ k, k < 5 → c₂.nmem _ = c.nmem (c.nreg aB + 5 * i + k) :=
      fun k hk => hm12 _ by_omega
    have hm3 : ztdrk := by zumwr
    have e3A : c₃.nreg zA = (ax[i]' by_omega).1 := by
      zumwr; show regB _ _ _ _ = _; rw [v3A, aB2, sP2', ← xa]
      simpa using mm 0 by_norm_num
    have e3N : c₃.nreg zN = (ax[i]' by_omega).2.1 := by
      zumwr; show regB _ _ _ _ = _; rw [v3N, aB2, sP2', ← xn]; exact mm 1 by_norm_num
    have e3L : c₃.nreg zL = (ax[i]' by_omega).2.2.1 := by
      zumwr; show regB _ _ _ _ = _; rw [v3L, aB2, sP2', ← xl]; exact mm 2 by_norm_num
    have e3M : c₃.nreg zM = (ax[i]' by_omega).2.2.2.1 := by
      zumwr; show regB _ _ _ _ = _; rw [v3M, aB2, sP2', ← xm]; exact mm 3 by_norm_num
    have k3 : ∀ q, q ≠ zX → q ≠ zA → q ≠ zN → q ≠ zL → q ≠ zM → c₃.nreg q = c₂.nreg q :=
      fun q h1 h2 h3 h4 h5 => by zumwr; exact stAux_other _ _ h1 h2 h3 h4 h5
    have keep3 : ∀ q, ztebu → c₃.nreg q = c₂.nreg q := by
      zuco
      have hq' : ztpii := by
        zucul

      refine k3 q ?_ ?_ ?_ ?_ ?_ <;>
        (intro h; subst h; unfold LblR at hq; simp [kN, kL, aF, sP, zX, zA, zN, zL, zM, sw] at hq)
    have hA3 : ztbox :=
      k3 _ by_decide by_decide by_decide
        by_decide by_decide
    -- the labels
    have n3 : c₃.nreg kN ≤ 4 := by
      rw [keep3 kN ztxvr, keepS kN ztxvr]; exact sN
    refine IRS.seq (stLabs_irs hI₃ E.hK n3 by_omega hW4) ?_
    rintro c₄ hI₄ hA₄ - ⟨n4, l4, a4, f4, m4⟩
    -- advance the pointer
    have sP4 : c₄.nreg sP = i := by
      rw [f4 _ (by simp [LblR, kN, kL, sP, sw]) by_decide, keep3 sP by_omega,
        sP2']
    have k1₄ := (E.hK.fix hI₄).2.1
    refine (IRS.instr1 (i := .addN sP sP K1) hI₄ ⟨iscr_sw by_decide by_decide,
      by omega⟩).mono le_rfl ?_
    rintro c₅ hc₅
    have f5 : ∀ q, q ≠ sP → c₅.nreg q = c₄.nreg q := fun q hq => by
      zunbe; zumzd
    have v5 : c₅.nreg sP = i + 1 := by zunbe; simp [regI, sP4, k1₄]
    have hm5 : ztpnw := by zunbe
    -- the label list
    have hlab3 : lblOf c₃ kN kL = lblOf c kN kL := by
      rw [lblOf_congrK (fun q hq => keep3 q ztjks), lblOf_congrK (fun q hq => keepS q ztjks)]
    have hlab5 :=
      lblOf_congrK (fun q hq => f5 q (by unfold LblR at hq; simp only [kN, kL, sP, sw] at hq ⊢; omega))
    rw [hlab3] at l4
    have e3A' : c₃.nreg zA = 1 ↔ (ax[i]' by_omega).1 = 1 := by rw [e3A]
    have hlen2 : (lblOf c kN kL).length ≤ 2 := by_omega
    have aF3 : c₃.nreg aF = c.nreg aF := by
      rw [keep3 aF by_omega, keepS aF by_omega]
    refine ⟨ztbfh, by_omega, fun hn => absurd hat (hn hi),
      fun r hr hws hra => ?_, ?_, fun a ha => ?_⟩
    · rw [f5 _ by_decide]; exact n4
    · omega
    · omega
    · zumgz
      rw [v5] at hj'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h' | rfl
      · exact sAt j hj h'
      omega
    · rw [hlab5, l4, v5]
      split_ifs
      · have := labAdd_len ztlqp (c₃.nreg zN) (c₃.nreg zL) (c₃.nreg zM); omega
      · omega
    · intro j hj v hv
      rw [hlab5, l4]
      rw [v5] at hj
      zujdh
      · have := sLab j h' v hv
        split_ifs
        · exact labAdd_old this
        omega
      · rw [getD_d5' _] at hv
        unfold axLabs at hv
        by_cases ha : (ax[i]' by_omega).1 = 1
        · rw [ite_eq_left ha] at hv
          rw [ite_eq_left (e3A'.2 ha), e3N, e3L, e3M]
          refine labAdd_new hlen2 ?_
          simp only [List.mem_append] at hv
          zukmn
          · zulsp
            · exact Or.inl ztpfp
            · simp at hv
          · zulsp
            · exact Or.inr ztpfp
            · simp at hv
        · rw [ite_eq_right ha] at hv; simp at hv
    · zuml
      rw [hlab5, l4] at hv
      split_ifs at hv with ha
      · rcases labAdd_mem hv with hv | ⟨h0, rfl⟩ | ⟨h1, rfl⟩
        · zulzr
        · omega
        omega
      · zulzr
    · rw [f5 _ by_decide, a4]
      split_ifs
      · omega
      omega
    · rw [f5 _ by_decide, a4, v5]
      by_cases ha : c₃.nreg zA = 1
      · zuhme
        refine ⟨fun _ => ztrdj, by_omega⟩
        rw [getD_d5' by_omega]; omega
      · rw [ite_eq_right ha, aF3, aFi]
        constructor
        · rintro ⟨j, hj, hjx⟩; exact ⟨j, by_omega, hjx⟩
        · rintro ⟨j, hj, hjx⟩
          zujdh
          · exact ⟨j, h', hjx⟩
          · rw [getD_d5' by_omega] at hjx
            omega
    · -- the frame
      have hr5 : r ≠ sP := fun h => hws ztmej
      have hraF : r ≠ aF := fun h => hws ztmej
      have hrL : ¬ LblR kN kL r := fun h => hws (by simp [WS, h])
      rw [f5 r hr5, f4 r hrL hraF, k3 r ztbmv
        ztbmv ztbmv
        ztbmv ztbmv, fr12 r hr hws hra]
    · have := f5 ALLOC by_decide
      omega
    · rw [hm5, m4, hm3]; exact hm12 a ha
end
end SweepEv
end Chazelle.Core
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
    (hroom : c.nreg ALLOC + 30000 * ztgf ≤ W) :
    IRS P W c₀ face c (30000 * ztgf) (FaceOut P J N₂ c) := by
  zubkh

  unfold face
  refine IRS.mono ?_
    (face_cost _) ztb
  -- 1. the prefix
  refine IRS.seq (faceLoc_irs E hI hfe (face_room1 hroom)) ?_
  rintro c₁ hI₁ - - ⟨j, hj, hl1, hl2, r0, r1, r2, vSE, vSH, vEE, vEH, hm1, hAl1, hk1⟩
  zubke
  have hfe1 : c₁.nreg fE = c.nreg fE :=
    hk1 _ ztmr
      ztbcz
  have hfa1 : c₁.nreg fA = c.nreg fA :=
    hk1 _ ztmr
      ztbcz
  have hsj := NFLoc.seq_lt hNF hj
  obtain ⟨⟨pps, hse, hsy⟩, ⟨ppe, hee, hey⟩⟩ := arc_end_facts hP₂ hNF hsj
  zuc
  -- 2. normalise the start of the arc
  refine IRS.seq (normS_irs hI₁ hK₁
    ztuxv ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide⟩
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide⟩
    (by rw [vSE]; tauto) ztliz ztliz
    by_grind) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨v2SE, v2SH, k2, hA2, hm2⟩
  zudhh
  have n2 := k2
  have n2' : ∀ q, (q = fEE ∨ q = fEH ∨ q = fE ∨ q = fA ∨ q = lR0 ∨ q = lR1 ∨ q = lR2) →
      c₂.nreg q = c₁.nreg q := by
    zuco
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact n2 _ (not_oracle_sw by_decide
        by_decide)
        by_decide
        by_decide
        by_decide
        by_decide
  -- 3. normalise the end of the arc
  refine IRS.seq (normS_irs hI₂ hK₂
    ztmas ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide⟩
    ⟨by_decide, by_decide, by_decide,
      by decide, by_decide, by_decide,
      by decide⟩
    (by rw [n2' fEE by_simp, vEE]; tauto)
    ztgfx
    ztgfx
    by_grind) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨v3EE, v3EH, k3, hA3, hm3⟩
  have n3 := k3
  have n3' : ∀ q, (q = fSE ∨ q = fSH ∨ q = fE ∨ q = fA ∨ q = lR0 ∨ q = lR1 ∨ q = lR2 ∨
      q = K0 ∨ q = K1) → c₃.nreg q = c₂.nreg q := by
    zuco
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact n3 _ (not_oracle_sw by_decide
        by_decide)
        by_decide
        by_decide
        by_decide
        by_decide
  zuhei
  -- 4. the selection
  refine (faceSel_irs hI₃ hK₃.1).mono le_rfl ?_
  rintro c₄ ⟨v4R, k4, hm4⟩
  -- the values at the selection
  have eA : c₃.nreg fA = c.nreg fA := by_grind
  have eE : c₃.nreg fE = c.nreg fE := by_grind
  have eK1 := hK₃.2.1
  have eSE : c₃.nreg fSE = (N₂.arc ztvt).s.edge := by_grind
  have eSH : c₃.nreg fSH = nhgt ztj zta (N₂.arc ztvt).s := by
    rw [n3' fSH by_simp, v2SH, vSE, vSH]
  have eEE : c₃.nreg fEE = (N₂.arc ztvt).e.edge := by_grind
  have eEH : c₃.nreg fEH = nhgt ztj zta (N₂.arc ztvt).e := by
    rw [v3EH, n2' fEE by_simp, n2' fEH by_simp, vEE, vEH]
  have eR0 : c₃.nreg lR0 = (N₂.arc ztdih).reg := by
    grind
  have eR1 : c₃.nreg lR1 = (N₂.arc ztvt).reg := by
    grind
  have eR2 : c₃.nreg lR2 = (N₂.arc ztdii).reg := by
    grind
  rw [eA, eE, eK1, eSE, eSH, eEE, eEH, eR0, eR1, eR2] at v4R
  -- the key tests
  have hS : (N₂.arc ztvt).s.edge = c.nreg fE ∧
      nhgt _ _ (N₂.arc ztvt).s = 0 ↔
      sk _ _ N₂ j = c.nreg fE :=
    (key_eq_nat_iff pps _).symm
  have hE : (N₂.arc ztvt).e.edge = c.nreg fE ∧
      nhgt _ _ (N₂.arc ztvt).e = 0 ↔
      ek _ _ N₂ j = c.nreg fE :=
    (key_eq_nat_iff ppe _).symm
  have hjP := OracleQ.predP_lt hj
  have hjN := OracleQ.succP_lt hj
  refine ⟨?_, fun h0 => ?_, fun h1 => ?_, ?_, ?_, ?_⟩
  · rw [v4R]
    split_ifs
    · exact (arc_regOf hNF hjP).1
    · zuisk
    · exact (arc_regOf hNF hjN).1
    · zuisk
  · rw [v4R, ite_eq_left by_omega]
    zus
    · exact face_before_eq hP₂ hNF hfe hj (hS.1 h)
    · exact face_before_ne hP₂ hNF hfe hj hl1 hl2 by_grind
  · rw [v4R, ite_eq_right by_omega]
    zus
    · exact face_after_eq hP₂ hNF hfe hj (hE.1 h)
    · exact face_after_ne hP₂ hNF hfe hj hl1 hl2 by_grind
  · zuge
    rw [hm4, hm3 a by_omega, hm2 a by_omega, hm1]
  · rw [k4 ALLOC by_decide]; omega
  · intro r hr hFR hra
    have hout' : ¬ ztgz := fun h => hFR zteg
    unfold sw at hout'
    have hout : r < sw 1102 ∨ sw 1203 < r := by unfold sw; omega
    have hrR := fun h => hFR ztwkb
    have h1 : r ≠ fEH := fun h => by subst h; tauto
    have h2 : r ≠ fSH := fun h => by subst h; tauto
    have h3 : r ≠ fO := fun h => by subst h; tauto
    have h4 : r ≠ fO + 1 := fun h => by subst h; tauto
    rw [k4 r hrR, n3 r hr h1 h3 h4 hra, n2 r hr h2 h3 h4 hra]
    grind

/-! ## The constants of the right correspondence -/
section Consts
variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}
theorem cst_regs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c) :
    c.nreg ztbex = 6 + tpos J.right 0 ∧ c.nreg ztyl = rL1 J ∧ c.nreg ztbsy = rL2 J ∧
      c.nreg ztbsz = rδ J ∧ c.nreg zthy = (chainModel J.right).W.n := by
  zubos
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, -, -, h34, -⟩ := hst
  have fx : ztyac := fun k hk =>
    hI.hin _ ztze
  zuflw
  · rw [fx 41 by_norm_num, show sw 41 = sw _ from rfl, h40 1 by_norm_num]; rfl
  · rw [fx 42 by_norm_num, show sw 42 = sw _ from rfl, h40 2 by_norm_num]; rfl
  · rw [fx 43 by_norm_num, show sw 43 = sw _ from rfl, h40 3 by_norm_num]; rfl
  · rw [fx 44 by_norm_num, show sw 44 = sw _ from rfl, h40 4 by_norm_num]; rfl
  · rw [fx 34 by_norm_num, h34, cm_n]
end Consts

/-! ## Reduction modulo -/

/-- `dst := a mod b` for `a < 2 b`. -/
def modR (dst a b : ℕ) : Stmt := .ifLtN a b ztigo ztgwx
theorem modR_irs {P : Polygon} {W : ℕ} {c₀ c : Config} {dst a b : ℕ} (hI : IInv W c₀ c)
    (hd : IScr dst) (h2 : c.nreg a < 2 * c.nreg b) :
    IRS P W c₀ (modR dst a b) c 3 (fun c' => c'.nreg dst = c.nreg a % c.nreg b ∧
      ztedc ∧ c'.nmem = c.nmem) := by
  unfold modR
  zura
  · refine (IRS.instr1 (i := .copyN dst a) hI hd).mono le_rfl ?_
    zuu
    refine ⟨by simp [regI, Nat.mod_eq_of_lt h], fun q hq => by zumzd, rfl⟩
  · refine (IRS.instr1 (i := .subN dst a b) hI hd).mono le_rfl ?_
    zuu
    refine ⟨?_, fun q hq => by zumzd, rfl⟩
    zubiv
    zul

/-! ## A faced region at a computed vertex -/

/-- Compute `zT` (block `l`), `fE := zT mod n₂`, `fA := side`, run `face`. -/
def fpos (l : List Instr) (side : ℕ) : Stmt :=
  .seq ztgfk (.seq (modR fE zT zthy) (.seq (.instr (.constN fA side)) face))

/-- The cost of `fpos`. -/
def fposK (L T : ℕ) : ℕ := L + (3 + (1 + 30000 * ztxz))

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
    (hroom : c.nreg ALLOC + fposK l.length ztdg ≤ W) :
    IRS P W c₀ (fpos l side) c (fposK l.length ztdg) (fun c' =>
      c'.nreg fR < N₂.nRegions ∧
      (side = 0 → BeforeFaces ztj ztojf 0
        ztxhg) ∧
      (side = 1 → AfterFaces ztj ztojf 0
        ztxhg) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ FPR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  unfold fpos fposK
  unfold fposK at hroom
  have h34c := (cst_regs E hI).2.2.2.2
  refine IRS.seq ztrjq ?_
  zuer
  have h34 := (cst_regs E hI₁).2.2.2.2
  refine IRS.seq (modR_irs hI₁
    ztbua (by
      simp_all)) ?_
  rintro c₂ hI₂ - - ⟨e2, f2, m2⟩
  have e2' : c₂.nreg fE = v % (chainModel J.right).W.n := by
    simp_all
  refine IRS.seq (IRS.instr1 hI₂
    ⟨iscr_sw by_decide by_decide, by_omega⟩) ?_
  rintro c₃ hI₃ hA₃ - hc₃
  have e3E : c₃.nreg fE = v % (chainModel J.right).W.n := by
    zuktv
  have e3A : c₃.nreg fA = side := by zumwr; rfl
  have hA2 : ztbae := by
    rw [f2 _ by_decide]
    show regB c.nmem l c.nreg ALLOC = _
    exact hl _ by_decide
  have hA3 : ztcke := by
    zuktv
  refine (face_irs E hI₃ (by rw [e3E]; exact Nat.mod_lt _ by_omega)
    by_omega (by
      grind)).mono le_rfl ?_
  rintro c₄ ⟨r4, hb4, ha4, m4, A4, k4⟩
  rw [e3A, e3E] at hb4 ha4
  refine ⟨r4, hb4, ha4, fun r hr hfp hra => ?_, by_omega, fun a ha => ?_⟩
  · rw [k4 r hr (fun h => hfp zteg) hra]
    zumnd
    zuwc
    rw [upd_other _ _ _ ztzfa,
      f2 r ztzfa]
    exact hl r (fun h => hfp ztwkb)
  simp_all
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
theorem dq_end (J : Merge.Junction) :
    dq ztns ztpg ztevg + 1 = rL1 J + rL2 J + rδ J := by
  have hL := Lst_pos J
  have hL' : 0 < rL1 J + rL2 J := by unfold Lst at hL; exact_mod_cast hL
  have h20 : rL2 J = 0 → rδ J = 0 := by
    unfold rL2 rδ
    grind
  zujql
  grind
theorem vEnd_eq (J : Merge.Junction) :
    vEnd J = (6 + tpos J.right 0 + rL1 J + rL2 J + rδ J) % (chainModel J.right).W.n := by
  unfold vEnd
  rw [dq_end]
  grind

/-- The position of the end of the right stretch. -/
def vEndL : List Instr := [.addN zT ztbex ztyl, .addN zT zT ztbsy, .addN zT zT ztbsz]
def gap1L : List Instr := [.addN zT ztbex ztyl]
def gap2L : List Instr := [.addN zT ztbex ztyl, .addN zT zT ztbsz]

/-- **The label `V` at the start** (no anchored stop). -/
def stLab : Stmt :=
  .ifLtN aF K1 (.seq (fpos vEndL 0) (block [.copyN kL fR, .constN kN 1])) .skip

/-- **The gap regions.** -/
def stGap : Stmt :=
  .ifLtN K0 ztbsz (.seq (fpos gap1L 1) (.seq (block [.copyN gR fR])
    (.seq (fpos gap2L 0) (block [.copyN ztduu fR, .constN gN 2])))) (block [.constN gN 0])
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
  have e1 : ztbld := cm_n _
  have e2 : ztlh := cm_n _
  have : ztmti := by_simp
  omega
theorem iscrT : IScr zT := iscr_sw by_decide by_decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem stLab_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (haF : c.nreg aF ≤ 1) (hroom : c.nreg ALLOC + ztzet ≤ W) :
    IRS P W c₀ stLab c ztzet (fun c' =>
      (c.nreg aF = 1 → ∀ q, LblR kN kL q → c'.nreg q = c.nreg q) ∧
      (c.nreg aF ≠ 1 → c'.nreg kN = 1 ∧ c'.nreg kL < N₂.nRegions ∧
        BeforeFaces ztj ztqyg 0
          ztzgv) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ FPR r → ¬ LblR kN kL r → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zubex

  unfold stLab
  zura
  · have h0 : c.nreg aF = 0 := by rw [hK₀.2.1] at h; omega
    have hok : okB W c.nmem vEndL c.nreg := by
      simp only [vEndL, okB, okI, regI, upd, zT, sw]
      zubcf

      rw [e1, e2, e3, e4]
      exact ⟨ztfws, ztfws, ztfws, trivial⟩
    have hv : regB c.nmem vEndL c.nreg zT = 6 + tpos J.right 0 + rL1 J + rL2 J + rδ J := by
      simp only [vEndL, regB, regI, upd, zT, sw]
      zubcf

      omega
    have hl : ∀ q, q ≠ zT → regB c.nmem vEndL c.nreg q = c.nreg q := fun q hq =>
      regB_other _ _ _ (fun i hi => by
        simp only [vEndL, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl <;> exact fun h => hq h.symm)
    refine IRS.seq (fpos_irs E hI hok hv hl by_omega
      by_omega (by simp [vEndL]; omega)) ?_
    rintro c₁ hI₁ hA₁ - ⟨r1, hb1, -, k1, A1, m1⟩
    have hb1' := hb1 rfl
    rw [← vEnd_eq] at hb1'
    refine (IRS.block [.copyN kL fR, .constN kN 1] hI₁ ⟨iscr_sw by_decide
      by_decide, ⟨iscr_sw by_decide by_decide,
        by omega⟩, trivial⟩).mono by_simp ?_
    zuu
    have vL : regB c₁.nmem [.copyN kL fR, .constN kN 1] c₁.nreg kL = c₁.nreg fR := by
      rfl
    have vN : regB c₁.nmem [.copyN kL fR, .constN kN 1] c₁.nreg kN = 1 := by
      rfl
    have vo : ∀ q, q ≠ kL → q ≠ kN → regB c₁.nmem [.copyN kL fR, .constN kN 1] c₁.nreg q =
        c₁.nreg q := fun q h1 h2 => by zunet
    refine ⟨by_simp_all, by_simp_all,
      fun r hr hfp hlb hra => ?_, ?_, by_omega⟩
    · show regB _ _ _ r = _
      rw [vo r (fun h => hlb ztbh) (fun h => hlb zteg)]
      simp_all
    tauto
  · exact IRS.skip hI ⟨by_omega, (absurd (by rw [hK₀.2.1] at h; omega)),
      by omega, le_rfl, by_omega⟩

/-- The registers of the gap regions. -/
def GapR (r : ℕ) : Prop := r = gN ∨ r = gR ∨ r = gR + 1
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
theorem stGap_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (hroom : c.nreg ALLOC + ztyeu ≤ W) :
    IRS P W c₀ stGap c ztyeu (fun c' =>
      c'.nreg gN ≤ 2 ∧ ztxsl ∧
      (∀ V, GapLab J ztwis V →
        ∃ i, i < c'.nreg gN ∧ regOf ztj zta N₂ ztbafy = V) ∧
      (∀ r, bandOf r ∉ oracleBands → ¬ FPR r → ¬ GapR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zubex

  zueqn
  zuhho
  zukap
  unfold stGap
  zura
  · have hδ : ztixu := by_omega
    -- the first gap region
    have hok1 : okB W c.nmem gap1L c.nreg := by
      simp only [gap1L, okB, okI]
      exact ⟨ztfws, trivial⟩
    have hv1 : regB c.nmem gap1L c.nreg zT = 6 + tpos J.right 0 + rL1 J := by
      simp only [gap1L, regB, regI, upd_same]; omega
    have hl1 : ∀ q, q ≠ zT → regB c.nmem gap1L c.nreg q = c.nreg q := fun q hq =>
      regB_other _ _ _ (fun i hi => by
        simp only [gap1L, List.mem_cons, List.not_mem_nil, or_false] at hi
        subst hi; tauto)
    refine IRS.seq (K₁ := fposK 1 ztdg) (K₂ := 1 + (fposK 2 ztdg + 2))
      (fpos_irs E hI (side := 1) hok1 hv1 hl1 by_omega le_rfl (by
        show c.nreg ALLOC + fposK 1 _ ≤ W; omega)) ?_ |>.mono
      by_omega ztb
    rintro c₁ hI₁ hA₁ hA₁' ⟨r1, -, ha1, k1, A1, m1⟩
    have ha1' := ha1 rfl
    refine IRS.seq (IRS.block [.copyN gR fR] hI₁
      ⟨iscr_sw by_decide by_decide, trivial⟩) ?_
    rintro c₂ hI₂ hA₂ - rfl
    have vR2 : regB c₁.nmem [.copyN gR fR] c₁.nreg gR = c₁.nreg fR := by_rfl
    have vo2 : ∀ q, q ≠ gR → regB c₁.nmem [.copyN gR fR] c₁.nreg q = c₁.nreg q := fun q h =>
      by zunne
    set c₂ : Config := { c₁ with nreg := regB c₁.nmem [.copyN gR fR] c₁.nreg } with hc₂
    have kk2 : ∀ q, q ≠ gR → bandOf q ∉ oracleBands → ¬ FPR q → q ≠ ALLOC →
        c₂.nreg q = c.nreg q := by_simp_all
    have cst : ∀ k, (k = 41 ∨ k = 42 ∨ k = 44) → c₂.nreg ztcbe = c.nreg ztcbe := by
      rintro k (rfl | rfl | rfl) <;>
        exact kk2 _ by_decide ztmr
          (by simp [FPR, FR, zT, fE, fA, fR, sw]) by_decide
    -- the second gap region
    have hok2 : okB W c₂.nmem gap2L c₂.nreg := by
      simp only [gap2L, okB, okI, regI, upd, zT, sw]
      zuqa

      rw [e1, e2, e4]
      exact ⟨ztfws, ztfws, trivial⟩
    have hv2 : regB c₂.nmem gap2L c₂.nreg zT = 6 + tpos J.right 0 + rL1 J + rδ J := by
      simp only [gap2L, regB, regI, upd, zT, sw]
      zuqa

      omega
    have hl2 : ∀ q, q ≠ zT → regB c₂.nmem gap2L c₂.nreg q = c₂.nreg q := fun q hq =>
      regB_other _ _ _ (fun i hi => by
        simp only [gap2L, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> exact fun h => hq h.symm)
    have hA2' : zteic := vo2 ALLOC by_decide
    refine IRS.seq
      (fpos_irs E hI₂ hok2 hv2 hl2 by_omega by_norm_num (by
        show c₂.nreg ALLOC + fposK 2 _ ≤ W; omega)) ?_
    rintro c₃ hI₃ hA₃ - ⟨r3, hb3, -, k3, A3, m3⟩
    have hb3' := hb3 rfl
    refine (IRS.block [.copyN _ fR, .constN gN 2] hI₃
      ⟨iscr_sw by_decide by_decide,
        ⟨iscr_sw by_decide by_decide, hW1⟩, trivial⟩).mono by_simp ?_
    zuu
    have vR3 : regB c₃.nmem [.copyN ztduu fR, .constN gN 2] c₃.nreg ztduu = c₃.nreg fR := by
      rfl
    have vN3 : regB c₃.nmem [.copyN ztduu fR, .constN gN 2] c₃.nreg gN = 2 := by
      rfl
    have vo3 : ∀ q, q ≠ gR + 1 → q ≠ gN →
        regB c₃.nmem [.copyN ztduu fR, .constN gN 2] c₃.nreg q = c₃.nreg q := fun q h1 h2 => by
      zunet
    have gR3 : c₃.nreg gR = c₁.nreg fR := by
      rw [k3 gR ztmr
        (by simp [FPR, FR, zT, fE, fA, fR, gR, sw]) by_decide]
      omega
    have eR0 : regB c₃.nmem [.copyN ztduu fR, .constN gN 2] c₃.nreg (gR + 0) = c₁.nreg fR := by
      tauto
    have ev : ztjp % (chainModel J.right).W.n =
        ztjp % (chainModel J.right).W.n := rfl
    refine ⟨by_rfl, fun i hi => ?_,
      fun V hV => ?_, fun r hr hfp hgr hra => ?_, ?_, fun a ha => ?_⟩
    · have hi' : ztsja := by_grind
      interval_cases i
      · grind
      grind
    · obtain ⟨-, hVr, hfac⟩ := hV
      have e1 := hRC.1 _ r1
      have e3 := hRC.1 _ r3
      rcases hfac with hfac | hfac
      · exact ⟨0, by_grind,
          by show regOf _ _ _ ztqvl = V; rw [eR0]
             exact after_unique one_pos e1 hVr ha1' hfac⟩
      · exact ⟨1, by_grind,
          by show regOf _ _ _ ztqvl = V; rw [vR3]
             exact before_unique le_rfl e3 hVr hb3' hfac⟩
    · show regB _ _ _ r = _
      rw [vo3 r (fun h => hgr ztwxb) (fun h => hgr zteg), k3 r hr hfp hra,
        kk2 r (fun h => hgr ztwkb) hr hfp hra]
    · show c.nreg ALLOC ≤ regB _ _ _ ALLOC
      rw [vo3 _ by_decide by_decide]
      omega
    · zuooj
      show c₁.nmem a = _
      exact m1 a ha
  · -- no gap
    have hδ : rδ J = 0 := by rw [hK₀.1, g4] at h; omega
    refine (IRS.block [.constN gN 0] hI ⟨⟨iscr_sw by_decide by_decide,
      Nat.zero_le _⟩, trivial⟩).mono by_simp ?_
    zuu
    have v0 : regB c.nmem [.constN gN 0] c.nreg gN = 0 := by_rfl
    have vo : ∀ q, q ≠ gN → regB c.nmem [.constN gN 0] c.nreg q = c.nreg q := fun q h => by
      zunne
    refine ⟨by_simp_all, fun i hi => ?_, fun V hV => ?_,
      fun r hr hfp hgr hra => ?_, ?_, by_simp_all⟩
    · simp_all
    · exact absurd hV.1 by_omega
    · tauto
    rfl
end Prog
def stores (a : ℕ) : List ℕ → Stmt
  | [] => .skip
  | r :: rs => .seq ztowc (.seq (.instr (.addN a a K1)) ztube)
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
set_option maxHeartbeats 4000000 in
/-- **Consecutive stores.** -/
theorem stores_irs (hK : Consts c₀) {a : ℕ} (ha : IScr a) :
    ∀ (rs : List ℕ) (c : Config), IInv W c₀ c → c₀.nreg ALLOC ≤ c.nreg a → (∀ r ∈ rs, r ≠ a) →
      c.nreg a + rs.length ≤ W →
      IRS P W c₀ ztube c (2 * rs.length) (fun c' => c'.nreg a = c.nreg a + rs.length ∧
        (∀ q, q ≠ a → c'.nreg q = c.nreg q) ∧
        ∀ x, c'.nmem x = if c.nreg a ≤ x ∧ x < c.nreg a + rs.length then
          c.nreg (rs.getD (x - c.nreg a) 0) else c.nmem x)
  | [], c, hI, _, _, _ => IRS.skip hI ⟨by_simp, fun _ _ => rfl, fun x => by
      simp⟩
  | r :: rs, c, hI, hA, hr, hW => by
    have hra : r ≠ a := hr r List.mem_cons_self
    refine IRS.seq (K₁ := 1) (K₂ := 1 + 2 * rs.length) (IRS.store (v := r) hI hA) ?_ |>.mono
      by_grind ztb
    zuer
    set c₁ : Config := { c with nmem := upd c.nmem (c.nreg a) (c.nreg r) } with hc₁
    have hk1 : ztcpf := (hK.fix hI₁).2.1
    have hk1' : ztfdp := hk1
    have ea : ztsgl := rfl
    refine IRS.seq (K₁ := 1) (K₂ := 2 * rs.length) (IRS.instr1 (i := .addN a a K1) hI₁
      ⟨ha, by_grind⟩) ?_
    zubuo
    have v2 : ({ c₁ with nreg := regI c₁.nmem (.addN a a K1) c₁.nreg } : Config).nreg a =
        c.nreg a + 1 := by simp [regI, hk1', hc₁]
    have o2 : ∀ q, q ≠ a →
        ({ c₁ with nreg := regI c₁.nmem (.addN a a K1) c₁.nreg } : Config).nreg q = c.nreg q :=
      fun q hq => by simp [regI, upd_other _ _ _ hq, hc₁]
    refine (stores_irs hK ha rs _ hI₂ by_omega
      (fun r' hr' => hr r' ztszl) by_grind).mono
      le_rfl ?_
    rintro c' ⟨e1, e2, e3⟩
    rw [v2] at e1 e3
    refine ⟨by_grind, fun q hq => by_grind, fun x => ?_⟩
    rw [e3 x]
    simp only [List.length_cons]
    by_cases hx : c.nreg a + 1 ≤ x ∧ x < c.nreg a + 1 + rs.length
    · grind
    · rw [ite_eq_right hx]
      show upd c.nmem ztcux ztfgx x = _
      by_cases hx0 : x = c.nreg a
      · subst hx0
        simp
      · rw [upd_other _ _ _ hx0, ite_eq_right by_omega]

/-- The registers of the log record. -/
def lsLogRegs : List ℕ := [kE, kH, kN, kL, kL + 1, kL + 2, kL + 3]

/-- **The first log record.** -/
def stLog : Stmt := .seq (.instr (.copyN zX lB)) (.seq (stores zX lsLogRegs) (.instr (.constN lC 1)))
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem stLog_irs (hK : Consts c₀) (hI : IInv W c₀ c) (hlB : c₀.nreg ALLOC ≤ c.nreg lB)
    (hroom : c.nreg lB + 7 ≤ W) :
    IRS P W c₀ stLog c 16 (fun c' => c'.nreg lC = 1 ∧
      (∀ q, q ≠ zX → q ≠ lC → c'.nreg q = c.nreg q) ∧
      (∀ x, x < c.nreg lB ∨ c.nreg lB + 7 ≤ x → c'.nmem x = c.nmem x) ∧
      c'.nmem ztqiv = c.nreg kE ∧ c'.nmem ztrmj = c.nreg kH ∧
      c'.nmem ztrmk = c.nreg kN ∧
      ∀ i, i < 4 → c'.nmem ztozz = c.nreg ztbuc) := by
  have hzX : IScr zX := iscr_sw by_decide by_decide
  refine IRS.seq (K₁ := 1) (K₂ := 14 + 1) (IRS.instr1 (i := .copyN zX lB) hI hzX) ?_ |>.mono
    by_norm_num ztb
  zuer
  have v1 : ({ c with nreg := regI c.nmem (.copyN zX lB) c.nreg } : Config).nreg zX = c.nreg lB := by
    rfl
  have o1 : ∀ q, q ≠ zX → ({ c with nreg := regI c.nmem (.copyN zX lB) c.nreg } : Config).nreg q =
      c.nreg q := fun q hq => by zumzd
  have hne : ∀ r ∈ lsLogRegs, r ≠ zX := by
    decide
  refine IRS.seq (K₁ := 14) (K₂ := 1) (stores_irs hK hzX lsLogRegs _ hI₁ by_omega hne
    by_tauto) ?_
  rintro c₂ hI₂ - - ⟨e1, e2, e3⟩
  rw [v1] at e3
  refine (IRS.instr1 (i := .constN lC 1) hI₂ ⟨iscr_sw by_decide by_decide,
    by omega⟩).mono le_rfl ?_
  zuu
  have hlen : lsLogRegs.length = 7 := rfl
  have val : ∀ k, k < 7 → c₂.nmem (c.nreg lB + k) = c.nreg (lsLogRegs.getD k 0) := by
    simp_all
  refine ⟨by_rfl, fun q h1 h2 => ?_, fun x hx => ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · zuwc
    rw [upd_other _ _ _ h2, e2 q h1, o1 q h1]
  · grind
  · show c₂.nmem _ = _; have := val 0 by_norm_num; tauto
  · show c₂.nmem _ = _; have := val 1 by_norm_num; tauto
  · show c₂.nmem _ = _; have := val 2 by_norm_num; tauto
  · show c₂.nmem _ = _
    have := val ztssx by_omega
    zujlw
    zubk
    interval_cases i <;> simp [lsLogRegs]
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
def stHead : List Instr :=
  [.copyN kE cGL, .constN kH 0, .constN kN 0, .constN sP 0, .constN aF 0, .constN dF 0]

/-- **The program of the start of the event loop.** -/
def start : Stmt := .seq (block stHead) (.seq stStep (.seq stStep (.seq stLab (.seq stGap stLog))))

/-- The cost of the start. -/
def startK (T : ℕ) : ℕ :=
  6 + (stStepK + (stStepK + ((fposK 3 T + 4) + ((fposK 1 T + fposK 2 T + 5) + 16))))
theorem startK_le (T : ℕ) : startK T ≤ 200000 * ztxz := by
  unfold startK stStepK fposK; omega

/-! ## The pointer after two steps -/
section Ptr
variable {P : Polygon} {J : Merge.Junction} {N₂ : NF}
theorem stepRes {rs : List ztcf} {s s' : ℕ}
    (ha : ∀ hi : s < rs.length, soff P J rs[s] = Lst J → s' = s + 1)
    (hb : (∀ hi : s < rs.length, soff P J rs[s] ≠ Lst J) → s' = s) (j : ℕ) (hj : j = s) :
    (∀ hi : j < rs.length, soff P J rs[j] = Lst J → s' = j + 1) ∧
      ((∀ hi : j < rs.length, soff P J rs[j] ≠ Lst J) → s' = j) := by
  simp_all

/-- **The pointer after two stop steps** skips exactly the stops at the start key. -/
theorem ptr_char (hP : J.P.Simple) (hN : IsNF ztj zta N₂)
    {rs : List ztcf}
    (hst : StopsOK J ztwis ztwoy) {s1 s2 : ℕ}
    (h1a : ∀ hi : 0 < rs.length, soff P J rs[0] = Lst J → s1 = 0 + 1)
    (h1b : (∀ hi : 0 < rs.length, soff P J rs[0] ≠ Lst J) → s1 = 0)
    (h2a : ∀ hi : s1 < rs.length, soff P J rs[s1] = Lst J → s2 = s1 + 1)
    (h2b : (∀ hi : s1 < rs.length, soff P J rs[s1] ≠ Lst J) → s2 = s1)
    (hat : ∀ i (hi : i < rs.length), i < s2 → soff P J rs[i] = Lst J) :
    ∀ i (hi : i < rs.length), i < s2 ↔ soff P J rs[i] = Lst J := by
  have ge : ztezi := fun i hi =>
    (stop_facts hst hi).2.2.2
  have s1le : s1 ≤ 1 := by
    grind
  have s2ge : s1 ≤ s2 := by
    grind
  zug
  refine ⟨hat i hi, fun hie => ?_⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with rfl | rfl | h2
  · grind
  · have h0 : soff P J (rs[0]' by_omega) = Lst J := by
      have := stops_sorted hst (i := 0) (i' := 1) by_omega hi
      grind
    grind
  · exfalso
    have h3 := stops_two hP hN hst (i := i - 2) by_omega
    grind
end Ptr

/-! ## The stop data along the start -/
theorem stopData_transport {P : Polygon} {J : Merge.Junction} {N₂ : NF} {c c' : Config}
    {rs ax : List ztcf} (h : StopData P J N₂ c rs ax)
    (hsC : c'.nreg sC = c.nreg sC) (hsB : c'.nreg sB = c.nreg sB) (haB : c'.nreg aB = c.nreg aB)
    (hlay : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC ∧ c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) : StopData P J N₂ c' rs ax := by
  zucia

  · rw [hsB, hm _ by_omega, hm _ by_omega, hm _ by_omega, hm _ by_omega, hm _ by_omega]
    zulys
  · rw [haB, hm _ by_omega, hm _ by_omega, hm _ by_omega, hm _ by_omega, hm _ by_omega]
    zulyk

/-! ## Register sets -/
variable {r : ℕ}
theorem fpr_stR (h : FPR r) : StR r := by
  unfold FPR FR at h; unfold StR
  simp only [zT, fE, fA, fR, kE, kH, kN, kL, gN, gR, sP, dF, lC, sw] at h ⊢
  omega
theorem lblR_stR (h : LblR kN kL r) : StR r := by
  unfold LblR at h; tauto
theorem gapR_stR (h : GapR r) : StR r := by
  unfold GapR at h; unfold StR
  grind

/-- The raw post of the start. -/
def SRaw (P : Polygon) (J : Merge.Junction) (N₂ : NF) (rs ax : List ztcf)
    (c c' : Config) : Prop :=
  c'.nreg kE = pK0 J ∧ c'.nreg kH = 0 ∧ c'.nreg dF = 0 ∧ c'.nreg lC = 1 ∧
  c'.nreg sP ≤ rs.length ∧ (∀ i (hi : i < rs.length), i < c'.nreg sP ↔ soff P J rs[i] = Lst J) ∧
  c'.nreg kN ≤ 4 ∧ (∀ v ∈ lblOf c' kN kL, v < N₂.nRegions) ∧
  (∀ i (hi : i < rs.length), soff P J rs[i] = Lst J → (ax.getD i d5).1 = 1 →
    ∀ v ∈ axLabs ztnrj, v ∈ lblOf c' kN kL) ∧
  (ztdpy →
    c'.nreg kN = 1 ∧ c'.nreg kL < N₂.nRegions ∧
    BeforeFaces ztj ztqyg 0
      ztzgv) ∧
  c'.nreg gN ≤ 2 ∧ ztxsl ∧
  (∀ V, GapLab J ztwis V →
    ∃ i, i < c'.nreg gN ∧ regOf ztj zta N₂ ztbafy = V) ∧
  c'.nmem ztqiv = c'.nreg kE ∧ c'.nmem ztrmj = c'.nreg kH ∧
  c'.nmem ztrmk = c'.nreg kN ∧
  (∀ i, i < 4 → c'.nmem ztozz = c'.nreg ztbuc) ∧
  ztdww ∧
  ztfcv ∧
  c.nreg ALLOC ≤ c'.nreg ALLOC
end
end SweepEv
end Chazelle.Core
namespace Chazelle.Core
namespace SweepEv
open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
@[expose] public section
variable (m f : ℕ → ℕ) {q : ℕ}
theorem stHead_val :
    regB m stHead f kE = f cGL ∧ regB m stHead f kH = 0 ∧ regB m stHead f kN = 0 ∧
      regB m stHead f sP = 0 ∧ regB m stHead f aF = 0 ∧ regB m stHead f dF = 0 := by
  tauto

/-- The registers of the head. -/
def HdR (q : ℕ) : Prop := q = kE ∨ q = kH ∨ q = kN ∨ q = sP ∨ q = aF ∨ q = dF
theorem stHead_other (h : ¬ HdR q) : regB m stHead f q = f q :=
  regB_other m stHead f (fun i hi => by
    simp only [stHead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> zvmwd <;> intro he <;>
      subst he <;> exact h by_tauto)
theorem hdR_stR (h : HdR q) : StR q := by
  unfold HdR at h; unfold StR
  simp only [kE, kH, kN, kL, gN, gR, sP, dF, lC, aF, sw] at h ⊢
  omega
theorem zX_stR : StR zX := by_tauto
theorem lC_stR : StR lC := by_tauto

/-- A register outside all write sets of the start keeps its value along the parts. -/
def Untouched (q : ℕ) : Prop :=
  bandOf q ∉ oracleBands ∧ ¬ HdR q ∧ ¬ WS q ∧ ¬ FPR q ∧ ¬ LblR kN kL q ∧ ¬ GapR q ∧ q ≠ zX ∧
    q ≠ lC ∧ q ≠ ALLOC
theorem untouched_of (hq : bandOf q ∉ oracleBands) (h : ¬ StR q) (ha : q ≠ ALLOC) :
    Untouched q :=
  ⟨hq, fun h' => h (hdR_stR h'), fun h' => h (ws_stR h'), fun h' => h (fpr_stR h'),
    fun h' => h (lblR_stR h'), fun h' => h (gapR_stR h'), fun h' => h (h' ▸ zX_stR),
    fun h' => h (h' ▸ lC_stR), ha⟩
theorem untouched_sw {j : ℕ} (hj : j < 10000)
    (h : ¬ (2400 ≤ j ∧ j ≤ 2406) ∧ ¬ (2440 ≤ j ∧ j ≤ 2442) ∧ j ≠ 2450 ∧ j ≠ 2451 ∧ j ≠ 2431 ∧
      ¬ (2480 ≤ j ∧ j < 2500) ∧ ¬ (700 ≤ j ∧ j < 2200) ∧ ¬ (2610 ≤ j ∧ j ≤ 2612) ∧
      ¬ (3000 ≤ j ∧ j < 6000)) : Untouched (sw j) := by
  refine untouched_of ztxlc ?_
    ztbpx
  unfold StR
  simp only [kE, kH, kN, kL, gN, gR, sP, dF, lC, sw]
  omega
set_option maxHeartbeats 32000000 in
set_option maxRecDepth 20000 in
/-- **The run step of the start.** -/
theorem start_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction}
    {N₁ N₂ : NF} (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    {rs ax : List ztcf} (hSD : StopData P J N₂ c rs ax)
    (hlay : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC ∧ c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC)
    (hlB : c₀.nreg ALLOC ≤ c.nreg lB) (hlB7 : c.nreg lB + 7 ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + startK ztdg ≤ W) :
    IRS P W c₀ start c (startK ztdg) (SRaw P J N₂ rs ax c) := by
  zulig
  zubns
  zueqn
  have hst := hSD.2.2.2.2.1
  have hlen := hSD.1
  have hlax := hSD.2.1
  unfold start startK
  unfold startK at hroom
  -- 1. the head
  have hokH : okB W c.nmem stHead c.nreg := by
    simp only [stHead, okB, okI]
    exact ⟨iscr_sw by_decide by_decide,
      ⟨iscr_sw by_decide by_decide, Nat.zero_le _⟩,
      ⟨iscr_sw by_decide by_decide, Nat.zero_le _⟩,
      ⟨iscr_sw by_decide by_decide, Nat.zero_le _⟩,
      ⟨iscr_sw by_decide by_decide, Nat.zero_le _⟩,
      ⟨iscr_sw by_decide by_decide, Nat.zero_le _⟩, trivial⟩
  refine IRS.seq (IRS.block stHead hI hokH) ?_ |>.mono
    by_rfl ztb
  rintro c₂ hI₂ - - hc₂
  obtain ⟨vE, vH, vN, vP, vA, vD⟩ := stHead_val c.nmem c.nreg
  have o2 : ∀ q, ¬ HdR q → c₂.nreg q = c.nreg q := fun q hq => by
    zumxp; exact stHead_other _ _ hq
  have m2 : ztckc := by zumxp
  have e2E : c₂.nreg kE = pK0 J := by
    zumxp; show regB _ _ _ kE = _; rw [vE, (E.hM.fix hI).gl]; rfl
  have e2H : c₂.nreg kH = 0 := by_simp_all
  have e2N : c₂.nreg kN = 0 := by_simp_all
  have e2P : c₂.nreg sP = 0 := by_simp_all
  have e2A : c₂.nreg aF = 0 := by_simp_all
  have e2D : c₂.nreg dF = 0 := by_simp_all
  have nh : ∀ j, j = 2600 ∨ j = 2601 ∨ j = 2602 ∨ j = 2430 → ¬ HdR ztgc := by
    rintro j (rfl | rfl | rfl | rfl) <;> simp [HdR, kE, kH, kN, sP, aF, dF, sw]
  have hA2 : ztbae := o2 _ (by simp [HdR, kE, kH, kN, sP, aF, dF, ALLOC, sw])
  have sC2 : c₂.nreg sC = c.nreg sC := o2 _ (nh 2601 by_norm_num)
  have sB2 : c₂.nreg sB = c.nreg sB := o2 _ (nh 2600 by_norm_num)
  have aB2 : ztshf := o2 _ (nh 2602 by_norm_num)
  have hSD2 := stopData_transport hSD sC2 sB2 aB2 hlay
    by_simp_all
  have hlay2 : c₂.nreg sB + 5 * c₂.nreg sC ≤ c₂.nreg ALLOC ∧
      c₂.nreg aB + 5 * c₂.nreg sC ≤ c₂.nreg ALLOC := by_omega
  have hS2 : StI P J N₂ rs ax c₂ := by
    have hl : lblOf c₂ kN kL = [] := by simp [lblOf, e2N]
    refine ⟨by_omega, by_omega, by_omega, by_simp_all, by_simp_all,
      by simp_all, by_simp_all, by_omega, ?_⟩
    omega
  -- 2. the first stop step
  refine IRS.seq (stStep_irs E hI₂ hSD2 hlay2 hS2 e2E e2H by_omega) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨S3, a3, b3, fr3, A3, m3⟩
  have ws : ∀ j, j = 2600 ∨ j = 2601 ∨ j = 2602 ∨ j = 2430 ∨ j = 2400 ∨ j = 2401 ∨ j = 2451 →
      ¬ WS ztgc := by
    rintro j (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [WS, LblR, zX, zE, zH, zO, zA, zN, zL, zM, aF, sP, kN, kL, sw]
  have kp3 : ∀ j, ztdvd →
      c₃.nreg _ = c₂.nreg _ := fun j hj =>
    fr3 _ ztxlc
      ztudl ztbpx
  have hSD3 := stopData_transport hSD2 (kp3 2601 by_norm_num)
    (kp3 2600 by_norm_num) (kp3 2602 by_norm_num) hlay2 m3
  have hlay3 : c₃.nreg sB + 5 * c₃.nreg sC ≤ c₃.nreg ALLOC ∧
      c₃.nreg aB + 5 * c₃.nreg sC ≤ c₃.nreg ALLOC := by
    have e1 : c₃.nreg sC = c₂.nreg sC := kp3 2601 by_norm_num
    have e2 : c₃.nreg sB = c₂.nreg sB := kp3 2600 by_norm_num
    have e3 : c₃.nreg aB = c₂.nreg aB := kp3 2602 by_norm_num
    omega
  have e3E := (kp3 2400 by_norm_num).trans e2E
  have e3H := (kp3 2401 by_norm_num).trans e2H
  -- 3. the second stop step
  refine IRS.seq (stStep_irs E hI₃ hSD3 hlay3 S3 e3E e3H by_omega) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨S4, a4, b4, fr4, A4, m4⟩
  have kp4 : ∀ j, ztdvd →
      c₄.nreg _ = c₃.nreg _ := fun j hj =>
    fr4 _ ztxlc
      ztudl ztbpx
  -- the pointer
  have hptr : ∀ i (hi : i < rs.length), i < c₄.nreg sP ↔ soff P J rs[i] = Lst J := by
    obtain ⟨h1a, h1b⟩ := stepRes a3 b3 0 e2P.symm
    exact ptr_char hP hNF hst h1a h1b a4 b4 S4.2.2.2.1
  -- 4. the label from a face
  obtain ⟨sN4, sP4, sPl4, sAt4, sLen4, sLab4, sReg4, aF4, aFi4⟩ := S4
  refine IRS.seq (stLab_irs E hI₄ aF4 by_omega) ?_
  rintro c₅ hI₅ hA₅ hA₅' ⟨l5a, l5b, fr5, A5, m5⟩
  -- 5. the gap regions
  refine IRS.seq
    (stGap_irs E hI₅ by_omega) ?_
  rintro c₆ hI₆ hA₆ hA₆' ⟨g1, g2, g3, fr6, A6, m6⟩
  -- registers kept by stLab and stGap
  have u : ∀ q, Untouched q → c₆.nreg q = c.nreg q := by
    rintro q ⟨hq, h1, h2, h3, h4, h5, -, -, hqa⟩
    rw [fr6 q hq h3 h5 hqa, fr5 q hq h3 h4 hqa, fr4 q hq h2 hqa, fr3 q hq h2 hqa, o2 q h1]
  have lB6 : c₆.nreg lB = c.nreg lB := u _ (untouched_sw by_norm_num by_omega)
  -- 6. the log record
  refine (stLog_irs E.hK hI₆ by_omega by_omega).mono
    le_rfl ?_
  rintro c₇ ⟨lc7, fr7, mem7, r70, r71, r72, r73⟩
  rw [lB6] at mem7 r70 r71 r72 r73
  -- values at the end
  have k7 := fr7
  have nP : ∀ q, (q = sP ∨ q = aF) → ¬ FPR q ∧ ¬ LblR kN kL q ∧ ¬ GapR q ∧ q ≠ zX ∧ q ≠ lC ∧
      bandOf q ∉ oracleBands ∧ q ≠ ALLOC := by
    rintro q (rfl | rfl) <;> refine ⟨?_, ?_, ?_, ?_, ?_, not_oracle_sw by_decide
      by_decide, by_decide⟩ <;>
      simp [FPR, FR, LblR, GapR, zT, fE, fA, fR, kN, kL, gN, gR, sP, aF, zX, lC, sw]
  have sP7 : c₇.nreg sP = c₄.nreg sP := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := nP sP ztp
    rw [k7 _ h4 h5, fr6 _ h6 h1 h3 h7, fr5 _ h6 h1 h2 h7]
  have u2 : ∀ q, bandOf q ∉ oracleBands → ¬ WS q → ¬ FPR q → ¬ LblR kN kL q → ¬ GapR q →
      q ≠ ALLOC → c₆.nreg q = c₂.nreg q := fun q hq h2 h3 h4 h5 hqa => by
    rw [fr6 q hq h3 h5 hqa, fr5 q hq h3 h4 hqa, fr4 q hq h2 hqa, fr3 q hq h2 hqa]
  have hd : ∀ j, (j = 2400 ∨ j = 2401 ∨ j = 2451) → c₇.nreg ztgc = c₂.nreg ztgc := by
    zun
    have hj' : 2400 ≤ j ∧ j ≤ 2451 := by_omega
    rw [k7 _ ztozy ztozp]
    refine u2 _ ztxlc ?_ ?_ ?_ ?_
      ztbpx
    · unfold WS LblR; simp only [zX, zE, zH, zO, zA, zN, zL, zM, aF, sP, kN, kL, sw]; omega
    · unfold FPR FR; zunld; omega
    · unfold LblR; simp only [kN, kL, sw]; omega
    · unfold GapR; zunxa; omega
  have hl57 : ∀ q, LblR kN kL q → c₇.nreg q = c₅.nreg q := by
    zuco
    have hq' : 242402 ≤ q ∧ q ≤ 242406 := by
      unfold LblR at hq; simp only [kN, kL, sw] at hq; omega
    rw [k7 q ztozy ztozp]
    exact fr6 q ztbet
      (by unfold FPR FR; zunld; omega)
      (by unfold GapR; zunxa; omega) ztu
  have hlbl7 := lblOf_congrK hl57
  have hg67 : ∀ q, GapR q → c₇.nreg q = c₆.nreg q := fun q hq => by
    unfold GapR at hq
    exact k7 q (by simp only [gN, gR, zX, sw] at hq ⊢; omega)
      (by simp only [gN, gR, lC, sw] at hq ⊢; omega)
  have hlab45 := fun h =>
    lblOf_congrK (l5a h)
  have hN75 := hl57 kN ztp
  have hL75 := hl57 kL ztbh
  have one : ∀ (cc : Config), cc.nreg kN = 1 → lblOf cc kN kL = [cc.nreg kL] := fun cc h => by
    simp [lblOf, h]
  have hnot : ztdpy →
      c₄.nreg aF ≠ 1 := by
    intro hall h1
    obtain ⟨i, hi, hia⟩ := aFi4.1 h1
    exact hall i by_omega ((hptr i by_omega).1 hi) hia
  have hA7 : ztfky := k7 _ by_decide by_decide
  refine ⟨?_, ?_, ?_, lc7, by_omega, fun i hi => by rw [sP7]; exact hptr i hi, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hd 2400 ztp).trans e2E
  · exact (hd 2401 by_omega).trans e2H
  · exact (hd 2451 by_omega).trans e2D
  · rw [hN75]
    zuird
    · rw [l5a h kN ztp]; omega
    omega
  · zuml
    rw [hlbl7] at hv
    zuird
    · rw [hlab45 h] at hv; exact sReg4 v hv
    · obtain ⟨h1, h2, -⟩ := l5b h
      rw [one c₅ h1] at hv
      zvnns at hv
      omega
  · intro i hi hik hia v hv
    have hi' := (hptr i hi).2 hik
    have h1 := aFi4.2 ⟨i, hi', hia⟩
    rw [hlbl7, hlab45 h1]
    exact sLab4 i hi' v hv
  · intro hall
    obtain ⟨h1, h2, h3⟩ := l5b (hnot hall)
    exact ⟨by_omega, by_omega, by rw [hL75]; exact h3⟩
  · rw [hg67 gN ztp]; exact g1
  · zug
    rw [hg67 gN ztp] at hi
    zukcp
    zuool
    exact g2 i hi
  · zulmk
    obtain ⟨i, hi, hiV⟩ := g3 V hV
    zukcp
    exact ⟨i, by rw [hg67 gN ztp]; exact hi,
      by zuool; omega⟩
  · rw [r70, k7 kE by_decide by_decide]
  · rw [r71, k7 kH by_decide by_decide]
  · rw [r72, k7 kN by_decide by_decide]
  · zug
    rw [r73 i hi, k7 _ (by unfold kL zX sw; omega) ztnvu]
  · zueth
    rw [mem7 x hx', m6 x by_omega, m5 x by_omega, m4 x by_omega, m3 x by_omega, m2]
  · intro r hr hs hra
    have hu := untouched_of hr hs hra
    rw [k7 r hu.2.2.2.2.2.2.1 hu.2.2.2.2.2.2.2.1]
    exact u r hu
  · omega
open Chazelle.Chain (SideAttach sidePt)
variable {P : Polygon} {J : Merge.Junction} {N₂ : NF} {c : Config} {v : ℕ}
theorem stopData_transport' {c c' : Config}
    {rs ax : List ztcf} (h : StopData P J N₂ c rs ax)
    (hsC : c'.nreg sC = c.nreg sC) (hsB : c'.nreg sB = c.nreg sB) (haB : c'.nreg aB = c.nreg aB)
    (hm : ∀ a, ((c.nreg sB ≤ a ∧ a < c.nreg sB + 5 * c.nreg sC) ∨
      (c.nreg aB ≤ a ∧ a < c.nreg aB + 5 * c.nreg sC)) → c'.nmem a = c.nmem a) :
    StopData P J N₂ c' rs ax := by
  zucia

  · rw [hsB, hm _ ztec, hm _ ztec, hm _ ztec,
      hm _ ztec, hm _ ztec]
    zulys
  · rw [haB, hm _ ztbh, hm _ ztbh, hm _ ztbh,
      hm _ ztbh, hm _ ztbh]
    zulyk
theorem stopOff_eq
    {rs : List ztcf} (hSR : StopRecsAt c.nmem zthvm rs) {i : ℕ}
    (hi : i < rs.length) : stopOff P J c i = soff P J rs[i] := by
  obtain ⟨h1, h2, -⟩ := hSR i hi
  rw [List.getD_eq_getElem _ _ hi] at h1 h2
  unfold stopOff stopE stopH offK soff oW
  zubuw
  rfl
theorem lblOf_mem (h : v ∈ lblOf c kN kL) :
    ∃ t, t < min ztjsi 4 ∧ v = c.nreg zttqo := by
  unfold lblOf at h
  grind
theorem mem_curLab
    (h : v ∈ lblOf c kN kL) : regOf ztj zta N₂ v ∈ curLab P J N₂ c := by
  obtain ⟨t, ht, rfl⟩ := lblOf_mem h
  refine ⟨c.nreg zttqo, ?_, rfl⟩
  have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by_omega
  rcases this with rfl | rfl | rfl | rfl
  · simp_all
  · simp_all
  · simp_all
  simp_all
set_option maxHeartbeats 32000000 in
set_option maxRecDepth 20000 in
/-- **Task L0: the start of the event loop.** -/
theorem loopStartTask : LoopStartTask := by
  refine ⟨start, fun _ => 200000, ?_⟩
  intro sh Bs F X Ok P W c₀ c₁ c J N₁ N₂ E hPrep hStop hI hroom
  obtain ⟨rs, ax, hl, hlax, hSR, hAR, hst, hw, haux, hlen, hsB1, hsB2, haB1, haB2, hm1, hfr1⟩ :=
    hStop
  obtain ⟨hflag, hlay1, hlC, hlay2, hm0, hfr0⟩ := hPrep
  have hSD : StopData P J N₂ c rs ax := ⟨hl, hlax, hSR, hAR, hst, hw, haux, hlen⟩
  zubns
  zueqn
  zueef
  have hS₂ : ztgap := hNF.1.2.1
  have hS₂f : S₂.Finite := hNF.1.1
  -- registers of `c`
  have hlBc : c.nreg lB = c₁.nreg lB := hfr1 _ (not_oracle_sw by_decide
    by_decide) (by unfold S2R; decide) by_decide
  have hTB : ztsfb := hI.hin _ by_trivial
  have hTB₀ : c₀.nreg cTB = c₀.nreg ALLOC := E.hTA
  have hlay : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC ∧
      c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC := by_omega
  have hlB : c₀.nreg ALLOC ≤ c.nreg lB := by_omega
  have hlogB : c.nreg lB + 7 * logCap N₁ N₂ ≤ c₁.nreg ALLOC := by rw [hlBc]; tauto
  have hcap7 : 7 ≤ 7 * logCap N₁ N₂ := by unfold logCap; omega
  have hlB7 : c.nreg lB + 7 ≤ c.nreg ALLOC := by_omega
  -- the run
  have hroom' : c.nreg ALLOC + 200000 * ztgf ≤ W := hroom
  refine (start_irs E hI hSD hlay hlB hlB7 (by have := startK_le ztdg; omega)).mono
    (startK_le _) ?_
  rintro c' ⟨kE', kH', dF', lC', sPl, hptr, kN4, lreg, hΛ, hB, gN2, gR', gap, r0, r1, r2, r3, mem,
    fr, hA⟩
  -- registers kept
  have keep : ∀ j, j < 10000 → ¬ StR ztgc → c'.nreg ztgc = c.nreg ztgc := by
    zujbg
    have h1 : ztujz := by unfold sw; simp
    zuglg
    have h3 : sw j ≠ ALLOC := by unfold ALLOC; omega
    exact fr ztgc ztsg h h3
  have nS : ∀ j, (j = 2600 ∨ j = 2601 ∨ j = 2602 ∨ j = 2430 ∨ j = 661) → ¬ StR ztgc := by
    rintro j (rfl | rfl | rfl | rfl | rfl) <;> unfold StR <;>
      simp [kE, kH, kN, kL, gN, gR, sP, dF, lC, sw]
  have sB' : ztiyz := keep 2600 by_norm_num zthis
  have sC' : ztmum := keep 2601 by_norm_num zthis
  have aB' : c'.nreg aB = c.nreg aB := keep 2602 by_norm_num zthis
  have lB' : ztgue := keep 2430 by_norm_num zthis
  have TB' : ztgud := keep 661 by_norm_num zthis
  -- the stop data
  have hSD' : StopData P J N₂ c' rs ax := stopData_transport' hSD sC' sB' aB' (fun a ha =>
    mem a by_omega ztbh)
  have hSR' : StopRecsAt c'.nmem ztqhe rs := hSD'.2.2.1
  have hlen' : rs.length = c'.nreg sC := hSD'.1
  -- the start key
  obtain ⟨hpw, hoK, -⟩ := startMathTask P J N₂ hP hNF
  have hkey : keyOff P J c' = Lst J := by
    unfold keyOff
    zunqp
    tauto
  have hge : ztezi := fun i hi =>
    (stop_facts hst hi).2.2.2
  -- the label set
  zuhho
  have hinv : EvInv J S₂ ztmbm ztjsy := by
    refine evInv_start hP hNF hlax hst ztdp (fun i hi hik hia => ?_) (fun hall => ?_)
    · have := haux i hi
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ by_omega] at this
      omega
    · rintro _ ⟨l, hl', rfl⟩
      have hx := haux i hi
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ by_omega] at hx
      have hnl : (ax[i]' by_omega).2.1 ≤ 2 := hx.2.2.1
      have hl'' : l ∈ axLabs ztnrj := by
        rw [List.getD_eq_getElem _ _ (show i < ax.length by omega)]
        unfold axLabs
        rw [ite_eq_left hia]
        rcases hl' with ⟨h0, rfl⟩ | ⟨h1, rfl⟩ | ⟨h2, rfl⟩ | ⟨h3, rfl⟩
        · simp [h0]
        · simp [h1]
        · omega
        · omega
      exact mem_curLab (hΛ i hi hik (by zuogm; omega) l hl'')
    · obtain ⟨h1, h2, h3⟩ := hB (fun i hi hik => by
        zuogm; exact hall i hi hik)
      refine ⟨regOf ztj zta N₂ ztqhd, hRC.1 _ h2, h3, ?_⟩
      ext V
      simp only [curLab, labSet, h1, Set.mem_image, mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨l, hl', rfl⟩
        rcases hl' with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · rfl
        all_goals omega
      · zumla
  have hinv' : EvInv J S₂ ztcnt ztjsy := by rw [hkey]; omega
  -- the labels are region indices
  have hlabR : ∀ i, i < c'.nreg kN → c'.nreg ztbuc < N₂.nRegions := fun i hi =>
    lreg _ (List.mem_map.2 ⟨i, List.mem_range.2 by_omega, rfl⟩)
  -- the log record
  set rec : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ := (c'.nreg kE, c'.nreg kH, c'.nreg kN, c'.nreg kL,
    c'.nreg ztdvf, c'.nreg ztdvg, c'.nreg ztdvh) with hrec
  have hpar0 : (chainModel J.whole).param zta ztryz = 0 := rfl
  have hoW : oW J (((pK0 J : ℕ) : ℝ) + (chainModel J.whole).param zta ztryz) = Lst J := by
    tauto
  refine ⟨⟨⟨rs, ax, hSD'⟩, fun i i' hii hi' => ?_, fun i hi => ?_, by_omega,
    by omega, ?_, ?_, ?_, ?_,
    by zunqp; tauto, by rw [hkey], kN4, hlabR, hinv', gN2, gR', gap,
    by omega, fun i hi => ?_, ⟨[rec], by zupci; rfl,
      ?_, ?_, ?_, rfl⟩, ?_, ?_, dF'⟩, fr, fun x hx hx' => mem x hx hx'⟩
  · zugxe
    exact stops_sorted hst hii by_omega
  · zugxe
    exact stops_two hP hNF hst by_omega
  · omega
  · omega
  · omega
  · omega
  · zufuv
    rw [stopOff_eq hSR' hi', hkey, hptr i hi']
    have := hge i hi'
    constructor
    · intro h; zvmwc
    · intro h; linarith
  · -- the record in memory
    zug
    have hi0 : ztfla := by simpa using hi
    zufpy
    rw [lB']
    simp only [List.getD_cons_zero, Nat.mul_zero, Nat.add_zero, hrec]
    refine ztion
    · have := r3 0 by_norm_num; omega
    · have := r3 1 by_norm_num; omega
    · have := r3 2 by_norm_num; omega
    · have := r3 3 by_norm_num; omega
  · -- the word facts
    zuz
    zvnns at hr
    subst hr
    simp only [hrec]
    refine ⟨by zunqp; tauto, kN4, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simpa using hlabR 0 h
    · exact hlabR 1 h
    · exact hlabR 2 h
    · exact hlabR 3 h
  · -- the log so far
    have hlog : logOf J zta N₂ [rec] = [((pK0 J : ℕ), (chainModel J.whole).param zta
        ⟨pK0 J, 0⟩, curLab P J N₂ c')] := by
      simp only [logOf, List.map_cons, List.map_nil, hrec, kE', kH']
      rfl
    rw [hlog]
    refine ⟨by_simp, ?_, ?_, List.pairwise_singleton _ _, fun i hi => by_tauto, ?_⟩
    · zuh
      zuhpj

      refine ⟨hpw.1, hpw.2.1.1, hpw.2.1.2.1, ?_⟩
      zubi
      zumnv
    · zuh
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
      zultk
      omega
    · zuh
      zuhpj

      exact labIn_of_evInv hP hS₂ hS₂f hpw.1 hpw.2.1.1 hpw.2.1.2.1 (by rw [hoW]; omega)
  · -- the measure
    zupci
    have hfin := (countTask P J N₁ N₂ hP E.hNF₁ hNF).1
    have := Set.ncard_le_ncard (Set.inter_subset_left (s := keyS P J N₁ N₂)
      (t := Ioi ztcnt)) hfin
    omega
  · -- the table
    zun
    have hz : c'.nmem (c'.nreg cTB + 3 * j) = 0 := by
      rw [TB', hTB, mem _ by_omega ztec, hm1 _ by_omega]
      exact hflag j hj
    zudur
    refine ⟨by_norm_num, fun h => absurd h by_norm_num, fun _ _ p t _ _ hlt hle => ?_⟩
    rw [hkey] at hle
    exact absurd hlt ztwan
