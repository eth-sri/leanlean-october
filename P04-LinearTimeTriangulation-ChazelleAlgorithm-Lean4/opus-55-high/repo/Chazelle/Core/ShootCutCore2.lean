module

public import Chazelle.MacT
public import Chazelle.Core.ShootCutLoop2
public import Chazelle.Core.SweepPrimKer
public import Chazelle.Core.FuseMathCut

namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK NFLoc
@[expose] public section
variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}
variable (d : Config)
theorem cHead1_exec (hw : WordsBounded W d) {MD Hh' cs cm : ℕ}
    (h00 : d.nreg 150000 = MD) (h91 : d.nreg 150091 = 1) (mA : d.nmem ztki = Hh')
    (mB : d.nmem ztqac = cs) (mC : d.nmem ztnmx = cm) (hMW : MD + 3 ≤ W) :
    ∃ d' k, Exec P W cHead1 d d' k ∧ k = 6 ∧ d'.nreg 150021 = Hh' ∧ d'.nreg 150022 = cs ∧
      d'.nreg 150023 = cm ∧ d'.nreg 150075 = MD + 1 + 1 + 1 ∧
      (∀ x, x ≠ 150021 → x ≠ 150022 → x ≠ 150023 → x ≠ 150075 → d'.nreg x = d.nreg x) ∧
      d'.nmem = d.nmem := by
  unfold cHead1
  exec_block
  all_goals first | (config_simp; rw [h00, h91]; omega) | skip
  simp_all
theorem cHead2_exec (hw : WordsBounded W d) {a cm T bit : ℕ}
    (h75 : d.nreg 150075 = a) (h91 : d.nreg 150091 = 1) (h96 : d.nreg 150096 = 6)
    (h23 : d.nreg 150023 = cm) (mD : d.nmem ztdf = T) (mE : d.nmem ztqdi = bit)
    (hMW : a + 2 ≤ W) (hcW : 2 * cm + 6 ≤ W) :
    ∃ d' k, Exec P W cHead2 d d' k ∧ k = 7 ∧ d'.nreg 150024 = T ∧ d'.nreg 150025 = bit ∧
      d'.nreg 150029 = 2 * cm ∧ d'.nreg 150032 = 2 * cm + 6 ∧ d'.nreg 150031 = 2 * cm + 5 ∧
      (∀ x, x ≠ 150024 → x ≠ 150025 → x ≠ 150029 → x ≠ 150031 → x ≠ 150032 → x ≠ 150075 →
        d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  unfold cHead2
  exec_block
  all_goals first | (config_simp; rw [h75, h91]; omega) | (config_simp; zuodb; omega) |
    (config_simp; rw [h23, h96]; omega) | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 h4 h5 h6 => ?_, rfl⟩
  · simp_all
  · simp_all
  · config_simp; omega
  · config_simp; omega
  · config_simp; omega
  simp_all
theorem cHead3_exec (hw : WordsBounded W d) {h : ℕ} {m₀ : ℕ → ℕ}
    (h13 : d.nreg 150013 = h) (h91 : d.nreg 150091 = 1) (h92 : d.nreg 150092 = 2)
    (h93 : d.nreg 150093 = 3) (mh : d.nmem h = m₀ h) (mh1 : d.nmem ztgn = m₀ ztgn)
    (mh2 : d.nmem zteu = m₀ zteu) (mh3 : d.nmem ztbba = m₀ ztbba)
    (hnW : P.n ≤ W) (hhW : h + 3 ≤ W) (hsW : m₀ ztgn + 2 ≤ W) :
    ∃ d' k, Exec P W cHead3 d d' k ∧ k = 9 ∧ d'.nreg 150027 = P.n ∧ d'.nreg 150033 = m₀ h ∧
      d'.nreg 150036 = m₀ ztgn + 2 ∧ d'.nreg 150034 = m₀ zteu ∧
      d'.nreg 150035 = m₀ ztbba ∧
      (∀ x, x ≠ 150027 → x ≠ 150033 → x ≠ 150034 → x ≠ 150035 → x ≠ 150036 → x ≠ 150075 →
        x ≠ 150076 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  unfold cHead3
  exec_block
  all_goals first | exact hnW | (config_simp; rw [h13, h91]; omega) |
    (config_simp; rw [h13, h91, mh1, h92]; omega) | (config_simp; rw [h13, h92]; omega) |
    (config_simp; rw [h13, h93]; omega) | skip
  simp_all

/-- **The set-up of the core.** -/
theorem cPre_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD mode : ℕ} {s e : WPos}
    (hD : ChainDescAt m₀ ztki zta H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ ztki = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (h00 : d.nreg 150000 = MD) (h01 : d.nreg 150001 = s.edge) (h02 : d.nreg 150002 = s.hgt)
    (h03 : d.nreg 150003 = e.edge) (h04 : d.nreg 150004 = e.hgt) (h09 : d.nreg 150009 = γ)
    (h13 : d.nreg 150013 = h) (h20 : d.nreg 150020 = mode) :
    ∃ d' k, Exec P W cPre d d' k ∧ k ≤ 12 * H.length + 60 ∧
      CoreRegs P C H Hh MD h γ mode s e m₀ d' ∧ FrameB Scr d d' := by
  zudn

  zuerk
  have hAW := S.hAW
  zucgk

  obtain ⟨hh3, -, -⟩ := grade_low S.hR
  obtain ⟨-, hpow, -⟩ := grade_low S.hR
  have hp0 := hpow 0 by_omega
  obtain ⟨hHost, hP, hs', hm', hT', hb'⟩ := hD
  zuwi
  -- the constants
  obtain ⟨d₁, k₁, e₁, hk₁, c90, c91, c92, c93, c96, r₁, m₁⟩ := cInit_exec (P := P) d hw by_omega
  have g₁ : ∀ x, x < 150090 → d₁.nreg x = d.nreg x := by_grind
  have mm : ztdbm := by_simp_all
  have a00 : d₁.nreg 150000 = MD := by_grind
  have a13 : d₁.nreg 150013 = h := by_grind
  have mA : d₁.nmem ztki = Hh := by_grind
  have mB : d₁.nmem ztqac = C.s := by_grind
  have mC : d₁.nmem ztnmx = C.m := by_grind
  have mD : d₁.nmem ztlfg = C.topIdx := by_grind
  have mh : d₁.nmem h = m₀ h := by_grind
  have mh1 : d₁.nmem _ = m₀ ztgn := mm _ by_omega
  have mh2 : d₁.nmem _ = m₀ zteu := mm _ by_omega
  have mh3 : d₁.nmem _ = m₀ ztbba := mm _ by_omega
  zud
  -- the descriptor and the handles
  obtain ⟨d₂, k₂, e₂, hk₂, o21, o22, o23, o75, r₂, m₂⟩ := cHead1_exec (P := P) d₁ w₁ a00 c91 mA mB mC
    by_omega
  have mD' : d₂.nmem ztlfg = C.topIdx := by_grind
  have mE' : d₂.nmem (MD + 1 + 1 + 1 + 1 + 1) = m₀ ztqad := by
    grind
  obtain ⟨d₃, k₃, e₃, hk₃, o24, o25, o29, o32, o31, r₃, m₃⟩ := cHead2_exec (P := P) d₂ e₂.wb_right
    o75 by_grind
    by_grind o23 mD' mE' by_omega
    by_omega
  have g₃ : ∀ x, x < 150021 ∨ x = 150026 ∨ x = 150028 ∨ x = 150030 ∨ 150037 ≤ x →
      x ≠ 150075 → d₃.nreg x = d₁.nreg x := fun x hx h75 => by
    rw [r₃ x by_omega by_omega by_omega by_omega by_omega h75,
      r₂ x by_omega by_omega by_omega h75]
  obtain ⟨d₄, k₄, e₄, hk₄, o27, o33, o36, o34, o35, r₄, m₄⟩ := cHead3_exec (P := P) d₃
    e₃.wb_right (m₀ := m₀) (by rw [g₃ _ by_omega by_omega, a13])
    (by rw [g₃ _ by_omega by_omega, c91]) (by rw [g₃ _ by_omega by_omega, c92])
    (by rw [g₃ _ by_omega by_omega, c93]) (by zundc; exact mh)
    (by zundc; exact mh1) (by zundc; exact mh2) (by zundc; exact mh3)
    by_omega by_omega by_omega
  zucc
  -- all the registers so far
  have f4 : ∀ x, (x < 150021 ∨ x = 150026 ∨ x = 150028 ∨ x = 150030 ∨ 150037 ≤ x) →
      x ≠ 150075 → x ≠ 150076 → x ≠ 150027 → x ≠ 150033 → x ≠ 150034 → x ≠ 150035 →
      x ≠ 150036 → d₄.nreg x = d₁.nreg x := fun x hx h1 h2 h3 h4 h5 h6 h7 => by
    rw [r₄ x h3 h4 h5 h6 h7 h1 h2, g₃ x hx h1]
  have b21 : d₄.nreg 150021 = Hh := by
    rw [r₄ _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega,
      r₃ _ by_omega by_omega by_omega by_omega by_omega by_omega, o21]
  have b22 : d₄.nreg 150022 = C.s := by
    rw [r₄ _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega,
      r₃ _ by_omega by_omega by_omega by_omega by_omega by_omega, o22]
  have b23 : d₄.nreg 150023 = C.m := by
    rw [r₄ _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega,
      r₃ _ by_omega by_omega by_omega by_omega by_omega by_omega, o23]
  have b24 : d₄.nreg 150024 = C.topIdx := by
    rw [r₄ _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega, o24]
  have b25 : d₄.nreg 150025 = m₀ ztqad := by
    rw [r₄ _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega, o25]
  have b29 : d₄.nreg 150029 = 2 * C.m := by
    rw [r₄ _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega, o29]
  have b31 : d₄.nreg 150031 = 2 * C.m + 5 := by
    rw [r₄ _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega, o31]
  have b32 : d₄.nreg 150032 = 2 * C.m + 6 := by
    rw [r₄ _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega, o32]
  have b91 : ztuua := by
    rw [f4 _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
      by_omega, c91]
  -- the tour start
  obtain ⟨d₅, k₅, e₅, hk₅, o28, r₅⟩ : ∃ d₅ k₅, Exec P W cS d₄ d₅ k₅ ∧ k₅ ≤ 5 ∧
      d₅.nreg 150028 = C.sideS C.sideBeta ∧ (∀ x, x ≠ 150028 → d₅.nreg x = d₄.nreg x) := by
    unfold cS Chazelle.Chain.sideS
    by_cases hb1 : d₄.nreg 150025 < d₄.nreg 150091
    · have hβ : ztidl := by
        grind
      refine spec_ifLtN_true hb1 (spec_instr ztgdq fun _ => ⟨by_omega, ?_,
        fun x hx => by zupbb⟩)
      config_simp; rw [b29, b24, hβ]; simp
    · by_cases hb2 : d₄.nreg 150091 < d₄.nreg 150025
      · have hβ : ztidl := by
          rw [b25, b91] at hb2
          cases hβ : C.sideBeta
          · rfl
          · have := hb'.2 hβ; omega
        refine spec_ifLtN_false hb1 (spec_ifLtN_true hb2 (spec_instr ztgdq
          fun _ => ztinp))
        config_simp; rw [b29, b24, hβ]; simp
      · have hβ : ztpiw := by
          rw [b25, b91] at hb1 hb2
          zubfo
        refine spec_ifLtN_false hb1 (spec_ifLtN_false hb2 (spec_instr ztlek
          fun _ => ztinp))
        config_simp; rw [b24, hβ]; simp
  zuef
  -- the number of host points
  have e₆ := Exec.copyN (P := P) w₅ 50060 150021
  set d₆ := ({ d₅ with nreg := upd d₅.nreg 50060 _ } : Config) with hd₆
  have m₆ : d₆.nmem = d.nmem := by
    show d₅.nmem = d.nmem
    rw [(exec_frameB e₅ (B := Bl [150028]) by_decide).2.2.1, m₄, m₃, m₂, m₁]
  have hH₆ : HostAt d₆.nmem Hh H := by
    rw [m₆, ← hHh]; exact hostAt_agree' by_omega (by zupbc; exact S.hHA)
      hm
  obtain ⟨d₇, k₇, e₇, hk₇, fr₇, o63, -⟩ := NFLoc.cnt_exec (P := P) (n := P.n) d₆ e₆.wb_right hH₆
    (by simp [hd₆, upd]; rw [r₅ _ by_omega, b21]) (by have := S.hHA; omega) by_omega
  have e₈ := Exec.copyN (P := P) e₇.wb_right 150026 50063
  set d₈ := ({ d₇ with nreg := upd d₇.nreg 150026 _ } : Config) with hd₈
  have g₈ : ∀ x, 150000 ≤ x → x ≠ 150026 → d₈.nreg x = d₅.nreg x := fun x hx h26 => by
    simp only [hd₈, upd]
    rw [ite_eq_right h26, fr₇.1 _ (by unfold Bhost; simp; omega)]
    zuogd; zvmyd
  have ex : Exec P W cPre d d₈ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (1 + (k₇ + 1))))))) := by
    unfold cPre cCount
    exact .seq e₁ ztey
  have gg : ∀ x, 150000 ≤ x → (x < 150021 ∨ x = 150030 ∨ 150037 ≤ x) → x ≠ 150075 →
      x ≠ 150076 → x ≠ 150033 → x ≠ 150034 → x ≠ 150035 → x ≠ 150036 → x ≠ 150027 →
      d₈.nreg x = d₁.nreg x := fun x h0 hx h1 h2 h3 h4 h5 h6 h7 => by
    rw [g₈ x h0 by_omega, r₅ x by_omega, f4 x by_omega h1 h2 h7 h3 h4 h5 h6]
  refine ⟨d₈, _, ex, by have := S.hlen; omega, ?_, exec_frameB ex by_decide⟩
  have k5 : ∀ x, 150000 ≤ x → x ≠ 150026 → x ≠ 150028 → d₈.nreg x = d₄.nreg x :=
    fun x h0 h1 h2 => by rw [g₈ x h0 h1, r₅ x h2]
  refine ⟨⟨by rw [k5 _ by_omega by_omega by_omega, b21],
      by rw [k5 _ by_omega by_omega by_omega, b22],
      by rw [k5 _ by_omega by_omega by_omega, b23],
      by simp only [hd₈, upd, ↓reduceIte]; rw [o63],
      by rw [g₈ _ by_omega by_omega, o28],
      by rw [k5 _ by_omega by_omega by_omega, b29],
      by rw [k5 _ by_omega by_omega by_omega, b91],
      by rw [gg _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega, c93],
      by rw [gg _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega, c96]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [k5 _ by_omega by_omega by_omega, o27],
    by rw [k5 _ by_omega by_omega by_omega, b31],
    by rw [k5 _ by_omega by_omega by_omega, b32],
    by rw [k5 _ by_omega by_omega by_omega, o33],
    by rw [k5 _ by_omega by_omega by_omega, o34],
    by rw [k5 _ by_omega by_omega by_omega, o35],
    by rw [k5 _ by_omega by_omega by_omega, o36], ?_, ?_⟩
  all_goals first
    | (rw [gg _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega, g₁ _ by_omega]; assumption)
    | (rw [gg _ by_omega by_omega by_omega by_omega by_omega by_omega by_omega
        by_omega by_omega]; assumption)
    | skip

/-- The cost bound of the core. -/
def coreCost (K γ : ℕ) : ℕ := genCost K γ + K + 20000

/-- **The core.** -/
theorem core_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ ztbwt I K)
    {ps₀ : List Pc} {MD mode : ℕ} {s e : WPos}
    (hD : ChainDescAt m₀ ztki zta H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ ztki = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (h00 : d.nreg 150000 = MD) (h01 : d.nreg 150001 = s.edge) (h02 : d.nreg 150002 = s.hgt)
    (h03 : d.nreg 150003 = e.edge) (h04 : d.nreg 150004 = e.hgt) (h09 : d.nreg 150009 = γ)
    (h13 : d.nreg 150013 = h) (h20 : d.nreg 150020 = mode) (hI : I ps₀ d)
    (hs : ProperPos ztc zta P.n s) (he : ProperPos ztc zta P.n e)
    (hs1 : s.edge < 2 * C.m + 7) (he1 : e.edge < 2 * C.m + 7)
    (hin : e.hgt = 0 ∨ (chainModel C).InnerPt ztwyx)
    (hwt : (chainModel C).arcWt ztwlj ztwli ≤ γ) :
    ∃ d' k ps, Exec P W ztvlt d d' k ∧ k ≤ coreCost K γ ∧ I ztrup d' ∧
      ArcOK C zta s e ps ∧ ztiuq ∧
      ps.length ≤ 2100 * ztir ∧ ztcqe := by
  zudn

  have hlen := S.hlen
  obtain ⟨d₁, k₁, e₁, hk₁, R₁, fr₁⟩ := cPre_exec S hD hMD hHh d hw hm h00 h01 h02 h03 h04 h09
    h13 h20
  have hm₁ : ztdbm := fun a ha => by rw [fr₁.2.2.1]; simp_all
  obtain ⟨d₂, k₂, e₂, hk₂, fr₂, i48, l48⟩ := decideS_exec S hD hMD hHh d₁ e₁.wb_right hm₁ R₁ hs he
    hs1 hin
  have hBd : ∀ r, 150000 ≤ r → r < 150044 → Bd r = false := fun r h1 h2 => by
    zumqh
  have hBd' : ∀ r, 150090 ≤ r → r < 150100 → Bd r = false := fun r h1 h2 => by
    zumqh
  have R₂ := R₁.of_frame'
    (fun r h1 h2 _ _ => fr₂.1 r by_simp_all)
    (by zundd; exact R₁.h90)
    (by zundd; exact R₁.chain.h91)
    (by zundd; exact R₁.h92)
    (by zundd; exact R₁.chain.h93)
    (by zundd; exact R₁.chain.h96)
  have hm₂ : ztkob := fun a ha => by rw [fr₂.2.2.1]; simp_all
  have hI₂ := hE.stable _ _ _ hI (fr₁.trans (FrameB.mono' fr₂ fun r hr => by
    unfold Scr at hr; unfold Bd; grind))
  zue
  have hpre : ∀ {d' : Config} {k : ℕ}, Exec P W _ d₂ d' k → Exec P W ztvlt d d' _ := fun ex => by
    unfold core; exact .seq e₁ (.seq e₂ ex)
  have hGc : ztxit := by_simp_all
  by_cases hsame : d₂.nreg 150090 < d₂.nreg 150048
  · -- the single piece `[s, e]`
    have hG : s.edge = e.edge ∧ (chainModel C).key _ s < (chainModel C).key _ e :=
      i48.1 by_omega
    have hpv : ztdjt := pSE_ok hs he hs1 he1
      (wt_same _ _ hs he hG.1 hG.2)
    obtain ⟨d₃, k₃, e₃, hk₃, hR₃, fr₃, -⟩ := pcSE_exec d₂ w₂ by_omega R₂.h01 R₂.h02
      R₂.h03 R₂.h04
    obtain ⟨d₄, k₄, e₄, hk₄, hI₄, -, mem₄⟩ := hE.run _ _ d₃ e₃.wb_right (hE.stable _ _ _ hI₂ fr₃) hR₃ hpv
    refine ⟨d₄, _, [pSE s e], hpre (.ifLtN_true hsame ztfml), ?_, hI₄,
      arcOK_single hs he hs1 he1 rfl rfl, by_simp_all, by_grind,
      fun a ha => by rw [mem₄ a ha, fr₃.2.2.1]; simp_all⟩
    unfold coreCost genCost; omega
  · have hns : ¬ (s.edge = e.edge ∧
        (chainModel C).key _ s < (chainModel C).key _ e) := fun hG => by
      have := i48.2 hG; rw [R₂.h90] at hsame; omega
    obtain ⟨d₃, k₃, ps, e₃, hk₃, hI₃, arc, hok, hl, hm₃⟩ := general_exec S hE hD hMD hHh d₂ w₂
      R₂ hm₂ hI₂ hs he hs1 he1 hns hwt
    refine ⟨d₃, _, ps, hpre (.ifLtN_false hsame e₃), ?_, hI₃, arc, hok, hl, hm₃⟩
    unfold coreCost; omega
def cutStore : Stmt := block [.storeN 140000 150050, .addN 140000 140000 140003,
  .storeN 140000 150051, .addN 140000 140000 140003, .storeN 140000 150052,
  .addN 140000 140000 140003, .storeN 140000 150053, .addN 140000 140000 140003,
  .storeN 140000 150054, .addN 140000 140000 140003]

/-- Kind `0`: two zero words. -/
def cutK0 : Stmt := block [.storeN 140000 140006, .addN 140000 140000 140003,
  .storeN 140000 140006, .addN 140000 140000 140003]

/-- Kind `1`: the descriptor and normal-form handles of the grade-table entry `150055`. -/
def cutK1 : Stmt := block [.loadN 140004 150055, .storeN 140000 140004,
  .addN 140000 140000 140003, .addN 140005 150055 140003, .loadN 140004 140005,
  .storeN 140000 140004, .addN 140000 140000 140003]

/-- **The arc-cutter's `emit`**: the record of the piece, if there is room. -/
def cutEmit : Stmt :=
  .ifLtN 140000 140007
    (.seq cutStore (.seq ztprm (.instr (.addN 140002 140002 140003))))
    .skip

/-! ## The records -/

/-- The records of the pieces `ps` from the list base `L + 1` on. -/
def RecOK (m₀ mem : ℕ → ℕ) (L : ℕ) (ps : List Pc) : Prop :=
  ∀ i (hi : i < ps.length),
    mem zthbc = (ps[i]'hi).s.edge ∧ mem ztdla = (ps[i]'hi).s.hgt ∧
    mem ztclq = (ps[i]'hi).e.edge ∧ mem ztdlb = (ps[i]'hi).e.hgt ∧
    mem ztley = (ps[i]'hi).kind ∧
    ((ps[i]'hi).kind = 1 → mem ztlez = m₀ (ps[i]'hi).entry ∧
      mem ztlfa = m₀ ztfau)

/-- **The invariant of `cutEmit`** (`Nmax` records fit below `LIM = A₀ + 1 + 7 Nmax`). -/
structure CutI (W A₀ Nmax : ℕ) (m₀ : ℕ → ℕ) (ps : List Pc) (c : Config) : Prop where
  alloc : c.nreg ALLOC = A₀
  base : c.nreg 140001 = A₀
  one : c.nreg 140003 = 1
  zero : c.nreg 140006 = 0
  lim : c.nreg 140007 = A₀ + 1 + 7 * Nmax
  limW : A₀ + 1 + 7 * Nmax + 7 ≤ W
  mem : ∀ a, a < A₀ → c.nmem a = m₀ a
  ptr : c.nreg 140000 = A₀ + 1 + 7 * min ps.length Nmax
  cnt : c.nreg 140002 = min ps.length Nmax
  recs : RecOK m₀ c.nmem A₀ ztwbw

/-! ## The pieces of `cutEmit` -/
theorem cutStore_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {p : ℕ}
    (h00 : c.nreg 140000 = p) (h03 : c.nreg 140003 = 1) (hp : p + 5 ≤ W) :
    ∃ c' k, Exec P W cutStore c c' k ∧ k = 10 ∧ c'.nreg 140000 = p + 5 ∧
      c'.nmem p = c.nreg 150050 ∧ c'.nmem ztr = c.nreg 150051 ∧
      c'.nmem ztcao = c.nreg 150052 ∧ c'.nmem ztdhu = c.nreg 150053 ∧
      c'.nmem zthiz = c.nreg 150054 ∧ ztbiu ∧
      ztivw := by
  unfold cutStore
  exec_block
  all_goals first | (config_simp; rw [h00, h03]; omega) | skip
  refine ztedx
  zulf
theorem cutK0_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {p : ℕ}
    (h00 : c.nreg 140000 = p) (h03 : c.nreg 140003 = 1) (h06 : c.nreg 140006 = 0)
    (hp : p + 2 ≤ W) :
    ∃ c' k, Exec P W cutK0 c c' k ∧ k = 4 ∧ c'.nreg 140000 = p + 2 ∧ c'.nmem p = 0 ∧
      c'.nmem ztr = 0 ∧ ztbiu ∧
      ztivw := by
  unfold cutK0
  exec_block
  all_goals first | (config_simp; rw [h00, h03]; omega) | skip
  refine ⟨rfl, ?_, ?_, ?_, fun a ha => ?_, fun x hx => ?_⟩
  all_goals simp only [upd, Config.nreg_mk, Config.nmem_mk, h00, h03, h06]
  zuefe
theorem cutK1_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {p en : ℕ}
    (h00 : c.nreg 140000 = p) (h03 : c.nreg 140003 = 1) (h55 : c.nreg 150055 = en)
    (hen : en + 1 < p) (hp : p + 2 ≤ W) :
    ∃ c' k, Exec P W cutK1 c c' k ∧ k = 7 ∧ c'.nreg 140000 = p + 2 ∧
      c'.nmem p = c.nmem en ∧ c'.nmem ztr = c.nmem (en + 1) ∧
      ztbiu ∧
      (∀ x, x ≠ 140000 → x ≠ 140004 → x ≠ 140005 → c'.nreg x = c.nreg x) := by
  unfold cutK1
  exec_block
  all_goals first | (config_simp; rw [h00, h03]; omega) | (config_simp; rw [h55, h03]; omega) |
    skip
  refine ⟨rfl, ?_, ?_, ?_, fun a ha => ?_, fun x h1 h2 h3 => ?_⟩
  all_goals simp only [upd, Config.nreg_mk, Config.nmem_mk, h00, h03, h55]
  zuefe

/-! ## The contract of `cutEmit` -/
variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}

/-- The grade-table entry of a kind-`1` piece lies below `A₀`. -/
theorem entry_lt (S : SEnv O P C H Hh h γ m₀ A₀ W) {pc : Pc} (hp : PcOK P C m₀ h γ pc)
    (hk : pc.kind = 1) : pc.entry + 2 < A₀ := by
  obtain ⟨g, b, -, hg, hb, hE, -⟩ := hp.2.2.2.2.2.2 hk
  zugun
  exact (grade_entry S.hR hg hb).2.2
theorem recOK_append {m₀ mem mem' : ℕ → ℕ} {L : ℕ} {ps : List Pc} {pc : Pc}
    (hold : RecOK m₀ mem L ps) (hsame : ∀ a, a < L + 1 + 7 * ps.length → mem' a = mem a)
    (h0 : mem' (L + 1 + 7 * ps.length) = pc.s.edge)
    (h1 : mem' (L + 1 + 7 * ps.length + 1) = pc.s.hgt)
    (h2 : mem' (L + 1 + 7 * ps.length + 2) = pc.e.edge)
    (h3 : mem' (L + 1 + 7 * ps.length + 3) = pc.e.hgt)
    (h4 : mem' (L + 1 + 7 * ps.length + 4) = pc.kind)
    (h56 : pc.kind = 1 → mem' (L + 1 + 7 * ps.length + 5) = m₀ pc.entry ∧
      mem' (L + 1 + 7 * ps.length + 6) = m₀ ztoei) :
    RecOK m₀ mem' L ztdvs := by
  zug
  zuvw
  zukng
  · zulpd
    obtain ⟨a0, a1, a2, a3, a4, a56⟩ := hold i hlt
    grind
  simp_all

/-- **The contract of the arc-cutter's `emit`.** -/
theorem cutEmit_ok (S : SEnv O P C H Hh h γ m₀ A₀ W) (Nmax : ℕ) :
    EmitOK P W cutEmit A₀ ztbwt (CutI W A₀ Nmax m₀) 30 := by
  refine ztfwi
  · zuiaz

    exact ⟨by zuonj; exact hI.alloc, by zumyu; exact hI.base,
      by zumyu; exact hI.one, by zumyu; exact hI.zero,
      by zumyu; exact hI.lim, hI.limW, fun a ha => by zunke; exact hI.mem a ha,
      by zumyu; exact hI.ptr, by zumyu; exact hI.cnt,
      by zunke; exact hI.recs⟩
  · obtain ⟨hA, hB, h1, h0, hL, hLW, hm, hp, hc, hrec⟩ := hI
    zudrq
    have hkind := hv.2.2.2.2.1
    zujtq
    · zulkn
      zujjk
      zufwn

      set p := A₀ + 1 + 7 * ps.length with hpdef
      have t₀ : c.nreg 140000 < c.nreg 140007 := by_omega
      obtain ⟨c₁, k₁, e₁, hk₁, q00, q0, q1, q2, q3, q4, qm, qr⟩ := cutStore_exec (P := P) c hw hp h1
        by_omega
      zud
      have b03 : c₁.nreg 140003 = 1 := by_simp_all
      -- the handles
      obtain ⟨c₂, k₂, e₂, hk₂, q20, q5, q6, qm₂, qr₂⟩ : ∃ c₂ k₂, Exec P W
          ztprm c₁ c₂ k₂ ∧ k₂ ≤ 9 ∧ c₂.nreg 140000 = p + 7 ∧
          (pc.kind = 1 → c₂.nmem ztkbt = m₀ pc.entry ∧ c₂.nmem ztoec = m₀ ztoei) ∧
          True ∧ (∀ a, a < p + 5 → c₂.nmem a = c₁.nmem a) ∧
          (∀ x, x ≠ 140000 → x ≠ 140004 → x ≠ 140005 → c₂.nreg x = c₁.nreg x) := by
        rcases hkind with hk0 | hk1
        · have t : c₁.nreg 150054 < c₁.nreg 140003 := by
            simp_all
          obtain ⟨c₂, k₂, e₂, hk₂, a0, -, -, am, ar⟩ := cutK0_exec c₁ w₁ q00 b03
            by_grind by_omega
          exact ⟨c₂, _, .ifLtN_true t e₂, by_omega, by rw [a0],
            by omega, trivial, am, by_grind⟩
        · have t : ¬ c₁.nreg 150054 < c₁.nreg 140003 := by
            simp_all
          have he := entry_lt S hv hk1
          obtain ⟨c₂, k₂, e₂, hk₂, a0, a5, a6, am, ar⟩ := cutK1_exec
            (en := pc.entry) c₁ w₁ q00 b03
            by_simp_all by_omega by_omega
          refine ⟨c₂, _, .ifLtN_false t e₂, by_omega, by rw [a0], fun _ => ztcp, trivial,
            am, ar⟩
          · grind
          grind
      zue
      have b02 : c₂.nreg 140002 = ps.length := by
        grind
      have b03' : c₂.nreg 140003 = 1 := by_grind
      have e₃ := Exec.addN (P := P) w₂ 140002 140002 140003 by_omega
      set c₃ := ({ c₂ with nreg := upd c₂.nreg 140002 _ } :
        Config) with hc₃
      have g₃ : ∀ x, x ≠ 140000 → x ≠ 140002 → x ≠ 140004 → x ≠ 140005 →
          c₃.nreg x = c.nreg x := fun x h1 h2 h3 h4 => by
        zuoge; grind
      have mem3 : ∀ a, a < p → c₃.nmem a = c.nmem a := fun a ha => by
        grind
      refine ⟨c₃, _, .ifLtN_true t₀ ztwrj, by_omega, ⟨?_, ?_, ?_, ?_, ?_, hLW,
        fun a ha => by_grind, ?_, ?_, ?_⟩, fun r hr => ?_,
        by grind⟩
      · rw [g₃ _ by_decide by_decide by_decide by_decide]; exact hA
      · grind
      · grind
      · grind
      · grind
      · zuoge
        rw [ite_eq_right by_omega, q20, List.length_append, List.length_singleton,
          min_eq_left by_omega]
        omega
      · simp only [hc₃, upd, ↓reduceIte]
        rw [b02, b03', List.length_append, List.length_singleton, min_eq_left by_omega]
      · zulpf
        refine recOK_append hrec by_omega ?_ ?_ ?_ ?_ ?_ ?_
        · grind
        · grind
        · grind
        · grind
        · grind
        omega
      · zumrb
        exact g₃ r by_omega by_omega by_omega by_omega
    · zukdu
      zujjk
      have t₀ : ¬ c.nreg 140000 < c.nreg 140007 := by_omega
      refine ⟨c, _, .ifLtN_false t₀ ztjd, by_omega, ⟨hA, hB, h1, h0, hL, hLW, hm, ?_, ?_, ?_⟩,
        by omega, by_omega⟩
      · grind
      · grind
      grind
def cutLimBody : Stmt := block [.addN 140009 140009 140009, .addN 140007 140007 140008]

/-- The constants of the set-up. -/
def cutInitA : Stmt :=
  block [.constN 140003 1, .constN 140006 0, .constN 140008 14700, .constN 140002 0,
    .constN 140009 1]

/-- The pointers of the set-up. -/
def cutInitB : Stmt := block [.copyN 140001 ALLOC, .addN 140000 ALLOC 140003]

/-- The set-up of the arc-cutter. -/
def cutInit : Stmt :=
  .seq cutInitA (.seq cutInitB (.seq (.instr (.addN 140007 140000 140008))
    (.whileLtN 140009 150009 cutLimBody)))

/-- Raise the allocator one by one to the end of the list. -/
def cutBump : Stmt := .whileLtN ALLOC 140000 (.instr ztrhw)

/-- The finish of the arc-cutter. -/
def cutFin : Stmt := .seq ztksq cutBump

/-- **The arc-cutter.** -/
def cutter : Stmt := .seq cutInit (.seq (core cutEmit) cutFin)
variable {P : Polygon} {W : ℕ}
/-- A `while` loop with a potential that pays for its steps, and a quantity that grows by at
most the step count. -/
theorem whileLtN_potential_lb' {a b : ℕ} {body : Stmt}
    (I : Config → Prop) (Φ ψ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c ∧ ψ c' ≤ ψ c + k)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W ztpx c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ Φ c + 2 ∧ ψ c' ≤ ψ c + k := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    zudm
    · zubu

    · zulfw

/-- **The set-up of the arc-cutter.** -/
theorem cutInit_exec (d : Config) (hw : WordsBounded W d) {γ A₀ : ℕ}
    {m₀ : ℕ → ℕ} (hm : ∀ a, a < A₀ → d.nmem a = m₀ a) (h09 : d.nreg 150009 = γ)
    (hA : d.nreg ALLOC = A₀) (hγW : 2 * γ ≤ W)
    (hroom : A₀ + 14700 * Nat.clog 2 γ + 14708 ≤ W) :
    ∃ d' k Nmax, Exec P W cutInit d d' k ∧ k ≤ 5 * Nat.clog 2 γ + 20 ∧
      CutI W A₀ Nmax m₀ [] d' ∧ 2100 * Nat.log 2 γ + 2100 ≤ Nmax ∧
      (∀ x, x / 10000 ≠ 14 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  zuk
  have hW1 : A₀ + 14708 ≤ W := by_omega
  obtain ⟨da, ka, ea, hka, a03, a06, a08, a02, a09, ra, ma⟩ : ∃ d₁ k₁, Exec P W cutInitA d d₁ k₁ ∧
      k₁ = 5 ∧ d₁.nreg 140003 = 1 ∧ d₁.nreg 140006 = 0 ∧ d₁.nreg 140008 = 14700 ∧
      d₁.nreg 140002 = 0 ∧ d₁.nreg 140009 = 1 ∧
      (∀ x, x / 10000 ≠ 14 → d₁.nreg x = d.nreg x) ∧ d₁.nmem = d.nmem := by
    zujup
    unfold cutInitA
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl⟩
    all_goals first | (config_simp; done) | skip
    zubd
  have hAa : ztutq := by_simp_all
  obtain ⟨db, kb, eb, hkb, b01, b00, rb, mb⟩ : ∃ d₁ k₁, Exec P W cutInitB da d₁ k₁ ∧
      k₁ = 2 ∧ d₁.nreg 140001 = A₀ ∧ d₁.nreg 140000 = A₀ + 1 ∧
      (∀ x, x ≠ 140001 → x ≠ 140000 → d₁.nreg x = da.nreg x) ∧ d₁.nmem = da.nmem := by
    zuffj

    unfold cutInitB
    rw [hAl]
    exec_block
    all_goals first | (config_simp; rw [hAa, a03]; omega) | skip
    simp_all
  have b03 : db.nreg 140003 = 1 := by_simp_all
  have b08 : db.nreg 140008 = 14700 := by_simp_all
  have ec := Exec.addN (P := P) eb.wb_right 140007 140000 140008 by_omega
  set d₁ := ({ db with nreg := upd db.nreg 140007 _ } : Config)
    with hd₁
  have r₁ : ∀ x, x / 10000 ≠ 14 → d₁.nreg x = d.nreg x := fun x hx => by
    zuipl

  have g₁ : ∀ x, x ≠ 140007 → d₁.nreg x = db.nreg x := by_simp_all
  have o03 : d₁.nreg 140003 = 1 := by_simp_all
  have o06 : d₁.nreg 140006 = 0 := by_simp_all
  have o08 : d₁.nreg 140008 = 14700 := by_simp_all
  have o01 : d₁.nreg 140001 = A₀ := by_simp_all
  have o00 : d₁.nreg 140000 = A₀ + 1 := by_simp_all
  have o02 : d₁.nreg 140002 = 0 := by_simp_all
  have o09 : d₁.nreg 140009 = 1 := by_simp_all
  have o07 : d₁.nreg 140007 = A₀ + 1 + 14700 := by
    simp_all
  have m₁ : ztpod := by
    simp_all
  -- the doubling loop
  obtain ⟨T, hT⟩ : ztorv := by_simp_all
  zugdl
  let Inv : Config → Prop := fun c => WordsBounded W c ∧ c.nmem = d.nmem ∧
    (∀ x, x / 10000 ≠ 14 → c.nreg x = d.nreg x) ∧ c.nreg 140003 = 1 ∧ c.nreg 140006 = 0 ∧
    c.nreg 140008 = 14700 ∧ c.nreg 140001 = A₀ ∧ c.nreg 140000 = A₀ + 1 ∧ c.nreg 140002 = 0 ∧
    ∃ t, c.nreg 140009 = 2 ^ t ∧ c.nreg 140007 = A₀ + 1 + ztjel ∧ t ≤ T
  have I₁ : Inv d₁ := ⟨ec.wb_right, m₁, r₁, o03, o06, o08, o01, o00, o02, 0, by_omega,
    by zupbd, Nat.zero_le _⟩
  obtain ⟨d₂, k₂, e₂, I₂, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 140009) (b := 150009)
    (body := cutLimBody) Inv
    (fun c => T + 1 - (Nat.log 2 (c.nreg 140009))) 2 ztjvp
    (fun c ⟨hw', hm', hr', h3, h6, h8, h1, h0, h2, t, h9, h7, ht⟩ hlt => by
      zubbo

      have hmul := Nat.mul_le_mul_left 14700 ztmoh
      have hW7 : A₀ + 1 + ztjel + 14700 ≤ W := by
        grind
      unfold cutLimBody
      obtain ⟨c', k, e, hk, o9, o7, r', m'⟩ : ∃ c' k, Exec P W (block [.addN 140009 140009 140009,
          .addN 140007 140007 140008]) c c' k ∧ k = 2 ∧ c'.nreg 140009 = 2 ^ (t + 1) ∧
          c'.nreg 140007 = A₀ + 1 + ztjel + 14700 ∧
          (∀ x, x ≠ 140009 → x ≠ 140007 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem := by
        have h2W : ztmsr := by_omega
        clear hroom hγW hm hmul hlt
        exec_block
        all_goals first | (config_simp; rw [h9]; omega) | (config_simp; rw [h7, h8]; omega) |
          skip
        refine ztdqy
        · config_simp; omega
        · config_simp; grind
        · zubd
      refine ⟨c', k, e, ⟨e.wb_right, by_grind, by_grind, by_grind,
        by grind, by_grind,
        by grind, by_grind,
        by grind, t + 1, o9, by_grind, by_omega⟩,
        by omega, ?_⟩
      zufoe
      omega) I₁
  obtain ⟨hw₂, hm₂, hr₂, h3, h6, h8, h1, h0, h2, t, h9, h7, ht⟩ := I₂
  zuegd

  have hlog : ztsce := by
    zujde
    · zukrp
    · have := Nat.log_lt_of_lt_pow (b := 2) (x := t + 1) (y := γ) by_omega
        by_omega
      omega
  have hmul := Nat.mul_le_mul_left 14700 ht
  zukdf
  refine ⟨d₂, ka + ztzwr, 2100 * t + 2100, .seq ea ztnck, ?_,
    ⟨by_grind, h1, h3, h6, by_grind, by_linarith, fun a ha => by_grind,
    by grind,
    by grind, fun i hi => by_grind⟩, by_omega, hr₂, hm₂⟩
  omega

/-- **The finish of the arc-cutter.** -/
theorem cutFin_exec {W A₀ Nmax : ℕ} {m₀ : ℕ → ℕ} {ps : List Pc} (d : Config)
    (hw : WordsBounded W d) (hI : CutI W A₀ Nmax m₀ ps d) (hq : ps.length ≤ Nmax) :
    ∃ d' k, Exec P W cutFin d d' k ∧ k ≤ 21 * ps.length + 10 ∧ d'.nreg 150010 = A₀ ∧
      d'.nmem A₀ = ps.length ∧ (∀ a, a ≠ A₀ → d'.nmem a = d.nmem a) ∧
      d'.nreg ALLOC = A₀ + 1 + 7 * ps.length ∧ d'.nreg ALLOC ≤ d.nreg ALLOC + k ∧
      (∀ x, x ≠ ALLOC → x ≠ 150010 → d'.nreg x = d.nreg x) ∧ d'.rreg = d.rreg ∧
      d'.rmem = d.rmem ∧ d'.output = d.output := by
  zuk
  obtain ⟨hA, hB, h1, -, -, hLW, -, hp, hc, -⟩ := hI
  rw [min_eq_left hq] at hp hc
  obtain ⟨d₁, k₁, e₁, hk₁, o10, om, omo, r₁, rr₁, rm₁, oo₁⟩ : ∃ d₁ k₁, Exec P W
      ztksq d d₁ k₁ ∧ k₁ = 2 ∧
      d₁.nreg 150010 = A₀ ∧ d₁.nmem A₀ = ps.length ∧ (∀ a, a ≠ A₀ → d₁.nmem a = d.nmem a) ∧
      (∀ x, x ≠ 150010 → d₁.nreg x = d.nreg x) ∧ d₁.rreg = d.rreg ∧ d₁.rmem = d.rmem ∧
      d₁.output = d.output := by
    exec_block
    simp_all
  set E := A₀ + 1 + 7 * ps.length with hE
  let Inv : Config → Prop := fun c => WordsBounded W c ∧ c.nreg ALLOC ≤ E ∧
    (∀ x, x ≠ ALLOC → c.nreg x = d₁.nreg x) ∧ c.nmem = d₁.nmem ∧ c.rreg = d₁.rreg ∧
    c.rmem = d₁.rmem ∧ c.output = d₁.output
  have a0 : ztutt := by_simp_all
  obtain ⟨d₂, k₂, e₂, ⟨hw₂, hA₂, hr₂, hm₂, hrr₂, hrm₂, ho₂⟩, hx₂, hk₂, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := ALLOC) (b := 140000)
    (body := .instr ztrhw) Inv ztjvn
    ztesf ztcvf
    (fun c ⟨hw', hA', hr', hm', hrr', hrm', ho'⟩ ht => by
      have e3 : c.nreg 140003 = 1 := by_simp_all
      have e0 : c.nreg 140000 = E := by_simp_all
      zukqt
      have ex := Exec.addN (P := P) hw' ALLOC ALLOC 140003 by_omega
      refine ⟨_, 1, ex, ⟨ex.wb_right, ?_, fun x hx => ?_, hm', hrr', hrm', ho'⟩, ?_, ?_⟩
      · simp_all
      · simp_all
      · zudlc
      simp_all)
    ⟨e₁.wb_right, by_omega, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have e0 : d₂.nreg 140000 = E := by_simp_all
  zukqu
  refine ⟨d₂, k₁ + k₂, by unfold cutFin cutBump; exact .seq e₁ e₂, ?_, ?_, ?_, fun a ha => ?_,
    by omega, ?_, fun x h1 h2 => ?_, by_simp_all, by_simp_all, by_simp_all⟩
  · omega
  · simp_all
  · simp_all
  · simp_all
  · omega
  simp_all
end
end ShootCut
namespace SweepPrim
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf)
@[expose] public section
def Bprim (r : ℕ) : Bool :=
  decide (10000 ≤ r ∧ r < 10600) || decide (50000 ≤ r ∧ r < 50200) ||
    decide (50210 ≤ r ∧ r < 51000)

/-- The bands of the primitives. -/
def primBands : Finset ℕ := {bSign, bLocate}
theorem Bprim_band (r : ℕ) (h : Bprim r = true) : bandOf r ∈ primBands ∧ r ≠ ALLOC := by
  simp only [Bprim, Bool.or_eq_true, decide_eq_true_eq] at h
  zudfh

/-- **The precondition of a primitive**: good environment, word bound, a well-formed chain
descriptor below the allocator at the address in `50200`, and the input condition. -/
def PrimPre (Inp : Polygon → ℕ → Chain → Config → Prop) (P : Polygon) (W : ℕ) (c : Config) :
    Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧ ChainWF P ztm c.nmem ztbok ∧
    ∃ H C, ChainDescAt c.nmem ztbok zta H C ∧ Inp P W C c

/-- **The postcondition of a primitive**: the output condition for the chain of the
descriptor. -/
def PrimPost (Out : Polygon → Chain → Config → Config → Prop) (P : Polygon) (c c' : Config) :
    Prop :=
  ∀ H C, ChainDescAt c.nmem ztbok zta H C → Out P C c c'

/-- The input registers survive `pHead`. -/
theorem pHead_inputs {c c' : Config} (h : FrameB Bhead c c') :
    ∀ r, 50200 ≤ r → r < 50210 → c'.nreg r = c.nreg r := fun r h1 h2 =>
  h.1 r (by simp only [Bhead, Bhost, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)

/-- **From an execution lemma of the core to the contract of the primitive.** -/
theorem prim_meets {core : Stmt} {B : ℕ → Bool} {K : ℕ}
    {Inp : Polygon → ℕ → Chain → Config → Prop} {Out : Polygon → Chain → Config → Config → Prop}
    (hB : ∀ r, B r = true → Bprim r = true) (hwr : wr B ztsqh = true)
    (hcore : ∀ (P : Polygon) (W : ℕ) (H : Host) (C : Chain) (c₀ c : Config),
      ChainDescAt c₀.nmem (c₀.nreg 50200) zta H C →
      CEnv P W H C c → Inp P W C c₀ → (∀ r, 50200 ≤ r → r < 50210 → c.nreg r = c₀.nreg r) →
      ∃ c' k, Exec P W core c c' k ∧ k ≤ K ∧ Out P C c₀ c') :
    Meets ztsqh primBands ztqbn ztqbm (fun _ _ => K + 800) := by
  intro P W c hw ⟨hG, hW, hwf, H, C, hC, hin⟩ hroom
  obtain ⟨hX5, hwf'⟩ := hwf
  obtain ⟨hlen, hHwf, haW, hs⟩ := hwf' H C hC
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hE₁⟩ := pHead_exec hG hW c hw rfl hC by_omega hlen hHwf
    by_omega hs
  obtain ⟨c₂, k₂, e₂, hk₂, hout⟩ := hcore P W H C c c₁ hC hE₁ hin (pHead_inputs f₁)
  have ex : ztpjk := .seq e₁ e₂
  refine ⟨c₂, _, ex, by_grind, fun H' C' hC' => ?_, frame_of_frameB (exec_frameB ex hwr)
    (fun r hr => Bprim_band r by_grind) _⟩
  rw [← chain_eq_of_desc hC hC']
  omega

/-! ## The direction of a walk edge -/

/-- The direction procedure of `NFLoc.chainDir` without its header (edge in `50002`). -/
def dirCore : Stmt :=
  .ifLtN 50002 50081 smallDir
    (.seq ztbin
      ztlzy)

/-- Restore the chain environment (the constant `1` and the host count). -/
def envRestore : Stmt := .seq ztfeq ztkpq

/-- **The direction code of the walk edge in `50002`** into `10502`. -/
def dirAt : Stmt := .seq dirCore envRestore

/-- The registers `dirCore` may write: those of `NFLoc`'s direction procedure except the
descriptor registers of the chain environment. -/
def Bdc (r : ℕ) : Bool :=
  Bdir r && !([50052, 50053, 50054, 50055, 50060, 50081, 50082, 50083, 50084, 50085].contains r)
theorem wr_dirCore : wr Bdc dirCore = true := by_decide
theorem wr_dirAt : wr Bdir dirAt = true := by_decide
variable {P : Polygon} {W : ℕ} (M : Model)
/-- **The direction code of a walk edge** (at most `82 |H| + 640` steps). -/
theorem dirAt_exec {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {e : ℕ} (h02 : c.nreg 50002 = e) (he : e < 2 * C.m + 7) :
    ∃ c' k, Exec P W dirAt c c' k ∧ k ≤ 82 * H.length + 640 ∧ FrameB Bdir c c' ∧
      CEnv P W H C c' ∧ c'.nreg 10502 = dirCode ztc e := by
  zuyv
  zucvu
  zuol
  zuc
  have hNlen := hE.n_eq
  zubnw
  zuwi
  zubb
  -- the core
  obtain ⟨c₁, k₁, e₁, hk₁, d₁⟩ : ∃ c₁ k₁, Exec P W dirCore c c₁ k₁ ∧ k₁ ≤ 70 * H.length + 600 ∧
      c₁.nreg 10502 = dirCode ztc e := by
    zubta
    · obtain ⟨c₂, k₂, e₂, hk₂, d₂⟩ := smallDir_exec c hw by_omega hE.r32 hE.r82
        hE.r83 hE.r84 hE.r85 by_omega
      refine ⟨c₂, _, .ifLtN_true ztlhj e₂, by_omega, ?_⟩
      rw [d₂, h02, chain_dirCode_small C hsm]
    obtain ⟨c₂, k₂, e₂, hk₂, q56, q57, r₂⟩ : ∃ c₂ k₂, Exec P W
        ztbin c c₂ k₂ ∧ k₂ = 2 ∧
        c₂.nreg 50056 = e - 6 ∧ c₂.nreg 50057 = e - 6 - C.m ∧
        ∀ r, r ≠ 50056 → r ≠ 50057 → c₂.nreg r = c.nreg r := by
      exec_block
      refine ⟨rfl, by config_simp; zuopo, by config_simp; rw [h02, hE.r81, hE.r53],
        by simp_all⟩
    zue
    have p53 : ztpnh := by rw [r₂ _ by_omega by_omega, hE.r53]
    zucus
    · zufuu
      have hH₂ : HostAt c₂.nmem ztmge H := by
        zubfs
        zuodc; exact hE.hH
      obtain ⟨c₃, k₃, e₃, hk₃, sp₁, sp₂, hsp₁, hsp₂, d₃⟩ := chGeneral_exec hG hW c₂ w₂
        hH₂ hE.wf hE.aW hE.NW hE.hs by_omega hT hi
        (by rw [r₂ _ by_omega by_omega, hE.r32]) by_simp_all
        (by rw [r₂ _ by_omega by_omega, hE.r52]) p53
        (by rw [r₂ _ by_omega by_omega, hE.r54]) rfl q56
      refine ⟨c₃, _, .ifLtN_false ztlhj
        ztgxc, by_omega, ?_⟩
      zubsj

      have hS : (if c₂.nreg 50055 = 1 then C.topIdx else 2 * C.m - C.topIdx) =
          C.sideS C.sideBeta := by
        rw [r₂ _ by_omega by_omega]
        zueeu

        · rw [ite_eq_left (hE.r55.2 hb), ite_eq_left hb]
        · rw [ite_eq_right (mt hE.r55.1 hb), ite_eq_right hb]
      zupw

      rw [chain_vertex_host C hE.hP _ ztepz,
        chain_vertex_host C hE.hP _ ztepz]
    · zufvg
      have hsm' : ¬ c.nreg 50002 < c.nreg 50081 := by zuopo; omega
      have hg' : ¬ c₂.nreg 50057 < c₂.nreg 50053 := by_omega
      refine ⟨{ c₂ with nreg := upd c₂.nreg 10502 1 }, _, .ifLtN_false hsm'
        (.seq e₂ (.ifLtN_false hg' ztpxz)), by_omega, ?_⟩
      zufb
      zukuw
  have f₁ := exec_frameB e₁ wr_dirCore
  zud
  -- restoring the environment
  have e₂ := Exec.constN (P := P) w₁ 50032 1 by_omega
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 50032 1 } with hc₂
  zue
  have m₂ : ztckc := by zumxp; exact f₁.2.2.1
  have k₂ : ∀ r, Bdc r = false → r ≠ 50032 → c₂.nreg r = c.nreg r := fun r hr h => by
    zumxp; zvmwf; zvnoi; exact f₁.1 r hr
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, n63, E₃⟩ := cnt_exec (P := P) (n := P.n) c₂ w₂
    (by zunbg; exact hE.hH) (k₂ _ by_decide by_decide)
    hE.aW (by have := hE.NW; omega)
  zubj
  have e₄ := Exec.copyN (P := P) w₃ 50087 50063
  set c₄ : Config := { c₃ with nreg := upd c₃.nreg 50087 _ } with hc₄
  have ex : Exec P W dirAt c c₄ _ := .seq e₁ ztcb
  have r₄ : ∀ r, r ≠ 50087 → c₄.nreg r = c₃.nreg r := by_simp_all
  zubgf
  refine ⟨c₄, _, ex, by_omega, exec_frameB ex wr_dirAt, ?_, ?_⟩
  · refine hE.keep e₄.wb_right (by zunbf; show c₃.nmem = c.nmem; rw [f₃.2.2.1, m₂])
      fun r hr => ?_
    zujs
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · zunnj; simp [hE.r32]
    · zubw
    · zubw
    · zubw
    · zubw
    · zubw
    · rw [r₄ _ by_decide, E₃.h61, hE.host.h61]
    · rw [r₄ _ by_decide, E₃.h67, hE.host.h67]
    · rw [r₄ _ by_decide, E₃.h68, hE.host.h68]
    · rw [r₄ _ by_decide, E₃.h69, hE.host.h69]
    · zubw
    · zubw
    · zubw
    · zubw
    · zubw
    · zunbf; simp [n63, hE.r87]
  · zunnj; simp_all

/-! ## Turning tests -/

/-- The sign code of a real number: `1` positive, `2` negative, `0` zero. -/
noncomputable def sgnCode (x : ℝ) : ℕ := if 0 < x then 1 else if x < 0 then 2 else 0

/-- The sign code the machine computes from a direction code `d` and a direction register `σ`. -/
def turnCode (d σ : ℕ) : ℕ :=
  if d = 0 then 0 else if σ = 1 then (if d = 2 then 1 else 2) else (if d = 2 then 2 else 1)

/-- The output of the turning tests: `50210 := turnCode (10502) (50203)`. -/
def turnOut : Stmt :=
  .ifLtN 10502 50032 ztbki
    (.ifLtN 50203 50032
      ztzab
      (.ifLtN 50032 50203
        ztzab
        (.ifLtN 50032 10502 ztbwr ztdsb)))
theorem turnOut_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W)
    (h32 : c.nreg 50032 = 1) (hd : c.nreg 10502 ≤ 2) :
    ∃ c' k, Exec P W turnOut c c' k ∧ k ≤ 9 ∧ c'.nreg 50210 = turnCode ztggz
      ztdzm ∧ ∀ r, r ≠ 50210 → c'.nreg r = c.nreg r := by
  unfold turnOut
  have fin : ∀ v, v ≤ 2 → v = turnCode ztggz ztdzm →
      ∃ c' k, Exec P W ztoud c c' k ∧ k = 1 ∧
      c'.nreg 50210 = turnCode ztggz ztdzm ∧
        ∀ r, r ≠ 50210 → c'.nreg r = c.nreg r := fun v hv hvt =>
    ⟨_, 1, Exec.constN hw _ _ by_omega, rfl, by_simp_all, by_simp_all⟩
  unfold turnCode at fin
  by_cases h0 : c.nreg 10502 < c.nreg 50032
  · obtain ⟨c', k, e, hk, h1, h2⟩ := fin 0 by_omega by_grind
    exact ⟨c', _, .ifLtN_true h0 e, by_omega, h1, h2⟩
  rw [h32] at h0
  have g0 : ¬ c.nreg 10502 < c.nreg 50032 := by_omega
  by_cases hs : c.nreg 50203 < c.nreg 50032
  · zukrx
    have gs : c.nreg 50203 < c.nreg 50032 := by_omega
    by_cases h2 : c.nreg 50032 < c.nreg 10502
    · zukrw
      zuzi
      exact ⟨c', _, .ifLtN_false g0 (.ifLtN_true gs ztdrx),
        by omega, h1, h3⟩
    · zukrw
      zuzh
      exact ⟨c', _, .ifLtN_false g0 (.ifLtN_true gs ztejp),
        by omega, h1, h3⟩
  zukrx
  have gs : ¬ c.nreg 50203 < c.nreg 50032 := by_omega
  by_cases hs2 : 1 < c.nreg 50203
  · have gs2 : c.nreg 50032 < c.nreg 50203 := by_omega
    zuiri
    · zuzi
      exact ⟨c', _, .ifLtN_false g0 (.ifLtN_false gs (.ifLtN_true gs2
        ztdrx)), by_omega, h1, h3⟩
    · zuzh
      exact ⟨c', _, .ifLtN_false g0 (.ifLtN_false gs (.ifLtN_true gs2
        ztejp)), by_omega, h1, h3⟩
  · have gs2 : ¬ c.nreg 50032 < c.nreg 50203 := by_omega
    zuiri
    · zuzh
      exact ⟨c', _, .ifLtN_false g0 (.ifLtN_false gs (.ifLtN_false gs2
        ztdrx)), by_omega, h1, h3⟩
    · zuzi
      exact ⟨c', _, .ifLtN_false g0 (.ifLtN_false gs (.ifLtN_false gs2
        ztejp)), by_omega, h1, h3⟩
theorem dirCode_le_two (e : ℕ) : dirCode M e ≤ 2 := by
  zuhal

/-- **The turning sign after a vertex**: `sideCross (b - v) (s, 0)` for the walk edge `v → b`. -/
theorem sgnCode_turnNext (p σ : ℕ) :
    sgnCode (sideCross ztbajf (ztlmz : Point)) =
      turnCode (dirCode M p) σ := by
  have e : sideCross ztbajf (ztlmz : Point) =
      -(dirOf σ * ((M.W.vtx ztwjk).2 - (M.W.vtx p).2)) := by
    zule
  zui
  unfold sgnCode turnCode dirCode Model.wa Model.wb dirOf
  split_ifs <;> first | rfl | omega | (exfalso; linarith)

/-- **The turning sign before a vertex**: `sideCross (s, 0) (a - v)` for the walk edge
`a → v`. -/
theorem sgnCode_turnPrev {p : ℕ} (hp : p < M.W.n) (σ : ℕ) :
    sgnCode (sideCross (ztlmz : Point) ztwll) =
      turnCode (dirCode M ztcm) σ := by
  have hq : ztbaqx := by
    zuiy
    zujdb
    · rw [Nat.zero_add, Nat.mod_eq_of_lt (show M.W.n - 1 < M.W.n by omega),
        Nat.sub_add_cancel hn, Nat.mod_self]
    · rw [show p + M.W.n - 1 = ztoq + M.W.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show p - 1 < M.W.n by omega), Nat.sub_add_cancel h0,
        Nat.mod_eq_of_lt hp]
  rw [← sgnCode_turnNext M _ σ, hq]
  zucr
  zule
variable (v f p : Point)
/-- The orientation of the far arm and a point at a height strictly between. -/
theorem det_lerp (hne : f.2 ≠ v.2) :
    det v f p = (f.2 - v.2) * ((Geometry.lerp v f zteje).1 - p.1) := by
  have : f.2 - v.2 ≠ 0 := sub_ne_zero.2 hne
  simp only [det, Geometry.lerp_fst]
  grind

/-- **The cap direction from an orientation test.** -/
theorem capx_iff (hne : f.2 ≠ v.2) :
    p.1 < (Geometry.lerp v f zteje).1 ↔
      (v.2 < f.2 ∧ 0 < det v f p) ∨ (f.2 < v.2 ∧ ¬ 0 < det v f p ∧ ¬ det v f p = 0) := by
  rw [det_lerp v f p hne]
  set L := (Geometry.lerp v f zteje).1
  zuto
  · -- `f` below `v`
    have hn : f.2 - v.2 < 0 := by_linarith
    constructor
    · intro hp; right
      refine ⟨h, ?_, ?_⟩
      · intro hc; nlinarith
      grind
    · rintro (⟨h1, -⟩ | ⟨-, h2, h3⟩)
      · linarith
      · zuca
        rcases hc.lt_or_eq with hc | hc
        · exact h2 by_nlinarith
        simp_all
  · have hp' : 0 < f.2 - v.2 := by_linarith
    constructor
    · simp_all
    · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
      · simp_all
      grind

/-- The height index of a symbolic point. -/
def shv : SymPt → ℕ
  | .vtx i => i
  | .onEdge _ h => h
theorem eval_snd_shv (Q : Polygon) (s : SymPt) : (s.eval Q).2 = (Q.vtx (shv s)).2 := by
  cases s <;> rfl

/-! ## The host point of a chain vertex -/

/-- The host point of chain vertex `50120` into `dst … dst + 2`. -/
def cvLoad (dst : ℕ) : Stmt :=
  .seq (.instr (.copyN 50091 50120))
    ztdes

/-- The registers written by `cvLoad dst`. -/
def Bcv (dst r : ℕ) : Bool := r == 50091 || Bhost r || decide ztlnb
theorem wr_cvLoad (dst : ℕ) : wr ztuwr ztqkb = true := by
  have h2 := wr_mono wr_hostPt (B' := Bcv dst) (fun r hr => by simp [Bcv, hr])
  simp only [cvLoad, copies, List.map_cons, List.map_nil, block_cons, block_nil, wr, wrOK, h2]
  simp [Bcv]

/-- **The host point of a chain vertex.** -/
theorem cvLoad_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {k : ℕ} (h120 : c.nreg 50120 = k) (hk : k ≤ C.m) {dst : ℕ}
    (hdst : 50100 ≤ dst) :
    ∃ c' k', Exec P W ztqkb c c' k' ∧ k' ≤ 27 * H.length + 20 ∧ FrameB ztuwr c c' ∧
      CEnv P W H C c' ∧ ∃ sp : SymPt, SymPtIn c' dst sp ∧ sp.Lt P.n ∧
        sp.eval zta = C.vertex k := by
  have e₁ := Exec.copyN (P := P) hE.wb 50091 50120
  have hE₁ : ztrfh := hE.frame (exec_frameB e₁ (B := fun r => r == 50091) by_decide)
    e₁.wb_right by_decide
  zubqu
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, E₂, sp, hsp, hin⟩ := hostPt_exec (P := P) _ hE₁.host hE₁.hH
    hE₁.wf (by have := hE₁.hW; omega) hE₁.aW hE₁.NW hE₁.r52 hE₁.r87 (k := k)
    by_simp_all hE₁.hs by_omega
  have hE₂ : CEnv P W H C c₂ := hE₁.of_host E₂ f₂
  obtain ⟨c₃, e₃, h3, h3', _h3r, h3m, _h3rm, _h3o⟩ := copies_exec (P := P)
    [ztjud, ztgii, ztgij] c₂ e₂.wb_right
    by_grind
    by_simp
  have ex : Exec P W ztqkb c c₃ (1 + ztocj) := .seq e₁ ztcr
  refine ⟨c₃, _, ex, by_omega, exec_frameB ex (wr_cvLoad dst), ?_, sp, ?_, ?_, ?_⟩
  · zugaq
    zujs
    zuenm

  · exact symPtIn_copy hin ztzvy ztzvw
      ztzvx
  · zueoz
  · rw [chain_vertex_host C hE.hP _ (sp := sp)]
    zudfz
open Chazelle.Chain (sidePt)
theorem pos_eq_sidePt (M : Model) (Q : Polygon) (x : WPos) :
    M.pos Q x = sidePt M.W x.edge ztbyt := rfl

/-- **When the parameter vanishes**: height code `0`, a horizontal edge, or the height of the start
vertex. -/
theorem param_eq_zero_iff (M : Model) (Q : Polygon) (x : WPos) :
    M.param Q x = 0 ↔ (x.hgt = 0 ∨ (M.wa x.edge).2 = (M.wb x.edge).2 ∨
      (Q.vtx ztzs).2 = (M.wa x.edge).2) := by
  zufde
  grind

/-- A positive parameter lies on a non-horizontal edge. -/
theorem ne_of_param_pos {M : Model} {Q : Polygon} {x : WPos} (h : 0 < M.param Q x) :
    (M.wa x.edge).2 ≠ (M.wb x.edge).2 := fun he =>
  ztvzp ((param_eq_zero_iff M Q x).2 by_simp_all)

/-- **The left sector inside an edge** for a horizontal direction. -/
theorem sideLeft_interior {W : Polygon} {p : ℕ} {t s : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hne : (W.vtx p).2 ≠ (W.vtx ztwjb).2) :
    sideLeft W p t (Visibility.rayPt ztia s 1) ↔
      s * ((W.vtx ztwjb).2 - (W.vtx p).2) < 0 := by
  have hne' : ztsdc := fun h => hne ztbzk
  rw [Chazelle.Chain.sideLeft_edge hne' by_simp_all]
  zucky
  simp only [det, Visibility.rayPt, Geometry.lerp_fst, Geometry.lerp_snd]
  grind

/-- The interior sign test is the turning code `1`. -/
theorem interior_bit (M : Model) (e σ : ℕ) :
    dirOf σ * ((M.W.vtx ztzzc).2 - (M.W.vtx e).2) < 0 ↔
      turnCode (dirCode M e) σ = 1 := by
  unfold turnCode dirCode Model.wa Model.wb dirOf
  split_ifs <;> first
    | (constructor <;> intro h <;> first | rfl | omega | (exfalso; linarith) | linarith)
    | (constructor <;> intro h <;> (exfalso; first | omega | linarith))

/-- **Positions on the box block are inside their edge** when the point is strictly inside the
height range of the box. -/
theorem box_param_pos (C : Chain) {Q : Polygon} {x : WPos} (he : x.edge < 6)
    (hp : 0 ≤ (chainModel C).param Q x)
    (hy : |((chainModel C).pos Q x).2| < C.radius) : 0 < (chainModel C).param Q x := by
  zuklw
  · zubh
  exfalso
  rw [pos_eq_sidePt, ← h] at hy
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := C.sidePt_box C.sideBeta 0
  zubo
  have hw : ztkf := rfl
  grind

/-! ## The machine -/

/-- The interior bit: `50210 := [turnCode (10502) (50203) = 1]`. -/
def intOut : Stmt :=
  .seq turnOut (.ifLtN 50210 50032 ztbki
    (.ifLtN 50032 50210 ztbki ztbwr))
variable {P : Polygon} {W : ℕ}
theorem intOut_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W)
    (h32 : c.nreg 50032 = 1) (hd : c.nreg 10502 ≤ 2) :
    ∃ c' k, Exec P W intOut c c' k ∧ k ≤ 14 ∧
      BitIs c' 50210 (turnCode ztggz ztdzm = 1) ∧
      ∀ r, r ≠ 50210 → c'.nreg r = c.nreg r := by
  obtain ⟨c₁, k₁, e₁, hk₁, o₁, r₁⟩ := turnOut_exec (P := P) c hw hW h32 hd
  zud
  have p₁ : ztizk := by_simp_all
  set t := turnCode ztggz ztdzm
  have fin : ∀ v, v ≤ 1 → (v = 1 ↔ t = 1) → ∃ c' k, Exec P W ztoud c₁ c' k ∧
      k = 1 ∧ BitIs c' 50210 (t = 1) ∧ ∀ r, r ≠ 50210 → c'.nreg r = c.nreg r := fun v hv hvt =>
    ⟨_, 1, Exec.constN w₁ _ _ by_omega, rfl, ⟨by_simp_all, by_simp_all⟩,
      by simp_all⟩
  by_cases h0 : t < 1
  · obtain ⟨c', k, e, hk, h1, h2⟩ := fin 0 by_omega by_omega
    exact ⟨c', _, .seq e₁ ztdrx, by_omega, h1, h2⟩
  by_cases h2 : 1 < t
  · obtain ⟨c', k, e, hk, h1, h3⟩ := fin 0 by_omega by_omega
    exact ⟨c', _, .seq e₁ (.ifLtN_false by_omega
      ztdrx), by_omega, h1, h3⟩
  · obtain ⟨c', k, e, hk, h1, h3⟩ := fin 1 le_rfl by_omega
    exact ⟨c', _, .seq e₁ (.ifLtN_false by_omega
      ztejp), by_omega, h1, h3⟩

/-- The vertex case: the sector procedure at the tour vertex `e - 6`, answer copied. -/
def vtxOut : Stmt :=
  .seq (.instr (.subN 50121 50201 50081)) (.seq secAt (.instr (.copyN 50210 50110)))

/-- **`leftSec`**: edge in `50201`, height code in `50202`, direction code in `50203`; answer bit
in `50210`. -/
def leftSecCore : Stmt :=
  .seq ztfex (.seq dirAt
    (.ifLtN 50201 50081 intOut
      (.ifLtN 50202 50032 vtxOut
        (.ifLtN 10502 50032 vtxOut
          (.seq ztbdp (.seq ztibk
            (.seq ztepm
              (.seq ztilk (.seq ztill
                (.ifLtN 50170 50032 (.ifLtN 50171 50032 vtxOut intOut) intOut))))))))))

/-- **The primitive `leftSec`.** -/
def leftSec : Stmt := .seq pHead leftSecCore
theorem wr_leftSec : wr Bprim leftSec = true := by_decide

/-- The vertex case of `leftSec`. -/
theorem vtxOut_exec {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {e : ℕ} (h01 : c.nreg 50201 = e) (he6 : 6 ≤ e)
    (he : e < 2 * C.m + 7) :
    ∃ c' k, Exec P W vtxOut c c' k ∧ k ≤ 81 * H.length + 3202 ∧
      BitIs c' 50210 (sideLeft (chainModel C).W e 0
        (Visibility.rayPt ztiey ztzek 1)) := by
  have e₁ := Exec.subN (P := P) hE.wb 50121 50201 50081
  set c₁ : Config := { c with nreg := upd c.nreg 50121 _ } with hc₁
  have hE₁ := hE.frame (exec_frameB e₁ (B := fun r => r == 50121)
    by_decide) e₁.wb_right by_decide
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, -, b₂⟩ := secAt_exec c₁ hE₁ (i := e - 6)
    ztirs by_omega
  have e₃ := Exec.copyN (P := P) e₂.wb_right 50210 50110
  refine ⟨_, _, .seq e₁ ztcr, by_omega, ?_⟩
  have s₁ : ztsgh := by_rfl
  rw [s₁, show e - 6 + 6 = e by omega] at b₂
  tauto

/-- The input condition of `leftSec`: a proper position of the walk whose point is strictly
inside the height range of the box. -/
def LeftIn (P : Polygon) (_ : ℕ) (C : Chain) (c : Config) : Prop :=
  c.nreg 50201 < (chainModel C).W.n ∧
    ProperPos ztc zta P.n ztbce ∧
    |((chainModel C).pos (Qof P) ⟨c.nreg 50201, c.nreg 50202⟩).2| < C.radius

/-- The output condition of `leftSec`. -/
def LeftOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  BitIs c' 50210 (sideLeft (chainModel C).W ztcuv
    ((chainModel C).param zta ztbce)
    (Visibility.rayPt ztyms
      ztzek 1))

/-- **Contract of `leftSec`** (at most `17400` steps): the bit of "the direction `dirOf σ` points
into the open left sector of the walk at the position `(e, h)`". -/
theorem leftSec_meets : Meets leftSec primBands (PrimPre LeftIn) (PrimPost LeftOut)
    (fun _ _ => 17400) := by
  refine prim_meets by_simp_all wr_leftSec ?_
  intro P W H C c₀ c _hC hE ⟨hen, ⟨hp0, hp1, hhn⟩, hy⟩ hinp
  zuhq

  zucwu
  unfold LeftOut
  zufai
  zucp

  -- the edge direction

  zudkw
  have hE₁ := hE.frame (exec_frameB e₁ (B := fun r => r == 50002)
    by_decide) e₁.wb_right by_decide
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, d₂⟩ := dirAt_exec c₁ hE₁ (e := e)
    by_simp_all by_omega
  zue
  have g₂ : ztdjy := fun r h1 h2 => by
    rw [f₂.1 r ztcpm,
      hc₁]
    zubi
    zubzb
  zugd

  -- the interior case, shared
  have interior : ∀ c₃ : Config, CEnv P W H C c₃ → c₃.nreg 10502 = dirCode M e →
      c₃.nreg 50203 = σ → 0 < M.param zta x →
      ∃ c' k, Exec P W intOut c₃ c' k ∧ k ≤ 14 ∧
        BitIs c' 50210 (sideLeft M.W e ztxkg
          ztbapy) := by
    intro c₃ hE₃ d₃ s₃ hpos
    obtain ⟨c', k, ex, hk, b, -⟩ := intOut_exec (P := P) c₃ hE₃.wb by_omega hE₃.r32
      by_simp_all
    refine ⟨c', k, ex, hk, b.congr ?_⟩
    rw [d₃, s₃, ← interior_bit, pos_eq_sidePt]
    exact (sideLeft_interior hpos hp1 (ne_of_param_pos hpos)).symm
  -- the vertex case, shared
  have vertex : ∀ c₃ : Config, CEnv P W H C c₃ → c₃.nreg 50201 = e → c₃.nreg 50203 = σ →
      6 ≤ e → M.param zta x = 0 →
      ∃ c' k, Exec P W vtxOut c₃ c' k ∧ k ≤ 81 * H.length + 3202 ∧
        BitIs c' 50210 (sideLeft M.W e ztxkg
          ztbapy) := by
    intro c₃ hE₃ e₃ s₃ h6 h0
    obtain ⟨c', k, ex, hk, b⟩ := vtxOut_exec c₃ hE₃ e₃ h6 by_omega
    refine ⟨c', k, ex, hk, ?_⟩
    rw [h0, pos_eq_sidePt, h0, Chazelle.Chain.sidePt_zero, ← s₃]
    exact b
  zubta
  · -- the box block
    zugmz
    obtain ⟨c', k, ex, hk, b⟩ := interior c₂ hE₂ d₂ q03 hpos
    exact ⟨c', _, .seq e₁ ztcsb,
      by omega, b⟩
  zuxh

  · obtain ⟨c', k, ex, hk, b⟩ := vertex c₂ hE₂ q01 q03 by_omega
      ztgbl
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_true
      ztfpq ex))), by_omega, b⟩
  zuuz

  · zukbt
    have hhor : ztdjn := by
      zuhqs

    obtain ⟨c', k, ex, hk, b⟩ := vertex c₂ hE₂ q01 q03 by_omega
      ztgbl
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_true
      zthes ex)))), by_omega, b⟩
  zuoq
  -- the start vertex of the edge and the height vertex

  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50120 _ }
    with hc₃
  have hE₃ := hE₂.frame (exec_frameB e₃ (B := fun r => r == 50120)
    by_decide) e₃.wb_right by_decide
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sa, ia, la, va, -⟩ := tvLoad_exec c₃ hE₃ (i := e - 6)
    ztcqt by_omega
    (dst := 50133) by_norm_num
  zucc
  obtain ⟨c₅, k₅, e₅, hk₅, q⟩ : ∃ c₅ k₅, Exec P W (block [.constN 50160 0,
      .subN 50161 50202 50032]) c₄ c₅ k₅ ∧ k₅ = 2 ∧ (c₅.nreg 50160 = 0 ∧
        c₅.nreg 50161 = hc - 1 ∧ ∀ r, r ≠ 50160 → r ≠ 50161 → c₅.nreg r = c₄.nreg r) := by
    exec_block
    · omega
    · refine ⟨rfl, by config_simp, ?_, fun r h1 h2 => by simp [h1, h2]⟩
      config_simp
      rw [f₄.1 50202 by_decide, f₄.1 50032 by_decide, hc₃]
      zubi
      zubcd
  zucxy
  zuef
  zukhx
  zuxe

  have ia₅ := symPtIn_of_eq ia fun j h1 h2 => r₅ j by_omega by_omega
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, b₆, t₆⟩ := kbit_exec (op := 1) (dst := 50170) hE.hG hW c₅ w₅
    by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num la lh la ia₅ ih ia₅
  zubra

  obtain ⟨c₇, k₇, e₇, hk₇, f₇, b₇, t₇⟩ := kbit_exec (op := 1) (dst := 50171) hE.hG hW c₆
    e₆.wb_right by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num lh la lh
    ih₆ ia₆ ih₆
  zubgp
  have hE₅ := hE₄.keep w₅ (exec_frameB e₅ (B := fun r => r == 50160 ||
    r == 50161) by_decide).2.2.1 (fun r hr => r₅ r (by intro h; subst h; revert hr; decide)
      ztcua)
  zubqr

  -- registers kept since `c₂`
  have g₇ : ∀ r, r = 50201 ∨ r = 50203 ∨ r = 10502 → c₇.nreg r = c₂.nreg r := by
    zuz
    rw [f₇.1 r (by rcases hr with rfl | rfl | rfl <;> decide),
      f₆.1 r (by rcases hr with rfl | rfl | rfl <;> decide),
      r₅ r by_omega by_omega, f₄.1 r (by rcases hr with rfl | rfl | rfl <;> decide), hc₃]
    zubi
    zutv
  have b70 : ztfks :=
    BitIs.keep ztomz f₇ by_decide
  have b71 : ztfkt :=
    ⟨b₇, t₇⟩
  zupy

  zujzx
  zublv

  · zugdd
    have n70 : zthow := fun h => by
      have := b70.2.2 h; omega
    zudwy
    · zugde
      have n71 : zthov := fun h => by
        have := b71.2.2 h; omega
      have heq : ztwvl := by
        grind
      obtain ⟨c', k, ex, hk, b⟩ := vertex c₇ hE₇ (by rw [g₇ _ ztp, q01])
        ztbvq by_omega
        ztgbl
      exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
        (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_true ztcmd
          ztzry)))))))))), by_omega, b⟩
    · have p71 : zticu := b71.2.1 (by
        have := b71.1; rw [hE₇.r32] at hlt2; omega)
      have hpos : ztfko := lt_of_le_of_ne hp0 (fun h => by
        zugk
        · grind
        · zufsf
        grind)
      obtain ⟨c', k, ex, hk, b⟩ := interior c₇ hE₇ ztdlu
        ztbvq hpos
      exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
        (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_true ztcmd
          ztnae)))))))))), by_omega, b⟩
  · have p70 : ztidb := b70.2.1 (by
      have := b70.1; rw [hE₇.r32] at hlt; omega)
    have hpos : ztfko := lt_of_le_of_ne hp0 (fun h => by
      zugk
      · grind
      · zufsf
      grind)
    obtain ⟨c', k, ex, hk, b⟩ := interior c₇ hE₇ ztdlu
      ztbvq hpos
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
      ztbxp)))), by_omega, b⟩
open Chazelle.Chain (sideE)
def candIdx (m S j : ℕ) : ℕ := if j < S then j + ztbru else j - S
theorem candIdx_mod {m S j : ℕ} (hS : S ≤ 2 * m) (hj : j < 2 * m) :
    (S + candIdx m S j) % ztdk = j ∧ candIdx m S j < 2 * m := by
  zumsa
  zus
  · refine ztdiv
    rw [show S + (j + ztbru) = j + 2 * m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  · exact ⟨by rw [show S + (j - S) = j by omega, Nat.mod_eq_of_lt hj], by_omega⟩

/-- The tour index of a candidate is the chain vertex of the tour position. -/
theorem sideIdx_candIdx (C : Chain) (β : Bool) {j : ℕ} (hj : j ≤ 2 * C.m) :
    candIdx C.m ztdku j ≤ 2 * C.m ∧ C.sideIdx β (candIdx C.m ztdku j) = sideE C.m j := by
  zuljd
  zubt
  zufzy
  · obtain ⟨h1, h2⟩ := candIdx_mod (m := C.m) hS hj
    exact ⟨h2.le, by rw [C.sideIdx_eq, h1]⟩
  · zumsa
    zufa
    zubsc
    rw [C.sideIdx_eq, show C.sideS β + (2 * C.m - C.sideS β) = 2 * C.m by omega, Nat.mod_self]
    zumu
theorem sideE_rev {m j : ℕ} (hj : j ≤ m) : sideE m (2 * m - j) = j := by
  zumu

/-- **The candidate tour steps of a chain vertex.** -/
theorem cand_vertex (C : Chain) (β : Bool) {k : ℕ} (hk : k ≤ C.m) :
    (candIdx C.m ztdku k ≤ 2 * C.m ∧ C.sideIdx β (candIdx C.m ztdku k) = k) ∧
      (candIdx C.m ztdku ztbdr ≤ 2 * C.m ∧
        C.sideIdx β (candIdx C.m ztdku ztbdr) = k) := by
  obtain ⟨a1, a2⟩ := sideIdx_candIdx C β (j := k) by_omega
  obtain ⟨b1, b2⟩ := sideIdx_candIdx C β (j := 2 * C.m - k) by_omega
  refine ⟨⟨a1, ?_⟩, ztufx⟩
  · zungr; unfold sideE; simp_all
  · rw [b2, sideE_rev hk]

/-- **Every tour step of a chain vertex is a candidate.** -/
theorem cand_complete (C : Chain) (β : Bool) {i k : ℕ} (hi : i ≤ 2 * C.m)
    (hk : C.sideIdx β i = k) :
    i = candIdx C.m ztdku k ∨ i = candIdx C.m ztdku ztbdr ∨ i = 2 * C.m := by
  zuljd
  zubt
  rcases hi.lt_or_eq with hi | hi
  · rw [C.sideIdx_eq] at hk
    have hj := Nat.mod_lt ztty ztcdw
    set j := ztty % ztbb with hjdef
    have hji : i = candIdx C.m ztdku j := by
      zumsa
      by_cases h : C.sideS β + i < 2 * C.m
      · zvnnm at hjdef
        simp_all
      · zvnae at hjdef
        grind
    have hjk : j = k ∨ j = 2 * C.m - k := by
      zunki; unfold sideE; grind
    grind
  omega

/-! ## Twin edges -/

/-- **Twin edges**: an edge whose ends are those of `p` swapped carries the same points at the same
height codes, with the complementary parameter. -/
theorem twin_pos_param (M : Model) (Q : Polygon) {p p' h : ℕ} (hh : 1 ≤ h)
    (h1 : M.wa p' = M.wb p) (h2 : M.wb p' = M.wa p) (hne : (M.wa p).2 ≠ (M.wb p).2) :
    M.pos Q ztcfq = M.pos Q ztnk ∧ M.param Q ztcfq = 1 - M.param Q ztnk := by
  zulr
  have hne' : ztehi := sub_ne_zero.2 hne.symm
  have hne'' : (M.wa p).2 - (M.wb p).2 ≠ 0 := sub_ne_zero.2 hne
  have hpar : M.param Q ⟨p', h' + 1⟩ = 1 - M.param Q ⟨p, h' + 1⟩ := by
    zufde
    grind
  refine ⟨?_, hpar⟩
  zueew
  zubi
  rw [hpar, h1, h2]
  zubvj
variable (C : Chain)
/-- The two slit edges are twins. -/
theorem slit_twin :
    (chainModel C).wa 5 = (chainModel C).wb ztcc ∧
      (chainModel C).wb 5 = (chainModel C).wa ztcc := by
  zubt
  zulkp
  zubzo
  zujx
  · rw [C.sideWalk_next_last, C.sideWalk_vtx_five, C.sideWalk_vtx_zero]
  · rw [hn, Nat.mod_eq_of_lt by_omega, C.sideWalk_vtx_six, C.sideWalk_vtx_tour _ le_rfl,
      C.sideTour_two_m]
theorem slit_twin' :
    (chainModel C).wa ztcc = (chainModel C).wb 5 ∧
      (chainModel C).wb ztcc = (chainModel C).wa 5 :=
  ⟨(slit_twin C).2.symm, (slit_twin C).1.symm⟩

/-- The twin tour step of tour edge `i`: the reversed tour position `2m - 1 - j`. -/
noncomputable def tourTwin (C : Chain) (i : ℕ) : ℕ :=
  candIdx C.m ztboi (2 * C.m - 1 - ztwz % ztbb)

/-- **The twin of a tour edge.** -/
theorem tour_twin {i : ℕ} (hi : i < 2 * C.m) :
    tourTwin C i < 2 * C.m ∧
      (chainModel C).wa ztkfx = (chainModel C).wb ztcy ∧
      (chainModel C).wb ztkfx = (chainModel C).wa ztcy := by
  zubt
  zuec
  zukcs
  set j := ztwz % ztbb with hjdef
  obtain ⟨h1, h2⟩ := candIdx_mod (m := C.m) (j := 2 * C.m - 1 - j) hS by_omega
  have ht : tourTwin C i = candIdx C.m ztboi ztgyf := rfl
  rw [← ht] at h1 h2
  refine ⟨h2, ?_, ?_⟩
  · zujns
    rw [show (chainModel C).W = C.sideWalk C.sideBeta from rfl, C.sideWalk_next_tour _ hi,
      C.sideWalk_vtx_tour _ h2.le, C.sideWalk_vtx_tour _ by_omega]
    zueev
    zucr
    rw [C.sideIdx_eq, h1, C.sideIdx_succ, ← hjdef]
    zumu
  · zujns
    rw [show (chainModel C).W = C.sideWalk C.sideBeta from rfl, C.sideWalk_next_tour _ h2,
      C.sideWalk_vtx_tour _ by_omega, C.sideWalk_vtx_tour _ hi.le]
    zueev
    zucr
    rw [C.sideIdx_succ, h1, C.sideIdx_eq, ← hjdef]
    zumu

/-! ## The positions of a point of a vertical side of the box -/

/-- **A point inside an open vertical side of the box has one position.** -/
theorem wall_unique (hP : C.P.Simple) {e : ℕ} (he : e = 1 ∨ e = 3) {t₀ : ℝ}
    (ht₀ : 0 < t₀) (ht₀1 : t₀ < 1) {p : ℕ} {t : ℝ} (hp : p < (chainModel C).W.n) (ht : 0 ≤ t)
    (ht1 : t < 1) (heq : sidePt (chainModel C).W p t = sidePt (chainModel C).W e t₀) :
    p = e ∧ t = t₀ := by
  zucn
  zujil
  zubo
  zugma
  obtain ⟨-, e1, -, e3, -, -, -⟩ := C.sidePt_box C.sideBeta t₀
  have hw : |(sidePt ztcs e t₀).1| = C.radius ∧
      |(sidePt (C.sideWalk C.sideBeta) e t₀).2| < C.radius ∧
      ((e = 1 ∧ (sidePt ztcs e t₀).1 = -C.radius) ∨
        (e = 3 ∧ (sidePt ztcs e t₀).1 = C.radius)) := by
    zudsd
    · zvmxy; simp only [abs_neg, abs_of_pos hR, true_and]
      refine ztmqc
    · zvnak; simp only [abs_of_pos hR, true_and]
      refine ztmqc
  zvnbo at hw
  obtain ⟨hw1, hw2, hw3⟩ := hw
  zudjl
  · obtain ⟨-, hside⟩ := C.sideWalk_box_pt C.sideBeta hbox ht ht1
    obtain ⟨hpe, -⟩ := hside hw1 hw2
    have hpe' : p = e := by
      grind
    subst hpe'
    zubee
    have hnd := C.sideWalk_nd hP C.sideBeta p hp
    exact Geometry.lerp_injective hnd heq
  · exfalso
    have hmem := C.sideWalk_tour_pt_mem C.sideBeta hi hit ht ht1
    have := (C.abs_le_coordBound_of_mem_set hmem).1
    linarith

/-! ## The positions of a chain vertex -/

/-- **The positions of a vertex of the chain** are tour vertices of that vertex. -/
theorem vertex_positions (hP : C.P.Simple) {k : ℕ} (hk : k ≤ C.m) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel C).W.n) (ht : 0 ≤ t) (ht1 : t < 1)
    (heq : sidePt (chainModel C).W p t = C.vertex k) :
    t = 0 ∧ ∃ i, i ≤ 2 * C.m ∧ p = i + 6 ∧ C.sideIdx C.sideBeta i = k := by
  zucn
  zujil
  have hmem := C.vertex_mem_set hk
  zudjl
  · exact absurd (heq ▸ hmem) (C.sideWalk_box_pt C.sideBeta hbox ht ht1).1
  · have ht0 : ztbhh := by
      rcases hi.lt_or_eq with hi' | hi'
      · zuccr
        have htp : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht ztval, ht1⟩
        obtain ⟨k', -, s, hs, hpt, -⟩ := C.sideTour_open C.sideBeta hi' htp
        zvmxe at heq
        exact C.sideOpen_ne_vertex hP hs heq
      simp_all
    zudlw
    refine ztlwn
    rw [Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour _ hi] at heq
    exact C.sideVertex_inj hP ztbdw hk heq
def classify (boxK vtxK intK : Stmt) : Stmt :=
  .seq ztfex (.seq dirAt
    (.ifLtN 50201 50081 boxK
      (.ifLtN 50202 50032 vtxK
        (.ifLtN 10502 50032 vtxK
          (.seq ztbdp (.seq ztibk
            (.seq ztepm
              (.seq ztilk (.seq ztill
                (.ifLtN 50170 50032 (.ifLtN 50171 50032 vtxK intK) intK))))))))))

/-- **Execution of the classification**: the continuation of the case of `x` runs from a
configuration with the chain environment and the inputs `50200 … 50209`. -/
theorem classify_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {boxK vtxK intK : Stmt}
    {Kb Kv Ki : ℕ} {R : Config → Prop} (c₀ c : Config) (hE : CEnv P W H C c)
    (hinp : ∀ r, 50200 ≤ r → r < 50210 → c.nreg r = c₀.nreg r)
    (hen : c₀.nreg 50201 < (chainModel C).W.n)
    (hp0 : 0 ≤ (chainModel C).param zta ztdqp)
    (_hp1 : (chainModel C).param zta ztdqp < 1)
    (hhn : c₀.nreg 50202 ≤ P.n)
    (hy : |((chainModel C).pos zta ⟨c₀.nreg 50201, c₀.nreg 50202⟩).2| < C.radius)
    (hbox : ∀ c₂ : Config, CEnv P W H C c₂ →
      ztdbc →
      c₂.nreg 10502 = dirCode ztc ztvmd → c₀.nreg 50201 < 6 →
      0 < (chainModel C).param zta ztdqp →
      ∃ c' k, Exec P W boxK c₂ c' k ∧ k ≤ Kb ∧ R c')
    (hvtx : ∀ c₂ : Config, CEnv P W H C c₂ →
      ztdbc → 6 ≤ c₀.nreg 50201 →
      (chainModel C).param zta ztdqp = 0 →
      ∃ c' k, Exec P W vtxK c₂ c' k ∧ k ≤ Kv ∧ R c')
    (hint : ∀ c₂ : Config, CEnv P W H C c₂ →
      ztdbc →
      c₂.nreg 10502 = dirCode ztc ztvmd → 6 ≤ c₀.nreg 50201 →
      0 < (chainModel C).param zta ztdqp →
      ∃ c' k, Exec P W intK c₂ c' k ∧ k ≤ Ki ∧ R c') :
    ∃ c' k, Exec P W (classify boxK vtxK intK) c c' k ∧
      k ≤ 110 * H.length + 1200 + Kb + Kv + Ki ∧ R c' := by
  zuhq

  zucwu
  zufai
  zucp

  -- the edge direction

  set c₁ : Config := { c with nreg := upd c.nreg 50002 (c.nreg 50201) } with hc₁
  have hE₁ : ztrfi := hE.frame (exec_frameB e₁ (B := fun r => r == 50002)
    by_decide) e₁.wb_right by_decide
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, d₂⟩ := dirAt_exec c₁ hE₁ (e := e)
    by_tauto by_omega
  zue
  have g₂ : ztdjy := fun r h1 h2 => by
    rw [f₂.1 r ztcpm,
      hc₁]
    zubi
    zubzb
  zugd

  zubta
  · -- the box block
    have hpos : ztxsz := box_param_pos C hsm hp0 hy
    obtain ⟨c', k, ex, hk, b⟩ := hbox c₂ hE₂ g₂ d₂ hsm hpos
    exact ⟨c', _, .seq e₁ ztcsb,
      by omega, b⟩
  zuxh

  · obtain ⟨c', k, ex, hk, b⟩ := hvtx c₂ hE₂ g₂ by_omega
      ((param_eq_zero_iff _ _ _).2 ztzz)
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_true
      ztfpq ex))), by_omega, b⟩
  zuuz

  · zukbt
    have hhor : ztdjn := by
      zuhqs

    obtain ⟨c', k, ex, hk, b⟩ := hvtx c₂ hE₂ g₂ by_omega
      ((param_eq_zero_iff _ _ _).2 (Or.inr (Or.inl hhor)))
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_true
      zthes ex)))), by_omega, b⟩
  zuoq
  -- the start vertex of the edge and the height vertex

  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50120 (c₂.nreg 50201 - c₂.nreg 50081) }
    with hc₃
  have hE₃ : ztrfj := hE₂.frame (exec_frameB e₃ (B := fun r => r == 50120)
    by_decide) e₃.wb_right by_decide
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sa, ia, la, va, -⟩ := tvLoad_exec c₃ hE₃ (i := e - 6)
    ztcqt by_omega
    (dst := 50133) by_norm_num
  zucc
  obtain ⟨c₅, k₅, e₅, hk₅, q⟩ : ∃ c₅ k₅, Exec P W (block [.constN 50160 0,
      .subN 50161 50202 50032]) c₄ c₅ k₅ ∧ k₅ = 2 ∧ (c₅.nreg 50160 = 0 ∧
        c₅.nreg 50161 = hc - 1 ∧ ∀ r, r ≠ 50160 → r ≠ 50161 → c₅.nreg r = c₄.nreg r) := by
    exec_block
    · omega
    · refine ⟨rfl, by config_simp, ?_, fun r h1 h2 => by simp [h1, h2]⟩
      config_simp
      rw [f₄.1 50202 by_decide, f₄.1 50032 by_decide, hc₃]
      zubi
      zubcd
  zucxy
  zuef
  have ih : SymPtIn c₅ 50160 (.vtx ztzk) := ztopg
  zuxe

  have ia₅ : ztumi := symPtIn_of_eq ia fun j h1 h2 => r₅ j by_omega by_omega
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, b₆, t₆⟩ := kbit_exec (op := 1) (dst := 50170) hE.hG hW c₅ w₅
    by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num la lh la ia₅ ih ia₅
  zubra

  obtain ⟨c₇, k₇, e₇, hk₇, f₇, b₇, t₇⟩ := kbit_exec (op := 1) (dst := 50171) hE.hG hW c₆
    e₆.wb_right by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num lh la lh
    ih₆ ia₆ ih₆
  zubgp
  have hE₅ : CEnv P W H C c₅ := hE₄.keep w₅ (exec_frameB e₅ (B := fun r => r == 50160 ||
    r == 50161) by_decide).2.2.1 (fun r hr => r₅ r (by intro h; subst h; revert hr; decide)
      ztcua)
  zubqr

  -- registers kept since `c₂`
  have g₇ : ∀ r, ztqt ∨ r = 10502 → c₇.nreg r = c₂.nreg r := by
    zuz
    have hB : ∀ B : ℕ → Bool, (∀ j, 50200 ≤ j → j < 50210 → B j = false) → B 10502 = false →
        B r = false := fun B h1 h2 => by rcases hr with ⟨h3, h4⟩ | rfl; exacts [h1 r h3 h4, h2]
    rw [f₇.1 r (hB _ (fun j h1 h2 => by interval_cases j <;> decide) by_decide),
      f₆.1 r (hB _ (fun j h1 h2 => by interval_cases j <;> decide) by_decide),
      r₅ r by_omega by_omega, f₄.1 r (hB _ (fun j h1 h2 => by interval_cases j <;> decide)
        by_decide), hc₃]
    zubi
    zutv
  have g₇' : ∀ r, 50200 ≤ r → r < 50210 → c₇.nreg r = c₀.nreg r := fun r h1 h2 => by
    rw [g₇ r (Or.inl ztwo), g₂ r h1 h2]
  have b70 : BitIs c₇ 50170 ((SymPt.eval zta sa).2 < ((SymPt.vtx ztzk).eval zta).2) :=
    BitIs.keep ztomz f₇ by_decide
  have b71 : BitIs c₇ 50171 (((SymPt.vtx ztzk).eval zta).2 < (SymPt.eval zta sa).2) :=
    ⟨b₇, t₇⟩
  zupy

  have hQ : ((SymPt.vtx ztzk).eval zta) = (Qof P).vtx ztzs := rfl
  zublv

  · zugdd
    have n70 : ¬ (M.W.vtx e).2 < ((Qof P).vtx ztzs).2 := fun h => by
      have := b70.2.2 h; omega
    zudwy
    · zugde
      have n71 : ¬ ((Qof P).vtx ztzs).2 < (M.W.vtx e).2 := fun h => by
        have := b71.2.2 h; omega
      have heq : ztwvl := by
        grind
      obtain ⟨c', k, ex, hk, b⟩ := hvtx c₇ hE₇ g₇' by_omega
        zthpz
      exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
        (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_true ztcmd
          ztzry)))))))))), by_omega, b⟩
    · have p71 : ((Qof P).vtx ztzs).2 < (M.W.vtx e).2 := b71.2.1 (by
        have := b71.1; rw [hE₇.r32] at hlt2; omega)
      have hpos : ztxsz := lt_of_le_of_ne hp0 (fun h => by
        zugk
        · grind
        · zufsf
        grind)
      obtain ⟨c', k, ex, hk, b⟩ := hint c₇ hE₇ g₇' ztyed by_omega
        hpos
      exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
        (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.ifLtN_true ztcmd
          ztnae)))))))))), by_omega, b⟩
  · have p70 : (M.W.vtx e).2 < ((Qof P).vtx ztzs).2 := b70.2.1 (by
      have := b70.1; rw [hE₇.r32] at hlt; omega)
    have hpos : ztxsz := lt_of_le_of_ne hp0 (fun h => by
      zugk
      · grind
      · zufsf
      grind)
    obtain ⟨c', k, ex, hk, b⟩ := hint c₇ hE₇ g₇' ztyed by_omega hpos
    exact ⟨c', _, .seq e₁ (.seq e₂ (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3
      ztbxp)))), by_omega, b⟩
end
end SweepPrim
end Chazelle.Core
section
set_option hygiene false
local macro "zqbgm" : tactic => `(tactic| simp only [HostEdgeOK, hostEdgeIdx, SymPt.Lt, SymPt.eval] at hok hl₁ hl₂ ⊢)
local macro "zqbgn" : tactic => `(tactic| (rcases h₁.2 with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> [skip; omega; omega]))
local macro "zqbgo" : tactic => `(tactic| (rcases h₂.2 with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> [skip; omega; omega]))
local macro "zqbgp" : tactic => `(tactic| (have e₃ := Exec.constN (P := P) e₂.wb_right 50210 1 (by have := hE.hW; omega)))
local macro "zqbgq" : tactic => `(tactic| obtain ⟨c₄, e₄, v₄, r₄⟩ := fin 50137 ztp)
set_option hygiene true

/-!
# Sweep RAM primitives (WP-D2), part 10: abscissae of walk positions (`absKey`, `absCmp`)

`absLt` of design-merge-v2 §9.6 item 4 (the `a ∈ e` test, the before-the-endpoint test, ordering
hits along a ray) compares the abscissae of two walk positions, possibly of different chain
models of one host.  It is split in two primitives:

* `absKey`: for a walk position `x` of `chainModel C`, an **abscissa record** (`AbsRec`): kind
  `0` (the abscissa is `-radius`: the left side of the box), `2` (`+radius`: the right side), or
  `1` and a symbolic point of `Qof P` with the same abscissa (a vertex of the chain, the top of the
  chain for a point of the slit, or the point `onEdge E h` of the edge `E` of `Q` carrying the
  host edge, for a point inside a tour edge at the height of vertex `h`).
* `absCmp`: the bit `x₁ < x₂` of two abscissa records (one sign-kernel test at most).

The edge `E` (`hostEdgeIdx`) is read off the two host points of the tour edge (regular hosts,
`HostRegular`: consecutive host points are both on the line of one edge of `Q`,
`hostEdge_onLine`).
-/
namespace Chazelle.Core
namespace SweepPrim
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
open Chazelle.Chain (sideE sideLeft sidePt)
@[expose] public section
def OnLine (Q : Polygon) (E : ℕ) (p : Point) : Prop := p.1 = Visibility.edgeX Q E p.2
variable {Q : Polygon} {E : ℕ} {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {c : Config} {r : ℕ} {x R : ℝ}
theorem onLine_lerp {a b : Point} (ha : OnLine Q E a) (hb : OnLine Q E b)
    (t : ℝ) : OnLine Q E (Geometry.lerp a b t) := by
  unfold OnLine Visibility.edgeX Visibility.xAt at *
  zubzm
  grind
theorem onLine_left (Q : Polygon) (E : ℕ) : OnLine Q E (Q.vtx E) := by
  unfold OnLine Visibility.edgeX; rw [Visibility.xAt_left]
theorem onLine_right (h : (Q.vtx E).2 ≠ (Q.vtx ztysw).2) :
    OnLine Q E (Q.vtx ztysw) := by
  unfold OnLine Visibility.edgeX; rw [Visibility.xAt_right h]
theorem onLine_onEdge (Q : Polygon) (E h : ℕ) : OnLine Q E ((SymPt.onEdge E h).eval Q) := rfl

/-- **The edge of `Q` of a host edge**, as the machine reads it off the two host points. -/
def hostEdgeIdx (n : ℕ) : SymPt → SymPt → ℕ
  | .onEdge e _, _ => e
  | .vtx _, .onEdge e _ => e
  | .vtx i, .vtx j => if j = ztg % n then i else j
theorem hostEdgeOK_symm {n : ℕ} {s₁ s₂ : SymPt} (h : HostEdgeOK n s₁ s₂) : HostEdgeOK n s₂ s₁ := by
  cases s₁ <;> cases s₂ <;> simp only [HostEdgeOK] at h ⊢ <;> omega
theorem edge_heights_ne (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {E : ℕ}
    (hE : E < Q.n) : (Q.vtx E).2 ≠ (Q.vtx ztysw).2 := by
  refine hD _ _ hE ztcv ?_
  zuq
  rcases Nat.lt_or_ge ztemk Q.n with h' | h'
  · zupe
  · rw [show E + 1 = Q.n by omega, Nat.mod_self] at h; omega

/-- **Both ends of a non-horizontal host edge lie on the line of the edge `hostEdgeIdx`.** -/
theorem hostEdge_onLine (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {s₁ s₂ : SymPt}
    (hl₁ : s₁.Lt Q.n) (hl₂ : s₂.Lt Q.n) (hok : HostEdgeOK Q.n s₁ s₂)
    (hnh : (s₁.eval Q).2 ≠ (s₂.eval Q).2) :
    hostEdgeIdx Q.n s₁ s₂ < Q.n ∧ OnLine Q ztrrz (s₁.eval Q) ∧
      OnLine Q ztrrz (s₂.eval Q) := by
  cases s₁ with
  | onEdge e h =>
    cases s₂ with
    | vtx j =>
      zqbgm
      refine ⟨hl₁.1, onLine_onEdge Q e h, ?_⟩
      zubuh
      · exact onLine_left Q j
      · exact onLine_right (edge_heights_ne hD hn hl₁.1)
    | onEdge e' h' =>
      simp only [HostEdgeOK, hostEdgeIdx, SymPt.Lt, SymPt.eval] at hok hl₁ hl₂ hnh ⊢
      zubuh
      · simp_all
      · tauto
  | vtx i =>
    cases s₂ with
    | onEdge e h =>
      zqbgm
      refine ⟨hl₂.1, ?_, onLine_onEdge Q e h⟩
      zubuh
      · exact onLine_left Q i
      · exact onLine_right (edge_heights_ne hD hn hl₂.1)
    | vtx j =>
      zqbgm
      zuhtb
      · zuhmf
        refine ⟨hl₁, onLine_left Q i, ?_⟩
        rw [hj]; exact onLine_right (edge_heights_ne hD hn hl₁)
      · zulqh
        have hi : ztzqg := by_omega
        refine ⟨hl₂, ?_, onLine_left Q j⟩
        rw [hi]; exact onLine_right (edge_heights_ne hD hn hl₂)

/-- The heights of `Qof P` are distinct in a good environment. -/
theorem distinct_Qof (hG : GoodEnv P) : DistinctHeights zta :=
  (goodShear_epsOf hG.2).2.1

/-! ## Abscissa records -/

/-- **An abscissa record** at `r`: kind `0` (`x = -R`), `2` (`x = R`), or `1` and a symbolic
point of `Qof P` in range at `r + 1` with abscissa `x`, `|x| < R`. -/
def AbsRec (P : Polygon) (c : Config) (r : ℕ) (x R : ℝ) : Prop :=
  0 < R ∧ (ztllt ∨ ztmha ∨
    (c.nreg r = 1 ∧ |x| < R ∧ ∃ s : SymPt, SymPtIn c ztgu s ∧ s.Lt P.n ∧ (s.eval zta).1 = x))

/-! ## The point inside a tour edge -/
theorem getD_of_getElem? {α : Type} {l : List α} {q : ℕ} {a d : α} (h : l[q]? = some a) :
    l.getD q d = a := by
  simp_all

/-- **The abscissa of a point inside a tour edge** is that of the point `onEdge E (h - 1)` of the
edge `E = hostEdgeIdx` of `Q` carrying the host edge. -/
theorem tour_abs (hG : GoodEnv P) {H : Host} {C : Chain} (_hCP : C.P = H.poly zta)
    (hreg : HostRegular P.n H) (hNn : C.P.n = (H.pts P.n).length) {i : ℕ} (hi : i < 2 * C.m)
    {s₁ s₂ : SymPt}
    (h1 : ztbkj[ztema % (H.pts P.n).length]? = some s₁)
    (h2 : ztbkj[ztxfx % (H.pts P.n).length]? = some s₂)
    (hl₁ : s₁.Lt P.n) (hl₂ : s₂.Lt P.n)
    (hv₁ : s₁.eval zta = (chainModel C).W.vtx ztcy)
    (hv₂ : s₂.eval zta = (chainModel C).W.vtx ztxyx) {hc : ℕ}
    (ht : 0 < (chainModel C).param zta ztcbx) :
    hostEdgeIdx P.n s₁ s₂ < P.n ∧
      ((chainModel C).pos zta ztcbx).1 =
        ((SymPt.onEdge ztfsk ztzk).eval zta).1 := by
  zuc
  zucgu
  zugyg
  have hN0 : ztgab := by_grind
  set L := H.pts P.n
  -- the host edge
  have hok : HostEdgeOK P.n s₁ s₂ := by
    have hstep := C.sideTour_step C.sideBeta i
    have hmod : ∀ a, ((a % N) + 1) % N = ztdf % N := by_simp_all
    rcases hstep with h | h
    · have := hreg (ztema % N) zthbs
      rw [getD_of_getElem? h1, hmod, show C.s + C.sideIdx C.sideBeta i + 1 =
        C.s + C.sideIdx C.sideBeta ztg by omega, getD_of_getElem? h2] at this
      omega
    · have := hreg (ztxfx % N) zthbs
      rw [getD_of_getElem? h2, hmod, show C.s + C.sideIdx C.sideBeta _ + 1 =
        C.s + C.sideIdx C.sideBeta i by omega, getD_of_getElem? h1] at this
      exact hostEdgeOK_symm this
  -- the walk edge
  have hwa : (chainModel C).wa _ = s₁.eval _ := hv₁.symm
  have hwb : (chainModel C).wb ztcy = s₂.eval zta := by
    rw [hv₂]; show (C.sideWalk C.sideBeta).vtx ztysl = _
    rw [C.sideWalk_next_tour _ hi]; rfl
  zubkn
  rw [hwa, hwb] at hne
  zulhu
  zvnof at hok hl₁ hl₂ ⊢
  obtain ⟨hE, hon₁, hon₂⟩ := hostEdge_onLine hD by_omega hl₁ hl₂ hok hne
  refine ⟨hE, ?_⟩
  have hpos : OnLine zta (hostEdgeIdx (Qof P).n s₁ s₂) ((chainModel C).pos zta ztcbx) := by
    show OnLine _ _ (Geometry.lerp ((chainModel C).wa ztcy) ((chainModel C).wb ztcy) _)
    rw [hwa, hwb]; exact onLine_lerp hon₁ hon₂ _
  zudul
  have hne' : ((chainModel C).wa ztcy).2 ≠ ((chainModel C).wb ztcy).2 := by
    simp_all
  rw [Model.pos_snd hne']
  have hc1 : ztixw := by
    zuzn
    · zulxw
    omega
  zucnu

/-! ## The machine: the edge of a host edge -/

/-- The edge `hostEdgeIdx n s₁ s₂` of the host points in the slots `50130` and `50136` into
`50142` (scratch `50140`, `50141`). -/
def edgeIdxS : Stmt :=
  .ifLtN 50130 50032
    (.ifLtN 50136 50032
      (.seq (block [.addN 50140 50131 50032, .inputSize 50141])
        (.seq (.ifLtN 50140 50141 .skip ztify)
          (.ifLtN 50140 50137 ztigk
            (.ifLtN 50137 50140 ztigk ztovp))))
      ztigk)
    ztovp
theorem edgeIdxS_exec (c : Config) (hw : WordsBounded W c)
    (hW : P.n + 1 ≤ W) (h32 : c.nreg 50032 = 1) {s₁ s₂ : SymPt} (h1 : SymPtIn c 50130 s₁)
    (h2 : SymPtIn c 50136 s₂) (hl₁ : s₁.Lt P.n) (hl₂ : s₂.Lt P.n) :
    ∃ c' k, Exec P W edgeIdxS c c' k ∧ k ≤ 12 ∧ c'.nreg 50142 = hostEdgeIdx P.n s₁ s₂ ∧
      ∀ r, r ≠ 50140 → r ≠ 50141 → r ≠ 50142 → c'.nreg r = c.nreg r := by
  unfold edgeIdxS
  cases s₁ with
  | onEdge e h =>
    obtain ⟨k1, k2, -⟩ := h1
    refine spec_ifLtN_false by_omega (spec_instr ztbim
      fun _ => ztraq)
  | vtx i =>
    obtain ⟨k1, k2⟩ := h1
    zudd
    cases s₂ with
    | onEdge e h =>
      obtain ⟨j1, j2, -⟩ := h2
      refine spec_ifLtN_false by_omega (spec_instr ztbim
        fun _ => ztraq)
    | vtx j =>
      obtain ⟨j1, j2⟩ := h2
      have k2' : c.nreg 50131 = i := k2
      have j2' : c.nreg 50137 = j := j2
      zueeq
      have e₁ := Exec.addN (P := P) hw 50140 50131 50032 by_omega
      set c₁ : Config := { c with nreg := upd c.nreg 50140 _ }
        with hc₁
      zud
      have e₂ := Exec.inputSize (P := P) w₁ 50141 by_omega
      set c₂ : Config := { c₁ with nreg := upd c₁.nreg 50141 P.n } with hc₂
      zue
      have q40 : c₂.nreg 50140 = i + 1 := by_simp_all
      have q41 : c₂.nreg 50141 = P.n := by_rfl
      have r₂ : ∀ r, r ≠ 50140 → r ≠ 50141 → c₂.nreg r = c.nreg r := by_simp_all
      obtain ⟨c₃, k₃, e₃, hk₃, q40', r₃⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 50140 50141 .skip
          ztify) c₂ c₃ k₃ ∧ k₃ ≤ 3 ∧ c₃.nreg 50140 = (i + 1) % P.n ∧
          ∀ r, r ≠ 50140 → c₃.nreg r = c₂.nreg r := by
        by_cases hl : i + 1 < P.n
        · exact spec_ifLtN_true by_omega (spec_skip w₂
            ⟨by_omega, by rw [q40, Nat.mod_eq_of_lt hl], by_omega⟩)
        · refine spec_ifLtN_false by_omega (spec_instr (Exec.constN w₂ _ _
            by_omega) fun _ => ⟨by_omega, ?_, by_simp_all⟩)
          zufb
          rw [show i + 1 = P.n by omega, Nat.mod_self]
      zubj
      have j3 : c₃.nreg 50137 = j := by_simp_all
      have i3 : c₃.nreg 50131 = i := by_simp_all
      have eb : Exec P W _ c c₂ 2 :=
        Exec.block_cons e₁ ztoww
      have t0 : c.nreg 50130 < c.nreg 50032 := by_omega
      have t1 : c.nreg 50136 < c.nreg 50032 := by_omega
      have fin : ∀ a, a = 50137 ∨ a = 50131 → ∃ c₄, Exec P W (.instr (.copyN 50142 a)) c₃ c₄ 1 ∧
          c₄.nreg 50142 = c₃.nreg a ∧ ∀ r, r ≠ 50140 → r ≠ 50141 → r ≠ 50142 →
            c₄.nreg r = c.nreg r := fun a ha =>
        ⟨_, Exec.copyN w₃ _ _, by_simp, by_simp_all⟩
      by_cases ha : ztg % P.n < j
      · have t2 : c₃.nreg 50140 < c₃.nreg 50137 := by_omega
        zqbgq
        refine ⟨c₄, _, .ifLtN_true t1 (.seq eb (.seq e₃ (.ifLtN_true t2 e₄))), by_omega, ?_, r₄⟩
        zuemt
      have t2 : ¬ c₃.nreg 50140 < c₃.nreg 50137 := by_omega
      by_cases hb : j < ztg % P.n
      · have t3 : c₃.nreg 50137 < c₃.nreg 50140 := by_omega
        zqbgq
        refine ⟨c₄, _, .ifLtN_true t1 (.seq eb (.seq e₃ (.ifLtN_false t2 (.ifLtN_true t3 e₄)))),
          by omega, ?_, r₄⟩
        zuemt
      · have t3 : ¬ c₃.nreg 50137 < c₃.nreg 50140 := by_omega
        obtain ⟨c₄, e₄, v₄, r₄⟩ := fin 50131 ztbt
        refine ⟨c₄, _, .ifLtN_true t1 (.seq eb (.seq e₃ (.ifLtN_false t2 (.ifLtN_false t3 e₄)))),
          by omega, ?_, r₄⟩
        rw [v₄, i3]; simp only [hostEdgeIdx]; grind

/-! ## The machine: `absKey` -/

/-- Output the point `onEdge (50142) (h - 1)`. -/
def outE : Stmt :=
  block [.constN 50210 1, .constN 50211 1, .copyN 50212 50142, .subN 50213 50202 50032]
/-- The abscissa of the top of the chain (a point of the slit). -/
def absTop : Stmt :=
  .seq (.instr (.constN 50120 0)) ztzsj
/-- The box block: the left side, the right side, or the slit. -/
def absBox : Stmt :=
  .ifLtN 50201 50082 ztbki
    ztzae
/-- A tour vertex. -/
def absVtx : Stmt :=
  .seq ztbdp ztzsj
/-- Inside a tour edge. -/
def absTour : Stmt :=
  .seq ztkgf (.seq ztnat (.seq ztkgg
    (.seq edgeIdxS outE)))
/-- Inside a tour edge or the up-slit edge. -/
def absInt : Stmt :=
  .seq ztiri
    (.ifLtN 50120 50143 absTour absTop)

/-- **The primitive `absKey`.** -/
def absKey : Stmt := .seq pHead (classify absBox absVtx absInt)
theorem wr_absKey : wr Bprim absKey = true := by_decide
theorem absTop_exec (c : Config)
    (hE : CEnv P W H C c) :
    ∃ c' k, Exec P W absTop c c' k ∧ k ≤ 27 * H.length + 45 ∧
      AbsRec P c' 50210 C.top.1 C.radius := by
  have e₁ := Exec.constN (P := P) hE.wb 50120 0 by_omega
  zumz
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := 0)
    by_simp by_omega (dst := 50211) by_norm_num
  zqbgp
  refine ⟨_, _, .seq e₁ ztcr, by_omega, C.radius_pos, Or.inr (Or.inr ⟨by_simp,
    C.abs_top_fst_lt_radius, sp, symPtIn_of_eq isp fun j h1 h2 => by simp [show j ≠ 50210 by
      omega], lsp, ?_⟩)⟩
  rw [vsp, zero_add, walk_vtx_six]
theorem absBox_exec (c : Config)
    (hE : CEnv P W H C c) {e hc : ℕ} (h01 : c.nreg 50201 = e)
    (hd : c.nreg 10502 = dirCode ztc e) (he : e < 6)
    (ht : 0 < (chainModel C).param zta ztev) :
    ∃ c' k, Exec P W absBox c c' k ∧ k ≤ 27 * H.length + 50 ∧
      AbsRec P c' 50210 ((chainModel C).pos zta ztev).1 C.radius := by
  zubkn
  have hdir : ztzqd := by
    zuhal
  zuihc
  zubo
  zuol
  obtain ⟨-, e1, -, e3, -, e5, -⟩ := C.sidePt_box C.sideBeta ztwtf
  have hpos : (chainModel C).pos _ ztev =
      sidePt ztcs e ztwtf := rfl
  by_cases h1 : e < 2
  · have he1 : ztsie := by_grind
    subst he1
    refine ⟨_, _, .ifLtN_true ztdlv ztpxs,
      by omega, hR, Or.inl zthml⟩
    simp_all
  by_cases h3 : e < 4
  · have he3 : ztsif := by_grind
    subst he3
    refine ⟨_, _, .ifLtN_false ztdlv (.ifLtN_true
      ztfpk ztpxs), by_omega, hR,
      Or.inr (Or.inl zthml)⟩
    simp_all
  · have he5 : ztpol := by_grind
    subst he5
    obtain ⟨c', k', ex, hk, hrec⟩ := absTop_exec c hE
    refine ⟨c', _, .ifLtN_false ztdlv (.ifLtN_false
      ztfpk ex), by_omega, ?_⟩
    simp_all
theorem absVtx_exec (c : Config)
    (hE : CEnv P W H C c) {e hc : ℕ} (h01 : c.nreg 50201 = e) (he6 : 6 ≤ e)
    (hen : e < 2 * C.m + 7) (hpar : (chainModel C).param zta ztev = 0) :
    ∃ c' k, Exec P W absVtx c c' k ∧ k ≤ 27 * H.length + 45 ∧
      AbsRec P c' 50210 ((chainModel C).pos zta ztev).1 C.radius := by
  zuiu
  zumz
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := e - 6)
    zteqd by_omega (dst := 50211) by_norm_num
  zqbgp
  have hv : ztwnq := by
    zubab
  have hmem : ztxpk := by
    zuday
  refine ⟨_, _, .seq e₁ ztcr, by_omega, C.radius_pos, Or.inr (Or.inr ⟨by_simp, ?_,
    sp, symPtIn_of_eq isp fun j h1 h2 => by zunxc, lsp, ?_⟩)⟩
  · zueyk
    exact lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hmem).1 C.coordBound_lt_radius
  simp_all
theorem absInt_exec (c : Config)
    (hE : CEnv P W H C c) (hreg : HostRegular P.n H) {e hc : ℕ} (h01 : c.nreg 50201 = e)
    (h02 : c.nreg 50202 = hc) (he6 : 6 ≤ e) (hen : e < 2 * C.m + 7)
    (ht : 0 < (chainModel C).param zta ztev) (ht1 : (chainModel C).param zta ztev < 1)
    (hhn : hc ≤ P.n) :
    ∃ c' k, Exec P W absInt c c' k ∧ k ≤ 60 * H.length + 200 ∧
      AbsRec P c' 50210 ((chainModel C).pos zta ztev).1 C.radius := by
  zuol
  zubb
  zudym

  zubnw
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.subN 50120 50201 50081,
      .addN 50143 50053 50053]) c c₁ k₁ ∧ k₁ = 2 ∧ (c₁.nreg 50120 = e - 6 ∧
        c₁.nreg 50143 = 2 * C.m ∧ ∀ r, r ≠ 50120 → r ≠ 50143 → c₁.nreg r = c.nreg r) := by
    zuyv
    exec_block
    · config_simp; rw [hE.r53]; omega
    · refine ⟨rfl, by config_simp; zunqk, by config_simp; zunkz; ring,
        by simp_all⟩
  zucxx
  have hE₁ := hE.keep e₁.wb_right
    (exec_frameB e₁ (B := fun r => r == 50120 || r == 50143) by_decide).2.2.1
    ztwxf
  zugjo
  · zuckk
    obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, s₁, i₁, l₁, v₁, x₁⟩ := tvLoad_exec c₁ hE₁ q20
      hlt.le (dst := 50130) by_norm_num
    zue
    have e₃ := Exec.addN (P := P) w₂ 50120 50120 50032
      ztdtz
    set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50120 _ }
      with hc₃
    zucls
    obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, s₂, i₂, l₂, v₂, x₂⟩ := tvLoad_exec c₃ hE₃ (i := i + 1)
      ztbtw
      by_omega (dst := 50136) by_norm_num
    have i₁' := symPtIn_keep (symPtIn_of_eq i₁ fun j h1 h2 => by
      zumwr; zunbj) f₄
      by_decide
    obtain ⟨c₅, k₅, e₅, hk₅, v₅, r₅⟩ := edgeIdxS_exec c₄ e₄.wb_right by_omega
      hE₄.r32 i₁' i₂ l₁ l₂
    have q02 : ztlyi := by
      zuwy
      zubi
      zudar
    have q32 : ztlyh := by
      zubqc
    obtain ⟨hEi, hx⟩ := tour_abs hE.hG hE.hP hreg hNn hlt x₁ x₂ l₁ l₂ v₁ v₂
      (hc := hc) by_grind
    have hc1 : ztixw := by
      zuzn
      · zulxx
      omega
    obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W outE c₅ c₆ k₆ ∧ k₆ = 4 ∧
        (c₆.nreg 50210 = 1 ∧ SymPtIn c₆ 50211 (.onEdge _ ztzk)) := by
      zumtu
      zudpp
      exec_block
      all_goals try omega
      refine ⟨rfl, by config_simp, by config_simp, by config_simp; exact v₅, ?_⟩
      config_simp; omega
    zucie
    have ex : Exec P W absInt c c₆ _ :=
      .seq e₁ (.ifLtN_true by_omega (.seq e₂ (.seq e₃ (.seq e₄
        ztcsd))))
    have hmem : ztyky := by
      have hei : ztsig := by_omega
      zudam

    refine ⟨c₆, _, ex, by_omega, C.radius_pos, Or.inr (Or.inr ⟨q10,
      lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hmem).1 C.coordBound_lt_radius,
      _, q11, ztonu, ?_⟩)⟩
    grind
  · zucgp

    refine ztxzn
    zulta
    obtain ⟨-, -, -, -, -, -, e6⟩ := C.sidePt_box C.sideBeta
      ((chainModel C).param zta zthly)
    rw [pos_eq_sidePt, show (chainModel C).W = C.sideWalk C.sideBeta from rfl]
    simp_all

/-! ## The contracts -/

/-- The input condition of `absKey`: that of `leftSec` and a regular host. -/
def AbsKeyIn (P : Polygon) (W : ℕ) (C : Chain) (c : Config) : Prop :=
  LeftIn P W C c ∧ ∀ H', HostAt c.nmem ztzdq H' → HostRegular P.n H'

/-- The output condition of `absKey`: an abscissa record of the point of `(e, h)`, with the radius
of the chain's box. -/
def AbsKeyOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  AbsRec P c' 50210 ((chainModel C).pos zta ztbce).1 C.radius

/-- **Contract of `absKey`** (at most `16700` steps). -/
theorem absKey_meets : Meets absKey primBands (PrimPre AbsKeyIn) (PrimPost AbsKeyOut)
    ztqnc := by
  refine prim_meets by_simp_all wr_absKey ?_
  intro P W H C c₀ c hC hE ⟨⟨hen, ⟨hp0, hp1, hhn⟩, hy⟩, hreg⟩ hinp
  zudpd
  zuet
  zubgf
  obtain ⟨c', k, ex, hk, hr⟩ := classify_exec (Kb := 27 * H.length + 50)
    (Kv := 27 * H.length + 45) (Ki := 60 * H.length + 200)
    (R := fun c' => AbsRec P c' 50210 ((chainModel C).pos zta
      ⟨c₀.nreg 50201, c₀.nreg 50202⟩).1 C.radius) c₀ c hE hinp hen hp0 hp1 hhn hy
    (fun c₂ hE₂ g₂ d₂ he hpos => absBox_exec c₂ hE₂ ztdop d₂ he
      hpos)
    (fun c₂ hE₂ g₂ h6 hpar => absVtx_exec c₂ hE₂ ztdop h6
      by_omega hpar)
    (fun c₂ hE₂ g₂ _ h6 hpos => absInt_exec c₂ hE₂ hregH ztdop
      ztlpk h6 by_omega hpos hp1 hhn)
  exact ztlvn

/-- **`absCmp`**: the bit `x₁ < x₂` of the abscissa records at `50201` and `50205` into `50210`. -/
def absCmp : Stmt :=
  .seq ztfeq
    (.ifLtN 50201 50032
      (.ifLtN 50205 50032 ztbki ztbwr)
      (.ifLtN 50032 50201 ztbki
        (.ifLtN 50205 50032 ztbki
          (.ifLtN 50032 50205 ztbwr
            (kbit 50202 50206 50202 0 50210)))))
theorem wr_absCmp : wr Bprim absCmp = true := by_decide

/-- The kind of an abscissa record is `0`, `1` or `2`. -/
theorem AbsRec.kind (h : AbsRec P c r x R) :
    c.nreg r ≤ 2 := by
  zucin
theorem AbsRec.le (h : AbsRec P c r x R) :
    -R ≤ x ∧ x ≤ R := by
  zuchy
  grind

/-- **Contract of `absCmp`** (at most `260` steps): for any abscissa records of `x₁`, `x₂` with a
common radius, the bit of `x₁ < x₂`. -/
theorem absCmp_meets : Meets absCmp primBands
    (fun P W c => GoodEnv P ∧ P.n + 3 ≤ W ∧
      ∃ x₁ x₂ R : ℝ, AbsRec P c 50201 x₁ R ∧ AbsRec P c 50205 x₂ R)
    (fun P c c' => ∀ x₁ x₂ R : ℝ, AbsRec P c 50201 x₁ R → AbsRec P c 50205 x₂ R →
      BitIs c' 50210 ztokg)
    (fun _ _ => 260) := by
  intro P W c hw ⟨hG, hW, y₁, y₂, R₀, hy₁, hy₂⟩ hroom
  have e₁ := Exec.constN (P := P) hw 50032 1 by_omega
  set c₁ : Config := { c with nreg := upd c.nreg 50032 1 } with hc₁
  zud
  have r₁ : ∀ r, r ≠ 50032 → c₁.nreg r = c.nreg r := by_simp_all
  have p₁ : ztizk := by_rfl
  have k₁ := hy₁.kind
  have k₂ := hy₂.kind
  -- the answer as a function of the kinds, when it does not need the kernel
  have fin : ∀ v, v ≤ 1 → (∀ x₁ x₂ R : ℝ, AbsRec P c 50201 x₁ R → AbsRec P c 50205 x₂ R →
      (v = 1 ↔ x₁ < x₂)) → ∃ c₂, Exec P W (.instr (.constN 50210 v)) c₁ c₂ 1 ∧
      ∀ x₁ x₂ R : ℝ, AbsRec P c 50201 x₁ R → AbsRec P c 50205 x₂ R →
        BitIs c₂ 50210 ztokg := fun v hv hvt =>
    ⟨_, Exec.constN w₁ _ _ by_omega, fun x₁ x₂ R h₁ h₂ =>
      ⟨by_simp_all, by zumwv; grind⟩⟩
  have frame : ∀ c₂ k, Exec P W absCmp c c₂ k → Frame primBands c c₂ k := fun c₂ k ex =>
    frame_of_frameB (exec_frameB ex wr_absCmp) Bprim_band _
  have u01 : c₁.nreg 50201 = c.nreg 50201 := by_grind
  have u05 : c₁.nreg 50205 = c.nreg 50205 := by_grind
  by_cases a0 : c.nreg 50201 < 1
  · have t0 : c₁.nreg 50201 < c₁.nreg 50032 := by_omega
    zuirc
    · obtain ⟨c₂, e₂, h₂⟩ := fin 0 by_omega (fun x₁ x₂ R h₁ h₂ => by
        zqbgn
        zqbgo
        simp)
      have ex : ztdjr :=
        .seq e₁ (.ifLtN_true t0 ztbxn)
      grind
    · obtain ⟨c₂, e₂, h₂⟩ := fin 1 le_rfl (fun x₁ x₂ R h₁ h₂ => by
        zumci
        zqbgn
        rcases h₂.2 with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨-, hx, -⟩
        · omega
        · grind
        grind)
      have ex : ztdjr :=
        .seq e₁ (.ifLtN_true t0 ztcry)
      grind
  have t0 : ¬ c₁.nreg 50201 < c₁.nreg 50032 := by_omega
  by_cases a2 : 1 < c.nreg 50201
  · obtain ⟨c₂, e₂, h₂⟩ := fin 0 by_omega (fun x₁ x₂ R h₁ h₂ => by
      rcases h₁.2 with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨h, -⟩ <;> [omega; skip; omega]
      have := h₂.le
      grind)
    have ex : ztdjr :=
      .seq e₁ (.ifLtN_false t0 ztbxn)
    grind
  have t1 : ¬ c₁.nreg 50032 < c₁.nreg 50201 := by_omega
  zuirc
  · obtain ⟨c₂, e₂, h₂⟩ := fin 0 by_omega (fun x₁ x₂ R h₁ h₂ => by
      zqbgo
      have := h₁.le
      grind)
    have ex : ztdjr :=
      .seq e₁ (.ifLtN_false t0 (.ifLtN_false t1 ztbxn))
    grind
  have t2 : ¬ c₁.nreg 50205 < c₁.nreg 50032 := by_omega
  by_cases b2 : 1 < c.nreg 50205
  · obtain ⟨c₂, e₂, h₂⟩ := fin 1 le_rfl (fun x₁ x₂ R h₁ h₂ => by
      zumci
      rcases h₂.2 with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨h, -⟩ <;> [omega; skip; omega]
      rcases h₁.2 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hx, -⟩ <;> [omega; omega; skip]
      grind)
    have ex : ztdjr :=
      .seq e₁ (.ifLtN_false t0 (.ifLtN_false t1 (.ifLtN_false t2
        ztbxn)))
    grind
  have t3 : ¬ c₁.nreg 50032 < c₁.nreg 50205 := by_omega
  -- both are symbolic points
  have k1 : c.nreg 50201 = 1 := by_omega
  have k2 : c.nreg 50205 = 1 := by_omega
  obtain ⟨-, h₁⟩ := hy₁
  obtain ⟨-, h₂⟩ := hy₂
  rcases h₁ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, s₁, i₁, l₁, -⟩ <;> [omega; omega; skip]
  rcases h₂ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, s₂, i₂, l₂, -⟩ <;> [omega; omega; skip]
  have i₁' : SymPtIn c₁ 50202 s₁ := symPtIn_of_eq i₁ by_grind
  have i₂' : SymPtIn c₁ 50206 s₂ := symPtIn_of_eq i₂ by_grind
  obtain ⟨c₂, k₂', e₂, hk₂, f₂, b₂, t₂⟩ := kbit_exec (op := 0) (dst := 50210) hG hW c₁ w₁
    by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num l₁ l₂ l₁ i₁' i₂' i₁'
  have ex : ztdjr :=
    .seq e₁ (.ifLtN_false t0 (.ifLtN_false t1 (.ifLtN_false t2 (.ifLtN_false t3 e₂))))
  refine ⟨c₂, _, ex, by_grind, fun x₁ x₂ R h₁ h₂ => ⟨b₂, ?_⟩, by_grind⟩
  rw [t₂]
  zvnhd
  obtain ⟨-, h₁⟩ := h₁
  obtain ⟨-, h₂⟩ := h₂
  rcases h₁ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, s₁', i₁'', -, v₁⟩ <;> [omega; omega; skip]
  rcases h₂ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, s₂', i₂'', -, v₂⟩ <;> [omega; omega; skip]
  rw [symPtIn_unique i₁ i₁'', symPtIn_unique i₂ i₂'', v₁, v₂]
end
end SweepPrim
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqbib" : tactic => `(tactic| simp only [upd_same, upd_other _ _ _ (show (50032 : ℕ) ≠ 50159 by decide)])
local macro "zqbic" : tactic => `(tactic| (intro h1 h2; apply h1
                                           rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4, h5⟩))
local macro "zqbid" : tactic => `(tactic| have hselE := (nearU_iff' ztlzf).symm)
set_option hygiene true

/-!
# Sweep RAM primitives (WP-D2), part 15: `capPrim` (the cap data, for WP-F)

Registers: slots `50130` (`u`), `50133` (`v`), `50136` (`w`); comparison bits `50141 … 50152`
(`cmp4` of `u`/`v`, `w`/`v`, `u`/`w`); `near` in `50153`, `far` in `50156`, its height code in
`50159`; orientation bits `50160`, `50161`; formulas at `50162` (extremum), `50170` (nearer arm
`u`), `50182` (cap direction `+1`).  Outputs `50210 … 50213` (`CapOut`).
-/
namespace Chazelle.Core
namespace SweepPrim
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
@[expose] public section
def capLoad : Stmt :=
  .seq (.instr (.subN 50120 50201 50032)) (.seq ztvma
    (.seq ztovo (.seq (cvLoad 50133)
      (.seq (.instr (.addN 50120 50201 50032)) (cvLoad 50136)))))

/-- The height comparisons. -/
def capBits : Stmt :=
  .seq (cmp4 50130 50133 50141) (.seq (cmp4 50136 50133 50145) (cmp4 50130 50136 50149))

/-- `v` below both neighbours. -/
def fBelow : BF := .and (.var 50142) (.var 50146)
/-- `v` above both neighbours. -/
def fAbove : BF := .and (.var 50141) (.var 50145)
/-- A local extremum. -/
def fExt : BF := .or fBelow fAbove
/-- The nearer arm is `u`. -/
def fNearU : BF := .or (.and fBelow (.var 50149)) (.and fAbove (.var 50150))
/-- The cap direction is `+1`. -/
def fPos : BF :=
  .not (.or (.and fBelow ztuvw) (.and fAbove (.and (.not ztuvw) (.not (.var 50161)))))

/-- Select `near` and `far`. -/
def capSel : Stmt :=
  .ifLtN 50170 50032
    (block (copies [ztngw, ztngy, ztnha, ztnhb,
      ztnhd, ztnhf]))
    (block (copies [ztngv, ztngx, ztngz, ztnhc,
      ztnhe, ztnhg]))

/-- The height code of `near`. -/
def capCode : Stmt :=
  .seq (.ifLtN 50153 50032 (.instr (.copyN 50159 50154)) (.instr (.copyN 50159 50155)))
    (.instr (.addN 50159 50159 50032))

/-- The orientation of `v`, `far`, `near`. -/
def capDet : Stmt := .seq (kbit 50133 50156 50153 2 50160) (kbit 50133 50156 50153 3 50161)

/-- The outputs. -/
def capOutS : Stmt := block [.copyN 50210 50162, .copyN 50211 50170, .copyN 50212 50159,
  .copyN 50213 50182]

/-- The core. -/
def capCore : Stmt :=
  .seq capLoad (.seq capBits (.seq ztvqh (.seq ztvqj
    ztfxu)))

/-- **The primitive `capPrim`.** -/
def capPrim : Stmt := .seq pHead capCore
theorem wr_capPrim : wr Bprim capPrim = true := by_decide

/-! ## The contract -/

/-- The input condition: an index with two neighbours on the chain. -/
def CapIn (_ : Polygon) (_ : ℕ) (C : Chain) (c : Config) : Prop :=
  1 ≤ c.nreg 50201 ∧ c.nreg 50201 + 1 ≤ C.m

/-- The output condition. -/
def CapOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  let k := c.nreg 50201
  let u := C.vertex ztie
  let v := C.vertex k
  let w := C.vertex zts
  let nearU := |u.2 - v.2| < |w.2 - v.2|
  let near := if nearU then u else w
  let far := if nearU then w else u
  BitIs c' 50210 (0 < zthks * ztcfj) ∧
    (0 < zthks * ztcfj → BitIs c' 50211 nearU) ∧
    1 ≤ c'.nreg 50212 ∧ c'.nreg 50212 ≤ P.n ∧
    (0 < zthks * ztcfj → ((Qof P).vtx ztrlf).2 = near.2) ∧
    (0 < zthks * ztcfj → u.2 ≠ w.2 →
      BitIs c' 50213 (¬ near.1 < (Geometry.lerp v far ((near.2 - v.2) / (far.2 - v.2))).1))

/-! ## Real arithmetic of the tests -/
theorem ext_iff' (u v w : ℝ) : 0 < (u - v) * ztbez ↔ ztojh ∨ ztoiy := by
  constructor
  · zuq
    rcases lt_trichotomy u v with h1 | h1 | h1
    · right; refine ztcya; by_contra h2; push Not at h2; nlinarith
    · simp_all
    simp_all
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> nlinarith
theorem nearU_iff' {u v w : ℝ} (h : ztojh ∨ ztoiy) :
    |u - v| < |w - v| ↔ ((v < u ∧ v < w) ∧ u < w) ∨ ((u < v ∧ w < v) ∧ w < u) := by
  grind

/-! ## Execution -/
set_option maxHeartbeats 4000000 in
/-- The host points of `u, v, w`. -/
theorem capLoad_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {k : ℕ} (h201 : c.nreg 50201 = k) (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ C.m) :
    ∃ c' k', Exec P W capLoad c c' k' ∧ k' ≤ 81 * H.length + 63 ∧ CEnv P W H C c' ∧
      (∀ r, 50200 ≤ r → c'.nreg r = c.nreg r) ∧
      ∃ su sv sw : SymPt, SymPtIn c' 50130 su ∧ SymPtIn c' 50133 sv ∧ SymPtIn c' 50136 sw ∧
        su.Lt P.n ∧ sv.Lt P.n ∧ sw.Lt P.n ∧ su.eval zta = C.vertex ztie ∧
        sv.eval zta = C.vertex k ∧ sw.eval zta = C.vertex zts := by
  have hBcv : ∀ (d : ℕ) (r : ℕ), 50200 ≤ r → Bcv d r = false → True := by_simp_all
  have keep200 : ∀ {c₁ c₂ : Config} {d : ℕ}, FrameB (Bcv d) c₁ c₂ → d < 50200 → d + 3 ≤ 50200 →
      ∀ r, 50200 ≤ r → c₂.nreg r = c₁.nreg r := fun hf _ hd r hr => hf.1 r (by
    simp only [Bcv, Bhost, Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
    omega)
  have e₁ := Exec.subN (P := P) hE.wb 50120 50201 50032
  zumz
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, su, iu, lu, vu⟩ := cvLoad_exec _ hE₁ (k := k - 1)
    (by simp [h201, hE.r32]) by_omega (dst := 50130) by_norm_num
  have r₂ : ∀ r, 50200 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [keep200 f₂ by_norm_num by_norm_num r hr]; simp only
    zutv
  have e₃ := Exec.copyN (P := P) e₂.wb_right 50120 50201
  zucls
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, sv, iv, lv, vv⟩ := cvLoad_exec _ hE₃ (k := k)
    (by zumwv; grind) by_omega
    (dst := 50133) by_norm_num
  have r₄ : ∀ r, 50200 ≤ r → c₄.nreg r = c.nreg r := fun r hr => by
    rw [keep200 f₄ by_norm_num by_norm_num r hr]; simp only
    rw [upd_other _ _ _ by_omega, r₂ r hr]
  have iu₄ := symPtIn_keep (symPtIn_of_eq iu fun j h1 h2 => by
    zvmwf; grind) f₄ by_decide
  have e₅ := Exec.addN (P := P) e₄.wb_right 50120 50201 50032
    (by rw [r₄ _ by_norm_num, h201, hE₄.r32]; have := hE₄.NW; have := C.m_lt;
        have := hE₄.n_eq; omega)
  zujze
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, hE₆, sw, iw, lw, vw⟩ := cvLoad_exec _ hE₅ (k := k + 1)
    (by zumwv; rw [r₄ 50201 by_norm_num, h201, hE₄.r32])
    by_omega (dst := 50136) by_norm_num
  have r₆ : ∀ r, 50200 ≤ r → c₆.nreg r = c.nreg r := fun r hr => by
    rw [keep200 f₆ by_norm_num by_norm_num r hr]; simp only
    rw [upd_other _ _ _ by_omega, r₄ r hr]
  have iu₆ := symPtIn_keep (symPtIn_of_eq iu₄ fun j h1 h2 => by
    zvmwf; grind) f₆ by_decide
  have iv₆ := symPtIn_keep (symPtIn_of_eq iv fun j h1 h2 => by
    zvmwf; grind) f₆ by_decide
  have ex : Exec P W capLoad c c₆ _ :=
    .seq e₁ ztfv
  grind
theorem BitIs.decEq {c : Config} {r : ℕ} {p : Prop} [Decidable p] (h : BitIs c r p) :
    decide ztdmw = decide p := by
  by_cases hp : p
  · rw [decide_eq_true hp]; exact decide_eq_true (h.2.2 hp)
  · rw [decide_eq_false hp]; exact decide_eq_false fun h' => hp (h.2.1 h')
set_option maxHeartbeats 8000000 in
/-- The tests after the loads. -/
theorem capTail_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {su sv sw : SymPt} (iu : SymPtIn c 50130 su) (iv : SymPtIn c 50133 sv)
    (iw : SymPtIn c 50136 sw) (lu : su.Lt P.n) (lv : sv.Lt P.n) (lw : sw.Lt P.n) :
    ∃ c' k', Exec P W (.seq capBits (.seq ztvqh (.seq ztvqj
        ztfxu))) c c' k' ∧
      k' ≤ 4000 ∧
      let U := su.eval zta
      let V := sv.eval zta
      let X := sw.eval zta
      let nearU := |U.2 - V.2| < |X.2 - V.2|
      let near := if nearU then U else X
      let far := if nearU then X else U
      BitIs c' 50210 ztzap ∧
        (0 < zthda * zthde → BitIs c' 50211 nearU) ∧
        1 ≤ c'.nreg 50212 ∧ c'.nreg 50212 ≤ P.n ∧
        (0 < zthda * zthde → ((Qof P).vtx ztrlf).2 = near.2) ∧
        (0 < zthda * zthde → U.2 ≠ X.2 →
          BitIs c' 50213 (¬ near.1 < (Geometry.lerp V far ((near.2 - V.2) / (far.2 - V.2))).1)) := by
  zucvu
  zuol
  zudoc
  -- the comparison bits
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, a1, a2, -, -⟩ := cmp4_exec (base := 50141) hG hW c hE.wb
    by_norm_num by_norm_num by_norm_num by_norm_num lu lv iu iv
  have iu₁ := symPtIn_keep iu f₁ by_decide
  have iv₁ := symPtIn_keep iv f₁ by_decide
  have iw₁ := symPtIn_keep iw f₁ by_decide
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, a5, a6, -, -⟩ := cmp4_exec (base := 50145) hG hW c₁ e₁.wb_right
    by_norm_num by_norm_num by_norm_num by_norm_num lw lv iw₁ iv₁
  have iu₂ := symPtIn_keep iu₁ f₂ by_decide
  have iv₂ := symPtIn_keep iv₁ f₂ by_decide
  have iw₂ := symPtIn_keep iw₁ f₂ by_decide
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, a9, a10, -, -⟩ := cmp4_exec (base := 50149) hG hW c₂ e₂.wb_right
    by_norm_num by_norm_num by_norm_num by_norm_num lu lw iu₂ iw₂
  have iu₃ := symPtIn_keep iu₂ f₃ by_decide
  have iv₃ := symPtIn_keep iv₂ f₃ by_decide
  have iw₃ := symPtIn_keep iw₂ f₃ by_decide
  have b41 := (a1.keep f₂ by_decide).keep f₃ by_decide
  have b42 := (a2.keep f₂ by_decide).keep f₃ by_decide
  have b45 := a5.keep f₃ by_decide
  have b46 := a6.keep f₃ by_decide
  have b49 := a9
  have b50 := a10
  simp only [Ys] at b41 b42 b45 b46 b49 b50
  zubvt
  generalize hU : su.eval _ = U at b41 b42 b45 b46 b49 b50 ⊢
  generalize hV : sv.eval _ = V at b41 b42 b45 b46 b49 b50 ⊢
  generalize hX : sw.eval _ = X at b41 b42 b45 b46 b49 b50 ⊢
  -- the extremum
  have vars : ∀ r, r ∈ [50141, 50142, 50145, 50146, 50149, 50150] → c₃.nreg r ≤ 1 := by
    zuz
    zuvy
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [b41.1, b42.1, b45.1, b46.1, b49.1, b50.1]
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄⟩ := BF.compile_exec (P := P) hW2 fExt 50162 c₃ e₃.wb_right
    (by simp only [fExt, fBelow, fAbove, BF.VarsOK]
        simp_all)
  have k34 := fun r hr =>
    f₄.1 r ztcev
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, f₅⟩ := BF.compile_exec (P := P) hW2 fNearU 50170 c₄ e₄.wb_right
    (by simp only [fNearU, fBelow, fAbove, BF.VarsOK]
        simp_all)
  have k45 := fun r hr =>
    f₅.1 r ztcev
  have k35 : ∀ r, r < 50162 → c₅.nreg r = c₃.nreg r := fun r hr => by
    grind
  have extE : fExt.eval (fun r => decide zthwd) =
      decide (ztnpz ∨ ztnpy) := by
    simp only [fExt, fBelow, fAbove, BF.eval, b41.decEq, b42.decEq, b45.decEq, b46.decEq]
    simp
  have nearE : fNearU.eval (fun r => decide ztrof) =
      decide ztdeb := by
    have e : ∀ r, r < 50162 → decide ztrof = decide zthwd := by_simp_all
    simp only [fNearU, fBelow, fAbove, BF.eval, e _ (show 50141 < 50162 by norm_num),
      e _ (show 50142 < 50162 by norm_num), e _ (show 50145 < 50162 by norm_num),
      e _ (show 50146 < 50162 by norm_num), e _ (show 50149 < 50162 by norm_num),
      e _ (show 50150 < 50162 by norm_num), b41.decEq, b42.decEq, b45.decEq, b46.decEq,
      b49.decEq, b50.decEq]
    simp
  have ext_bit : BitIs c₅ 50162 ztzap := by
    refine BitIs.of_bf (f := fExt) (v := fun r => decide zthwd)
      by_simp_all ?_
    rw [extE, decide_eq_true_iff, ext_iff']
  have near_bit : BitIs c₅ 50170
      ztdeb := by
    refine BitIs.of_bf v₅ ?_
    grind
  -- the environment so far
  have hE₅ :=
    ((((hE.frame f₁ e₁.wb_right by_decide).frame f₂ e₂.wb_right by_decide).frame f₃
      e₃.wb_right by_decide).frame f₄ e₄.wb_right by_decide).frame f₅ e₅.wb_right by_decide
  have iu₅ : SymPtIn c₅ 50130 su := symPtIn_of_eq iu₃ by_grind
  have iv₅ : SymPtIn c₅ 50133 sv := symPtIn_of_eq iv₃ by_grind
  have iw₅ : SymPtIn c₅ 50136 sw := symPtIn_of_eq iw₃ by_grind
  -- the selection
  set sel : Prop := (ztnpz ∧ U.2 < X.2) ∨ (ztnpy ∧ X.2 < U.2)
    with hsel
  obtain ⟨c₆, k₆, e₆, hk₆, sn, sf, isn, isf, hsn, r₆, m₆, rr₆, rm₆, o₆⟩ : ∃ c₆ k₆,
      Exec P W capSel c₅ c₆ k₆ ∧ k₆ ≤ 8 ∧ ∃ sn sf : SymPt, SymPtIn c₆ 50153 sn ∧
        SymPtIn c₆ 50156 sf ∧ (sn, sf) = (if sel then (su, sw) else (sw, su)) ∧
        (∀ r, (r < 50153 ∨ 50158 < r) → c₆.nreg r = c₅.nreg r) ∧ c₆.nmem = c₅.nmem ∧
        c₆.rreg = c₅.rreg ∧ c₆.rmem = c₅.rmem ∧ c₆.output = c₅.output := by
    have h32 := hE₅.r32
    have cp := fun (l : List _) => copies_exec (P := P) l c₅ e₅.wb_right
    zulwc
    · have h1 := near_bit.2.2 hs
      obtain ⟨c₆, e, h3, h3', hrr, hm, hrm, ho⟩ := cp [ztngv, ztngx,
        ztngz, ztnhc, ztnhe, ztnhg] by_decide by_decide
      refine ⟨c₆, _, .ifLtN_false by_omega e, by_simp, su, sw, ?_, ?_,
        by grind, fun r hr => h3' r ztbaw, hm, hrr, hrm, ho⟩
      · exact symPtIn_copy iu₅ (h3 ztngv by_simp) (h3 ztngx by_simp)
          (h3 ztngz by_simp)
      · exact symPtIn_copy iw₅ (h3 ztnhc by_simp) (h3 ztnhe by_simp)
          (h3 ztnhg by_simp)
    · have h0 : c₅.nreg 50170 = 0 := by
        grind
      obtain ⟨c₆, e, h3, h3', hrr, hm, hrm, ho⟩ := cp [ztngw, ztngy,
        ztnha, ztnhb, ztnhd, ztnhf] by_decide by_decide
      refine ⟨c₆, _, .ifLtN_true by_omega e, by_simp, sw, su, ?_, ?_,
        by simp [hs], fun r hr => h3' r ztbaw, hm, hrr, hrm, ho⟩
      · exact symPtIn_copy iw₅ (h3 ztngw by_simp) (h3 ztngy by_simp)
          (h3 ztnha by_simp)
      · exact symPtIn_copy iu₅ (h3 ztnhb by_simp) (h3 ztnhd by_simp)
          (h3 ztnhf by_simp)
  have hE₆ := hE₅.keep e₆.wb_right m₆ fun r hr => r₆ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr; omega)
  have lsn : sn.Lt P.n := by
    grind
  have lsf : sf.Lt P.n := by
    grind
  -- the height code
  obtain ⟨c₇, k₇, e₇, hk₇, v59, r₇, m₇, rr₇, rm₇, o₇⟩ : ∃ c₇ k₇, Exec P W capCode c₆ c₇ k₇ ∧
      k₇ ≤ 4 ∧ c₇.nreg 50159 = shv sn + 1 ∧ (∀ r, r ≠ 50159 → c₇.nreg r = c₆.nreg r) ∧
      c₇.nmem = c₆.nmem ∧ c₇.rreg = c₆.rreg ∧ c₇.rmem = c₆.rmem ∧ c₇.output = c₆.output := by
    have h32 := hE₆.r32
    have hnW : shv sn + 1 ≤ W := by
      cases sn with
      | vtx i => simp only [shv, SymPt.Lt] at lsn ⊢; omega
      | onEdge e h => simp only [shv, SymPt.Lt] at lsn ⊢; omega
    cases sn with
    | vtx i =>
      obtain ⟨i0, i1⟩ := isn
      have e₁ := Exec.copyN (P := P) e₆.wb_right 50159 50154
      have e₂ := Exec.addN (P := P) e₁.wb_right 50159 50159 50032 (by
        zqbib
        zuopm; simp only [shv] at hnW; omega)
      refine ⟨_, _, .seq ztjdl e₂, by_omega, ?_,
        fun r hr => by zunif, rfl, rfl, rfl, rfl⟩
      zqbib
      zuopm; rfl
    | onEdge e h =>
      obtain ⟨i0, i1, i2⟩ := isn
      have e₁ := Exec.copyN (P := P) e₆.wb_right 50159 50155
      have e₂ := Exec.addN (P := P) e₁.wb_right 50159 50159 50032 (by
        zqbib
        zuopn; simp only [shv] at hnW; omega)
      refine ⟨_, _, .seq ztnac e₂, by_omega, ?_,
        fun r hr => by zunif, rfl, rfl, rfl, rfl⟩
      zqbib
      zuopn; rfl
  have hE₇ := hE₆.keep e₇.wb_right m₇ fun r hr => r₇ r (by
    simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr; omega)
  have isn₇ : SymPtIn c₇ 50153 sn := symPtIn_of_eq isn by_grind
  have isf₇ : SymPtIn c₇ 50156 sf := symPtIn_of_eq isf by_grind
  have iv₇ : SymPtIn c₇ 50133 sv := symPtIn_of_eq iv₅ by_grind
  -- the orientation bits
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, d₈, t₈⟩ := kbit_exec (op := 2) (dst := 50160) hG hW c₇
    e₇.wb_right by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num lv lsf lsn
    iv₇ isf₇ isn₇
  zujaa
  have isf₈ := symPtIn_keep isf₇ f₈ by_decide
  have isn₈ := symPtIn_keep isn₇ f₈ by_decide
  obtain ⟨c₉, k₉, e₉, hk₉, f₉, d₉, t₉⟩ := kbit_exec (op := 3) (dst := 50161) hG hW c₈
    e₈.wb_right by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num lv lsf lsn
    iv₈ isf₈ isn₈
  have b60 : BitIs c₉ 50160 (0 < det V ztzgz ztzhe) := by
    have := BitIs.keep ⟨d₈, t₈⟩ f₉ by_decide
    zughf
  have b61 : BitIs c₉ 50161 (det V ztzgz ztzhe = 0) := by
    have : BitIs c₉ 50161 _ := ⟨d₉, t₉⟩
    zughf
  -- transport of the early bits to `c₉`
  have k59 : ∀ r, 50100 ≤ r → r < 50153 → c₉.nreg r = c₅.nreg r := fun r hr' hr => by
    rw [f₉.1 r (by simp only [Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        beq_eq_false_iff_ne]; omega),
      f₈.1 r (by simp only [Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        beq_eq_false_iff_ne]; omega), r₇ r by_omega, r₆ r by_omega]
  have g41 : BitIs c₉ 50141 _ := b41.of_eq by_grind
  have g42 : BitIs c₉ 50142 _ := b42.of_eq by_grind
  have g45 : BitIs c₉ 50145 _ := b45.of_eq by_grind
  have g46 : BitIs c₉ 50146 _ := b46.of_eq by_grind
  have h9w := e₉.wb_right
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, v₁₀, f₁₀⟩ := BF.compile_exec (P := P) hW2 fPos 50182 c₉ h9w
    (by simp only [fPos, fBelow, fAbove, BF.VarsOK]
        exact ⟨⟨by_grind, ⟨by_norm_num, b60.1⟩⟩,
          ⟨by_grind, ⟨⟨by_norm_num, b60.1⟩,
            by omega⟩⟩⟩)
  have k910 := fun r hr =>
    f₁₀.1 r ztcev
  set below : Prop := V.2 < U.2 ∧ V.2 < X.2 with hbelow
  set above : Prop := U.2 < V.2 ∧ X.2 < V.2 with habove
  set dt := det V ztzgz ztzhe with hdt
  have posE : fPos.eval (fun r => decide (c₉.nreg r = 1)) =
      decide (¬ ((below ∧ 0 < dt) ∨ (above ∧ ¬ 0 < dt ∧ ¬ dt = 0))) := by
    simp only [fPos, fBelow, fAbove, BF.eval, g41.decEq, g42.decEq, g45.decEq, g46.decEq,
      b60.decEq, b61.decEq]
    rfl
  have pos_bit : BitIs c₁₀ 50182 _ :=
    BitIs.of_bf v₁₀
      (by rw [posE, decide_eq_true_iff])
  -- the outputs
  obtain ⟨c₁₁, k₁₁, e₁₁, hk₁₁, q⟩ : ∃ c₁₁ k₁₁, Exec P W capOutS c₁₀ c₁₁ k₁₁ ∧ k₁₁ = 4 ∧
      (c₁₁.nreg 50210 = c₁₀.nreg 50162 ∧ c₁₁.nreg 50211 = c₁₀.nreg 50170 ∧
        c₁₁.nreg 50212 = c₁₀.nreg 50159 ∧ c₁₁.nreg 50213 = c₁₀.nreg 50182) := by
    have hw := e₁₀.wb_right
    unfold capOutS
    exec_block
    simp
  obtain ⟨q10, q11, q12, q13⟩ := q
  have ex : Exec P W (.seq capBits (.seq _ (.seq _
      (.seq capSel (.seq capCode (.seq capDet _)))))) c c₁₁
      _ :=
    .seq ztwrj (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq (.seq e₈ e₉)
      ztsqd)))))
  have hsz1 : fExt.size = 7 := rfl
  have hsz2 : fNearU.size = 11 := rfl
  have hsz3 : fPos.size = 16 := rfl
  -- values at the end
  have c62 : c₁₀.nreg 50162 = c₅.nreg 50162 := by
    rw [k910 _ by_norm_num, f₉.1 _ by_decide, f₈.1 _ by_decide, r₇ _ by_decide,
      r₆ _ by_norm_num]
  have c70 : c₁₀.nreg 50170 = c₅.nreg 50170 := by
    rw [k910 _ by_norm_num, f₉.1 _ by_decide, f₈.1 _ by_decide, r₇ _ by_decide,
      r₆ _ by_norm_num]
  have c59 : c₁₀.nreg 50159 = shv sn + 1 := by
    rw [k910 _ by_norm_num, f₉.1 _ by_decide, f₈.1 _ by_decide, v59]
  have hsnE : sn = if sel then su else sw := by
    grind
  have hsfE : sf = if sel then sw else su := by
    grind
  refine ⟨c₁₁, _, ex, by_omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ext_bit.of_eq by_omega
  · intro hext
    refine (near_bit.of_eq by_omega).congr ?_
    exact (nearU_iff' ztlzf).symm
  · omega
  · rw [q12, c59]
    cases sn with
    | vtx i => simp only [shv, SymPt.Lt] at lsn ⊢; omega
    | onEdge e h => simp only [shv, SymPt.Lt] at lsn ⊢; omega
  · intro hext
    zqbid
    rw [q12, c59, Nat.add_sub_cancel, ← eval_snd_shv, hsnE]
    grind
  · intro hext hUX
    zqbid
    refine (pos_bit.of_eq by_omega).congr ?_
    have hext' := (ext_iff' _ _ _).1 hext
    zulwc
    · have hn := hselE.1 hs
      simp only [ite_eq_left hn]
      rw [hdt, hsnE, hsfE, ite_eq_left hs, ite_eq_left hs, hU, hX]
      have hne : X.2 ≠ V.2 := by_grind
      rw [capx_iff V X U hne]
      constructor
      · zqbic
        · grind
        grind
      · zukjh
        rcases h2 with ⟨⟨-, h3⟩, h4⟩ | ⟨⟨-, h3⟩, h4, h5⟩
        · grind
        grind
    · have hn := fun h => hs (hselE.2 h)
      simp only [ite_eq_right hn]
      rw [hdt, hsnE, hsfE, ite_eq_right hs, ite_eq_right hs, hU, hX]
      have hne : U.2 ≠ V.2 := by_grind
      rw [capx_iff V U X hne]
      constructor
      · zqbic
        · grind
        grind
      · zukjh
        rcases h2 with ⟨⟨h3, -⟩, h4⟩ | ⟨⟨h3, -⟩, h4, h5⟩
        · grind
        grind

/-- **Contract of `capPrim`** (at most `10100` steps). -/
theorem capPrim_meets : Meets capPrim primBands (PrimPre CapIn) (PrimPost CapOut)
    (fun _ _ => 10100) := by
  refine prim_meets by_simp_all wr_capPrim ?_
  intro P W H C c₀ c _hC hE ⟨hk1, hk2⟩ hinp
  zujyp
  obtain ⟨c₁, k₁, e₁, hk₁, hE₁, -, su, sv, sw, iu, iv, iw, lu, lv, lw, vu, vv, vw⟩ :=
    capLoad_exec c hE h201 hk1 hk2
  obtain ⟨c₂, k₂, e₂, hk₂, hout⟩ := capTail_exec c₁ hE₁ iu iv iw lu lv lw
  zubgf
  refine ztkkk
  simp only [vu, vv, vw] at hout
  exact hout

/-! ## The height index of a chain vertex -/

/-- The core of `hvPrim`: the height index of the host point of chain vertex `50201`. -/
def hvCore : Stmt :=
  .seq ztovo (.seq ztvma
    (.ifLtN 50130 50032 (.instr (.copyN 50210 50131)) (.instr (.copyN 50210 50132))))

/-- **The primitive `hvPrim`.** -/
def hvPrim : Stmt := .seq pHead hvCore
theorem wr_hvPrim : wr Bprim hvPrim = true := by_decide

/-- The input condition of `hvPrim`. -/
def HvIn (_ : Polygon) (_ : ℕ) (C : Chain) (c : Config) : Prop := c.nreg 50201 ≤ C.m

/-- The output condition of `hvPrim`: a vertex of `Q` at the height of the chain vertex. -/
def HvOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  c'.nreg 50210 < P.n ∧ ((Qof P).vtx (c'.nreg 50210)).2 = (C.vertex ztcuv).2

/-- **Contract of `hvPrim`** (at most `3000` steps). -/
theorem hvPrim_meets : Meets hvPrim primBands (PrimPre HvIn) (PrimPost HvOut)
    (fun _ _ => 3000) := by
  refine prim_meets by_simp_all wr_hvPrim ?_
  intro P W H C c₀ c _hC hE hk hinp
  zujyp
  have e₁ := Exec.copyN (P := P) hE.wb 50120 50201
  zumz
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp⟩ := cvLoad_exec _ hE₁ (k := c₀.nreg 50201)
    by_simp_all hk (dst := 50130) by_norm_num
  have h32 := hE₂.r32
  zubgf
  zuja
  have key : ∀ (c₃ : Config) (v : ℕ), c₃.nreg 50210 = v → v = shv sp →
      HvOut P C c₀ c₃ := fun c₃ v h1 h2 => by
    refine ⟨by zvmza; cases sp <;> simp only [shv, SymPt.Lt] at lsp ⊢ <;> omega, ?_⟩
    rw [h1, h2, ← eval_snd_shv, vsp]
  cases sp with
  | vtx i =>
    obtain ⟨i0, i1⟩ := isp
    have e₃ := Exec.copyN (P := P) hw₂ 50210 50131
    exact ⟨_, _, .seq e₁ ztgxc, by_omega,
      key _ (c₂.nreg 50131) by_simp by_tauto⟩
  | onEdge e h =>
    obtain ⟨i0, i1, i2⟩ := isp
    have e₃ := Exec.copyN (P := P) hw₂ 50210 50132
    exact ⟨_, _, .seq e₁ ztejy, by_omega,
      key _ (c₂.nreg 50132) by_simp by_tauto⟩
