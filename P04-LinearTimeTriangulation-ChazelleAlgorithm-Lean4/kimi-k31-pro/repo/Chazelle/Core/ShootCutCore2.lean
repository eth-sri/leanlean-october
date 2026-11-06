module

public import Chazelle.Core.ShootCutGeneral
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# WP-G, part 33: the set-up and the whole core

* `cPre_exec`: the constants, the chain descriptor, the grade-table handles, the tour start and
  the number of host points (`CoreRegs`);
* `core_exec`: **the core** hands pieces that tile the subarc (`ArcOK`), are valid (`PcOK`), and
  number `O(log γ)`, in `O((K + 1) log γ)` steps (`K` the cost of `emit`).
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}

theorem cHead1_exec (d : Config) (hw : WordsBounded W d) {MD Hh' cs cm : ℕ}
    (h00 : d.nreg 150000 = MD) (h91 : d.nreg 150091 = 1) (mA : d.nmem (MD + 1) = Hh')
    (mB : d.nmem (MD + 1 + 1) = cs) (mC : d.nmem (MD + 1 + 1 + 1) = cm) (hMW : MD + 3 ≤ W) :
    ∃ d' k, Exec P W cHead1 d d' k ∧ k = 6 ∧ d'.nreg 150021 = Hh' ∧ d'.nreg 150022 = cs ∧
      d'.nreg 150023 = cm ∧ d'.nreg 150075 = MD + 1 + 1 + 1 ∧
      (∀ x, x ≠ 150021 → x ≠ 150022 → x ≠ 150023 → x ≠ 150075 → d'.nreg x = d.nreg x) ∧
      d'.nmem = d.nmem := by
  unfold cHead1
  exec_block
  all_goals first | (config_simp; rwo [h00, h91]) | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h1 h2 h3 h4 => ?_, rfl⟩
  · config_simp; rw [h00, h91, mA]
  · config_simp; rw [h00, h91, mB]
  · config_simp; rw [h00, h91, mC]
  · config_simp; rw [h00, h91]
  · simp only [upd]; split_ifs <;> first | rfl | omega

theorem cHead2_exec (d : Config) (hw : WordsBounded W d) {a cm T bit : ℕ}
    (h75 : d.nreg 150075 = a) (h91 : d.nreg 150091 = 1) (h96 : d.nreg 150096 = 6)
    (h23 : d.nreg 150023 = cm) (mD : d.nmem (a + 1) = T) (mE : d.nmem (a + 1 + 1) = bit)
    (hMW : a + 2 ≤ W) (hcW : 2 * cm + 6 ≤ W) :
    ∃ d' k, Exec P W cHead2 d d' k ∧ k = 7 ∧ d'.nreg 150024 = T ∧ d'.nreg 150025 = bit ∧
      d'.nreg 150029 = 2 * cm ∧ d'.nreg 150032 = 2 * cm + 6 ∧ d'.nreg 150031 = 2 * cm + 5 ∧
      (∀ x, x ≠ 150024 → x ≠ 150025 → x ≠ 150029 → x ≠ 150031 → x ≠ 150032 → x ≠ 150075 →
        d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  unfold cHead2
  exec_block
  all_goals first | (config_simp; rwo [h75, h91]) | (config_simp; rwo [h23]) |
    (config_simp; rwo [h23, h96]) | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 h4 h5 h6 => ?_, rfl⟩
  · config_simp; rw [h75, h91, mD]
  · config_simp; rw [h75, h91, mE]
  · config_simp; rwring [h23]
  · config_simp; rwring [h23, h96]
  · config_simp; rwo [h23, h96, h91]
  · simp only [upd]; split_ifs <;> first | rfl | omega

theorem cHead3_exec (d : Config) (hw : WordsBounded W d) {h : ℕ} {m₀ : ℕ → ℕ}
    (h13 : d.nreg 150013 = h) (h91 : d.nreg 150091 = 1) (h92 : d.nreg 150092 = 2)
    (h93 : d.nreg 150093 = 3) (mh : d.nmem h = m₀ h) (mh1 : d.nmem (h + 1) = m₀ (h + 1))
    (mh2 : d.nmem (h + 2) = m₀ (h + 2)) (mh3 : d.nmem (h + 3) = m₀ (h + 3))
    (hnW : P.n ≤ W) (hhW : h + 3 ≤ W) (hsW : m₀ (h + 1) + 2 ≤ W) :
    ∃ d' k, Exec P W cHead3 d d' k ∧ k = 9 ∧ d'.nreg 150027 = P.n ∧ d'.nreg 150033 = m₀ h ∧
      d'.nreg 150036 = m₀ (h + 1) + 2 ∧ d'.nreg 150034 = m₀ (h + 2) ∧
      d'.nreg 150035 = m₀ (h + 3) ∧
      (∀ x, x ≠ 150027 → x ≠ 150033 → x ≠ 150034 → x ≠ 150035 → x ≠ 150036 → x ≠ 150075 →
        x ≠ 150076 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem := by
  unfold cHead3
  exec_block
  all_goals first | exact hnW | (config_simp; rwo [h13, h91]) |
    (config_simp; rwo [h13, h91, mh1, h92]) | (config_simp; rwo [h13, h92]) |
    (config_simp; rwo [h13, h93]) | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 h4 h5 h6 h7 => ?_, rfl⟩
  · config_simp
  · config_simp; rw [h13, mh]
  · config_simp; rw [h13, h91, mh1, h92]
  · config_simp; rw [h13, h92, mh2]
  · config_simp; rw [h13, h93, mh3]
  · simp only [upd]; split_ifs <;> first | rfl | omega

/-- **The set-up of the core.** -/
theorem cPre_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD mode : ℕ} {s e : WPos}
    (hD : ChainDescAt m₀ (MD + 1) (Qof P) H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ (MD + 1) = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (h00 : d.nreg 150000 = MD) (h01 : d.nreg 150001 = s.edge) (h02 : d.nreg 150002 = s.hgt)
    (h03 : d.nreg 150003 = e.edge) (h04 : d.nreg 150004 = e.hgt) (h09 : d.nreg 150009 = γ)
    (h13 : d.nreg 150013 = h) (h20 : d.nreg 150020 = mode) :
    ∃ d' k, Exec P W cPre d d' k ∧ k ≤ 12 * H.length + 60 ∧
      CoreRegs P C H Hh MD h γ mode s e m₀ d' ∧ FrameB Scr d d' := by
  have hWn := S.hW
  unfold hostWords at hWn
  have hm2 := S.hm2'
  have hAW := S.hAW
  have hN := S.hN
  have hNn := S.hNn
  obtain ⟨hh3, -, -⟩ := grade_low S.hR
  obtain ⟨-, hpow, -⟩ := grade_low S.hR
  have hp0 := hpow 0 (by omega)
  obtain ⟨hHost, hP, hs', hm', hT', hb'⟩ := hD
  have hT := C.topIdx_le
  -- the constants
  obtain ⟨d₁, k₁, e₁, hk₁, c90, c91, c92, c93, c96, r₁, m₁⟩ := cInit_exec (P := P) d hw (by omega)
  have g₁ : ∀ x, x < 150090 → d₁.nreg x = d.nreg x := fun x hx =>
    r₁ x (by omega) (by omega) (by omega) (by omega) (by omega)
  have mm : ∀ a, a < A₀ → d₁.nmem a = m₀ a := fun a ha => by rw [m₁]; exact hm a ha
  have a00 : d₁.nreg 150000 = MD := by rw [g₁ _ (by omega), h00]
  have a13 : d₁.nreg 150013 = h := by rw [g₁ _ (by omega), h13]
  have mA : d₁.nmem (MD + 1) = Hh := by rw [mm _ (by omega), hHh]
  have mB : d₁.nmem (MD + 1 + 1) = C.s := by rwx [mm _ (by omega)]
  have mC : d₁.nmem (MD + 1 + 1 + 1) = C.m := by rwx [mm _ (by omega)]
  have mD : d₁.nmem (MD + 1 + 1 + 1 + 1) = C.topIdx := by rwx [mm _ (by omega)]
  have mh : d₁.nmem h = m₀ h := mm _ (by omega)
  have mh1 : d₁.nmem (h + 1) = m₀ (h + 1) := mm _ (by omega)
  have mh2 : d₁.nmem (h + 2) = m₀ (h + 2) := mm _ (by omega)
  have mh3 : d₁.nmem (h + 3) = m₀ (h + 3) := mm _ (by omega)
  have w₁ := e₁.wb_right
  -- the descriptor and the handles
  obtain ⟨d₂, k₂, e₂, hk₂, o21, o22, o23, o75, r₂, m₂⟩ := cHead1_exec (P := P) d₁ w₁ a00 c91 mA mB mC
    (by omega)
  have mD' : d₂.nmem (MD + 1 + 1 + 1 + 1) = C.topIdx := by rw [m₂]; exact mD
  have mE' : d₂.nmem (MD + 1 + 1 + 1 + 1 + 1) = m₀ (MD + 1 + 4) := by
    rw [m₂, mm _ (by omega)]
  obtain ⟨d₃, k₃, e₃, hk₃, o24, o25, o29, o32, o31, r₃, m₃⟩ := cHead2_exec (P := P) d₂ e₂.wb_right
    o75 (by rw [r₂ _ (by omega) (by omega) (by omega) (by omega), c91])
    (by rw [r₂ _ (by omega) (by omega) (by omega) (by omega), c96]) o23 mD' mE' (by omega)
    (by omega)
  have g₃ : ∀ x, x < 150021 ∨ x = 150026 ∨ x = 150028 ∨ x = 150030 ∨ 150037 ≤ x →
      x ≠ 150075 → d₃.nreg x = d₁.nreg x := fun x hx h75 => by
    rw [r₃ x (by omega) (by omega) (by omega) (by omega) (by omega) h75,
      r₂ x (by omega) (by omega) (by omega) h75]
  obtain ⟨d₄, k₄, e₄, hk₄, o27, o33, o36, o34, o35, r₄, m₄⟩ := cHead3_exec (P := P) d₃
    e₃.wb_right (m₀ := m₀) (by rw [g₃ _ (by omega) (by omega), a13])
    (by rw [g₃ _ (by omega) (by omega), c91]) (by rw [g₃ _ (by omega) (by omega), c92])
    (by rw [g₃ _ (by omega) (by omega), c93]) (by rw [m₃, m₂]; exact mh)
    (by rw [m₃, m₂]; exact mh1) (by rw [m₃, m₂]; exact mh2) (by rw [m₃, m₂]; exact mh3)
    (by omega) (by omega) (by omega)
  have w₄ := e₄.wb_right
  -- all the registers so far
  have f4 : ∀ x, (x < 150021 ∨ x = 150026 ∨ x = 150028 ∨ x = 150030 ∨ 150037 ≤ x) →
      x ≠ 150075 → x ≠ 150076 → x ≠ 150027 → x ≠ 150033 → x ≠ 150034 → x ≠ 150035 →
      x ≠ 150036 → d₄.nreg x = d₁.nreg x := fun x hx h1 h2 h3 h4 h5 h6 h7 => by
    rw [r₄ x h3 h4 h5 h6 h7 h1 h2, g₃ x hx h1]
  have b21 : d₄.nreg 150021 = Hh := by
    rw [r₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      r₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), o21]
  have b22 : d₄.nreg 150022 = C.s := by
    rw [r₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      r₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), o22]
  have b23 : d₄.nreg 150023 = C.m := by
    rw [r₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      r₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), o23]
  have b24 : d₄.nreg 150024 = C.topIdx := by
    rw [r₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), o24]
  have b25 : d₄.nreg 150025 = m₀ (MD + 1 + 4) := by
    rw [r₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), o25]
  have b29 : d₄.nreg 150029 = 2 * C.m := by
    rw [r₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), o29]
  have b31 : d₄.nreg 150031 = 2 * C.m + 5 := by
    rw [r₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), o31]
  have b32 : d₄.nreg 150032 = 2 * C.m + 6 := by
    rw [r₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), o32]
  have b91 : d₄.nreg 150091 = 1 := by
    rw [f4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), c91]
  -- the tour start
  obtain ⟨d₅, k₅, e₅, hk₅, o28, r₅⟩ : ∃ d₅ k₅, Exec P W cS d₄ d₅ k₅ ∧ k₅ ≤ 5 ∧
      d₅.nreg 150028 = C.sideS C.sideBeta ∧ (∀ x, x ≠ 150028 → d₅.nreg x = d₄.nreg x) := by
    unfold cS Chazelle.Chain.sideS
    by_cases hb1 : d₄.nreg 150025 < d₄.nreg 150091
    · have hβ : C.sideBeta = false := by
        rw [b25, b91] at hb1
        cases hβ : C.sideBeta
        · rfl
        · have := hb'.2 hβ; rwo [show MD + 1 + 4 = MD + 1 + 4 from rfl] at hb1
      refine spec_ifLtN_true hb1 (spec_instr (Exec.subN w₄ _ _ _) fun _ => ⟨by omega, ?_,
        fun x hx => by simp [hx]⟩)
      config_simp; rws [b29, b24, hβ]
    · by_cases hb2 : d₄.nreg 150091 < d₄.nreg 150025
      · have hβ : C.sideBeta = false := by
          rw [b25, b91] at hb2
          cases hβ : C.sideBeta
          · rfl
          · have := hb'.2 hβ; omega
        refine spec_ifLtN_false hb1 (spec_ifLtN_true hb2 (spec_instr (Exec.subN w₄ _ _ _)
          fun _ => ⟨by omega, ?_, fun x hx => by simp [hx]⟩))
        config_simp; rws [b29, b24, hβ]
      · have hβ : C.sideBeta = true := by
          rw [b25, b91] at hb1 hb2
          exact hb'.1 (by omega)
        refine spec_ifLtN_false hb1 (spec_ifLtN_false hb2 (spec_instr (Exec.copyN w₄ _ _)
          fun _ => ⟨by omega, ?_, fun x hx => by simp [hx]⟩))
        config_simp; rws [b24, hβ]
  have w₅ := e₅.wb_right
  -- the number of host points
  have e₆ := Exec.copyN (P := P) w₅ 50060 150021
  set d₆ := ({ d₅ with nreg := upd d₅.nreg 50060 (d₅.nreg 150021) } : Config) with hd₆
  have m₆ : d₆.nmem = d.nmem := by
    rw [(exec_frameB e₅ (B := Bl [150028]) (by decide)).2.2.1, m₄, m₃, m₂, m₁]
  have hH₆ : HostAt d₆.nmem Hh H := by
    rw [m₆, ← hHh]; exact hostAt_agree' (hHh ▸ S.hH) (by rw [hHh]; exact S.hHA)
      (hm)
  obtain ⟨d₇, k₇, e₇, hk₇, fr₇, o63, -⟩ := NFLoc.cnt_exec (P := P) (n := P.n) d₆ e₆.wb_right hH₆
    (by simp [hd₆, upd]; rw [r₅ _ (by omega), b21]) (by have := S.hHA; omega) (by omega)
  have e₈ := Exec.copyN (P := P) e₇.wb_right 150026 50063
  set d₈ := ({ d₇ with nreg := upd d₇.nreg 150026 (d₇.nreg 50063) } : Config) with hd₈
  have g₈ : ∀ x, 150000 ≤ x → x ≠ 150026 → d₈.nreg x = d₅.nreg x := fun x hx h26 => by
    simp only [hd₈, upd]
    rw [ite_eq_right h26, fr₇.1 _ (by ufs Bhost; omega)]
    simp only [hd₆, upd]; rw [ite_eq_right (by omega)]
  have ex : Exec P W cPre d d₈ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (1 + (k₇ + 1))))))) := by
    unfold cPre cCount
    exact .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈))))))
  have gg : ∀ x, 150000 ≤ x → (x < 150021 ∨ x = 150030 ∨ 150037 ≤ x) → x ≠ 150075 →
      x ≠ 150076 → x ≠ 150033 → x ≠ 150034 → x ≠ 150035 → x ≠ 150036 → x ≠ 150027 →
      d₈.nreg x = d₁.nreg x := fun x h0 hx h1 h2 h3 h4 h5 h6 h7 => by
    rw [g₈ x h0 (by omega), r₅ x (by omega), f4 x (by omega) h1 h2 h7 h3 h4 h5 h6]
  refine ⟨d₈, _, ex, by have := S.hlen; omega, ?_, exec_frameB ex (by decide)⟩
  have k5 : ∀ x, 150000 ≤ x → x ≠ 150026 → x ≠ 150028 → d₈.nreg x = d₄.nreg x :=
    fun x h0 h1 h2 => by rw [g₈ x h0 h1, r₅ x h2]
  refine ⟨⟨by rw [k5 _ (by omega) (by omega) (by omega), b21],
      by rw [k5 _ (by omega) (by omega) (by omega), b22],
      by rw [k5 _ (by omega) (by omega) (by omega), b23],
      by simp only [hd₈, upd, ↓reduceIte]; rw [o63],
      by rw [g₈ _ (by omega) (by omega), o28],
      by rw [k5 _ (by omega) (by omega) (by omega), b29],
      by rw [k5 _ (by omega) (by omega) (by omega), b91],
      by rw [gg _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), c93],
      by rw [gg _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), c96]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [k5 _ (by omega) (by omega) (by omega), o27],
    by rw [k5 _ (by omega) (by omega) (by omega), b31],
    by rw [k5 _ (by omega) (by omega) (by omega), b32],
    by rw [k5 _ (by omega) (by omega) (by omega), o33],
    by rw [k5 _ (by omega) (by omega) (by omega), o34],
    by rw [k5 _ (by omega) (by omega) (by omega), o35],
    by rw [k5 _ (by omega) (by omega) (by omega), o36], ?_, ?_⟩
  all_goals first
    | (rw [gg _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), g₁ _ (by omega)]; assumption)
    | (rw [gg _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]; assumption)
    | skip

/-- The cost bound of the core. -/
def coreCost (K γ : ℕ) : ℕ := genCost K γ + K + 20000

/-- **The core.** -/
theorem core_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ (PcOK P C m₀ h γ) I K)
    {ps₀ : List Pc} {MD mode : ℕ} {s e : WPos}
    (hD : ChainDescAt m₀ (MD + 1) (Qof P) H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ (MD + 1) = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (h00 : d.nreg 150000 = MD) (h01 : d.nreg 150001 = s.edge) (h02 : d.nreg 150002 = s.hgt)
    (h03 : d.nreg 150003 = e.edge) (h04 : d.nreg 150004 = e.hgt) (h09 : d.nreg 150009 = γ)
    (h13 : d.nreg 150013 = h) (h20 : d.nreg 150020 = mode) (hI : I ps₀ d)
    (hs : ProperPos (chainModel C) (Qof P) P.n s) (he : ProperPos (chainModel C) (Qof P) P.n e)
    (hs1 : s.edge < 2 * C.m + 7) (he1 : e.edge < 2 * C.m + 7)
    (hin : e.hgt = 0 ∨ (chainModel C).InnerPt ((chainModel C).pos (Qof P) e))
    (hwt : (chainModel C).arcWt ((chainModel C).key (Qof P) s) ((chainModel C).key (Qof P) e) ≤ γ) :
    ∃ d' k ps, Exec P W (core emit) d d' k ∧ k ≤ coreCost K γ ∧ I (ps₀ ++ ps) d' ∧
      ArcOK C (Qof P) s e ps ∧ (∀ pc ∈ ps, PcOK P C m₀ h γ pc) ∧
      ps.length ≤ 2100 * (Nat.log 2 γ + 1) ∧ (∀ a, a < A₀ → d'.nmem a = m₀ a) := by
  have hWn := S.hW
  unfold hostWords at hWn
  have hlen := S.hlen
  obtain ⟨d₁, k₁, e₁, hk₁, R₁, fr₁⟩ := cPre_exec S hD hMD hHh d hw hm h00 h01 h02 h03 h04 h09
    h13 h20
  have hm₁ : ∀ a, a < A₀ → d₁.nmem a = m₀ a := fun a ha => by rw [fr₁.2.2.1]; exact hm a ha
  obtain ⟨d₂, k₂, e₂, hk₂, fr₂, i48, l48⟩ := decideS_exec S hD hMD hHh d₁ e₁.wb_right hm₁ R₁ hs he
    hs1 hin
  have hBd : ∀ r, 150000 ≤ r → r < 150044 → Bd r = false := fun r h1 h2 => by
    ufs Bd; omega
  have hBd' : ∀ r, 150090 ≤ r → r < 150100 → Bd r = false := fun r h1 h2 => by
    ufs Bd; omega
  have R₂  := R₁.of_frame'
    (fun r h1 h2 _ _ => fr₂.1 r (hBd r h1 h2))
    (by rw [fr₂.1 _ (hBd' _ (by omega) (by omega))]; exact R₁.h90)
    (by rw [fr₂.1 _ (hBd' _ (by omega) (by omega))]; exact R₁.chain.h91)
    (by rw [fr₂.1 _ (hBd' _ (by omega) (by omega))]; exact R₁.h92)
    (by rw [fr₂.1 _ (hBd' _ (by omega) (by omega))]; exact R₁.chain.h93)
    (by rw [fr₂.1 _ (hBd' _ (by omega) (by omega))]; exact R₁.chain.h96)
  have hm₂ : ∀ a, a < A₀ → d₂.nmem a = m₀ a := fun a ha => by rw [fr₂.2.2.1]; exact hm₁ a ha
  have hI₂ := hE.stable _ _ _ hI (fr₁.trans (FrameB.mono' fr₂ fun r hr => by
    unfold Scr at hr; unfold Bd; sio at hr ⊢))
  have w₂ := e₂.wb_right
  have hpre : ∀ {d' : Config} {k : ℕ}, Exec P W (.ifLtN 150090 150048 (.seq pcSE emit)
      (general emit)) d₂ d' k → Exec P W (core emit) d d' (k₁ + (k₂ + k)) := fun ex => by
    unfold core; exact .seq e₁ (.seq e₂ ex)
  have hGc : 2 * K + 90 ≤ (2 * K + 90) * (Nat.log 2 γ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  by_cases hsame : d₂.nreg 150090 < d₂.nreg 150048
  · -- the single piece `[s, e]`
    have hG : s.edge = e.edge ∧ (chainModel C).key (Qof P) s < (chainModel C).key (Qof P) e :=
      i48.1 (by rwo [R₂.h90] at hsame)
    have hpv : PcOK P C m₀ h γ (pSE s e) := pSE_ok hs he hs1 he1
      (wt_same _ _ hs he hG.1 hG.2)
    obtain ⟨d₃, k₃, e₃, hk₃, hR₃, fr₃, -⟩ := pcSE_exec (P := P) d₂ w₂ (by omega) R₂.h01 R₂.h02
      R₂.h03 R₂.h04
    obtain ⟨d₄, k₄, e₄, hk₄, hI₄, -, mem₄⟩ := hE.run _ _ d₃ e₃.wb_right (hE.stable _ _ _ hI₂ fr₃) hR₃ hpv
    refine ⟨d₄, _, [pSE s e], hpre (.ifLtN_true hsame (.seq e₃ e₄)), ?_, hI₄,
      arcOK_single hs he hs1 he1 rfl rfl, by simpa using hpv, by sio,
      fun a ha => by rw [mem₄ a ha, fr₃.2.2.1]; exact hm₂ a ha⟩
    ufo coreCost genCost
  · have hns : ¬ (s.edge = e.edge ∧
        (chainModel C).key (Qof P) s < (chainModel C).key (Qof P) e) := fun hG => by
      have := i48.2 hG; rwo [R₂.h90] at hsame
    obtain ⟨d₃, k₃, ps, e₃, hk₃, hI₃, arc, hok, hl, hm₃⟩ := general_exec S hE hD hMD hHh d₂ w₂
      R₂ hm₂ hI₂ hs he hs1 he1 hns hwt
    refine ⟨d₃, _, ps, hpre (.ifLtN_false hsame e₃), ?_, hI₃, arc, hok, hl, hm₃⟩
    ufo coreCost

end

end ShootCut

end Chazelle.Core
