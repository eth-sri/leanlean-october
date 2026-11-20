module

public import Chazelle.Core.ShootCutBox

/-!
# WP-G, part 27: the decision `SAME`

`decideS_exec`: `150048` is `1` iff the subarc lies inside the edge of its start (the ends are
on one walk edge and the start comes first); then the core hands the single piece `[s, e]`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

/-- The registers the decision writes: `150044 … 150089` of band `bCut` and the kernel bands. -/
def Bd (r : ℕ) : Bool :=
  decide (150044 ≤ r ∧ r < 150090) || decide (10000 ≤ r ∧ r < 20000) ||
    decide (50000 ≤ r ∧ r < 60000)

theorem wr_decideS : wr Bd decideS = true := by decide

theorem FrameB.mono' {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B' r = false → B r = false) : FrameB B' c c' :=
  ⟨fun r hr => h.1 r (hB r hr), fun r hr => h.2.1 r (hB r hr), h.2.2⟩

variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}

/-- **The box edges.** -/
theorem decBox_exec {P : Polygon} {W : ℕ} (d : Config) (hw : WordsBounded W d) {p : ℕ}
    (h01 : d.nreg 150001 = p) (hp : p < 6) (h48 : d.nreg 150048 = 0) (h91 : d.nreg 150091 = 1)
    (h92 : d.nreg 150092 = 2) (h93 : d.nreg 150093 = 3) (hW : 1 ≤ W) :
    ∃ d' k, Exec P W decBox d d' k ∧ k ≤ 12 ∧ (d'.nreg 150048 = 1 ↔ (p = 1 ∨ p = 3 ∨ p = 5)) ∧
      d'.nreg 150048 ≤ 1 ∧ (∀ x, x ≠ 150048 → x ≠ 150075 → d'.nreg x = d.nreg x) ∧
      d'.nmem = d.nmem := by
  unfold decBox
  interval_cases p
  · refine spec_ifLtN_true (by rw [h01, h91]; omega) (spec_skip hw ⟨by omega, ?_, by omega,
      fun _ _ _ => rfl, rfl⟩)
    rw [h48]; simp
  · refine spec_ifLtN_false (by rw [h01, h91]; omega) (spec_ifLtN_true (by rw [h01, h92]; omega)
      (spec_instr (Exec.constN hw _ _ hW) fun _ => ⟨by omega, by simp, by simp,
        fun x h1 _ => by simp [h1], rfl⟩))
  · refine spec_ifLtN_false (by rw [h01, h91]; omega) (spec_ifLtN_false (by rw [h01, h92]; omega)
      (spec_ifLtN_true (by rw [h01, h93]; omega) (spec_skip hw ⟨by omega, ?_, by omega,
        fun _ _ _ => rfl, rfl⟩)))
    rw [h48]; simp
  · refine spec_ifLtN_false (by rw [h01, h91]; omega) (spec_ifLtN_false (by rw [h01, h92]; omega)
      (spec_ifLtN_false (by rw [h01, h93]; omega) (spec_seq (spec_instr (Exec.subN hw _ _ _)
        fun w₁ => spec_ifLtN_true (by config_simp; rw [h01, h93, h91]; omega) (spec_instr
          (Exec.constN w₁ _ _ hW) fun _ => ⟨by omega, by simp, by simp,
            fun x h1 h2 => by simp [h1, h2], rfl⟩)))))
  · refine spec_ifLtN_false (by rw [h01, h91]; omega) (spec_ifLtN_false (by rw [h01, h92]; omega)
      (spec_ifLtN_false (by rw [h01, h93]; omega) (spec_seq (spec_instr (Exec.subN hw _ _ _)
        fun w₁ => spec_ifLtN_false (by config_simp; rw [h01, h93, h91]; omega)
          (spec_ifLtN_true (by config_simp; rw [h01, h93, h92]; omega) (spec_skip w₁
            ⟨by omega, ?_, ?_, fun x h1 h2 => by simp [h2], rfl⟩))))))
    · config_simp; rw [h48]; simp
    · config_simp; rw [h48]; omega
  · refine spec_ifLtN_false (by rw [h01, h91]; omega) (spec_ifLtN_false (by rw [h01, h92]; omega)
      (spec_ifLtN_false (by rw [h01, h93]; omega) (spec_seq (spec_instr (Exec.subN hw _ _ _)
        fun w₁ => spec_ifLtN_false (by config_simp; rw [h01, h93, h91]; omega)
          (spec_ifLtN_false (by config_simp; rw [h01, h93, h92]; omega) (spec_instr
            (Exec.constN w₁ _ _ hW) fun _ => ⟨by omega, by simp, by simp,
              fun x h1 h2 => by simp [h1, h2], rfl⟩))))))

/-- **The start at a vertex**: is the parameter of the end `⟨p, hh⟩` positive? -/
theorem decVtx_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD : ℕ}
    (hD : ChainDescAt m₀ (MD + 1) (Qof P) H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ (MD + 1) = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (R : ChainRegs C (H.pts P.n).length Hh d) (h00 : d.nreg 150000 = MD)
    (h27 : d.nreg 150027 = P.n) (h48 : d.nreg 150048 = 0) (h90 : d.nreg 150090 = 0)
    (h92 : d.nreg 150092 = 2) {p hh : ℕ} (h01 : d.nreg 150001 = p) (h04 : d.nreg 150004 = hh)
    (hp : p < 2 * C.m + 7) (hh1 : 1 ≤ hh) (hhn : hh ≤ P.n)
    (hx : ProperPos (chainModel C) (Qof P) P.n ⟨p, hh⟩)
    (hin : (chainModel C).InnerPt ((chainModel C).pos (Qof P) ⟨p, hh⟩)) :
    ∃ d' k, Exec P W decVtx d d' k ∧ k ≤ 100 * H.length + 2050 ∧
      (d'.nreg 150048 = 1 ↔ 0 < (chainModel C).param (Qof P) ⟨p, hh⟩) ∧ d'.nreg 150048 ≤ 1 := by
  have hWn := S.hW
  unfold hostWords at hWn
  obtain ⟨j, rfl⟩ : ∃ j, hh = j + 1 := ⟨hh - 1, by omega⟩
  unfold decVtx
  by_cases hp6 : p < 6
  · obtain ⟨d', k, ex, hk, h1, h2, -, -⟩ := decBox_exec (P := P) d hw h01 hp6 h48 R.h91 h92 R.h93
      (by omega)
    refine ⟨d', _, .ifLtN_true (by rw [h01, R.h96]; exact hp6) ex, by omega, ?_, h2⟩
    rw [h1]
    constructor
    · intro hb; exact box_param_pos C (Qof P) hb hx hin
    · intro hpos
      by_contra hb
      have hb' : p = 0 ∨ p = 2 ∨ p = 4 := by omega
      rw [param_succ, ite_eq_left (box_horizontal C hb')] at hpos
      exact lt_irrefl 0 hpos
  · obtain ⟨d₁, k₁, e₁, hk₁, o49, o76, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W
        (block [.copyN 150049 150001, .subN 150076 150004 150091]) d d₁ k₁ ∧ k₁ = 2 ∧
        d₁.nreg 150049 = p ∧ d₁.nreg 150076 = j ∧
        (∀ x, x ≠ 150049 → x ≠ 150076 → d₁.nreg x = d.nreg x) ∧ d₁.nmem = d.nmem := by
      exec_block
      refine ⟨rfl, by config_simp; exact h01, by config_simp; rw [h04, R.h91]; omega,
        fun x h1 h2 => ?_, rfl⟩
      simp only [upd]; split_ifs <;> first | rfl | omega
    have R₁ : ChainRegs C (H.pts P.n).length Hh d₁ := R.of_frame fun r hr => r₁ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega)
    obtain ⟨d₂, k₂, e₂, hk₂, fr₂, i₂, l₂⟩ := posP_exec S hD hMD hHh d₁ e₁.wb_right
      (fun a ha => by rw [m₁]; exact hm a ha) R₁ (by rw [r₁ _ (by omega) (by omega), h00])
      (by rw [r₁ _ (by omega) (by omega), h27]) (by rw [r₁ _ (by omega) (by omega), h90])
      (by rw [r₁ _ (by omega) (by omega), h92]) o49 o76 (by omega) (by omega) (by omega)
    have e₃ := Exec.copyN (P := P) e₂.wb_right 150048 150089
    refine ⟨_, _, .ifLtN_false
      (show ¬ d.nreg 150001 < d.nreg 150096 by rw [h01, R.h96]; exact hp6)
      (.seq e₁ (.seq e₂ e₃)), by omega, ?_, ?_⟩
    · config_simp
      exact i₂.trans (param_pos_iff _ _ hx).symm
    · config_simp; exact l₂

/-- **Both ends on one edge**, the end not at its start vertex: are they in key order? -/
theorem decSame_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD : ℕ}
    (hD : ChainDescAt m₀ (MD + 1) (Qof P) H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ (MD + 1) = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (R : ChainRegs C (H.pts P.n).length Hh d) (h00 : d.nreg 150000 = MD)
    (h27 : d.nreg 150027 = P.n) (h48 : d.nreg 150048 = 0) (h90 : d.nreg 150090 = 0)
    (h92 : d.nreg 150092 = 2) {p h₁ h₂ : ℕ} (h01 : d.nreg 150001 = p)
    (h02 : d.nreg 150002 = h₁) (h04 : d.nreg 150004 = h₂)
    (hp : p < 2 * C.m + 7) (hh₂ : 1 ≤ h₂) (hh₁n : h₁ ≤ P.n) (hh₂n : h₂ ≤ P.n)
    (he : ProperPos (chainModel C) (Qof P) P.n ⟨p, h₂⟩)
    (hin : (chainModel C).InnerPt ((chainModel C).pos (Qof P) ⟨p, h₂⟩)) :
    ∃ d' k, Exec P W decSame d d' k ∧ k ≤ 100 * H.length + 2100 ∧
      (d'.nreg 150048 = 1 ↔
        (chainModel C).key (Qof P) ⟨p, h₁⟩ < (chainModel C).key (Qof P) ⟨p, h₂⟩) ∧
      d'.nreg 150048 ≤ 1 := by
  have hWn := S.hW
  unfold hostWords at hWn
  unfold decSame
  by_cases h0 : d.nreg 150002 < d.nreg 150091
  · have hz : h₁ = 0 := by rw [h02, R.h91] at h0; omega
    subst hz
    obtain ⟨d', k, ex, hk, h1, h2⟩ := decVtx_exec S hD hMD hHh d hw hm R h00 h27 h48 h90 h92
      h01 h04 hp hh₂ hh₂n he hin
    refine ⟨d', _, .ifLtN_true h0 ex, by omega, ?_, h2⟩
    rw [h1, key_hgt0]
    unfold Model.key
    constructor <;> intro h <;> linarith
  · have hh₁ : 1 ≤ h₁ := by rw [h02, R.h91] at h0; omega
    have e₁ := Exec.copyN (P := P) hw 150049 150001
    set d₁ := ({ d with nreg := upd d.nreg 150049 (d.nreg 150001) } : Config) with hd₁
    have g₁ : ∀ x, x ≠ 150049 → d₁.nreg x = d.nreg x := fun x hx => by simp [hd₁, upd, hx]
    obtain ⟨d₂, k₂, e₂, hk₂, fr₂, i₂, l₂⟩ := keyLess_exec S hD hMD hHh d₁ e₁.wb_right
      (fun a ha => hm a ha) (by rw [g₁ _ (by omega), h00]) (by rw [g₁ _ (by omega), R.h91])
      (by simp [hd₁, upd, h01]) (by rw [g₁ _ (by omega), h02]) (by rw [g₁ _ (by omega), h04])
      hp hh₁ hh₁n hh₂ hh₂n
    have e₃ := Exec.copyN (P := P) e₂.wb_right 150048 150089
    refine ⟨_, _, .ifLtN_false h0 (.seq e₁ (.seq e₂ e₃)), by omega, ?_, ?_⟩
    · config_simp
      exact i₂.trans (key_lt_iff _ _ hh₁ hh₂).symm
    · config_simp; exact l₂

/-- **The decision `SAME`.** -/
theorem decideS_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {MD mode : ℕ} {s e : WPos}
    (hD : ChainDescAt m₀ (MD + 1) (Qof P) H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ (MD + 1) = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (R : CoreRegs P C H Hh MD h γ mode s e m₀ d)
    (hs : ProperPos (chainModel C) (Qof P) P.n s) (he : ProperPos (chainModel C) (Qof P) P.n e)
    (hs1 : s.edge < 2 * C.m + 7)
    (hin : e.hgt = 0 ∨ (chainModel C).InnerPt ((chainModel C).pos (Qof P) e)) :
    ∃ d' k, Exec P W decideS d d' k ∧ k ≤ 100 * H.length + 2110 ∧ FrameB Bd d d' ∧
      (d'.nreg 150048 = 1 ↔ (s.edge = e.edge ∧
        (chainModel C).key (Qof P) s < (chainModel C).key (Qof P) e)) ∧
      d'.nreg 150048 ≤ 1 := by
  have hWn := S.hW
  unfold hostWords at hWn
  suffices main : ∃ d' k, Exec P W decideS d d' k ∧ k ≤ 100 * H.length + 2110 ∧
      (d'.nreg 150048 = 1 ↔ (s.edge = e.edge ∧
        (chainModel C).key (Qof P) s < (chainModel C).key (Qof P) e)) ∧
      d'.nreg 150048 ≤ 1 by
    obtain ⟨d', k, ex, hk, h1, h2⟩ := main
    exact ⟨d', k, ex, hk, exec_frameB ex wr_decideS, h1, h2⟩
  have e₀ := Exec.constN (P := P) hw 150048 0 (by omega)
  set d₀ := ({ d with nreg := upd d.nreg 150048 0 } : Config) with hd₀
  have g₀ : ∀ x, x ≠ 150048 → d₀.nreg x = d.nreg x := fun x hx => by simp [hd₀, upd, hx]
  have w₀ := e₀.wb_right
  have z₀ : d₀.nreg 150048 = 0 := by simp [hd₀]
  have r01 : d₀.nreg 150001 = s.edge := by rw [g₀ _ (by omega), R.h01]
  have r02 : d₀.nreg 150002 = s.hgt := by rw [g₀ _ (by omega), R.h02]
  have r03 : d₀.nreg 150003 = e.edge := by rw [g₀ _ (by omega), R.h03]
  have r04 : d₀.nreg 150004 = e.hgt := by rw [g₀ _ (by omega), R.h04]
  have r90 : d₀.nreg 150090 = 0 := by rw [g₀ _ (by omega), R.h90]
  have hks := key_bounds hs
  have hke := key_bounds he
  have zero : ∀ (d' : Config) (k : ℕ), Exec P W decideS d d' k → k ≤ 100 * H.length + 2110 →
      d'.nreg 150048 = 0 → ¬ (s.edge = e.edge ∧
        (chainModel C).key (Qof P) s < (chainModel C).key (Qof P) e) →
      ∃ d' k, Exec P W decideS d d' k ∧ k ≤ 100 * H.length + 2110 ∧
        (d'.nreg 150048 = 1 ↔ (s.edge = e.edge ∧
          (chainModel C).key (Qof P) s < (chainModel C).key (Qof P) e)) ∧
        d'.nreg 150048 ≤ 1 :=
    fun d' k ex hk hz hng => ⟨d', k, ex, hk, by rw [hz]; simp only [zero_ne_one, false_iff]; exact hng,
      by omega⟩
  by_cases hlt : d₀.nreg 150001 < d₀.nreg 150003
  · refine zero d₀ _ (by unfold decideS; exact .seq e₀ (.ifLtN_true hlt (.skip w₀))) (by omega)
      z₀ ?_
    rw [r01, r03] at hlt; rintro ⟨h1, -⟩; omega
  by_cases hgt : d₀.nreg 150003 < d₀.nreg 150001
  · refine zero d₀ _ (by unfold decideS; exact .seq e₀ (.ifLtN_false hlt (.ifLtN_true hgt
      (.skip w₀)))) (by omega) z₀ ?_
    rw [r01, r03] at hgt; rintro ⟨h1, -⟩; omega
  have heq : s.edge = e.edge := by rw [r01, r03] at hlt hgt; omega
  by_cases h4 : d₀.nreg 150090 < d₀.nreg 150004
  · have hh₂ : 1 ≤ e.hgt := by rw [r90, r04] at h4; omega
    have hin' : (chainModel C).InnerPt ((chainModel C).pos (Qof P) e) := by
      rcases hin with h | h
      · omega
      · exact h
    have hs' : s = ⟨s.edge, s.hgt⟩ := rfl
    have he' : e = ⟨s.edge, e.hgt⟩ := by rw [heq]
    obtain ⟨d', k, ex, hk, h1, h2⟩ := decSame_exec S hD hMD hHh d₀ w₀ (fun a ha => hm a ha)
      (R.chain.of_frame fun r hr => g₀ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; omega))
      (by rw [g₀ _ (by omega), R.h00]) (by rw [g₀ _ (by omega), R.h27]) z₀ r90
      (by rw [g₀ _ (by omega), R.h92]) r01 r02 r04 hs1 hh₂ hs.2.2 he.2.2
      (by rw [← he']; exact he) (by rw [← he']; exact hin')
    refine ⟨d', _, by unfold decideS; exact .seq e₀ (.ifLtN_false hlt (.ifLtN_false hgt
      (.ifLtN_true h4 ex))), by omega, ?_, h2⟩
    rw [h1, ← hs', ← he']
    exact ⟨fun h => ⟨heq, h⟩, fun h => h.2⟩
  · refine zero d₀ _ (by unfold decideS; exact .seq e₀ (.ifLtN_false hlt (.ifLtN_false hgt
      (.ifLtN_false h4 (.skip w₀))))) (by omega) z₀ ?_
    rw [r90, r04] at h4
    have he0 : e.hgt = 0 := by omega
    rintro ⟨-, h⟩
    have : (chainModel C).key (Qof P) e = e.edge := by
      rw [show e = ⟨e.edge, 0⟩ by rw [← he0]]; exact key_hgt0 _ _ _
    rw [this, ← heq] at h
    linarith [hks.1]

end

end ShootCut

end Chazelle.Core
