module

public import Chazelle.Core.ShootCutArc
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics

/-!
# WP-G, part 32: the general case on the RAM

`general_exec`: the flags of the uncounted block, the final vertex `f` (`41`), the first piece,
then (unless the first piece is the whole subarc) the main loop and the last piece.  The pieces
tile the subarc (`ArcOK`), are valid, and there are `O(log γ)` of them.
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc
open Chazelle.Chain (sideInArc)

@[expose] public section

variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}

theorem CoreRegs.of_low {MD mode : ℕ} {s e : WPos} {c c' : Config}
    (R : CoreRegs P C H Hh MD h γ mode s e m₀ c)
    (hk : ∀ r, 150000 ≤ r → r < 150037 → r ≠ 150030 → c'.nreg r = c.nreg r)
    (h90 : c'.nreg 150090 = 0) (h91 : c'.nreg 150091 = 1) (h92 : c'.nreg 150092 = 2)
    (h93 : c'.nreg 150093 = 3) (h96 : c'.nreg 150096 = 6) :
    CoreRegs P C H Hh MD h γ mode s e m₀ c' := by
  have k : ∀ r, 150000 ≤ r → r < 150030 ∨ (150030 < r ∧ r < 150037) →
      c'.nreg r = c.nreg r := fun r h1 h2 => hk r h1 (by omega) (by omega)
  exact ⟨⟨(k _ (by norm_num) (by norm_num)).trans R.chain.h21,
      (k _ (by norm_num) (by norm_num)).trans R.chain.h22,
      (k _ (by norm_num) (by norm_num)).trans R.chain.h23,
      (k _ (by norm_num) (by norm_num)).trans R.chain.h26,
      (k _ (by norm_num) (by norm_num)).trans R.chain.h28,
      (k _ (by norm_num) (by norm_num)).trans R.chain.h29, h91, h93, h96⟩,
    (k _ (by norm_num) (by norm_num)).trans R.h00, (k _ (by norm_num) (by norm_num)).trans R.h01,
    (k _ (by norm_num) (by norm_num)).trans R.h02, (k _ (by norm_num) (by norm_num)).trans R.h03,
    (k _ (by norm_num) (by norm_num)).trans R.h04, (k _ (by norm_num) (by norm_num)).trans R.h09,
    (k _ (by norm_num) (by norm_num)).trans R.h13, (k _ (by norm_num) (by norm_num)).trans R.h20,
    (k _ (by norm_num) (by norm_num)).trans R.h27, (k _ (by norm_num) (by norm_num)).trans R.h31,
    (k _ (by norm_num) (by norm_num)).trans R.h32, (k _ (by norm_num) (by norm_num)).trans R.h33,
    (k _ (by norm_num) (by norm_num)).trans R.h34, (k _ (by norm_num) (by norm_num)).trans R.h35,
    (k _ (by norm_num) (by norm_num)).trans R.h36, h90, h92⟩

/-- The cost bound of the general case. -/
def genCost (K γ : ℕ) : ℕ := 1100 * ((2 * K + 90) * (Nat.log 2 γ + 1) + 1702) + 2 * K + 20000

/-- **The general case.** -/
theorem general_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ (PcOK P C m₀ h γ) I K)
    {ps₀ : List Pc} {MD mode : ℕ} {s e : WPos}
    (hD : ChainDescAt m₀ (MD + 1) (Qof P) H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ (MD + 1) = Hh)
    (d : Config) (hw : WordsBounded W d) (R : CoreRegs P C H Hh MD h γ mode s e m₀ d)
    (hm : ∀ a, a < A₀ → d.nmem a = m₀ a) (hI : I ps₀ d)
    (hs : ProperPos (chainModel C) (Qof P) P.n s) (he : ProperPos (chainModel C) (Qof P) P.n e)
    (hs1 : s.edge < 2 * C.m + 7) (he1 : e.edge < 2 * C.m + 7)
    (hsame : ¬ (s.edge = e.edge ∧ (chainModel C).key (Qof P) s < (chainModel C).key (Qof P) e))
    (hwt : (chainModel C).arcWt ((chainModel C).key (Qof P) s) ((chainModel C).key (Qof P) e) ≤ γ) :
    ∃ d' k ps, Exec P W (general emit) d d' k ∧ k ≤ genCost K γ ∧ I (ps₀ ++ ps) d' ∧
      ArcOK C (Qof P) s e ps ∧ (∀ pc ∈ ps, PcOK P C m₀ h γ pc) ∧
      ps.length ≤ 2100 * (Nat.log 2 γ + 1) ∧ (∀ a, a < A₀ → d'.nmem a = m₀ a) := by
  have hWn := S.hW
  unfold hostWords at hWn
  have hm2 := S.hm2'
  have hm1 := C.one_le
  set n := 2 * C.m + 7 with hn
  -- the flags of the uncounted block
  obtain ⟨d₁, k₁, e₁, hk₁, o38, o37, r₁, m₁⟩ := uFlag_exec (P := P) d hw 150001 150038 150037
    (by omega) (by omega) (by omega) R.h01 hs1 R.chain.h96 R.chain.h91 R.h32 (by omega)
  obtain ⟨d₂, k₂, e₂, hk₂, o39, o30, r₂, m₂⟩ := uFlag_exec (P := P) d₁ e₁.wb_right 150003 150039
    150030 (by omega) (by omega) (by omega) (by rw [r₁ _ (by omega) (by omega), R.h03]) he1
    (by rw [r₁ _ (by omega) (by omega), R.chain.h96])
    (by rw [r₁ _ (by omega) (by omega), R.chain.h91])
    (by rw [r₁ _ (by omega) (by omega), R.h32]) (by omega)
  have g₂ : ∀ x, x ≠ 150037 → x ≠ 150038 → x ≠ 150039 → x ≠ 150030 → d₂.nreg x = d.nreg x :=
    fun x h1 h2 h3 h4 => by rw [r₂ x h3 h4, r₁ x h2 h1]
  have w₂ := e₂.wb_right
  -- `41 := f`
  obtain ⟨d₃, k₃, e₃, hk₃, o41, r₃, m₃⟩ : ∃ d₃ k₃, Exec P W (.ifLtN 150090 150039
      (.instr (.copyN 150041 150031)) (.instr (.copyN 150041 150003))) d₂ d₃ k₃ ∧ k₃ ≤ 3 ∧
      d₃.nreg 150041 = fOf C.m e.edge ∧ (∀ x, x ≠ 150041 → d₃.nreg x = d₂.nreg x) ∧
      d₃.nmem = d₂.nmem := by
    unfold fOf
    have a90 : d₂.nreg 150090 = 0 := by
      rw [g₂ 150090 (by omega) (by omega) (by omega) (by omega), R.h90]
    have a31 : d₂.nreg 150031 = 2 * C.m + 5 := by
      rw [g₂ 150031 (by omega) (by omega) (by omega) (by omega), R.h31]
    have a03 : d₂.nreg 150003 = e.edge := by
      rw [g₂ 150003 (by omega) (by omega) (by omega) (by omega), R.h03]
    by_cases heU : e.edge ≤ 5 ∨ e.edge = 2 * C.m + 6
    · have c39 : d₂.nreg 150090 < d₂.nreg 150039 := by rwo [a90, o39, ite_eq_left heU]
      refine spec_ifLtN_true c39 (spec_instr (Exec.copyN w₂ _ _) fun _ => ⟨by omega, ?_,
          fun x hx => by simp [hx], rfl⟩)
      config_simp; rw [a31, ite_eq_left heU]
    · have c39 : ¬ d₂.nreg 150090 < d₂.nreg 150039 := by rwo [a90, o39, ite_eq_right heU]
      refine spec_ifLtN_false c39 (spec_instr (Exec.copyN w₂ _ _) fun _ => ⟨by omega, ?_,
          fun x hx => by simp [hx], rfl⟩)
      config_simp; rw [a03, ite_eq_right heU]
  -- `43 := 0`
  have e₄ := Exec.constN (P := P) e₃.wb_right 150043 0 (by omega)
  set d₄ := ({ d₃ with nreg := upd d₃.nreg 150043 0 } : Config) with hd₄
  have g₄ : ∀ x, x ≠ 150037 → x ≠ 150038 → x ≠ 150039 → x ≠ 150030 → x ≠ 150041 →
      x ≠ 150043 → d₄.nreg x = d.nreg x := fun x h1 h2 h3 h4 h5 h6 => by
    simp only [hd₄, upd]; rw [ite_eq_right h6, r₃ x h5, g₂ x h1 h2 h3 h4]
  have w₄ := e₄.wb_right
  have R₄  := R.of_low
    (fun r h1 h2 h3 => g₄ r (by omega) (by omega) (by omega) h3 (by omega) (by omega))
    (by rw [g₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), R.h90])
    (by rw [g₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), R.chain.h91])
    (by rw [g₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), R.h92])
    (by rw [g₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), R.chain.h93])
    (by rw [g₄ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), R.chain.h96])
  have hm₄ : ∀ a, a < A₀ → d₄.nmem a = m₀ a := fun a ha => by
    show d₃.nmem a = m₀ a; rw [m₃, m₂, m₁]; exact hm a ha
  have fr₄ : FrameB Scr d d₄ := ((exec_frameB e₁ (by decide)).trans
    (exec_frameB e₂ (by decide))).trans ((exec_frameB e₃ (by decide)).trans
      (exec_frameB e₄ (by decide)))
  have hI₄ := hE.stable _ _ _ hI fr₄
  have b38 : d₄.nreg 150038 = if s.edge ≤ 5 ∨ s.edge = 2 * C.m + 6 then 1 else 0 := by
    simp only [hd₄, upd]; rw [ite_eq_right (by omega), r₃ _ (by omega), r₂ _ (by omega) (by omega)]
    exact o38
  have b37 : d₄.nreg 150037 = uIx s.edge := by
    simp only [hd₄, upd]; rw [ite_eq_right (by omega), r₃ _ (by omega), r₂ _ (by omega) (by omega)]
    exact o37
  have b39 : d₄.nreg 150039 = if e.edge ≤ 5 ∨ e.edge = 2 * C.m + 6 then 1 else 0 := by
    simp only [hd₄, upd]; rwx [ite_eq_right (by omega), r₃ _ (by omega)]
  have b30 : d₄.nreg 150030 = uIx e.edge := by
    simp only [hd₄, upd]; rwx [ite_eq_right (by omega), r₃ _ (by omega)]
  have b41 : d₄.nreg 150041 = fOf C.m e.edge := by
    simp only [hd₄, upd]; rwx [ite_eq_right (by omega)]
  have b43 : d₄.nreg 150043 = 0 := by simp [hd₄]
  -- the first piece
  obtain ⟨d₅, k₅, p₁, ex₅, hk₅, hI₅, hp₁, hp₁s, hdone, hndone, kp₅, mem₅⟩ :=
    first_exec S hE (ps₀ := ps₀) d₄ w₄ R₄ b38 b37 b39 b30 hI₄ hs he hs1 he1
  have w₅ := ex₅.wb_right
  have R₅  := R₄.of_low
    (fun r h1 h2 h3 => kp₅ r (Or.inl ⟨h1, by omega⟩) (by omega) (by omega))
    (by rw [kp₅ _ (by ufo Keep) (by omega) (by omega), R₄.h90])
    (by rw [kp₅ _ (by ufo Keep) (by omega) (by omega), R₄.chain.h91])
    (by rw [kp₅ _ (by ufo Keep) (by omega) (by omega), R₄.h92])
    (by rw [kp₅ _ (by ufo Keep) (by omega) (by omega), R₄.chain.h93])
    (by rw [kp₅ _ (by ufo Keep) (by omega) (by omega), R₄.chain.h96])
  have hm₅ : ∀ a, a < A₀ → d₅.nmem a = m₀ a := fun a ha => by rw [mem₅ a ha]; exact hm₄ a ha
  have c91  := R₅.chain.h91
  have hpre : ∀ {d' : Config} {k : ℕ}, Exec P W (.ifLtN 150043 150091
      (.seq setFlag (.seq (mainLoop emit) (final emit))) .skip) d₅ d' k →
      Exec P W (general emit) d d' ((k₁ + k₂) + (k₃ + (1 + (k₅ + k)))) := fun ex => by
    unfold general; exact .seq (.seq e₁ e₂) (.seq e₃ (.seq e₄ (.seq ex₅ ex)))
  have hGc : 2 * K + 90 ≤ (2 * K + 90) * (Nat.log 2 γ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  by_cases hd43 : d₅.nreg 150043 < d₅.nreg 150091
  · -- the main loop and the last piece
    have hnd : ¬ Done C.m s.edge e.edge := fun hd => by rwo [(hdone hd).2, c91] at hd43
    obtain ⟨hp₁e, h40, h43⟩ := hndone hnd
    obtain ⟨U₀, F, hU₀, hksU, hF, hUF, hFU, hFT, hfin1, hfin2⟩ :=
      plan C (Qof P) hs he hs1 he1 hsame hnd
    set ks := (chainModel C).key (Qof P) s
    set ke := (chainModel C).key (Qof P) e
    have kS := key_range hs hs1
    have kE := key_range he he1
    have hTle : ks + len ((2 * C.m + 7 : ℕ) : ℝ) ks ke ≤ ks + ((2 * C.m + 7 : ℕ) : ℝ) := by
      have := len_le ((2 * C.m + 7 : ℕ) : ℝ) ks ke kS.1 kE.2; linarith
    -- the flag
    obtain ⟨d₆, k₆, e₆, hk₆, o42, r₆, m₆⟩ := setFlag_exec (P := P) d₅ w₅ (by omega)
    have w₆ := e₆.wb_right
    have a40 : d₆.nreg 150040 = U₀ % n := by rw [r₆ _ (by omega), h40, hU₀]
    have a41 : d₆.nreg 150041 = F % n := by
      rw [r₆ _ (by omega), kp₅ _ (by ufo Keep) (by omega) (by omega), b41, hF]
    have hc0 : 6 ≤ U₀ % n ∧ U₀ % n ≤ 2 * C.m + 6 := by
      rw [hU₀]; unfold c0Of; splao
    have hf : 6 ≤ F % n ∧ F % n ≤ 2 * C.m + 5 := by
      rw [hF]; unfold fOf; splao
    have hUof : Uof U₀ n (U₀ % n) = U₀ := Uof_eq (by omega) le_rfl (by omega)
    have L : LStat C U₀ F γ := ⟨hUF, hFU, hf.1, hf.2, fun v L hv hvF h6 hL => le_trans
      (arcWt_ge C kS kE ⟨0, by ring⟩ (T_unw ks ke _) hTle h6 hL
        (by have : (U₀ : ℝ) ≤ v := by exact_mod_cast hv
            linarith)
        (by have : ((v + L : ℕ) : ℝ) ≤ F := by exact_mod_cast hvF
            push_cast at this; linarith)) hwt⟩
    have hI₆ := hE.stable _ _ _ hI₅ (exec_frameB e₆ (by decide))
    have hL0 : LoopI P C H Hh MD h γ mode s e m₀ A₀ W I (ps₀ ++ [p₁]) U₀ F
        (mu C (Qof P).n H F U₀) d₆ d₆ := by
      refine ⟨w₆, R₅.of_frame' (fun r h1 h2 h3 h4 => r₆ r h4) (by rw [r₆ _ (by omega)]; exact R₅.h90)
        (by rwx [r₆ _ (by omega)]) (by rw [r₆ _ (by omega)]; exact R₅.h92)
        (by rw [r₆ _ (by omega)]; exact R₅.chain.h93) (by rw [r₆ _ (by omega)]; exact R₅.chain.h96),
        fun a ha => by rw [m₆]; exact hm₅ a ha, fun _ _ _ _ _ => rfl, by rwo [a40],
        by rwo [a40], by rwx [a40, hUof], ?_, [], ?_, by simpa using hI₆,
        by simp, by rws [a40, hUof]⟩
      · rw [o42, a40, hUof, show d₅.nreg 150040 = U₀ % n by rw [h40, hU₀],
          show d₅.nreg 150041 = F % n by rw [← a41, r₆ _ (by omega)]]
        exact flag_of (by omega) hUF (by omega)
      · rwr [a40, hUof]
    obtain ⟨d₇, k₇, e₇, hL₇, hU₇, hk₇⟩ := mainLoop_exec S hE L d₆ a41 d₆ hL0
    obtain ⟨w₇, R₇, hm₇, hk₇', -, -, -, -, loop, hpath, hI₇, hok₇, hcnt⟩ := hL₇
    rw [hU₇] at hpath hcnt
    -- the last piece
    obtain ⟨d₈, k₈, fin, e₈, hk₈, hI₈, hok₈, hfinY, hfinN, mem₈⟩ := final_exec S hE
      (ps := ps₀ ++ [p₁] ++ loop) hD hMD hHh d₇ w₇ hm₇ R₇
      (by rw [hk₇' _ (by omega) (by omega) (by omega) (by omega), r₆ _ (by omega),
        kp₅ _ (by ufo Keep) (by omega) (by omega), b39]) hI₇ he he1
    -- the pieces
    have hfin : (fin = [pVE (F % n) e] ∧ (F : ℝ) < ks + len ((2 * C.m + 7 : ℕ) : ℝ) ks ke) ∨
        (fin = [] ∧ (F : ℝ) = ks + len ((2 * C.m + 7 : ℕ) : ℝ) ks ke) := by
      by_cases hc : InUB C.m e.edge ∨ 0 < (chainModel C).param (Qof P) e
      · left; rw [hfinY hc, hF]; exact ⟨rfl, hfin1 hc⟩
      · right; exact ⟨hfinN hc, hfin2 hc⟩
    have hok : ∀ pc ∈ p₁ :: (loop ++ fin), PcOK P C m₀ h γ pc := by
      intro pc hpc
      rcases List.mem_cons.1 hpc with rfl | hpc
      · exact hp₁
      · rcases List.mem_append.1 hpc with hpc | hpc
        · exact hok₇ pc hpc
        · exact hok₈ pc hpc
    have arc := arcOK_general hs he hs1 he1 hp₁s (by rw [hp₁e, hU₀]) (by exact_mod_cast hksU)
      hpath hfin hok
    -- the count
    have hμ : mu C (Qof P).n H F U₀ ≤ 1031 := by
      have h1 := mu_le (C := C) (nQ := (Qof P).n) (H := H) F U₀
      have h2 := card_brkU_le (C := C) (nQ := (Qof P).n) (H := H)
        (by rwo [S.hQn]) (by rw [S.hQn]; exact S.hwf) (U := U₀) (F := F) (by omega)
      have := S.hlen
      omega
    have hfinL : fin.length ≤ 1 := by rcases hfin with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
    refine ⟨d₈, _, p₁ :: (loop ++ fin), hpre (.ifLtN_true hd43 (.seq e₆ (.seq e₇ e₈))), ?_,
      by simpa using hI₈, arc, hok, ?_, fun a ha => by rw [mem₈ a ha]; exact hm₇ a ha⟩
    · have hcl : ((2 * K + 90) * (Nat.log 2 γ + 1) + 1702) * mu C (Qof P).n H F U₀ ≤
          ((2 * K + 90) * (Nat.log 2 γ + 1) + 1702) * 1031 := Nat.mul_le_mul_left _ hμ
      rw [a40, hUof] at hk₇
      unfold genCost
      have := S.hlen
      omega
    · simp only [List.length_cons, List.length_append]
      have e1 : 2 * (Nat.log 2 γ + 1) * mu C (Qof P).n H F U₀ ≤ 2 * (Nat.log 2 γ + 1) * 1031 :=
        Nat.mul_le_mul_left _ hμ
      have e2 : 2 * (Nat.log 2 γ + 1) * 1031 + 3 ≤ 2100 * (Nat.log 2 γ + 1) := by omega
      omega
  · -- a single piece
    have hd : Done C.m s.edge e.edge := by
      by_contra hnd
      have := (hndone hnd).2.2
      rwo [this, b43, c91] at hd43
    obtain ⟨hp₁e, -⟩ := hdone hd
    refine ⟨d₅, _, [p₁], hpre (.ifLtN_false hd43 (.skip w₅)), ?_, hI₅,
      arcOK_single hs he hs1 he1 hp₁s hp₁e, by simpa using hp₁, ?_, hm₅⟩
    · ufo genCost
    · sio

end

end ShootCut

end Chazelle.Core
