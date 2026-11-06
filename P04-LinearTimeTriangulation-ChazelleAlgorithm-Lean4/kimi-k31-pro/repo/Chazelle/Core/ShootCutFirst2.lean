module

public import Chazelle.Core.ShootCutFirst
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics

/-!
# WP-G, part 30: the first piece on the RAM

`first_exec`: from the start `s`, the piece to the first walk vertex `c₀ = c0Of m e₁` of the
main loop (`40 := c₀`), or, when the subarc is short (`Done`), the whole piece `[s, e]`
(`43 := 1`).
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK NFLoc

@[expose] public section

variable {O : OracleIface} {P : Polygon} {C : Chain} {H : Host} {Hh h γ : ℕ} {m₀ : ℕ → ℕ}
  {A₀ W : ℕ}

theorem uIx_eq {p : ℕ} (hp : InU C p) : uIx p = uIdx C p := by
  unfold uIx uIdx InU at *; splao

/-- **The first piece.** -/
theorem first_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ (PcOK P C m₀ h γ) I K)
    {ps₀ : List Pc} {MD mode : ℕ} {s e : WPos} (d : Config) (hw : WordsBounded W d)
    (R : CoreRegs P C H Hh MD h γ mode s e m₀ d)
    (h38 : d.nreg 150038 = if s.edge ≤ 5 ∨ s.edge = 2 * C.m + 6 then 1 else 0)
    (h37 : d.nreg 150037 = uIx s.edge)
    (h39 : d.nreg 150039 = if e.edge ≤ 5 ∨ e.edge = 2 * C.m + 6 then 1 else 0)
    (h30 : d.nreg 150030 = uIx e.edge) (hI : I ps₀ d)
    (hs : ProperPos (chainModel C) (Qof P) P.n s) (he : ProperPos (chainModel C) (Qof P) P.n e)
    (hs1 : s.edge < 2 * C.m + 7) (he1 : e.edge < 2 * C.m + 7) :
    ∃ d' k p₁, Exec P W (first emit) d d' k ∧ k ≤ K + 20 ∧ I (ps₀ ++ [p₁]) d' ∧
      PcOK P C m₀ h γ p₁ ∧ p₁.s = s ∧
      (Done C.m s.edge e.edge → p₁.e = e ∧ d'.nreg 150043 = 1) ∧
      (¬ Done C.m s.edge e.edge → p₁.e = ⟨c0Of C.m s.edge, 0⟩ ∧
        d'.nreg 150040 = c0Of C.m s.edge ∧ d'.nreg 150043 = d.nreg 150043) ∧
      (∀ r, Keep r → r ≠ 150040 → r ≠ 150043 → d'.nreg r = d.nreg r) ∧
      (∀ a, a < A₀ → d'.nmem a = d.nmem a) := by
  have hWn := S.hW
  unfold hostWords at hWn
  have hm2 := S.hm2'
  have hm1 := C.one_le
  -- the trailing instructions
  have tc43 : ∀ d₂ : Config, WordsBounded W d₂ → (∀ r, Keep r → d₂.nreg r = d.nreg r) →
      ∃ d₃, Exec P W (.instr (.constN 150043 1)) d₂ d₃ 1 ∧ FrameB Scr d₂ d₃ ∧
        d₃.nreg 150043 = 1 ∧ (∀ r, r ≠ 150043 → d₃.nreg r = d₂.nreg r) ∧ d₃.nmem = d₂.nmem :=
    fun d₂ w₂ _ => ⟨_, Exec.constN w₂ 150043 1 (by omega),
      exec_frameB (Exec.constN (P := P) w₂ 150043 1 (by omega)) (by decide), by config_simp,
      fun r hr => by simp [hr], rfl⟩
  have tc40 : ∀ (d₁ : Config), (∀ r, Keep r → d₁.nreg r = d.nreg r) →
      ∀ d₂ : Config, WordsBounded W d₂ → (∀ r, Keep r → d₂.nreg r = d₁.nreg r) →
      ∃ d₃, Exec P W (.instr (.addN 150040 150001 150091)) d₂ d₃ 1 ∧ FrameB Scr d₂ d₃ ∧
        d₃.nreg 150040 = s.edge + 1 ∧ (∀ r, r ≠ 150040 → d₃.nreg r = d₂.nreg r) ∧
        d₃.nmem = d₂.nmem := by
    intro d₁ k₁ d₂ w₂ k₂
    have a1 : d₂.nreg 150001 = s.edge := by
      rw [k₂ _ (by ufo Keep), k₁ _ (by ufo Keep), R.h01]
    have a91 : d₂.nreg 150091 = 1 := by
      rw [k₂ _ (by ufo Keep), k₁ _ (by ufo Keep), R.chain.h91]
    exact ⟨_, Exec.addN w₂ 150040 150001 150091 (by rwo [a1, a91]),
      exec_frameB (Exec.addN (P := P) w₂ 150040 150001 150091 (by rwo [a1, a91]))
        (by decide), by config_simp; rw [a1, a91], fun r hr => by simp [hr], rfl⟩
  have tc40' : ∀ (d₁ : Config), (∀ r, Keep r → d₁.nreg r = d.nreg r) →
      ∀ d₂ : Config, WordsBounded W d₂ → (∀ r, Keep r → d₂.nreg r = d₁.nreg r) →
      ∃ d₃, Exec P W (.instr (.copyN 150040 150096)) d₂ d₃ 1 ∧ FrameB Scr d₂ d₃ ∧
        d₃.nreg 150040 = 6 ∧ (∀ r, r ≠ 150040 → d₃.nreg r = d₂.nreg r) ∧
        d₃.nmem = d₂.nmem := by
    intro d₁ k₁ d₂ w₂ k₂
    have a96 : d₂.nreg 150096 = 6 := by
      rw [k₂ _ (by ufo Keep), k₁ _ (by ufo Keep), R.chain.h96]
    exact ⟨_, Exec.copyN w₂ 150040 150096, exec_frameB (Exec.copyN (P := P) w₂ 150040 150096)
      (by decide), by config_simp; rw [a96], fun r hr => by simp [hr], rfl⟩
  unfold first
  by_cases hsU : s.edge ≤ 5 ∨ s.edge = 2 * C.m + 6
  · have t38 : d.nreg 150090 < d.nreg 150038 := by rwo [R.h90, h38, ite_eq_left hsU]
    -- the piece to `6` (with `75 := 6` first)
    have toSix : ¬ Done C.m s.edge e.edge →
        ∃ d' k, Exec P W (.seq (.instr (.copyN 150075 150096)) (.seq pcSV (.seq emit
          (.instr (.copyN 150040 150096))))) d d' k ∧ k ≤ K + 7 ∧ I (ps₀ ++ [pSV s 6]) d' ∧
          d'.nreg 150040 = 6 ∧ (∀ r, Keep r → r ≠ 150040 → d'.nreg r = d.nreg r) ∧
          (∀ a, a < A₀ → d'.nmem a = d.nmem a) := by
      intro _
      have e₁ := Exec.copyN (P := P) hw 150075 150096
      set d₁ := ({ d with nreg := upd d.nreg 150075 (d.nreg 150096) } : Config) with hd₁
      have k₁ : ∀ r, Keep r → d₁.nreg r = d.nreg r := fun r hr => by
        simp only [hd₁, upd]; rw [ite_eq_right (by ufo Keep at hr)]
      have hpv : PcOK P C m₀ h γ (pSV s 6) := pSV_ok hs hs1 (by omega) (by
        rwo [wt_U_to_six C (Qof P) hs hsU])
      obtain ⟨d', k, ex, hk, hI', h40, kp, mem⟩ := leaf_exec hE (pc := pSV s 6) (tgt := 150040)
        d₁ (hE.stable _ _ _ hI (exec_frameB e₁ (by decide))) hpv
        (pcSV_exec d₁ e₁.wb_right (by omega) (by rw [k₁ _ (by ufo Keep), R.h01])
          (by rw [k₁ _ (by ufo Keep), R.h02]) (by simp [hd₁, upd, R.chain.h96]))
        (tc40' d₁ k₁)
      exact ⟨d', _, .seq e₁ ex, by omega, hI', h40, fun r hr h1 => (kp r hr h1).trans (k₁ r hr),
        mem⟩
    have notDone : ¬ (e.edge ≤ 5 ∨ e.edge = 2 * C.m + 6) ∨ ¬ uIx s.edge < uIx e.edge →
        ¬ Done C.m s.edge e.edge := by
      rintro hc (⟨-, h2, h3⟩ | ⟨h1, -⟩)
      · rcases hc with hc | hc
        · exact hc h2
        · exact hc h3
      · exact h1 hsU
    have fin6 : ¬ Done C.m s.edge e.edge → ∀ (d' : Config) (k : ℕ),
        Exec P W (first emit) d d' k → k ≤ K + 20 → I (ps₀ ++ [pSV s 6]) d' →
        d'.nreg 150040 = 6 → (∀ r, Keep r → r ≠ 150040 → d'.nreg r = d.nreg r) →
        (∀ a, a < A₀ → d'.nmem a = d.nmem a) →
        ∃ d' k p₁, Exec P W (first emit) d d' k ∧ k ≤ K + 20 ∧ I (ps₀ ++ [p₁]) d' ∧
          PcOK P C m₀ h γ p₁ ∧ p₁.s = s ∧
          (Done C.m s.edge e.edge → p₁.e = e ∧ d'.nreg 150043 = 1) ∧
          (¬ Done C.m s.edge e.edge → p₁.e = ⟨c0Of C.m s.edge, 0⟩ ∧
            d'.nreg 150040 = c0Of C.m s.edge ∧ d'.nreg 150043 = d.nreg 150043) ∧
          (∀ r, Keep r → r ≠ 150040 → r ≠ 150043 → d'.nreg r = d.nreg r) ∧
          (∀ a, a < A₀ → d'.nmem a = d.nmem a) := by
      intro hnd d' k ex hk hI' h40 kp mem
      have hc0 : c0Of C.m s.edge = 6 := by unfold c0Of; rw [ite_eq_left hsU]
      refine ⟨d', k, pSV s 6, ex, hk, hI', pSV_ok hs hs1 (by omega) (by
        rwo [wt_U_to_six C (Qof P) hs hsU]), rfl, fun hd => absurd hd hnd, fun _ => ⟨by
        rwr [hc0], by rw [hc0, h40], kp _ (by ufo Keep) (by omega)⟩,
        fun r hr h1 _ => kp r hr h1, mem⟩
    by_cases heU : e.edge ≤ 5 ∨ e.edge = 2 * C.m + 6
    · have t39 : d.nreg 150090 < d.nreg 150039 := by rwo [R.h90, h39, ite_eq_left heU]
      by_cases hlt : uIx s.edge < uIx e.edge
      · -- a single piece through the uncounted block
        have hpv : PcOK P C m₀ h γ (pSE s e) := pSE_ok hs he hs1 he1 (by
          rw [wt_U_U C (Qof P) hs he hsU heU (by rwx [← uIx_eq hsU, ← uIx_eq heU])]; omega)
        obtain ⟨d', k, ex, hk, hI', h43, kp, mem⟩ := leaf_exec hE (pc := pSE s e)
          (tgt := 150043) d hI hpv (pcSE_exec d hw (by omega) R.h01 R.h02 R.h03 R.h04) tc43
        refine ⟨d', _, pSE s e, .ifLtN_true t38 (.ifLtN_true t39 (.ifLtN_true
          (by rwx [h37, h30]) ex)), by omega, hI', hpv, rfl, fun _ => ⟨rfl, h43⟩,
          fun hnd => absurd (Or.inl ⟨hsU, heU, hlt⟩) hnd, fun r hr h1 h2 => kp r hr h2, mem⟩
      · obtain ⟨d', k, ex, hk, hI', h40, kp, mem⟩ := toSix (notDone (Or.inr hlt))
        exact fin6 (notDone (Or.inr hlt)) d' _ (.ifLtN_true t38 (.ifLtN_true t39
          (.ifLtN_false (by rwx [h37, h30]) ex))) (by omega) hI' h40 kp mem
    · have t39 : ¬ d.nreg 150090 < d.nreg 150039 := by rwo [R.h90, h39, ite_eq_right heU]
      obtain ⟨d', k, ex, hk, hI', h40, kp, mem⟩ := toSix (notDone (Or.inl heU))
      exact fin6 (notDone (Or.inl heU)) d' _ (.ifLtN_true t38 (.ifLtN_false t39 ex)) (by omega)
        hI' h40 kp mem
  · have t38 : ¬ d.nreg 150090 < d.nreg 150038 := by rwo [R.h90, h38, ite_eq_right hsU]
    have hc0 : c0Of C.m s.edge = s.edge + 1 := by unfold c0Of; rw [ite_eq_right hsU]
    -- `75 := e₁ + 1`
    have e₁ := Exec.addN (P := P) hw 150075 150001 150091 (by rwo [R.h01, R.chain.h91])
    set d₁ := ({ d with nreg := upd d.nreg 150075 (d.nreg 150001 + d.nreg 150091) } : Config)
      with hd₁
    have k₁ : ∀ r, Keep r → d₁.nreg r = d.nreg r := fun r hr => by
      simp only [hd₁, upd]; rw [ite_eq_right (by ufo Keep at hr)]
    have o75 : d₁.nreg 150075 = s.edge + 1 := by simp [hd₁, upd, R.h01, R.chain.h91]
    have w₁ := e₁.wb_right
    have hI₁ := hE.stable _ _ _ hI (exec_frameB e₁ (by decide))
    have a39 : d₁.nreg 150039 = d.nreg 150039 := k₁ _ (by ufo Keep)
    have a90 : d₁.nreg 150090 = 0 := by rw [k₁ _ (by ufo Keep), R.h90]
    have a32 : d₁.nreg 150032 = 2 * C.m + 6 := by rw [k₁ _ (by ufo Keep), R.h32]
    -- the piece to `e₁ + 1`
    have toNext : ¬ Done C.m s.edge e.edge →
        ∃ d' k, Exec P W (.seq pcSV (.seq emit (.instr (.addN 150040 150001 150091)))) d₁ d' k ∧
          k ≤ K + 6 ∧ I (ps₀ ++ [pSV s (s.edge + 1)]) d' ∧ d'.nreg 150040 = s.edge + 1 ∧
          (∀ r, Keep r → r ≠ 150040 → d'.nreg r = d₁.nreg r) ∧
          (∀ a, a < A₀ → d'.nmem a = d₁.nmem a) := by
      intro _
      have hpv : PcOK P C m₀ h γ (pSV s (s.edge + 1)) := pSV_ok hs hs1 (by omega)
        (wt_to_next _ _ hs)
      exact leaf_exec hE (pc := pSV s (s.edge + 1)) (tgt := 150040) d₁ hI₁ hpv
        (pcSV_exec d₁ w₁ (by omega) (by rw [k₁ _ (by ufo Keep), R.h01])
          (by rw [k₁ _ (by ufo Keep), R.h02]) o75)
        (fun d₂ w₂ k₂ => tc40 d₁ k₁ d₂ w₂ k₂)
    have finN : ¬ Done C.m s.edge e.edge → ∀ (d' : Config) (k : ℕ),
        Exec P W (first emit) d d' k → k ≤ K + 20 → I (ps₀ ++ [pSV s (s.edge + 1)]) d' →
        d'.nreg 150040 = s.edge + 1 → (∀ r, Keep r → r ≠ 150040 → d'.nreg r = d₁.nreg r) →
        (∀ a, a < A₀ → d'.nmem a = d₁.nmem a) →
        ∃ d' k p₁, Exec P W (first emit) d d' k ∧ k ≤ K + 20 ∧ I (ps₀ ++ [p₁]) d' ∧
          PcOK P C m₀ h γ p₁ ∧ p₁.s = s ∧
          (Done C.m s.edge e.edge → p₁.e = e ∧ d'.nreg 150043 = 1) ∧
          (¬ Done C.m s.edge e.edge → p₁.e = ⟨c0Of C.m s.edge, 0⟩ ∧
            d'.nreg 150040 = c0Of C.m s.edge ∧ d'.nreg 150043 = d.nreg 150043) ∧
          (∀ r, Keep r → r ≠ 150040 → r ≠ 150043 → d'.nreg r = d.nreg r) ∧
          (∀ a, a < A₀ → d'.nmem a = d.nmem a) := by
      intro hnd d' k ex hk hI' h40 kp mem
      refine ⟨d', k, pSV s (s.edge + 1), ex, hk, hI', pSV_ok hs hs1 (by omega)
        (wt_to_next _ _ hs), rfl, fun hd => absurd hd hnd, fun _ => ⟨by rwr [hc0],
        by rw [hc0, h40], (kp _ (by ufo Keep) (by omega)).trans
          (k₁ _ (by ufo Keep))⟩,
        fun r hr h1 _ => (kp r hr h1).trans (k₁ r hr), fun a ha => (mem a ha).trans rfl⟩
    by_cases heU : e.edge ≤ 5 ∨ e.edge = 2 * C.m + 6
    · have t39 : d₁.nreg 150090 < d₁.nreg 150039 := by
        rwo [a90, a39, h39, ite_eq_left heU]
      by_cases hnx : s.edge + 1 < 2 * C.m + 6
      · have hnd : ¬ Done C.m s.edge e.edge := by
          rintro (⟨h1, -⟩ | ⟨-, -, h3⟩)
          · exact hsU h1
          · exact h3 hnx
        obtain ⟨d', k, ex, hk, hI', h40, kp, mem⟩ := toNext hnd
        exact finN hnd d' _ (.ifLtN_false t38 (.seq e₁ (.ifLtN_true t39 (.ifLtN_true
          (by rwx [o75, a32]) ex)))) (by omega) hI' h40 kp mem
      · -- a single piece from the last edge into the uncounted block
        have hpv : PcOK P C m₀ h γ (pSE s e) := pSE_ok hs he hs1 he1
          (wt_last_edge C (Qof P) hs he (by omega) heU)
        obtain ⟨d', k, ex, hk, hI', h43, kp, mem⟩ := leaf_exec hE (pc := pSE s e)
          (tgt := 150043) (post := fun d₃ => d₃.nreg 150043 = 1) d₁ hI₁ hpv
          (pcSE_exec d₁ w₁ (by omega)
            (by rw [k₁ _ (by ufo Keep), R.h01])
            (by rw [k₁ _ (by ufo Keep), R.h02])
            (by rw [k₁ _ (by ufo Keep), R.h03])
            (by rw [k₁ _ (by ufo Keep), R.h04]))
          (fun d₂ w₂ _ => ⟨_, Exec.constN w₂ 150043 1 (by omega),
            exec_frameB (Exec.constN (P := P) w₂ 150043 1 (by omega)) (by decide),
            by config_simp, fun r hr => by simp [hr], rfl⟩)
        refine ⟨d', _, pSE s e, .ifLtN_false t38 (.seq e₁ (.ifLtN_true t39 (.ifLtN_false
          (by rwx [o75, a32]) ex))), by omega, hI', hpv, rfl, fun _ => ⟨rfl, h43⟩,
          fun hnd => absurd (Or.inr ⟨hsU, heU, hnx⟩) hnd,
          fun r hr h1 h2 => (kp r hr h2).trans (k₁ r hr), fun a ha => (mem a ha).trans rfl⟩
    · have t39 : ¬ d₁.nreg 150090 < d₁.nreg 150039 := by
        rwo [a90, a39, h39, ite_eq_right heU]
      have hnd : ¬ Done C.m s.edge e.edge := by
        rintro (⟨h1, -⟩ | ⟨-, h2, -⟩)
        · exact hsU h1
        · exact heU h2
      obtain ⟨d', k, ex, hk, hI', h40, kp, mem⟩ := toNext hnd
      exact finN hnd d' _ (.ifLtN_false t38 (.seq e₁ (.ifLtN_false t39 ex))) (by omega) hI' h40
        kp mem

/-- A piece to the end `e` from the walk vertex in `75`, handed to `emit`. -/
theorem leafVE_exec {W A₀ K : ℕ} {emit : Stmt} {Pv : Pc → Prop} {I : List Pc → Config → Prop}
    (hE : EmitOK P W emit A₀ Pv I K) {ps : List Pc} {e : WPos} {v : ℕ} (d : Config)
    (hw : WordsBounded W d) (hW : 1 ≤ W) (h75 : d.nreg 150075 = v)
    (h03 : d.nreg 150003 = e.edge) (h04 : d.nreg 150004 = e.hgt) (hI : I ps d)
    (hpv : Pv (pVE v e)) :
    ∃ d' k, Exec P W (.seq pcVE emit) d d' k ∧ k ≤ K + 5 ∧ I (ps ++ [pVE v e]) d' ∧
      (∀ r, Keep r → d'.nreg r = d.nreg r) ∧ (∀ a, a < A₀ → d'.nmem a = d.nmem a) := by
  obtain ⟨d₁, k₁, e₁, hk₁, hR, fr₁, kp₁⟩ := pcVE_exec (P := P) d hw hW h75 h03 h04
  obtain ⟨d₂, k₂, e₂, hk₂, hI₂, kp₂, mem₂⟩ := hE.run _ _ d₁ e₁.wb_right (hE.stable _ _ _ hI fr₁) hR hpv
  exact ⟨d₂, k₁ + k₂, .seq e₁ e₂, by omega, hI₂, fun r hr => (kp₂ r hr).trans (kp₁ r hr),
    fun a ha => by rw [mem₂ a ha, fr₁.2.2.1]⟩

/-- **The last piece**: from the walk vertex `2m + 5` into the uncounted block, or from the start
vertex of the edge of the end when its parameter is positive, or none. -/
theorem final_exec (S : SEnv O P C H Hh h γ m₀ A₀ W) {emit : Stmt}
    {I : List Pc → Config → Prop} {K : ℕ} (hE : EmitOK P W emit A₀ (PcOK P C m₀ h γ) I K)
    {ps : List Pc} {MD mode : ℕ} {s e : WPos}
    (hD : ChainDescAt m₀ (MD + 1) (Qof P) H C) (hMD : MD + 6 ≤ A₀) (hHh : m₀ (MD + 1) = Hh)
    (d : Config) (hw : WordsBounded W d) (hm : ∀ a, a < A₀ → d.nmem a = m₀ a)
    (R : CoreRegs P C H Hh MD h γ mode s e m₀ d)
    (h39 : d.nreg 150039 = if e.edge ≤ 5 ∨ e.edge = 2 * C.m + 6 then 1 else 0) (hI : I ps d)
    (he : ProperPos (chainModel C) (Qof P) P.n e) (he1 : e.edge < 2 * C.m + 7) :
    ∃ d' k fin, Exec P W (final emit) d d' k ∧ k ≤ K + 100 * H.length + 2200 ∧
      I (ps ++ fin) d' ∧ (∀ pc ∈ fin, PcOK P C m₀ h γ pc) ∧
      ((InUB C.m e.edge ∨ 0 < (chainModel C).param (Qof P) e) →
        fin = [pVE (fOf C.m e.edge) e]) ∧
      (¬ (InUB C.m e.edge ∨ 0 < (chainModel C).param (Qof P) e) → fin = []) ∧
      (∀ a, a < A₀ → d'.nmem a = d.nmem a) := by
  have hWn := S.hW
  unfold hostWords at hWn
  have hm2 := S.hm2'
  have hm1 := C.one_le
  unfold final
  by_cases heU : e.edge ≤ 5 ∨ e.edge = 2 * C.m + 6
  · have t39 : d.nreg 150090 < d.nreg 150039 := by rwo [R.h90, h39, ite_eq_left heU]
    have hf : fOf C.m e.edge = 2 * C.m + 5 := by unfold fOf; rw [ite_eq_left heU]
    have e₁ := Exec.copyN (P := P) hw 150075 150031
    set d₁ := ({ d with nreg := upd d.nreg 150075 (d.nreg 150031) } : Config) with hd₁
    have k₁ : ∀ r, Keep r → d₁.nreg r = d.nreg r := fun r hr => by
      simp only [hd₁, upd]; rw [ite_eq_right (by ufo Keep at hr)]
    have hpv : PcOK P C m₀ h γ (pVE (2 * C.m + 5) e) := pVE_ok he he1 (by omega)
      (wt_last_to_U C (Qof P) he heU)
    obtain ⟨d', k, ex, hk, hI', -, mem⟩ := leafVE_exec hE d₁ e₁.wb_right (by omega)
      (by simp [hd₁, upd, R.h31]) (by rw [k₁ _ (by ufo Keep), R.h03])
      (by rw [k₁ _ (by ufo Keep), R.h04])
      (hE.stable _ _ _ hI (exec_frameB e₁ (by decide))) hpv
    refine ⟨d', _, [pVE (2 * C.m + 5) e], .ifLtN_true t39 (.seq e₁ ex), by omega, hI', ?_,
      fun _ => by rw [hf], fun h => absurd (Or.inl heU) h, mem⟩
    intro pc hp; simp only [List.mem_singleton] at hp; rwx [hp]
  · have t39 : ¬ d.nreg 150090 < d.nreg 150039 := by rwo [R.h90, h39, ite_eq_right heU]
    have hf : fOf C.m e.edge = e.edge := by unfold fOf; rw [ite_eq_right heU]
    by_cases h4 : d.nreg 150090 < d.nreg 150004
    · have hh : 1 ≤ e.hgt := by rwo [R.h90, R.h04] at h4
      obtain ⟨j, hj⟩ : ∃ j, e.hgt = j + 1 := ⟨e.hgt - 1, by omega⟩
      have hex : e = ⟨e.edge, j + 1⟩ := by rw [← hj]
      obtain ⟨d₁, k₁, e₁, hk₁, o49, o76, r₁, m₁⟩ : ∃ d₁ k₁, Exec P W
          (block [.copyN 150049 150003, .subN 150076 150004 150091]) d d₁ k₁ ∧ k₁ = 2 ∧
          d₁.nreg 150049 = e.edge ∧ d₁.nreg 150076 = j ∧
          (∀ x, x ≠ 150049 → x ≠ 150076 → d₁.nreg x = d.nreg x) ∧ d₁.nmem = d.nmem := by
        exec_block
        refine ⟨rfl, by config_simp; exact R.h03, by config_simp; rwo [R.h04, R.chain.h91],
          fun x h1 h2 => ?_, rfl⟩
        simp only [upd]; split_ifs <;> first | rfl | omega
      have R₁ : ChainRegs C (H.pts P.n).length Hh d₁ := R.chain.of_frame fun r hr => r₁ r (by
        sio only [List.mem_cons, List.not_mem_nil, or_false] at hr) (by
        sio only [List.mem_cons, List.not_mem_nil, or_false] at hr)
      have hpe : ProperPos (chainModel C) (Qof P) P.n ⟨e.edge, j + 1⟩ := by rwx [← hex]
      obtain ⟨d₂, k₂, e₂, hk₂, fr₂, i₂, l₂⟩ := posP_exec S hD hMD hHh d₁ e₁.wb_right
        (fun a ha => by rw [m₁]; exact hm a ha) R₁ (by rw [r₁ _ (by omega) (by omega), R.h00])
        (by rw [r₁ _ (by omega) (by omega), R.h27]) (by rw [r₁ _ (by omega) (by omega), R.h90])
        (by rw [r₁ _ (by omega) (by omega), R.h92]) o49 o76 (by omega) (by omega)
        (by have := he.2.2; omega)
      have ip : d₂.nreg 150089 = 1 ↔ 0 < (chainModel C).param (Qof P) e := by
        rw [hex]; exact i₂.trans (param_pos_iff _ _ hpe).symm
      have c90 : d₂.nreg 150090 = 0 := by
        rw [(exec_frameB e₂ (B := Bd) (by decide)).1 _ (by decide), r₁ _ (by omega) (by omega),
          R.h90]
      have hI₂ := hE.stable _ _ _ hI ((exec_frameB e₁ (by decide)).trans fr₂)
      have w₂ := e₂.wb_right
      by_cases hp : d₂.nreg 150090 < d₂.nreg 150089
      · have hpos : 0 < (chainModel C).param (Qof P) e := ip.1 (by omega)
        have e₃ := Exec.copyN (P := P) w₂ 150075 150003
        set d₃ := ({ d₂ with nreg := upd d₂.nreg 150075 (d₂.nreg 150003) } : Config) with hd₃
        have a3 : d₂.nreg 150003 = e.edge := by
          rw [fr₂.1 _ (by decide), r₁ _ (by omega) (by omega), R.h03]
        have a4 : d₂.nreg 150004 = e.hgt := by
          rw [fr₂.1 _ (by decide), r₁ _ (by omega) (by omega), R.h04]
        have hpv : PcOK P C m₀ h γ (pVE e.edge e) := pVE_ok he he1 (by omega)
          (wt_from_start _ _ he hpos)
        obtain ⟨d', k, ex, hk, hI', -, mem⟩ := leafVE_exec hE d₃ e₃.wb_right (by omega)
          (by simp [hd₃, upd, a3]) (by simp [hd₃, upd, a3]) (by simp [hd₃, upd, a4])
          (hE.stable _ _ _ hI₂ (exec_frameB e₃ (by decide))) hpv
        refine ⟨d', _, [pVE e.edge e], .ifLtN_false t39 (.ifLtN_true h4 (.seq e₁ (.seq e₂
          (.ifLtN_true hp (.seq e₃ ex))))), by have := S.hlen; omega, hI', ?_, fun _ => by rw [hf],
          fun h => absurd (Or.inr hpos) h, fun a ha => ?_⟩
        · intro pc hpc; simp only [List.mem_singleton] at hpc; rwx [hpc]
        · rw [mem a ha]; show d₂.nmem a = d.nmem a; rw [fr₂.2.2.1, m₁]
      · have hpos : ¬ 0 < (chainModel C).param (Qof P) e := fun h' => by
          have := ip.2 h'; omega
        refine ⟨d₂, _, [], .ifLtN_false t39 (.ifLtN_true h4 (.seq e₁ (.seq e₂
          (.ifLtN_false hp (.skip w₂))))), by have := S.hlen; omega, by simpa using hI₂,
          by simp, fun h => h.elim (fun h => absurd h heU) (fun h => absurd h hpos),
          fun _ => rfl, fun a ha => by rw [fr₂.2.2.1, m₁]⟩
    · have hpos : ¬ 0 < (chainModel C).param (Qof P) e := by
        rw [R.h90, R.h04] at h4
        have he0 : e.hgt = 0 := by omega
        rw [show e = ⟨e.edge, 0⟩ by rw [← he0]]
        simp [Model.param]
      refine ⟨d, _, [], .ifLtN_false t39 (.ifLtN_false h4 (.skip hw)), by omega,
        by simpa using hI, by simp, fun h => h.elim (fun h => absurd h heU) (fun h => absurd h hpos), fun _ => rfl,
        fun a _ => rfl⟩

end

end ShootCut

end Chazelle.Core
