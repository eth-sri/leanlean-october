module

public import Chazelle.Core.ShootCutShP0
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# WP-G, part 48: shooting at a kind-0 piece

`pieceK0`: the piece from `x` (`140250`, `140251`) to `y` (`140252`, `140253`) of the walk of
`chainModel C` (`n = 2m + 7` in `140334`), segment by segment (`edgeH`), each answer merged into
the best answer (`mrg`).  Loop registers: `140330` the segment index `d`, `140331` the last
index `D`, `140332 = D + 1`, `140333` the walk edge of segment `d`.
-/


namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim

@[expose] public section

/-- The set-up: `D`, `D + 1`, `d = 0`, the first edge. -/
def k0Init : Stmt :=
  .seq (.ifLtN 140252 140250 (block [.subN 140331 140334 140250, .addN 140331 140331 140252])
      (.instr (.subN 140331 140252 140250)))
    (block [.addN 140332 140331 K1, .constN 140330 0, .copyN 140333 140250])

/-- The ends of segment `d`. -/
def setUV : Stmt :=
  .seq (block [.copyN 140262 140333, .copyN 140263 140333])
    (.seq (.ifLtN 140330 K1 (.instr (.copyN 140264 140251)) (.instr (.constN 140264 0)))
      (.ifLtN 140330 140331
        (.seq (.instr (.addN 140265 140333 K1))
          (.seq (.ifLtN 140265 140334 .skip (.instr (.constN 140265 0)))
            (.instr (.constN 140266 0))))
        (block [.copyN 140265 140252, .copyN 140266 140253])))

/-- The next segment. -/
def adv : Stmt :=
  .seq (block [.addN 140330 140330 K1, .addN 140333 140333 K1])
    (.ifLtN 140333 140334 .skip (.instr (.constN 140333 0)))

/-- **A kind-0 piece.** -/
def pieceK0 : Stmt :=
  .seq k0Init (.whileLtN 140330 140332 (.seq setUV (.seq edgeH (.seq mrg adv))))

/-- The registers written by `pieceK0`. -/
def Bk0 (r : ℕ) : Bool := Bedge r || Bmrg r || decide (140330 ≤ r ∧ r < 140334)

theorem Bk0_env (r : ℕ) (h : envR r) : Bk0 r = false := by
  have := Bedge_env r h
  unfold envR at h
  simp [Bk0, this, Bmrg, Bk, K1, ALLOC, Bool.false_or, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, beq_eq_false_iff_ne] at h ⊢
  omega

variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

theorem CandAt.keep {c c' : Config} {b : ℕ} {S : Set Point} (h : CandAt P C c b S z σ)
    (hk : ∀ j, j < 7 → c'.nreg (b + j) = c.nreg (b + j)) : CandAt P C c' b S z σ := by
  have h0 := hk 0 (by norm_num)
  simp [Nat.add_zero] at h0
  obtain ⟨hb, hn, hy⟩ := h
  refine ⟨by rwx [h0], fun hne => hn (by rwx [← h0]), fun h1 => ?_⟩
  obtain ⟨x, a, f, p, n, q⟩ := hy (by rwx [← h0])
  rw [hk 5 (by norm_num), hk 6 (by norm_num)]
  exact ⟨x, absRec_copy' a (hk 1 (by norm_num)) (hk 2 (by norm_num)) (hk 3 (by norm_num))
    (hk 4 (by norm_num)), f, p, n, q⟩

theorem CandAt.of_eq {c : Config} {b : ℕ} {S S' : Set Point} (h : CandAt P C c b S z σ)
    (hS : S = S') : CandAt P C c b S' z σ := hS ▸ h

/-! ## The set-up -/

theorem k0Init_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {n sE eE : ℕ}
    (h34 : c.nreg 140334 = n) (h50 : c.nreg 140250 = sE) (h52 : c.nreg 140252 = eE)
    (hs : sE < n) (he : eE < n) (hnW : n + 1 ≤ W) :
    ∃ c' k, Exec P W k0Init c c' k ∧ k ≤ 8 ∧ c'.nreg 140330 = 0 ∧
      c'.nreg 140331 = pcD n sE eE ∧ c'.nreg 140332 = pcD n sE eE + 1 ∧
      c'.nreg 140333 = sE ∧ (∀ r, (r < 140330 ∨ 140334 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₂, k₂, e₂, hk₂, q31', r₂, m₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 140252 140250
      (block [.subN 140331 140334 140250, .addN 140331 140331 140252])
      (.instr (.subN 140331 140252 140250))) c c₂ k₂ ∧ k₂ ≤ 4 ∧ c₂.nreg 140331 = pcD n sE eE ∧
      (∀ r, r ≠ 140331 → c₂.nreg r = c.nreg r) ∧ c₂ = { c with nreg := c₂.nreg } := by
    unfold pcD
    by_cases hl : eE < sE
    · obtain ⟨c₁, k₁, e₁, hk₁, q31, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.subN 140331 140334 140250,
          .addN 140331 140331 140252]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 140331 = n - sE + eE ∧
          (∀ r, r ≠ 140331 → c₁.nreg r = c.nreg r) ∧ c₁ = { c with nreg := c₁.nreg } := by
        exec_block
        all_goals first | omega | (config_simp; rwo [h34, h50, h52]) | skip
        refine ⟨rfl, by config_simp; rw [h34, h50, h52], fun r hr => by simp [hr], rfl⟩
      refine ⟨c₁, _, .ifLtN_true (by rwx [h52, h50]) e₁, by omega, ?_, r₁, m₁⟩
      rwo [q31, Nat.mod_eq_of_lt (by omega)]
    · refine ⟨_, _, .ifLtN_false (by rwx [h52, h50]) (Exec.subN hw _ _ _), by norm_num,
        ?_, fun r hr => by simp [hr], rfl⟩
      simp [upd_same]
      rw [h52, h50, show eE + n - sE = (eE - sE) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
  have w₂ := e₂.wb_right
  have hD : pcD n sE eE < n := Nat.mod_lt _ (by omega)
  obtain ⟨c₃, k₃, e₃, hk₃, q32, q30, q33, r₃, m₃⟩ : ∃ c₃ k₃, Exec P W (block [.addN 140332 140331 K1,
      .constN 140330 0, .copyN 140333 140250]) c₂ c₃ k₃ ∧ k₃ = 3 ∧
      c₃.nreg 140332 = pcD n sE eE + 1 ∧ c₃.nreg 140330 = 0 ∧ c₃.nreg 140333 = sE ∧
      (∀ r, r ≠ 140332 → r ≠ 140330 → r ≠ 140333 → c₃.nreg r = c₂.nreg r) ∧
      c₃ = { c₂ with nreg := c₃.nreg } := by
    have g1 : c₂.nreg K1 = 1 := by rw [r₂ _ (by decide), h1]
    have g50 : c₂.nreg 140250 = sE := by rw [r₂ _ (by decide), h50]
    exec_block
    all_goals first | omega | (config_simp; rwo [q31', g1]) | skip
    refine ⟨rfl, by config_simp; rw [q31', g1], by config_simp, by config_simp; rw [g50],
      fun r h1 h2 h3 => ?_, rfl⟩
    simp [upd]; split_ifs <;> first | rfl | omega
  refine ⟨c₃, _, .seq e₂ e₃, by omega, q30, ?_, q32, q33, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [r₃ _ (by decide) (by decide) (by decide), q31']
  · rw [r₃ r (by omega) (by omega) (by omega), r₂ r (by omega)]
  all_goals rw [m₃, m₂]

/-! ## One segment's ends, and the next segment -/

theorem wr_setUV : wr (fun r => decide (140262 ≤ r ∧ r < 140267)) setUV = true := by decide

theorem setUV_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {n : ℕ} {x y : WPos}
    {d D : ℕ} (h30 : c.nreg 140330 = d) (h31 : c.nreg 140331 = D)
    (h33 : c.nreg 140333 = pcEdge n x.edge d) (h34 : c.nreg 140334 = n)
    (h50 : c.nreg 140250 = x.edge) (h51 : c.nreg 140251 = x.hgt) (h52 : c.nreg 140252 = y.edge)
    (h53 : c.nreg 140253 = y.hgt) (hxn : x.edge < n) (hdD : d ≤ D) (hnW : n + 1 ≤ W) :
    ∃ c' k, Exec P W setUV c c' k ∧ k ≤ 12 ∧ c'.nreg 140262 = pcEdge n x.edge d ∧
      c'.nreg 140263 = (pcU n x d).edge ∧ c'.nreg 140264 = (pcU n x d).hgt ∧
      c'.nreg 140265 = (pcV n x y D d).edge ∧ c'.nreg 140266 = (pcV n x y D d).hgt ∧
      FrameB (fun r => decide (140262 ≤ r ∧ r < 140267)) c c' := by
  have hn : 0 < n := by omega
  have hj : pcEdge n x.edge d < n := pcEdge_lt hn d
  have e0 : pcEdge n x.edge 0 = x.edge := by
    unfold pcEdge; rw [Nat.add_zero, Nat.mod_eq_of_lt hxn]
  -- the edge and `U.edge`
  have ea := Exec.copyN (P := P) hw 140262 140333
  have eb := Exec.copyN (P := P) ea.wb_right 140263 140333
  set c₁ := ({ ({ c with nreg := upd c.nreg 140262 (c.nreg 140333) } : Config) with
    nreg := upd (upd c.nreg 140262 (c.nreg 140333)) 140263
      (upd c.nreg 140262 (c.nreg 140333) 140333) } : Config) with hc₁
  have e₁ : Exec P W (block [.copyN 140262 140333, .copyN 140263 140333]) c c₁ 2 :=
    Exec.block_cons ea (Exec.block_cons eb (Exec.block_nil eb.wb_right))
  have g₁ : ∀ r, r ≠ 140262 → r ≠ 140263 → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    rw [hc₁]; simp [h1, h2]
  have q62 : c₁.nreg 140262 = pcEdge n x.edge d := by rw [hc₁]; simp [h33]
  have q63 : c₁.nreg 140263 = pcEdge n x.edge d := by rw [hc₁]; simp [h33]
  have w₁ := e₁.wb_right
  have p30 : c₁.nreg 140330 = d := by rw [g₁ _ (by decide) (by decide), h30]
  have pK : c₁.nreg K1 = 1 := by rw [g₁ _ (by decide) (by decide), h1]
  -- `U.hgt`
  obtain ⟨c₂, k₂, e₂, hk₂, q64, g₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 140330 K1
      (.instr (.copyN 140264 140251)) (.instr (.constN 140264 0))) c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 140264 = (pcU n x d).hgt ∧ ∀ r, r ≠ 140264 → c₂.nreg r = c₁.nreg r := by
    by_cases h0 : d = 0
    · refine ⟨_, _, .ifLtN_true (by rwn [p30, pK, h0]) (Exec.copyN w₁ _ _), by norm_num, ?_,
        fun r hr => by simp [hr]⟩
      simp [pcU, h0, g₁ _ (by decide : (140251 : ℕ) ≠ 140262) (by decide), h51]
    · refine ⟨_, _, .ifLtN_false (by rwo [p30, pK]) (Exec.constN w₁ _ _ (Nat.zero_le _)),
        by norm_num, ?_,
        fun r hr => by simp [hr]⟩
      simp [pcU, h0]
  have w₂ := e₂.wb_right
  have gg : ∀ r, r ≠ 140262 → r ≠ 140263 → r ≠ 140264 → c₂.nreg r = c.nreg r :=
    fun r a b c' => by rw [g₂ r c', g₁ r a b]
  have q30 : c₂.nreg 140330 = d := by rw [gg _ (by decide) (by decide) (by decide), h30]
  have q31 : c₂.nreg 140331 = D := by rw [gg _ (by decide) (by decide) (by decide), h31]
  have q33 : c₂.nreg 140333 = pcEdge n x.edge d := by
    rw [gg _ (by decide) (by decide) (by decide), h33]
  have q34 : c₂.nreg 140334 = n := by rw [gg _ (by decide) (by decide) (by decide), h34]
  have qK : c₂.nreg K1 = 1 := by rw [gg _ (by decide) (by decide) (by decide), h1]
  -- `V`
  obtain ⟨c₃, k₃, e₃, hk₃, v5, v6, g₃⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 140330 140331
      (.seq (.instr (.addN 140265 140333 K1))
        (.seq (.ifLtN 140265 140334 .skip (.instr (.constN 140265 0)))
          (.instr (.constN 140266 0))))
      (block [.copyN 140265 140252, .copyN 140266 140253])) c₂ c₃ k₃ ∧ k₃ ≤ 6 ∧
      c₃.nreg 140265 = (pcV n x y D d).edge ∧ c₃.nreg 140266 = (pcV n x y D d).hgt ∧
      (∀ r, r ≠ 140265 → r ≠ 140266 → c₃.nreg r = c₂.nreg r) := by
    by_cases hD : d < D
    · have hne : d ≠ D := by omega
      have ea := Exec.addN (P := P) w₂ 140265 140333 K1 (by rwo [q33, qK])
      set ca : Config := { c₂ with nreg := upd c₂.nreg 140265 (c₂.nreg 140333 + c₂.nreg K1) }
        with hca
      have a65 : ca.nreg 140265 = pcEdge n x.edge d + 1 := by rw [hca]; simp [q33, qK]
      have a34 : ca.nreg 140334 = n := by rw [hca]; simp [q34]
      have ga : ∀ r, r ≠ 140265 → ca.nreg r = c₂.nreg r := fun r hr => by rw [hca]; simp [hr]
      obtain ⟨cb, kb, eb, hkb, b65, gb⟩ : ∃ cb kb, Exec P W (.ifLtN 140265 140334 .skip
          (.instr (.constN 140265 0))) ca cb kb ∧ kb ≤ 3 ∧
          cb.nreg 140265 = (pcEdge n x.edge d + 1) % n ∧
          ∀ r, r ≠ 140265 → cb.nreg r = ca.nreg r := by
        by_cases hl : pcEdge n x.edge d + 1 < n
        · exact ⟨ca, _, .ifLtN_true (by rwx [a65, a34]) (.skip ea.wb_right),
            by norm_num, by rw [a65, Nat.mod_eq_of_lt hl], fun _ _ => rfl⟩
        · refine ⟨_, _, .ifLtN_false (by rwx [a65, a34])
            (Exec.constN ea.wb_right _ _ (Nat.zero_le _)), by norm_num, ?_,
            fun r hr => by simp [hr]⟩
          simp [Config.nreg_mk, upd_same]
          rw [show pcEdge n x.edge d + 1 = n by omega, Nat.mod_self]
      have ec := Exec.constN (P := P) eb.wb_right 140266 0 (Nat.zero_le _)
      refine ⟨_, _, .ifLtN_true (by rwx [q30, q31]) (.seq ea (.seq eb ec)), by omega,
        ?_, ?_, fun r h1 h2 => ?_⟩
      · simp [Config.nreg_mk, upd_other _ _ _ (by decide : (140265 : ℕ) ≠ 140266)]
        rw [b65]; simp [pcV, hne, pcEdge_succ]
      · simp [pcV, hne]
      · simp [Config.nreg_mk, upd_other _ _ _ h2]; rw [gb r h1, ga r h1]
    · have hD' : d = D := by omega
      have ea := Exec.copyN (P := P) w₂ 140265 140252
      have eb := Exec.copyN (P := P) ea.wb_right 140266 140253
      refine ⟨_, _, .ifLtN_false (by rwx [q30, q31])
        (Exec.block_cons ea (Exec.block_cons eb (Exec.block_nil eb.wb_right))), by norm_num,
        ?_, ?_, fun r h1 h2 => by simp [h1, h2]⟩
      · simp [pcV, hD', gg _ (by decide : (140252 : ℕ) ≠ 140262) (by decide) (by decide), h52]
      · simp [pcV, hD', gg _ (by decide : (140253 : ℕ) ≠ 140262) (by decide) (by decide), h53]
  have ex : Exec P W setUV c c₃ (2 + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  refine ⟨c₃, _, ex, by omega, ?_, ?_, ?_, v5, v6, exec_frameB ex wr_setUV⟩
  · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), q62]
  · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), q63]
    unfold pcU; split_ifs with h0
    · rw [h0, e0]
    · rfl
  · rw [g₃ _ (by decide) (by decide), q64]

theorem wr_adv : wr (fun r => r == 140330 || r == 140333) adv = true := by decide

theorem adv_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {n j d : ℕ}
    (h30 : c.nreg 140330 = d) (h33 : c.nreg 140333 = j) (h34 : c.nreg 140334 = n) (hj : j < n)
    (hW : d + 1 ≤ W) (hnW : n + 1 ≤ W) :
    ∃ c' k, Exec P W adv c c' k ∧ k ≤ 5 ∧ c'.nreg 140330 = d + 1 ∧
      c'.nreg 140333 = (j + 1) % n ∧ FrameB (fun r => r == 140330 || r == 140333) c c' := by
  have h1' : c.nreg 140401 = 1 := h1
  have ea := Exec.addN (P := P) hw 140330 140330 K1 (by rwo [h30, h1])
  have eb := Exec.addN (P := P) ea.wb_right 140333 140333 K1 (by sio [K1, h33, h1'])
  set c₁ := ({ ({ c with nreg := upd c.nreg 140330 (c.nreg 140330 + c.nreg K1) } : Config) with
    nreg := upd (upd c.nreg 140330 (c.nreg 140330 + c.nreg K1)) 140333
      (upd c.nreg 140330 (c.nreg 140330 + c.nreg K1) 140333 +
        upd c.nreg 140330 (c.nreg 140330 + c.nreg K1) K1) } : Config) with hc₁
  have e₁ : Exec P W (block [.addN 140330 140330 K1, .addN 140333 140333 K1]) c c₁ 2 :=
    Exec.block_cons ea (Exec.block_cons eb (Exec.block_nil eb.wb_right))
  have q30 : c₁.nreg 140330 = d + 1 := by rw [hc₁]; simp [K1, h30, h1']
  have q33 : c₁.nreg 140333 = j + 1 := by rw [hc₁]; simp [K1, h33, h1']
  have q34 : c₁.nreg 140334 = n := by rw [hc₁]; simp [h34]
  have w₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, v33, v30⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 140333 140334 .skip
      (.instr (.constN 140333 0))) c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧ c₂.nreg 140333 = (j + 1) % n ∧
      c₂.nreg 140330 = d + 1 := by
    by_cases hl : j + 1 < n
    · exact ⟨c₁, _, .ifLtN_true (by rwx [q33, q34]) (.skip w₁), by norm_num,
        by rw [q33, Nat.mod_eq_of_lt hl], q30⟩
    · refine ⟨_, _, .ifLtN_false (by rwx [q33, q34]) (Exec.constN w₁ _ _
        (Nat.zero_le _)), by norm_num, ?_, by simp [q30]⟩
      simp [Config.nreg_mk, upd_same]
      rw [show j + 1 = n by omega, Nat.mod_self]
  have ex : Exec P W adv c c₂ (2 + k₂) := .seq e₁ e₂
  exact ⟨c₂, _, ex, by omega, v30, v33, exec_frameB ex wr_adv⟩

/-! ## The loop -/

theorem Bmrg_env (r : ℕ) (h : envR r) : Bmrg r = false := by
  unfold envR at h
  simp [Bmrg, Bk, K1, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne] at h ⊢
  omega

/-- The loop invariant of `pieceK0`. -/
def K0Inv (P : Polygon) (W : ℕ) (H : Host) (C : Chain) (z : Point) (σ : ℝ) (x y : WPos)
    (S₀ : Set Point) (A : ℕ) (c₀ c : Config) : Prop :=
  WordsBounded W c ∧ ShEnv P W H C z σ c ∧ ∃ d, d ≤ pcD (2 * C.m + 7) x.edge y.edge + 1 ∧
    c.nreg 140330 = d ∧ c.nreg 140331 = pcD (2 * C.m + 7) x.edge y.edge ∧
    c.nreg 140332 = pcD (2 * C.m + 7) x.edge y.edge + 1 ∧
    c.nreg 140333 = pcEdge (2 * C.m + 7) x.edge d ∧ c.nreg 140334 = 2 * C.m + 7 ∧
    c.nreg 140250 = x.edge ∧ c.nreg 140251 = x.hgt ∧ c.nreg 140252 = y.edge ∧
    c.nreg 140253 = y.hgt ∧ CandAt P C c 140210 (S₀ ∪ segSet C (Qof P) x y d) z σ ∧
    c.nreg ALLOC = A ∧ FrameB Bk0 c₀ c

theorem pieceK0_exec (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c)
    {x y : WPos} (h50 : c.nreg 140250 = x.edge) (h51 : c.nreg 140251 = x.hgt)
    (h52 : c.nreg 140252 = y.edge) (h53 : c.nreg 140253 = y.hgt)
    (h34 : c.nreg 140334 = 2 * C.m + 7)
    (hx : ProperPos (chainModel C) (Qof P) P.n x) (hy : ProperPos (chainModel C) (Qof P) P.n y)
    (hxn : x.edge < 2 * C.m + 7) (hyn : y.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ((chainModel C).key (Qof P) x)
      ((chainModel C).key (Qof P) y) ≤ 1)
    (hxe : x.hgt = 0 ∨ |((chainModel C).pos (Qof P) x).2| < C.radius)
    (hye : y.hgt = 0 ∨ |((chainModel C).pos (Qof P) y).2| < C.radius)
    (hz : z ∉ (chainModel C).arcSet ((chainModel C).key (Qof P) x) ((chainModel C).key (Qof P) y))
    {S₀ : Set Point} (hB : CandAt P C c 140210 S₀ z σ) (hnW : (2 * C.m + 7) + 1 ≤ W)
    (hroom : c.nreg ALLOC + 600000 ≤ W) :
    ∃ c' k, Exec P W pieceK0 c c' k ∧ k ≤ 600000 ∧
      CandAt P C c' 140210 (S₀ ∪ (chainModel C).arcSet ((chainModel C).key (Qof P) x)
        ((chainModel C).key (Qof P) y)) z σ ∧ FrameB Bk0 c c' := by
  have hnWn : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  set n := 2 * C.m + 7 with hn
  set D := pcD n x.edge y.edge with hDdef
  have hD9 : D ≤ 9 := piece0_D_le hx hy hxn hyn hwt
  have hDn : D < n := Nat.mod_lt _ (by omega)
  have hfull := segSet_full (Q := Qof P) hx hy hxn hyn hwt
  -- the set-up
  obtain ⟨c₁, k₁, e₁, hk₁, q30, q31, q32, q33, r₁, m₁, rr₁, rm₁, o₁⟩ :=
    k0Init_exec (P := P) c hw E.k1 h34 h50 h52 hxn hyn (by omega)
  have f₁ : FrameB Bk0 c c₁ := ⟨fun r hr => r₁ r (by sio [Bk0] at hr),
    fun r _ => by rw [rr₁], m₁, rm₁, o₁⟩
  have E₁ := E.frame f₁ Bk0_env
  have I₁ : K0Inv P W H C z σ x y S₀ (c.nreg ALLOC) c c₁ := by
    refine ⟨e₁.wb_right, E₁, 0, by omega, q30, q31, q32, ?_, by rw [r₁ _ (by omega), h34],
      by rw [r₁ _ (by omega), h50], by rw [r₁ _ (by omega), h51], by rw [r₁ _ (by omega), h52],
      by rw [r₁ _ (by omega), h53], ?_, by rw [r₁ _ (by simp [ALLOC])], f₁⟩
    · rw [q33]; unfold pcEdge; rw [Nat.add_zero, Nat.mod_eq_of_lt hxn]
    · rw [segSet_zero, Set.union_empty]
      exact hB.keep fun j hj => r₁ _ (by omega)
  -- the body
  obtain ⟨c₂, k₂, e₂, I₂, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 140330)
    (b := 140332) (body := .seq setUV (.seq edgeH (.seq mrg adv)))
    (K0Inv P W H C z σ x y S₀ (c.nreg ALLOC) c) (fun c' => D + 1 - c'.nreg 140330) 50300
    (fun _ h => h.1) (fun c₀ ⟨hw₀, E₀, d, hd, i30, i31, i32, i33, i34, i50, i51, i52, i53, iB,
      iA, iF⟩ hlt => by
      rw [i30, i32] at hlt
      have hdD : d ≤ D := Nat.lt_succ_iff.mp hlt
      -- the ends
      obtain ⟨c₁', k₁', e₁', hk₁', u62, u63, u64, u65, u66, fu⟩ := setUV_exec (P := P) c₀ hw₀
        E₀.k1 (n := n) (x := x) (y := y) (d := d) (D := D) i30 i31 i33 i34 i50 i51 i52 i53
        hxn hdD (by omega)
      have E₁' := E₀.frame fu fun r hr => by
        unfold envR at hr; sio only [decide_eq_false_iff_not, K1, ALLOC] at hr ⊢
      have ku : ∀ r, (r < 140262 ∨ 140267 ≤ r) → c₁'.nreg r = c₀.nreg r := fun r hr =>
        fu.1 r (by sio)
      -- the segment
      obtain ⟨hU, hV⟩ := pc0_pts (Q := Qof P) (C := C) hxn hyn (d := d) hdD
      obtain ⟨a0, ab, b1⟩ := pc0_ab hx hy hxn hyn hwt d
      have hU' : PosAt P C c₁' 140263 140264 ((chainModel C).pos (Qof P) (pcU n x d)) := by
        refine ⟨by rw [u63, u64], ?_, ?_⟩
        · rw [u63, u64]
          unfold pcU; split_ifs
          · exact hx
          · exact proper_vtx _ _ _ _
        · rw [u63, hnWn]; unfold pcU; split_ifs
          · exact hxn
          · exact pcEdge_lt (by omega) _
      have hV' : PosAt P C c₁' 140265 140266 ((chainModel C).pos (Qof P) (pcV n x y D d)) := by
        refine ⟨by rw [u65, u66], ?_, ?_⟩
        · rw [u65, u66]
          unfold pcV; split_ifs
          · exact hy
          · exact proper_vtx _ _ _ _
        · rw [u65, hnWn]; unfold pcV; split_ifs
          · exact hyn
          · exact pcEdge_lt (by omega) _
      have iU : EndIn P C c₁' 140263 140264 ((chainModel C).pos (Qof P) (pcU n x d)) :=
        ⟨hU', by rw [u64]; unfold pcU; split_ifs <;> first | exact hxe | exact Or.inl rfl⟩
      have iV : EndIn P C c₁' 140265 140266 ((chainModel C).pos (Qof P) (pcV n x y D d)) :=
        ⟨hV', by rw [u66]; unfold pcV; split_ifs <;> first | exact hye | exact Or.inl rfl⟩
      have geo : SegGeo C (pcEdge n x.edge d) ((chainModel C).pos (Qof P) (pcU n x d))
          ((chainModel C).pos (Qof P) (pcV n x y D d)) :=
        ⟨by rw [hnWn]; exact pcEdge_lt (by omega) _, _, _, a0, ab, b1, hU, hV⟩
      have hzd : z ∉ seg ((chainModel C).pos (Qof P) (pcU n x d))
          ((chainModel C).pos (Qof P) (pcV n x y D d)) := fun hm => hz (by
        rw [← hfull]
        unfold segSet
        simp [Set.mem_iUnion, List.mem_range, exists_prop]
        exact ⟨d, by omega, hm⟩)
      have hA₁' : c₁'.nreg ALLOC = c.nreg ALLOC := by rw [ku _ (by simp [ALLOC]), iA]
      obtain ⟨c₂', k₂', e₂', hk₂', ca, fe⟩ := edgeH_exec c₁' e₁'.wb_right E₁' iU iV u62 geo hzd
        (by rwo [hA₁'])
      have E₂' := E₁'.frame fe Bedge_env
      have ke : ∀ r, Bedge r = false → c₂'.nreg r = c₁'.nreg r := fe.1
      have iB' : CandAt P C c₂' 140210 (S₀ ∪ segSet C (Qof P) x y d) z σ := by
        refine iB.keep fun j hj => ?_
        rw [ke _ (by sio [Bedge, Bprim]), ku _ (by omega)]
      obtain ⟨c₃', k₃', e₃', hk₃', cb, fm⟩ := mrg_exec c₂' e₂'.wb_right E₂' iB' ca
      have E₃' := E₂'.frame fm Bmrg_env
      have km : ∀ r, Bmrg r = false → c₃'.nreg r = c₂'.nreg r := fm.1
      -- registers kept through the segment
      have keep3 : ∀ r, (140330 ≤ r ∧ r < 140335) ∨ (140250 ≤ r ∧ r < 140254) ∨ r = ALLOC →
          c₃'.nreg r = c₀.nreg r := fun r hr => by
        rw [km r (by simp [Bmrg, Bk]; ufo ALLOC at hr),
          ke r (by simp [Bedge, Bprim]; ufo ALLOC at hr),
          ku r (by ufo ALLOC at hr)]
      obtain ⟨c₄', k₄', e₄', hk₄', v30, v33, fa⟩ := adv_exec (P := P) c₃' e₃'.wb_right E₃'.k1
        (n := n) (j := pcEdge n x.edge d) (d := d)
        (by rw [keep3 _ (Or.inl ⟨le_rfl, by norm_num⟩), i30])
        (by rw [keep3 _ (Or.inl ⟨by norm_num, by norm_num⟩), i33])
        (by rw [keep3 _ (Or.inl ⟨by norm_num, by norm_num⟩), i34]) (pcEdge_lt (by omega) _)
        (by omega) (by omega)
      have E₄' := E₃'.frame fa fun r hr => by
        unfold envR at hr; simp [Bool.or_eq_false_iff, beq_eq_false_iff_ne, K1, ALLOC] at hr ⊢
        omega
      have ka : ∀ r, r ≠ 140330 → r ≠ 140333 → c₄'.nreg r = c₃'.nreg r := fun r h1 h2 =>
        fa.1 r (by simp [h1, h2])
      have kk : ∀ r, (r = 140331 ∨ r = 140332 ∨ r = 140334 ∨ (140250 ≤ r ∧ r < 140254) ∨
          r = ALLOC) → c₄'.nreg r = c₀.nreg r := fun r hr => by
        rw [ka r (by ufo ALLOC at hr) (by ufo ALLOC at hr),
          keep3 r (by ufo ALLOC at hr ⊢)]
      have fb : FrameB Bk0 c₀ c₄' :=
        (((FrameB.wk fu (fun r h => by simp at h; sio [Bk0, Bedge])).trans
          (FrameB.wk fe (fun r h => by simp [Bk0, h]))).trans
          (FrameB.wk fm (fun r h => by simp [Bk0, h]))).trans
          (FrameB.wk fa (fun r h => by simp at h; sio [Bk0]))
      refine ⟨c₄', _, .seq e₁' (.seq e₂' (.seq e₃' e₄')), ⟨e₄'.wb_right, E₄', d + 1, by omega,
        v30, by rw [kk _ (Or.inl rfl), i31], by rw [kk _ (Or.inr (Or.inl rfl)), i32],
        by rw [v33, pcEdge_succ], by rw [kk _ (Or.inr (Or.inr (Or.inl rfl))), i34],
        by rw [kk _ (by omega), i50], by rw [kk _ (by omega), i51], by rw [kk _ (by omega), i52],
        by rw [kk _ (by omega), i53], ?_, by rw [kk _ (by simp), iA], iF.trans fb⟩,
        by omega, by rwo [v30, i30]⟩
      refine (cb.keep fun j hj => ka _ (by omega) (by omega)).of_eq ?_
      rw [segSet_succ, Set.union_assoc]) I₁
  obtain ⟨-, E₂, d, hd, i30, -, i32, -, -, -, -, -, -, iB, -, iF⟩ := I₂
  have i32' : c₂.nreg 140332 = D + 1 := i32
  have hd' : d ≤ D + 1 := hd
  rw [i30, i32'] at hx₂
  have hdD : d = D + 1 := by omega
  rw [hdD, hfull] at iB
  refine ⟨c₂, _, .seq e₁ e₂, ?_, iB, iF⟩
  have : D + 1 - c₁.nreg 140330 = D + 1 := by rwr [q30]
  rw [this] at hk₂
  have : (50300 + 2) * (D + 1) ≤ 50302 * 10 := Nat.mul_le_mul_left _ (by omega)
  omega

end

end ShootCut

end Chazelle.Core
