module

public import Chazelle.Core.NFBuildPassProg
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# WP-C (BuildNF), RAM part 9: executions of the pieces of the main pass (stack part)

`curS_exec`, `topS_exec`, `chordS_exec`, `stepS_exec`: register values and memory writes of the
pieces `curS`, `topS`, `chordS`, `stepS` of the main pass.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- Decide the conditions of nested `if`s by `omega`. -/
macro "ifs_omega" : tactic =>
  `(tactic| repeat' (first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)]))


/-! ## Write sets allowing natural stores -/

/-- `wrOK` with natural stores allowed. -/
def wrOKM (B : ℕ → Bool) : Instr → Bool
  | .storeN _ _ => true
  | i => wrOK B i

/-- Every instruction satisfies `wrOKM B`. -/
def wrM (B : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrOKM B i
  | .seq s t => wrM B s && wrM B t
  | .ifLtN _ _ t e => wrM B t && wrM B e
  | .ifLtR _ _ t e => wrM B t && wrM B e
  | .whileLtN _ _ b => wrM B b
  | .whileLtR _ _ b => wrM B b

/-- Registers outside `B`, the real memory and the output agree (the natural memory may change). -/
def FrameM (B : ℕ → Bool) (c c' : Config) : Prop :=
  (∀ r, B r = false → c'.nreg r = c.nreg r) ∧ (∀ r, B r = false → c'.rreg r = c.rreg r) ∧
    c'.rmem = c.rmem ∧ c'.output = c.output

theorem FrameM.refl (B : ℕ → Bool) (c : Config) : FrameM B c c :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem FrameM.trans {B : ℕ → Bool} {c₁ c₂ c₃ : Config} (h₁ : FrameM B c₁ c₂)
    (h₂ : FrameM B c₂ c₃) : FrameM B c₁ c₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), fun r hr => (h₂.2.1 r hr).trans (h₁.2.1 r hr),
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem FrameM.mono {B B' : ℕ → Bool} {c c' : Config} (h : FrameM B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameM B' c c' :=
  ⟨fun r hr => h.1 r (by cases h' : B r; rfl; rw [hB r h'] at hr; exact absurd hr (by simp)),
    fun r hr => h.2.1 r (by cases h' : B r; rfl; rw [hB r h'] at hr; exact absurd hr (by simp)),
    h.2.2.1, h.2.2.2⟩

theorem FrameB.toM {B : ℕ → Bool} {c c' : Config} (h : FrameB B c c') : FrameM B c c' :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **Frame of a statement with natural stores.** -/
theorem exec_frameM {P : Polygon} {W : ℕ} {B : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wrM B s = true) : FrameM B c c' := by
  induction h with
  | skip _ => exact FrameM.refl B _
  | @instr ins c c' _ he _ _ =>
    simp only [wrM] at hs
    cases ins <;> simp only [wrOKM, wrOK, Bool.false_eq_true] at hs <;>
      simp only [Instr.effect, Option.some.injEq] at he <;>
      (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst he <;>
      refine ⟨fun j hj => ?_, fun j hj => ?_, rfl, rfl⟩ <;>
      first
      | rfl
      | (simp only [upd]; split_ifs with hh
         · subst hh; simp_all
         · rfl)
  | seq _ _ ih₁ ih₂ =>
    simp only [wrM, Bool.and_eq_true] at hs
    exact (ih₁ hs.1).trans (ih₂ hs.2)
  | ifLtN_true _ _ ih =>
    simp only [wrM, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtN_false _ _ ih =>
    simp only [wrM, Bool.and_eq_true] at hs; exact ih hs.2
  | ifLtR_true _ _ ih =>
    simp only [wrM, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtR_false _ _ ih =>
    simp only [wrM, Bool.and_eq_true] at hs; exact ih hs.2
  | whileLtN_false _ _ => exact FrameM.refl B _
  | whileLtN_true _ _ _ ih₁ ih₂ => exact (ih₁ hs).trans (ih₂ hs)
  | whileLtR_false _ _ => exact FrameM.refl B _
  | whileLtR_true _ _ _ ih₁ ih₂ => exact (ih₁ hs).trans (ih₂ hs)

/-- A write set without stores allows stores. -/
theorem wrM_of_wr {B : ℕ → Bool} {s : Stmt} (h : wr B s = true) : wrM B s = true := by
  induction s with
  | skip => rfl
  | instr i => simp only [wr] at h; simp only [wrM]; cases i <;> simp_all [wrOK, wrOKM]
  | seq s t ihs iht =>
    simp only [wr, Bool.and_eq_true] at h; simp only [wrM, ihs h.1, iht h.2, Bool.and_self]
  | ifLtN a b s t ihs iht =>
    simp only [wr, Bool.and_eq_true] at h; simp only [wrM, ihs h.1, iht h.2, Bool.and_self]
  | ifLtR a b s t ihs iht =>
    simp only [wr, Bool.and_eq_true] at h; simp only [wrM, ihs h.1, iht h.2, Bool.and_self]
  | whileLtN a b s ih => simp only [wr] at h; simp only [wrM, ih h]
  | whileLtR a b s ih => simp only [wr] at h; simp only [wrM, ih h]

theorem wrM_mono {B B' : ℕ → Bool} (hB : ∀ r, B r = true → B' r = true) {s : Stmt}
    (h : wrM B s = true) : wrM B' s = true := by
  induction s with
  | skip => rfl
  | instr i => simp only [wrM] at h ⊢; cases i <;> simp_all [wrOK, wrOKM]
  | seq s t ihs iht =>
    simp only [wrM, Bool.and_eq_true] at h; simp only [wrM, ihs h.1, iht h.2, Bool.and_self]
  | ifLtN a b s t ihs iht =>
    simp only [wrM, Bool.and_eq_true] at h; simp only [wrM, ihs h.1, iht h.2, Bool.and_self]
  | ifLtR a b s t ihs iht =>
    simp only [wrM, Bool.and_eq_true] at h; simp only [wrM, ihs h.1, iht h.2, Bool.and_self]
  | whileLtN a b s ih => simp only [wrM] at h; simp only [wrM, ih h]
  | whileLtR a b s ih => simp only [wrM] at h; simp only [wrM, ih h]

section exec

variable {P : Polygon} {W : ℕ}

theorem wr_curS : wr (fun r => decide (r = 43110 ∨ r = 43111 ∨ r = 42110 ∨ r = 42111 ∨
    r = 42112 ∨ r = 43113 ∨ r = 43114)) curS = true := by decide

/-- **The current code.** -/
theorem curS_exec (d : Config) (hw : WordsBounded W d) {c T : ℕ} (hc : d.nmem (d.nreg 43103) = c)
    (hT : d.nreg 42000 = T) (h1 : d.nreg 42102 = 1) (h1' : d.nreg 43011 = 1)
    (hTW : T + 4 * c + 3 ≤ W) (hxW : d.nmem (T + 4 * c + 3) + 1 ≤ W) :
    ∃ d' k, Exec P W curS d d' k ∧ k = 12 ∧
      d'.nreg 42110 = d.nmem (T + 4 * c) ∧ d'.nreg 42111 = d.nmem (T + 4 * c + 1) ∧
      d'.nreg 42112 = d.nmem (T + 4 * c + 2) ∧ d'.nreg 43113 = d.nmem (T + 4 * c + 3) ∧
      d'.nreg 43114 = d.nmem (T + 4 * c + 3) + 1 ∧
      FrameB (fun r => decide (r = 43110 ∨ r = 43111 ∨ r = 42110 ∨ r = 42111 ∨
        r = 42112 ∨ r = 43113 ∨ r = 43114)) d d' := by
  have x₀ := Exec.loadN (P := P) hw 43110 43103
  set d₀ : Config := { d with nreg := upd d.nreg 43110 (d.nmem (d.nreg 43103)) } with hd₀
  have w₀ := x₀.wb_right
  obtain ⟨d₁, k₁, x₁, hk₁, e₁, g₁, p₁, fr₁, m₁, -, -, -, a₁⟩ := loadRec_exec (P := P) d₀ w₀
    (src := 43110) (ad := 43111) (o := 42110) (c := c) (T := T)
    (by rw [hd₀]; simp [hc]) (by rw [hd₀]; simp [hT]) (by rw [hd₀]; simp [h1])
    (by norm_num) (by norm_num) (by norm_num) (by omega) (by norm_num) (by norm_num)
  have w₁ := x₁.wb_right
  have o₁ : d₁.nreg 42102 = 1 := by
    rw [fr₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), hd₀]; simp [h1]
  have o₁' : d₁.nreg 43011 = 1 := by
    rw [fr₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), hd₀]; simp [h1']
  have mm₁ : d₁.nmem = d.nmem := by rw [m₁, hd₀]
  suffices H : ∃ d' k, Exec P W curS d d' k ∧ k = 12 ∧
      d'.nreg 42110 = d.nmem (T + 4 * c) ∧ d'.nreg 42111 = d.nmem (T + 4 * c + 1) ∧
      d'.nreg 42112 = d.nmem (T + 4 * c + 2) ∧ d'.nreg 43113 = d.nmem (T + 4 * c + 3) ∧
      d'.nreg 43114 = d.nmem (T + 4 * c + 3) + 1 by
    obtain ⟨d', k, x, hk, v1, v2, v3, v4, v5⟩ := H
    exact ⟨d', k, x, hk, v1, v2, v3, v4, v5, exec_frameB x wr_curS⟩
  obtain ⟨d₂, k₂, x₂, hk₂, v₂⟩ : ∃ d₂ k₂, Exec P W
      (block [.addN 43111 43111 42102, .loadN 43113 43111, .addN 43114 43113 43011]) d₁ d₂ k₂ ∧
      k₂ = 3 ∧ d₂.nreg 43113 = d.nmem (T + 4 * c + 3) ∧
      d₂.nreg 43114 = d.nmem (T + 4 * c + 3) + 1 ∧
      (∀ r, r ≠ 43111 → r ≠ 43113 → r ≠ 43114 → d₂.nreg r = d₁.nreg r) := by
    exec_block
    · rwo [a₁, o₁]
    · config_simp; rwx [a₁, o₁, o₁', mm₁]
    · refine ⟨rfl, ?_, ?_, fun r r1 r2 r3 => ?_⟩ <;> config_simp
      · rw [a₁, o₁, mm₁]
      · rw [a₁, o₁, o₁', mm₁]
      · simp (disch := omega) only [upd_other]
  obtain ⟨b3, b4, g₂⟩ := v₂
  refine ⟨d₂, _, .seq x₀ (.seq x₁ x₂), by omega, ?_, ?_, ?_, b3, b4⟩
  · rw [g₂ _ (by norm_num) (by norm_num) (by norm_num), e₁, hd₀]
  · rw [g₂ _ (by norm_num) (by norm_num) (by norm_num), g₁, hd₀]
  · rw [g₂ _ (by norm_num) (by norm_num) (by norm_num), p₁, hd₀]


theorem wr_topS (dst : ℕ) : wr (fun r => decide (r = dst ∨ r = 43116)) (topS dst) = true := by
  simp [topS, wr, block, wrOK]

/-- **The region index of the label.** -/
theorem topS_exec (d : Config) (hw : WordsBounded W d) {dst : ℕ} (h0 : d.nreg 43010 = 0)
    (h1 : d.nreg 43011 = 1) (hSW : d.nreg 44006 + d.nreg 43101 ≤ W) :
    ∃ d' k, Exec P W (topS dst) d d' k ∧ k ≤ 5 ∧
      d'.nreg dst = (if d.nreg 43101 = 0 then 0 else d.nmem (d.nreg 44006 + d.nreg 43101 - 1)) ∧
      FrameB (fun r => decide (r = dst ∨ r = 43116)) d d' := by
  suffices H : ∃ d' k, Exec P W (topS dst) d d' k ∧ k ≤ 5 ∧
      d'.nreg dst = (if d.nreg 43101 = 0 then 0 else d.nmem (d.nreg 44006 + d.nreg 43101 - 1)) by
    obtain ⟨d', k, x, hk, hv⟩ := H
    exact ⟨d', k, x, hk, hv, exec_frameB x (wr_topS dst)⟩
  unfold topS
  by_cases hs : d.nreg 43101 = 0
  · refine spec_ifLtN_false (by rwo [h0, hs]) (spec_instr (Exec.constN hw _ _ (by
      have := hw.1 43010; omega)) fun _ => ⟨by omega, ?_⟩)
    simp [hs]
  · refine spec_ifLtN_true (by rwo [h0]) ?_
    exec_block
    · exact hSW
    · refine ⟨by omega, ?_⟩
      config_simp
      rw [ite_eq_right hs, h1]

/-- Five consecutive words written at `b`. -/
def wr5 (m : ℕ → ℕ) (b v0 v1 v2 v3 v4 : ℕ) (a : ℕ) : ℕ :=
  if a = b then v0 else if a = b + 1 then v1 else if a = b + 2 then v2 else if a = b + 3 then v3
  else if a = b + 4 then v4 else m a

theorem wr_chordS : wrM (fun r => decide (43130 ≤ r ∧ r < 43135)) chordS = true := by decide

/-- **The chord record** of `x = r43113` at `CT + 5 x`. -/
theorem chordS_exec (d : Config) (hw : WordsBounded W d) {x B CT : ℕ} (hx : d.nreg 43113 = x)
    (hB : d.nreg 43001 = B) (hCT : d.nreg 44001 = CT) (h1 : d.nreg 43011 = 1)
    (hBW : B + 3 * x + 2 ≤ W) (hCW : CT + 5 * x + 4 ≤ W) :
    ∃ d' k, Exec P W chordS d d' k ∧ k ≤ 25 ∧
      d'.nmem = wr5 d.nmem (CT + 5 * x) (d.nmem (B + 3 * x)) (d.nmem (B + 3 * x + 1))
        (d.nmem (B + 3 * x + 2))
        (if d.nreg 42112 < 1 then d.nreg 43115 else d.nreg 43114)
        (if d.nreg 42112 < 1 then d.nreg 43114 else d.nreg 43115) ∧
      FrameM (fun r => decide (43130 ≤ r ∧ r < 43135)) d d' := by
  suffices H : ∃ d' k, Exec P W chordS d d' k ∧ k ≤ 25 ∧
      d'.nmem = wr5 d.nmem (CT + 5 * x) (d.nmem (B + 3 * x)) (d.nmem (B + 3 * x + 1))
        (d.nmem (B + 3 * x + 2))
        (if d.nreg 42112 < 1 then d.nreg 43115 else d.nreg 43114)
        (if d.nreg 42112 < 1 then d.nreg 43114 else d.nreg 43115) by
    obtain ⟨d', k, x, hk, hv⟩ := H
    exact ⟨d', k, x, hk, hv, exec_frameM x wr_chordS⟩
  unfold chordS
  refine spec_seq ?_
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [hx, hB, hCT, h1]; omega)
    | skip
  by_cases hp : d.nreg 42112 < 1
  · refine spec_ifLtN_true (by config_simp; rwx [h1]) ?_
    exec_block
    all_goals first
      | (config_simp; simp (config := { failIfUnchanged := false }) only [hx, hB, hCT, h1]; omega)
      | skip
    refine ⟨by omega, ?_⟩
    config_simp
    funext a
    simp only [hx, hB, hCT, h1, ite_eq_left hp, upd_apply, wr5]
    by_cases e0 : a = CT + 5 * x
    · subst e0; ifs_omega; congr 1; omega
    by_cases e1 : a = CT + 5 * x + 1
    · subst e1; ifs_omega; congr 1; omega
    by_cases e2 : a = CT + 5 * x + 2
    · subst e2; ifs_omega; congr 1; omega
    by_cases e3 : a = CT + 5 * x + 3
    · subst e3; ifs_omega
    by_cases e4 : a = CT + 5 * x + 4
    · subst e4; ifs_omega
    ifs_omega
  · refine spec_ifLtN_false (by config_simp; rwx [h1]) ?_
    exec_block
    all_goals first
      | (config_simp; simp (config := { failIfUnchanged := false }) only [hx, hB, hCT, h1]; omega)
      | skip
    refine ⟨by omega, ?_⟩
    config_simp
    funext a
    simp only [hx, hB, hCT, h1, ite_eq_right hp, upd_apply, wr5]
    by_cases e0 : a = CT + 5 * x
    · subst e0; ifs_omega; congr 1; omega
    by_cases e1 : a = CT + 5 * x + 1
    · subst e1; ifs_omega; congr 1; omega
    by_cases e2 : a = CT + 5 * x + 2
    · subst e2; ifs_omega; congr 1; omega
    by_cases e3 : a = CT + 5 * x + 3
    · subst e3; ifs_omega
    by_cases e4 : a = CT + 5 * x + 4
    · subst e4; ifs_omega
    ifs_omega


/-- The registers of the stack step. -/
def Bstep (r : ℕ) : Bool := decide (43130 ≤ r ∧ r < 43135) || decide (r = 43116 ∨ r = 43101)

theorem wr_stepS : wrM Bstep stepS = true := by decide

/-- The memory after a push. -/
def pushMem (d : Config) (x B CT ST : ℕ) : ℕ → ℕ :=
  upd (wr5 d.nmem (CT + 5 * x) (d.nmem (B + 3 * x)) (d.nmem (B + 3 * x + 1))
    (d.nmem (B + 3 * x + 2))
    (if d.nreg 42112 < 1 then d.nreg 43115 else d.nreg 43114)
    (if d.nreg 42112 < 1 then d.nreg 43114 else d.nreg 43115)) (ST + d.nreg 43101) (d.nreg 43114)

/-- **The stack step**: pop if the label is `x + 1`, else chord record and push. -/
theorem stepS_exec (d : Config) (hw : WordsBounded W d) {x B CT ST : ℕ} (hx : d.nreg 43113 = x)
    (hB : d.nreg 43001 = B) (hCT : d.nreg 44001 = CT) (hST : d.nreg 44006 = ST)
    (h1 : d.nreg 43011 = 1) (hBW : B + 3 * x + 2 ≤ W) (hCW : CT + 5 * x + 4 ≤ W)
    (hSW : ST + d.nreg 43101 ≤ W) (hsW : d.nreg 43101 + 1 ≤ W) :
    ∃ d' k, Exec P W stepS d d' k ∧ k ≤ 32 ∧ FrameM Bstep d d' ∧
      (d.nreg 43115 = d.nreg 43114 → d'.nreg 43101 = d.nreg 43101 - 1 ∧ d'.nmem = d.nmem) ∧
      (d.nreg 43115 ≠ d.nreg 43114 → d'.nreg 43101 = d.nreg 43101 + 1 ∧
        d'.nmem = pushMem d x B CT ST) := by
  have push : ∃ d' k, Exec P W pushS d d' k ∧ k ≤ 28 ∧ d'.nreg 43101 = d.nreg 43101 + 1 ∧
      d'.nmem = pushMem d x B CT ST := by
    obtain ⟨d₁, k₁, x₁, hk₁, m₁, f₁⟩ := chordS_exec (P := P) d hw hx hB hCT h1 hBW hCW
    have w₁ := x₁.wb_right
    have r₁ : ∀ r, (r < 43130 ∨ 43135 ≤ r) → d₁.nreg r = d.nreg r := fun r hr =>
      f₁.1 r (by sio only [decide_eq_false_iff_not])
    unfold pushS
    refine spec_seq ⟨d₁, k₁, x₁, ?_⟩
    exec_block
    · rwx [r₁ _ (by norm_num), r₁ _ (by norm_num), hST]
    · config_simp; rwx [r₁ _ (by norm_num), r₁ _ (by norm_num), h1]
    · refine ⟨by omega, ?_, ?_⟩ <;> config_simp
      · rw [r₁ _ (by norm_num), r₁ _ (by norm_num), h1]
      · rwr [r₁ _ (by norm_num), r₁ _ (by norm_num), r₁ _ (by norm_num), hST, m₁]
  unfold stepS
  by_cases a1 : d.nreg 43115 < d.nreg 43114
  · obtain ⟨d', k, x', hk, h2, h3⟩ := push
    refine ⟨d', k + 1, .ifLtN_true a1 x', by omega, exec_frameM (.ifLtN_true a1 x') wr_stepS,
      fun h => absurd h (by omega), fun _ => ⟨h2, h3⟩⟩
  by_cases a2 : d.nreg 43114 < d.nreg 43115
  · obtain ⟨d', k, x', hk, h2, h3⟩ := push
    have X := Exec.ifLtN_false (t := pushS) a1 (Exec.ifLtN_true (e := popS) a2 x')
    refine ⟨d', _, X, by omega, exec_frameM X wr_stepS, fun h => absurd h (by omega),
      fun _ => ⟨h2, h3⟩⟩
  · have x' := Exec.subN (P := P) hw 43101 43101 43011
    have X := Exec.ifLtN_false (t := pushS) a1 (Exec.ifLtN_false (t := pushS) a2 x')
    refine ⟨_, _, X, by omega, exec_frameM X wr_stepS, fun _ => ⟨?_, rfl⟩,
      fun h => absurd h (by omega)⟩
    simp [h1]

end exec

end

end BuildRam

end Chazelle.Core
