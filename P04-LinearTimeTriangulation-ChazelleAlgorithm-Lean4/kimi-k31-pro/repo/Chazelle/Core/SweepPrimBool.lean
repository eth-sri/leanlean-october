module

public import Chazelle.Core.SignKernel
public import Chazelle.SimpTactics

/-!
# Sweep RAM primitives (WP-D2), part 1: Boolean formulas over bit registers

The sweep primitives (`docs/design-merge-v2.md` §9.6) decide geometric predicates from a handful
of sign-kernel bits (each a register holding `0` or `1`).  Combining the bits is done by a
**branch-free compiler** of Boolean formulas:

* `BF`: formulas over register variables (`var r`), constants, `not`, `and`, `or`;
* `BF.compile f d`: a straight-line block computing the value of `f` into register `d`, using
  the registers `d + 1 … d + size f` as scratch (`not` is `1 - x`, `and` is `x + y - 1`, `or` is
  `s - (s - 1)` for `s = x + y`, all truncated subtractions);
* `BF.compile_exec`: if the variables of `f` are registers below `d` holding bits, the block
  writes `(f.eval …).toNat` into `d` in at most `4 · size f` steps and changes no register outside
  `d … d + size f`, no memory and not the output.
-/

namespace Chazelle.Core

namespace SweepPrim

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-! ## Write sets -/

/-- Monotonicity of the write check in the accepted set. -/
theorem wr_mono {B B' : ℕ → Bool} {s : Stmt} (h : wr B s = true)
    (hB : ∀ r, B r = true → B' r = true) : wr B' s = true := by
  induction s with
  | skip => rfl
  | instr i =>
    simp only [wr] at h ⊢
    cases i <;> simp only [wrOK] at h ⊢ <;> first | exact hB _ h | exact h
  | seq s t ihs iht =>
    simp only [wr, Bool.and_eq_true] at h ⊢; exact ⟨ihs h.1, iht h.2⟩
  | ifLtN a b t e iht ihe =>
    simp only [wr, Bool.and_eq_true] at h ⊢; exact ⟨iht h.1, ihe h.2⟩
  | ifLtR a b t e iht ihe =>
    simp only [wr, Bool.and_eq_true] at h ⊢; exact ⟨iht h.1, ihe h.2⟩
  | whileLtN a b body ih => simp only [wr] at h ⊢; exact ih h
  | whileLtR a b body ih => simp only [wr] at h ⊢; exact ih h

/-- A register frame for fewer registers is one for more. -/
theorem frameB_mono {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameB B' c c' :=
  ⟨fun r hr => h.1 r (by cases hb : B r <;> simp_all), fun r hr => h.2.1 r (by
    cases hb : B r <;> simp_all), h.2.2⟩

/-! ## Formulas -/

/-- **A Boolean formula** over bit registers. -/
inductive BF where
  /-- The bit held in register `r` (true iff it is `1`). -/
  | var (r : ℕ)
  /-- A constant. -/
  | const (b : Bool)
  /-- Negation. -/
  | not (f : BF)
  /-- Conjunction. -/
  | and (f g : BF)
  /-- Disjunction. -/
  | or (f g : BF)

namespace BF

/-- The value of a formula under an assignment of the variables. -/
def eval (v : ℕ → Bool) : BF → Bool
  | var r => v r
  | const b => b
  | not f => !(f.eval v)
  | and f g => f.eval v && g.eval v
  | or f g => f.eval v || g.eval v

/-- The number of nodes. -/
def size : BF → ℕ
  | var _ => 1
  | const _ => 1
  | not f => f.size + 1
  | and f g => f.size + g.size + 1
  | or f g => f.size + g.size + 1

theorem one_le_size (f : BF) : 1 ≤ f.size := by
  cases f <;> simp only [size] <;> omega

/-- Every variable register satisfies `p`. -/
def VarsOK (p : ℕ → Prop) : BF → Prop
  | var r => p r
  | const _ => True
  | not f => f.VarsOK p
  | and f g => f.VarsOK p ∧ g.VarsOK p
  | or f g => f.VarsOK p ∧ g.VarsOK p

theorem VarsOK.mono {p q : ℕ → Prop} (hpq : ∀ r, p r → q r) :
    ∀ {f : BF}, f.VarsOK p → f.VarsOK q
  | var r, h => hpq r h
  | const _, _ => trivial
  | not f, h => VarsOK.mono hpq (f := f) h
  | and f g, h => ⟨VarsOK.mono hpq (f := f) h.1, VarsOK.mono hpq (f := g) h.2⟩
  | or f g, h => ⟨VarsOK.mono hpq (f := f) h.1, VarsOK.mono hpq (f := g) h.2⟩

/-- **The branch-free compiler**: the value of `f` into `d`, scratch `d + 1 …`. -/
def compile : BF → ℕ → Stmt
  | var r, d => .instr (.copyN d r)
  | const b, d => .instr (.constN d b.toNat)
  | not f, d => .seq (f.compile d) (block [.constN (d + 1) 1, .subN d (d + 1) d])
  | and f g, d => .seq (f.compile d) (.seq (g.compile (d + 1))
      (block [.addN d d (d + 1), .constN (d + 1) 1, .subN d d (d + 1)]))
  | or f g, d => .seq (f.compile d) (.seq (g.compile (d + 1))
      (block [.addN d d (d + 1), .constN (d + 1) 1, .subN (d + 1) d (d + 1),
        .subN d d (d + 1)]))

/-- The registers the compiled block may write. -/
def wset (f : BF) (d : ℕ) (r : ℕ) : Bool := decide (d ≤ r ∧ r ≤ d + f.size)

theorem wr_compile : ∀ (f : BF) (d : ℕ), wr (f.wset d) (f.compile d) = true
  | var r, d => by simp [compile, wr, wrOK, wset]
  | const b, d => by simp [compile, wr, wrOK, wset]
  | not f, d => by
    have h := wr_mono (wr_compile f d) (B' := (not f).wset d) (fun r hr => by
      unfold wset at hr ⊢; have := of_decide_eq_true hr; simp only [size] at this ⊢
      exact decide_eq_true (by omega))
    have h1 := one_le_size f
    simp only [compile, wr]
    rw [h]
    simp only [block, wr, wrOK, wset, size, Bool.true_and, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_⟩ <;>
      exact decide_eq_true (by omega)
  | and f g, d => by
    have hf := wr_mono (wr_compile f d) (B' := (and f g).wset d) (fun r hr => by
      unfold wset at hr ⊢; have := of_decide_eq_true hr; simp only [size] at this ⊢
      exact decide_eq_true (by omega))
    have hg := wr_mono (wr_compile g (d + 1)) (B' := (and f g).wset d) (fun r hr => by
      unfold wset at hr ⊢; have := of_decide_eq_true hr; simp only [size] at this ⊢
      exact decide_eq_true (by omega))
    have h1 := one_le_size f
    have h2 := one_le_size g
    simp only [compile, wr]
    rw [hf, hg]
    simp only [block, wr, wrOK, wset, size, Bool.true_and, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_⟩ <;> (try refine ⟨?_, ?_⟩) <;>
      exact decide_eq_true (by omega)
  | or f g, d => by
    have hf := wr_mono (wr_compile f d) (B' := (or f g).wset d) (fun r hr => by
      unfold wset at hr ⊢; have := of_decide_eq_true hr; simp only [size] at this ⊢
      exact decide_eq_true (by omega))
    have hg := wr_mono (wr_compile g (d + 1)) (B' := (or f g).wset d) (fun r hr => by
      unfold wset at hr ⊢; have := of_decide_eq_true hr; simp only [size] at this ⊢
      exact decide_eq_true (by omega))
    have h1 := one_le_size f
    have h2 := one_le_size g
    simp only [compile, wr]
    rw [hf, hg]
    simp only [block, wr, wrOK, wset, size, Bool.true_and, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_⟩ <;> (try refine ⟨?_, ?_⟩) <;> (try refine ⟨?_, ?_⟩) <;>
      exact decide_eq_true (by omega)
/-- **The compiled formula computes its value.**  If every variable is a register below `d`
holding a bit, the block writes `(f.eval …).toNat` into `d` (at most `4 · size f` steps) and
changes only the registers `d … d + size f`. -/
theorem compile_exec {P : Polygon} {W : ℕ} (hW : 2 ≤ W) :
    ∀ (f : BF) (d : ℕ) (c : Config), WordsBounded W c →
      f.VarsOK (fun r => r < d ∧ c.nreg r ≤ 1) →
      ∃ c' k, Exec P W (f.compile d) c c' k ∧ k ≤ 4 * f.size ∧
        c'.nreg d = (f.eval fun r => decide (c.nreg r = 1)).toNat ∧ FrameB (f.wset d) c c'
  | var r, d, c, hw, hv => by
    obtain ⟨hr, hb⟩ := hv
    refine ⟨_, 1, Exec.copyN (P := P) hw d r, by simp [size], ?_,
      exec_frameB (Exec.copyN (P := P) hw d r) (wr_compile (var r) d)⟩
    simp only [eval]
    config_simp
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h | h <;> simp [h]
  | const b, d, c, hw, _ => by
    have hb : b.toNat ≤ W := by cases b <;> simp; omega
    refine ⟨_, 1, Exec.constN (P := P) hw d _ hb, by simp [size], by simp [eval],
      exec_frameB (Exec.constN (P := P) hw d _ hb) (wr_compile (const b) d)⟩
  | not f, d, c, hw, hv => by
    obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁⟩ := compile_exec (P := P) hW f d c hw hv
    have hw₁ := e₁.wb_right
    have e₂ : ∃ c₂ k₂, Exec P W (block [.constN (d + 1) 1, .subN d (d + 1) d]) c₁ c₂ k₂ ∧
        k₂ = 2 ∧ c₂.nreg d = 1 - c₁.nreg d := by
      exec_block
      · omega
      · refine ⟨rfl, ?_⟩
        simp [upd]
    obtain ⟨c₂, k₂, e₂, hk₂, v₂⟩ := e₂
    have ex : Exec P W ((not f).compile d) c c₂ (k₁ + k₂) := .seq e₁ e₂
    refine ⟨c₂, _, ex, by sio only [size], ?_, exec_frameB ex (wr_compile (not f) d)⟩
    rw [v₂, v₁]
    simp only [eval]
    cases f.eval _ <;> rfl
  | and f g, d, c, hw, hv => by
    obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁⟩ := compile_exec (P := P) hW f d c hw (VarsOK.mono (by
      intro r h; exact h) hv.1)
    have hw₁ := e₁.wb_right
    have keep : ∀ r, r < d → c₁.nreg r = c.nreg r := fun r hr =>
      f₁.1 r (by sio only [wset, decide_eq_false_iff_not])
    obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂⟩ := compile_exec (P := P) hW g (d + 1) c₁ hw₁ (VarsOK.mono (by
      intro r h; exact ⟨by omega, by rw [keep r h.1]; exact h.2⟩) hv.2)
    have hw₂ := e₂.wb_right
    have d₂ : c₂.nreg d = c₁.nreg d := f₂.1 d (by simp [wset])
    have hb₁ : c₁.nreg d ≤ 1 := by rw [v₁]; exact Bool.toNat_le _
    have hb₂ : c₂.nreg (d + 1) ≤ 1 := by rw [v₂]; exact Bool.toNat_le _
    have e₃ : ∃ c₃ k₃, Exec P W (block [.addN d d (d + 1), .constN (d + 1) 1,
        .subN d d (d + 1)]) c₂ c₃ k₃ ∧ k₃ = 3 ∧
        c₃.nreg d = c₂.nreg d + c₂.nreg (d + 1) - 1 := by
      exec_block
      · omega
      · omega
      · refine ⟨rfl, ?_⟩
        simp [upd]
    obtain ⟨c₃, k₃, e₃, hk₃, v₃⟩ := e₃
    have ex : Exec P W ((and f g).compile d) c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
    refine ⟨c₃, _, ex, by sio only [size], ?_, exec_frameB ex (wr_compile (and f g) d)⟩
    rw [v₃, d₂, v₁, v₂]
    have hg : (g.eval fun r => decide (c₁.nreg r = 1)) = g.eval fun r => decide (c.nreg r = 1) :=
      eval_congr (p := fun r => r < d ∧ c.nreg r ≤ 1) (fun r hr => by rw [keep r hr.1]) hv.2
    rw [hg]
    simp only [eval]
    cases f.eval _ <;> cases g.eval _ <;> rfl
  | or f g, d, c, hw, hv => by
    obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁⟩ := compile_exec (P := P) hW f d c hw (VarsOK.mono (by
      intro r h; exact h) hv.1)
    have hw₁ := e₁.wb_right
    have keep : ∀ r, r < d → c₁.nreg r = c.nreg r := fun r hr =>
      f₁.1 r (by sio only [wset, decide_eq_false_iff_not])
    obtain ⟨c₂, k₂, e₂, hk₂, v₂, f₂⟩ := compile_exec (P := P) hW g (d + 1) c₁ hw₁ (VarsOK.mono (by
      intro r h; exact ⟨by omega, by rw [keep r h.1]; exact h.2⟩) hv.2)
    have hw₂ := e₂.wb_right
    have d₂ : c₂.nreg d = c₁.nreg d := f₂.1 d (by simp [wset])
    have hb₁ : c₁.nreg d ≤ 1 := by rw [v₁]; exact Bool.toNat_le _
    have hb₂ : c₂.nreg (d + 1) ≤ 1 := by rw [v₂]; exact Bool.toNat_le _
    have e₃ : ∃ c₃ k₃, Exec P W (block [.addN d d (d + 1), .constN (d + 1) 1,
        .subN (d + 1) d (d + 1), .subN d d (d + 1)]) c₂ c₃ k₃ ∧ k₃ = 4 ∧
        c₃.nreg d = (c₂.nreg d + c₂.nreg (d + 1)) - (c₂.nreg d + c₂.nreg (d + 1) - 1) := by
      exec_block
      · omega
      · omega
      · refine ⟨rfl, ?_⟩
        simp [upd]
    obtain ⟨c₃, k₃, e₃, hk₃, v₃⟩ := e₃
    have ex : Exec P W ((or f g).compile d) c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
    refine ⟨c₃, _, ex, by sio only [size], ?_, exec_frameB ex (wr_compile (or f g) d)⟩
    rw [v₃, d₂, v₁, v₂]
    have hg : (g.eval fun r => decide (c₁.nreg r = 1)) = g.eval fun r => decide (c.nreg r = 1) :=
      eval_congr (p := fun r => r < d ∧ c.nreg r ≤ 1) (fun r hr => by rw [keep r hr.1]) hv.2
    rw [hg]
    simp only [eval]
    cases f.eval _ <;> cases g.eval _ <;> rfl
where
  /-- The value depends only on the variables. -/
  eval_congr {v v' : ℕ → Bool} {p : ℕ → Prop} {f : BF} (h : ∀ r, p r → v r = v' r)
      (hf : f.VarsOK p) : f.eval v = f.eval v' := by
    induction f with
    | var r => exact h r hf
    | const b => rfl
    | not f ih => simp only [eval, ih hf]
    | and f g ihf ihg => simp only [eval, ihf hf.1, ihg hf.2]
    | or f g ihf ihg => simp only [eval, ihf hf.1, ihg hf.2]

end BF

end

end SweepPrim

end Chazelle.Core
