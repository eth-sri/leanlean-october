module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SpecRam
public import Chazelle.Core.SignKernelRam

/-!
# WP-C (BuildNF), RAM part 0: renaming registers

A statement written for one register band can run in another: `Stmt.ren f` applies an
involution `f` of the register numbers to every register argument (natural and real), and an
execution of `s` from `c` becomes an execution of `s.ren f` from `cfgRen f c`, the configuration
whose register `f r` holds what `c` holds in `r` (`Exec.ren`).  Memory, the output and the costs
are unchanged.

`σ` swaps `40000 … 40999 ↔ 50000 … 50999` and `41000 … 41999 ↔ 90000 … 90999`: it moves the
double-identification routines (band `bLocate`) and the parameter test of the granularity
procedure (band `bGran`) into the band `bBuild` of `BuildNF`, keeping the sign kernel (band
`bSign`) and the allocator in place.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt

@[expose] public section

/-- Rename the registers of an instruction. -/
def Instr.ren (f : ℕ → ℕ) : Instr → Instr
  | .halt => .halt
  | .inputSize r => .inputSize (f r)
  | .constN r k => .constN (f r) k
  | .copyN r a => .copyN (f r) (f a)
  | .addN r a b => .addN (f r) (f a) (f b)
  | .subN r a b => .subN (f r) (f a) (f b)
  | .loadN r a => .loadN (f r) (f a)
  | .storeN a r => .storeN (f a) (f r)
  | .constR r z => .constR (f r) z
  | .copyR r a => .copyR (f r) (f a)
  | .addR r a b => .addR (f r) (f a) (f b)
  | .subR r a b => .subR (f r) (f a) (f b)
  | .mulR r a b => .mulR (f r) (f a) (f b)
  | .divR r a b => .divR (f r) (f a) (f b)
  | .loadR r a => .loadR (f r) (f a)
  | .storeR a r => .storeR (f a) (f r)
  | .readX r a => .readX (f r) (f a)
  | .readY r a => .readY (f r) (f a)
  | .jump l => .jump l
  | .brLtN a b l => .brLtN (f a) (f b) l
  | .brLtR a b l => .brLtR (f a) (f b) l
  | .emit a b d => .emit (f a) (f b) (f d)

/-- Rename the registers of a statement. -/
def Stmt.ren (f : ℕ → ℕ) : Stmt → Stmt
  | .skip => .skip
  | .instr i => .instr (Instr.ren f i)
  | .seq s t => .seq (Stmt.ren f s) (Stmt.ren f t)
  | .ifLtN a b t e => .ifLtN (f a) (f b) (Stmt.ren f t) (Stmt.ren f e)
  | .ifLtR a b t e => .ifLtR (f a) (f b) (Stmt.ren f t) (Stmt.ren f e)
  | .whileLtN a b s => .whileLtN (f a) (f b) (Stmt.ren f s)
  | .whileLtR a b s => .whileLtR (f a) (f b) (Stmt.ren f s)

/-- The configuration seen through the renaming: register `f r` holds what `c` holds in `r`
(for an involution `f`). -/
def cfgRen (f : ℕ → ℕ) (c : Config) : Config :=
  { c with nreg := fun r => c.nreg (f r), rreg := fun r => c.rreg (f r) }

variable {f : ℕ → ℕ}

theorem upd_ren {α : Type} (hf : ∀ r, f (f r) = r) (g : ℕ → α) (i : ℕ) (v : α) :
    (fun r => upd g i v (f r)) = upd (fun r => g (f r)) (f i) v := by
  aesop (add simp [upd_apply]) (add safe (by omega))

section
variable (hf : ∀ r, f (f r) = r) (c : Config)
include hf
theorem cfgRen_cfgRen : cfgRen f (cfgRen f c) = c := by
  simp_all [cfgRen] <;> omega_nf

theorem wordsBounded_ren {W : ℕ} :
    WordsBounded W (cfgRen f c) ↔ WordsBounded W c := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun r => ?_, h2⟩
    have := h1 (f r); simp_all [cfgRen] <;> omega_nf
  · rintro ⟨h1, h2⟩; exact ⟨fun r => h1 _, h2⟩


end

theorem isStraight_ren {ins : Instr} (h : ins.IsStraight) : (Instr.ren f ins).IsStraight := by
  cases ins <;> aesop

section
variable (hf : ∀ r, f (f r) = r) {P : Polygon}
include hf
theorem effect_ren {ins : Instr} {c c' : Config}
    (h : ins.effect P c = some c') :
    (Instr.ren f ins).effect P (cfgRen f c) = some (cfgRen f c') := by
  cases ins <;> simp only [Instr.effect, Instr.ren, Option.some.injEq, reduceCtorEq] at h ⊢ <;>
    (try split at h) <;> (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    (try subst h) <;> simp_all [cfgRen, upd_ren hf]

/-- **Renaming registers preserves executions.** -/
theorem Exec.ren {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) : Exec P W (Stmt.ren f s) (cfgRen f c) (cfgRen f c') k := by
  induction h with
  | skip hw => exact .skip ((wordsBounded_ren hf _).2 hw)
  | instr hs he hw hw' =>
    exact .instr (isStraight_ren hs) (effect_ren hf he) ((wordsBounded_ren hf _).2 hw)
      ((wordsBounded_ren hf _).2 hw')
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifLtN_true ht _ ih => exact .ifLtN_true (by grind [cfgRen]) ih
  | ifLtN_false ht _ ih => exact .ifLtN_false (by grind [cfgRen]) ih
  | ifLtR_true ht _ ih => exact .ifLtR_true (by grind [cfgRen]) ih
  | ifLtR_false ht _ ih => exact .ifLtR_false (by grind [cfgRen]) ih
  | whileLtN_false ht hw =>
    exact .whileLtN_false (by grind [cfgRen]) ((wordsBounded_ren hf _).2 hw)
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true (by grind [cfgRen]) ih₁ ih₂
  | whileLtR_false ht hw =>
    exact .whileLtR_false (by grind [cfgRen]) ((wordsBounded_ren hf _).2 hw)
  | whileLtR_true ht _ _ ih₁ ih₂ => exact .whileLtR_true (by grind [cfgRen]) ih₁ ih₂

/-- **Running a renamed statement**: an execution of `s` from the renamed view of `d` gives an
execution of `s.ren f` from `d`. -/
theorem exec_of_ren {W : ℕ} {s : Stmt} {d c' : Config}
    {k : ℕ} (h : Exec P W s (cfgRen f d) c' k) :
    Exec P W (Stmt.ren f s) d (cfgRen f c') k := by
  have := Exec.ren hf h
  rwa [cfgRen_cfgRen hf] at this

/-! ## Write sets -/


end

open SignK (wr wrOK)

section
variable {B B' : ℕ → Bool} (hB : ∀ r, B r = true → B' r = true)
include hB
theorem wrOK_mono {i : Instr}
    (h : wrOK B i = true) : wrOK B' i = true := by
  cases i <;> aesop

/-- A larger write set. -/
theorem wr_mono {s : Stmt}
    (h : wr B s = true) : wr B' s = true := by
  induction s <;> simp_all [wr, wrOK_mono hB]


end

theorem wrOK_ren {f : ℕ → ℕ} (_hf : ∀ r, f (f r) = r) (B : ℕ → Bool) (i : Instr) :
    wrOK B (Instr.ren f i) = wrOK (fun r => B (f r)) i := by
  cases i <;> aesop

theorem wr_ren {f : ℕ → ℕ} (hf : ∀ r, f (f r) = r) (B : ℕ → Bool) (s : Stmt) :
    wr B (Stmt.ren f s) = wr (fun r => B (f r)) s := by
  induction s <;> simp_all [wr, Stmt.ren, wrOK_ren hf]

/-! ## The swap of bands used by `BuildNF` -/

/-- The involution: `40000 … 40999 ↔ 50000 … 50999`, `41000 … 41999 ↔ 90000 … 90999`. -/
def σ (r : ℕ) : ℕ :=
  if 40000 ≤ r ∧ r < 41000 then r + 10000
  else if 50000 ≤ r ∧ r < 51000 then r - 10000
  else if 41000 ≤ r ∧ r < 42000 then r + 49000
  else if 90000 ≤ r ∧ r < 91000 then r - 49000
  else r

theorem σ_σ (r : ℕ) : σ (σ r) = r := by
  unfold σ; ram_grind

/-- The renamed view: register `r` of the view holds register `σ r`. -/
theorem cfgRen_nreg (c : Config) (r : ℕ) : (cfgRen σ c).nreg r = c.nreg (σ r) := rfl

end

end BuildRam

end Chazelle.Core
