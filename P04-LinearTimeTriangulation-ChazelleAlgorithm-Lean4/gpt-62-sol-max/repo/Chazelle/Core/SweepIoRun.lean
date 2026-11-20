module

public import Chazelle.Core.RunSpec

public import Chazelle.Programs.RamSimp

public import Chazelle.Core.SweepRamStage0

/-!
# The sweep RAM (WP-D), answers: run steps

The answer stage of the sweep works in band `bSweep` from register `sw 700` on (scratch) and in
the oracle bands; the registers `sw 0 … 699` (inputs, stage 0, the outputs of stages 2/3 and the
constants of the answer stage) are fixed.  After its initialisation (configuration `c₀`) every
intermediate configuration `c` satisfies `IInv`: the fixed registers are unchanged, the allocator
has not decreased, and the memory below `c₀`'s allocator is unchanged.

`IRS P W c₀ s c K Q`: from `c`, the statement `s` runs in at most `K` steps to a configuration
satisfying `IInv` and `Q`, within the relative frame `IFr` (registers outside `ioBands`
unchanged, nothing emitted, the allocator raised by at most the step count).  Combinators:
`IRS.seq`, `IRS.ifT`, `IRS.ifF`, `IRS.skip`, `IRS.while`, `IRS.block` (straight-line register
code, `regB`), `IRS.store` (a store above `c₀`'s allocator), `IRS.call` (a statement with a
`Meets` contract writing only `ioBands` and the scratch).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam

@[expose] public section

/-! ## Registers and bands -/

/-- The bands of the sweep (and of the procedures it inlines). -/
@[ram_layout] def ioBands : Finset ℕ := sweepBands ∪ oracleBands

/-- A fixed register of the answer stage: `sw 0 … 699`. -/
@[ram_layout] def IFix (q : ℕ) : Prop := 240000 ≤ q ∧ q < 240700

/-- A scratch register of the answer stage: band `bSweep` from `sw 700` on, or an oracle band. -/
@[ram_layout] def IScr (r : ℕ) : Prop := (240700 ≤ r ∧ r < 250000) ∨ bandOf r ∈ oracleBands

theorem band_sw {r : ℕ} (h1 : 240000 ≤ r) (h2 : r < 250000) : bandOf r = bSweep := by
  reg_omega

theorem bSweep_mem : bSweep ∈ ioBands := by decide

theorem oracle_sub : oracleBands ⊆ ioBands := Finset.subset_union_right

theorem alloc_not_io : bandOf ALLOC ∉ ioBands := by decide

theorem fix_not_scr {q : ℕ} (h : IFix q) : ¬ IScr q := by
  rintro (h' | h')
  · unfold IFix at h; omega
  · unfold IFix at h
    ram_rw [band_sw] at h'
    exact absurd h' (by decide)

theorem alloc_not_scr : ¬ IScr ALLOC := by
  rintro (h | h)
  · reg_omega
  · exact absurd h (by decide)

theorem scr_band {r : ℕ} (h : IScr r) : bandOf r ∈ ioBands := by
  rcases h with h | h
  · rw [band_sw (by omega) h.2]; exact bSweep_mem
  · exact oracle_sub h

/-! ## The invariant and the run steps -/

/-- **The invariant of the answer stage** relative to `c₀`. -/
structure IInv (W : ℕ) (c₀ c : Config) : Prop where
  hw : WordsBounded W c
  hin : ∀ q, IFix q → c.nreg q = c₀.nreg q
  hA : c₀.nreg ALLOC ≤ c.nreg ALLOC
  hm : MemEqBelow (c₀.nreg ALLOC) c.nmem c₀.nmem
  hrm : MemEqBelow (c₀.nreg ALLOC) c.rmem c₀.rmem

/-- **The relative frame** of a step: registers outside the bands unchanged (except the
allocator), nothing emitted, the allocator raised by at most the step count. -/
def IFr (c c' : Config) (k : ℕ) : Prop :=
  (∀ r, bandOf r ∉ ioBands → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    (∀ r, bandOf r ∉ ioBands → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k

theorem IFr.refl (c : Config) (k : ℕ) : IFr c c k :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, rfl, le_rfl, by omega⟩

theorem IFr.trans {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : IFr c c₁ k₁) (h₂ : IFr c₁ c₂ k₂) :
    IFr c c₂ (k₁ + k₂) := by
  obtain ⟨r₁, rr₁, o₁, a₁, b₁⟩ := h₁
  obtain ⟨r₂, rr₂, o₂, a₂, b₂⟩ := h₂
  exact ⟨fun r hr hra => (r₂ r hr hra).trans (r₁ r hr hra), fun r hr => (rr₂ r hr).trans (rr₁ r hr),
    o₂.trans o₁, a₁.trans a₂, by omega⟩

theorem IFr.mono {c c' : Config} {k k' : ℕ} (h : IFr c c' k) (hk : k ≤ k') : IFr c c' k' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by have := h.2.2.2.2; omega⟩

theorem IFr.of_frame {B : Finset ℕ} {c c' : Config} {k : ℕ} (h : Frame B c c' k)
    (hB : B ⊆ ioBands) : IFr c c' k :=
  ⟨fun r hr hra => h.1 r (fun h' => hr (hB h')) hra, fun r hr => h.2.1 r (fun h' => hr (hB h')),
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

instance : RunFrame IFr where
  refl c := IFr.refl c 0
  comp := IFr.trans
  pad := IFr.mono
  base_le h := h.2.2.2.1
  base_le_add h := h.2.2.2.2

/-- **A run step of the answer stage.** -/
abbrev IRS (P : Polygon) (W : ℕ) (c₀ : Config) (s : Stmt) (c : Config) (K : ℕ)
    (Q : Config → Prop) : Prop :=
  RunSpec (IInv W c₀) (IFr) P W s c K Q

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem IRS.mono {s : Stmt} {K K' : ℕ} {Q Q' : Config → Prop} (h : IRS P W c₀ s c K Q)
    (hK : K ≤ K') (hQ : ∀ c', Q c' → Q' c') : IRS P W c₀ s c K' Q' :=
  RunSpec.mono h hK hQ

theorem IRS.seq {s t : Stmt} {K₁ K₂ : ℕ} {Q₁ Q₂ : Config → Prop} (h₁ : IRS P W c₀ s c K₁ Q₁)
    (h₂ : ∀ c₁, IInv W c₀ c₁ → c.nreg ALLOC ≤ c₁.nreg ALLOC → c₁.nreg ALLOC ≤ c.nreg ALLOC + K₁ →
      Q₁ c₁ → IRS P W c₀ t c₁ K₂ Q₂) : IRS P W c₀ (.seq s t) c (K₁ + K₂) Q₂ :=
  RunSpec.seq h₁ h₂

section

variable {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
include a b t e K Q

theorem IRS.ifT
    (ht : c.nreg a < c.nreg b) (h : IRS P W c₀ t c K Q) :
    IRS P W c₀ (.ifLtN a b t e) c (K + 2) Q :=
  RunSpec.ifT ht h

theorem IRS.ifF
    (ht : ¬ c.nreg a < c.nreg b) (h : IRS P W c₀ e c K Q) :
    IRS P W c₀ (.ifLtN a b t e) c (K + 2) Q :=
  RunSpec.ifF ht h

theorem IRS.ite
    (ht : c.nreg a < c.nreg b → IRS P W c₀ t c K Q)
    (he : ¬ c.nreg a < c.nreg b → IRS P W c₀ e c K Q) :
    IRS P W c₀ (.ifLtN a b t e) c (K + 2) Q := by
  by_cases h : c.nreg a < c.nreg b
  · exact IRS.ifT h (ht h)
  · exact IRS.ifF h (he h)

end

theorem IRS.skip {K : ℕ} {Q : Config → Prop} (hI : IInv W c₀ c) (hq : Q c) :
    IRS P W c₀ .skip c K Q :=
  RunSpec.skip hI.hw hI hq

/-- A register-only change on scratch registers keeps the invariant. -/
theorem IInv.regs {c' : Config} {k : ℕ} (hI : IInv W c₀ c) (hw : WordsBounded W c')
    (hr : ∀ r, ¬ IScr r → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) : IInv W c₀ c' ∧ IFr c c' k := by
  have hA := hr ALLOC alloc_not_scr
  refine ⟨⟨hw, fun q hq => (hr q (fix_not_scr hq)).trans (hI.hin q hq), by rw [hA]; exact hI.hA,
    fun a ha => by rw [hm]; exact hI.hm a ha, fun a ha => by rw [hrm]; exact hI.hrm a ha⟩,
    fun r hr' _ => hr r (fun h => hr' (scr_band h)), fun r _ => by rw [hrr], ho, by omega,
    by omega⟩

/-- **One register instruction** on a scratch register. -/
theorem IRS.reg {i : Instr} {r v : ℕ} (hI : IInv W c₀ c) (hr : IScr r)
    (hex : Exec P W (.instr i) c { c with nreg := upd c.nreg r v } 1) :
    IRS P W c₀ (.instr i) c 1 (fun c' => c' = { c with nreg := upd c.nreg r v }) := by
  obtain ⟨hI', hfr⟩ := hI.regs (c' := { c with nreg := upd c.nreg r v }) (k := 1) hex.wb_right
    (fun q h => upd_other _ _ _ fun eq => h (eq ▸ hr)) rfl rfl rfl rfl
  exact ⟨_, 1, hex, le_rfl, hI', hfr, rfl⟩

abbrev okI := okRegI IScr
abbrev okB := okRegB IScr

/-- One covered instruction. -/
theorem IRS.instr1 {i : Instr} (hI : IInv W c₀ c) (hi : okI W c.nreg i) :
    IRS P W c₀ (.instr i) c 1 (fun c' => c' = { c with nreg := regI c.nmem i c.nreg }) := by
  have e := Exec.regInstr (P := P) hI.hw hi
  obtain ⟨hI', hf⟩ := hI.regs e.wb_right
    (fun _ h => regI_other _ _ _ fun eq => h (eq ▸ hi.dst)) rfl rfl rfl rfl
  exact ⟨_, 1, e, le_rfl, hI', hf, rfl⟩

/-- **A straight-line block** of register instructions. -/
theorem IRS.block (l : List Instr) {c : Config} (hI : IInv W c₀ c)
    (hok : okB W c.nmem l c.nreg) : IRS P W c₀ (Stmt.block l) c l.length
      (fun c' => c' = { c with nreg := regB c.nmem l c.nreg }) := by
  have e := Exec.regBlock (P := P) hI.hw hok
  obtain ⟨hI', hf⟩ := hI.regs e.wb_right (fun _ h => hok.keeps h) rfl rfl rfl rfl
  exact ⟨_, _, e, le_rfl, hI', hf, rfl⟩

/-- **A store** at an address at or above `c₀`'s allocator. -/
theorem IRS.store {a v : ℕ} (hI : IInv W c₀ c) (ha : c₀.nreg ALLOC ≤ c.nreg a) :
    IRS P W c₀ (.instr (.storeN a v)) c 1
      (fun c' => c' = { c with nmem := upd c.nmem (c.nreg a) (c.nreg v) }) := by
  have ex := Exec.storeN (P := P) hI.hw a v
  refine ⟨_, 1, ex, le_rfl, ⟨ex.wb_right, hI.hin, hI.hA, fun b hb => ?_, hI.hrm⟩,
    ⟨fun _ _ _ => rfl, fun _ _ => rfl, rfl, le_rfl, Nat.le_add_right _ _⟩, rfl⟩
  simp only [upd]
  ram_rw [ite_eq_right]
  exact hI.hm b hb

/-- **A loop**: an invariant `I` and a measure `μ`; each iteration costs at most `Kb` and lowers
`μ`.  The allocator must leave room for all iterations. -/
theorem IRS.while {a b : ℕ} {body : Stmt} (I : Config → Prop) (μ : Config → ℕ) (Kb : ℕ)
    (hpos : ∀ c, I c → c.nreg a < c.nreg b → 0 < μ c)
    (hbody : ∀ c, IInv W c₀ c → I c → c.nreg a < c.nreg b → c.nreg ALLOC + Kb ≤ W →
      IRS P W c₀ body c Kb (fun c' => I c' ∧ μ c' < μ c))
    (hI : IInv W c₀ c) (hc : I c) (hroom : c.nreg ALLOC + (Kb + 2) * μ c ≤ W) :
    IRS P W c₀ (.whileLtN a b body) c ((Kb + 2) * μ c + 2)
      (fun c' => I c' ∧ ¬ c'.nreg a < c'.nreg b) :=
  RunSpec.whileN I μ Kb (fun _ h => h.hw) hpos hbody hI hc hroom

/-- **A call of a statement with a `Meets` contract in the oracle bands**: the fixed registers
are kept by the frame. -/
theorem IRS.callO {s : Stmt} {B' : Finset ℕ} {Pre : Polygon → ℕ → Config → Prop}
    {Post : Polygon → Config → Config → Prop} {cost : Polygon → Config → ℕ}
    (hs : Meets s B' Pre Post cost) (hB : B' ⊆ oracleBands) (hI : IInv W c₀ c)
    (hpre : Pre P W c) (hroom : c.nreg ALLOC + cost P c ≤ W) :
    IRS P W c₀ s c (cost P c) (fun c' => Post P c c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      (MemEqBelow (c.nreg ALLOC) c'.nmem c.nmem) ∧
      ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → c'.nreg r = c.nreg r) := by
  obtain ⟨c', k, ex, hk, hpost, hfr⟩ := hs P W c hI.hw hpre hroom
  have hkeep : ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → c'.nreg r = c.nreg r :=
    fun r hr hra => hfr.1 r (fun h => hr (hB h)) hra
  have hfix : ∀ q, IFix q → c'.nreg q = c.nreg q := fun q hq => hkeep q (by
    unfold IFix at hq; ram_rw [band_sw]; decide) (by reg_omega)
  exact ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq => (hfix q hq).trans (hI.hin q hq),
    le_trans hI.hA hfr.2.2.2.2.2.1,
    fun a ha => (hfr.2.2.1 a (lt_of_lt_of_le ha hI.hA)).trans (hI.hm a ha),
    fun a ha => (hfr.2.2.2.1 a (lt_of_lt_of_le ha hI.hA)).trans (hI.hrm a ha)⟩,
    IFr.of_frame hfr (hB.trans oracle_sub), hpost, hfr.2.2.2.2.2.1, hfr.2.2.1, hkeep⟩

/-- **A run step from an execution** that writes scratch registers, the allocator (raised by at
most the step count) and memory at or above `c₀`'s allocator. -/
theorem IRS.ofExec {s : Stmt} {c' : Config} {k K : ℕ} {Q : Config → Prop} (hI : IInv W c₀ c)
    (ex : Exec P W s c c' k) (hk : k ≤ K)
    (hr : ∀ r, ¬ IScr r → r ≠ ALLOC → c'.nreg r = c.nreg r) (hrr : c'.rreg = c.rreg)
    (hm : MemEqBelow (c₀.nreg ALLOC) c'.nmem c.nmem) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) (hA1 : c.nreg ALLOC ≤ c'.nreg ALLOC)
    (hA2 : c'.nreg ALLOC ≤ c.nreg ALLOC + k) (hq : Q c') : IRS P W c₀ s c K Q :=
  ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq' => (hr q (fix_not_scr hq') (by
      reg_omega)).trans (hI.hin q hq'), le_trans hI.hA hA1,
      fun a ha => (hm a ha).trans (hI.hm a ha), fun a ha => by rw [hrm]; exact hI.hrm a ha⟩,
    ⟨fun r hr' hra => hr r (fun h => hr' (scr_band h)) hra, fun r _ => by rw [hrr], ho, hA1, hA2⟩,
    hq⟩

end

end SweepIo

namespace SweepEv

@[expose] public section

/-! ## The local frame of a sweep component -/

/-- **The frame of a component**: registers outside the oracle bands and the set `X` (and the
allocator) are unchanged, the allocator grows, the memory below it is kept. -/
def EFr (X : ℕ → Prop) (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ X r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (MemEqBelow (c.nreg ALLOC) c'.nmem c.nmem)

theorem EFr.refl (X : ℕ → Prop) (c : Config) : EFr X c c :=
  ⟨fun _ _ _ _ => rfl, le_rfl, fun _ _ => rfl⟩

theorem EFr.trans {X : ℕ → Prop} {c₁ c₂ c₃ : Config} (h₁ : EFr X c₁ c₂) (h₂ : EFr X c₂ c₃) :
    EFr X c₁ c₃ :=
  ⟨fun r a b d => (h₂.1 r a b d).trans (h₁.1 r a b d), h₁.2.1.trans h₂.2.1,
    fun a ha => (h₂.2.2 a (lt_of_lt_of_le ha h₁.2.1)).trans (h₁.2.2 a ha)⟩

theorem EFr.mono {X Y : ℕ → Prop} {c c' : Config} (h : EFr X c c') (hXY : ∀ r, X r → Y r) :
    EFr Y c c' :=
  ⟨fun r a b d => h.1 r a (fun hx => b (hXY r hx)) d, h.2.1, h.2.2⟩


end

end SweepEv

end Chazelle.Core
