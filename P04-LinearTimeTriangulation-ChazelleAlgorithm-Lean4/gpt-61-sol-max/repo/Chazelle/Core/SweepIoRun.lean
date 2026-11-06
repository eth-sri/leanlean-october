module

public meta import Chazelle.Arithmetic

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

/-! ## Straight-line register code -/

/-- The register effect of a straight-line register instruction (memory `m`). -/
def regI (m : ℕ → ℕ) : Instr → (ℕ → ℕ) → (ℕ → ℕ)
  | .constN r k, f => upd f r k
  | .copyN r a, f => upd f r (f a)
  | .addN r a b, f => upd f r (f a + f b)
  | .subN r a b, f => upd f r (f a - f b)
  | .loadN r a, f => upd f r (m (f a))
  | _, f => f

/-- The register effect of a block. -/
def regB (m : ℕ → ℕ) : List Instr → (ℕ → ℕ) → (ℕ → ℕ)
  | [], f => f
  | i :: l, f => regB m l (regI m i f)

/-- The destination register of a covered instruction. -/
def dstI : Instr → ℕ
  | .constN r _ => r
  | .copyN r _ => r
  | .addN r _ _ => r
  | .subN r _ _ => r
  | .loadN r _ => r
  | _ => 0

theorem regI_other (m f : ℕ → ℕ) (i : Instr) {q : ℕ} (hq : dstI i ≠ q) :
    regI m i f q = f q := by
  cases i <;> aesop <;> exact upd_other _ _ _ (Ne.symm hq)

/-- **A block leaves the registers it does not write.** -/
theorem regB_other (m : ℕ → ℕ) : ∀ (l : List Instr) (f : ℕ → ℕ) {q : ℕ},
    (∀ i ∈ l, dstI i ≠ q) → regB m l f q = f q
  | [], _, _, _ => rfl
  | i :: l, f, q, h => by
    rw [regB, regB_other m l _ (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    exact regI_other m f i (h i List.mem_cons_self)

/-! ## Registers and bands -/

/-- The bands of the sweep (and of the procedures it inlines). -/
def ioBands : Finset ℕ := sweepBands ∪ oracleBands

/-- A fixed register of the answer stage: `sw 0 … 699`. -/
def IFix (q : ℕ) : Prop := 240000 ≤ q ∧ q < 240700

/-- A scratch register of the answer stage: band `bSweep` from `sw 700` on, or an oracle band. -/
def IScr (r : ℕ) : Prop := (240700 ≤ r ∧ r < 250000) ∨ bandOf r ∈ oracleBands

theorem band_sw {r : ℕ} (h1 : 240000 ≤ r) (h2 : r < 250000) : bandOf r = bSweep := by
  omega_nf

theorem bSweep_mem : bSweep ∈ ioBands := by decide

theorem oracle_sub : oracleBands ⊆ ioBands := Finset.subset_union_right

theorem alloc_not_io : bandOf ALLOC ∉ ioBands := by decide

theorem fix_not_scr {q : ℕ} (h : IFix q) : ¬ IScr q := by
  rintro (h' | h')
  · omega_nf
  · unfold IFix at h
    rw [band_sw (by omega) (by omega)] at h'
    exact absurd h' (by decide)

theorem alloc_not_scr : ¬ IScr ALLOC := by
  rintro (h | h)
  · omega_nf
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
  hm : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a
  hrm : ∀ a, a < c₀.nreg ALLOC → c.rmem a = c₀.rmem a

/-- **The relative frame** of a step: registers outside the bands unchanged (except the
allocator), nothing emitted, the allocator raised by at most the step count. -/
def IFr (c c' : Config) (k : ℕ) : Prop :=
  (∀ r, bandOf r ∉ ioBands → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    (∀ r, bandOf r ∉ ioBands → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k

theorem IFr.refl (c : Config) (k : ℕ) : IFr c c k :=
  by core_grind

theorem IFr.trans {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : IFr c c₁ k₁) (h₂ : IFr c₁ c₂ k₂) :
    IFr c c₂ (k₁ + k₂) := by
  core_grind

theorem IFr.mono {c c' : Config} {k k' : ℕ} (h : IFr c c' k) (hk : k ≤ k') : IFr c c' k' :=
  by core_grind

theorem IFr.of_frame {B : Finset ℕ} {c c' : Config} {k : ℕ} (h : Frame B c c' k)
    (hB : B ⊆ ioBands) : IFr c c' k :=
  ⟨fun r hr hra => h.1 r (fun h' => hr (hB h')) hra, fun r hr => h.2.1 r (fun h' => hr (hB h')),
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- **A run step of the answer stage.** -/
def IRS (P : Polygon) (W : ℕ) (c₀ : Config) (s : Stmt) (c : Config) (K : ℕ)
    (Q : Config → Prop) : Prop :=
  ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ IInv W c₀ c' ∧ IFr c c' k ∧ Q c'

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem IRS.mono {s : Stmt} {K K' : ℕ} {Q Q' : Config → Prop} (h : IRS P W c₀ s c K Q)
    (hK : K ≤ K') (hQ : ∀ c', Q c' → Q' c') : IRS P W c₀ s c K' Q' := by
  core_grind

theorem IRS.seq {s t : Stmt} {K₁ K₂ : ℕ} {Q₁ Q₂ : Config → Prop} (h₁ : IRS P W c₀ s c K₁ Q₁)
    (h₂ : ∀ c₁, IInv W c₀ c₁ → c.nreg ALLOC ≤ c₁.nreg ALLOC → c₁.nreg ALLOC ≤ c.nreg ALLOC + K₁ →
      Q₁ c₁ → IRS P W c₀ t c₁ K₂ Q₂) : IRS P W c₀ (.seq s t) c (K₁ + K₂) Q₂ := by
  obtain ⟨c₁, k₁, e₁, hk₁, hI₁, hfr₁, hq₁⟩ := h₁
  obtain ⟨c', k₂, e₂, hk₂, hI', hfr₂, hq⟩ := h₂ c₁ hI₁ hfr₁.2.2.2.1
    (by ram_grind) hq₁
  exact ⟨c', k₁ + k₂, .seq e₁ e₂, by omega, hI', hfr₁.trans hfr₂, hq⟩

section
variable {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop}
theorem IRS.ifT
    (ht : c.nreg a < c.nreg b) (h : IRS P W c₀ t c K Q) :
    IRS P W c₀ (.ifLtN a b t e) c (K + 2) Q := by
  obtain ⟨c', k, ex, hk, hI, hfr, hq⟩ := h
  exact ⟨c', k + 1, .ifLtN_true ht ex, by omega, hI, hfr.mono (by omega), hq⟩

theorem IRS.ifF
    (ht : ¬ c.nreg a < c.nreg b) (h : IRS P W c₀ e c K Q) :
    IRS P W c₀ (.ifLtN a b t e) c (K + 2) Q := by
  obtain ⟨c', k, ex, hk, hI, hfr, hq⟩ := h
  exact ⟨c', k + 2, .ifLtN_false ht ex, by omega, hI, hfr.mono (by omega), hq⟩

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
  ⟨c, 0, .skip hI.hw, by omega, hI, IFr.refl c 0, hq⟩

/-- A register-only change on scratch registers keeps the invariant. -/
theorem IInv.regs {c' : Config} {k : ℕ} (hI : IInv W c₀ c) (hw : WordsBounded W c')
    (hr : ∀ r, ¬ IScr r → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) : IInv W c₀ c' ∧ IFr c c' k := by
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hr ALLOC alloc_not_scr
  refine ⟨⟨hw, fun q hq => (hr q (fix_not_scr hq)).trans (hI.hin q hq), by ram_grind,
    fun a ha => by ram_grind, fun a ha => by ram_grind⟩,
    fun r hr' _ => hr r (fun h => hr' (scr_band h)), fun r _ => by rw [hrr], ho, by omega,
    by omega⟩

/-- **One register instruction** on a scratch register. -/
theorem IRS.reg {i : Instr} {r v : ℕ} (hI : IInv W c₀ c) (hr : IScr r)
    (hex : Exec P W (.instr i) c { c with nreg := upd c.nreg r v } 1) :
    IRS P W c₀ (.instr i) c 1 (fun c' => c' = { c with nreg := upd c.nreg r v }) := by
  obtain ⟨hI', hfr⟩ := hI.regs (c' := { c with nreg := upd c.nreg r v }) (k := 1) hex.wb_right
    (fun q h => by
      ram_all <;> ram_grind) rfl rfl rfl rfl
  ram_grind

/-- An instruction the block lemma covers: a register instruction writing a scratch register,
with its value within the word bound. -/
def okI (W : ℕ) (f : ℕ → ℕ) : Instr → Prop
  | .constN r k => IScr r ∧ k ≤ W
  | .copyN r _ => IScr r
  | .addN r a b => IScr r ∧ f a + f b ≤ W
  | .subN r _ _ => IScr r
  | .loadN r _ => IScr r
  | _ => False

/-- The side conditions of a block, along its run. -/
def okB (W : ℕ) (m : ℕ → ℕ) : List Instr → (ℕ → ℕ) → Prop
  | [], _ => True
  | i :: l, f => okI W f i ∧ okB W m l (regI m i f)

/-- One covered instruction. -/
theorem IRS.instr1 {i : Instr} (hI : IInv W c₀ c) (hi : okI W c.nreg i) :
    IRS P W c₀ (.instr i) c 1 (fun c' => c' = { c with nreg := regI c.nmem i c.nreg }) := by
  cases i with
  | constN r k => exact IRS.reg hI hi.1 (Exec.constN hI.hw r k hi.2)
  | copyN r a => exact IRS.reg hI hi (Exec.copyN hI.hw r a)
  | addN r a b => exact IRS.reg hI hi.1 (Exec.addN hI.hw r a b hi.2)
  | subN r a b => exact IRS.reg hI hi (Exec.subN hI.hw r a b)
  | loadN r a => exact IRS.reg hI hi (Exec.loadN hI.hw r a)
  | _ => ram_grind

/-- **A straight-line block** of register instructions. -/
theorem IRS.block : ∀ (l : List Instr) {c : Config}, IInv W c₀ c →
    okB W c.nmem l c.nreg →
    IRS P W c₀ (Stmt.block l) c l.length
      (fun c' => c' = { c with nreg := regB c.nmem l c.nreg })
  | [], c, hI, _ => IRS.skip hI rfl
  | i :: l, c, hI, hok => by
    obtain ⟨hi, hl⟩ := hok
    have h := IRS.seq (IRS.instr1 (P := P) hI hi) (fun c₁ hI₁ _ _ h₁ => by
      subst h₁
      exact IRS.block l hI₁ hl)
    simp only [List.length_cons]
    rw [Nat.add_comm]
    ram_all

/-- **A store** at an address at or above `c₀`'s allocator. -/
theorem IRS.store {a v : ℕ} (hI : IInv W c₀ c) (ha : c₀.nreg ALLOC ≤ c.nreg a) :
    IRS P W c₀ (.instr (.storeN a v)) c 1
      (fun c' => c' = { c with nmem := upd c.nmem (c.nreg a) (c.nreg v) }) := by
  have ex := Exec.storeN (P := P) hI.hw a v
  refine ⟨_, 1, ex, le_rfl, ⟨ex.wb_right, hI.hin, hI.hA, fun b hb => ?_, hI.hrm⟩,
    ⟨fun _ _ _ => rfl, fun _ _ => rfl, rfl, le_rfl, Nat.le_add_right _ _⟩, rfl⟩
  simp only [upd]
  rw [ite_eq_right (by omega)]
  ram_grind

/-- **A loop**: an invariant `I` and a measure `μ`; each iteration costs at most `Kb` and lowers
`μ`.  The allocator must leave room for all iterations. -/
theorem IRS.while {a b : ℕ} {body : Stmt} (I : Config → Prop) (μ : Config → ℕ) (Kb : ℕ)
    (hpos : ∀ c, I c → c.nreg a < c.nreg b → 0 < μ c)
    (hbody : ∀ c, IInv W c₀ c → I c → c.nreg a < c.nreg b → c.nreg ALLOC + Kb ≤ W →
      IRS P W c₀ body c Kb (fun c' => I c' ∧ μ c' < μ c))
    (hI : IInv W c₀ c) (hc : I c) (hroom : c.nreg ALLOC + (Kb + 2) * μ c ≤ W) :
    IRS P W c₀ (.whileLtN a b body) c ((Kb + 2) * μ c + 2)
      (fun c' => I c' ∧ ¬ c'.nreg a < c'.nreg b) := by
  induction hn : μ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · have hμ : 0 < μ c := hpos c hc ht
      obtain ⟨c₁, k₁, e₁, hk₁, hI₁, hfr₁, hc₁, hμ₁⟩ := hbody c hI hc ht (by
        have : Kb ≤ (Kb + 2) * μ c := by nlinarith
        omega)
      have hA₁ := hfr₁.2.2.2.2
      have hroom₁ : c₁.nreg ALLOC + (Kb + 2) * μ c₁ ≤ W := by
        have : (Kb + 2) * (μ c₁ + 1) ≤ (Kb + 2) * μ c := Nat.mul_le_mul_left _ hμ₁
        grind
      obtain ⟨c', k₂, e₂, hk₂, hI', hfr₂, hq⟩ := ih (μ c₁) (by omega) hI₁ hc₁ hroom₁ rfl
      refine ⟨c', k₁ + 2 + k₂, .whileLtN_true ht e₁ e₂, ?_, hI',
        (hfr₁.trans hfr₂).mono (by omega), hq⟩
      have : (Kb + 2) * (μ c₁ + 1) ≤ (Kb + 2) * n := Nat.mul_le_mul_left _ (by omega)
      grind
    · exact ⟨c, 2, .whileLtN_false ht hI.hw, by omega, hI, IFr.refl c 2, hc, ht⟩

/-- **A call of a statement with a `Meets` contract in the oracle bands**: the fixed registers
are kept by the frame. -/
theorem IRS.callO {s : Stmt} {B' : Finset ℕ} {Pre : Polygon → ℕ → Config → Prop}
    {Post : Polygon → Config → Config → Prop} {cost : Polygon → Config → ℕ}
    (hs : Meets s B' Pre Post cost) (hB : B' ⊆ oracleBands) (hI : IInv W c₀ c)
    (hpre : Pre P W c) (hroom : c.nreg ALLOC + cost P c ≤ W) :
    IRS P W c₀ s c (cost P c) (fun c' => Post P c c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → c'.nreg r = c.nreg r) := by
  obtain ⟨c', k, ex, hk, hpost, hfr⟩ := hs P W c hI.hw hpre hroom
  have hkeep : ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → c'.nreg r = c.nreg r :=
    fun r hr hra => hfr.1 r (fun h => hr (hB h)) hra
  have hfix : ∀ q, IFix q → c'.nreg q = c.nreg q := fun q hq => hkeep q (by
    unfold IFix at hq; rw [band_sw (by omega) (by omega)]; decide) (by omega_nf)
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
    (hm : ∀ a, a < c₀.nreg ALLOC → c'.nmem a = c.nmem a) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) (hA1 : c.nreg ALLOC ≤ c'.nreg ALLOC)
    (hA2 : c'.nreg ALLOC ≤ c.nreg ALLOC + k) (hq : Q c') : IRS P W c₀ s c K Q :=
  ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq' => (hr q (fix_not_scr hq') (by
      omega_nf)).trans (hI.hin q hq'), le_trans hI.hA hA1,
      fun a ha => (hm a ha).trans (hI.hm a ha), fun a ha => by ram_grind⟩,
    ⟨fun r hr' hra => hr r (fun h => hr' (scr_band h)) hra, fun r _ => by rw [hrr], ho, hA1, hA2⟩,
    hq⟩

end

end SweepIo

end Chazelle.Core
