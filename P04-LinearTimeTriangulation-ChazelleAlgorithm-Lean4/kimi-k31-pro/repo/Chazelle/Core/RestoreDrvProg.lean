module

public import Chazelle.Core.RestoreFind
public import Chazelle.Core.RestoreRound
public import Chazelle.Core.RestoreCost
public import Chazelle.Core.GranBD
public import Chazelle.UnfoldTactics

/-!
# WP-E, part 6: the restoration driver — the program

`restoreStmt sF sB` runs `d₀ + 1` **rounds**; each round

1. reads the header of the current normal form (handle `H`): `K` chords, `R` regions, the chord
   area `CB`, the region area `RB`;
2. copies the `K` chord triples to a fresh list at `LB` (the allocator, bumped by `3` per chord),
   then reserves `3 R` more words for the new chords;
3. for every region `r` with more than `D` exit chords calls the splitting step `sF`
   (`FindOK`) and appends the chord it returns;
4. builds the normal form of the list with `sB` (`BuildNFSpec`), which becomes the current one.

The output is the last current normal form.  Registers (band `bRestore`):

| register | content |
|---|---|
| `80000` … `80006` | inputs and output of `RestoreSpec` (`0` model, `1` normal form, `2` `d₀`, `3` `D`, `4` `γ`, `5` output, `6` context) |
| `80010`, `80011` | round counter `t`, number of rounds `d₀ + 1` |
| `80012` | current handle `H` |
| `80013` … `80016` | `K`, `R`, `CB`, `RB` |
| `80017`, `80018` | list base `LB`, list length |
| `80019` | degree cap `d₀ + D` passed to `sF` |
| `80020` … `80024` | constants `1, 2, 3, 5, 0` |
| `80030` … `80033` | copy loop: index, source pointer, (unused), scratch |
| `80034` | reservation loop index |
| `80036` | header scratch |
| `80040` … `80043` | region loop: index, pointer to the degree word, degree, destination |
-/

namespace Chazelle.Core

namespace Restore

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## The program -/

/-- Read the header of the current normal form. -/
def headS : Stmt := block [.loadN 80013 80012, .addN 80036 80012 80021, .loadN 80014 80036,
  .addN 80036 80012 80022, .loadN 80015 80036, .addN 80036 80036 80021, .loadN 80016 80036,
  .copyN 80017 ALLOC, .copyN 80031 80015, .constN 80030 0]

/-- Copy one chord triple to the allocator, bumping it by `3`. -/
def copyBody : Stmt := block [.loadN 80033 80031, .storeN ALLOC 80033, .addN ALLOC ALLOC 80020,
  .addN 80031 80031 80020, .loadN 80033 80031, .storeN ALLOC 80033, .addN ALLOC ALLOC 80020,
  .addN 80031 80031 80020, .loadN 80033 80031, .storeN ALLOC 80033, .addN ALLOC ALLOC 80020,
  .addN 80031 80031 80022, .addN 80030 80030 80020]

/-- The copy loop. -/
def copyS : Stmt := .whileLtN 80030 80013 copyBody

/-- Set up the reservation. -/
def midS : Stmt := block [.copyN 80018 80013, .copyN 80043 ALLOC, .constN 80034 0]

/-- Reserve three words (one per step). -/
def resBody : Stmt := block [.addN ALLOC ALLOC 80020, .addN ALLOC ALLOC 80020,
  .addN ALLOC ALLOC 80020, .addN 80034 80034 80020]

/-- The reservation loop (`3 R` words). -/
def resS : Stmt := .whileLtN 80034 80014 resBody

/-- Set up the region loop. -/
def preRegS : Stmt := block [.constN 80040 0, .addN 80041 80016 80021]

/-- The arguments of the splitting step. -/
def argS : Stmt := block [.copyN 81000 80000, .copyN 81001 80012, .copyN 81002 80040,
  .copyN 81003 80004, .copyN 81004 80006, .copyN 81005 80019, .copyN 81006 80003]

/-- Append the returned chord triple. -/
def appS : Stmt := block [.storeN 80043 81008, .addN 80043 80043 80020, .storeN 80043 81009,
  .addN 80043 80043 80020, .storeN 80043 81010, .addN 80043 80043 80020,
  .addN 80018 80018 80020]

/-- Call the splitting step and append its chord if it found one. -/
def callS (sF : Stmt) : Stmt := .seq argS (.seq sF (.ifLtN 80024 81007 appS .skip))

/-- The step of the region loop. -/
def regBody (sF : Stmt) : Stmt :=
  .seq (block [.loadN 80042 80041]) (.seq (.ifLtN 80003 80042 (callS sF) .skip)
    (block [.addN 80041 80041 80023, .addN 80040 80040 80020]))

/-- The region loop. -/
def regS (sF : Stmt) : Stmt := .whileLtN 80040 80014 (regBody sF)

/-- Build the normal form of the list. -/
def buildS (sB : Stmt) : Stmt :=
  .seq (block [.copyN 40000 80000, .copyN 40001 80017, .copyN 40002 80018])
    (.seq sB (block [.copyN 80012 40003]))

/-- One round. -/
def roundBody (sF sB : Stmt) : Stmt :=
  .seq headS (.seq copyS (.seq midS (.seq resS (.seq preRegS (.seq (regS sF)
    (.seq (buildS sB) (block [.addN 80010 80010 80020])))))))

/-- Initialisation. -/
def initS : Stmt := block [.constN 80020 1, .constN 80021 2, .constN 80022 3, .constN 80023 5,
  .constN 80024 0, .copyN 80012 80001, .constN 80010 0, .addN 80011 80002 80020,
  .addN 80019 80002 80003]

/-- **The restoration driver.** -/
def restoreStmt (sF sB : Stmt) : Stmt :=
  .seq initS (.seq (.whileLtN 80010 80011 (roundBody sF sB)) (block [.copyN 80005 80012]))

/-! ## The frame relative to a fixed base -/

/-- **The frame of the driver relative to the base `A₀`**: registers outside the bands
unchanged (except the allocator), memory below `A₀` unchanged, nothing emitted, the allocator
nondecreasing and raised by at most the step count. -/
def RF (bands : Finset ℕ) (A₀ : ℕ) (c c' : Config) (k : ℕ) : Prop :=
  (∀ r, bandOf r ∉ bands → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    (∀ r, bandOf r ∉ bands → c'.rreg r = c.rreg r) ∧
    (∀ a, a < A₀ → c'.nmem a = c.nmem a) ∧
    (∀ a, a < A₀ → c'.rmem a = c.rmem a) ∧
    c'.output = c.output ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k

theorem RF.trans {B : Finset ℕ} {A₀ : ℕ} {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : RF B A₀ c c₁ k₁)
    (h₂ : RF B A₀ c₁ c₂ k₂) : RF B A₀ c c₂ (k₁ + k₂) := by
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := h₁
  obtain ⟨r₂, rr₂, m₂, rm₂, o₂, a₂, b₂⟩ := h₂
  exact ⟨fun r hr hra => (r₂ r hr hra).trans (r₁ r hr hra), fun r hr => (rr₂ r hr).trans (rr₁ r hr),
    fun a ha => (m₂ a ha).trans (m₁ a ha), fun a ha => (rm₂ a ha).trans (rm₁ a ha),
    o₂.trans o₁, a₁.trans a₂, by omega⟩

theorem RF.mono {B B' : Finset ℕ} {A₀ : ℕ} {c c' : Config} {k k' : ℕ} (h : RF B A₀ c c' k)
    (hB : B ⊆ B') (hk : k ≤ k') : RF B' A₀ c c' k' := by
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := h
  exact ⟨fun r hr hra => r₁ r (fun h => hr (hB h)) hra, fun r hr => rr₁ r (fun h => hr (hB h)),
    m₁, rm₁, o₁, a₁, by omega⟩

theorem RF.of_frame {B : Finset ℕ} {A₀ : ℕ} {c c' : Config} {k : ℕ} (h : Frame B c c' k)
    (hA : A₀ ≤ c.nreg ALLOC) : RF B A₀ c c' k := by
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := h
  exact ⟨r₁, rr₁, fun a ha => m₁ a (by omega), fun a ha => rm₁ a (by omega), o₁, a₁, b₁⟩

theorem RF.to_frame {B : Finset ℕ} {c c' : Config} {k : ℕ} (h : RF B (c.nreg ALLOC) c c' k) :
    Frame B c c' k := h

/-- The bands of the driver. -/
def dBands : Finset ℕ := restoreBands ∪ oracleBands

theorem band8 {r : ℕ} (h1 : 80000 ≤ r) (h2 : r < 90000) : bandOf r = bRestore := by
  ufo bandOf bRestore

theorem mem_dBands_8 : bRestore ∈ dBands := by decide

theorem alloc_notin : bandOf ALLOC ∉ dBands := by decide

/-- A register-only change within band `8` is an `RF` step. -/
theorem rf_of_regs {A₀ : ℕ} {c c' : Config} {k : ℕ}
    (hr : ∀ r, (r < 80000 ∨ 90000 ≤ r) → c'.nreg r = c.nreg r) (hrr : c'.rreg = c.rreg)
    (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) :
    RF dBands A₀ c c' k := by
  have hA : c'.nreg ALLOC = c.nreg ALLOC := hr ALLOC (by left; decide)
  refine ⟨fun r hr' _ => hr r ?_, fun r _ => by rw [hrr], fun a _ => by rw [hm],
    fun a _ => by rw [hrm], ho, by omega, by omega⟩
  by_contra hcon
  push Not at hcon
  exact hr' (band8 hcon.1 hcon.2 ▸ mem_dBands_8)

end

end Restore

end Chazelle.Core

namespace Chazelle.Core

namespace Restore

open Machine Machine.Stmt Programs

@[expose] public section

/-- A register-only change within the bands of the driver is an `RF` step. -/
theorem rf_of_regs' {A₀ : ℕ} {c c' : Config} {k : ℕ}
    (hr : ∀ r, bandOf r ∉ dBands → c'.nreg r = c.nreg r) (hrr : c'.rreg = c.rreg)
    (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) :
    RF dBands A₀ c c' k := by
  have hA  := hr ALLOC alloc_notin
  exact ⟨fun r hr' _ => hr r hr', fun r _ => by rw [hrr], fun a _ => by rw [hm],
    fun a _ => by rw [hrm], ho, by omega, by omega⟩

theorem RF.refl {B : Finset ℕ} {A₀ : ℕ} (c : Config) (k : ℕ) : RF B A₀ c c k :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, le_rfl, by omega⟩

/-- **A loop with a bounded body keeps the relative frame.** -/
theorem whileLtN_frame {P : Polygon} {W : ℕ} {a b : ℕ} {body : Stmt} {B : Finset ℕ} {A₀ : ℕ}
    (I : Config → Prop) (μ : Config → ℕ) (Kb : ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ RF B A₀ c c' k ∧ k ≤ Kb ∧ μ c' < μ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      RF B A₀ c c' k ∧ k ≤ (Kb + 2) * μ c + 2 := by
  induction hn : μ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨c₁, k₁, hb, hI₁, hF₁, hk₁, hμ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hF₂, hk₂⟩ := ih (μ c₁) (by omega) hI₁ rfl
      refine ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht',
        (hF₁.trans hF₂).mono subset_rfl (by omega), ?_⟩
      have : (Kb + 2) * (μ c₁ + 1) ≤ (Kb + 2) * n := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    · exact ⟨c, 2, .whileLtN_false ht (hI c hc), hc, ht, RF.refl c 2, by omega⟩

end

end Restore

end Chazelle.Core
