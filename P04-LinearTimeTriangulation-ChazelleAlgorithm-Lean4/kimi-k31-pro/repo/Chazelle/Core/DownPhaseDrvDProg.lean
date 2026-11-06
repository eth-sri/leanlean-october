module

public import Chazelle.Core.DownPhaseDrvRSplH
public import Chazelle.Core.NFBuildCmpRam

/-!
# Down-phase restoration rounds (D8), part 4: the program

`roundsS sF sB` runs `d₀` rounds (`d₀` in `r216000`) on the level state (`DrvR.StateAt`:
registers `210001 … 210005` of `bDownDrv`); `sF` is a splitting step (`Restore.FindOK`), `sB` a
sorted build (`DrvR.SortedMeets`).  A round

1. reads the header of the current normal form `N` (`r210005`): `A` arcs, `R` regions, the arc,
   region and list areas;
2. reserves `3 R` words for the new triples `L₂` and `2 R` words for the buckets at the allocator;
3. visits the regions `r < R`; for a region with more than `4` exit chords it calls `sF` (degree
   cap `d₀`, target `4`, weight bound `γ = r216001`, context `coreReg 1`) and, if a chord is
   found, appends its triple and, for each of its two ends `x`, scans the arcs of `r` (`scanS`:
   two key decisions `BuildRam.halfS` per arc) for the bucket of `x` (`DrvD.bktB`);
4. passes `L₂` and the buckets to the splice `DrvR.splS sB` (buckets `≤ A`, at most `2` codes
   each), which writes the new state.

Registers of `bDownDrv` (`216000 + i`):

| `i` | content |
|---|---|
| `0`, `1` | inputs `d₀`, `γ` |
| `2 … 6` | constants `1, 0, 4, 2, 5` |
| `10` | round counter |
| `12 … 17` | handle `H`, `R`, arc base `AB`, region base `RB`, list base `LB`, `A` |
| `18 … 23` | `L₂` base, bucket base, `q` (new chords), `L₂` and bucket write pointers, reservation counter |
| `30 … 34` | region `r`, pointer `RB + 5 r + 2`, degree, scratch, arc-list offset |
| `40 … 46` | scan: end `x` (edge, height code), number of arcs of `r`, arc-list pointer, index `t`, arc `j`, `AB + 5 j` |
| `53 … 55` | bucket, `j + 1`, scratch |

The key decisions use `42100 … 42109` of `bBuild` and the model descriptor in `r40000`.
-/

namespace Chazelle.Core

namespace DrvD

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- Constants and the round counter. -/
def initS : Stmt := block [.constN 216002 1, .constN 216003 0, .constN 216004 4,
  .constN 216005 2, .constN 216006 5, .constN 216010 0]

/-- The header of the current normal form; the bases of `L₂`. -/
def hdS : Stmt := block [.copyN 216012 210005, .addN 216033 216012 216002, .loadN 216017 216033,
  .addN 216033 216033 216002, .loadN 216013 216033, .addN 216033 216033 216005,
  .loadN 216014 216033, .addN 216033 216033 216002, .loadN 216015 216033,
  .addN 216033 216033 216005, .loadN 216016 216033, .copyN 216018 9999, .copyN 216021 9999,
  .constN 216020 0, .constN 216023 0]

/-- Reserve five words. -/
def resBody : Stmt := block [.addN 9999 9999 216002, .addN 9999 9999 216002,
  .addN 9999 9999 216002, .addN 9999 9999 216002, .addN 9999 9999 216002,
  .addN 216023 216023 216002]

/-- The reservation loop (`5 R` words). -/
def resS : Stmt := .whileLtN 216023 216013 resBody

/-- The bucket base `L₂ base + 3 R`; the region loop set-up. -/
def midS : Stmt := block [.addN 216033 216013 216013, .addN 216033 216033 216013,
  .addN 216019 216018 216033, .copyN 216022 216019, .constN 216030 0, .addN 216031 216015 216005]

/-! ## The arc scan -/

/-- Load arc `j` (the `t`-th arc of the region) and the end `x` into the key-decision registers. -/
def ldArc : Stmt := block [.addN 216055 216043 216044, .loadN 216045 216055,
  .addN 216046 216045 216045, .addN 216046 216046 216046, .addN 216046 216046 216045,
  .addN 216046 216046 216014, .addN 216055 216046 216002, .loadN 42102 216055,
  .addN 216055 216055 216002, .loadN 42103 216055, .addN 216055 216055 216002,
  .loadN 42104 216055, .addN 216055 216055 216002, .loadN 42105 216055, .copyN 42100 216040,
  .copyN 42101 216041, .addN 216054 216045 216002]

/-- The decision on arc `j`: `t₁ = r42107`, `t₂ = r42109` (`DrvD.matchB`, `DrvD.bktB`). -/
def decS : Stmt :=
  .ifLtN 216054 216017
    (.ifLtN 216003 42107 (.ifLtN 216003 42109 (.instr (.copyN 216053 216054)) .skip) .skip)
    (.ifLtN 216003 42109 (.instr (.constN 216053 0))
      (.ifLtN 216003 42107 (.instr (.copyN 216053 216017)) .skip))

/-- One arc of the scan. -/
def scanBody : Stmt :=
  .seq ldArc (.seq (BuildRam.halfS 42100 42101 42102 42103 42106 42107)
    (.seq (BuildRam.halfS 42104 42105 42100 42101 42108 42109)
      (.seq decS (block [.addN 216044 216044 216002]))))

/-- **The arc scan** of the end `x = (r216040, r216041)` over the arcs of the region. -/
def scanS : Stmt := .seq (.instr (.constN 216044 0)) (.whileLtN 216044 216042 scanBody)

/-! ## The call of the splitting step -/

/-- The arguments of the splitting step. -/
def argS : Stmt := block [.copyN 81000 210001, .copyN 81001 216012, .copyN 81002 216030,
  .copyN 81003 216001, .copyN 81004 230001, .copyN 81005 216000, .copyN 81006 216004]

/-- Append the triple; the region data of the scans; the left end. -/
def appT : Stmt := block [.storeN 216021 81008, .addN 216021 216021 216002,
  .storeN 216021 81009, .addN 216021 216021 216002, .storeN 216021 81010,
  .addN 216021 216021 216002, .addN 216020 216020 216002, .subN 216033 216031 216005,
  .loadN 216042 216033, .addN 216033 216033 216002, .loadN 216034 216033,
  .addN 216043 216016 216034, .addN 216041 81008 216002, .copyN 40000 210001,
  .copyN 216040 81009]

/-- Store a bucket. -/
def stB : Stmt := block [.storeN 216022 216053, .addN 216022 216022 216002]

/-- Append the chord and the buckets of its two ends. -/
def appS : Stmt :=
  .seq appT (.seq scanS (.seq stB (.seq (.instr (.copyN 216040 81010)) (.seq scanS stB))))

/-- Call the splitting step on region `r` and append its chord, if any. -/
def callS (sF : Stmt) : Stmt := .seq argS (.seq sF (.ifLtN 216003 81007 appS .skip))

/-- The step of the region loop. -/
def regBody (sF : Stmt) : Stmt :=
  .seq (.instr (.loadN 216032 216031)) (.seq (.ifLtN 216004 216032 (callS sF) .skip)
    (block [.addN 216031 216031 216006, .addN 216030 216030 216002]))

/-- The region loop. -/
def regS (sF : Stmt) : Stmt := .whileLtN 216030 216013 (regBody sF)

/-! ## A round, and the rounds -/

/-- The arguments of the splice. -/
def splArgs : Stmt := block [.copyN 210020 216018, .copyN 210021 216020, .copyN 210022 216019,
  .copyN 210023 216017, .copyN 210024 216005]

/-- One round. -/
def roundBody (sF sB : Stmt) : Stmt :=
  .seq hdS (.seq resS (.seq midS (.seq (regS sF) (.seq splArgs (.seq (DrvR.splS sB)
    (block [.addN 216010 216010 216002]))))))

/-- **The restoration rounds.** -/
def roundsS (sF sB : Stmt) : Stmt := .seq initS (.whileLtN 216010 216000 (roundBody sF sB))

/-! ## Write sets -/

/-- The registers the arc scan writes. -/
def Bscan (r : ℕ) : Bool :=
  decide (216044 ≤ r ∧ r < 216060) || decide (42100 ≤ r ∧ r < 42110) || BuildRam.Bhalf r

/-- A register frame for fewer registers is one for more. -/
theorem fbMono {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameB B' c c' :=
  ⟨fun r hr => h.1 r (by cases h' : B r; rfl; rw [hB r h'] at hr; exact absurd hr (by simp)),
    fun r hr => h.2.1 r (by cases h' : B r; rfl; rw [hB r h'] at hr; exact absurd hr (by simp)),
    h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The registers `ldArc` writes. -/
def BldArc (r : ℕ) : Bool :=
  decide (r = 216045) || decide (r = 216046) || decide (r = 216054) || decide (r = 216055) ||
    decide (42100 ≤ r ∧ r ≤ 42105)

theorem wr_ldArc : wr BldArc ldArc = true := by decide

theorem wr_decS : wr (fun r => decide (r = 216053)) decS = true := by decide

theorem bldArc_scan (r : ℕ) (h : BldArc r = true) : Bscan r = true := by
  simp only [BldArc, Bscan, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega

theorem b53_scan (r : ℕ) (h : decide (r = 216053) = true) : Bscan r = true := by
  simp only [Bscan, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega

theorem bhalf_scan {dd dst : ℕ} (hdd : 42100 ≤ dd ∧ dd < 42110) (hdst : 42100 ≤ dst ∧ dst < 42110)
    (r : ℕ) (h : BuildRam.BhalfS dd dst r = true) : Bscan r = true := by
  simp only [BuildRam.BhalfS, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [Bscan, Bool.or_eq_true, decide_eq_true_eq]
  rcases h with (h | h) | h
  · exact Or.inr h
  · subst h; exact Or.inl (Or.inr hdd)
  · subst h; exact Or.inl (Or.inr hdst)

end

end DrvD

end Chazelle.Core
