module

public import Chazelle.Core.RestoreFind
public import Chazelle.Core.SpecPhases
public import Chazelle.Core.DownPhaseMirrorExtract
public import Chazelle.Core.NFBuildCmp

/-!
# Down-phase driver: the obligations it consumes from the other down-phase packages

The driver of the down phase (`DownPhaseDrvR*.lean`) proves
`DownPhaseSpecH (gradeCtx O)` from `MergeSpec` **and the statements of this file**, which it takes
as hypotheses.  They are proved by the interior-oracle files (§1) and the mathematical files (§2).  Each statement
is a plain `Prop` (a `def`), so that the driver's theorems compile now and the final assembly just
plugs in the proofs.

Status of each statement: **firm** (will not change unless its prover reports a problem) or
**draft** (shape may still change; see the docstring).

## 1. Interior oracles (firm)

`IntOraclesSpec O`: a ray-shooter and an arc-cutter for the **interior model** of `Qof P`, on the
up-phase context `gradeCtx O`, writing the bands `insert bUp oracleBands` (finding E7-B1), with the
cost shape of `ShootCutSpec O` (a larger constant `κ` is allowed).  This is what
`Restore.FindSpec` needs to restore conformality in the interior model (design
`docs/design-downphase-driver.md` §4.3, §5.3; `docs/design-downphase.md` §9).

* The models served are only the interior models (`OkInt P M := M = interiorModel (Qof P)`).  The
  adapters of wpm-design §9 serve `OkI := OkModel ∨ interior`, which implies this
  (`ShooterOK`/`CutterOK` are antitone in the model predicate: it occurs only in the precondition).
* The cost functions are those of `ShootCutSpec` (`F γ = κ (⌈log₂ γ⌉ + 1) ⌈(h(γ) (γ+1)²)^{1/3}⌉ + κ`,
  `G γ = κ (⌈log₂ γ⌉ + 1)`, `H = cutGran`).  The adapter costs of wpm-design §9
  (`4 F + κI (⌈log₂ γ⌉ + 1)`, `4 G + κI (G + ⌈log₂ γ⌉ + 1)`, `H`) have this shape with
  `κ' = 4 κ + κI (κ + 1)`, since `⌈(h(γ)(γ+1)²)^{1/3}⌉ ≥ 1`.

## 2. Mathematics

Already proved and used directly (no hypothesis needed): `DownDrv.extractOK_region`,
`DownDrv.downStepG_level` (`DownPhaseDrvMStep`), `DownDrv.kept_iff_host`,
`DownDrv.kept_iff_host_cw`, `DownDrv.full_in_region` (B-M1), `DownDrv.missing_found` and
`DownDrv.chord_of_hostPoly` (B-M2, `DownPhaseDrvMBase`), `DownDrv.splice_ok` (S-M2),
`DownDrv.buildNF_arc` (S-M1), `DownDrv.sum_nk_le`, `lemma23`.

### 2.1 H-R1 / H-R2: the host of a region (firm)

The driver's RAM writes, for region `r` of the current interior normal form
`N = buildNF I Q L E`, the host description **`regHost li n N r`** defined below (a plain function
of the records, computed by the RAM), and uses the chain `⟨H.poly Q, 0, #points - 1⟩` of it (the
edge left out is the last one, from the last host point back to the first; by construction it is
a chord edge of the region).  **`HostR1Spec`** asks: the host is well formed and regular (H-R2),
its polygon is simple with interior the region and boundary on `∂Q ∪ ⋃ S`, it has every vertex of
the host polygon `hostPoly Q S R` among its vertices (base case, B-M2), and the extraction facts
`ExtractOK` hold for the chain (H-R1; both orientations of `Q`).

**The host description** (`regHost`).  Let `as = (N.region r).arcs = [j₀, …, j_{k-1}]` (arc
indices; for `buildNF` they are in increasing order of their start keys) and for an arc `j` write
`s_j = (N.arc j).s`, `e_j = (N.arc j).e` (walk positions of the interior walk, `⟨edge, h + 1⟩`).
* `partner N r x`: the other end of the exit chord of `r` attached at the position `x` (the first
  chord of `(N.region r).chords` whose `lpos` or `rpos` is `x`).
* In walk order the items are, for `t = 1, …, k - 1, 0` (the arc `as[t]` after its predecessor
  `as[t - 1]`): the junction point `P (partner e_prev)` if it differs from `s_j` (two exit chords
  meeting at a vertex), then `P s_j`, the run of walk vertices strictly inside the arc, `P e_j`.
* `P x` is `.pt (.onEdge q (x.hgt - 1))` with `q` the edge of `Q` carrying the walk edge `x.edge`
  (`qE`), except that an **arc end at a vertex** uses the previous walk edge `x.edge - 1` (so that
  every host edge satisfies `HostEdgeOK`).  "At a vertex" means `x.hgt - 1 = iv x.edge`
  (distinct heights).
* A run of the walk vertices `a, a + 1, …, a + ℓ` (mod `n`) is `.run a ℓ` if `LeftInside Q`, and
  `.run (n - 1 - (a + ℓ) mod n) ℓ` otherwise (the walk then runs in decreasing index).
* If `LeftInside Q` the description is this list; otherwise it is reversed (items in increasing
  index of `Q`, as `.run` requires).

M-M1 (junction genericity) and the count bookkeeping D10 are handled on the driver's side.
-/

namespace Chazelle.Core

namespace DrvR

@[expose] public section

open Machine

/-! ## 1. Interior oracles -/

/-- The models the interior oracles must serve: the interior model of the geometry polygon. -/
def OkInt (P : Polygon) (M : Model) : Prop := M = interiorModel (Qof P)

/-- The bands of the interior oracles: the oracle bands and the band `bUp` (finding E7-B1). -/
def ioBandsD : Finset ℕ := insert bUp oracleBands

/-- The shooter cost of `ShootCutSpec`, with constant `κ`. -/
noncomputable def shCost (κ : ℕ) (γ : ℕ) : ℕ :=
  κ * (Nat.clog 2 γ + 1) * rpowCeil (cutGran γ * (γ + 1) ^ 2) ((1 : ℝ) / 3) + κ

/-- The cutter cost of `ShootCutSpec` (number of pieces), with constant `κ`. -/
def cuCost (κ : ℕ) (γ : ℕ) : ℕ := κ * (Nat.clog 2 γ + 1)

/-- **Obligation (interior oracles, firm): the interior oracles.**  A shooter and a cutter serving
the interior model of `Qof P` on `gradeCtx O`, writing `insert bUp oracleBands`, with the cost
shape of `ShootCutSpec O`. -/
def IntOraclesSpec (O : OracleIface) : Prop :=
  ∃ (sh cu : Stmt) (κ : ℕ),
    ShooterOK sh ioBandsD (shCost κ) (gradeCtx O) OkInt ∧
    CutterOK cu ioBandsD (cuCost κ) cutGran (gradeCtx O) OkInt

theorem bRestore_notin_ioBandsD : bRestore ∉ ioBandsD := by decide

theorem oracleBands_subset_ioBandsD : oracleBands ⊆ ioBandsD := Finset.subset_insert _ _

/-! ## 2.1 The host of a region -/

/-- The vertex of `Q` at walk vertex `p` of the interior walk (`li` the `LeftInside` bit). -/
def ivB (li : Bool) (n p : ℕ) : ℕ := if li then p else n - 1 - p

/-- The edge of `Q` carrying the walk edge `e` of the interior walk. -/
def qE (li : Bool) (n e : ℕ) : ℕ := if li then e else if e + 1 < n then n - 2 - e else n - 1

/-- The position is at the walk vertex starting its edge (distinct heights: its height vertex is
that vertex). -/
def atVtx (li : Bool) (n : ℕ) (x : WPos) : Bool := decide (x.hgt - 1 = ivB li n x.edge)

/-- The host point of a walk position; `isEnd`: the position ends an arc. -/
def ptI (li : Bool) (n : ℕ) (x : WPos) (isEnd : Bool) : HostItem :=
  .pt (.onEdge (qE li n (if isEnd && atVtx li n x then (x.edge + n - 1) % n else x.edge))
    (x.hgt - 1))

/-- The other end of the exit chord of region `r` attached at `x` (`x` itself if none). -/
def partner (N : NF) (r : ℕ) (x : WPos) : WPos :=
  match (N.region r).chords.find? (fun i => decide ((N.chord i).lpos = x ∨ (N.chord i).rpos = x))
  with
  | some i => if (N.chord i).lpos = x then (N.chord i).rpos else (N.chord i).lpos
  | none => x

/-- The number of walk vertices strictly inside the arc from `s` to `e`. -/
def runCnt (li : Bool) (n : ℕ) (s e : WPos) : ℕ :=
  (e.edge + (if atVtx li n e then 0 else 1) + n - 1 - s.edge) % n

/-- The run of walk vertices strictly inside the arc from `s` to `e` (as host items, empty or one
`.run` in increasing index of `Q`). -/
def runItems (li : Bool) (n : ℕ) (s e : WPos) : List HostItem :=
  if runCnt li n s e = 0 then []
  else if li then [.run ((s.edge + 1) % n) (runCnt li n s e - 1)]
  else [.run (n - 1 - (s.edge + runCnt li n s e) % n) (runCnt li n s e - 1)]

/-- The items of arc `j` after its predecessor arc `jp` (junction point, start, run, end). -/
def arcItems (li : Bool) (n : ℕ) (N : NF) (r jp j : ℕ) : List HostItem :=
  (if partner N r (N.arc jp).e = (N.arc j).s then [] else [ptI li n (partner N r (N.arc jp).e) false]) ++
    [ptI li n (N.arc j).s false] ++ runItems li n (N.arc j).s (N.arc j).e ++
    [ptI li n (N.arc j).e true]

/-- The host items of region `r` in walk order, starting after the end of its first arc. -/
def walkItems (li : Bool) (n : ℕ) (N : NF) (r : ℕ) : List HostItem :=
  (List.range (N.region r).arcs.length).flatMap fun t =>
    arcItems li n N r ((N.region r).arcs.getD t 0)
      ((N.region r).arcs.getD ((t + 1) % (N.region r).arcs.length) 0)

/-- **The host description of region `r`** written by the driver (items in increasing index of
`Q`). -/
def regHost (li : Bool) (n : ℕ) (N : NF) (r : ℕ) : Host :=
  if li then walkItems li n N r else (walkItems li n N r).reverse

/-- **Obligation H-R1/H-R2 (mathematics, firm).**  For region `r` of `N = buildNF I Q L E` (valid
sorted input, at least one chord, degree `≤ 4`) and the region correspondence `reg` of `N`, the
driver's host `H = regHost li n N r` (`li` the `LeftInside` bit of `Q`) is well formed and regular,
its polygon is simple, has interior `reg r` and boundary on `∂Q ∪ ⋃ S`, contains every vertex of
`hostPoly Q S (reg r)`, and the chain `⟨H.poly Q, 0, #points - 1⟩` satisfies the extraction facts. -/
noncomputable def HostR1Spec : Prop :=
  open Classical in
  ∀ (P : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (reg : ℕ → Set Point) (r : ℕ),
    GoodEnv P → L ≠ [] →
    ChordTriplesOK (interiorModel (Qof P)) (Qof P) L → E.Perm (List.range (2 * L.length)) →
    E.Pairwise (BuildNF.codeLe (interiorModel (Qof P)) (Qof P) L) →
    (interiorModel (Qof P)).DegLe
      ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).F (interiorModel (Qof P)) (Qof P)) 4 →
    Restore.NFRegs (interiorModel (Qof P)) (Qof P)
      (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E) reg →
    r < (BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).nRegions →
    let Q := Qof P
    let N := BuildNF.buildNF (interiorModel Q) Q L E
    let S := N.F (interiorModel Q) Q
    let H := regHost (decide (Mountain.LeftInside Q)) Q.n N r
    HostWF Q.n H ∧ HostRegular Q.n H ∧ (H.poly Q).Simple ∧
      ∀ C : Chain, C.P = H.poly Q → C.s = 0 → C.m + 1 = C.P.n → DownDrv.ExtractOK Q S (reg r) C

end

end DrvR

end Chazelle.Core
