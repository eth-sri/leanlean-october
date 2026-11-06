module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvOrg3
public import Chazelle.Core.SweepIoLHit2

/-!
# The sweep (WP-D), stage 3: the shot of a candidate (RAM)

`evShot sh`: from the symbolic point `a` of a chord end (`oSym`), in the direction `oD`, shoot at
the arcs gathered at `wGB` (`wGK` arcs of `N₁` in the model of `C₁`, descriptor `MD₁`), then
compute the arrival position of the hit (`callArr`, reversed direction `eRD`) and normalise its
height code (`normS`).  Outputs: the hit flag `eF`, the arrival flag `eA`, the arrival position
`(eA + 1, eA + 2)`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt)

@[expose] public section

/-! ## Registers -/

/-- The model descriptor of `C₁` (built by the initialisation) and its chain descriptor. -/
def MD₁ : ℕ := sw 650
def CD₁ : ℕ := sw 651

/-- The gathered arcs of the window (base, count). -/
def wGB : ℕ := sw 2420
def wGK : ℕ := sw 2421

def eF : ℕ := sw 2240
def eA : ℕ := sw 2243
def eRD : ℕ := sw 2246
def eNo : ℕ := sw 2247

/-! ## The frame of the stage-3 components -/

section
variable (X : ℕ → Prop)
include X
/-- **The frame of a component**: registers outside the oracle bands and the set `X` (and the
allocator) are unchanged, the allocator grows, the memory below it is kept. -/
def EFr (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ X r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)

theorem EFr.refl (c : Config) : EFr X c c :=
  by core_grind


end

theorem EFr.trans {X : ℕ → Prop} {c₁ c₂ c₃ : Config} (h₁ : EFr X c₁ c₂) (h₂ : EFr X c₂ c₃) :
    EFr X c₁ c₃ :=
  by core_grind

theorem EFr.mono {X Y : ℕ → Prop} {c c' : Config} (h : EFr X c c') (hXY : ∀ r, X r → Y r) :
    EFr Y c c' :=
  by core_grind

/-! ## The program -/

/-- The shot block preparation (and the reversed direction code). -/
def evPrepL : List Instr :=
  [.copyN 241300 MD₁, .copyN 241301 wGB, .copyN 241302 wGK, .copyN 241303 oSym,
    .copyN 241304 (oSym + 1), .copyN 241305 (oSym + 2), .copyN 241306 oD, .copyN 241307 (sw 5),
    .copyN 241308 (sw 10), .constN 241309 0, .subN eRD K1 oD]

/-- The arrival and its normalisation. -/
def evArr : Stmt :=
  .seq (callArr CD₁ 241321 241322 eRD eA) (.ifLtN K0 eA (normS CD₁ (eA + 1) (eA + 2) eNo) .skip)

/-- **The shot of a candidate.** -/
def evShot (sh : Stmt) : Stmt :=
  .seq (block evPrepL) (.seq (ShotList.shotList sh RS) (.seq (block [.copyN eF 241320])
    (.ifLtN K0 eF evArr .skip)))

/-- The registers written by `evShot` (besides the oracle bands and the allocator). -/
def ShW (r : ℕ) : Prop := (RS ≤ r ∧ r < RS + 300) ∨ (eF ≤ r ∧ r ≤ eNo + 1)

theorem evPrepL_val (m f : ℕ → ℕ) :
    regB m evPrepL f 241300 = f MD₁ ∧ regB m evPrepL f 241301 = f wGB ∧
    regB m evPrepL f 241302 = f wGK ∧ regB m evPrepL f 241303 = f oSym ∧
    regB m evPrepL f 241304 = f (oSym + 1) ∧ regB m evPrepL f 241305 = f (oSym + 2) ∧
    regB m evPrepL f 241306 = f oD ∧ regB m evPrepL f 241307 = f (sw 5) ∧
    regB m evPrepL f 241308 = f (sw 10) ∧ regB m evPrepL f 241309 = 0 ∧
    regB m evPrepL f eRD = f K1 - f oD ∧
    (∀ q, (q < 241300 ∨ 241309 < q) → q ≠ eRD → regB m evPrepL f q = f q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun q hq hq' => regB_other _ _ _ (fun i hi => by
    simp only [evPrepL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      core_grind <;> first | omega)⟩ <;>
  aesop

/-! ## The contract -/

/-- The cost of `evShot`. -/
def evShotK (Fg K : ℕ) : ℕ := ShotList.shotCost Fg K + 50000

/-- **The outputs of the shot** from `a` in the direction `σ` at the arcs `(m, B, K)` of the model
of `C₁`: the hit flag, complete for genuine hits on the arcs; for a hit at `τ`, the arrival flag
and the normalised arrival position of `rayPt a σ τ`. -/
def ShotOut (P : Polygon) (J : Merge.Junction) (m : ℕ → ℕ) (B K : ℕ) (a : Point) (σ : ℝ)
    (c' : Config) : Prop :=
  c'.nreg eF ≤ 1 ∧
    (∀ τ₀, Genuine J.left a σ τ₀ →
      rayPt a σ τ₀ ∈ ShotList.loSet (chainModel J.left) (Qof P) m B K [] → c'.nreg eF = 1) ∧
    (c'.nreg eF = 1 → ∃ τ, 0 < τ ∧
      (∀ τ₀, Genuine J.left a σ τ₀ →
        rayPt a σ τ₀ ∈ ShotList.loSet (chainModel J.left) (Qof P) m B K [] → τ = τ₀) ∧
      c'.nreg eA ≤ 1 ∧
      (c'.nreg eA = 1 → c'.nreg (eA + 1) < (chainModel J.left).W.n ∧
        ProperPos (chainModel J.left) (Qof P) P.n ⟨c'.nreg (eA + 1), c'.nreg (eA + 2)⟩ ∧
        Arrival (chainModel J.left).W (rayPt a σ τ) σ (c'.nreg (eA + 1))
          ((chainModel J.left).param (Qof P) ⟨c'.nreg (eA + 1), c'.nreg (eA + 2)⟩) ∧
        (c'.nreg (eA + 2) = 0 ↔
          (chainModel J.left).param (Qof P) ⟨c'.nreg (eA + 1), c'.nreg (eA + 2)⟩ = 0)) ∧
      (c'.nreg eA ≠ 1 → ∀ p t, ¬ Arrival (chainModel J.left).W (rayPt a σ τ) σ p t))

/-- A normalised position: same parameter and point, and a zero code exactly at the vertex. -/
theorem nhgt_facts {M : Model} {Q : Polygon} {n : ℕ} {u : WPos} (hu : ProperPos M Q n u) :
    ProperPos M Q n ⟨u.edge, nhgt M Q u⟩ ∧ M.param Q ⟨u.edge, nhgt M Q u⟩ = M.param Q u ∧
      M.pos Q ⟨u.edge, nhgt M Q u⟩ = M.pos Q u ∧
      (nhgt M Q u = 0 ↔ M.param Q ⟨u.edge, nhgt M Q u⟩ = 0) := by
  obtain ⟨⟨hpp, hcase⟩, hedge, hpos, hkey, -⟩ := Restore.normOf_facts hu
  have he : (⟨u.edge, nhgt M Q u⟩ : WPos) = Restore.normOf M Q u := by
    unfold nhgt; rw [← hedge]
  rw [he]
  have hpar : M.param Q (Restore.normOf M Q u) = M.param Q u := by
    simp_all [Model.key] <;> omega_nf
  refine ⟨hpp, hpar, hpos, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [← he, h]; rfl
  grind

end

end SweepEv

end Chazelle.Core
