module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreTestSpec
public import Chazelle.Core.SweepPrimOff
public import Chazelle.Core.SweepPrimAbs
public import Chazelle.Core.SweepPrimArr
public import Chazelle.Core.SweepPrimLeft
public import Chazelle.Core.SweepPrimNF

/-!
# WP-E, the candidate test on the RAM, part 1: calling the chain primitives

The candidate test (`TestOK`) is built from the WP-D2 primitives of the chain model (`offCmp`,
`leftSec`, `turnNext`, `turnPrev`, `absKey`, `absCmp`, `arrivalPos`) and the normal-form readers.
A primitive reads its inputs from `50200 …` (the chain descriptor address in `50200`); the test
keeps its state in band `bRestore` and copies the inputs in before each call.

* `callPrim`: a copy block followed by a primitive with a `PrimPre`/`PrimPost` contract.
* `frame_copies`: the copy block writes only its targets.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

/-- The copy block into the band `bLocate` writes only band `bLocate`. -/
theorem frame_copies {l : List (ℕ × ℕ)} {c c₁ : Config} {k : ℕ}
    (hl : ∀ q ∈ l, 50000 ≤ q.1 ∧ q.1 < 60000)
    (h1 : ∀ r, r ∉ l.map Prod.fst → c₁.nreg r = c.nreg r) (h2 : c₁.rreg = c.rreg)
    (h3 : c₁.nmem = c.nmem) (h4 : c₁.rmem = c.rmem) (h5 : c₁.output = c.output) :
    Frame {bLocate} c c₁ k := by
  core_grind [ALLOC, bandOf, Finset.mem_singleton]

/-- **Calling a chain primitive**: copy the inputs (among them the descriptor address), run the
primitive. -/
theorem callPrim {p : Stmt} {K : ℕ} {Inp : Polygon → ℕ → Chain → Config → Prop}
    {Out : Polygon → Chain → Config → Config → Prop}
    (hp : Meets p primBands (PrimPre Inp) (PrimPost Out) (fun _ _ => K))
    (l : List (ℕ × ℕ)) (hd : ∀ q ∈ l, ∀ r ∈ l, q.1 ≠ r.2) (hnd : (l.map Prod.fst).Nodup)
    (hl : ∀ q ∈ l, 50000 ≤ q.1 ∧ q.1 < 60000) {src : ℕ} (hsrc : (50200, src) ∈ l)
    {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) (hG : GoodEnv P)
    (hW : hostWords P.n ≤ W) {H : Host} {C : Chain}
    (hwf : ChainWF P (c.nreg ALLOC) c.nmem (c.nreg src))
    (hC : ChainDescAt c.nmem (c.nreg src) (Qof P) H C)
    (hInp : ∀ c₁ : Config, (∀ q ∈ l, c₁.nreg q.1 = c.nreg q.2) →
      (∀ r, r ∉ l.map Prod.fst → c₁.nreg r = c.nreg r) → c₁.nmem = c.nmem → Inp P W C c₁)
    (hroom : c.nreg ALLOC + K ≤ W) :
    ∃ c₁ c' k, (∀ q ∈ l, c₁.nreg q.1 = c.nreg q.2) ∧
      (∀ r, r ∉ l.map Prod.fst → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      Exec P W (.seq (block (copies l)) p) c c' k ∧ k ≤ l.length + K ∧ Out P C c₁ c' ∧
      Frame primBands c c' k := by
  obtain ⟨c₁, e₁, h1, h2, h3, h4, h5, h6⟩ := copies_exec (P := P) l c hw hd hnd
  have hf₁ : Frame {bLocate} c c₁ l.length := frame_copies hl h2 h3 h4 h5 h6
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := h2 ALLOC (by
    grind [ALLOC])
  have h00 : c₁.nreg 50200 = c.nreg src := h1 _ hsrc
  have hpre : PrimPre Inp P W c₁ := by
    grind [Chazelle.Core.SweepPrim.PrimPre]
  obtain ⟨c', k, e, hk, hpost, hf⟩ := hp P W c₁ e₁.wb_right hpre (by ram_grind)
  refine ⟨c₁, c', l.length + k, h1, h2, h4, .seq e₁ e, by grind, hpost H C ?_, ?_⟩
  · ram_grind
  · have := hf₁.trans hf
    grind [Finset.mem_union, Finset.mem_singleton, primBands]

end

end Restore

end Chazelle.Core
