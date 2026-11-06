module

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
  have hA : c₁.nreg ALLOC = c.nreg ALLOC := h1 ALLOC (by
    intro h
    obtain ⟨q, hq, hq'⟩ := List.mem_map.1 h
    have := hl q hq
    unfold ALLOC at hq'; omega)
  refine ⟨fun r hr _ => h1 r ?_, fun r _ => by rw [h2], fun a _ => by rw [h3], fun a _ => by rw [h4],
    h5, by omega, by omega⟩
  intro h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
  apply hr
  have := hl q hq
  simp only [bandOf, bLocate, Finset.mem_singleton]
  omega

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
      Exec P W (.seq (block (copies l)) p) c c' k ∧ k ≤ l.length + K ∧ Out P C c₁ c' ∧
      Frame primBands c c' k := by
  obtain ⟨c₁, e₁, h1, h2, h3, h4, h5, h6⟩ := copies_exec (P := P) l c hw hd hnd
  have hf₁ : Frame {bLocate} c c₁ l.length := frame_copies hl h2 h3 h4 h5 h6
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := h2 ALLOC (by
    intro h
    obtain ⟨q, hq, hq'⟩ := List.mem_map.1 h
    have := hl q hq
    unfold ALLOC at hq'; omega)
  have h00 : c₁.nreg 50200 = c.nreg src := h1 _ hsrc
  have hpre : PrimPre Inp P W c₁ := by
    refine ⟨hG, hW, ?_, H, C, ?_, hInp c₁ h1 h2 h4⟩
    · rwa [h00, hA₁, h4]
    · rwa [h00, h4]
  obtain ⟨c', k, e, hk, hpost, hf⟩ := hp P W c₁ e₁.wb_right hpre (by rwa [hA₁])
  refine ⟨c₁, c', l.length + k, h1, .seq e₁ e, by simp only at hk; omega, hpost H C ?_, ?_⟩
  · rwa [h00, h4]
  · have := hf₁.trans hf
    exact this.mono (by
      intro b hb
      simp only [Finset.mem_union, Finset.mem_singleton] at hb
      rcases hb with rfl | hb
      · simp [primBands]
      · exact hb) le_rfl

end

end Restore

end Chazelle.Core
