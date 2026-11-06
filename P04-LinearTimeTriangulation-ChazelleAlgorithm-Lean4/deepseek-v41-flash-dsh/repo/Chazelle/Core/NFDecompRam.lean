module

public import Chazelle.Golf

public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.SortRam

/-!
# Tree decomposition (WP-C), part 11: the RAM program

The decomposition as a structured statement over band `bDecomp = 6` (registers `60000 …`).

## Registers

| register | role |
|---|---|
| `60000 … 60003` | inputs (model descriptor, normal form `B`, degree cap `D`), output handle |
| `60010`, `60011`, `60012` | the constants `0`, `1`, `2` |
| `60013`, `60014`, `60019` | `R` (regions), `K` (chords), `R - 1` |
| `60015`, `60016`, `60017` | the chord, region and list areas `CB`, `RB`, `LB` of the input |
| `60018` | `A`, the allocator on entry: the new header |
| `60020`, `60021` | loop indices; `60022` the round, `60023` the finished leaves, `60024` the root |
| `60025`, `60026` | head and tail of the search queue |
| `60027 … 60029` | list length, list base, current region of the search |
| `60030 …` | temporaries |
| `60100 + f` | the base `A + 12 + f R` of field `f` (`f < 19`); `60119` the node table `DB` |

## Memory

The new header at `A … A + 11`, then 19 arrays of `R` words (fields `0` `lpar`, `1` `ord`,
`2` `vis`, `3` `prg`, `4` `pch`, `5` `isdn`, `6` `chOf`, `7` `size`, `8` `top`, `9` `best`,
`10` `bestv`, `11` `rem`, `12` `pend`, `13` `act`, `14` `cpar`, `15` `side`, `16` `dpar`,
`17` `dlo`, `18` `dhi`), then the node table `DB = A + 12 + 19 R` of `3 K` words.
-/

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## Program pieces -/

/-- `if nreg a = nreg b then t else e`. -/
def ifEqN (a b : ℕ) (t e : Stmt) : Stmt := .ifLtN a b e (.ifLtN b a e t)

/-- The base register of field `f`. -/
def fb (f : ℕ) : ℕ := 60100 + f

/-- `d := field f [nreg x]` (temporary `60030`). -/
def ldF (d f x : ℕ) : Stmt := block [.addN 60030 (fb f) x, .loadN d 60030]

/-- `field f [nreg x] := nreg v` (temporary `60030`). -/
def stF (f x v : ℕ) : Stmt := block [.addN 60030 (fb f) x, .storeN 60030 v]

section spec

variable {P : Polygon} {W : ℕ}

/-- Spec of `ifEqN`, equal case. -/
theorem ifEqN_eq {a b : ℕ} {t e : Stmt} {c : Config} {Q : Config → ℕ → Prop}
    (h : c.nreg a = c.nreg b) (ht : ∃ c' k, Exec P W t c c' k ∧ Q c' (k + 4)) :
    ∃ c' k, Exec P W (ifEqN a b t e) c c' k ∧ Q c' k := by
  unfold ifEqN
  refine spec_ifLtN_false (by omega) (spec_ifLtN_false (by omega) ?_)
  obtain ⟨c', k, ex, q⟩ := ht
  exact ⟨c', k, ex, by rwa [show k + 2 + 2 = k + 4 by omega]⟩

/-- Spec of `ifEqN`, unequal case (cost at most `k + 3`). -/
theorem ifEqN_ne {a b : ℕ} {t e : Stmt} {c : Config} {Q : Config → ℕ → Prop}
    (h : c.nreg a ≠ c.nreg b) (he : ∃ c' k, Exec P W e c c' k ∧ ∀ k', k' ≤ k + 3 → Q c' k') :
    ∃ c' k, Exec P W (ifEqN a b t e) c c' k ∧ Q c' k := by
  unfold ifEqN
  obtain ⟨c', k, ex, q⟩ := he
  by_cases hlt : c.nreg a < c.nreg b
  · exact ⟨c', k + 1, .ifLtN_true hlt ex, q _ (⋄)⟩
  · have hlt' : c.nreg b < c.nreg a := ⋄
    exact ⟨c', k + 1 + 2, .ifLtN_false hlt (.ifLtN_true hlt' ex), q _ (⋄)⟩

/-- Spec of `ldF`. -/
theorem ldF_exec {c : Config} (hw : WordsBounded W c) (d f x : ℕ)
    (hb : c.nreg (fb f) + c.nreg x ≤ W) :
    ∃ c' k, Exec P W (ldF d f x) c c' k ∧ k = 2 ∧
      c' = { c with nreg := (upd (upd c.nreg 60030 (c.nreg (fb f) + c.nreg x)) d
        (c.nmem (c.nreg (fb f) + c.nreg x))) } := by
  unfold ldF
  refine spec_step (Exec.addN hw _ _ _ hb) fun hw1 => ?_
  refine spec_step (Exec.loadN hw1 _ _) fun _ => ?_
  refine spec_nil ‹_› ⟨rfl, ?_⟩
  ϴ Machine.upd_same

/-- Spec of `stF`. -/
theorem stF_exec {c : Config} (hw : WordsBounded W c) (f x v : ℕ) (hv : v ≠ 60030)
    (hb : c.nreg (fb f) + c.nreg x ≤ W) :
    ∃ c' k, Exec P W (stF f x v) c c' k ∧ k = 2 ∧
      c' = { c with
        nreg := upd c.nreg 60030 (c.nreg (fb f) + c.nreg x)
        nmem := upd c.nmem (c.nreg (fb f) + c.nreg x) (c.nreg v) } := by
  unfold stF
  refine spec_step (Exec.addN hw _ _ _ hb) fun hw1 => ?_
  refine spec_step (Exec.storeN hw1 _ _) fun _ => ?_
  refine spec_nil ‹_› ⟨rfl, ?_⟩
  ϴ Machine.upd_same, Machine.upd_other _ _ _ hv

end spec

/-! ## Registers, frames and field views -/

/-- The constant registers of the decomposition. -/
structure DRegs (A R K CB RB LB : ℕ) (c : Config) : Prop where
  zero : c.nreg 60010 = 0
  one : c.nreg 60011 = 1
  two : c.nreg 60012 = 2
  rR : c.nreg 60013 = R
  rK : c.nreg 60014 = K
  rCB : c.nreg 60015 = CB
  rRB : c.nreg 60016 = RB
  rLB : c.nreg 60017 = LB
  rA : c.nreg 60018 = A
  rR1 : c.nreg 60019 = R - 1
  base : ∀ f, f < 20 → c.nreg (fb f) = A + 12 + f * R

/-- A register the loops may not write: below `60020` or from `60100` on. -/
def Prot (r : ℕ) : Prop := r < 60020 ∨ 60100 ≤ r

/-- **The frame of a loop** of the decomposition: protected registers (except `ALLOC`), real
state and output unchanged; memory unchanged outside `[lo, hi)`. -/
def DFr (lo hi : ℕ) (c c' : Config) : Prop :=
  (∀ r, Prot r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
    c'.output = c.output ∧ ∀ a, (a < lo ∨ hi ≤ a) → c'.nmem a = c.nmem a

theorem DFr.refl (lo hi : ℕ) (c : Config) : DFr lo hi c c :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem DFr.trans {lo hi : ℕ} {c₁ c₂ c₃ : Config} (h₁ : DFr lo hi c₁ c₂) (h₂ : DFr lo hi c₂ c₃) :
    DFr lo hi c₁ c₃ :=
  ⟨fun r h h' => (h₂.1 r h h').trans (h₁.1 r h h'), h₂.2.1.trans h₁.2.1,
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1,
    fun a ha => (h₂.2.2.2.2 a ha).trans (h₁.2.2.2.2 a ha)⟩

theorem DRegs.of_regs {A R K CB RB LB : ℕ} {c c' : Config} (h : DRegs A R K CB RB LB c)
    (k : ∀ r, Prot r → r ≠ ALLOC → c'.nreg r = c.nreg r) : DRegs A R K CB RB LB c' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun f hf' => ?_⟩
  · rw [k _ (by unfold Prot; omega) (⌖)]; exact h.zero
  · rw [k _ (by unfold Prot; omega) (⌖)]; exact h.one
  · rw [k _ (by unfold Prot; omega) (⌖)]; exact h.two
  · rw [k _ (by unfold Prot; omega) (⌖)]; exact h.rR
  · rw [k _ (by unfold Prot; omega) (⌖)]; exact h.rK
  · rw [k _ (by unfold Prot; omega) (⌖)]; exact h.rCB
  · rw [k _ (by unfold Prot; omega) (⌖)]; exact h.rRB
  · rw [k _ (by unfold Prot; omega) (⌖)]; exact h.rLB
  · rw [k _ (by unfold Prot; omega) (⌖)]; exact h.rA
  · rw [k _ (by unfold Prot; omega) (⌖)]; exact h.rR1
  · rw [k _ (by unfold Prot fb; omega) (by unfold fb ALLOC; omega)]; exact h.base f hf'

theorem DRegs.frame {A R K CB RB LB lo hi : ℕ} {c c' : Config} (h : DRegs A R K CB RB LB c)
    (hf : DFr lo hi c c') : DRegs A R K CB RB LB c' := h.of_regs hf.1

/-- An explicit update of scratch registers (`60020 ≤ r < 60100`) is within the frame. -/
theorem DFr.nreg {lo hi : ℕ} {c : Config} (f : ℕ → ℕ) (hf : ∀ r, Prot r → r ≠ ALLOC → f r = c.nreg r) :
    DFr lo hi c { c with nreg := f } :=
  ⟨hf, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- **The field view**: entry `i` of field `f`. -/
def fv (m : ℕ → ℕ) (A R f i : ℕ) : ℕ := m (A + 12 + f * R + i)

theorem addr_inj {A R f g i j : ℕ} (hi : i < R) (hj : j < R)
    (h : A + 12 + f * R + i = A + 12 + g * R + j) : f = g ∧ i = j := by
  rcases lt_trichotomy f g with hfg | rfl | hfg
  · have : (f + 1) * R ≤ g * R := Nat.mul_le_mul_right _ hfg
    rw [Nat.succ_mul] at this; omega
  · exact ⟨rfl, ⋄⟩
  · have : (g + 1) * R ≤ f * R := Nat.mul_le_mul_right _ hfg
    rw [Nat.succ_mul] at this; omega

/-- A store into field `f` at `i` changes exactly that entry of the view. -/
theorem fv_store {m : ℕ → ℕ} {A R f i v g j : ℕ} (hi : i < R) (hj : j < R) :
    fv (upd m (A + 12 + f * R + i) v) A R g j = if g = f ∧ j = i then v else fv m A R g j := by
  unfold fv
  by_cases e : g = f ∧ j = i
  · Ξ ite_eq_left e, e.1, e.2, Machine.upd_same
  · Ξ ite_eq_right e, Machine.upd_other
    intro h
    exact e (addr_inj hj hi h)

/-- A store into the field block leaves the memory outside it unchanged. -/
theorem fv_store_out {m : ℕ → ℕ} {A R f i v a : ℕ} (hf : f < 19) (hi : i < R)
    (ha : a < A + 12 ∨ A + 12 + 19 * R ≤ a) : upd m (A + 12 + f * R + i) v a = m a := by
  Ξ Machine.upd_other
  intro h
  rcases ha with ha | ha
  · omega
  · have : (f + 1) * R ≤ 19 * R := Nat.mul_le_mul_right _ (⋄)
    rw [Nat.succ_mul] at this; omega

end

end Chazelle.Core.DecR
