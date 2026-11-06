module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SpecRam
public import Chazelle.Core.SignKernelRam
public import Chazelle.Core.NFLocateHost

/-!
# Shooting at a list of arcs with holes, part 3: frames with named registers

`FrameR B Wr c c' k` is `Frame B c c' k` refined inside the written bands: registers outside the
bands `B` are unchanged unless they satisfy `Wr` (the registers the procedure writes in the
caller's band).  It composes (`FrameR.trans`), weakens (`FrameR.mono`), and arises from register
frames (`FrameR.of_frameB`) and from frames of procedures in the bands `B` (`FrameR.of_frame`).
-/

namespace Chazelle.Core

namespace ShotList

open Machine SignK

@[expose] public section

/-- `if` with a false condition (a simp lemma for a discharger). -/
theorem ite_no {α : Type*} {p : Prop} [Decidable p] (a b : α) (h : ¬ p) :
    (if p then a else b) = b := by simp [h]

/-- `if` with a true condition (a simp lemma for a discharger). -/
theorem ite_yes {α : Type*} {p : Prop} [Decidable p] (a b : α) (h : p) :
    (if p then a else b) = a := by simp [h]

/-- Register reads through `upd` with symbolic registers: conditions decided by `omega`. -/
macro "rsimp" : tactic =>
  `(tactic| simp (disch := omega) only [Chazelle.upd, ite_no, ite_yes, ↓reduceIte,
    Chazelle.Programs.Config.nreg_mk, Chazelle.Programs.Config.nmem_mk])

section
variable (B : Finset ℕ) (Wr : ℕ → Prop)
include B Wr
/-- **A frame with named registers**: `Frame B` except that the registers satisfying `Wr` may
also change. -/
def FrameR (c c' : Config) (k : ℕ) : Prop :=
  (∀ r, bandOf r ∉ B → r ≠ ALLOC → ¬ Wr r → c'.nreg r = c.nreg r) ∧
    (∀ r, bandOf r ∉ B → ¬ Wr r → c'.rreg r = c.rreg r) ∧
    (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
    (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧
    c'.output = c.output ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k

theorem FrameR.refl (c : Config) : FrameR B Wr c c 0 :=
  by core_grind


end

theorem FrameR.trans {B : Finset ℕ} {Wr : ℕ → Prop} {c c₁ c₂ : Config} {k₁ k₂ : ℕ}
    (h₁ : FrameR B Wr c c₁ k₁) (h₂ : FrameR B Wr c₁ c₂ k₂) : FrameR B Wr c c₂ (k₁ + k₂) := by
  grind [Chazelle.Core.ShotList.FrameR]

theorem FrameR.mono {B B' : Finset ℕ} {Wr Wr' : ℕ → Prop} {c c' : Config} {k k' : ℕ}
    (h : FrameR B Wr c c' k) (hB : B ⊆ B') (hW : ∀ r, Wr r → Wr' r) (hk : k ≤ k') :
    FrameR B' Wr' c c' k' := by
  core_grind

section
variable {B : Finset ℕ} {Wr : ℕ → Prop}
/-- A register frame gives a named frame. -/
theorem FrameR.of_frameB {Bw : ℕ → Bool} {c c' : Config}
    (h : FrameB Bw c c') (hB : ∀ r, Bw r = true → Wr r ∨ bandOf r ∈ B) (hA : Bw ALLOC = false)
    (k : ℕ) : FrameR B Wr c c' k := by
  core_grind

/-- A frame of the bands `B` is a named frame. -/
theorem FrameR.of_frame {c c' : Config} {k : ℕ}
    (h : Frame B c c' k) : FrameR B Wr c c' k := by
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := h
  core_grind

/-! ## Descriptors below a bound survive memory changes above it -/


end

section
variable {m m' : ℕ → ℕ}
/-- A host layout below `E` survives a change of the memory at or above `E`. -/
theorem hostAt_agree {h E : ℕ} {H : Host} (hH : HostAt m h H)
    (hE : h + 3 * H.length + 4 ≤ E) (he : ∀ a, a < E → m' a = m a) : HostAt m' h H := by
  obtain ⟨h0, h1⟩ := hH
  refine ⟨by grind, fun i hi => ?_⟩
  have := h1 i hi
  revert this
  cases H.getD i (.run 0 0) with
  | run a l =>
    ram_grind
  | pt x =>
    cases x with
    | vtx j => ram_grind
    | onEdge e j =>
      ram_grind

/-- **A copied chain descriptor** (host layout below `E`, the five words copied to `d`). -/
theorem chainDescAt_copy {bw d E : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (hC : ChainDescAt m bw Q H C) (hE : m bw + 3 * H.length + 4 ≤ E)
    (he : ∀ a, a < E → m' a = m a) (hc : ∀ j, j < 5 → m' (d + j) = m (bw + j)) :
    ChainDescAt m' d Q H C := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hC
  have c0 := hc 0 (by omega)
  have c1 := hc 1 (by omega)
  have c2 := hc 2 (by omega)
  have c3 := hc 3 (by omega)
  
  simp only [add_zero] at c0
  refine ⟨?_, h1, by omega, by omega, by omega,
    by simp_all⟩
  rw [c0]
  exact hostAt_agree h0 hE he


end

/-- **A well-formed copy of a chain descriptor.** -/
theorem chainWF_copy {P : Polygon} {m m' : ℕ → ℕ} {bw d E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw (Qof P) H C)
    (he : ∀ a, a < E → m' a = m a) (hc : ∀ j, j < 5 → m' (d + j) = m (bw + j))
    (hd : d + 5 ≤ E') (hEE : E ≤ E') : ChainWF P E' m' d := by
  obtain ⟨hl, hHW, hEb, hs⟩ := hwf.2 H C hC
  refine ⟨hd, fun H' C' hC' => ?_⟩
  have c0 : m' d = m bw := by simpa using hc 0 (by omega)
  have hH' : HostAt m' (m bw) H := hostAt_agree hC.1 hEb he
  have hHH : H' = H := NFLoc.hostAt_unique (by rw [← c0]; exact hC'.1) hH'
  ram_grind


end

end ShotList

end Chazelle.Core
