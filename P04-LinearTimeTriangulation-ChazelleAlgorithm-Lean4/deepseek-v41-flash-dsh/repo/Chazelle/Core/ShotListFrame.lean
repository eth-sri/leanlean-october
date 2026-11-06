module

public import Chazelle.Golf

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
    (if p then a else b) = b := ⊚ h

/-- `if` with a true condition (a simp lemma for a discharger). -/
theorem ite_yes {α : Type*} {p : Prop} [Decidable p] (a b : α) (h : p) :
    (if p then a else b) = a := ⊚ h

/-- Register reads through `upd` with symbolic registers: conditions decided by `omega`. -/
macro "rsimp" : tactic =>
  `(tactic| simp (disch := omega) only [Chazelle.upd, ite_no, ite_yes, ↓reduceIte,
    Chazelle.Programs.Config.nreg_mk, Chazelle.Programs.Config.nmem_mk])

/-- **A frame with named registers**: `Frame B` except that the registers satisfying `Wr` may
also change. -/
def FrameR (B : Finset ℕ) (Wr : ℕ → Prop) (c c' : Config) (k : ℕ) : Prop :=
  (∀ r, bandOf r ∉ B → r ≠ ALLOC → ¬ Wr r → c'.nreg r = c.nreg r) ∧
    (∀ r, bandOf r ∉ B → ¬ Wr r → c'.rreg r = c.rreg r) ∧
    (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
    (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧
    c'.output = c.output ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k

theorem FrameR.refl (B : Finset ℕ) (Wr : ℕ → Prop) (c : Config) : FrameR B Wr c c 0 :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, le_rfl, ⋄⟩

theorem FrameR.trans {B : Finset ℕ} {Wr : ℕ → Prop} {c c₁ c₂ : Config} {k₁ k₂ : ℕ}
    (h₁ : FrameR B Wr c c₁ k₁) (h₂ : FrameR B Wr c₁ c₂ k₂) : FrameR B Wr c c₂ (k₁ + k₂) := by
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := h₁
  obtain ⟨r₂, rr₂, m₂, rm₂, o₂, a₂, b₂⟩ := h₂
  refine ⟨fun r hr ha hw => ?_, fun r hr hw => ?_, fun a ha => ?_, fun a ha => ?_, o₂.trans o₁,
    a₁.trans a₂, ⋄⟩
  · Ξ r₂ r hr ha hw, r₁ r hr ha hw
  · Ξ rr₂ r hr hw, rr₁ r hr hw
  · Ξ m₂ a (lt_of_lt_of_le ha a₁), m₁ a ha
  · Ξ rm₂ a (lt_of_lt_of_le ha a₁), rm₁ a ha

theorem FrameR.mono {B B' : Finset ℕ} {Wr Wr' : ℕ → Prop} {c c' : Config} {k k' : ℕ}
    (h : FrameR B Wr c c' k) (hB : B ⊆ B') (hW : ∀ r, Wr r → Wr' r) (hk : k ≤ k') :
    FrameR B' Wr' c c' k' := by
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := h
  exact ⟨fun r hr ha hw => r₁ r (fun h => hr (hB h)) ha (fun h => hw (hW r h)),
    fun r hr hw => rr₁ r (fun h => hr (hB h)) (fun h => hw (hW r h)), m₁, rm₁, o₁, a₁,
    ⋄⟩

/-- A register frame gives a named frame. -/
theorem FrameR.of_frameB {B : Finset ℕ} {Wr : ℕ → Prop} {Bw : ℕ → Bool} {c c' : Config}
    (h : FrameB Bw c c') (hB : ∀ r, Bw r = true → Wr r ∨ bandOf r ∈ B) (hA : Bw ALLOC = false)
    (k : ℕ) : FrameR B Wr c c' k := by
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁⟩ := h
  have hal := r₁ ALLOC hA
  refine ⟨fun r hr _ hw => r₁ r ?_, fun r hr hw => rr₁ r ?_, fun a _ => by rw [m₁],
    fun a _ => by rw [rm₁], o₁, by rw [hal], by rw [hal]; omega⟩
  · cases hb : Bw r
    · rfl
    · rcases hB r hb with h | h
      · exact absurd h hw
      · exact absurd h hr
  · cases hb : Bw r
    · rfl
    · rcases hB r hb with h | h
      · exact absurd h hw
      · exact absurd h hr

/-- A frame of the bands `B` is a named frame. -/
theorem FrameR.of_frame {B : Finset ℕ} {Wr : ℕ → Prop} {c c' : Config} {k : ℕ}
    (h : Frame B c c' k) : FrameR B Wr c c' k := by
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁, b₁⟩ := h
  exact ⟨fun r hr ha _ => r₁ r hr ha, fun r hr _ => rr₁ r hr, m₁, rm₁, o₁, a₁, b₁⟩

/-! ## Descriptors below a bound survive memory changes above it -/

/-- A host layout below `E` survives a change of the memory at or above `E`. -/
theorem hostAt_agree {m m' : ℕ → ℕ} {h E : ℕ} {H : Host} (hH : HostAt m h H)
    (hE : h + 3 * H.length + 4 ≤ E) (he : ∀ a, a < E → m' a = m a) : HostAt m' h H := by
  obtain ⟨h0, h1⟩ := hH
  refine ⟨by rw [he _ (⋄)]; exact h0, fun i hi => ?_⟩
  have := h1 i hi
  revert this
  cases H.getD i (.run 0 0) with
  | run a l =>
    intro h; simp only at h ⊢
    rw [he _ (⋄), he _ (by omega), he _ (by omega)]; exact h
  | pt x =>
    cases x with
    | vtx j => intro h; simp only at h ⊢; rw [he _ (⋄), he _ (by omega)]; exact h
    | onEdge e j =>
      intro h; simp only at h ⊢
      rw [he _ (⋄), he _ (by omega), he _ (by omega)]; exact h

/-- **A copied chain descriptor** (host layout below `E`, the five words copied to `d`). -/
theorem chainDescAt_copy {m m' : ℕ → ℕ} {bw d E : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (hC : ChainDescAt m bw Q H C) (hE : m bw + 3 * H.length + 4 ≤ E)
    (he : ∀ a, a < E → m' a = m a) (hc : ∀ j, j < 5 → m' (d + j) = m (bw + j)) :
    ChainDescAt m' d Q H C := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hC
  have c0 := hc 0 (⋄)
  have c1 := hc 1 (⋄)
  have c2 := hc 2 (⋄)
  have c3 := hc 3 (⋄)
  have c4 := hc 4 (⋄)
  simp only [add_zero] at c0
  refine ⟨?_, h1, by rw [c1]; exact h2, by rw [c2]; exact h3, by rw [c3]; exact h4,
    by rw [c4]; exact h5⟩
  Ξ c0
  exact hostAt_agree h0 hE he

/-- **A well-formed copy of a chain descriptor.** -/
theorem chainWF_copy {P : Polygon} {m m' : ℕ → ℕ} {bw d E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw (Qof P) H C)
    (he : ∀ a, a < E → m' a = m a) (hc : ∀ j, j < 5 → m' (d + j) = m (bw + j))
    (hd : d + 5 ≤ E') (hEE : E ≤ E') : ChainWF P E' m' d := by
  obtain ⟨hl, hHW, hEb, hs⟩ := hwf.2 H C hC
  refine ⟨hd, fun H' C' hC' => ?_⟩
  have c0 : m' d = m bw := by simpa using hc 0 (⋄)
  have hH' : HostAt m' (m bw) H := hostAt_agree hC.1 hEb he
  have hHH : H' = H := NFLoc.hostAt_unique (by rw [← c0]; exact hC'.1) hH'
  subst hHH
  refine ⟨hl, hHW, by rw [c0]; omega, ?_⟩
  have e1 : C'.s = C.s := by rw [← hC'.2.2.1, ← hC.2.2.1, hc 1 (⋄)]
  have e2 : C'.P = C.P := Ρ hC'.2.1, hC.2.1
  rw [e1, e2]; exact hs


end

end ShotList

end Chazelle.Core
