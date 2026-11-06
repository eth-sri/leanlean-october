module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Aesop

public import Glennie.Native.PairReduction
public import Glennie.Native.RealConjugation
public import Glennie.Theorems.DiagonalFrames
public import Glennie.Native.SectorLeftAction
public import Glennie.Compact.FlatBase

@[expose] public section
namespace Glennie.NativeOrderedPositivePair
open Glennie Glennie.Compact.FlatBase
section
private theorem six_diagonal_patterns (a b c : ℝ)
    (ht : a + b + c = 0) (hn : a^2 + b^2 + c^2 = 2) (hc : a*b*c = 0) :
    (a = 1 ∧ b = 0 ∧ c = -1) ∨
    (a = 1 ∧ b = -1 ∧ c = 0) ∨
    (a = 0 ∧ b = 1 ∧ c = -1) ∨
    (a = -1 ∧ b = 1 ∧ c = 0) ∨
    (a = -1 ∧ b = 0 ∧ c = 1) ∨
    (a = 0 ∧ b = -1 ∧ c = 1) := by
  grind

private theorem swap01_diagonal (a b c : ℝ) :
    realSwap01Automorphism.equiv (diagonalAlbert a b c) = diagonalAlbert b a c := by
  change realConjugateAlbert realSwap01 (diagonalAlbert a b c) = _
  rw [realSwap01_coordinates]
  simp [diagonalAlbert, octConj]

private theorem swap02_diagonal (a b c : ℝ) :
    realSwap02Automorphism.equiv (diagonalAlbert a b c) = diagonalAlbert c b a := by
  change realConjugateAlbert realSwap02 (diagonalAlbert a b c) = _
  rw [realSwap02_coordinates]
  simp [diagonalAlbert, octConj]

private theorem ordered_diagonal (x : Albert) (hx : IsDiagonal x)
    (ht : trace x = 0) (hn : inner x x = 2) (hc : x.d0*x.d1*x.d2 = 0) :
    ∃ g : CompactAutomorphism, g.equiv x = flatXN := by
  have ht'                          := ht
  have hn' : x.d0^2 + x.d1^2 + x.d2^2 = 2 := by
    rw [inner_self_coordinates] at hn
    simp only [hx.1, hx.2.1, hx.2.2] at hn
    norm_num [octNormSq, Quaternion.normSq_def'] at hn
    exact hn
  have hp := six_diagonal_patterns x.d0 x.d1 x.d2 ht' hn' hc
  have hrep := (diagonalAlbert_eq x hx).symm
  let A := realSwap01Automorphism
  let B := realSwap02Automorphism
  let C := A.comp (B.comp A)
  have hC (a b c : ℝ) : C.equiv (diagonalAlbert a b c) = diagonalAlbert a c b := by
    dsimp only [C, A, B]
    rw [CompactAutomorphism.comp_apply, CompactAutomorphism.comp_apply,
      swap01_diagonal, swap02_diagonal, swap01_diagonal]
  rcases hp with h | h | h | h | h | h
  all_goals rw [h.1, h.2.1, h.2.2] at hrep
  all_goals rw [hrep]
  all_goals first
    | exact ⟨CompactAutomorphism.refl, rfl⟩
    | exact ⟨C, hC _ _ _⟩
    | exact ⟨A, swap01_diagonal _ _ _⟩
    | exact ⟨B, swap02_diagonal _ _ _⟩
    | exact ⟨C.comp A, by rw [CompactAutomorphism.comp_apply, swap01_diagonal, hC]; rfl⟩
    | exact ⟨C.comp B, by rw [CompactAutomorphism.comp_apply, swap02_diagonal, hC]; rfl⟩

/-- A genuine native frame is carried to the ORIGINAL ordered first frame.
The six encoder orders are realized by carrier automorphisms, not outcome relabels. -/
theorem native_ordered_frame (p : Fin 3 → Albert) (hp : Frame p) :
    ∃ g : CompactAutomorphism, g.equiv (encoder p) = flatXN ∧
      ∀ i : Fin 3, g.equiv (p i) = flatFrameP i := by
  obtain ⟨d, hd⟩ := native_diagonalization (encoder p)
  let p' := fun i => d.equiv (p i)
  have hp'            := d.map_frame p hp
  have he : IsDiagonal (encoder p') := by
    rw [d.encoder_map]
    exact hd
  obtain ⟨u, hu⟩ := ordered_diagonal (encoder p') he
    (frame_encoder_trace p' hp') (frame_encoder_norm p' hp')
    (diagonal_frame_encoder_cubic_zero p' hp' he)
  let g := u.comp d
  have hg : g.equiv (encoder p) = flatXN := by
    change u.equiv (d.equiv (encoder p)) = flatXN
    rw [← d.encoder_map]
    exact hu
  refine ⟨g, hg, ?_⟩
  intro i
  rw [frame_as_projector p hp, compactAutomorphism_projectorFrame, hg]
  rfl

private theorem relatedTriple_flatXN (t : OctRelatedTriple) :
    t.compactAutomorphism.equiv flatXN = flatXN := by
  change (⟨flatXN.d0, flatXN.d1, flatXN.d2,
    t.A flatXN.o01, t.C flatXN.o02, t.B flatXN.o12⟩ : Albert) = flatXN
  simp [flatXN, map_zero]

/-- Retain the nonnegative real 01/12 slots actually constructed by PairReduction.
The ordered first frame stays fixed, and the remaining slot lies in the actual
complex sector. The second native element is unrestricted, including zero. -/
theorem native_ordered_positive_pair (p : Fin 3 → Albert) (hp : Frame p) (y : Albert) :
    ∃ g : CompactAutomorphism, ∃ a b : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧
      (∀ i : Fin 3, g.equiv (p i) = flatFrameP i) ∧
      (g.equiv y).o01 = octScalar a ∧ (g.equiv y).o12 = octScalar b ∧
      InComplexSector (g.equiv y) := by
  obtain ⟨d, hd, hdp⟩ := native_ordered_frame p hp
  let z := d.equiv y
  obtain ⟨t, a, b, ha, hb, h01, h12⟩ := octTwoSlotsReal z.o01 z.o12
  obtain ⟨k, hk, h02⟩ := exists_octAutomorphism_to_complex (t.C z.o02)
  let g := k.compactAutomorphism.comp (t.compactAutomorphism.comp d)
  have hgX : g.equiv (encoder p) = flatXN := by
    change k.compactAutomorphism.equiv
      (t.compactAutomorphism.equiv (d.equiv (encoder p))) = flatXN
    rw [hd, relatedTriple_flatXN, relatedTriple_flatXN]
  refine ⟨g, a, b, ha, hb, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [frame_as_projector p hp, compactAutomorphism_projectorFrame, hgX]
    rfl
  · change k.A (t.A z.o01) = octScalar a
    rw [h01, diagonalOctTriple_scalar k hk a]
  · change k.B (t.B z.o12) = octScalar b
    rw [h12, hk.1, diagonalOctTriple_scalar k hk b]
  · change OctInComplex (k.A (t.A z.o01)) ∧
      OctInComplex (k.C (t.C z.o02)) ∧ OctInComplex (k.B (t.B z.o12))
    rw [h01, h12, diagonalOctTriple_scalar k hk a, hk.1,
      diagonalOctTriple_scalar k hk b]
    exact ⟨octInComplex_scalar a, h02, octInComplex_scalar b⟩

end
end Glennie.NativeOrderedPositivePair
