module

public import Glennie.Native.PairReduction
public import Glennie.Native.RealConjugation
public import Glennie.Theorems.DiagonalFrames
public import Glennie.Native.SectorLeftAction
public import Glennie.Compact.FlatBase

@[expose] public section
namespace Glennie.NativeOrderedPositivePair
open Glennie Glennie.Compact.FlatBase
noncomputable section
set_option autoImplicit false

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
  simp [realSwap01_coordinates, diagonalAlbert, octConj]

private theorem swap02_diagonal (a b c : ℝ) :
    realSwap02Automorphism.equiv (diagonalAlbert a b c) = diagonalAlbert c b a := by
  simp [realSwap02_coordinates, diagonalAlbert, octConj]

private theorem ordered_diagonal (x : Albert) (hx : IsDiagonal x)
    (ht : trace x = 0) (hn : inner x x = 2) (hc : x.d0*x.d1*x.d2 = 0) :
    ∃ g : CompactAutomorphism, g.equiv x = flatXN := by
  have ht' : x.d0 + x.d1 + x.d2 = 0 := ht
  have hn' : x.d0^2 + x.d1^2 + x.d2^2 = 2 := by
    simp_all [inner_self_coordinates, hx.1, hx.2.1, hx.2.2, octNormSq, Quaternion.normSq_def']
  have hp := six_diagonal_patterns x.d0 x.d1 x.d2 ht' hn' hc
  have hrep := diagonalAlbert_representation x hx
  let A := realSwap01Automorphism
  let B := realSwap02Automorphism
  let C := A.comp (B.comp A)
  have hC (a b c : ℝ) : C.equiv (diagonalAlbert a b c) = diagonalAlbert a c b := by
    rw [CompactAutomorphism.comp_apply, CompactAutomorphism.comp_apply,
      swap01_diagonal, swap02_diagonal, swap01_diagonal]
  rw [hrep]
  rcases hp with h|h|h|h|h|h <;> rw [h.1,h.2.1,h.2.2]
  all_goals first | exact ⟨CompactAutomorphism.refl,rfl⟩ | exact ⟨A,by rw [swap01_diagonal]; rfl⟩ | exact ⟨B,by rw [swap02_diagonal]; rfl⟩ | exact ⟨C,by rw [hC]; rfl⟩ | exact ⟨C.comp A,by rw [CompactAutomorphism.comp_apply,swap01_diagonal,hC]; rfl⟩ | exact ⟨C.comp B,by rw [CompactAutomorphism.comp_apply,swap02_diagonal,hC]; rfl⟩

theorem frame_as_projector (p : Fin 3 → Albert) (hp : Frame p) :
    p = projectorFrame (encoder p) := by
  funext i
  fin_cases i
  · exact (frame_projector_first p hp).symm
  · exact (frame_projector_middle p hp).symm
  exact (frame_projector_last p hp).symm

theorem frames_eq {p q : Fin 3 → Albert} (hp : Frame p) (hq : Frame q)
    (h : encoder p = encoder q) : p = q :=
  (frame_as_projector _ hp).trans ((congrArg projectorFrame h).trans (frame_as_projector _ hq).symm)

/-- A genuine native frame is carried to the ORIGINAL ordered first frame.
The six encoder orders are realized by carrier automorphisms, not outcome relabels. -/
theorem native_ordered_frame (p : Fin 3 → Albert) (hp : Frame p) :
    ∃ g : CompactAutomorphism, g.equiv (encoder p) = flatXN := by
  obtain ⟨d, hd⟩ := native_diagonalization (encoder p)
  let p' := fun i => d.equiv (p i)
  have hp' : Frame p' := d.map_frame p hp
  have he : IsDiagonal (encoder p') := by
    grind [d.encoder_map]
  obtain ⟨u, hu⟩ := ordered_diagonal (encoder p') he
    (frame_encoder_trace p' hp') (frame_encoder_norm p' hp')
    (diagonal_frame_encoder_cubic_zero p' hp' he)
  exact ⟨u.comp d, by change u.equiv (d.equiv _) = _; rw [← d.encoder_map]; exact hu⟩

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
      InComplexSector (g.equiv y) ∧ 0 ≤ (g.equiv y).o02.1.imI := by
  obtain ⟨d,hd⟩ := native_ordered_frame p hp
  obtain ⟨t,a,b,ha,hb,h1,h2,h3,h4⟩ := positive_slots (d.equiv y)
  let g := t.compactAutomorphism.comp d
  have h : encoder (fun i => g.equiv (p i)) = encoder flatFrameP := by
    rw [g.encoder_map, flatFrameP_encoder, CompactAutomorphism.comp_apply, hd, relatedTriple_flatXN]
  exact ⟨g,a,b,ha,hb,congrFun (frames_eq (g.map_frame _ hp) flatFrameP_frame h),h1,h2,h3,h4⟩

end
end Glennie.NativeOrderedPositivePair
