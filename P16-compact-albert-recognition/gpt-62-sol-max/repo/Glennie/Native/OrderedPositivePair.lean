module

public import Glennie.Native.PairReduction
public import Glennie.Native.RealConjugation
public import Glennie.Diagonalization
public import Glennie.Theorems.Frames
public import Glennie.UnitShifts
public import Glennie.Native.SectorLeftAction
public import Glennie.Compact.FlatBase
@[expose] public section
namespace Glennie.NativeOrderedPositivePair
open Glennie Glennie.Compact.FlatBase
noncomputable section
set_option autoImplicit false

private def encVal : Fin 3 → ℤ := ![1,0,-1]

private theorem encVal_cert : ∀ f : Fin 3 → Fin 3,
    (∑ i, encVal (f i)) = 0 → (∑ i, encVal (f i)^2) = 2 → Function.Bijective f := by
  decide +kernel

private theorem ordered_diagonal (x : Albert) (hx : IsDiagonal x)
    (ht : trace x = 0) (hn : inner x x = 2) (hc : jordan x (jordan x x) = x) :
    ∃ g : CompactAutomorphism, g.equiv x = flatXN := by
  let v : Fin 3 → ℝ := ![x.d0, x.d1, x.d2]
  have hxv : x = diagonalOf v := (diagonalAlbert_eq x hx).symm
  rw [hxv] at hc
  rw [diagonal_jordan, diagonal_jordan] at hc
  have hv (i : Fin 3) : v i * ((v i-1)*(v i+1)) = 0 := by
    have h := congrArg (fun x : Albert => ![x.d0,x.d1,x.d2] i) hc
    fin_cases i <;> dsimp [v, diagonalOf, diagonalAlbert] at h ⊢ <;> linear_combination h
  have vals (i : Fin 3) : ∃ j : Fin 3, v i = (encVal j : ℝ) := by
    rcases mul_eq_zero.mp (hv i) with h | h
    · exact ⟨1, by simpa [encVal] using h⟩
    rcases mul_eq_zero.mp h with h | h
    · exact ⟨0, by simp [encVal]; linarith⟩
    · exact ⟨2, by simp [encVal]; linarith⟩
  choose f hf using vals
  have ht' : ∑ i, v i = 0 := by simpa [v, trace, Fin.sum_univ_three] using ht
  have hn' : ∑ i, v i^2 = 2 := by
    simpa [v, Fin.sum_univ_three, inner_self_coordinates, hx.1, hx.2.1, hx.2.2,
      octNormSq, Quaternion.normSq_def'] using hn
  simp only [hf] at ht' hn'
  have hF := encVal_cert f (by exact_mod_cast ht') (by exact_mod_cast hn')
  let e := Equiv.ofBijective f hF
  refine ⟨permutationAutomorphism e.symm, ?_⟩
  rw [hxv, permutation_diagonalOf]
  suffices v ∘ ⇑e.symm = fun i => (encVal i : ℝ) by rw [this]; norm_num [diagonalOf, encVal, flatXN, diagonalAlbert]
  funext i
  exact (hf _).trans (congrArg (fun j => (encVal j : ℝ)) (e.apply_symm_apply i))


private theorem orderEncoder (p : Fin 3 → Albert) (hp : Frame p) :
    ∃ g : CompactAutomorphism, g.equiv (encoder p) = flatXN := by
  obtain ⟨d, hd⟩ := native_diagonalization (encoder p)
  have hf := d.map_frame p hp
  obtain ⟨u, hu⟩ := ordered_diagonal _ ((d.encoder_map p).symm ▸ hd)
    (frame_encoder_trace _ hf) (frame_encoder_norm _ hf) (frame_encoder_cube _ hf)
  exact ⟨u.comp d, by simpa only [CompactAutomorphism.comp_apply, d.encoder_map] using hu⟩

/-- Retain the nonnegative real 01/12 slots actually constructed by PairReduction.
The ordered first frame stays fixed, and the remaining slot lies in the actual
complex sector. The second native element is unrestricted, including zero. -/
theorem native_ordered_positive_pair (p : Fin 3 → Albert) (hp : Frame p) (y : Albert) :
    ∃ g : CompactAutomorphism, (∀ i, g.equiv (p i) = flatFrameP i) ∧
      PositiveNormal (g.equiv y) := by
  obtain ⟨d, hd⟩ := orderEncoder p hp
  obtain ⟨g, hg⟩ := positive_complex_reduction (d.equiv y)
  refine ⟨g.compactAutomorphism.comp d, fun i => ?_, hg⟩
  rw [frame_as_projector p hp, compactAutomorphism_projectorFrame, CompactAutomorphism.comp_apply,
    hd, relatedTriple_fixes_diagonal g _ ⟨rfl,rfl,rfl⟩]
  rfl

end
end Glennie.NativeOrderedPositivePair
