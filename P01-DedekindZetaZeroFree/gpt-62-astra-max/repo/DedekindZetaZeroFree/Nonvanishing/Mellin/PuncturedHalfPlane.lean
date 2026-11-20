module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.HalfPlane

@[expose] public section

namespace DedekindZetaZeroFree

section

variable (σ : ℝ) (hσ : σ < 1)

include hσ in
theorem mellin_punctured_halfplane_isOpen :
    IsOpen {s : ℂ | σ < s.re ∧ s ≠ 1} := (Complex.isOpen_re_gt σ).inter isOpen_ne

include hσ in
theorem mellin_punctured_halfplane_isPreconnected :
    IsPreconnected {s : ℂ | σ < s.re ∧ s ≠ 1} := by
  let R : Set ℂ := {s | 1 < s.re}
  let U : Set ℂ := {s | σ < s.re} ∩ {s | 0 < s.im}
  let D : Set ℂ := {s | σ < s.re} ∩ {s | s.im < 0}
  let L : Set ℂ := {s | σ < s.re} ∩ {s | s.re < 1}
  have hAll :=
    ((((convex_halfSpace_re_gt 1).isPreconnected).union (2 + Complex.I)
      (by simp [R]) (by simp [U]; linarith) (((convex_halfSpace_re_gt σ).inter
        (convex_halfSpace_im_gt 0)).isPreconnected)).union (2 - Complex.I)
      (by simp [R]) (by simp [D]; linarith) (((convex_halfSpace_re_gt σ).inter
        (convex_halfSpace_im_lt 0)).isPreconnected)).union (((σ + 1) / 2 : ℝ) + Complex.I)
      (by left; right; simp [U]; linarith)
      (by simp [L]; constructor <;> linarith) (((convex_halfSpace_re_gt σ).inter
        (convex_halfSpace_re_lt 1)).isPreconnected)
  have heq : (((R ∪ U) ∪ D) ∪ L) = {s : ℂ | σ < s.re ∧ s ≠ 1} := by
    ext s
    simp only [R, U, D, L, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro (((hr | hu) | hd) | hl)
      · exact ⟨lt_trans hσ hr, fun h => by simpa [h] using hr⟩
      · exact ⟨hu.1, fun h => by simpa [h] using hu.2⟩
      · exact ⟨hd.1, fun h => by simpa [h] using hd.2⟩
      · exact ⟨hl.1, fun h => by simpa [h] using hl.2⟩
    · rintro ⟨hs, hn⟩
      by_cases hr : 1 < s.re
      · exact Or.inl (Or.inl (Or.inl hr))
      by_cases hl : s.re < 1
      · exact Or.inr ⟨hs, hl⟩
      by_cases hi : 0 < s.im
      · exact Or.inl (Or.inl (Or.inr ⟨hs, hi⟩))
      by_cases hd : s.im < 0
      · exact Or.inl (Or.inr ⟨hs, hd⟩)
      exfalso
      apply hn
      apply Complex.ext <;> simp only [Complex.one_re, Complex.one_im] <;> linarith
  rwa [heq] at hAll

include hσ in
theorem mellin_punctured_halfplane_two_mem :
    (2 : ℂ) ∈ {s : ℂ | σ < s.re ∧ s ≠ 1} := by
  constructor
  · change σ < 2; linarith
  · norm_num

end

theorem mellin_punctured_halfplane_two_accPt :
    AccPt (2 : ℂ) (Filter.principal
      {s : ℂ | ∃ t : ℝ, t ≠ 0 ∧ s = (2 : ℂ) + t * Complex.I}) := by
  rw [accPt_iff_nhds]
  intro V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨(2 : ℂ) + (ε / 2 : ℝ) * Complex.I, ⟨hball ?_, ?_⟩, ?_⟩
  · simp_all [abs_of_pos]
  · exact ⟨ε / 2, by positivity, rfl⟩
  · intro h
    simp_all

end DedekindZetaZeroFree
