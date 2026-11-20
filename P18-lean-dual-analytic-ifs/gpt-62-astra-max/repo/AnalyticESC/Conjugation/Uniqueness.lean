module
public import AnalyticESC.Conjugation.Linearisation

@[expose] public section
namespace AnalyticESC.IFS
open Set Metric
variable {N : ℕ} (Φ : IFS N)

lemma regular_comp {g} (hg : Regular g) (a : Letters N) : Regular (g ∘ Φ.R a) := by
  have hf := Φ.regular_R a
  refine ⟨hg.1.comp hf.1 (Φ.re_comp_mem_I a),fun x hx => ?_⟩
  rw [deriv_comp x (hg.1 _ (Φ.re_comp_mem_I a hx)).differentiableAt (hf.1 x hx).differentiableAt]
  exact mul_ne_zero (hg.2 _ (Φ.re_comp_mem_I a hx)) (hf.2 x hx)

/-- At the fixed point the slope of an affine conjugate is the derivative of the word. -/
lemma linearizes_iff_D {g} (hg : Regular g) {a : Letters N} (ha : a ≠ []) :
    Linearizes g (Φ.R a) ↔ EqOn (D (g ∘ Φ.R a)) (D g) I := by
  rw [← affine_iff (Φ.regular_comp hg a) hg]
  refine ⟨fun ⟨l,b,_,_,h⟩ => ⟨l,b,h⟩,?_⟩
  rintro ⟨l,b,h⟩
  have hf := Φ.regular_R a
  obtain ⟨p,hp,ep⟩ := exists_mem_Icc_isFixedPt_of_mapsTo hf.1.continuousOn zero_le_one (Φ.re_comp_mem_I a)
  have he := affine_deriv (Φ.regular_comp hg a).1 hg.1 h hp
  rw [deriv_comp p (hg.1 _ (Φ.re_comp_mem_I a hp)).differentiableAt (hf.1 _ hp).differentiableAt,ep.eq] at he
  have e : l = deriv (Φ.R a) p := by grind [hg.2 p hp]
  exact ⟨l,b,e ▸ hf.2 p hp,e ▸ Φ.deriv_R_lt ha hp,h⟩

lemma rec_comp {g} (hg : Regular g) (a : Letters N) : Φ.Rec a (D (g ∘ Φ.R a)) (D g) := by
  intro x hx; dsimp only
  rw [← Φ.R_deriv a hx,← Φ.R_logDer a (Φ.real_mem hx),D,logDer_comp (hg.1 _ (Φ.re_comp_mem_I a hx)) ((Φ.regular_R a).1 _ hx) (hg.2 _ (Φ.re_comp_mem_I a hx))]
  simp [D]

lemma linearizes_iff_rec {g} (hg : Regular g) {a : Letters N} (ha : a ≠ []) :
    Linearizes g (Φ.R a) ↔ Φ.Rec a (D g) (D g) := by
  rw [Φ.linearizes_iff_D hg ha]; exact ⟨fun h => h.symm.trans (Φ.rec_comp hg a),fun h => (Φ.rec_comp hg a).trans h.symm⟩

end AnalyticESC.IFS
