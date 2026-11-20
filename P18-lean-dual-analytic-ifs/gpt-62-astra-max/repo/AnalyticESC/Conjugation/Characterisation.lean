module
public import AnalyticESC.Conjugation.Uniqueness

@[expose] public section
/-! # Projection recursions characterize simultaneous linearizations -/
namespace AnalyticESC.IFS
open Set Metric
variable {N : ℕ} (Φ : IFS N)

lemma coord_for (w : Address N) : ∃ g, Regular g ∧ EqOn (D g) (Φ.P w) I :=
  exists_coord Φ.ε_pos (Φ.analytic_dual ⊤ _).differentiableOn (fun _ => Φ.im_dualProj_ofReal ⊤ _)

/-- Uniqueness of the bounded solution, peeling off one nonempty block at each step. -/
lemma match_of_rec {α : Type*} {w : α → Address N} {s : α → α} {a : α → Letters N}
    (ha : ∀ i, a i ≠ []) (h : ∀ i, Φ.Rec (a i) (Φ.P (w i)) (Φ.P (w (s i))))
    {g} (hg : Regular g) (hl : ∀ i, Linearizes g (Φ.R (a i))) (i) : EqOn (D g) (Φ.P (w i)) I := by
  have hc := Complex.continuous_ofReal.comp_continuousOn
    ((hg.1.deriv.deriv.continuousOn).div hg.1.deriv.continuousOn hg.2)
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image hc.norm
  let E (p : α × I) := ‖D g p.2 - Φ.P (w p.1) p.2‖
  have hb : BddAbove (range E) := by
    refine ⟨B+Φ.amp,?_⟩; rintro _ ⟨⟨j,x⟩,rfl⟩
    exact (norm_sub_le _ _).trans
      (add_le_add (hB (mem_image_of_mem _ x.2)) (Φ.proj_le ⊤ _ (Φ.closedReal x.2)))
  have step (p : α × I) : ∃ q, E p ≤ Φ.cmax * E q := by
    obtain ⟨j,x⟩ := p
    refine ⟨(s j,⟨_,Φ.re_comp_mem_I (a j) x.2⟩),?_⟩
    dsimp [E]; rw [(Φ.linearizes_iff_rec hg (ha j)).mp (hl j) x.2, h j x.2, add_sub_add_left_eq_sub,← mul_sub,norm_mul]
    gcongr
    refine (Φ.bounds _ (Φ.closedReal x.2)).2.trans ?_
    simpa using pow_le_pow_of_le_one Φ.cmax_nonneg Φ.cmax_lt_one.le (List.length_pos_iff.mpr (ha j))
  intro x hx
  have := contraction_estimate Φ.cmax_nonneg Φ.cmax_lt_one hb step (i,⟨x,hx⟩)
  simpa [E,sub_eq_zero] using this

lemma linearizes_iff_match {a} (ha : a ≠ []) {w} (hw : Φ.Rec a (Φ.P w) (Φ.P w)) {g} (hg : Regular g) :
    Linearizes g (Φ.R a) ↔ EqOn (D g) (Φ.P w) I := by
  refine ⟨fun h => Φ.match_of_rec (s := id) (fun _ => ha) (fun _ => hw) hg (fun _ => h) (), ?_⟩
  intro he; apply (Φ.linearizes_iff_rec hg ha).mpr; intro x hx
  dsimp only
  rw [he hx,he (Φ.re_comp_mem_I a hx)]; exact hw hx

end AnalyticESC.IFS
