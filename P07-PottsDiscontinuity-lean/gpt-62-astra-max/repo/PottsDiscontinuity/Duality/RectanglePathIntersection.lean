/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Tactic

@[expose] public section

open Set Topology unitInterval

namespace PottsDiscontinuity.FK.Curves

noncomputable section

/-- The sign of a nonvanishing continuous real function is constant along a path. -/
private theorem same_sign {f : I → ℝ} (hf : Continuous f) (hn : ∀ t, f t ≠ 0) :
    0 < f 0 ↔ 0 < f 1 := by
  have step (a b : I) (ha : 0 < f a) : 0 < f b := by
    by_contra! hb
    obtain ⟨t, ht⟩ := intermediate_value_univ b a hf (show 0 ∈ Icc (f b) (f a) from ⟨hb, ha.le⟩)
    grind
  grind

/-- Two-dimensional intermediate value theorem. A nonvanishing map on the
square has a continuous square root. Following that root around the four
sides would reverse its sign, by the indicated half-plane conditions. -/
private theorem rectangle_zero (f : I × I → ℂ) (hf : Continuous f)
    (left : ∀ t, (f (0,t)).re ≤ 0) (right : ∀ t, 0 ≤ (f (1,t)).re)
    (bottom : ∀ t, (f (t,0)).im ≤ 0) (top : ∀ t, 0 ≤ (f (t,1)).im) : ∃ z, f z = 0 := by
  by_contra! h
  let c (x : ℝ × ℝ) : I × I := (projIcc 0 1 zero_le_one x.1, projIcc 0 1 zero_le_one x.2)
  have hc : Continuous c := (continuous_projIcc.comp continuous_fst).prodMk
    (continuous_projIcc.comp continuous_snd)
  have hsc : IsSimplyConnected (univ : Set (ℝ × ℝ)) := by
    let := (convex_univ : Convex ℝ (univ : Set (ℝ × ℝ))).contractibleSpace univ_nonempty
    unfold IsSimplyConnected
    infer_instance
  obtain ⟨s, hs, hs2⟩ := Complex.exists_continuousOn_pow_eq hsc isOpen_univ (hf.comp hc).continuousOn
    (by rintro ⟨x, _, hx⟩; exact h (c x) hx) (by decide : (2:ℕ) ≠ 0)
  let g (z : I × I) := s (z.1, z.2)
  have hg : Continuous g := (continuousOn_univ.mp hs).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  have heq (z : I × I) : g z ^ 2 = f z := by simpa [g, c] using hs2 ((z.1:ℝ), (z.2:ℝ))
  let u z := (g z).re
  let v z := (g z).im
  have hu : Continuous u := Complex.continuous_re.comp hg
  have hv : Continuous v := Complex.continuous_im.comp hg
  have nz (z) : u z ≠ 0 ∨ v z ≠ 0 := by
    by_contra! hz
    apply h z
    rw [← heq, show g z = 0 from Complex.ext hz.1 hz.2, zero_pow (by decide : (2:ℕ) ≠ 0)]
  have re (z) : u z ^ 2 - v z ^ 2 = (f z).re := by
    simpa [u, v, sq, Complex.mul_re] using congrArg Complex.re (heq z)
  have im (z) : 2 * (u z * v z) = (f z).im := by
    rw [← heq]; simp [sq, Complex.mul_im, u, v]; ring
  have L (t:I) : v (0,t) ≠ 0 := by
    intro hz
    have hn := (nz (0,t)).resolve_right (not_not_intro hz)
    nlinarith [left t, re (0,t), sq_pos_of_ne_zero hn]
  have R (t:I) : u (1,t) ≠ 0 := by
    intro hz
    have hn := (nz (1,t)).resolve_left (not_not_intro hz)
    nlinarith [right t, re (1,t), sq_pos_of_ne_zero hn]
  have B (t:I) : u (t,0) * v (t,0) ≤ 0 := by linarith [im (t,0), bottom t]
  have T (t:I) : 0 ≤ u (t,1) * v (t,1) := by linarith [im (t,1), top t]
  have hL := same_sign (f := (fun t => v (0,t))) (hv.comp (continuous_const.prodMk continuous_id)) L
  have hR := same_sign (f := (fun t => u (1,t))) (hu.comp (continuous_const.prodMk continuous_id)) R
  have hB := same_sign (f := (fun t => u (t,0) - v (t,0)))
    ((hu.sub hv).comp (continuous_id.prodMk continuous_const)) (fun t he => by
      have hn := nz (t,0)
      have he' := sub_eq_zero.mp he
      rcases mul_nonpos_iff.mp (B t) with h | h <;> grind)
  have hT := same_sign (f := (fun t => u (t,1) + v (t,1)))
    ((hu.add hv).comp (continuous_id.prodMk continuous_const)) (fun t he => by
      rcases mul_nonneg_iff.mp (T t) with h | h <;> grind [nz (t,1)])
  have b₀ := mul_nonpos_iff.mp (B 0)
  have b₁ := mul_nonpos_iff.mp (B 1)
  have t₀ := mul_nonneg_iff.mp (T 0)
  have t₁ := mul_nonneg_iff.mp (T 1)
  grind [L 0, L 1, R 0, R 1]

/-- Opposite-side crossings of a closed rectangle intersect. -/
theorem pathRectangle_crossing_intersection
    {a b : ℝ × ℝ} {p₀ p₁ q₀ q₁ : ℝ × ℝ}
    (P : Path p₀ p₁) (Q : Path q₀ q₁)
    (hPbox : ∀ t, a.1 ≤ (P t).1 ∧ (P t).1 ≤ b.1 ∧
      a.2 ≤ (P t).2 ∧ (P t).2 ≤ b.2)
    (hQbox : ∀ t, a.1 ≤ (Q t).1 ∧ (Q t).1 ≤ b.1 ∧
      a.2 ≤ (Q t).2 ∧ (Q t).2 ≤ b.2)
    (hPleft : (P 0).1 = a.1) (hPright : (P 1).1 = b.1)
    (hQbottom : (Q 0).2 = a.2) (hQtop : (Q 1).2 = b.2) :
    ∃ s t : I, P s = Q t := by
  let f (z : I × I) : ℂ := ⟨(P z.1).1 - (Q z.2).1, (Q z.2).2 - (P z.1).2⟩
  have hf := Complex.equivRealProdCLM.symm.continuous.comp
    (show Continuous (fun z : I × I => ((P z.1).1 - (Q z.2).1, (Q z.2).2 - (P z.1).2)) by fun_prop)
  have := rectangle_zero f hf
    (fun t => sub_nonpos.mpr (hPleft.trans_le (hQbox t).1))
    (fun t => sub_nonneg.mpr ((hQbox t).2.1.trans_eq hPright.symm))
    (fun t => sub_nonpos.mpr (hQbottom.trans_le (hPbox t).2.2.1))
    (fun t => sub_nonneg.mpr ((hPbox t).2.2.2.trans_eq hQtop.symm))
  obtain ⟨⟨s,t⟩, h⟩ := this
  exact ⟨s,t,Prod.ext (sub_eq_zero.mp (congrArg Complex.re h))
    (sub_eq_zero.mp (congrArg Complex.im h)).symm⟩

end
end PottsDiscontinuity.FK.Curves
