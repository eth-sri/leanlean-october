module

public import AnalyticESC.Conjugation.Koenigs

@[expose] public section

namespace AnalyticESC

open Set Metric Filter Topology

abbrev AffineRel (u v : ℝ → ℝ) (l b : ℝ) := ∀ x ∈ I, u x = l * v x + b
def Linearizes (g F : ℝ → ℝ) := ∃ l b : ℝ, l ≠ 0 ∧ |l| < 1 ∧ AffineRel (g ∘ F) g l b

lemma eq_deriv_I {u v : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ I)
    (hu : HasDerivAt u a x) (hv : HasDerivAt v b x) (h : EqOn u v I) : a = b :=
  (uniqueDiffOn_Icc zero_lt_one x hx).eq_deriv _ hu.hasDerivWithinAt
    (hv.hasDerivWithinAt.congr h (h hx))

lemma affine_deriv {u v : ℝ → ℝ} (hu : AnalyticOnNhd ℝ u I) (hv : AnalyticOnNhd ℝ v I)
    {l b : ℝ} (h : AffineRel u v l b) {x} (hx : x ∈ I) :
    deriv u x = l * deriv v x := eq_deriv_I hx (hu x hx).differentiableAt.hasDerivAt
      (((hv x hx).differentiableAt.hasDerivAt.const_mul l).add_const b) (fun _ hy => h _ hy)


/-- Equality of logarithmic derivatives makes the slope ratio constant. -/
lemma proportional {u g : ℝ → ℝ} (hu : Regular u) (hg : Regular g) (h : EqOn (D u) (D g) I) :
    ∃ l, EqOn (deriv u) (fun x => l * deriv g x) I := by
  let v := fun x => deriv u x / deriv g x
  have h1 (x) (hx : x ∈ I) : HasDerivWithinAt v 0 I x := by
    simpa only [show logDer u x = logDer g x from Complex.ofReal_inj.mp (h hx),sub_self,mul_zero] using (ratio_jet hu hg hx).hasDerivWithinAt (s := I)
  exact ⟨v 0,fun x hx => (div_eq_iff (hg.2 x hx)).mp (eq_of_hasDerivWithinAt_zero_I h1 hx zero_I)⟩

/-- Equality of logarithmic derivatives integrates to an affine relation, in two steps. -/
lemma affine_iff {u g : ℝ → ℝ} (hu : Regular u) (hg : Regular g) :
    (∃ l b, AffineRel u g l b) ↔ EqOn (D u) (D g) I := by
  constructor
  · rintro ⟨l,b,h⟩ x hx
    have h1 (x) (hx : x ∈ I) := affine_deriv hu.1 hg.1 h hx
    have h2 := eq_deriv_I hx (hu.1 x hx).deriv.differentiableAt.hasDerivAt
      ((hg.1 x hx).deriv.differentiableAt.hasDerivAt.const_mul l) (fun y hy => h1 y hy)
    have hn := hu.2 x hx
    grind [D]
  · intro h
    obtain ⟨l,H⟩ := proportional hu hg h
    have h2 (x) (hx : x ∈ I) : HasDerivWithinAt (fun y => u y - l * g y) 0 I x := by
      convert ((hu.1 x hx).differentiableAt.hasDerivAt.sub
        ((hg.1 x hx).differentiableAt.hasDerivAt.const_mul l)).hasDerivWithinAt using 1
      linarith [H hx]
    exact ⟨l, _,fun x hx => eq_add_of_sub_eq (eq_of_hasDerivWithinAt_zero_I h2 hx zero_I) |>.trans (add_comm ..)⟩

end AnalyticESC
