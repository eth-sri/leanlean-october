module

public import AnalyticESC.Dual.Cylinders

@[expose] public section

/-!
# Dual compositions of two systems that agree along an orbit

Tools for the proof of Theorem 1.4 in Section 4.2. If the maps of `Ψ` agree with those of `Φ` to
second order along the orbit of a point `x`, then `G_w h = F_w h` at `x`. If they agree only to
first order at `x` itself, then `G_w h` at `x` is `F_w h` shifted by the change of `f''/f'` at
`x`. The section also bounds the width of the cylinder intervals and shows that the dual maps send
the closed cylinder into the open one under bounds on `[0,1]` alone.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- `g` agrees with `f` to second order at `y`: equal values, first and second derivatives. -/
def AgreeAt (f g : ℂ → ℂ) (y : ℂ) : Prop :=
  g y = f y ∧ deriv g y = deriv f y ∧ deriv (deriv g) y = deriv (deriv f) y

namespace IFS

variable {N : ℕ} {ε ε' : ℝ}

/-! ## Dual compositions along an orbit -/

/-- If `g_{w_m}` agrees with `f_{w_m}` to second order at `f_{w_{m-1}} ∘ ⋯ ∘ f_{w_0}(z)` for every
`m < |w|`, then `G_w h = F_w h` at `z`. -/
private theorem dualComp_eq_of_agreeAt (Φ : IFS N ε) (Ψ : IFS N ε') {w : List (Fin N)} {z : ℂ}
    (hag : ∀ m (hm : m < w.length),
      AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse z))
    (h : ℂ → ℂ) : Ψ.dualComp w h z = Φ.dualComp w h z := by
  induction w generalizing z with
  | nil => rfl
  | cons i w ih =>
    obtain ⟨h0, h1, h2⟩ := hag 0 (by simp)
    simp only [List.getElem_cons_zero, List.take_zero, List.reverse_nil, comp_nil, id] at h0 h1 h2
    show deriv (Ψ.f i) z * Ψ.dualComp w h (Ψ.f i z) + Ψ.nonlin i z =
      deriv (Φ.f i) z * Φ.dualComp w h (Φ.f i z) + Φ.nonlin i z
    rw [h0, ih fun m hm => by
      have := hag (m + 1) (by simp [hm])
      rwa [List.take_succ_cons, List.reverse_cons, Φ.comp_append, List.getElem_cons_succ] at this,
      h1, nonlin, nonlin, h1, h2]

/-- The cylinder intervals of `Φ` and `Ψ` at `x ∈ I` agree when the maps agree to second order
along the orbit. -/
theorem dualCylAt_eq_of_agreeAt (Φ : IFS N ε) (Ψ : IFS N ε') (k K : ℝ) {w : List (Fin N)}
    {x : ℝ} (hx : x ∈ I)
    (hag : ∀ m (hm : m < w.length),
      AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse x).re) :
    Ψ.dualCylAt k K w x = Φ.dualCylAt k K w x := by
  have hag' : ∀ m (hm : m < w.length),
      AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse x) :=
    fun m hm => by rw [Φ.comp_ofReal _ hx]; exact hag m hm
  rw [dualCylAt, dualCylAt, dualComp_eq_of_agreeAt Φ Ψ hag', dualComp_eq_of_agreeAt Φ Ψ hag']

/-- Under the hypothesis of `dualComp_cons_eq_of_agreeAt` at a real point `x ∈ I`, the cylinder
interval of `Ψ` at `x` is that of `Φ` shifted by the real part of the change of `f_i''/f_i'`. -/
theorem dualCylAt_cons_eq_of_agreeAt (Φ : IFS N ε) (Ψ : IFS N ε') (k K : ℝ) {i : Fin N}
    {w : List (Fin N)} {x : ℝ} (hx : x ∈ I) (h0 : Ψ.f i x = Φ.f i x)
    (h1 : deriv (Ψ.f i) x = deriv (Φ.f i) x)
    (hag : ∀ m (hm : m < w.length),
      AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp ((i :: w).take (m + 1)).reverse x).re) :
    Ψ.dualCylAt k K (i :: w) x =
      (· + (Ψ.nonlin i x - Φ.nonlin i x).re) '' Φ.dualCylAt k K (i :: w) x := by
  have hag' : ∀ m (hm : m < w.length),
      AgreeAt (Φ.f w[m]) (Ψ.f w[m]) (Φ.comp (w.take m).reverse (Φ.f i x)) := fun m hm => by
    have := hag m hm
    rwa [← Φ.comp_ofReal _ hx, List.take_succ_cons, List.reverse_cons, Φ.comp_append] at this
  have heq (h : ℂ → ℂ) :
      Ψ.dualComp (i :: w) h x = Φ.dualComp (i :: w) h x + (Ψ.nonlin i x - Φ.nonlin i x) := by
    show deriv (Ψ.f i) x * Ψ.dualComp w h (Ψ.f i x) + Ψ.nonlin i x =
      (deriv (Φ.f i) x * Φ.dualComp w h (Φ.f i x) + Φ.nonlin i x) + _
    rw [h0, h1, dualComp_eq_of_agreeAt Φ Ψ hag']; ring
  rw [dualCylAt, dualCylAt, image_add_const_uIcc, heq, heq, Complex.add_re, Complex.add_re]

end IFS

/-- Two intersecting sets of diameter less than `δ/3`, one of them shifted by `τ` with
`|τ| ≥ δ`, are disjoint. -/
theorem disjoint_image_add_of_abs_sub_lt {A B : Set ℝ} {δ τ : ℝ}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, |a - a'| < δ / 3) (hB : ∀ b ∈ B, ∀ b' ∈ B, |b - b'| < δ / 3)
    (hAB : (A ∩ B).Nonempty) (hτ : δ ≤ |τ|) : Disjoint ((· + τ) '' A) B := by
  obtain ⟨x, hxA, hxB⟩ := hAB
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ hb
  have h3 : |τ| ≤ |a + τ - x| + |a - x| := by simpa using abs_sub (a + τ - x) (a - x)
  have h0 := hA x hxA x hxA
  rw [sub_self, abs_zero] at h0
  linarith [hA a ha x hxA, hB (a + τ) hb x hxB]

end AnalyticESC
