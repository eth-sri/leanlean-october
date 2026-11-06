module

public import AnalyticESC.Dual.Cylinders
set_option hygiene false
local notation "𝖕" => Ψ.f w[m]

local notation "𝖔" => Φ.f w[m]


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

variable {x : ℝ}



/-- `g` agrees with `f` to second order at `y`: equal values, first and second derivatives. -/
def AgreeAt (f g : ℂ → ℂ) (y : ℂ) : Prop :=
  g y = f y ∧ deriv g y = deriv f y ∧ 𝔇 g y = 𝔇 f y

namespace IFS

variable (Φ : IFS N ε) (Ψ : IFS N ε') (k K : ℝ)

/-! ## Dual compositions along an orbit -/

/-- If `g_{w_m}` agrees with `f_{w_m}` to second order at `f_{w_{m-1}} ∘ ⋯ ∘ f_{w_0}(z)` for every
`m < |w|`, then `G_w h = F_w h` at `z`. -/
theorem dualComp_eq_of_agreeAt
    (hag : ∀ m (hm : m < w.length),
      AgreeAt 𝖔 𝖕 (Φ.comp (w.take m).reverse z))
    (h : ℂ → ℂ) : Ψ.dualComp w h z = Φ.dualComp w h z := by
  induction w generalizing z with
  | nil => rfl
  | cons i w ih =>
    obtain ⟨h0, h1, h2⟩ := hag 0 (by simp)
    simp at h0 h1 h2
    have := ih fun m hm => by
      have := hag (m + 1) (by simp_all); rw [List.getElem_cons_succ] at this; simpa [Φ.comp_append]
    simp [dualComp, dualOp, nonlin] at this ⊢
    rw [h0, this, h1, h2]

/-- If `g_i` agrees with `f_i` to first order at a real point `x`, and the later maps agree to
second order along the orbit of `f_i(x)`, then the cylinder interval of `Ψ` at `x` is that of `Φ`
shifted by the real part of the change of `f_i''/f_i'`. -/
theorem dualCylAt_cons_eq_of_agreeAt
    (h0 : Ψ.f i x = Φ.f i x)
    (h1 : 𝔡 Ψ i x = 𝔡 Φ i x)
    (hag : ∀ m (hm : m < w.length),
      AgreeAt 𝖔 𝖕 (Φ.comp (w.take m).reverse (Φ.f i x))) :
    Ψ.dualCylAt k K (i :: w) x =
      (· + (Ψ.nonlin i x - Φ.nonlin i x).re) '' Φ.dualCylAt k K (i :: w) x := by
  simp [dualCylAt, dualComp, dualOp, h0, h1]
  rw [← dualComp, ← dualComp]
  simp [dualComp_eq_of_agreeAt Φ Ψ hag]
  ring_nf

/-- The cylinder intervals of `Φ` and `Ψ` at `x` agree under the hypothesis of
`dualComp_eq_of_agreeAt`. -/
theorem dualCylAt_eq_of_agreeAt
    (hag : ∀ m (hm : m < w.length),
      AgreeAt 𝖔 𝖕 (Φ.comp (w.take m).reverse x)) :
    Ψ.dualCylAt k K w x = Φ.dualCylAt k K w x := by
  simp [dualCylAt, dualComp_eq_of_agreeAt Φ Ψ hag]

end IFS

/-- Two intersecting sets of diameter less than `δ/3`, one of them shifted by `τ` with
`|τ| ≥ δ`, are disjoint. -/
theorem disjoint_image_add_of_abs_sub_lt {δ τ : ℝ}
    (hA : ∀ a ∈ A, ∀ a' ∈ A, |a - a'| < δ / 3) (hB : ∀ b ∈ B, ∀ b' ∈ B, |b - b'| < δ / 3)
    (hAB : (A ∩ B).Nonempty) (hτ : δ ≤ |τ|) : Disjoint ((· + τ) '' A) B := by
  obtain ⟨x, hxA, hxB⟩ := hAB
  grind

end AnalyticESC
