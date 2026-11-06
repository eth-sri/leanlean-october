module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import RequestProject.HerglotzForm
public import RequestProject.Reparam

/-!
# Reparametrization of the actual Herglotz boundary bound

A monotone Lipschitz change of parameter fixing `0` and `2π` preserves the
initial Herglotz jet and the monodromy. Consequently it preserves both the
actual observation of the conormal density and the Herglotz quadratic form.
The finite number of linear conditions on the direction density is unchanged.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open scoped Real InnerProductSpace

variable {γ : ℝ → ℂ} {K : NNReal}

/-- The observation of a genuine Herglotz conormal density is unchanged by an
orientation-preserving Lipschitz reparametrization fixing the endpoints. -/
theorem observationAdj_herglotz_comp (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0)
    {τ : ℝ → ℝ} (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ)
    (h0 : τ 0 = 0) (hL : τ (2 * π) = 2 * π)
    {E : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport (γ ∘ τ) E W')
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    observationAdj W' (herglotzConormal (Real.sqrt E) a (γ ∘ τ)) =
      observationAdj W (herglotzConormal (Real.sqrt E) a γ) := by
  have hU := monodromy_comp hK hm hτ h0 hL hW hW'
  rw [(herglotzForm_eq (hK.comp hτ) (by
    simp_all) hW' ha).1,
    (herglotzForm_eq hK hclosed hW ha).1]
  change (Real.sqrt 2 * Complex.I) • (monodromy W' - 1)
      (herglotzVec ha (Real.sqrt E) ((γ ∘ τ) 0)) =
    (Real.sqrt 2 * Complex.I) • (monodromy W - 1)
      (herglotzVec ha (Real.sqrt E) (γ 0))
  simp_all

/-- The genuine Herglotz form is unchanged by the same reparametrization. -/
theorem herglotzForm_comp (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0)
    {τ : ℝ → ℝ} (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ)
    (h0 : τ 0 = 0) (hL : τ (2 * π) = 2 * π)
    {E : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport (γ ∘ τ) E W')
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    herglotzForm W' (γ ∘ τ) E a = herglotzForm W γ E a := by
  have hU := monodromy_comp hK hm hτ h0 hL hW hW'
  simp_all [herglotzForm_eq_im (hK.comp hτ) (by     simp_all) hW' ha, herglotzForm_eq_im hK hclosed hW ha]

/-- The same equality also transfers a density bound back to the original
curve. No Lipschitz estimate for the inverse change of parameter is needed. -/
theorem herglotz_density_lower_bound_of_comp (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0)
    {τ : ℝ → ℝ} (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ)
    (h0 : τ 0 = 0) (hL : τ (2 * π) = 2 * π)
    {E A : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport (γ ∘ τ) E W')
    {m : ℕ} (L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hbound : ∀ a, IsDirDensity a → L a = 0 →
      -(A * ‖observationAdj W' (herglotzConormal (Real.sqrt E) a (γ ∘ τ))‖ ^ 2) ≤
        herglotzForm W' (γ ∘ τ) E a) :
    ∀ a, IsDirDensity a → L a = 0 →
      -(A * ‖observationAdj W (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
        herglotzForm W γ E a := by
  intro a ha hLa
  have hb := hbound a ha hLa
  simp_all [observationAdj_herglotz_comp hK hclosed hm hτ h0 hL hW hW' ha, herglotzForm_comp hK hclosed hm hτ h0 hL hW hW' ha]

end PolyaNeumann

end
