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

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) {τ : ℝ → ℝ} (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ) (h0 : τ 0 = 0) (hL : τ (2 * π) = 2 * π)
include γ K hK hclosed τ hm Kτ hτ h0 hL

/-- The same equality also transfers a density bound back to the original
curve. No Lipschitz estimate for the inverse change of parameter is needed. -/
theorem herglotz_density_lower_bound_of_comp 
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
  have hc : (γ ∘ τ) (2 * π) = (γ ∘ τ) 0 := by simp [Function.comp_apply, h0, hL, hclosed]
  have hU := monodromy_comp hK hm hτ h0 hL hW hW'
  change ContinuousLinearMap.adjoint (W' (2 * π)) = ContinuousLinearMap.adjoint (W (2 * π)) at hU
  obtain ⟨hO, hF⟩ := herglotzForm_eq hK hclosed hW ha
  obtain ⟨hO', hF'⟩ := herglotzForm_eq (hK.comp hτ) hc hW' ha
  have hb := hbound a ha hLa
  simp only [hF', hO', hU, Function.comp_apply, h0] at hb
  simpa only [hF, hO] using hb

end

end PolyaNeumann

end
