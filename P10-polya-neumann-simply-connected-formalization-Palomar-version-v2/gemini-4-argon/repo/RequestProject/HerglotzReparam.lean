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

/-- The same equality also transfers a density bound back to the original
curve. No Lipschitz estimate for the inverse change of parameter is needed. -/
theorem herglotz_density_lower_bound_of_comp  
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0)
     (hm : Monotone τ) {Kτ} (hτ : LipschitzWith Kτ τ)
    (h0 : τ 0 = 0) (hL : τ (2 * π) = 2 * π)
     
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
  rw [show observationAdj W' (herglotzConormal (Real.sqrt E) a (γ ∘ τ)) = observationAdj W (herglotzConormal (Real.sqrt E) a γ) by
    have hclosed' : (γ ∘ τ) (2 * π) = (γ ∘ τ) 0 := by
      change γ (τ (2 * π)) = γ (τ 0)
      rw [hL, h0, hclosed]
    rw [(herglotzForm_eq (hK.comp hτ) hclosed' hW' ha).1,
      (herglotzForm_eq hK hclosed hW ha).1]
    change ((Real.sqrt 2) * Complex.I) • (monodromy W' - 1)
        (herglotzVec ha (Real.sqrt E) ((γ ∘ τ) 0)) =
      ((Real.sqrt 2) * Complex.I) • (monodromy W - 1)
        (herglotzVec ha (Real.sqrt E) (γ 0))
    simp [h0, monodromy_comp hK hm hτ h0 hL hW hW'],
    show herglotzForm W' (γ ∘ τ) E a = herglotzForm W γ E a by
      rw [herglotzForm_eq_im (hK.comp hτ) (by
        change γ (τ (2 * π)) = γ (τ 0)
        rw [hL, h0, hclosed]) hW' ha,
        herglotzForm_eq_im hK hclosed hW ha]
      simp [h0, monodromy_comp hK hm hτ h0 hL hW hW']] at hb
  exact hb

end PolyaNeumann

end
