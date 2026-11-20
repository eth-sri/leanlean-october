module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import RequestProject.HerglotzForm
public import RequestProject.Reparam
public import RequestProject.PlanarNotation

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

/-- The observation of a genuine Herglotz conormal density is unchanged by an
orientation-preserving Lipschitz reparametrization fixing the endpoints. -/
theorem observationAdj_herglotz_comp {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ anglePeriod = γ 0)
    {τ : ℝ → ℝ} (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ)
    (h0 : τ 0 = 0) (hL : τ anglePeriod = anglePeriod)
    {E : ℝ} {W W' : TransportPath}
    (hW : IsTransport γ E W) (hW' : IsTransport (γ ∘ τ) E W')
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    observationAdj W' (herglotzConormal (Real.sqrt E) a (γ ∘ τ)) =
      observationAdj W (herglotzConormal (Real.sqrt E) a γ) := by
  
  
  rw [(herglotzForm_eq (hK.comp hτ) (by
    simp [hL, h0, hclosed]) hW' ha).1,
    (herglotzForm_eq hK hclosed hW ha).1]
  change (vacuumWeight * Complex.I) • (monodromy W' - 1)
      (herglotzVec ha (Real.sqrt E) ((γ ∘ τ) 0)) =
    (vacuumWeight * Complex.I) • (monodromy W - 1)
      (herglotzVec ha (Real.sqrt E) (γ 0))
  simp [h0, (monodromy_comp hK hm hτ h0 hL hW hW')]

/-- The genuine Herglotz form is unchanged by the same reparametrization. -/
theorem herglotzForm_comp {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ anglePeriod = γ 0)
    {τ : ℝ → ℝ} (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ)
    (h0 : τ 0 = 0) (hL : τ anglePeriod = anglePeriod)
    {E : ℝ} {W W' : TransportPath}
    (hW : IsTransport γ E W) (hW' : IsTransport (γ ∘ τ) E W')
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    herglotzForm W' (γ ∘ τ) E a = herglotzForm W γ E a := by
  
  
  rw [herglotzForm_eq_im (hK.comp hτ) (by
    simp [hL, h0, hclosed]) hW' ha,
    herglotzForm_eq_im hK hclosed hW ha]
  simp [h0, (monodromy_comp hK hm hτ h0 hL hW hW')]

/-- The same equality also transfers a density bound back to the original
curve. No Lipschitz estimate for the inverse change of parameter is needed. -/
theorem herglotz_density_lower_bound_of_comp {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ anglePeriod = γ 0)
    {τ : ℝ → ℝ} (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ)
    (h0 : τ 0 = 0) (hL : τ anglePeriod = anglePeriod)
    {E A : ℝ} {W W' : TransportPath}
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
  rw [observationAdj_herglotz_comp hK hclosed hm hτ h0 hL hW hW' ha,
    herglotzForm_comp hK hclosed hm hτ h0 hL hW hW' ha] at hb
  exact hb

end PolyaNeumann

end
