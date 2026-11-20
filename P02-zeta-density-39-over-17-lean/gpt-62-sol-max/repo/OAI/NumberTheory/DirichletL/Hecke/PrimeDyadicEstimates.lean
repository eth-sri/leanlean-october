module
public import OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicContour
public import OAI.NumberTheory.DirichletL.Hecke.DyadicPointwise

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem polynomial_bound_of_rectangle (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hr : 1<r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ (s+shift σ freq)‖≤K) :
    ‖polynomial χ W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*K*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*eulerBound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0<D := zero_lt_one.trans_le hD
  rw [polynomial_mellin χ W a b ha hWs hW D r σ freq hDp hr]
  have habs (t : ℝ) := series_norm_le χ hr (s := (r : ℂ)+t*I+shift σ freq) (by simp)
  exact mellin_rectangle_bound (series χ) W D σ freq l r T C₂ Cn K K _ n hD hlr hT hC₂ hCn hK
    (mellinIntegrand_on_rectangle _ W a b ha hWs hW D σ freq l r T hDp
      (fun z hz' => series_differentiableAt_nonprincipal χ hχ (hz z hz')))
    (mellinIntegrand_vertical_integrable _ W a b ha hWs hW D r σ freq hDp _
      (fun _ => series_differentiableAt_right χ (by simpa using hr)) habs)
    habs hm₂ hmn (fun t ht => hs _ (rectangle_mem_of_mem_Icc hlr hT ⟨le_rfl,hlr⟩ ht)) hs

end SevenEighths.HeckePrimeDyadic

end

end OAI
