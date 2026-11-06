module
public import OAI.NumberTheory.DirichletL.Hecke.DyadicBuffered
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical Topology ContDiff
open Set MeasureTheory Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem norm_four_sides (A B C D : ℂ) :
    ‖A+I*(B-C)+D‖≤‖A‖+‖B‖+‖C‖+‖D‖ := by
  have h₁ := norm_add_le (A+I*(B-C)) D
  have h₂ := norm_add_le A (I*(B-C))
  have h₃ := norm_sub_le B C
  simp only [norm_mul,norm_I,one_mul] at h₂
  linarith

section
variable (χ : Character) (hχ : χ.residue≠1) (inverse : Bool) (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
include χ hχ inverse W a b ha hWs hW
theorem polynomial_bound_of_rectangle
    (D σ freq l r T C₂ Cn K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤ r) (hr : 1< r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ inverse (s+shift σ freq)‖≤K) :
    ‖polynomial χ inverse W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D ^(l+σ-1/2)*K*Real.pi +
       2*(Cn*D ^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D ^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi) := by
  pm_3107
  have hcentral := central_segment_bound χ inverse W D l σ freq C₂ K T hDp hC₂ hK hT
    hm₂ (fun t ht => hs _ (hmem l t ⟨le_rfl,hlr⟩ ht))
  pm_3106

theorem polynomial_bound_of_rectangle_split
    (D σ freq l r T C₂ Cn K Kc : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤ r) (hr : 1< r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K) (hKc : 0≤Kc)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hcentralSeries : ∀ t ∈ Icc (-T) T, ‖series χ inverse ((l : ℂ)+t*I+shift σ freq)‖≤Kc)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ inverse (s+shift σ freq)‖≤K) :
    ‖polynomial χ inverse W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D ^(l+σ-1/2)*Kc*Real.pi +
       2*(Cn*D ^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D ^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi) := by
  pm_3107
  have hcentral := central_segment_bound χ inverse W D l σ freq C₂ Kc T hDp hC₂ hKc hT
    hm₂ hcentralSeries
  pm_3106
end

end SevenEighths.HeckeDyadic


end OAI
