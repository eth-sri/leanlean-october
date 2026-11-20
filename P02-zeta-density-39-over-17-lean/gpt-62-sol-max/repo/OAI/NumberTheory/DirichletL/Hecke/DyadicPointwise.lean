module
public import OAI.NumberTheory.DirichletL.Hecke.DyadicBuffered

@[expose] public section

namespace OAI

noncomputable section
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

theorem rectangle_mem_of_mem_Icc {l r T x t : ℝ} (hlr : l≤r) (hT : 0≤T)
    (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
    ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
  change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
  simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using And.intro hx ht

/-- Bounds for the left, horizontal, and absolute right tails of one Mellin rectangle. -/
theorem mellin_rectangle_bound (L : ℂ → ℂ) (W : ℝ → ℂ)
    (D σ freq l r T C₂ Cn K Kc Ka : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hKc : 0≤Kc)
    (hhol : DifferentiableOn ℂ (mellinIntegrand L W D σ freq) (uIcc l r ×ℂ uIcc (-T) T))
    (hi : Integrable (fun t : ℝ => mellinIntegrand L W D σ freq ((r : ℂ)+t*I)))
    (ha : ∀ t : ℝ, ‖L ((r : ℂ)+t*I+shift σ freq)‖≤Ka)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hcentralSeries : ∀ t ∈ Icc (-T) T, ‖L ((l : ℂ)+t*I+shift σ freq)‖≤Kc)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖L (s+shift σ freq)‖≤K) :
    ‖(1/(2*Real.pi) : ℂ)*(∫ t : ℝ, mellinIntegrand L W D σ freq ((r : ℂ)+t*I))‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*Kc*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*Ka)/(1+T)^n*Real.pi) := by
  have hDp : 0<D := by linarith
  have hmem {x t : ℝ} hx ht := @rectangle_mem_of_mem_Icc l r T x t hlr hT hx ht
  have hcentral := mellin_central_bound L W D l σ freq C₂ Kc T hDp hC₂ hKc hT
    hm₂ hcentralSeries
  have hm (x : ℝ) (hx : x∈Icc l r) (t : ℝ) :
      (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤Cn := by
    apply le_trans _ (hmn x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · omega
  have hbottom := mellin_join_bound L W D σ freq l r (-T) Cn K n hD hlr hCn
    (fun x hx => hm x hx (-T)) (fun x hx => hs _ (hmem hx ⟨le_rfl,by linarith⟩))
  have htop := mellin_join_bound L W D σ freq l r T Cn K n hD hlr hCn
    (fun x hx => hm x hx T) (fun x hx => hs _ (hmem hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := mellin_tail_bound L W D r σ freq Cn T Ka n hDp hCn hT ha
    (hmn r ⟨hlr,le_rfl⟩)
  rw [vertical_integral_shift _ l r T hT hi hhol,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

theorem polynomial_bound_of_rectangle_split (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K Kc : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hr : 1<r+σ) (hT : 0≤T)
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
      (C₂*D^(l+σ-1/2)*Kc*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0<D := zero_lt_one.trans_le hD
  rw [polynomial_mellin χ inverse W a b ha hWs hW D r σ freq hDp hr]
  exact mellin_rectangle_bound (series χ inverse) W D σ freq l r T C₂ Cn K Kc _ n hD hlr hT
    hC₂ hCn hKc
    (mellinIntegrand_on_rectangle _ W a b ha hWs hW D σ freq l r T hDp
      (fun z hz' => series_differentiableAt_nonprincipal χ hχ inverse (hz z hz')))
    (integrand_vertical_integrable χ inverse W a b ha hWs hW D r σ freq hDp hr)
    (fun _ => series_norm_le χ inverse hr (by simp)) hm₂ hmn hcentralSeries hs

theorem polynomial_bound_of_rectangle (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hr : 1<r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ inverse (s+shift σ freq)‖≤K) :
    ‖polynomial χ inverse W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*K*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi) :=
  polynomial_bound_of_rectangle_split χ hχ inverse W a b ha hWs hW D σ freq l r T C₂ Cn K K n
    hD hlr hr hT hC₂ hCn hK hK hm₂ hmn
    (fun t ht => hs _ (rectangle_mem_of_mem_Icc hlr hT ⟨le_rfl,hlr⟩ ht)) hz hs

end SevenEighths.HeckeDyadic

end

end OAI
