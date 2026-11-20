module

public import OAI.NumberTheory.DirichletL.Hecke.DyadicBuffered

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ContDiff
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

theorem contour_mem_rect {l r T x t : ℝ} (hlr : l≤r) (hT : 0≤T)
    (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
    ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
  change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
  simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using And.intro hx ht

theorem mellin_le_of_higher_decay (W : ℝ → ℂ) (x t C : ℝ) (n : ℕ)
    (h : (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤C) :
    (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤C := by
  apply le_trans _ h
  gcongr
  · exact le_add_of_nonneg_right (abs_nonneg t)
  · omega

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
  have hDp : 0<D := by linarith
  have hcentral := central_segment_bound χ inverse W D l σ freq C₂ Kc T hDp hC₂ hKc hT
    hm₂ hcentralSeries
  have hbottom := horizontal_join_bound χ inverse W D σ freq l r (-T) Cn K n hD hlr hCn
    (fun x hx => mellin_le_of_higher_decay W x (-T) Cn n (hmn x hx (-T))) (fun x hx => hs _ (contour_mem_rect hlr hT hx ⟨le_rfl,by linarith⟩))
  have htop := horizontal_join_bound χ inverse W D σ freq l r T Cn K n hD hlr hCn
    (fun x hx => mellin_le_of_higher_decay W x T Cn n (hmn x hx T)) (fun x hx => hs _ (contour_mem_rect hlr hT hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := absolute_tail_bound χ inverse W D r σ freq Cn T n hDp hr hCn hT
    (hmn r ⟨hlr,le_rfl⟩)
  rw [polynomial_finite_shift χ hχ inverse W a b ha hWs hW D σ freq l r T hDp hr hT hz,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

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
       (Cn*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi) := by
  apply polynomial_bound_of_rectangle_split χ hχ inverse W a b ha hWs hW
    D σ freq l r T C₂ Cn K K n hD hlr hr hT hC₂ hCn hK hK hm₂ hmn _ hz hs
  intro t ht
  exact hs _ (contour_mem_rect hlr hT ⟨le_rfl,hlr⟩ ht)

/-- Rescale the central integral and the two outer contributions with a common constant. -/
lemma rescale_rectangle_bound {q C₂ Cn E c d x y L J P w W V : ℝ} {n : ℕ}
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hE : 0≤E) (hc : 0≤c) (hd : 0≤d)
    (hx : 0≤x) (hy : 0≤y) (hJ₀ : 0≤J) (hV : 0≤V)
    (hL : L≤c*x) (hJ : J≤d*y) (hP : P≤y) (hw : |w|≤W)
    (h : q≤(1/(2*Real.pi))*(C₂*L*Real.pi+2*(Cn*J/(1+V)^n)*|w|+Cn*P*E/(1+V)^n*Real.pi)) :
    let C := 1+c*Real.pi+2*d*W+E*Real.pi
    q≤C*C₂*x+C*Cn*y/(1+V)^n := by
  dsimp only
  have hW := (abs_nonneg w).trans hw
  have hπ := Real.pi_pos
  have hfac : 1/(2*Real.pi)≤(1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  apply h.trans
  calc
    _ ≤ (1/(2*Real.pi))*(C₂*(c*x)*Real.pi+2*(Cn*(d*y)/(1+V)^n)*W+Cn*y*E/(1+V)^n*Real.pi) := by
      gcongr
    _ ≤ _ := mul_le_of_le_one_left (by positivity) hfac
    _ = (c*Real.pi)*C₂*x+(2*d*W+E*Real.pi)*Cn*y/(1+V)^n := by ring
    _ ≤ _ := by
      gcongr
      · linarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hd) hW, mul_nonneg hE hπ.le]
      · linarith [mul_nonneg hc hπ.le]

end SevenEighths.HeckeDyadic

end

end OAI
