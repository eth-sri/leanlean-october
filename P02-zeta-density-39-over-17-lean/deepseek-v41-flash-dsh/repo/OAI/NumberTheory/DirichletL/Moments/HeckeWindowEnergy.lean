module
public import OAI.NumberTheory.DirichletL.Moments.HeckeColumnWindow

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeWindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem finite_weighted_integral_energy {κ : Type*} [Fintype κ]
    (b : ℝ → ℂ) (φ : κ → ℝ → ℂ) (w : ℝ → ℝ) (hw : ∀ t,0<w t)
    (E : ℝ) (hE : 0≤E) (hb : Integrable (fun t => w t*‖b t‖))
    (hφ : ∀ k,Integrable (fun t => b t*φ k t))
    (hbound : ∀ t,(∑ k,‖φ k t‖^2)≤E*(w t)^2) :
    (∑ k,‖∫ t : ℝ,b t*φ k t‖^2)≤E*(∫ t : ℝ,w t*‖b t‖)^2 := by
  have hn (t : ℝ) : (w t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hw t).ne'
  have hnorm (t : ℝ) : ‖(w t:ℂ)‖=w t := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hw t)]
  have he (k : κ) (t : ℝ) : ((w t:ℂ)*b t)*(φ k t/(w t:ℂ))=b t*φ k t := by
    field_simp [hn t]
  have hh := CompletedGauss.finite_integral_energy_bound
    (fun t => (w t:ℂ)*b t) (fun k t => φ k t/(w t:ℂ)) E hE
    (by simpa only [norm_mul,hnorm] using hb)
    (fun k => by simpa only [he] using hφ k) (fun t => by
      simp only [norm_div,hnorm,div_pow,← Finset.sum_div]
      exact (div_le_iff₀ (sq_pos_of_pos (hw t))).mpr (hbound t))
  simpa only [he,norm_mul,hnorm] using hh

theorem gauss_column_integrable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      gaussPolynomial S a ha (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z) := by
  have hi (i : α) := ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul (β i)).mul_const
    (gaussRow (a i) (ha i) z)
  convert integrable_finsetSum S (fun i _ => hi i) using 1
  funext w
  simp only [gaussPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def heightCost (t θ : ℝ) : ℝ := (1+‖t‖+2*Real.pi*‖θ‖)*(1+2*Real.pi)

theorem heightCost_pos (t θ : ℝ) : 0<heightCost t θ := by
  unfold heightCost
  positivity

theorem norm_height_shift (t θ w : ℝ) :
    1+‖t+2*Real.pi*(w-θ)‖≤heightCost t θ*(1+‖w‖) := by
  have hπ : 0≤2*Real.pi := by positivity
  have hn := norm_add_le t (2*Real.pi*(w-θ))
  rw [norm_mul,Real.norm_of_nonneg hπ] at hn
  have hs := norm_sub_le w θ
  have hr : 1+‖t+2*Real.pi*(w-θ)‖≤1+‖t‖+2*Real.pi*‖θ‖+2*Real.pi*‖w‖ := by
    nlinarith
  have hb : 1≤1+‖t‖+2*Real.pi*‖θ‖ := by
    nlinarith [norm_nonneg t,mul_nonneg hπ (norm_nonneg θ)]
  have hw : 0≤2*Real.pi*‖w‖ := by positivity
  calc
    _ ≤ (1+‖t‖+2*Real.pi*‖θ‖)*(1+2*Real.pi*‖w‖) := by nlinarith
    _ ≤ _ := by
      unfold heightCost
      rw [mul_assoc (1+‖t‖+2*Real.pi*‖θ‖) (1+2*Real.pi) (1+‖w‖)]
      apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hb)
      nlinarith [norm_nonneg w,Real.pi_pos]

end SevenEighths.CenteredMomentHeckeWindowEnergy

end

end OAI
