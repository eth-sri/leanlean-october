module
public import OAI.NumberTheory.DirichletL.Moments.PlainWindowEnergy
public import OAI.NumberTheory.DirichletL.Moments.RestrictedEnergy
public import OAI.NumberTheory.DirichletL.Moments.SmoothedWindowEnergy
import WeylPort.Analytic.RealLaplace

public section

namespace OAI

open scoped Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentRestrictedWindow
open CanonicalQuadraticSieve CenteredMomentRowNorm CenteredMomentRestrictedEnergy
open CenteredMomentPlainWindowEnergy CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

section
variable {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ) (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
include α keep S a ha c U K hK
theorem restricted_hasSum_weighted :
    HasSum (fun z : O => ‖rowPolynomial S a c z‖^2*
      (if keep z then (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0))
      (restrictedEnergy keep S a c U K) := by
  simpa only [mul_ite,mul_zero,restrictedEnergy] using
    (restricted_summable keep S a ha c U K hK).hasSum

theorem finite_weighted_le_restricted
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rows : Finset O) :
    (∑ z∈rows,‖rowPolynomial S a c z‖^2*
      (if keep z then (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0))≤
      restrictedEnergy keep S a c U K := by
  apply sum_le_hasSum rows _ (restricted_hasSum_weighted keep S a ha c U K hK)
  intro z hz
  apply mul_nonneg (sq_nonneg _)
  split_ifs
  grind
  grind
end

section
variable {α : Type*} (keep : O → Prop) (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i})) (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X) (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (E : ℝ) (hE : 0≤E)
include α keep V hVc hVs J S a ha β τ t θ X hX U K hK hU E hE
theorem restricted_window_energy_from_shifted
    (henergy : ∀ w : ℝ,(restrictedEnergy keep S a
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) U K)≤E*(1+‖w‖)^(2*J)) :
    (restrictedEnergy keep S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let u := fun z : O => if keep z then (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hu (z : O) : 0≤u z := by dsimp only [u];split_ifs;exact hU z;exact le_rfl
  pm_2983
  have hnorm (z : O) (x : ℂ) : ‖(Real.sqrt (u z):ℂ)*x‖^2=u z*‖x‖^2 := by
    pm_6185 hu
  have hfin (rows : Finset O) : (∑ z∈rows,‖rowPolynomial S a c z‖^2*u z)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
    let φ := fun z : rows => fun w : ℝ => (Real.sqrt (u z):ℂ)*
      (logPhase (θ-w) (Real.log X)*rowPolynomial S a
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z)
    pm_2984 plain_column_integrable
    have hb (w : ℝ) : (∑ z : rows,‖φ z w‖^2)≤E*((1+‖w‖)^J)^2 := by
      simp only [φ]
      simp_rw [hnorm]
      pm_1444 norm_mul logPhase_norm one_mul pow_mul
      rw [Finset.sum_coe_sort rows (fun z : O => u z*‖rowPolynomial S a
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)]
      have hbound :=
        (finite_weighted_le_restricted keep S a ha _ U K hK hU rows).trans (henergy w)
      rw [Nat.mul_comm 2 J] at hbound
      calc
        _ = ∑ z ∈ rows, ‖rowPolynomial S a
            (fun i => β i * heightCoeff τ (t + 2 * Real.pi * (w - θ))
              (Ideal.span {a i})) z‖ ^ 2 * u z := by
          pm_8454 z hz
        _ ≤ _ := hbound
    pm_2982
    have he (z : rows) : (∫ w : ℝ,columnDensity V hVc hVs w*φ z w)=
        (Real.sqrt (u z):ℂ)*rowPolynomial S a c z := by
      rw [show rowPolynomial S a c z=_ from plain_column_integral S a ha β τ t θ X hX V hVc hVs z,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [φ]
      ring
    simp only [he,hnorm] at hh
    rw [Finset.sum_coe_sort rows (fun z : O => u z*‖rowPolynomial S a c z‖^2)] at hh
    calc
      _ = ∑ z ∈ rows, u z * ‖rowPolynomial S a c z‖ ^ 2 := by
        pm_8454 z hz
      _ ≤ _ := hh
  pm_528 hs restricted_hasSum_weighted keep S a ha c U K hK
  pm_6186 hu

theorem restricted_window_energy_from_height
    (henergy : ∀ v : ℝ,(restrictedEnergy keep S a
      (fun i => β i*heightCoeff τ v (Ideal.span {a i})) U K)≤E*(1+‖v‖)^(2*J)) :
    (restrictedEnergy keep S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K)≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by pf_135 (restricted_window_energy_from_shifted keep)
end

end SevenEighths.CenteredMomentRestrictedWindow


end OAI
