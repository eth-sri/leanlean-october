module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
public import OAI.NumberTheory.DirichletL.Moments.SmoothedWindowEnergy

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplifiedRetainedRadius
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice CenteredMomentGaussEnergy
open CenteredMomentSmoothedWindowEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentAmplificationErrorEnergy CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentGaussNormalization


section
variable (x : ℝ) (Q : Finset (Ideal ActualEisensteinCubic.O)) (c f : Ideal ActualEisensteinCubic.O→ℂ) (Y V : ℝ) (hx : 0≤x) (hY : 0<Y) (hV : 0<V) (hscale : 2*Y≤V)

include hx in
theorem ballProfile_support_upper     (h : ballProfile x≠0) : x<2 := by
  have hb : x∈Function.support QuadraticInitialBound.sieveBump := by
    simp_all
  rw [QuadraticInitialBound.sieveBump.support_eq] at hb
  simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hx,
    QuadraticInitialBound.sieveBump] using hb

include hx hY hV hscale in
theorem ballProfile_radius_le        
      : (ballProfile (x/Y)).re≤(ballProfile (x/V)).re := by
  by_cases hz : ballProfile (x/Y)=0
  · simpa only [hz,Complex.zero_re] using ballProfile_nonneg (x/V)
  have hs := ballProfile_support_upper (x/Y) (div_nonneg hx hY.le) hz
  have hxy : x≤V := ((div_lt_iff₀ hY).mp hs).le.trans hscale
  rw [ballProfile_one (x/V) (div_nonneg hx hV.le) ((div_le_one hV).mpr hxy)]
  exact ballProfile_le_one _

theorem gaussEnergy_radius_le {α : Type*} (S : Finset α) (a : α→ActualEisensteinCubic.O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
     Y V  (hY : 0<Y) (hV : 0<V) (hscale : 2*Y≤V) :
    (gaussEnergy S a ha c ballProfile Y).re≤(gaussEnergy S a ha c ballProfile V).re := by
  have h1 := gaussEnergy_hasSum_re S a ha c ballProfile Y hY
  have h2 := gaussEnergy_hasSum_re S a ha c ballProfile V hV
  rw [←h1.tsum_eq,←h2.tsum_eq]
  apply Summable.tsum_le_tsum _ h1.summable h2.summable
  intro z
  exact mul_le_mul_of_nonneg_left
    (ballProfile_radius_le _ Y V (sq_nonneg _) hY hV hscale) (sq_nonneg _)

include hY hV hscale in
theorem sourceGaussEnergy_radius_le    
            :
    (sourceGaussEnergy Q c f ballProfile Y).re≤(sourceGaussEnergy Q c f ballProfile V).re :=
  gaussEnergy_radius_le _ _ _ _ Y V hY hV hscale

end

section
variable (d K0 j c g sigma δ Z : ℝ) (p : ActualEisensteinCubic.O) (k : ℕ) (hδ : 0≤δ) (hj : j≤K0+δ) (a b reserve : ℝ)

theorem childEnergy_radius_le {ι : Type*} [Fintype ι]
    (D : OriginalData ι)  τ   p   n 
     t T Y V  (hT : 0≤T) (hY : 0<Y) (hV : 0<V) (hscale : 2*Y≤V) :
    D.childEnergy τ p n t T Y≤D.childEnergy τ p n t T V := by
  unfold OriginalData.childEnergy
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by positivity) (localErrorCost_nonneg p n))
  apply div_le_div_of_nonneg_right _ (div_nonneg hT (by positivity))
  apply Finset.sum_le_sum
  intro χ _
  apply Finset.sum_le_sum
  intro B _
  exact sourceGaussEnergy_radius_le _ _ _ Y V hY hV hscale



include hδ hj in
lemma envelope_exponent       :
    j+(max (d+K0-j-c) 0+g)≤K0+max (d-c) 0+g+δ := by
  grind

include hδ hj in
theorem main_exponent_envelope       :
    j+mainGain (d+K0-j) c sigma≤K0+max (d-c) 0+2*sigma+δ :=
  envelope_exponent d K0 j c (2*sigma) δ hδ hj

include hδ hj in
theorem error_exponent_envelope      
        :
    j+errorGain (d+K0-j) c sigma Z p k≤
      K0+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+δ := by
  grind [envelope_exponent, errorRemoval, errorMoving, errorGain]

theorem eventually_support_reserve   (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ 2≤Z^reserve := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hreserve).eventually (eventually_ge_atTop (2:ℝ))] with Z hZ hpow
  exact ⟨hZ,hpow⟩

lemma doubled_radius_le   (hZ : 1<Z) (hab : a≤b)
    (hreserve : 2≤Z^reserve) : 2*Z^a≤Z^(b+reserve) := by
  rw [Real.rpow_add (zero_lt_one.trans hZ)]
  calc
    _≤2*Z^b := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le hab) (by norm_num)
    _≤Z^b*Z^reserve := by
      rw [mul_comm (Z^b)]
      bound

end

def mainCommonRadius (Z d K0 c sigma δ reserve : ℝ)  :=
  Z^(K0+max (d-c) 0+2*sigma+δ+reserve)

def errorCommonRadius (Z d K0 c sigma δ reserve : ℝ) (p : ActualEisensteinCubic.O) (k : ℕ)  :=
  Z^(K0+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+δ+reserve)

theorem main_energy_common {α : Type*} (S : Finset α) (a : α→ActualEisensteinCubic.O)
    (ha : ∀i,Supported (Ideal.span {a i})) (coeff : α→ℂ)
     Z d K0 j c sigma δ reserve  (hZ : 1<Z) (hδ : 0≤δ)
    (hj : j≤K0+δ) (hreserve : 2≤Z^reserve) :
    (gaussEnergy S a ha coeff ballProfile (Z^(j+mainGain (d+K0-j) c sigma))).re≤
      (gaussEnergy S a ha coeff ballProfile (mainCommonRadius Z d K0 c sigma δ reserve)).re := by
  apply gaussEnergy_radius_le _ _ _ _ _ _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  simp_all [doubled_radius_le, main_exponent_envelope]

theorem child_energy_common {ι : Type*} [Fintype ι]
    (D : OriginalData ι)  τ   p   n 
     t T Z d K0 j c sigma δ reserve  (hT : 0≤T) (hZ : 1<Z) (hδ : 0≤δ)
    (hj : j≤K0+δ) (hreserve : 2≤Z^reserve) :
    D.childEnergy τ p n t T (Z^(j+errorGain (d+K0-j) c sigma Z p (n+1)))≤
      D.childEnergy τ p n t T (errorCommonRadius Z d K0 c sigma δ reserve p (n+1)) := by
  apply childEnergy_radius_le D τ p n t T _ _ hT
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  simp_all [doubled_radius_le, error_exponent_envelope]

open CenteredMomentFirstScale

theorem retained_nominal_upper  I J E  (hE : E≠0)
    (K X Z Csec Tsec xi : ℝ) (hK : 0<K) (hX : 0<X) (hZ : 1<Z)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E K X)
     n  (hn : Retained (frequencyRadius Tsec Z xi) n) :
    Real.logb Z (dyadicScale n)≤nominalLog I J E K X Z+frequencyLoss Z Csec xi := by
  apply retained_first_dyad_enclosure Tsec Z Csec (nominalLog I J E K X Z) xi hZ hC _ n hn
  rw [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
    (firstNominalScale_pos I J E hE K X hK hX)]
  exact hsec

open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationOriginalErrors CenteredMomentAmplificationGlobal

end SevenEighths.CenteredMomentAmplifiedRetainedRadius

end

end OAI
