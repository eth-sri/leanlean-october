module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.OriginalReflectionEnergy
public import OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy
public import OAI.NumberTheory.DirichletL.Moments.Counting
public import OAI.NumberTheory.DirichletL.Hecke.PrimeRay
public import OAI.NumberTheory.DirichletL.Moments.ComparisonReflection

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentOriginalReflectionErrorMass
open HeckeFamily HeckeDyadic HeckePrimeAnnular HeckePrimeRay
open CenteredMomentCounting CenteredMomentAbsoluteEnergy CenteredMomentComparisonReflection
open QuadraticInitialBound ConcreteTraceCRT


section
variable (χ : Character) (W : ℝ→ℂ) (b D freq B c : ℝ) (hD : 0<D) (hB : 0≤B) (hW : ∀x,‖W x‖≤B) (hs : Function.support W⊆Set.Iic b) (I : Ideal HeckeFamily.O)

include hD in
lemma annularWeight_zero_norm      
      (hI : I≠0) :
    ‖annularWeight W D 0 freq I‖=‖W ((I.absNorm:ℝ)/D)‖ := by
  have hn : 0<(I.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hn hD)]
  simp_all

include hD hB hW in
lemma actual_coefficient_norm      
            :
    ‖idealCoeff χ I*annularWeight W D 0 freq I‖≤B := by
  by_cases hI:I=0
  · subst I
    simpa only [idealCoeff_zero,zero_mul,norm_zero] using hB
  rw [norm_mul,annularWeight_zero_norm W D freq hD I hI]
  exact (mul_le_mul (idealCoeff_norm_le_one χ I) (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)

include hD hs in
lemma actual_coefficient_support      
         
    (hne : idealCoeff χ I*annularWeight W D 0 freq I≠0) :
    (I.absNorm:ℝ)≤max 1 b*D := by
  have hw : W ((I.absNorm:ℝ)/D)≠0:=by
    simp_all [annularWeight]
  exact ((div_le_iff₀ hD).mp (hs hw)).trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le)

lemma polynomial_all_ideals       :
    polynomial χ false W D 0 freq=
      (D:ℂ)^(-(1/2:ℂ))*∑'I:Ideal HeckeFamily.O,idealCoeff χ I*annularWeight W D 0 freq I := by
  unfold polynomial
  congr 1
  have he:(∑'I:NonzeroIdeal,idealCoeff χ I.val*annularWeight W D 0 freq I.val)=
      ∑'I:Ideal HeckeFamily.O,idealCoeff χ I*annularWeight W D 0 freq I:=by
    apply tsum_subtype_eq_of_support_subset (s:={I:Ideal HeckeFamily.O|I≠0})
      (f:=fun I:Ideal HeckeFamily.O=>idealCoeff χ I*annularWeight W D 0 freq I)
    intro I hI hz
    subst I
    exact hI (by simp only [idealCoeff_zero,zero_mul])
  simpa only [summand,coefficient,Bool.false_eq_true,ite_false,HeckeDyadic.norm,
    annularWeight,mul_assoc] using he

include hD in
lemma normalized_linear_bound      v 
    (hv : ‖v‖≤c*D) : ‖(D:ℂ)^(-(1/2:ℂ))*v‖≤c*Real.sqrt D := by
  rw [inverse_half_power D hD.le,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg D)]
  
  have hd:D/Real.sqrt D=Real.sqrt D:=by
    simp_all
  calc
    _ ≤ (Real.sqrt D)⁻¹*(c*D):=mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr (Real.sqrt_nonneg D))
    _ = c*(D/Real.sqrt D):=by ring
    _ = _:=by rw [hd]

theorem plain_polynomial_bound      b B D freq 
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) :
    ‖polynomial χ false W D 0 freq‖≤(128*max 1 b*B)*Real.sqrt D := by
  rw [polynomial_all_ideals]
  apply normalized_linear_bound D _ hD
  have hh:=norm_tsum_ideal_ball (fun I:Ideal HeckeFamily.O=>idealCoeff χ I*annularWeight W D 0 freq I)
    (max 1 b*D) B (by positivity) hB (by
      simp_all [idealCoeff, Ideal])
    (actual_coefficient_norm χ W D freq B hD hB hW)
    (actual_coefficient_support χ W b D freq hD hs)
  convert hh using 1; ring

end

def errorConstant {α } (F : Finset α) (bshort Bshort : ℝ) (b B : α→ℝ)  :=
  (1+(128*max 1 bshort*Bshort)^2)*∏j∈F,max 1 ((128*max 1 (b j)*B j)^2)

lemma errorConstant_pos {α : Type*} (F : Finset α)  bshort Bshort  (b B : α→ℝ) :
    0<errorConstant F bshort Bshort b B := by
  apply mul_pos
  · positivity
  positivity

lemma compact_norm_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : Continuous W) :
    ∃B:ℝ,0<B ∧ ∀x,‖W x‖≤B := by
  obtain ⟨B,hB,hbound⟩:=fixed_profile_norm_bound W hW a b 0 0 ha
  refine ⟨B,hB,?_⟩
  intro x
  by_cases hx:W x=0
  · simpa only [hx,norm_zero] using hB.le
  · simpa using hbound 0 (by simp) x (hs hx)

end SevenEighths.CenteredMomentOriginalReflectionErrorMass

end

end OAI
