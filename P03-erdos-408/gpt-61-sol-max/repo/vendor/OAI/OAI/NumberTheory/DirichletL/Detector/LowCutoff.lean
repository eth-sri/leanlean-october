module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.LowRay
public import OAI.NumberTheory.DirichletL.Detector.GaussianPartition

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical


def lowOuterCutoff (a b x : ℝ)  :=
  (Real.smoothTransition (2*x/a-1):ℂ)*(Real.smoothTransition (2-x/b):ℂ)

section
variable (a b : ℝ) (ha : 0<a) (hb : 0<b) (x : ℝ) (C : CalibrationData) (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1) (B q X Y m : ℝ) (hq : 0<q) (hY : 0<Y)

include ha in
lemma lowOuterCutoff_small       (hx : x≤a/2) :
    lowOuterCutoff a b x=0 := by
  have h : 2*x/a-1≤0 := by
    have hh : 2*x/a≤1 := (div_le_iff₀ ha).mpr (by linarith)
    linarith
  simp_all [lowOuterCutoff]

include hb in
lemma lowOuterCutoff_large       (hx : 2*b≤x) :
    lowOuterCutoff a b x=0 := by
  have h : 2-x/b≤0 := by
    have hh : 2≤x/b := (le_div_iff₀ hb).mpr hx
    linarith
  simp_all [lowOuterCutoff]

include ha hb in
lemma lowOuterCutoff_one         (hlo : a≤x) (hhi : x≤b) :
    lowOuterCutoff a b x=1 := by
  have hl : 1≤2*x/a-1 := by
    have hh : 2≤2*x/a := (le_div_iff₀ ha).mpr (by linarith)
    linarith
  have hr : 1≤2-x/b := by
    have hh : x/b≤1 := (div_le_iff₀ hb).mpr (by simpa using hhi)
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.one_of_one_le hl,
    Real.smoothTransition.one_of_one_le hr,Complex.ofReal_one,mul_one]

lemma lowOuterCutoff_smooth   : ContDiff ℝ ∞ (lowOuterCutoff a b) := by
  unfold lowOuterCutoff
  exact (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))).mul
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop)))

include ha hb in
lemma lowOuterCutoff_support       :
    Function.support (lowOuterCutoff a b)⊆Set.Icc (a/2) (2*b) := by
  intro x hx
  constructor
  · by_contra hh
    exact hx (lowOuterCutoff_small a b ha x (le_of_lt (lt_of_not_ge hh)))
  · by_contra hh
    exact hx (lowOuterCutoff_large a b hb x (le_of_lt (lt_of_not_ge hh)))

include ha hb in
lemma lowOuterCutoff_compact       :
    HasCompactSupport (lowOuterCutoff a b) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (lowOuterCutoff_support a b ha hb)

include hq hY in
lemma physical_ratio_factor       :
    m/(B*X*Y)=(q/Y)*(m/(B*q*X)) := by
  field_simp

include ha0 ha1 hW0 hW1 hq hY in
lemma physical_window_cutoff_one    
       
       
         
    (h0 : W0 (m/(B*q*X))≠0) (h1 : W1 (q/Y)≠0) :
    lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (m/(B*X*Y))=1 := by
  have h0b := hW0 h0
  have h1b := hW1 h1
  apply lowOuterCutoff_one _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  · rw [physical_ratio_factor B q X Y m hq hY]
    have hh := mul_le_mul h0b.1 h1b.1 ha1.le (le_trans ha0.le h0b.1)
    simpa only [mul_comm] using hh
  · rw [physical_ratio_factor B q X Y m hq hY]
    have hh := mul_le_mul h0b.2 h1b.2 (le_trans ha1.le h1b.1) (le_trans ha0.le (h0b.1.trans h0b.2))
    grind

include ha0 ha1 hW0 hW1 hY in
theorem physicalRowWeight_insert_cutoff    
         
       
         r  :
    physicalRowWeight C W0 W1 X Y r=
      lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (elementNorm r.2/(elementNorm C.generator*X*Y))*
        physicalRowWeight C W0 W1 X Y r := by
  by_cases hz : physicalRowWeight C W0 W1 X Y r=0
  · simp only [hz,mul_zero]
  have h0 : W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))≠0 :=
    fun h=>hz (physicalRowWeight_inner_zero C W0 W1 X Y r h)
  have h1 : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)≠0 :=
    fun h=>hz (physicalRowWeight_outer_zero C W0 W1 X Y r h)
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  rw [physical_window_cutoff_one W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (elementNorm C.generator) (Ideal.absNorm r.1.val) X Y (elementNorm r.2) hq hY h0 h1,one_mul]

end

end SevenEighths.ProbePhysical
end

end OAI
