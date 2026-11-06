module
public import OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadiusSaving
open HeckeFamily CanonicalQuadraticSieve CompletedGauss CenteredMomentDescentLedger CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization CenteredMomentCompleteCommon CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical ConcreteTraceCRT ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

theorem common_saving_identity (c d x w q wo B sigma branch delta reserve ell : ℝ) :
    firstSaving c (d+x) w q wo B
      (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell =
      c/6+5*d/6+w/3+q/6+wo+B-5*max (d-c-2*w+wo) 0/6-
        5*branch*sigma/6-5*(delta+reserve)/6+ell := by
  unfold firstSaving
  ring

theorem common_saving_lower (c d x w q wo B sigma branch delta reserve ell : ℝ)
    (hc : 0≤c) (hw : 0≤w) (hq : 0≤q) (hwo : 0≤wo) (hB : 0≤B)
    (hallow : 3*c-5*d≤6*B+q) :
    2*(c+w)/3-max (w/3-wo) 0-5*branch*sigma/6-5*(delta+reserve)/6+ell≤
      firstSaving c (d+x) w q wo B
        (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell := by
  rw [common_saving_identity]
  have hm0 := le_max_right (w/3-wo) (0:ℝ)
  have hm1 := le_max_left (w/3-wo) (0:ℝ)
  by_cases h : 0≤d-c-2*w+wo
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

theorem main_saving_lower (c d x q B sigma delta reserve : ℝ)
    (hc : 0≤c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q) :
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+x) 0 q 0 B
        (x+max (d-c) 0+2*sigma+delta+reserve) (sigma/3) := by
  have hh := common_saving_lower c d x 0 q 0 B sigma 2 delta reserve (sigma/3)
    hc (by norm_num) hq (by norm_num) hB hallow
  norm_num only [zero_div,sub_zero,add_zero,mul_zero,max_self] at hh
  linarith

theorem error_penalty_le (l sigma : ℝ) (hl : 0≤l) (hu : l≤sigma/3)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    max (((k:ℝ)*l)/3-(if k=6 then 0 else l)) 0≤2*sigma/3 := by
  rcases hk with rfl|rfl|rfl <;> norm_num only [Nat.cast_ofNat,ite_false,ite_true,
    one_mul,sub_zero] <;> apply max_le <;> linarith

theorem error_saving_lower (c d x q B sigma delta reserve l : ℝ)
    (hc : 0≤c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q)
    (hl : 0≤l) (hu : l≤sigma/3) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    2*(c+(k:ℝ)*l)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+x) ((k:ℝ)*l) q (if k=6 then 0 else l) B
        (x+max (d-c-2*((k:ℝ)*l)+(if k=6 then 0 else l)) 0+
          sigma+delta+reserve) 0 := by
  have hw : 0≤(k:ℝ)*l := mul_nonneg (Nat.cast_nonneg k) hl
  have hwo : 0≤(if k=6 then (0:ℝ) else l) := by split_ifs <;> linarith
  have hh := common_saving_lower c d x ((k:ℝ)*l) q (if k=6 then 0 else l)
    B sigma 1 delta reserve 0 hc hw hq hwo hB hallow
  simp only [one_mul,add_zero] at hh
  linarith [error_penalty_le l sigma hl hu k hk]

theorem main_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1<Z) :
    Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j=
      (K0-j)+max (d-c) 0+2*sigma+delta+reserve := by
  rw [mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

theorem error_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1<Z)
    (p : O) (k : ℕ) :
    Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j=
      (K0-j)+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+
        sigma+delta+reserve := by
  rw [errorCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

open CenteredMomentFirstScale

end SevenEighths.CenteredMomentCommonRadiusSaving

end

end OAI
