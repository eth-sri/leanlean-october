module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.Moments.OneReflectionScaleEnergy

public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalStability
public import OAI.NumberTheory.DirichletL.Moments.ScaleSupremum

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentEnergyProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalSource
open CenteredMomentScaleSupremum

structure Test (a b:ℝ) where
  profile : 𝓢(ℝ,ℂ)
  support : Function.support (profile:ℝ→ℂ)⊆Set.Icc a b

def lower (a b:ℝ):ℕ→ℝ
  | 0=>a
  | n+1=>lower a b n/max 1 b

section
variable (a b:ℝ)

lemma lower_pos  (ha:0<a) n :0<lower a b n:=Nat.recAux ha (fun n ih => div_pos ih (lt_of_lt_of_le zero_lt_one (le_max_left 1 b))) n

def derivativeChoice (W:𝓢(ℝ,ℂ))(j:Fin 2):=
  if j=0 then W else DetectorDictionaryInverseUniform.scaleCLM W

lemma derivativeChoice_apply  W  j :
    (derivativeChoice W j:ℝ→ℂ)=scaleTest W j:=by
  unfold derivativeChoice scaleTest
  split_ifs
  · rfl
  · exact funext (DetectorDictionaryInverseUniform.scaleCLM_apply W)

lemma derivativeChoice_support  (W:𝓢(ℝ,ℂ))
    (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b) j :
    Function.support (derivativeChoice W j:ℝ→ℂ)⊆Set.Icc a b:=by
  rw [derivativeChoice_apply]
  exact scaleTest_support W a b hs j

lemma lower_antitone  (ha:0<a):Antitone (lower a b):=by
  apply antitone_nat_of_succ_le
  intro n
  exact div_le_self (lower_pos a b ha n).le (le_max_left _ _)

end

open CenteredMomentSectorLocalization in
alias annulus_support := _root_.OAI.SevenEighths.CenteredMomentOneReflectionScaleEnergy.annulus_complex_support

def annulusTemplate:Test (1/4) 1 where
  profile:=(HasCompactSupport.of_support_subset_isCompact isCompact_Icc annulus_support).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp CenteredMomentSectorLocalization.annulus_smooth)
  support:=annulus_support

lemma annulusTemplate_apply  x :annulusTemplate.profile x=(CenteredMomentSectorLocalization.annulus x:ℂ):=rfl

def annulusSeed (a b:ℝ)(ha:a≤1/4)(hb:1≤b):Test a b where
  profile:=annulusTemplate.profile
  support:=fun _x hx=>⟨ha.trans (annulusTemplate.support hx).1,
    (annulusTemplate.support hx).2.trans hb⟩

end SevenEighths.CenteredMomentEnergyProfiles

end

end OAI
