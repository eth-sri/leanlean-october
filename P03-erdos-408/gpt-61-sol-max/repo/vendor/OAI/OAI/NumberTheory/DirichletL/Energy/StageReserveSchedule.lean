module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Energy.StageReserve
public import OAI.NumberTheory.DirichletL.Energy.WidthSchedule

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyWidthSchedule CenteredMomentSuccessorPaidParameters

def stageLoss (M B ε:ℝ)(k:ℕ):=ε/1000+loss M B ε k

section
variable (M B κ ε:ℝ) (hM:0≤M) (hB:0≤B) (hκ:0≤κ) (hε:0<ε) (k:ℕ)
include M B κ ε hM hB hκ hε k

lemma stageLoss_pos       :
    0<stageLoss M B ε k:=by
  have hr:0<reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  unfold stageLoss loss
  positivity

lemma stageLoss_final      
     (hk:k≤count M ε):stageLoss M B ε k≤ε/500:=by
  have hh:=loss_le_final M B κ ε hM hB hκ hε k hk
  unfold stageLoss
  linarith

lemma successor_with_references      
      er d e d1 d2 theta other highReflection zeroReflection 
    (her:er≤reserve M B ε)(hd:d≤reserve M B ε)(he:e≤reserve M B ε)
    (hd1:d1≤reserve M B ε)(hd2:d2≤reserve M B ε)(ht:theta≤reserve M B ε)
    (ho:other≤48*reserve M B ε)
    (hhigh:highReflection≤reserve M B ε)(hzero:zeroReflection≤reserve M B ε):
    stageLoss M B ε k+edge 0 er d e d1 d2 theta κ (mesh M B κ ε)+
      other+highReflection+zeroReflection≤stageLoss M B ε (k+1):=by
  have hh:=next_paid_loss M B κ ε hM hB hκ hε k er d e d1 d2 theta
    (other+highReflection+zeroReflection) her hd he hd1 hd2 ht (by linarith)
  unfold stageLoss
  linarith

lemma one_time_with_new_cost      
      sourceLoss extra (hsource:sourceLoss≤ε/1000)
    (hextra:extra≤50*reserve M B ε):
    sourceLoss+extra≤stageLoss M B ε (k+1):=by
  have hr:0<reserve M B ε:=(bounds M B κ ε hM hB hκ hε).2.2.2.1
  
  simp only [stageLoss,loss,Nat.cast_add,Nat.cast_one]
  nlinarith

lemma actual_one_time_with_new_cost      
      df es d theta other A extra 
    (hdf:df≤reserve M B ε)(hes:es≤reserve M B ε)(hd:d≤reserve M B ε)
    (ht:theta≤reserve M B ε)(ho:other≤reserve M B ε)(he0:0≤es)(hA:A≤M)
    (hextra:extra≤50*reserve M B ε):
    CenteredMomentSuccessorPaidParameters.exceptional (amplification ε) df es d B theta+extra≤
      stageLoss M B ε (k+1) ∧
    CenteredMomentSuccessorPaidParameters.diagonal (amplification ε) d other es A+extra≤
      stageLoss M B ε (k+1):=by
  have hh:=one_time_losses M B κ ε hM hB hκ hε df es d theta other A hdf hes hd ht ho he0 hA
  grind [one_time_with_new_cost, hh]

end

end SevenEighths.CenteredMomentEnergyStageReserveSchedule

end

end OAI
