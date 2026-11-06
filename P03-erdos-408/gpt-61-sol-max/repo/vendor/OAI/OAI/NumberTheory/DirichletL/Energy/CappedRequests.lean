module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction
public import OAI.NumberTheory.DirichletL.Energy.SourceCapSchedule

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentEnergyCappedRequests
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthInduction CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergySourceCapSchedule

def requestLength (M B L:ℝ):=max L (2*M+B+2)+1

section
variable (M B L ε parent rho d e : ℝ) (hM : 0≤M) (hB _hB : 0≤B) (hp : parent≤M) (hL : 0≤L) (he : e≤1) (hε : 0<ε) (k : ℕ) (hk : k<count M ε)

include hM hB in
lemma request_bounds    (_hL:0≤L):
    0≤requestLength M B L ∧ L≤requestLength M B L ∧ M≤requestLength M B L:=by
  grind [hh, requestLength]

include hM _hB hp in
lemma actual_contours    
     (hr:rho≤M)(hd:d≤1):
    max (max L (parent+B+2*d)+1) (parent+B+rho/100)≤requestLength M B L:=by
  grind [max, hh, requestLength]

include hM hB hL he in
lemma doubled_request      :
    2*requestLength M B L+e≤step M B L:=by
  grind [hh, max, requestLength, step]

include hM hB hp he hk in
lemma previous_admits    
        :
    2*max (requestLength M B (lengthAt M B L ε (k+1))) parent+e≤lengthAt M B L ε k:=by
  have hL:=range_nonneg M B L hM hB (remaining M ε (k+1))
  change 0≤lengthAt M B L ε (k+1) at hL
  have hreq:=request_bounds M B (lengthAt M B L ε (k+1)) hM hB hL
  rw [max_eq_left (hp.trans hreq.2.2),child_length M B L ε k hk]
  exact doubled_request M B _ e hM hB hL he

include hM hB hk in
lemma request_le_final      :
    requestLength M B (lengthAt M B L ε (k+1))≤range M B L (count M ε):=by
  have hh:=previous_admits M B L ε M 0 hM hB le_rfl (by norm_num) k hk
  have hl:=range_nonneg M B L hM hB (remaining M ε (k+1))
  
  have hprev:lengthAt M B L ε k≤range M B L (count M ε):=
    range_mono M B L hM hB (Nat.sub_le _ _)
  grind

include hε in
lemma parent_drop    :
    bandWidth M B ε (k+1)-amplification ε/2≤bandWidth M B ε k:=
  actual_child_band M B ε _ _ hε k le_rfl le_rfl

lemma band_positive  (hM:0<M)(hB:0≤B)(hε:0<ε) k :
    0<bandWidth M B ε k:=by
  have hh:=bounds M B 0 ε hM.le hB (by norm_num) hε
  have hr:=hh.2.2.2.1
  have hs:=hh.1
  unfold bandWidth width
  exact lt_min hM (by positivity)

end

end SevenEighths.CenteredMomentEnergyCappedRequests

end

end OAI
