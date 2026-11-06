module
public import Mathlib

public import PottsDiscontinuity.Torus.RibbonClusterSurgery
public import PottsDiscontinuity.TorusLoops.Measure

/-!
# One-edge finite-energy bound for the indexed torus law

Opening one closed indexed edge changes the primal cluster count by either zero
or one. This gives the uniform upper bound on the open/closed weight ratio used
to force a prescribed set of seam edges closed.
-/

@[expose] public section



namespace PottsDiscontinuity.TorusLoops


open PottsDiscontinuity.Torus
open PottsDiscontinuity.TorusRC

variable {N M : ℕ}

section

variable (A : RCConfig N M) (v : Fin N × Fin M) (hA : A v = false)
include hA

theorem openCount_toggle_of_closed  :
    openCount (toggleEdge A v) = openCount A + 1 := by
  
  unfold openCount
  have hfilter :
      Finset.univ.filter  fun w  => toggleEdge A v w = true  =
        insert v (Finset.univ.filter  fun w => A w = true ) := by
    ext w
    by_cases hw : w = v
    · subst w
      simp [hA]
    · simp only [Finset.mem_filter]
      rw [toggleEdge_away A hw]
      simp [hw]
  grind

theorem closedCount_toggle_of_closed  :
    closedCount A = closedCount (toggleEdge A v) + 1 := by
  
  unfold closedCount
  have hfilter :
      Finset.univ.filter  fun w  => toggleEdge A v w = false  =
        (Finset.univ.filter  fun w => A w = false ).erase v := by
    ext w
    by_cases hw : w = v
    · subst w
      simp [hA]
    · simp only [Finset.mem_filter]
      rw [toggleEdge_away A hw]
      simp [hw]
  grind

end

/-- Opening a specified closed edge never increases the torus weight by more
than the Bernoulli odds `p_c/(1-p_c)`. -/
theorem torusRCWeight_toggle_le (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) (v : Fin N × Fin M)
    (hA : A v = false) :
    torusRCWeight hN hM q (toggleEdge A v) ≤
       (rcCriticalParameter q).val / (1 - (rcCriticalParameter q).val)  *
        torusRCWeight hN hM q A := by
  
  have hclosed  :=
    sub_pos.mpr (criticalParameter_lt_one q)
  have hk : clusterCount hN hM true (toggleEdge A v) ≤
      clusterCount hN hM true A := by
    by_cases hr : (diamondOpenGraph hN hM true A).Reachable
        (faceEndpoint hN hM true v false) (faceEndpoint hN hM true v true)
    · rw [clusterCount_toggle_of_reachable hN hM A v hA hr]
    · have ht := clusterCount_toggle_of_not_reachable hN hM A v hA hr
      omega
  
  
  have hclose := closedCount_toggle_of_closed A v hA
  calc
    torusRCWeight hN hM q (toggleEdge A v) =
        (rcCriticalParameter q).val ^ (openCount A + 1) *
          (1 - (rcCriticalParameter q).val) ^ closedCount (toggleEdge A v) *
            q.val ^ clusterCount hN hM true (toggleEdge A v) := by
      simp [torusRCWeight,  openCount_toggle_of_closed A v hA ]
    _ ≤ (rcCriticalParameter q).val ^ (openCount A + 1) *
          (1 - (rcCriticalParameter q).val) ^ closedCount (toggleEdge A v) *
            q.val ^ clusterCount hN hM true A := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ q.property hk)
        (mul_nonneg (pow_nonneg (criticalParameter_pos q).le _) (pow_nonneg hclosed.le _))
    _ =  (rcCriticalParameter q).val / (1 - (rcCriticalParameter q).val)  *
          torusRCWeight hN hM q A := by
      grind [torusRCWeight]

abbrev ClosedAt (v : Fin N × Fin M) :=
  {A : RCConfig N M // A v = false}

def edgeStateEquiv (v : Fin N × Fin M) :
    RCConfig N M ≃ ClosedAt v × Bool where
  toFun A := (⟨Function.update A v false, by simp⟩, A v)
  invFun x := Function.update x.1.1 v x.2
  left_inv A := by
    simp_all
  right_inv x := by
    aesop

section

variable (v : Fin N × Fin M) (A : ClosedAt v)


@[simp] private theorem edgeStateEquiv_symm_apply_false  : (edgeStateEquiv v).symm (A, false) = A.1 := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [edgeStateEquiv, A.2]
  · simp [edgeStateEquiv, Function.update_of_ne hw]

@[simp] private theorem edgeStateEquiv_symm_apply_true  :
    (edgeStateEquiv v).symm (A, true) = toggleEdge A.1 v := by
  funext w
  by_cases hw : w = v
  · 
    simp [edgeStateEquiv, toggleEdge, A.2]
  · simp_all [edgeStateEquiv, toggleEdge]

end

private theorem edgeState_sum (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (v : Fin N × Fin M) (f : RCConfig N M → ℝ) :
     ∑ A : RCConfig N M, torusRCMass hN hM q A * f A  =
      ∑ A : ClosedAt v,
        (torusRCMass hN hM q A.1 * f A.1 +
          torusRCMass hN hM q (toggleEdge A.1 v) * f (toggleEdge A.1 v)) := by
  
  rw [← (edgeStateEquiv v).symm.sum_comp, Fintype.sum_prod_type]
  simp only [edgeStateEquiv_symm_apply_false, edgeStateEquiv_symm_apply_true,
    Fintype.sum_bool]
  grind

noncomputable def eventIndicator (E : Set (RCConfig N M)) : RCConfig N M → ℝ :=
  E.indicator  fun _ => 1 

section

variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
include hN hM q

private theorem phi_T_probability_mul_indicator  (E : Set (RCConfig N M)) :
    phi_T_probability hN hM q E =
      ∑ A : RCConfig N M, torusRCMass hN hM q A * eventIndicator E A := by
  erw [phi_T_probability_eq_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hE : A ∈ E <;> simp [eventIndicator, hE]

private theorem mass_toggle_le_odds  (v : Fin N × Fin M)
    (A : ClosedAt v) :
    torusRCMass hN hM q (toggleEdge A.1 v) ≤
       (rcCriticalParameter q).val / (1 - (rcCriticalParameter q).val)  *
        torusRCMass hN hM q A.1 := by
  
  calc
    torusRCWeight hN hM q (toggleEdge A.1 v) /
        torusRCPartition hN hM q ≤
        (rcCriticalParameter q).val / (1 - (rcCriticalParameter q).val)  *
        torusRCWeight hN hM q A.1  / torusRCPartition hN hM q :=
      (div_le_div_iff_of_pos_right (torusRCPartition_pos hN hM q)).2
        (torusRCWeight_toggle_le hN hM q A.1 v A.2)
    _ =  (rcCriticalParameter q).val / (1 - (rcCriticalParameter q).val)  *
        (torusRCWeight hN hM q A.1 / torusRCPartition hN hM q) := by ring

/-- If an event is invariant under toggling an indexed edge, its closed-edge
probability is at least the Bernoulli closed probability times its full mass. -/
theorem torusRCProbability_closed_lower  (v : Fin N × Fin M)
    (E : Set (RCConfig N M))
    (hstable : ∀ A, A ∈ E ↔ toggleEdge A v ∈ E) :
    (1 - (rcCriticalParameter q).val) * phi_T_probability hN hM q E ≤
      phi_T_probability hN hM q (E ∩ {A | A v = false}) := by
  classical
  let p := (rcCriticalParameter q).val
  
  have hp1 : 0 < 1 - p := sub_pos.mpr (criticalParameter_lt_one q)
  have htotal : phi_T_probability hN hM q E =
      ∑ A : ClosedAt v,
        if A.1 ∈ E then
          torusRCMass hN hM q A.1 + torusRCMass hN hM q (toggleEdge A.1 v)
        else 0 := by
    rw [phi_T_probability_mul_indicator hN hM q E,
      edgeState_sum hN hM q v]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hE : A.1 ∈ E
    · 
      simp [eventIndicator, hE,  (hstable A.1).mp hE ]
    · have htoggle : toggleEdge A.1 v ∉ E := by
        grind
      simp [eventIndicator, hE, htoggle]
  have hclosed : phi_T_probability hN hM q (E ∩ {A | A v = false}) =
      ∑ A : ClosedAt v, if A.1 ∈ E then torusRCMass hN hM q A.1 else 0 := by
    rw [phi_T_probability_mul_indicator hN hM q (E ∩ {A | A v = false}),
      edgeState_sum hN hM q v]
    apply Finset.sum_congr rfl
    intro A hA
    
    by_cases hE : A.1 ∈ E <;> simp [eventIndicator, hE, A.2]
  have hterm (A : ClosedAt v) :
      (1 - p) * (if A.1 ∈ E then
        torusRCMass hN hM q A.1 + torusRCMass hN hM q (toggleEdge A.1 v)
        else 0) ≤ if A.1 ∈ E then torusRCMass hN hM q A.1 else 0 := by
    by_cases hE : A.1 ∈ E
    · simp only [ite_eq_left hE]
      
      have hsum := add_le_add_right (mass_toggle_le_odds hN hM q v A) (torusRCMass hN hM q A.1)
      calc
        (1 - p) * (torusRCMass hN hM q A.1 +
            torusRCMass hN hM q (toggleEdge A.1 v)) ≤
          (1 - p) * (torusRCMass hN hM q A.1 +
             p / (1 - p)  * torusRCMass hN hM q A.1) :=
          mul_le_mul_of_nonneg_left hsum hp1.le
        _ = torusRCMass hN hM q A.1 := by
          field_simp
          ring
    · simp [hE]
  rw [htotal, hclosed]
  calc
    (1 - p) *
        (∑ A : ClosedAt v,
          if A.1 ∈ E then
            torusRCMass hN hM q A.1 + torusRCMass hN hM q (toggleEdge A.1 v)
          else 0) =
      ∑ A : ClosedAt v,
        (1 - p) *  if A.1 ∈ E then
          torusRCMass hN hM q A.1 + torusRCMass hN hM q (toggleEdge A.1 v)
          else 0  := by rw [Finset.mul_sum]
    _ ≤ ∑ A : ClosedAt v,
         if A.1 ∈ E then torusRCMass hN hM q A.1 else 0  :=
      Finset.sum_le_sum  fun A _ => hterm A 

end

 def closedOn (S : Finset (Fin N × Fin M)) : Set (RCConfig N M) :=
  {A | ∀ v ∈ S, A v = false}

/-- Closing a finite prescribed edge set costs at most one factor `1-p_c`
per edge, provided the event being measured is invariant under those edge
toggles. -/
theorem torusRCProbability_close_finite_set (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (S : Finset (Fin N × Fin M))
    (E : Set (RCConfig N M))
    (hstable : ∀ v ∈ S, ∀ A, A ∈ E ↔ toggleEdge A v ∈ E) :
    (1 - (rcCriticalParameter q).val) ^ S.card * phi_T_probability hN hM q E ≤
      phi_T_probability hN hM q (E ∩ closedOn S) := by
  
  suffices hInd : ∀ T ,
      (∀ v ∈ T, ∀ A, A ∈ E ↔ toggleEdge A v ∈ E) →
      (1 - (rcCriticalParameter q).val) ^ T.card * phi_T_probability hN hM q E ≤
        phi_T_probability hN hM q (E ∩ closedOn T) by
    exact hInd S hstable
  intro T hT
  induction T using Finset.induction_on with
  | empty =>
      simp [closedOn]
  | @insert a T ha ih =>
      
      
      have hstep := torusRCProbability_closed_lower hN hM q a
        (E ∩ closedOn T) (by
                            intro A
                            
                            have hclosed : A ∈ closedOn T ↔ toggleEdge A a ∈ closedOn T := by
                              constructor
                              · intro hA v hv
                                
                                rw [toggleEdge_away A (by
                                                         grind)]
                                exact hA v hv
                              · intro hA v hv
                                
                                have hAv := hA v hv
                                rw [toggleEdge_away A (by
                                                         grind)] at hAv
                                exact hAv
                            grind)
      
      have hset :  E ∩ closedOn T  ∩ {A | A a = false} =
          E ∩ closedOn (insert a T) := by
        ext A
        simp [closedOn, and_left_comm, and_comm]
      
      rw [Finset.card_insert_of_notMem ha, pow_succ]
      calc
         (1 - (rcCriticalParameter q).val) ^ T.card *
            (1 - (rcCriticalParameter q).val)  *
            phi_T_probability hN hM q E =
          (1 - (rcCriticalParameter q).val) *
            ((1 - (rcCriticalParameter q).val) ^ T.card *
              phi_T_probability hN hM q E) := by ring
        _ ≤ (1 - (rcCriticalParameter q).val) *
            phi_T_probability hN hM q (E ∩ closedOn T) :=
          mul_le_mul_of_nonneg_left (ih (by
                                                         grind)) (sub_nonneg.mpr
            (criticalParameter_lt_one q).le)
        _ ≤ phi_T_probability hN hM q
            (E ∩ closedOn (insert a T)) :=  by
                                              simpa only [hset] using hstep 

end PottsDiscontinuity.TorusLoops
