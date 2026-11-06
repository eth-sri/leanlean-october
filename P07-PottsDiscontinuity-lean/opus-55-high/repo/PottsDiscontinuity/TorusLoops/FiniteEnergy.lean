module

public import PottsDiscontinuity.Torus.RibbonClusterSurgery
public import PottsDiscontinuity.TorusLoops.Measure

/-!
# One-edge finite-energy bound for the indexed torus law

Opening one closed indexed edge changes the primal cluster count by either zero
or one. This gives the uniform upper bound on the open/closed weight ratio used
to force a prescribed set of seam edges closed.
-/

@[expose] public section

open scoped BigOperators

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity
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
      Finset.univ.filter (fun w : Fin N × Fin M => toggleEdge A v w = true) =
        insert v (Finset.univ.filter (fun w => A w = true)) := by
    ext w
    by_cases hw : w = v
    · simp_all
    · simp
      rw [toggleEdge_away A hw]
      simp_all
  have hv : v ∉ Finset.univ.filter (fun w : Fin N × Fin M => A w = true) := by
    simp_all
  rw [hfilter, Finset.card_insert_of_notMem hv]

theorem closedCount_toggle_of_closed  :
    closedCount A = closedCount (toggleEdge A v) + 1 := by
  unfold closedCount
  have hfilter :
      Finset.univ.filter (fun w : Fin N × Fin M => toggleEdge A v w = false) =
        (Finset.univ.filter (fun w => A w = false)).erase v := by
    ext w
    by_cases hw : w = v
    · simp_all
    · simp
      rw [toggleEdge_away A hw]
      simp_all
  have hv : v ∈ Finset.univ.filter (fun w : Fin N × Fin M => A w = false) := by
    simp_all
  rw [hfilter]
  exact (Finset.card_erase_add_one hv).symm
end

/-- Opening a specified closed edge never increases the torus weight by more
than the Bernoulli odds `p_c/(1-p_c)`. -/
theorem torusRCWeight_toggle_le (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) (v : Fin N × Fin M)
    (hA : A v = false) :
    torusRCWeight hN hM q (toggleEdge A v) ≤
      ((rcCriticalParameter q).val / (1 - (rcCriticalParameter q).val)) *
        torusRCWeight hN hM q A := by
  have hp := criticalParameter_pos q
  have hclosed :=
    sub_pos.mpr (criticalParameter_lt_one q)
  have hk : clusterCount hN hM true (toggleEdge A v) ≤
      clusterCount hN hM true A := by
    by_cases hr : (diamondOpenGraph hN hM true A).Reachable
        (faceEndpoint hN hM true v false) (faceEndpoint hN hM true v true)
    · rw [clusterCount_toggle_of_reachable hN hM A v hA hr]
    · have ht := clusterCount_toggle_of_not_reachable hN hM A v hA hr
      omega
  have hopen := openCount_toggle_of_closed A v hA
  have hclose := closedCount_toggle_of_closed A v hA
  calc
    torusRCWeight hN hM q (toggleEdge A v) =
        (rcCriticalParameter q).val ^ (openCount A + 1) *
          (1 - (rcCriticalParameter q).val) ^ closedCount (toggleEdge A v) *
            q.val ^ clusterCount hN hM true (toggleEdge A v) := by
      simp_all [torusRCWeight]
    _ ≤ (rcCriticalParameter q).val ^ (openCount A + 1) *
          (1 - (rcCriticalParameter q).val) ^ closedCount (toggleEdge A v) *
            q.val ^ clusterCount hN hM true A :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ q.property hk)
        (mul_nonneg (pow_nonneg hp.le _) (pow_nonneg hclosed.le _))
    _ = ((rcCriticalParameter q).val / (1 - (rcCriticalParameter q).val)) *
          torusRCWeight hN hM q A := by
      grind [torusRCWeight]

section
variable (v : Fin N × Fin M)
abbrev ClosedAt  :=
  {A : RCConfig N M // A v = false}

def edgeStateEquiv  :
    RCConfig N M ≃ ClosedAt v × Bool where
  toFun A := (⟨Function.update A v false, by simp⟩, A v)
  invFun x := Function.update x.1.1 v x.2
  left_inv A := by
    simp
  right_inv x := by
    aesop

@[simp] theorem edgeStateEquiv_symm_apply_false (A : ClosedAt v) : (edgeStateEquiv v).symm (A, false) = A.1 := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [edgeStateEquiv, A.2]
  · simp [edgeStateEquiv, Function.update_of_ne hw]

@[simp] theorem edgeStateEquiv_symm_apply_true (A : ClosedAt v) :
    (edgeStateEquiv v).symm (A, true) = toggleEdge A.1 v := by
  funext w
  by_cases hw : w = v
  · simp [edgeStateEquiv, toggleEdge, A.2]
  · simp [edgeStateEquiv, toggleEdge, Function.update_of_ne hw]
end

theorem edgeState_sum (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (v : Fin N × Fin M) (f : RCConfig N M → ℝ) :
    (∑ A : RCConfig N M, torusRCMass hN hM q A * f A) =
      ∑ A : ClosedAt v,
        (torusRCMass hN hM q A.1 * f A.1 +
          torusRCMass hN hM q (toggleEdge A.1 v) * f (toggleEdge A.1 v)) := by
  rw [← (edgeStateEquiv v).symm.sum_comp, Fintype.sum_prod_type]
  simp
  apply Finset.sum_congr rfl
  intro A hA
  ring

noncomputable def eventIndicator (E : Set (RCConfig N M)) : RCConfig N M → ℝ :=
  E.indicator (fun _ => 1)

section
variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
theorem phi_T_probability_mul_indicator (E : Set (RCConfig N M)) :
    phi_T_probability hN hM q E =
      ∑ A : RCConfig N M, torusRCMass hN hM q A * eventIndicator E A := by
  rw [phi_T_probability_eq_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hE : A ∈ E <;> simp [eventIndicator, hE]

theorem mass_toggle_le_odds (v : Fin N × Fin M)
    (A : ClosedAt v) :
    torusRCMass hN hM q (toggleEdge A.1 v) ≤
      ((rcCriticalParameter q).val / (1 - (rcCriticalParameter q).val)) *
        torusRCMass hN hM q A.1 := by
  calc
    torusRCWeight hN hM q (toggleEdge A.1 v) /
        torusRCPartition hN hM q ≤
      (((rcCriticalParameter q).val / (1 - (rcCriticalParameter q).val)) *
        torusRCWeight hN hM q A.1) / torusRCPartition hN hM q :=
      (div_le_div_iff_of_pos_right (torusRCPartition_pos hN hM q)).2
        (torusRCWeight_toggle_le hN hM q A.1 v A.2)
    _ = ((rcCriticalParameter q).val / (1 - (rcCriticalParameter q).val)) *
        (torusRCWeight hN hM q A.1 / torusRCPartition hN hM q) := by ring

/-- If an event is invariant under toggling an indexed edge, its closed-edge
probability is at least the Bernoulli closed probability times its full mass. -/
theorem torusRCProbability_closed_lower (v : Fin N × Fin M)
    (E : Set (RCConfig N M))
    (hstable : ∀ A, A ∈ E ↔ toggleEdge A v ∈ E) :
    (1 - (rcCriticalParameter q).val) * phi_T_probability hN hM q E ≤
      phi_T_probability hN hM q (E ∩ {A | A v = false}) := by
  classical
  let p := (rcCriticalParameter q).val
  have hp1 := sub_pos.mpr (criticalParameter_lt_one q)
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
    · have htoggle : toggleEdge A.1 v ∈ E := by grind
      simp [eventIndicator, hE, htoggle]
    · have htoggle : toggleEdge A.1 v ∉ E := by
        grind
      simp [eventIndicator, hE, htoggle]
  have hclosed : phi_T_probability hN hM q (E ∩ {A | A v = false}) =
      ∑ A : ClosedAt v, if A.1 ∈ E then torusRCMass hN hM q A.1 else 0 := by
    rw [phi_T_probability_mul_indicator hN hM q (E ∩ {A | A v = false}),
      edgeState_sum hN hM q v]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hE : A.1 ∈ E <;> simp [eventIndicator, hE, A.2, toggleEdge]
  have hterm (A : ClosedAt v) :
      (1 - p) * (if A.1 ∈ E then
        torusRCMass hN hM q A.1 + torusRCMass hN hM q (toggleEdge A.1 v)
        else 0) ≤ if A.1 ∈ E then torusRCMass hN hM q A.1 else 0 := by
    by_cases hE : A.1 ∈ E
    · simp only [ite_eq_left hE]
      have hratio := mass_toggle_le_odds hN hM q v A
      calc
        (1 - p) * (torusRCMass hN hM q A.1 +
            torusRCMass hN hM q (toggleEdge A.1 v)) ≤
          (1 - p) * (torusRCMass hN hM q A.1 +
            (p / (1 - p)) * torusRCMass hN hM q A.1) :=
          mul_le_mul_of_nonneg_left (add_le_add_right hratio (torusRCMass hN hM q A.1)) hp1.le
        _ = torusRCMass hN hM q A.1 := by
          grind
    · simp [hE]
  rw [htotal, hclosed]
  calc
    (1 - p) *
        (∑ A : ClosedAt v,
          if A.1 ∈ E then
            torusRCMass hN hM q A.1 + torusRCMass hN hM q (toggleEdge A.1 v)
          else 0) =
      ∑ A : ClosedAt v,
        (1 - p) * (if A.1 ∈ E then
          torusRCMass hN hM q A.1 + torusRCMass hN hM q (toggleEdge A.1 v)
          else 0) := by rw [Finset.mul_sum]
    _ ≤ ∑ A : ClosedAt v,
        (if A.1 ∈ E then torusRCMass hN hM q A.1 else 0) :=
      Finset.sum_le_sum (fun A _ => hterm A)
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
  suffices hInd : ∀ T : Finset (Fin N × Fin M),
      (∀ v ∈ T, ∀ A, A ∈ E ↔ toggleEdge A v ∈ E) →
      (1 - (rcCriticalParameter q).val) ^ T.card * phi_T_probability hN hM q E ≤
        phi_T_probability hN hM q (E ∩ closedOn T) by
    grind
  intro T hT
  induction T using Finset.induction_on with
  | empty =>
      simp [closedOn]
  | @insert a T ha ih =>
      have hstablePrevious : ∀ v ∈ T, ∀ A, A ∈ E ↔ toggleEdge A v ∈ E := by
        grind
      have hstepStable : ∀ A, A ∈ E ∩ closedOn T ↔
          toggleEdge A a ∈ E ∩ closedOn T := by
        intro A
        have hclosed : A ∈ closedOn T ↔ toggleEdge A a ∈ closedOn T := by
          constructor
          · intro hA v hv
            have hva : v ≠ a := by
              grind
            rw [toggleEdge_away A hva]
            tauto
          · intro hA v hv
            have hva : v ≠ a := by
              grind
            have hAv := hA v hv
            rw [toggleEdge_away A hva] at hAv
            omega
        grind
      have hstep := torusRCProbability_closed_lower hN hM q a
        (E ∩ closedOn T) hstepStable
      have hset : (E ∩ closedOn T) ∩ {A | A a = false} =
          E ∩ closedOn (insert a T) := by
        ext A
        simp [closedOn, and_left_comm, and_comm]
      have hstep' : (1 - (rcCriticalParameter q).val) *
          phi_T_probability hN hM q (E ∩ closedOn T) ≤
          phi_T_probability hN hM q (E ∩ closedOn (insert a T)) := by
        grind
      rw [Finset.card_insert_of_notMem ha, pow_succ]
      calc
        ((1 - (rcCriticalParameter q).val) ^ T.card *
            (1 - (rcCriticalParameter q).val)) *
            phi_T_probability hN hM q E =
          (1 - (rcCriticalParameter q).val) *
            ((1 - (rcCriticalParameter q).val) ^ T.card *
              phi_T_probability hN hM q E) := by ring
        _ ≤ (1 - (rcCriticalParameter q).val) *
            phi_T_probability hN hM q (E ∩ closedOn T) :=
          mul_le_mul_of_nonneg_left (ih hstablePrevious) (sub_nonneg.mpr
            (criticalParameter_lt_one q).le)
        _ ≤ phi_T_probability hN hM q
            (E ∩ closedOn (insert a T)) := hstep'

end PottsDiscontinuity.TorusLoops
