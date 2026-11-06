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

theorem openCount_toggle_of_closed (A : RCConfig N M) (v : Fin N × Fin M)
    (hA : A v = false) :
    openCount (toggleEdge A v) = openCount A + 1 := by
  classical
  unfold openCount
  rw [show Finset.univ.filter (fun w => toggleEdge A v w = true) =
      insert v (Finset.univ.filter fun w => A w = true) by
    ext w; by_cases hw : w = v <;> simp [toggleEdge, hw, hA],
    Finset.card_insert_of_notMem (by simp [hA])]

theorem closedCount_toggle_of_closed (A : RCConfig N M) (v : Fin N × Fin M)
    (hA : A v = false) :
    closedCount A = closedCount (toggleEdge A v) + 1 := by
  classical
  unfold closedCount
  rw [show Finset.univ.filter (fun w => toggleEdge A v w = false) =
      (Finset.univ.filter fun w => A w = false).erase v by
    ext w; by_cases hw : w = v <;> simp [toggleEdge, hw, hA]]
  exact (Finset.card_erase_add_one (by simp [hA])).symm

/-- Opening a specified closed edge never increases the torus weight by more
than the Bernoulli odds `p_c/(1-p_c)`. -/
theorem torusRCWeight_toggle_le (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) (v : Fin N × Fin M)
    (hA : A v = false) :
    torusRCWeight hN hM q (toggleEdge A v) ≤
      ((rcCriticalParameter q).val / (1 - (rcCriticalParameter q).val)) *
        torusRCWeight hN hM q A := by
  have hp : 0 < (rcCriticalParameter q).val := criticalParameter_pos q
  have hclosed : 0 < 1 - (rcCriticalParameter q).val := sub_pos.mpr (criticalParameter_lt_one q)
  have hk : clusterCount hN hM true (toggleEdge A v) ≤ clusterCount hN hM true A := by
    by_cases hr : (diamondOpenGraph hN hM true A).Reachable
        (faceEndpoint hN hM true v false) (faceEndpoint hN hM true v true)
    · rw [clusterCount_toggle_of_reachable hN hM A v hA hr]
    · have := clusterCount_toggle_of_not_reachable hN hM A v hA hr; omega
  have hmul := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ q.property hk)
    (mul_nonneg (pow_nonneg hp.le (openCount (toggleEdge A v)))
      (pow_nonneg hclosed.le (closedCount (toggleEdge A v))))
  change torusRCWeight hN hM q (toggleEdge A v) ≤ _ at hmul
  refine hmul.trans_eq ?_
  simp only [torusRCWeight, openCount_toggle_of_closed A v hA,
    closedCount_toggle_of_closed A v hA, pow_succ]
  field_simp

abbrev ClosedAt (v : Fin N × Fin M) :=
  {A : RCConfig N M // A v = false}

def edgeStateEquiv (v : Fin N × Fin M) :
    RCConfig N M ≃ ClosedAt v × Bool where
  toFun A := (⟨Function.update A v false, by simp⟩, A v)
  invFun x := Function.update x.1.1 v x.2
  left_inv A := by funext w; by_cases hw : w = v <;> simp [hw]
  right_inv := fun ⟨⟨A, hA⟩, b⟩ => by
    ext w
    · by_cases hw : w = v <;> simp [hw, hA]
    · simp

@[simp] private theorem edgeStateEquiv_symm_apply_false (v : Fin N × Fin M)
    (A : ClosedAt v) : (edgeStateEquiv v).symm (A, false) = A.1 := by
  funext w; by_cases hw : w = v <;> simp [edgeStateEquiv, hw, A.2]

@[simp] private theorem edgeStateEquiv_symm_apply_true (v : Fin N × Fin M)
    (A : ClosedAt v) :
    (edgeStateEquiv v).symm (A, true) = toggleEdge A.1 v := by
  funext w; by_cases hw : w = v <;> simp [edgeStateEquiv, toggleEdge, hw, A.2]

open scoped Classical in
private theorem phi_T_probability_split (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (v : Fin N × Fin M) (E : Set (RCConfig N M)) :
    phi_T_probability hN hM q E =
      ∑ A : ClosedAt v,
        ((if A.1 ∈ E then torusRCMass hN hM q A.1 else 0) +
          (if toggleEdge A.1 v ∈ E then torusRCMass hN hM q (toggleEdge A.1 v) else 0)) := by
  rw [phi_T_probability_eq_sum, ← (edgeStateEquiv v).symm.sum_comp, Fintype.sum_prod_type]
  simp only [edgeStateEquiv_symm_apply_false, edgeStateEquiv_symm_apply_true, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun A _ => ?_
  by_cases h1 : A.1 ∈ E <;> by_cases h2 : toggleEdge A.1 v ∈ E <;> simp [h1, h2, add_comm]

private theorem mass_toggle_le_odds (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (v : Fin N × Fin M) (A : ClosedAt v) :
    torusRCMass hN hM q (toggleEdge A.1 v) ≤
      ((rcCriticalParameter q).val / (1 - (rcCriticalParameter q).val)) *
        torusRCMass hN hM q A.1 := by
  simpa only [torusRCMass, mul_div_assoc] using
    (div_le_div_iff_of_pos_right (torusRCPartition_pos hN hM q)).2
      (torusRCWeight_toggle_le hN hM q A.1 v A.2)

/-- If an event is invariant under toggling an indexed edge, its closed-edge
probability is at least the Bernoulli closed probability times its full mass. -/
theorem torusRCProbability_closed_lower (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (v : Fin N × Fin M)
    (E : Set (RCConfig N M))
    (hstable : ∀ A, A ∈ E ↔ toggleEdge A v ∈ E) :
    (1 - (rcCriticalParameter q).val) * phi_T_probability hN hM q E ≤
      phi_T_probability hN hM q (E ∩ {A | A v = false}) := by
  classical
  let p := (rcCriticalParameter q).val
  have hp1 : 0 < 1 - p := sub_pos.mpr (criticalParameter_lt_one q)
  rw [phi_T_probability_split hN hM q v E, phi_T_probability_split hN hM q v (E ∩ {A | A v = false}),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun A _ => ?_
  by_cases hE : A.1 ∈ E
  · have htoggle : toggleEdge A.1 v ∈ E := (hstable A.1).mp hE
    have hopen : toggleEdge A.1 v v = true := by simp [toggleEdge, A.2]
    simp only [hE, htoggle, hopen, A.2, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Bool.true_eq_false, and_false, and_true, ite_true, ite_false, add_zero]
    calc
      (1 - p) * (torusRCMass hN hM q A.1 + torusRCMass hN hM q (toggleEdge A.1 v)) ≤
        (1 - p) * (torusRCMass hN hM q A.1 + (p / (1 - p)) * torusRCMass hN hM q A.1) :=
        mul_le_mul_of_nonneg_left (add_le_add_right (mass_toggle_le_odds hN hM q v A) _) hp1.le
      _ = torusRCMass hN hM q A.1 := by field_simp; ring
  · have htoggle : toggleEdge A.1 v ∉ E := mt (hstable A.1).mpr hE
    simp [hE, htoggle]

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
  classical
  induction S using Finset.induction_on with
  | empty => simp [closedOn]
  | @insert a T ha ih =>
      have hprev := ih fun v hv => hstable v (Finset.mem_insert_of_mem hv)
      have hstep := torusRCProbability_closed_lower hN hM q a (E ∩ closedOn T) fun A => by
        refine and_congr (hstable a (Finset.mem_insert_self a T) A) (forall₂_congr fun v hv => ?_)
        rw [toggleEdge_away A (by rintro rfl; exact ha hv)]
      have hset : (E ∩ closedOn T) ∩ {A | A a = false} = E ∩ closedOn (insert a T) := by
        ext A; simp [closedOn, and_left_comm, and_comm]
      rw [hset] at hstep
      rw [Finset.card_insert_of_notMem ha, pow_succ', mul_assoc]
      exact (mul_le_mul_of_nonneg_left hprev (sub_nonneg.mpr (criticalParameter_lt_one q).le)).trans
        hstep

end PottsDiscontinuity.TorusLoops
