module

public import PottsDiscontinuity.Torus.RibbonClusterSurgery
public import PottsDiscontinuity.TorusLoops.Measure
public import PottsDiscontinuity.Infra.PairedMass

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
  have hfilter :
      Finset.univ.filter (fun w : Fin N × Fin M => toggleEdge A v w = true) =
        insert v (Finset.univ.filter (fun w => A w = true)) := by
    ext w
    by_cases hw : w = v
    · subst w
      simp [toggleEdge, hA]
    · grind [toggleEdge_away]
  have hv : v ∉ Finset.univ.filter (fun w : Fin N × Fin M => A w = true) := by
    grind
  grind

theorem closedCount_toggle_of_closed (A : RCConfig N M) (v : Fin N × Fin M)
    (hA : A v = false) :
    closedCount A = closedCount (toggleEdge A v) + 1 := by
  have := openCount_toggle_of_closed A v hA
  have := openCount_add_closedCount A
  have := openCount_add_closedCount (toggleEdge A v)
  omega

/-- Opening a specified closed edge never increases the torus weight by more
than the Bernoulli odds `p_c/(1-p_c)`. -/
theorem torusRCWeight_toggle_le (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) (v : Fin N × Fin M)
    (hA : A v = false) :
    torusRCWeight hN hM q (toggleEdge A v) ≤
      ((rcCriticalParameter q).val / (1 - (rcCriticalParameter q).val)) *
        torusRCWeight hN hM q A := by
  have hk : clusterCount hN hM true (toggleEdge A v) ≤
      clusterCount hN hM true A := by
    by_cases hr : (diamondOpenGraph hN hM true A).Reachable
        (faceEndpoint hN hM true v false) (faceEndpoint hN hM true v true)
    · rw [clusterCount_toggle_of_reachable hN hM A v hA hr]
    · have ht := clusterCount_toggle_of_not_reachable hN hM A v hA hr
      omega
  unfold torusRCWeight
  rw [openCount_toggle_of_closed A v hA, closedCount_toggle_of_closed A v hA, pow_succ, pow_succ]
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ q.property hk)
    (by positivity [criticalParameter_pos q, criticalParameter_lt_one q])).trans_eq ?_
  field_simp [ne_of_gt (sub_pos.mpr (criticalParameter_lt_one q))]


section

variable (v : Fin N × Fin M)

abbrev ClosedAt :=
  {A : RCConfig N M // A v = false}

def edgeStateEquiv :
    RCConfig N M ≃ ClosedAt v × Bool where
  toFun A := (⟨Function.update A v false, by simp⟩, A v)
  invFun x := Function.update x.1.1 v x.2
  left_inv A := by
    simp
  right_inv x := by
    aesop

@[simp] private theorem edgeStateEquiv_symm_apply_false
    (A : ClosedAt v) : (edgeStateEquiv v).symm (A, false) = A.1 := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [edgeStateEquiv, A.2]
  · simp [edgeStateEquiv, Function.update_of_ne hw]

@[simp] private theorem edgeStateEquiv_symm_apply_true
    (A : ClosedAt v) :
    (edgeStateEquiv v).symm (A, true) = toggleEdge A.1 v := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [edgeStateEquiv, toggleEdge, A.2]
  · simp [edgeStateEquiv, toggleEdge, Function.update_of_ne hw]

end

section

variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))

/-- If an event is invariant under toggling an indexed edge, its closed-edge
probability is at least the Bernoulli closed probability times its full mass. -/
theorem torusRCProbability_closed_lower (v : Fin N × Fin M)
    (E : Set (RCConfig N M))
    (hstable : ∀ A, A ∈ E ↔ toggleEdge A v ∈ E) :
    (1 - (rcCriticalParameter q).val) * phi_T_probability hN hM q E ≤
      phi_T_probability hN hM q (E ∩ {A | A v = false}) := by
  classical
  let p := (rcCriticalParameter q).val
  let w := torusRCMass hN hM q
  simp only [phi_T_probability_eq_sum]
  refine (pairedMass_bounds (edgeStateEquiv v) w E {A | A v = false} false (b := 1) ?_ ?_ ?_).1
  · simpa using fun A : ClosedAt v => (hstable A.1).symm
  · intro A i
    cases i <;> simp [toggleEdge, A.2]
  · intro A
    simp only [edgeStateEquiv_symm_apply_false, edgeStateEquiv_symm_apply_true, one_mul]
    have hp : 0 < 1 - p := sub_pos.mpr (criticalParameter_lt_one q)
    have h := torusRCWeight_toggle_le hN hM q A.1 v A.2
    have hw : w (toggleEdge A.1 v) ≤ (p / (1 - p)) * w A.1 := by
      unfold w torusRCMass
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right h (torusRCPartition_pos hN hM q).le
    have hn := (torusRCMass_pos hN hM q (toggleEdge A.1 v)).le
    rw [div_mul_eq_mul_div] at hw
    constructor
    · nlinarith only [(le_div_iff₀ hp).mp hw]
    · linarith

def closedOn (S : Finset (Fin N × Fin M)) : Set (RCConfig N M) :=
  {A | ∀ v ∈ S, A v = false}

/-- Closing a finite prescribed edge set costs at most one factor `1-p_c`
per edge, provided the event being measured is invariant under those edge
toggles. -/
theorem torusRCProbability_close_finite_set (S : Finset (Fin N × Fin M))
    (E : Set (RCConfig N M))
    (hstable : ∀ v ∈ S, ∀ A, A ∈ E ↔ toggleEdge A v ∈ E) :
    (1 - (rcCriticalParameter q).val) ^ S.card * phi_T_probability hN hM q E ≤
      phi_T_probability hN hM q (E ∩ closedOn S) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [closedOn]
  | @insert a T ha ih =>
    have hs : ∀ A, A ∈ E ∩ closedOn T ↔ toggleEdge A a ∈ E ∩ closedOn T := by
      intro A
      exact and_congr (hstable a (Finset.mem_insert_self a T) A)
        (show A ∈ closedOn T ↔ toggleEdge A a ∈ closedOn T from
          forall₂_congr fun v hv => by rw [toggleEdge_away A (by grind : v ≠ a)])
    have hset : (E ∩ closedOn T) ∩ {A | A a = false} = E ∩ closedOn (insert a T) := by
      ext A
      simp [closedOn, and_left_comm, and_comm]
    rw [Finset.card_insert_of_notMem ha, pow_succ', mul_assoc, ← hset]
    exact (mul_le_mul_of_nonneg_left (ih (fun v hv => hstable v (Finset.mem_insert_of_mem hv)))
      (sub_nonneg.mpr (criticalParameter_lt_one q).le)).trans
      (torusRCProbability_closed_lower hN hM q a _ hs)

end

end PottsDiscontinuity.TorusLoops
