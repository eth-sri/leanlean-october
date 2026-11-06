module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSource
import Mathlib.Tactic.Ring

/-! # The complete flattened-profile conditions

The representatives below use the jointly selected witnesses of the profile statement.
The proposition records the full conclusion proved in `FlatteningSourceProfile`.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

variable {d : ℕ}

variable {alpha : ℝ} (h : CounterProfileStatement d alpha) (r : ℝ)

/-- The literal flattening of the selected profile. -/
noncomputable def selectedFlatProfile   : XV d → ℝ :=
  flatProfile (profileFunction h) flatteningPsi flatteningOffset alpha r

variable (q : XV d)

/-- The position derivative representative obtained by the scalar chain rule. -/
noncomputable def flatProfilePositionJet    : PDE.Vec d :=
  fun i => -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
    profilePositionJet h q i

/-- The velocity derivative representative obtained by the scalar chain rule. -/
noncomputable def flatProfileVelocityJet    : PDE.Vec d :=
  fun i => -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
    profileVelocityJet h q i

/-- The second velocity derivative, including the rank-one chain-rule term. -/
noncomputable def flatProfileHessian    : PDE.Mat d :=
  fun i k =>
    -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
      profileHessian h q i k -
    Real.rpow r (-alpha) *
      deriv (deriv flatteningPsi) (profileFunction h q / Real.rpow r alpha) *
      profileVelocityJet h q i * profileVelocityJet h q k

/-- The selected literal flattened profile is continuous. -/
theorem continuous_selectedFlatProfile   :
    Continuous (selectedFlatProfile h r) := by

  unfold selectedFlatProfile flatProfile
  exact continuous_const.sub (continuous_const.mul
    (contDiff_flatteningPsi.continuous.comp (((selectedProfile_spec h).2.2.2.2.2.2.1).div_const _)))

/-- The ordinary first chain rule at a differentiability point of the unflattened profile. -/
theorem fderiv_flatProfile  (H : XV d → ℝ) (alpha r : ℝ)
    (hr : 0 < r) (q : XV d) (hH : DifferentiableAt ℝ H q) :
    fderiv ℝ (flatProfile H flatteningPsi flatteningOffset alpha r) q =
      (-deriv flatteningPsi (H q / Real.rpow r alpha)) • fderiv ℝ H q := by
  let a := Real.rpow r alpha
  have ha  := (Real.rpow_pos_of_pos hr alpha).ne'
  have hin : HasFDerivAt (fun z => H z / a) (a⁻¹ • fderiv ℝ H q) q := by
    simpa only [div_eq_mul_inv, mul_comm] using hH.hasFDerivAt.const_mul a⁻¹
  have hp : DifferentiableAt ℝ flatteningPsi (H q / a) :=
    (contDiff_flatteningPsi.differentiable (by simp)).differentiableAt


  have he := (((hp.hasDerivAt.comp_hasFDerivAt q hin).const_mul a).const_sub (1 - flatteningOffset * a)).fderiv
  change fderiv ℝ (flatProfile H flatteningPsi flatteningOffset alpha r) q = _ at he
  rw [he]
  simp only [smul_smul]
  rw [← neg_smul]
  congr 1
  dsimp [a] at ha ⊢
  field_simp

/-- Entrywise contraction expands the rank-one term of the flattening chain rule. -/
theorem contraction_flattening_identity  (A B : PDE.Mat d)
    (w : PDE.Vec d) (s t : ℝ) :
    matrixContraction A (fun i k => -s * B i k - t * w i * w k) =
      -s * matrixContraction A B - t * PDE.vecDot (A.mulVec w) w := by
  unfold matrixContraction PDE.vecDot Matrix.mulVec dotProduct
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

variable {alpha : ℝ} (h : CounterProfileStatement d alpha) (r : ℝ)

/-- The explicit weak representatives satisfy the source equation algebraically almost everywhere.
This conclusion alone does not establish that they are derivatives of the flattened profile. -/
theorem flatProfile_representatives_source   :
    ∀ᵐ q,
      PDE.vecDot q.2 (flatProfilePositionJet h r q) -
        matrixContraction (profileMatrix h q) (flatProfileHessian h r q) =
      flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q := by


  filter_upwards [((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), ((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.1)] with q hq hj
  unfold flatProfilePositionJet flatProfileHessian
  rw [contraction_flattening_identity]
  unfold flatSource
  rw [← hj.2.1, hq]
  have hdot (s : ℝ) :
      PDE.vecDot q.2 (fun i => -s * profilePositionJet h q i) =
        -s * PDE.vecDot q.2 (profilePositionJet h q) := by
    unfold PDE.vecDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hdot]
  ring

/-- All explicit flattened derivative representatives are measurable. -/
theorem measurable_flatProfile_jets   :
    Measurable (flatProfilePositionJet h r) ∧ Measurable (flatProfileVelocityJet h r) ∧
      (∀ i k, Measurable (fun q => flatProfileHessian h r q i k)) := by


  have hmv := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.1

  have hpsi : Continuous (deriv flatteningPsi) := by
    rw [funext deriv_flatteningPsi]
    exact contDiff_flatteningSlope.continuous

  have harg := ((selectedProfile_spec h).2.2.2.2.2.2.1).measurable.div_const (Real.rpow r alpha)
  have hs := (hpsi.measurable.comp harg).neg

  refine ⟨?_, ?_, ?_⟩
  · apply Measurable.of_eval
    intro i
    exact hs.mul ((measurable_pi_apply i).comp ((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.1))
  · apply Measurable.of_eval
    intro i
    exact hs.mul ((measurable_pi_apply i).comp hmv)
  · intro i k
    exact (hs.mul (((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.1) i k)).sub
      (((measurable_const.mul ((show Continuous (deriv (deriv flatteningPsi)) by
          rw [funext deriv_flatteningPsi]
          exact contDiff_flatteningSlope.continuous_deriv (by simp)).measurable.comp harg)).mul ((measurable_pi_apply i).comp hmv)).mul ((measurable_pi_apply k).comp hmv))

/-- The complete weak flattened-profile conclusion required by the mollification lane. -/
def FlatProfileSourceStatement   : Prop :=
  let u := selectedFlatProfile h r
  let gx := flatProfilePositionJet h r
  let gv := flatProfileVelocityJet h r
  let hess := flatProfileHessian h r
  Continuous u ∧
  Measurable gx ∧ Measurable gv ∧ (∀ i k, Measurable (fun q => hess q i k)) ∧
  (∀ K : Set (XV d), IsCompact K →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q ∈ K,
      ‖gx q‖ ≤ M ∧ ‖gv q‖ ≤ M ∧ ∀ i k, |hess q i k| ≤ M) ∧
  (∀ i, LocallyIntegrable (fun q => gx q i) ) ∧
  (∀ i, LocallyIntegrable (fun q => gv q i) ) ∧
  (∀ i k, LocallyIntegrable (fun q => hess q i k) ) ∧
  (∀ᵐ q, gx q = dx u q ∧ gv q = dv u q ∧ hess q = dvv u q) ∧
  (∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
    (∀ i, (∫ q, u q * dx test q i) = -(∫ q, gx q i * test q)) ∧
    (∀ i, (∫ q, u q * dv test q i) = -(∫ q, gv q i * test q)) ∧
    (∀ i k, (∫ q, u q * dvv test q i k) = (∫ q, hess q i k * test q))) ∧
  (∀ᵐ q,
    PDE.vecDot q.2 (gx q) - matrixContraction (profileMatrix h q) (hess q) =
      flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q) ∧
  (∀ᵐ q, statOp (profileMatrix h) u q =
    flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
