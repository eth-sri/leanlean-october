module
public import HypoellipticAleksandrov.Parabolic.Transposition.KineticFields
public import HypoellipticAleksandrov.Parabolic.Transposition.Lift
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
import Mathlib

/-! # Continuous, bounded pointwise limits of harmonic functions

Pass to the limit against a compact adjoint test, then apply interior hypoellipticity.
Only a bound on the functions is needed, with no convergence assumptions on their jets.
-/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open Hypoellipticity KineticAleksandrov Set Filter MeasureTheory
open scoped ContDiff Topology MatrixOrder
variable {d k : ℕ} {U : Domain d}

theorem harmonic_limit (X : Fin (k+1) → Vector d) (span : LieAlgebraSpansOn ((unpack _) ⁻¹' (U : Set _)) (fun i => liftField (X i)))
    (u : ℕ → Local U) (h : ∀ i z, z ∈ U → generator X (u i).val z = 0) {C : ℝ} (bnd : ∀ i z, z ∈ U → |(u i).val z| ≤ C)
    {v : TimeVelocity d → ℝ} (hc : ContinuousOn v U) (hv : ∀ z ∈ U, Tendsto (fun i => (u i).val z) atTop (𝓝 (v z))) :
    ContDiffOn ℝ ∞ v U ∧ ∀ z ∈ U, generator X v z = 0 := by
  obtain ⟨w,hw,he⟩ := smooth_solution ⟨fun _ => 0,contDiff_const⟩ span v (hc.locallyIntegrableOn U.isOpen.measurableSet) (by
    intro φ
    let ψ := adjoint X φ
    have hz (i) : ∫ z in U, (u i).val z * ψ z = 0 := by
      rw [← local_apply,generator_pair,pair_eq,local_apply,applied_val]
      exact setIntegral_eq_zero_of_forall_eq_zero fun z hz => by rw [h i z hz,zero_mul]
    have h0 : Tendsto (fun i => ∫ z in U, (u i).val z * ψ z) atTop (𝓝 0) := by simp [hz]
    simp only [zero_mul, integral_zero]
    apply tendsto_nhds_unique _ h0
    refine tendsto_integral_of_dominated_convergence (fun z => C*|ψ z|) (fun i => (local_int (u i) ψ).aestronglyMeasurable) ?_ ?_ ?_
    · exact (ψ.contDiff.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).norm.restrict.const_mul C
    · intro i; filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with z hm
      simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_right (bnd i z hm) (abs_nonneg (ψ z))
    · filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with z hm using (hv z hm).mul_const (ψ z))
  have e := Measure.eqOn_open_of_ae_eq hw U.isOpen hc (smooth_local w).continuousOn
  exact ⟨(smooth_local w).congr e,fun z hz => (generator_congr (e.eventuallyEq_of_mem (U.isOpen.mem_nhds hz))).trans (he hz)⟩

/-- Interior regularity and equation of a kinetic cutoff limit in physical coordinates. -/
theorem kinetic_harmonic_limit {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {T : ℝ}
    (hΩ : IsOpen Ω) (hγ : Continuous γ) {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {lam Lam m : ℝ}
    (hlam : 0 < lam) (hB : IsSmoothFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hb : IsSmoothDrift b) (hm : 0 < m) (hcoerc : HasUnitDirectionDriftCoercivity m b) (u : ℕ → KineticPoint n → ℝ) (v : KineticPoint n → ℝ)
    (hs : ∀ i, ContDiffOn ℝ ∞ (fun q => u i ⟨q.1,q.2.1,q.2.2⟩) (evolutionPastInteriorRaw Ω γ T))
    (he : ∀ i p, p ∈ evolutionPastOpenCylinder Ω γ T → transportedForwardOperator B b (u i) p = 0)
    {C : ℝ} (hC : ∀ i p, p ∈ evolutionPastOpenCylinder Ω γ T → |u i p| ≤ C)
    (hc : ContinuousOn v (evolutionPastOpenCylinder Ω γ T))
    (ht : ∀ p ∈ evolutionPastOpenCylinder Ω γ T, Tendsto (fun i => u i p) atTop (𝓝 (v p))) :
    ContDiffOn ℝ ∞ (fun q => v ⟨q.1,q.2.1,q.2.2⟩) (evolutionPastInteriorRaw Ω γ T) ∧ ∀ p ∈ evolutionPastOpenCylinder Ω γ T, transportedForwardOperator B b v p = 0 := by
  let U : Domain (n+n) := ⟨(split n) ⁻¹' evolutionPastInteriorRaw Ω γ T, (isOpen_evolutionPastInteriorRaw hΩ hγ T).preimage (split n).continuous⟩
  have maps : MapsTo (world n) (U : Set _) (evolutionPastOpenCylinder Ω γ T) := fun _ hz => hz
  let w (i : ℕ) : Local U := ⟨u i ∘ world n,(hs i).comp (split n).contDiff.contDiffOn (fun _ z => z)⟩
  obtain ⟨X,span,op⟩ := kinetic_fields U hlam hB hell hb hm hcoerc
  obtain ⟨s,e⟩ := harmonic_limit X span w
    (fun i z hz => (op (u i) z (((smooth_local (w i)).contDiffAt (U.isOpen.mem_nhds hz)).of_le (by simp))).trans (he i _ (maps hz)))
    (fun i z hz => hC i _ (maps hz)) (hc.comp (world n).continuous.continuousOn maps) (fun z hz => ht _ (maps hz))
  refine ⟨?_,fun p hp => ?_⟩
  · have rev : MapsTo (split n).symm (evolutionPastInteriorRaw Ω γ T) (U : Set _) := by
      intro q hq; change split n ((split n).symm q) ∈ evolutionPastInteriorRaw Ω γ T; rwa [ContinuousLinearEquiv.apply_symm_apply]
    have key := s.comp (split n).symm.contDiff.contDiffOn rev
    apply key.congr; intro q hq
    change v ⟨q.1,q.2.1,q.2.2⟩ = v ⟨(split n ((split n).symm q)).1,(split n ((split n).symm q)).2.1,(split n ((split n).symm q)).2.2⟩
    rw [ContinuousLinearEquiv.apply_symm_apply]
  · let z := (world n).symm p
    have ep : world n z = p := (world n).apply_symm_apply p
    have hz : z ∈ U := (ep ▸ hp : world n z ∈ evolutionPastOpenCylinder Ω γ T)
    simpa only [ep] using (op v z ((s.contDiffAt (U.isOpen.mem_nhds hz)).of_le (by simp))).symm.trans (e z hz)

end HypoellipticAleksandrov.Parabolic.Transposition
