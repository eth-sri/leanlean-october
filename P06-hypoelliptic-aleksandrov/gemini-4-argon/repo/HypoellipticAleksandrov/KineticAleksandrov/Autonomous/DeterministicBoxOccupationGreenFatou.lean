module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationEndpointLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsWeightLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationBarrierEndpoint
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BarrierModulusEstimates
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrier

/-! # Singular Bellman Green inequality for the actual occupation measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set Filter
open scoped Topology ENNReal
open BarrierRegularization

/- Position regularization and extended Fatou retain the singular weight at every atom.
The first bound is the signed terminal endpoint difference. -/
theorem deterministic_barrier_green_fatou
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam alpha c } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    {phi } (h : IsBellmanHomogeneous alpha phi)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hc : 0 < c)
    (hbound : ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) (hT : 0 < (T : ℝ)) (Y : ℝ) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    ENNReal.ofReal c *
      (∫⁻ q, rhoWeight (gamma alpha) (q.1 - Y, q.2)
        ∂physicalOccupationMeasure E z T) ≤
      ENNReal.ofReal (∫ q, bellmanOriginExtension phi (q.1 - Y, q.2) -
        bellmanOriginExtension phi (z.1 - Y, z.2) ∂kernelXV E T z) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let f := fun n : ℕ => fun q : Z => ENNReal.ofReal c *
    ENNReal.ofReal (regularizedBarrierWeight alpha n (q.1 - Y, q.2))
  let F := fun q : Z => ENNReal.ofReal c * rhoWeight (gamma alpha) (q.1 - Y, q.2)
  let b := fun n : ℕ =>
    (∫ q, positionConvolution (barrierMollifier n) (bellmanOriginExtension phi)
      (q.1 - Y, q.2) ∂kernelXV E T z) -
    positionConvolution (barrierMollifier n) (bellmanOriginExtension phi) (z.1 - Y, z.2)
  have hm (n : ℕ) : Measurable (f n) := measurable_const.mul
    (ENNReal.measurable_ofReal.comp ((regularizedBarrierWeight_measurable alpha n).comp
      ((measurable_fst.sub_const Y).prodMk measurable_snd)))
  have hp (q : Z) : Tendsto (fun n => f n q) atTop (𝓝 (F q)) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).tendsto
      (rhoWeight (gamma alpha) (q.1 - Y, q.2)) |>.comp
        (regularizedBarrierWeight_tendsto alpha ha ha1 (q.1 - Y, q.2))
  have hi (n : ℕ) : (∫⁻ q, f n q ∂physicalOccupationMeasure E z T) ≤
      ENNReal.ofReal (b n) := by
    rw [show f n = fun q => ENNReal.ofReal c *
      ENNReal.ofReal (regularizedBarrierWeight alpha n (q.1 - Y, q.2)) from rfl,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact deterministic_regularized_barrier_green hH hLE hlam hLam h ha ha1 hc hbound
      _ (barrierMollifier_spec n) A z T hT Y
  simpa only [F, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] using (singular_fatou_of_real_bounds (physicalOccupationMeasure E z T) f F hm hp b _ (barrier_mollifier_endpoint_tendsto hH hLE hlam hLam h ha ha1 A z T Y) hi)

/- A selected barrier gives a uniform quantitative occupation bound with no return-time input.
Both constants are chosen before the coefficient field, pole, time and translation. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
