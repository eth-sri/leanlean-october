module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.InflationVolume
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Tactic
import Mathlib.Tactic.Measurability



/-! # Volume-preserving transport coordinates and cylinder slices -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- Transport coordinates ordered as velocity, transported position, time. -/
def transportChart {d : ℕ} (z : PDE.Vec d × (PDE.Vec d × ℝ)) : KineticPoint d :=
  ⟨z.2.2, z.2.1+z.2.2 • z.1, z.1⟩

/-- The transport chart is continuous. -/
theorem continuous_transportChart (d : ℕ) : Continuous (@transportChart d) := by
  apply KineticPoint.continuous_mk <;> fun_prop

/-- At fixed velocity, time-dependent position translation preserves product volume. -/
theorem measurePreserving_transport_fiber {d : ℕ} (v : PDE.Vec d) :
    MeasurePreserving (fun z : PDE.Vec d × ℝ => (z.2, z.1+z.2 • v)) volume  := by
  have h : MeasurePreserving (fun z : ℝ × PDE.Vec d => (z.1, z.2+z.1 • v))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) := by
    refine (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (g := fun t x => x+t • v) ?_ ?_
    · measurability
    · exact Filter.Eventually.of_forall fun t =>
        (measurePreserving_add_right (volume : Measure (PDE.Vec d)) (t • v)).map_eq
  simpa only [Measure.volume_eq_prod, Function.comp_def, Prod.swap,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply] using
    h.comp (Measure.measurePreserving_swap
      )

/-- The full transport chart preserves kinetic volume, with Jacobian one. -/
theorem measurePreserving_transportChart (d : ℕ) :
    MeasurePreserving (@transportChart d) volume  := (id
  (id
    (MeasurePreserving.comp { measurable := KineticPoint.measurable_equivProd_symm d, map_eq := rfl }
      (MeasurePreserving.comp
        (id
          (Eq.mp
            (congrFun'
              (congrFun'
                (congrArg
                  (@MeasurePreserving (PDE.Vec d × ℝ × PDE.Vec d) (ℝ × PDE.Vec d × PDE.Vec d) Prod.instMeasurableSpace
                    Prod.instMeasurableSpace)
                  (funext fun x => Equiv.prodAssoc_apply ℝ (PDE.Vec d) (PDE.Vec d) (x.2, x.1)))
                (volume.prod (volume.prod volume)))
              (volume.prod (volume.prod volume)))
            (MeasurePreserving.comp (measurePreserving_prodAssoc volume volume volume) Measure.measurePreserving_swap)))
        (MeasurePreserving.skew_product (MeasurePreserving.id volume)
          (Measurable.prodMk (Measurable.snd (Measurable.snd measurable_id'))
            (Measurable.fun_add (Measurable.fst (Measurable.snd measurable_id'))
              (Measurable.fun_smul (Measurable.snd (Measurable.snd measurable_id')) (Measurable.fst measurable_id'))))
          (Filter.Eventually.of_forall fun v => (measurePreserving_transport_fiber v).map_eq))))))

variable {d : ℕ} (P : KineticPoint d) {r : ℝ} (hr : 0 < r)

include hr
/-- Backward transport slices fit in a fixed transported position ball of radius 2r³. -/
theorem cylinder_transport_slice
    (v y : PDE.Vec d) (t : ℝ)
    (h : transportChart (v, y, t) ∈ backwardCylinder P r) :
    t ∈ Ioo (P.time-r^2) P.time ∧ v ∈ PDE.euclideanBall P.velocity r ∧
      y ∈ PDE.euclideanBall (P.position-P.time • v) (2*r^3) := by
  refine ⟨⟨h.1, h.2.1⟩, h.2.2.1, ?_⟩
  have hv := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp h.2.2.1
  have hx := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3)).mp h.2.2.2
  rw [sub_zero] at hx
  change PDE.vecEuclideanNorm (v-P.velocity) < r at hv
  have htime₁ : P.time-r^2 < t := h.1
  have htime₂ : t < P.time := h.2.1

  have heq : y-(P.position-P.time • v) = relativePosition P (transportChart (v,y,t))-
      (t-P.time) • (v-P.velocity) := by
    ext i
    simp only [relativePosition, transportChart, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity : 0 < 2*r^3), heq]
  have hn := PDE.vecEuclideanNorm_add_le (relativePosition P (transportChart (v,y,t)))
    (-((t-P.time) • (v-P.velocity)))
  rw [PDE.vecEuclideanNorm_neg, PDE.vecEuclideanNorm_smul] at hn
  rw [sub_eq_add_neg]
  have hm := mul_le_mul (show |t-P.time| < r^2 by
      rw [abs_lt]
      constructor <;> linarith only [htime₁, htime₂]).le hv.le (PDE.vecEuclideanNorm_nonneg _) (sq_nonneg r)
  nlinarith

/-- The delayed transport product is contained in the forward stack. -/
theorem delayed_transport_slice
    (m : ℕ) (v y : PDE.Vec d) (t : ℝ)
    (ht : t ∈ Ioo P.time (P.time+(m : ℝ)*r^2))
    (hv : v ∈ PDE.euclideanBall P.velocity r)
    (hy : y ∈ PDE.euclideanBall (P.position-P.time • v) (2*r^3)) :
    transportChart (v,y,t) ∈ forwardStack P r m := by
  let sharedTerm_ecf15ecb7b := ((m : ℝ) * r ^ 2)
  refine ⟨by change 0 < t-P.time; linarith only [ht.1],
    by change t-P.time ≤ sharedTerm_ecf15ecb7b; linarith only [ht.2], hv, ?_⟩

  have hyn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by positivity : 0 < 2*r^3)).mp hy
  have heq : relativePosition P (transportChart (v,y,t)) =
      (y-(P.position-P.time • v))+(t-P.time) • (v-P.velocity) := by
    ext i
    simp only [relativePosition, transportChart, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity), sub_zero, heq]
  have hn := PDE.vecEuclideanNorm_add_le (y-(P.position-P.time • v))
    ((t-P.time) • (v-P.velocity))
  rw [PDE.vecEuclideanNorm_smul, abs_of_pos (sub_pos.mpr ht.1)] at hn
  have hm := mul_le_mul (by linarith only [ht.2] : t-P.time ≤ sharedTerm_ecf15ecb7b)
    ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hv).le (PDE.vecEuclideanNorm_nonneg _) (by positivity : 0 ≤ sharedTerm_ecf15ecb7b)
  push_cast
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
