module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.TransportSlices
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.IntervalDelay
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.InflationVolume
import Mathlib.MeasureTheory.Group.Prod

/-! # The sharp delayed-union estimate in kinetic transport coordinates -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/- Open stack interiors avoid any uncountable union of terminal faces. -/
def openForwardStack {d } (P : KineticPoint d) (r : ℝ) (m : ℕ) :
    Set (KineticPoint d) :=
  forwardStack P r m ∩ {X | X.time < P.time+(m : ℝ)*r^2}

/- Open forward stack interiors are open. -/
theorem isOpen_openForwardStack {d } (P : KineticPoint d) (r : ℝ) (m : ℕ) :
    IsOpen (openForwardStack P r m) := by
  have hx : Continuous (relativePosition P) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  have heq : openForwardStack P r m =
      {X | P.time < X.time ∧ X.time < P.time+(m : ℝ)*r^2 ∧
        X.velocity ∈ PDE.euclideanBall P.velocity r ∧
        relativePosition P X ∈ PDE.euclideanBall 0 (((m+2 : ℕ) : ℝ)*r^3)} := by
    ext X
    change (0 < X.time-P.time ∧ X.time-P.time ≤ (m : ℝ)*r^2 ∧ _ ∧ _) ∧ _ ↔ _
    constructor
    · rintro ⟨⟨ht, _, hv, hx⟩, htop⟩
      exact ⟨by linarith, htop, hv, hx⟩
    · rintro ⟨ht, htop, hv, hx⟩
      exact ⟨⟨by linarith, by linarith, hv, hx⟩, htop⟩
  rw [heq]
  exact (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      (((PDE.isOpen_euclideanBall _ _).preimage continuous_velocity).inter
        ((PDE.isOpen_euclideanBall _ _).preimage hx)))

/- Kinetic volume equals integration of time-slice volumes in transport coordinates. -/
theorem volume_transport_slices {d S}
    (hS : MeasurableSet S) :
    volume S = ∫⁻ v : PDE.Vec d, ∫⁻ y : PDE.Vec d,
      volume {t : ℝ | transportChart (v,y,t) ∈ S} := by
  have _h_xinl_0 : Continuous (@transportChart d) := by
    apply KineticPoint.continuous_mk <;> fun_prop
  have hs :=
    hS.preimage _h_xinl_0.measurable
  have _h_xinl_0 : MeasurePreserving (@transportChart d) volume volume := by
    have hshear : MeasurePreserving
        (fun z : PDE.Vec d × (PDE.Vec d × ℝ) => (z.1, z.2.2, z.2.1+z.2.2 • z.1))
        ((volume : Measure (PDE.Vec d)).prod volume)
        ((volume : Measure (PDE.Vec d)).prod volume) := by
      refine (MeasurePreserving.id (volume : Measure (PDE.Vec d))).skew_product
        (g := fun (v : PDE.Vec d) (z : PDE.Vec d × ℝ) => (z.2, z.1+z.2 • v)) ?_ ?_
      · exact (continuous_snd.snd.prodMk
          (continuous_snd.fst.add (continuous_snd.snd.smul continuous_fst))).measurable
      · exact Filter.Eventually.of_forall fun v => (measurePreserving_transport_fiber v).map_eq
    have hperm : MeasurePreserving
        (fun z : PDE.Vec d × (ℝ × PDE.Vec d) => (z.2.1, z.2.2, z.1)) volume volume := by
      simpa only [Measure.volume_eq_prod, Function.comp_def, Prod.swap,
      MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply] using
        (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure (PDE.Vec d))
          (volume : Measure (PDE.Vec d))).comp
          (Measure.measurePreserving_swap (μ := (volume : Measure (PDE.Vec d)))
            (ν := (volume : Measure (ℝ × PDE.Vec d))))
    have hinv : MeasurePreserving (KineticPoint.equivProd d).symm volume volume :=
      ⟨KineticPoint.measurable_equivProd_symm d, rfl⟩
    change MeasurePreserving
      (fun z : PDE.Vec d × (PDE.Vec d × ℝ) =>
        KineticPoint.mk z.2.2 (z.2.1+z.2.2 • z.1) z.1) _ _
    simpa only [Measure.volume_eq_prod, Function.comp_def, transportChart,
      KineticPoint.equivProd, Equiv.coe_fn_symm_mk] using hinv.comp (hperm.comp hshear)
  rw [← _h_xinl_0.measure_preimage hS.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_apply hs]
  apply lintegral_congr
  intro v
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurable_prodMk_left hs)]
  rfl

/- Each transport slice satisfies the sharp one-dimensional delayed-union inequality. -/
theorem delayed_union_slice {d } {ι : Type*} [Countable ι]
    (P : ι → KineticPoint d) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (m : ℕ) (hm : 0 < m) (v y : PDE.Vec d) :
    volume {t : ℝ | transportChart (v,y,t) ∈ ⋃ i, backwardCylinder (P i) (r i)} ≤
      ENNReal.ofReal (((m : ℝ)+1)/(m : ℝ)) *
        volume {t : ℝ | transportChart (v,y,t) ∈ ⋃ i, openForwardStack (P i) (r i) m} := by
  let A : Set ι := {i | v ∈ PDE.euclideanBall (P i).velocity (r i) ∧
    y ∈ PDE.euclideanBall ((P i).position-(P i).time • v) (2*(r i)^3)}
  have hback : {t : ℝ | transportChart (v,y,t) ∈ ⋃ i, backwardCylinder (P i) (r i)} ⊆
      ⋃ i : A, Ioo ((P i).time-(r i)^2) (P i).time := by
    intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    obtain ⟨htime, hv, hy⟩ := cylinder_transport_slice (P i) (hr i) v y t hi
    exact mem_iUnion.mpr ⟨⟨i, hv, hy⟩, htime⟩
  have hforward : (⋃ i : A, Ioo (P i).time ((P i).time+(m : ℝ)*(r i)^2)) ⊆
      {t : ℝ | transportChart (v,y,t) ∈ ⋃ i, openForwardStack (P i) (r i) m} := by
    intro t ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    apply mem_iUnion.mpr
    exact ⟨i, delayed_transport_slice (P i) (hr i) m v y t hi i.2.1 i.2.2, hi.2⟩
  calc
    _ ≤ volume (⋃ i : A, Ioo ((P i).time-(r i)^2) (P i).time) := measure_mono hback
    _ ≤ ENNReal.ofReal (((m : ℝ)+1)/(m : ℝ)) *
        volume (⋃ i : A, Ioo (P i).time ((P i).time+(m : ℝ)*(r i)^2)) :=
      interval_delay_countable (fun i : A => (P i).time) (fun i : A => (r i)^2)
        (by exact_mod_cast hm) (fun i => sq_pos_of_pos (hr i))
    _ ≤ _ := mul_le_mul_right (measure_mono hforward) _

/- Countable kinetic cylinder families satisfy the sharp delayed-union estimate. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
