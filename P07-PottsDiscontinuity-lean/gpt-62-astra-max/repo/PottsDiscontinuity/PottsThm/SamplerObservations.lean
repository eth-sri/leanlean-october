module

public import PottsDiscontinuity.PottsThm.PottsColoringErgodicity
public import PottsDiscontinuity.PottsThm.ColoringCylinderLaw

@[expose] public section
namespace PottsDiscontinuity.PottsThm
open MeasureTheory Set Filter FK RCInfinite Potts ProbabilityTheory
open scoped ENNReal Classical

variable {q : ℕ} {φ : Measure LatticeConfiguration} [IsProbabilityMeasure φ]

variable (pin : Set.Icc 1 q) {E : Set (SpinSpace q)}

/-- Disintegrate an observation of the colouring by first fixing its bonds. -/
theorem colorLaw_apply (hE : MeasurableSet E) :
    colorLaw φ pin E = ∫⁻ ω, colorNoise _ ((fun u => clusterColoring pin (ω,u)) ⁻¹' E) ∂φ := by
  let : Nonempty (Set.Icc 1 q) := ⟨pin⟩
  rw [colorLaw, Measure.map_apply (measurable_clusterColoring pin) hE,
    Measure.prod_apply (measurable_clusterColoring pin hE)]
  rfl

private theorem colorLaw_two_values (hE : MeasurableSet E)
    {S : Set LatticeConfiguration} (hS : MeasurableSet S) {r t : ℝ≥0∞} (hr : r ≠ ⊤) (ht : t ≠ ⊤)
    (hf : ∀ᵐ ω ∂φ, colorNoise _ ((fun u => clusterColoring pin (ω,u)) ⁻¹' E) =
      if ω ∈ S then r else t) :
    (colorLaw φ pin).real E = t.toReal + (r.toReal - t.toReal) * φ.real S := by
  rw [Measure.real_def, colorLaw_apply pin hE, lintegral_congr_ae hf]
  change (∫⁻ ω, S.piecewise (fun _ => r) (fun _ => t) ω ∂φ).toReal = _
  rw [lintegral_piecewise hS]
  simp only [lintegral_const, Measure.restrict_apply_univ, ENNReal.toReal_add
    (ENNReal.mul_ne_top hr (measure_ne_top _ _)) (ENNReal.mul_ne_top ht (measure_ne_top _ _)),
    ENNReal.toReal_mul, ← Measure.real_def, measureReal_compl hS, probReal_univ]
  ring

/-- At a site in an infinite cluster one sees the pin; otherwise the site's
colour is uniform. The formula also covers off-pin colours. -/
theorem colorLaw_one_site (pin c : Set.Icc 1 q) (x : Vertex) :
    (colorLaw φ pin).real {σ | σ x = c} = (q : ℝ)⁻¹ +
      ((if pin = c then 1 else 0) - (q : ℝ)⁻¹) * φ.real (infiniteAt x) := by
  let : Nonempty (Set.Icc 1 q) := ⟨pin⟩
  have hq0 : 0 < q := pin.prop.1.trans pin.prop.2
  apply Eq.trans (colorLaw_two_values (φ := φ) pin ((measurable_pi_apply x) (measurableSet_singleton c))
    (measurableSet_infiniteAt x) (r := if pin = c then 1 else 0) (t := q⁻¹)
    (by split <;> simp) (by simp [hq0.ne']) ?_)
  · simp [apply_ite ENNReal.toReal]
  apply Eventually.of_forall; intro ω
  have hn := clusterRepresentative_none_iff ω x
  change _ ↔ ω ∈ infiniteAt x at hn
  cases h : clusterRepresentative ω x with
  | none =>
    change colorNoise _ ((fun u => (clusterRepresentative ω x).elim pin u) ⁻¹' {c}) = _
    aesop
  | some y =>
    have hf : ω ∉ infiniteAt x := by grind
    simp only [hf, if_false]
    change colorNoise _ ((fun u => (clusterRepresentative ω x).elim pin u) ⁻¹' {c}) = _
    rw [h]; exact ((measurePreserving_eval_infinitePi (fun _ : Vertex => uniformOn univ) y).measure_preimage
      (measurableSet_singleton c).nullMeasurableSet).trans (pottsUniformColor_singleton q c)

private theorem noise_agreement {x y : Vertex} (hxy : x ≠ y) [Nonempty (Set.Icc 1 q)] :
    colorNoise (Set.Icc 1 q) {u | u x = u y} = (q : ℝ≥0∞)⁻¹ := by
  let ν : Measure (Set.Icc 1 q) := uniformOn univ
  have hind : iIndepFun (fun j (u : Vertex → Set.Icc 1 q) => u j) (colorNoise _) :=
    iIndepFun_infinitePi (X := fun _ c => c) (by fun_prop)
  let f (u : Vertex → Set.Icc 1 q) := (u x, u y)
  have hm : (colorNoise _).map f = ν.prod ν := by
    simpa [ν, colorNoise, iidFieldMeasure, Measure.infinitePi_map_eval, f] using
      (hind.indepFun hxy).map_prod_eq_prod_map_map (measurable_pi_apply x).aemeasurable
        (measurable_pi_apply y).aemeasurable
  have hD : MeasurableSet (diagonal (Set.Icc 1 q)) := measurableSet_diagonal
  change colorNoise _ (f ⁻¹' diagonal _) = _
  rw [← Measure.map_apply (by fun_prop) hD, hm,
    Measure.prod_apply hD]
  simpa [diagonal, Set.preimage, eq_comm, ν, pottsUniformColor_singleton]

/-- In a free phase all clusters are finite. Connected sites agree surely;
distinct clusters agree with the uniform coincidence probability. -/
theorem colorLaw_agreement (x y : Vertex)
    (hfin : ∀ᵐ ω ∂φ, ∀ z, (cluster ω z).Finite) :
    (colorLaw φ pin).real {σ | σ x = σ y} = (q : ℝ)⁻¹ + (1 - (q : ℝ)⁻¹) *
      φ.real {ω | (rcInfiniteOpenGraph ω).Reachable x y} := by
  let : Nonempty (Set.Icc 1 q) := ⟨pin⟩
  have hq0 : 0 < q := pin.prop.1.trans pin.prop.2
  apply Eq.trans (colorLaw_two_values pin (measurableSet_eq_fun (measurable_pi_apply x) (measurable_pi_apply y))
    (measurableSet_open_reachable x y) (r := 1) (t := q⁻¹) (by simp) (by simp [hq0.ne']) ?_)
  · simp
  filter_upwards [hfin] with ω hf
  have eqv := clusterRepresentative_eq_iff_reachable ω (hf x) (hf y)
  cases hx : clusterRepresentative ω x with
  | none => exact ((clusterRepresentative_none_iff ω x).mp hx (hf x)).elim
  | some v =>
    cases hy : clusterRepresentative ω y with
    | none => exact ((clusterRepresentative_none_iff ω y).mp hy (hf y)).elim
    | some w =>
      simp only [hx, hy, Option.some.injEq] at eqv
      simp only [Set.mem_ofPred_eq, ← eqv, Set.preimage, clusterColoring, hx, hy, Option.elim_some]
      split_ifs with e
      · simp_all
      · exact noise_agreement e

end PottsDiscontinuity.PottsThm
