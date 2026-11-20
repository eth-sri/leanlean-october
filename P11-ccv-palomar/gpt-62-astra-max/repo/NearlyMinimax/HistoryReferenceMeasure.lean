module

public import NearlyMinimax.HistoryReferenceSum
public import NearlyMinimax.FiniteSigmaProbability

@[expose] public section

/-!
# Actual marked-history reference probability measure

The countable shape law uses the source weight `rho^length`. Conditional on a
shape, all of its marks have the independent finite product law. The source
shape-count argument proves finiteness, and the empty shape proves nonzero
mass, so normalization constructs a probability measure without a finiteness
or positivity assumption on the desired law.
-/

noncomputable section
open MeasureTheory
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

abbrev HistoryMarked (dependent : J → J → Prop) (E : Type*) :=
  Σ g : DependenceHeap dependent, Fin (historyShapeLength g) → E

section
variable {dependent : J → J → Prop} {E I : Type*}

/-- The chosen representative has exactly the intrinsic number of pieces. -/
theorem historyShapeLength_out
    (g : DependenceHeap dependent) :
    historyShapeLength g = g.out.length := by
  have hh := congrArg (historyShapeLength) (Quotient.out_eq g)
  rw [historyShapeLength_mk] at hh
  exact hh.symm

/-- Label evaluations in the canonical word of a shape. -/
def historyShapeCanonicalLabels
    (g : DependenceHeap dependent) : Fin (historyShapeLength g) → J :=
  fun i => g.out.get (Fin.cast (historyShapeLength_out g) i)

end

omit [Fintype J] [LinearOrder J] in
/-- Finite marked update recursion is measurable for measurable local updates. -/
theorem historyMarked_indexFold_measurable {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] (update : J → E → X → X)
    (hu : ∀ j, Measurable (fun ex : E × X => update j ex.1 ex.2))
    (n : ℕ) (labels : Fin n → J) (indices : List (Fin n))
    (f : (Fin n → E) → X) (hf : Measurable f) :
    Measurable (fun marks => indices.foldl (fun state i => update (labels i) (marks i) state) (f marks)) := by
  induction indices generalizing f with
  | nil => exact hf
  | cons i indices ih =>
    fun_prop

/-- The actual finite recursion on a canonical marked representative. -/
def historyMarkedRawState {dependent : J → J → Prop} {E X : Type*}
    (update : J → E → X → X) (initial : X) (h : HistoryMarked dependent E) : X :=
  (List.ofFn (fun i : Fin (historyShapeLength h.1) => i)).foldl
    (fun state i => update (historyShapeCanonicalLabels h.1 i) (h.2 i) state) initial

section
variable (dependent : J → J → Prop) (Δ : ℕ) {E X : Type*} [MeasurableSpace E] (π : Measure E)

/-- No measurability of a desired law is assumed: it follows from the finite recursion. -/
theorem historyMarkedRawState_measurable [MeasurableSpace X] (update : J → E → X → X)
    (hu : ∀ j, Measurable (fun ex : E × X => update j ex.1 ex.2)) (initial : X) :
    Measurable (historyMarkedRawState (dependent := dependent) update initial) := by
  rw [sigma_measurable_iff]
  intro g
  exact historyMarked_indexFold_measurable update hu (historyShapeLength g)
    (historyShapeCanonicalLabels g) (List.ofFn (fun i : Fin (historyShapeLength g) => i))
    (fun _ => initial) measurable_const

/-- The unnormalized source measure: countably many shapes, independently marked. -/
def historyMarkedReferenceRaw : Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight Δ g) •
    Measure.map (Sigma.mk g) (Measure.pi fun _ : Fin (historyShapeLength g) => π)

theorem historyMarkedReferenceRaw_univ [IsProbabilityMeasure π] :
    historyMarkedReferenceRaw dependent Δ π Set.univ =
      ∑' g, ENNReal.ofReal (historyShapeReferenceWeight (dependent := dependent) Δ g) := by
  unfold historyMarkedReferenceRaw
  simp

/-- The empty shape contributes exactly one unit of raw reference mass. -/
theorem historyMarkedReferenceRaw_univ_one_le [IsProbabilityMeasure π] :
    1 ≤ historyMarkedReferenceRaw dependent Δ π Set.univ := by
  rw [historyMarkedReferenceRaw_univ]
  let empty : DependenceHeap dependent := Quotient.mk _ []
  have he : ENNReal.ofReal (historyShapeReferenceWeight Δ empty) = 1 := by
    simp [empty, historyShapeReferenceWeight, historyShapeLength_mk]
  rw [← he]
  exact ENNReal.le_tsum (f := fun g => ENNReal.ofReal (historyShapeReferenceWeight Δ g)) empty

theorem historyMarkedReferenceRaw_finite {dependent : J → J → Prop}
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hlabels : DegreeAtMost dependent Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) := by
  constructor
  rw [historyMarkedReferenceRaw_univ]
  exact (historyShapeReferenceWeight_summable hΔ hlabels).tsum_ofReal_lt_top

/-- The normalized actual infinite marked-history reference law `tau_0`. -/
def historyMarkedReference : Measure (HistoryMarked dependent E) :=
  (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹ • historyMarkedReferenceRaw dependent Δ π

end

theorem historyMarkedReference_probability {dependent : J → J → Prop}
    [Std.Refl dependent] [Std.Symm dependent]
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (hlabels : DegreeAtMost dependent Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (historyMarkedReference dependent Δ π) := by
  let  :=
    historyMarkedReferenceRaw_finite hΔ hlabels π
  have hpos : historyMarkedReferenceRaw dependent Δ π Set.univ ≠ 0 := by
    have hh := historyMarkedReferenceRaw_univ_one_le dependent Δ π
    positivity
  constructor
  exact ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)

end NearlyMinimax
