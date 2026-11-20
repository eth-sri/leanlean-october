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

/-- The sum sigma-algebra makes sectionwise measurable maps measurable. -/
theorem historySigma_measurable_iff {I : Type*} {X : I → Type*} {Y : Type*}
    [∀ i, MeasurableSpace (X i)] [MeasurableSpace Y] (f : Sigma X → Y) :
    Measurable f ↔ ∀ i, Measurable (fun x => f ⟨i, x⟩) := by
  constructor
  · intro hf i
    have hi : Measurable (fun x : X i => (⟨i, x⟩ : Sigma X)) :=
      Measurable.of_le_map (iInf_le _ i)
    exact hf.comp hi
  · intro hf s hs
    rw [MeasurableSpace.measurableSet_iInf] <;> solve_by_elim

variable {J : Type*} [Fintype J] [LinearOrder J]

abbrev HistoryMarked (dependent : J → J → Prop) (E : Type*) :=
  Σ g : HistoryShape (fun a b => ¬ dependent a b), Fin (historyShapeLength dependent g) → E

section
variable (dependent : J → J → Prop)

/-- Each canonical history fiber is measurably included in the marked-history space. -/
theorem historyMarked_measurable_mk {E : Type*}
    [MeasurableSpace E] (g : HistoryShape (fun a b => ¬ dependent a b)) :
    Measurable (fun marks : Fin (historyShapeLength dependent g) → E => (⟨g, marks⟩ : HistoryMarked dependent E)) := by
  apply Measurable.of_le_map
  exact iInf_le _ g

/-- The chosen representative has exactly the intrinsic number of pieces. -/
theorem historyShapeLength_out
    (g : HistoryShape (fun a b => ¬ dependent a b)) :
    historyShapeLength dependent g = g.out.length := by
  have hh := congrArg (historyShapeLength dependent) (Quotient.out_eq g)
  simp_all [historyShapeLength_mk]

end

/-- Label evaluations in the canonical word of a shape. -/
def historyShapeCanonicalLabels (dependent : J → J → Prop)
    (g : HistoryShape (fun a b => ¬ dependent a b)) : Fin (historyShapeLength dependent g) → J :=
  fun i => g.out.get (Fin.cast (historyShapeLength_out dependent g) i)

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
    exact ih (fun marks => update (labels i) (marks i) (f marks))
      ((hu (labels i)).comp ((measurable_pi_apply i).prodMk hf))

/-- The actual finite recursion on a canonical marked representative. -/
def historyMarkedRawState (dependent : J → J → Prop) {E X : Type*}
    (update : J → E → X → X) (initial : X) (h : HistoryMarked dependent E) : X :=
  (List.ofFn (fun i : Fin (historyShapeLength dependent h.1) => i)).foldl
    (fun state i => update (historyShapeCanonicalLabels dependent h.1 i) (h.2 i) state) initial

/-- No measurability of a desired law is assumed: it follows from the finite recursion. -/
theorem historyMarkedRawState_measurable (dependent : J → J → Prop) {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] (update : J → E → X → X)
    (hu : ∀ j, Measurable (fun ex : E × X => update j ex.1 ex.2)) (initial : X) :
    Measurable (historyMarkedRawState dependent update initial) := by
  rw [historySigma_measurable_iff]
  intro g
  exact historyMarked_indexFold_measurable update hu (historyShapeLength dependent g)
      (historyShapeCanonicalLabels dependent g) (List.ofFn (fun i : Fin (historyShapeLength dependent g) => i))
      (fun _ => initial) measurable_const

/-- The unnormalized source measure: countably many shapes, independently marked. -/
def historyMarkedReferenceRaw (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) : Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
    Measure.map (Sigma.mk g) (Measure.pi fun _ : Fin (historyShapeLength dependent g) => π)

section
variable (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]

theorem historyMarkedReferenceRaw_univ :
    historyMarkedReferenceRaw dependent Δ π Set.univ =
      ∑' g, ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) := by
  unfold historyMarkedReferenceRaw
  simp_all

/-- The empty shape contributes exactly one unit of raw reference mass. -/
theorem historyMarkedReferenceRaw_univ_one_le :
    1 ≤ historyMarkedReferenceRaw dependent Δ π Set.univ := by
  rw [historyMarkedReferenceRaw_univ]
  let empty : HistoryShape (fun a b => ¬ dependent a b) := Quotient.mk _ []
  have he : ENNReal.ofReal (historyShapeReferenceWeight dependent Δ empty) = 1 := by
    simp [empty, historyShapeReferenceWeight, historyShapeLength_mk]
  rw [← he]
  exact ENNReal.le_tsum (f := fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g)) empty

end

theorem historyMarkedReferenceRaw_finite {dependent : J → J → Prop} {Δ : ℕ}
    (geom : HistoryDegreeBound dependent Δ) (hΔ : 1 ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) := by
  constructor
  rw [historyMarkedReferenceRaw_univ]
  exact (historyShapeReferenceWeight_summable geom hΔ).tsum_ofReal_lt_top

/-- The normalized actual infinite marked-history reference law `tau_0`. -/
def historyMarkedReference (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) : Measure (HistoryMarked dependent E) :=
  (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹ • historyMarkedReferenceRaw dependent Δ π

theorem historyMarkedReference_probability {dependent : J → J → Prop} {Δ : ℕ}
    (geom : HistoryDegreeBound dependent Δ) (hΔ : 1 ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (historyMarkedReference dependent Δ π) := by
  let : IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) :=
    historyMarkedReferenceRaw_finite geom hΔ π
  have hpos : historyMarkedReferenceRaw dependent Δ π Set.univ ≠ 0 := by
    have hh := historyMarkedReferenceRaw_univ_one_le dependent Δ π
    apply ne_of_gt <;> positivity
  unfold historyMarkedReference
  constructor
  exact ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)

end NearlyMinimax
