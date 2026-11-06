module

public import NearlyMinimax.HistoryReferenceSum

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



section
variable (dependent : J → J → Prop)
include dependent

abbrev HistoryMarked  (E : Type*) :=
  Σ g : HistoryShape (fun a b => ¬ dependent a b), Fin (historyShapeLength dependent g) → E

/-- Each canonical history fiber is measurably included in the marked-history space. -/
theorem historyMarked_measurable_mk  {E : Type*}
    [MeasurableSpace E] (g : HistoryShape (fun a b => ¬ dependent a b)) :
    Measurable (fun marks : Fin (historyShapeLength dependent g) → E => (⟨g, marks⟩ : HistoryMarked dependent E)) := by
  apply Measurable.of_le_map
  exact iInf_le _ g

/-- A map on histories is measurable exactly when it is measurable on every shape fiber. -/
theorem historyMarked_measurable_iff  {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] (f : HistoryMarked dependent E → X) :
    Measurable f ↔ ∀ g, Measurable (fun marks => f ⟨g, marks⟩) := by
  constructor
  · intro hf g
    exact hf.comp (historyMarked_measurable_mk dependent g)
  · intro hf s hs
    
    rw [MeasurableSpace.measurableSet_iInf]
    exact fun g => hf g hs
end


/-- A countable disjoint union of Borel fibers has exactly their sum sigma-algebra. -/
theorem historySigma_borelSpace {I : Type*} [Countable I] {X : I → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)] :
    BorelSpace (Sigma X) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hsec  :=
      MeasurableSpace.measurableSet_iInf.1 hs
    let  := borel (Sigma X)
    let : BorelSpace (Sigma X) := ⟨rfl⟩
    have hu : s = ⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' s) := by
      ext x
      constructor
      · intro hx; exact Set.mem_iUnion.2 ⟨x.1, x.2, hx, rfl⟩
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨i, y, hy, rfl⟩
        exact hy
    rw [hu]
    exact MeasurableSet.iUnion fun i =>
      (Topology.IsClosedEmbedding.sigmaMk (i := i)).measurableEmbedding.measurableSet_image' (hsec i)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    intro i
    exact (hs.preimage continuous_sigmaMk).measurableSet

section
variable (dependent : J → J → Prop) (g : HistoryShape (fun a b => ¬ dependent a b))

/-- The chosen representative has exactly the intrinsic number of pieces. -/
theorem historyShapeLength_out  :
    historyShapeLength dependent g = g.out.length := by
  have hh := congrArg (historyShapeLength dependent) (Quotient.out_eq g)
  rw [historyShapeLength_mk] at hh
  exact hh.symm

/-- Label evaluations in the canonical word of a shape. -/
def historyShapeCanonicalLabels   :=
  fun i => g.out.get (Fin.cast (historyShapeLength_out dependent g) i)
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
    exact ih (fun marks => update (labels i) (marks i) (f marks))
      ((hu (labels i)).comp ((measurable_pi_apply i).prodMk hf))

section
variable (dependent : J → J → Prop)

section
variable {E X : Type*}

/-- The actual finite recursion on a canonical marked representative. -/
def historyMarkedRawState  
    (update : J → E → X → X) (initial : X) (h : HistoryMarked dependent E) : X :=
  (List.ofFn (fun i : Fin (historyShapeLength dependent h.1) => i)).foldl
    (fun state i => update (historyShapeCanonicalLabels dependent h.1 i) (h.2 i) state) initial

/-- No measurability of a desired law is assumed: it follows from the finite recursion. -/
theorem historyMarkedRawState_measurable  
    [MeasurableSpace E] [MeasurableSpace X] (update : J → E → X → X)
    (hu : ∀ j, Measurable (fun ex : E × X => update j ex.1 ex.2)) (initial : X) :
    Measurable (historyMarkedRawState dependent update initial) := by
  rw [historyMarked_measurable_iff]
  
  unfold historyMarkedRawState
  aesop (add unsafe [historyMarked_indexFold_measurable])
end


section
variable (Δ : ℕ) {E : Type*}
include Δ

/-- The unnormalized source measure: countably many shapes, independently marked. -/
def historyMarkedReferenceRaw  
    [MeasurableSpace E] (π : Measure E) : Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
    Measure.map (Sigma.mk g) (Measure.pi fun _ : Fin (historyShapeLength dependent g) => π)

section
variable [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]

theorem historyMarkedReferenceRaw_univ  
     :
    historyMarkedReferenceRaw dependent Δ π Set.univ =
      ∑' g, ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) := by
  unfold historyMarkedReferenceRaw
  simp_all

/-- The empty shape contributes exactly one unit of raw reference mass. -/
theorem historyMarkedReferenceRaw_univ_one_le  
     :
    1 ≤ historyMarkedReferenceRaw dependent Δ π Set.univ := by
  rw [historyMarkedReferenceRaw_univ]
  let empty : HistoryShape (fun a b => ¬ dependent a b) := Quotient.mk _ []
  have he : ENNReal.ofReal (historyShapeReferenceWeight dependent Δ empty) = 1 := by
    simp [empty, historyShapeReferenceWeight, historyShapeLength_mk]
  rw [← he]
  exact ENNReal.le_tsum (f := fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g)) empty
end

end


theorem historyMarkedReferenceRaw_finite 
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) := by
  constructor
  rw [historyMarkedReferenceRaw_univ]
  exact (historyShapeReferenceWeight_summable dependent hrefl hsymm Δ hΔ hlabels).tsum_ofReal_lt_top

/-- The normalized actual infinite marked-history reference law `tau_0`. -/
def historyMarkedReference  (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) : Measure (HistoryMarked dependent E) :=
  (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹ • historyMarkedReferenceRaw dependent Δ π

theorem historyMarkedReference_probability 
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (historyMarkedReference dependent Δ π) := by
  let  :=
    historyMarkedReferenceRaw_finite dependent hrefl hsymm Δ hΔ hlabels π
  have hpos : historyMarkedReferenceRaw dependent Δ π Set.univ ≠ 0 := by
    have hh := historyMarkedReferenceRaw_univ_one_le dependent Δ π
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hh)
  
  constructor
  
  exact ENNReal.inv_mul_cancel hpos (measure_ne_top _ _)
end


end NearlyMinimax
