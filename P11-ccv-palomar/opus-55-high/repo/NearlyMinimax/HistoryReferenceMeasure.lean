module

public import NearlyMinimax.HistoryReferenceSum
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-!
# Actual marked-history reference probability measure

The countable shape law uses the source weight `rho^length`. Conditional on a
shape, all of its marks have the independent finite product law. The source
shape-count argument proves finiteness, and the empty shape proves nonzero
mass, so normalization constructs a probability measure without a finiteness
or positivity assumption on the desired law.
-/

𝚯
𝚨

𝚲

𝗇 𝔄 𝙁
𝗇 𝔅 HistoryShape 𝖴
𝗃 𝔔 ἀ dependent g
𝗇 𝔇 𝔔 historyShapeLength
abbrev HistoryMarked (dependent : 𝔄) (E : Type*) :=
  Σ g : 𝔅, Fin 𝔇 → E

𝗇 𝔊 𝙗
/-- Each canonical history fiber is measurably included in the marked-history space. -/
theorem historyMarked_measurable_mk (dependent : 𝔄)
    [MeasurableSpace E] g :
    Measurable fun marks => (𝗬 : 𝔊) := by
  apply Measurable.of_le_map
  exact iInf_le _ g

/-- A map on histories is measurable exactly when it is measurable on every shape fiber. -/
theorem historyMarked_measurable_iff (dependent : 𝔄)
    [MeasurableSpace E] [MeasurableSpace X] (f : 𝔊 → X) :
    Measurable f ↔ ∀ g, Measurable fun marks => f 𝗬 := by
  constructor
  · intro hf g
    exact hf.comp 𝔔 historyMarked_measurable_mk
  · intro hf s hs
    rw [MeasurableSpace.measurableSet_iInf]
    bound

𝗃 𝔓 ∀ i, ἀ $ X i
/-- A countable disjoint union of Borel fibers has exactly their sum sigma-algebra. -/
theorem historySigma_borelSpace {I : Type*} [Countable I] {X : 𝗀}
    [𝔓 TopologicalSpace] [𝔓 MeasurableSpace] [𝔓 BorelSpace] :
    BorelSpace $ Sigma X := by
  constructor
  apply le_antisymm
  · intro s hs
    let := borel $ Sigma X
    let : BorelSpace $ Sigma X := ⟨rfl⟩
    have hu : s = ⋃ i, Sigma.mk i '' Sigma.mk i ⁻¹' s := by
      ext x
      constructor
      · intro hx; exact Set.mem_iUnion.2 ⟨x.1, x.2, hx, rfl⟩
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨i, y, hy, rfl⟩
        exact hy
    rw [hu]
    exact MeasurableSet.iUnion fun i =>
      (Topology.IsClosedEmbedding.sigmaMk ).measurableEmbedding.measurableSet_image' $ (MeasurableSpace.measurableSet_iInf.1 hs) i
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    intro i
    exact (hs.preimage continuous_sigmaMk).measurableSet

/-- The chosen representative has exactly the intrinsic number of pieces. -/
theorem historyShapeLength_out (dependent : 𝔄)
    g :
    𝔇 = g.out.length := by
  have hh := congrArg (historyShapeLength dependent) $ Quotient.out_eq g
  rw [historyShapeLength_mk] at hh
  exact hh.symm

/-- Label evaluations in the canonical word of a shape. -/
def historyShapeCanonicalLabels (dependent : 𝔄)
    (g : 𝔅) : Fin 𝔇 → J :=
  fun i => g.out.get $ Fin.cast 𝔔 historyShapeLength_out i

𝗇 𝔈 ∀ j, Measurable fun ex : E × X => update j ex.1 ex.2
𝗇 𝔐 update (labels i) $ marks i
𝗇 𝔑 J → E → X → X
omit [Fintype J] [LinearOrder J] in
/-- Finite marked update recursion is measurable for measurable local updates. -/
theorem historyMarked_indexFold_measurable
    [MeasurableSpace E] [MeasurableSpace X] (update : 𝔑)
    (hu : 𝔈)
    (n : ℕ) (labels : Fin n → J) (indices : List $ Fin n )
    (f : 𝗚₁ → X) (hf : Measurable f) :
    Measurable fun marks => indices.foldl (fun state i => 𝔐 state) $ f marks := by
  induction indices generalizing f with
  | nil => exact hf
  | cons i indices ih =>
    exact ih (fun marks => 𝔐 $ f marks )
      $ (hu $ labels i ).comp $ (measurable_pi_apply i).prodMk hf

/-- The actual finite recursion on a canonical marked representative. -/
def historyMarkedRawState (dependent : 𝔄)
    (update : 𝔑) (initial : X) (h : 𝔊) : X :=
  (List.ofFn fun i : Fin $ historyShapeLength dependent h.1 => i ).foldl
    (fun state i => update (historyShapeCanonicalLabels dependent h.1 i) (h.2 i) state) initial

/-- No measurability of a desired law is assumed: it follows from the finite recursion. -/
theorem historyMarkedRawState_measurable (dependent : 𝔄)
    [MeasurableSpace E] [MeasurableSpace X] update
    (hu : 𝔈) initial :
    Measurable $ historyMarkedRawState dependent update initial := by
  rw [historyMarked_measurable_iff]
  intro g
  exact historyMarked_indexFold_measurable update hu 𝔇
    𝔔 historyShapeCanonicalLabels 𝘞₁
    (fun _ => initial) measurable_const

𝗇 𝔍 ENNReal.ofReal 𝘎₁
/-- The unnormalized source measure: countably many shapes, independently marked. -/
def historyMarkedReferenceRaw (dependent : 𝔄) (Δ : ℕ)
    [MeasurableSpace E] (π : Measure E) : Measure 𝔊 :=
  Measure.sum fun g => 𝔍 •
    Measure.map (Sigma.mk g) (Measure.pi fun _ : Fin 𝔇 => π)

𝗇 𝔒 𝚊₂
𝗇 𝔉 𝔒 Set.univ
theorem historyMarkedReferenceRaw_univ (dependent : 𝔄) (Δ : ℕ)
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    𝔉 =
      ∑' g, 𝔍 := by
  unfold historyMarkedReferenceRaw
  simp

/-- The empty shape contributes exactly one unit of raw reference mass. -/
theorem historyMarkedReferenceRaw_univ_one_le (dependent : 𝔄) (Δ : ℕ)
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    1 ≤ 𝔉 := by
  rw [historyMarkedReferenceRaw_univ]
  let empty : 𝔅 := Quotient.mk _ []
  have he : ENNReal.ofReal (historyShapeReferenceWeight dependent Δ empty) = 1 := by
    simp [empty, historyShapeReferenceWeight, historyShapeLength_mk]
  rw [← he]
  exact ENNReal.le_tsum (f := fun g => 𝔍) empty

𝗇 𝔎 𝘼
𝗇 𝔏 𝘽
theorem historyMarkedReferenceRaw_finite (dependent : 𝔄)
    (hrefl : 𝙂) (hsymm : 𝔎)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔏)
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsFiniteMeasure 𝔒 := by
  constructor
  rw [historyMarkedReferenceRaw_univ]
  exact (historyShapeReferenceWeight_summable dependent hrefl hsymm Δ hΔ hlabels).tsum_ofReal_lt_top

/-- The normalized actual infinite marked-history reference law `tau_0`. -/
def historyMarkedReference (dependent : 𝔄) (Δ : ℕ)
    [MeasurableSpace E] (π : Measure E) : Measure 𝔊 :=
  𝔉⁻¹ • 𝔒

theorem historyMarkedReference_probability (dependent : 𝔄)
    (hrefl : 𝙂) (hsymm : 𝔎)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔏)
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsProbabilityMeasure 𝙤 := by
  let :=
    historyMarkedReferenceRaw_finite dependent hrefl hsymm Δ hΔ hlabels π
  have hpos : 𝔉 ≠ 0 := by
    have hh := historyMarkedReferenceRaw_univ_one_le dependent Δ π
    positivity
  constructor
  exact ENNReal.inv_mul_cancel hpos 𝚃₁
