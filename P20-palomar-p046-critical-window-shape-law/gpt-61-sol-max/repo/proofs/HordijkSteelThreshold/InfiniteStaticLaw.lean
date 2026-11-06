
import proofs.HordijkSteelThreshold.ReversibleMeasurableEvents
import proofs.HordijkSteelThreshold.WordContourProbability
import proofs.HordijkSteelThreshold.WordEffectiveClosure




namespace HordijkSteelThreshold
open MeasureTheory RAF.Polymer RAF.Concrete unitInterval

noncomputable def literalSplitCoordinate {N : ℕ} (r : Reaction N)  :=
  (moleculeWord (reactionProduct r), reactionLeftLength r)

variable (N : ℕ)

theorem literalSplitCoordinate_injective  : Function.Injective (@literalSplitCoordinate N) := by
  intro r s he
  have hp := moleculeWord_injective (congrArg Prod.fst he)
  have hk := congrArg Prod.snd he
  simp only [literalSplitCoordinate, reactionProduct, reactionLeftLength] at hp hk
  measurability

def currySplitField (ω : (List Bool × ℕ) → Prop) : InfiniteSplitEnvironment :=
  fun w k => ω (w,k)

theorem measurable_currySplitField : Measurable currySplitField := by
  unfold currySplitField
  fun_prop

variable (a : I)

noncomputable def infiniteSplitPi  : Measure ((List Bool × ℕ) → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw a)

noncomputable def infiniteStaticMeasure : Measure InfiniteSplitEnvironment :=
  (infiniteSplitPi a).map currySplitField

noncomputable instance infiniteSplitPi_probability  : IsProbabilityMeasure (infiniteSplitPi a) := by
  unfold infiniteSplitPi
  infer_instance

noncomputable instance infiniteStaticMeasure_probability  : IsProbabilityMeasure (infiniteStaticMeasure a) := by
  unfold infiniteStaticMeasure
  infer_instance

/-- The infinite iid environment restricts to the exact finite static source
law, with each product/split pair a distinct coordinate. -/
theorem infiniteStatic_restriction_map   :
    (infiniteStaticMeasure a).map
      (fun field r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r)) =
      staticReactionMeasure N a := by
  rw [infiniteStaticMeasure, Measure.map_map (by fun_prop) measurable_currySplitField]
  exact (Measure.map_infinitePi_infinitePi_of_inj (literalSplitCoordinate_injective N)).trans
    (Measure.infinitePi_eq_pi _)


end HordijkSteelThreshold
