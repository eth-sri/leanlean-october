module

public import proofs.HordijkSteelThreshold.ReversibleMeasurableEvents
public import proofs.HordijkSteelThreshold.WordContourProbability
public import proofs.HordijkSteelThreshold.WordEffectiveClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval

noncomputable def literalSplitCoordinate {N : ℕ} (r : Reaction N) : List Bool × ℕ :=
  (moleculeWord (reactionProduct r), reactionLeftLength r)

theorem literalSplitCoordinate_injective (N : ℕ) : Function.Injective (@literalSplitCoordinate N) := by
  rintro ⟨kr, cr, sr⟩ ⟨ks, cs, ss⟩ he
  have hp : (⟨kr, cr⟩ : Molecule N) = ⟨ks, cs⟩ := moleculeWord_injective (congrArg Prod.fst he)
  have hk := congrArg Prod.snd he
  cases hp
  cases Fin.ext (Nat.succ.inj hk)
  rfl

def currySplitField (ω : (List Bool × ℕ) → Prop) : InfiniteSplitEnvironment :=
  fun w k => ω (w,k)

theorem measurable_currySplitField : Measurable currySplitField :=
  Measurable.of_eval fun w => Measurable.of_eval fun k => measurable_pi_apply (w, k)

noncomputable def infiniteSplitPi (a : I) : Measure ((List Bool × ℕ) → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw a)

noncomputable def infiniteStaticMeasure (a : I) : Measure InfiniteSplitEnvironment :=
  (infiniteSplitPi a).map currySplitField

noncomputable instance infiniteSplitPi_probability (a : I) : IsProbabilityMeasure (infiniteSplitPi a) := by
  unfold infiniteSplitPi; infer_instance

noncomputable instance infiniteStaticMeasure_probability (a : I) : IsProbabilityMeasure (infiniteStaticMeasure a) := by
  unfold infiniteStaticMeasure; infer_instance

theorem infiniteStatic_restriction_map (N : ℕ) (a : I) :
    (infiniteStaticMeasure a).map
      (fun field r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r)) =
      staticReactionMeasure N a := by
  have hi : iIndepFun (fun z (ω : (List Bool × ℕ) → Prop) => ω z) (infiniteSplitPi a) :=
    iIndepFun_infinitePi fun _ => measurable_id
  rw [infiniteStaticMeasure, Measure.map_map (measurable_splitRestriction N) measurable_currySplitField]
  change (infiniteSplitPi a).map (fun ω r => ω (literalSplitCoordinate r)) = _
  rw [(hi.precomp (literalSplitCoordinate_injective N)).map_fun_eq_pi_map
    fun r => (measurable_pi_apply (literalSplitCoordinate r)).aemeasurable]
  simp_rw [infiniteSplitPi, Measure.infinitePi_map_eval]
  exact (Measure.infinitePi_eq_pi _).symm

theorem finite_static_seed_probability_tendsto (L : ℕ) (a : I) (seed : Finset (List Bool)) :
    Filter.Tendsto (fun N => staticReactionMeasure N a {ω | ∀ w ∈ seed,
      ∃ x ∈ temporaryReactionClosure L (staticOpenReactions ω), moleculeWord x = w})
      Filter.atTop (nhds (infiniteStaticMeasure a
        {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w})) := by
  have he (N : ℕ) : staticReactionMeasure N a {ω | ∀ w ∈ seed,
      ∃ x ∈ temporaryReactionClosure L (staticOpenReactions ω), moleculeWord x = w} =
    infiniteStaticMeasure a {field | ∀ w ∈ seed, FiniteReversibleGenerated N L field w} := by
    rw [← infiniteStatic_restriction_map N a,
      Measure.map_apply (measurable_splitRestriction N) (Set.toFinite _).measurableSet]
    congr 1; ext field
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, finiteReversible_iff_literalClosure]
    rfl
  simp_rw [he]
  exact finite_seed_probability_tendsto (infiniteStaticMeasure a) L seed

end HordijkSteelThreshold
