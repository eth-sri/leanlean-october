module

public import proofs.HordijkSteelThreshold.ReversibleMeasurableEvents
public import proofs.HordijkSteelThreshold.WordContourProbability
public import proofs.HordijkSteelThreshold.WordEffectiveClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval

noncomputable def literalSplitCoordinate {N : ℕ} (r : Reaction N) : List Bool × ℕ :=
  (moleculeWord $ reactionProduct r, reactionLeftLength r)

theorem literalSplitCoordinate_injective (N : ℕ) : Function.Injective (@literalSplitCoordinate N) := by
  intro r s he
  have hp := moleculeWord_injective $ congrArg Prod.fst he
  have hk := congrArg Prod.snd he
  rcases r with ⟨kr, cr, sr⟩
  rcases s with ⟨ks, cs, ss⟩
  have hidx : kr = ks := congrArg Sigma.fst hp
  subst ks
  have hc : cr = cs := by
    have h := congrArg (fun x : Molecule N => x.2.val) hp
    aesop
  have hs : sr = ss := Fin.ext $ by change sr.val + 1 = ss.val + 1 at hk; omega
  simp_all

def currySplitField (ω : (List Bool × ℕ) → Prop) : InfiniteSplitEnvironment :=
  fun w k => ω (w,k)

theorem measurable_currySplitField : Measurable currySplitField := by
  unfold currySplitField; fun_prop

variable (a : I)

noncomputable def infiniteSplitPi  : Measure ((List Bool × ℕ) → Prop) :=
  Measure.infinitePi $ fun _ => ambientCoordLaw a

noncomputable def infiniteStaticMeasure  : Measure InfiniteSplitEnvironment :=
  (infiniteSplitPi a).map currySplitField

noncomputable instance infiniteSplitPi_probability  : IsProbabilityMeasure (infiniteSplitPi a) := by
  unfold infiniteSplitPi
  infer_instance

noncomputable instance infiniteStaticMeasure_probability  : IsProbabilityMeasure (infiniteStaticMeasure a) := by
  unfold infiniteStaticMeasure
  infer_instance

end HordijkSteelThreshold
