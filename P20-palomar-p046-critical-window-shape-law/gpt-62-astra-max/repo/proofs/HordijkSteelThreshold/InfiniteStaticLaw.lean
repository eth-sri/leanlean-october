module
public import proofs.HordijkSteelThreshold.ReversibleClosureDock
public import proofs.HordijkSteelThreshold.AmbientIndependence

/-! Infinite iid field and finite prefix cylinders. -/

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval

def literalSplitCoordinate {N : ℕ} (r : Reaction N) : List Bool × ℕ :=
  (moleculeWord (reactionProduct r), reactionLeftLength r)

theorem literalSplitCoordinate_injective (N : ℕ) : Function.Injective (@literalSplitCoordinate N) := by
  rintro ⟨i,u,k⟩ ⟨j,v,l⟩ he
  have hp := moleculeWord_injective (congrArg Prod.fst he)
  change (⟨i,u⟩ : Molecule N) = ⟨j,v⟩ at hp
  cases hp
  have e := congrArg Prod.snd he
  change k.val+1 = l.val+1 at e
  grind [Fin.ext_iff]

def currySplitField (ω : (List Bool × ℕ) → Prop) : InfiniteSplitEnvironment :=
  fun w k => ω (w,k)

theorem measurable_currySplitField : Measurable currySplitField := by
  unfold currySplitField; fun_prop

variable (a : I)
noncomputable def infiniteSplitPi : Measure ((List Bool × ℕ) → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw a)

noncomputable def infiniteStaticMeasure : Measure InfiniteSplitEnvironment :=
  (infiniteSplitPi a).map currySplitField

noncomputable instance infiniteSplitPi_probability : IsProbabilityMeasure (infiniteSplitPi a) := by
  unfold infiniteSplitPi
  infer_instance

noncomputable instance infiniteStaticMeasure_probability : IsProbabilityMeasure (infiniteStaticMeasure a) := by
  exact (Measure.isProbabilityMeasure_map_iff measurable_currySplitField.aemeasurable).2 inferInstance


noncomputable def staticSurvival : ENNReal :=
  infiniteStaticMeasure a {field | ReversibleUnbounded 2 field}


abbrev SplitField := (List Bool × ℕ) → Prop

abbrev Coord := List Bool × ℕ
abbrev past (n : ℕ) := {z : Coord | z.1.length ≤ n}

/-- Information carried by a set of coordinates. -/
noncomputable abbrev observed (S : Set Coord) := ⨆ z ∈ S, MeasurableSpace.comap (fun ω : SplitField => ω z) inferInstance

lemma observed_read {S : Set Coord} {J : Type*} (f : J → Coord) (h : ∀ j, f j ∈ S) :
    Measurable[observed S] fun (ω : SplitField) j => ω (f j) := by
  let _ := observed S
  exact Measurable.of_eval fun j => Measurable.of_comap_le (le_iSup₂_of_le _ (h j) le_rfl)

lemma observed_le (S : Set Coord) : observed S ≤ MeasurableSpace.pi := iSup₂_le fun z _ => (measurable_pi_apply z).comap_le

lemma fresh_law {P : Set Coord} {T : Finset Coord} (hd : Disjoint P T) {E} (hE : MeasurableSet[observed P] E) (D : Set (T → Prop)) :
    infiniteSplitPi a (E ∩ T.restrict ⁻¹' D) = infiniteSplitPi a E * RAFEmergenceApprox.Generic.colLaw T a D := by
  have hi : iIndepFun (fun i (ω : SplitField) => ω i) (infiniteSplitPi a) := iIndepFun_infinitePi fun _ => measurable_id
  have ind := indep_iSup_of_disjoint (fun z => (measurable_pi_apply z).comap_le) hi hd
  rw [←(iid_read a Subtype.val (@Subtype.val_injective _ (· ∈ T))).finite_event D]
  exact (Indep_iff _ _ _).mp ind E _ hE (observed_read _ (fun j : T => j.property) (Set.toFinite D).measurableSet)

end HordijkSteelThreshold
