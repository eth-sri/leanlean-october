module

public import PottsDiscontinuity.Potts.CylinderColoring
public import PottsDiscontinuity.Potts.LimitCompactness
public import PottsDiscontinuity.Potts.ObservedPartitionLimits
public import PottsDiscontinuity.PottsThm.ColoringFactor

public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite
open scoped ENNReal

noncomputable section

/-- An iid field assigns independent coordinate values at any finite family
of distinct sites. -/
theorem iidFieldMeasure_injective_cylinder {A C : Type*} [Fintype A]
    [DecidableEq A] [MeasurableSpace C] [MeasurableSingletonClass C]
    [Finite C] [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (v : A → Vertex) (hv : Function.Injective v) (ξ : A → C) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (v a) = ξ a} =
      ∏ a : A, ν {ξ a} := by
  let S := Finset.univ.image v
  let rep (y : ↥S) := Classical.choose (Finset.mem_image.mp y.2)
  let t := fun y => if hy : y ∈ S then {ξ (rep ⟨y, hy⟩)} else Set.univ
  have hevent : {u : Vertex → C | ∀ a, u (v a) = ξ a} = Set.pi S t := by
    grind
  rw [hevent]
  refine (Measure.infinitePi_pi (μ := fun _ : Vertex => ν) fun y hy => by simp [t, hy]).trans ?_
  rw [Finset.prod_image hv.injOn]
  exact Finset.prod_congr rfl fun a _ => congrArg ν (by grind)

section
variable {A C : Type*} [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C] [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν] (R : Setoid A)
/-- Conditional cylinder probability for coordinates indexed by the classes of
a finite observed relation, represented by distinct lattice sites. -/
theorem iidFieldMeasure_observedColoring_of_compatible [Fintype (Quotient R)] (rep : A → Vertex)
    (hrep : ∀ a b, R a b ↔ rep a = rep b) (ξ : A → C)
    (hξ : R ≤ Setoid.ker ξ) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (rep a) = ξ a} =
      ∏ c : Quotient R, ν {ξ (Classical.choose (Quotient.exists_rep c))} := by
  classical
  let repQ := Quotient.lift rep fun a b hab => (hrep a b).mp hab
  let ξQ := Quotient.lift ξ fun a b hab => hξ hab
  have hset : {u : Vertex → C | ∀ a, u (rep a) = ξ a} = {u | ∀ c, u (repQ c) = ξQ c} :=
    Set.ext fun u => ⟨fun h c => Quotient.inductionOn c h, fun h a => h ⟦a⟧⟩
  rw [hset, iidFieldMeasure_injective_cylinder ν repQ (fun x y hxy => Quotient.inductionOn₂ x y
    (fun a b h => Quotient.sound ((hrep a b).2 h)) hxy) ξQ]
  refine Finset.prod_congr rfl fun c _ => ?_
  conv_lhs => rw [← Classical.choose_spec (Quotient.exists_rep c)]
  rfl

/-- An incompatible observed pattern has zero iid coloring probability. -/
theorem iidFieldMeasure_observedColoring_of_incompatible (rep : A → Vertex)
    (hrep : ∀ a b, R a b ↔ rep a = rep b) (ξ : A → C)
    (hξ : ¬ R ≤ Setoid.ker ξ) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (rep a) = ξ a} = 0 := by
  obtain ⟨a, b, hab, hcolors⟩ : ∃ a b, R a b ∧ ξ a ≠ ξ b := by
    by_contra h
    exact hξ fun a b hab => by aesop
  rw [show {u : Vertex → C | ∀ a, u (rep a) = ξ a} = ∅ by grind, measure_empty]
end

section
variable (q : ℕ)
theorem pottsUniformColor_singleton (c : Set.Icc 1 q) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)) {c} =
      (q : ℝ≥0∞)⁻¹ := by
  simpa using ProbabilityTheory.uniformOn_apply_finset (s := Finset.univ) (t := {c})

/-- For a fixed free bond configuration with finite clusters, the iid
representative coloring has the free Edwards--Sokal cylinder kernel. -/
theorem freeClusterColoring_fiber_cylinder_uniform (hq : 0 < q)
    (ω : LatticeConfiguration) (A : Finset Vertex) (ξ : SpinSpace q)
    [Fintype (Quotient (infiniteFreePartition (fun a : ↥A => a.val) ω))]
    (hfinite : ∀ x, (cluster ω x).Finite) :
    iidFieldMeasure (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)))
      {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
        clusterColoring ⟨1, le_rfl, by omega⟩ (ω, u) a.val = ξ a.val} =
      ENNReal.ofReal (clusterCylinderProbability
        (infiniteFreePartition (fun a : ↥A => a.val) ω) id
        (fun a : ↥A => ξ a.val)) := by
  let R := infiniteFreePartition (fun a : ↥A => a.val) ω
  have : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, hq⟩⟩
  have hrepExists (a : ↥A) := Option.ne_none_iff_exists'.1
    ((clusterRepresentative_none_iff ω a.val).not.2 (not_not.2 (hfinite a)))
  let repA a := Classical.choose (hrepExists a)
  have hrepA a : clusterRepresentative ω a.val = some (repA a) := Classical.choose_spec (hrepExists a)
  have hrep (a b : ↥A) : R a b ↔ repA a = repA b :=
    (clusterRepresentative_eq_iff_reachable ω a.val b.val (hfinite a.val) (hfinite b.val)).symm.trans (by grind)
  rw [show {u : Vertex → Set.Icc 1 q | ∀ a : ↥A, clusterColoring ⟨1, le_rfl, by omega⟩ (ω, u) a.val = ξ a.val} =
      {u | ∀ a : ↥A, u (repA a) = ξ a.val} by simp [clusterColoring, hrepA]]
  by_cases hcompat : R ≤ Setoid.ker (fun a : ↥A => ξ a.val)
  · rw [iidFieldMeasure_observedColoring_of_compatible _ R repA hrep _ hcompat]
    simp_rw [pottsUniformColor_singleton]
    simp [clusterCylinderProbability, Setoid.comap_id, R, hcompat]
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.inv_pow]
    simp
    exact congrArg _ Nat.card_eq_fintype_card.symm
  · rw [iidFieldMeasure_observedColoring_of_incompatible _ R repA hrep _ hcompat]
    simp [clusterCylinderProbability, Setoid.comap_id, R, hcompat]
end

/-- A pinned quotient coloring has independent iid colors on every observed
class except the distinguished class represented by `none`. -/
theorem iidFieldMeasure_pinnedObservedColoring_of_compatible
    {A C : Type*} [Fintype A] [MeasurableSpace C] [MeasurableSingletonClass C]
    [Finite C] [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (R : Setoid (Option A)) [Fintype (Quotient R)]
    [Fintype {c : Quotient R // c ≠ Quotient.mk R none}]
    (rep : Option A → Option Vertex)
    (hrep : ∀ a b, R a b ↔ rep a = rep b)
    (hrepGhost : rep none = none) (c₀ : C) (ξ : Option A → C)
    (hξGhost : ξ none = c₀) (hcompat : R ≤ Setoid.ker ξ) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a : Option A,
      (rep a).elim c₀ u = ξ a} =
      ∏ c : {c : Quotient R // c ≠ Quotient.mk R none},
        ν {ξ (Classical.choose (Quotient.exists_rep c.val))} := by
  classical
  let repQ := Quotient.lift rep fun a b hab => (hrep a b).mp hab
  let ξQ := Quotient.lift ξ fun a b hab => hcompat hab
  have hrepQ (a : Option A) : repQ (Quotient.mk R a) = rep a := rfl
  have hξQ (a : Option A) : ξQ (Quotient.mk R a) = ξ a := rfl
  have hinj : Function.Injective repQ := fun x y => Quotient.inductionOn₂ x y fun a b h => Quotient.sound ((hrep a b).2 h)
  have hrepExists (c : {c : Quotient R // c ≠ Quotient.mk R none}) : ∃ v, repQ c.val = some v :=
    Option.ne_none_iff_exists'.1 fun h => c.2 (by grind)
  let repNz c := Classical.choose (hrepExists c)
  have hrepNz c : repQ c.val = some (repNz c) := Classical.choose_spec (hrepExists c)
  have heventNz : {u : Vertex → C | ∀ a : Option A, (rep a).elim c₀ u = ξ a} =
      {u | ∀ c, u (repNz c) = ξQ c.val} := by
    ext u
    constructor
    · intro hu c
      obtain ⟨a, ha⟩ := Quotient.exists_rep c.val
      grind
    · intro hu a
      by_cases hc : Quotient.mk R a = Quotient.mk R none
      · grind
      · rw [← hrepQ, hrepNz ⟨_, hc⟩]
        exact hu ⟨_, hc⟩
  rw [heventNz, iidFieldMeasure_injective_cylinder ν repNz (fun c d hcd => by grind) fun c => ξQ c.val]
  refine Finset.prod_congr rfl fun c _ => ?_
  conv_lhs => rw [← Classical.choose_spec (Quotient.exists_rep c.val)]
  rfl

/-- The representative of an observed wired class is the ghost point for the
distinguished class and the lexicographic representative otherwise. -/
def wiredObservedRepresentative {A : Type*} (ω : LatticeConfiguration)
    (v : A → Vertex) (a : Option A) : Option Vertex :=
  a.elim none (fun x => clusterRepresentative ω (v x))

theorem rcCluster_eq_of_reachable (ω : LatticeConfiguration) {x y : Vertex}
    (hxy : (rcInfiniteOpenGraph ω).Reachable x y) :
    RCInfinite.cluster ω x = RCInfinite.cluster ω y :=
  Set.ext fun _ => ⟨hxy.symm.trans, hxy.trans⟩

theorem wiredObservedRepresentative_eq_iff {A : Type*} [Fintype A]
    (ω : LatticeConfiguration) (v : A → Vertex) (a b : Option A) :
    infiniteWiredPartition (Option.map v) ω a b ↔
      wiredObservedRepresentative ω v a = wiredObservedRepresentative ω v b := by
  have hi (x) : clusterIsInfinite (rcInfiniteOpenGraph ω) x ↔ clusterRepresentative ω x = none :=
    (clusterRepresentative_none_iff ω x).symm
  rcases a with _ | a <;> rcases b with _ | b
  · simp [wiredObservedRepresentative]
  · change infiniteMergedSetoid _ none (some (v b)) ↔ none = clusterRepresentative ω (v b)
    rw [Setoid.comm', infiniteMergedSetoid_some_none, hi, eq_comm]
  · exact (infiniteMergedSetoid_some_none _ _).trans (hi _)
  change infiniteMergedSetoid _ (some (v a)) (some (v b)) ↔
    clusterRepresentative ω (v a) = clusterRepresentative ω (v b)
  have ha := clusterRepresentative_none_iff ω (v a)
  have hb := clusterRepresentative_none_iff ω (v b)
  rw [infiniteMergedSetoid_some_some, hi, hi]
  by_cases hfa : (RCInfinite.cluster ω (v a)).Finite <;> by_cases hfb : (RCInfinite.cluster ω (v b)).Finite
  · rw [clusterRepresentative_eq_iff_reachable ω _ _ hfa hfb, ha]
    simp [Set.not_infinite.2 hfa]
  · have : ¬ (rcInfiniteOpenGraph ω).Reachable (v a) (v b) := fun h => hfb (by rwa [← rcCluster_eq_of_reachable ω h])
    simp [this, hb.2 hfb, ha.not.2 (not_not.2 hfa)]
  · have : ¬ (rcInfiniteOpenGraph ω).Reachable (v a) (v b) := fun h => hfa (by rwa [rcCluster_eq_of_reachable ω h])
    simp [this, ha.2 hfa, eq_comm]
  · simp [ha.2 hfa, hb.2 hfb]

/-- For a fixed wired configuration, canonical coloring by iid colors on
finite clusters and the boundary color on all infinite clusters has the
pinned Edwards--Sokal cylinder probability. -/
theorem wiredClusterColoring_fiber_cylinder_uniform (q : ℕ) (hq : 0 < q)
    (ω : LatticeConfiguration) (A : Finset Vertex) (ξ : SpinSpace q)
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) :
    iidFieldMeasure (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)))
      {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
        clusterColoring (boundaryColor q i hi) (ω, u) a.val = ξ a.val} =
      ENNReal.ofReal (pinnedClusterCylinderProbability
        (infiniteWiredPartition (Option.map (fun a : ↥A => a.val)) ω)
        some (fun a : ↥A => ξ a.val) none (boundaryColor q i hi)) := by
  classical
  set c₀ := boundaryColor q i hi
  set R := infiniteWiredPartition (Option.map fun a : ↥A => a.val) ω
  let rep := wiredObservedRepresentative ω fun a : ↥A => a.val
  set ξ' := markedMap (fun a : ↥A => ξ a.val) c₀
  have : Nonempty (Set.Icc 1 q) := ⟨c₀⟩
  have hrep : ∀ a b, R a b ↔ rep a = rep b := wiredObservedRepresentative_eq_iff ω _
  have hcomap : R.comap (markedMap some none) = R := Setoid.ext fun a b => by cases a <;> cases b <;> rfl
  rw [show {u : Vertex → Set.Icc 1 q | ∀ a : ↥A, clusterColoring c₀ (ω, u) a.val = ξ a.val} =
      {u | ∀ a, (rep a).elim c₀ u = ξ' a} by
    ext u; simp [Option.forall, rep, ξ', wiredObservedRepresentative, clusterColoring, markedMap]]
  unfold pinnedClusterCylinderProbability
  rw [hcomap]
  by_cases hcompat : R ≤ Setoid.ker ξ'
  · rw [iidFieldMeasure_pinnedObservedColoring_of_compatible _ R rep hrep rfl c₀ ξ' rfl hcompat, if_pos hcompat,
      observedClassCount, hcomap]
    simp_rw [pottsUniformColor_singleton]
    simp
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast,
      ENNReal.inv_pow]
  · rw [if_neg hcompat, ENNReal.ofReal_zero]
    exact measure_mono_null (fun u (hu : ∀ a, _) => (hcompat fun a b hab =>
      (hu a).symm.trans ((congrArg (·.elim c₀ u) ((hrep a b).1 hab)).trans (hu b))).elim) measure_empty

section
variable {Ω A : Type*} [MeasurableSpace Ω]
/-- Integrating a finite partition kernel over the first factor gives its
finite weighted sum. -/
theorem lintegral_finitePartitionKernel [Fintype A] [Fintype (Setoid A)] (μ : Measure Ω)
    (r : Ω → Setoid A) (K : Setoid A → ℝ≥0∞)
    (hr : ∀ R, MeasurableSet {ω | r ω = R}) :
    ∫⁻ ω, K (r ω) ∂μ =
      ∑ R : Setoid A, K R * μ {ω | r ω = R} := by
  classical
  simp_rw [← lintegral_indicator_const (hr _)]
  rw [← lintegral_finsetSum _ fun R _ => measurable_const.indicator (hr R)]
  simp [Set.indicator]

theorem toReal_lintegral_finitePartitionKernel [Finite A] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Setoid A) (K : Setoid A → ℝ)
    (hK : ∀ R, 0 ≤ K R)
    (hr : ∀ R, MeasurableSet {ω | r ω = R}) :
    (∫⁻ ω, ENNReal.ofReal (K (r ω)) ∂μ).toReal =
      PottsDiscontinuity.Potts.partitionExpectation μ r K := by
  let  := Fintype.ofFinite A
  let  := Fintype.ofFinite (Setoid A)
  rw [lintegral_finitePartitionKernel μ r (fun R => ENNReal.ofReal (K R)) hr, ENNReal.toReal_sum fun R _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)]
  exact Finset.sum_congr rfl fun R _ => by simp [hK, mul_comm, Measure.real]
end

end
end PottsDiscontinuity.PottsThm
