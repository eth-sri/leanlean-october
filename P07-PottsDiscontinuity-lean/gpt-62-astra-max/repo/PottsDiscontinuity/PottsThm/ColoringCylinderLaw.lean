module

public import PottsDiscontinuity.Potts.CylinderColoring
public import PottsDiscontinuity.Potts.SpinCylinder
public import PottsDiscontinuity.Potts.ObservedPartitionLimits
public import PottsDiscontinuity.PottsThm.ColoringFactor

@[expose] public section

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
      ∏ a, ν {ξ a} := by
  classical
  let S := Finset.univ.image v
  let rep (y : ↥S) := Classical.choose (Finset.mem_image.mp y.2)
  let t := fun y => if hy : y ∈ S then {ξ (rep ⟨y, hy⟩)} else Set.univ
  have hevent : {u : Vertex → C | ∀ a, u (v a) = ξ a} = Set.pi S t := by
    grind
  rw [hevent]
  have hpi : Measure.infinitePi (fun _ : Vertex => ν) (Set.pi S t) =
      ∏ y ∈ S, ν (t y) := by
    apply Measure.infinitePi_pi
    intro y hy
    simp [t, hy]
  rw [hpi, Finset.prod_image hv.injOn]
  grind

/-- Distinct iid coordinates attached to the classes of a finite observed
partition have the ordinary product law. -/
theorem iidFieldMeasure_quotient_cylinder {A C : Type*} [Fintype A]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (R : Setoid A) [Fintype (Quotient R)]
    (v : Quotient R → Vertex) (hv : Function.Injective v)
    (ξ : Quotient R → C) :
    iidFieldMeasure ν
        {u : Vertex → C | ∀ a, u (v (Quotient.mk R a)) = ξ (Quotient.mk R a)} =
      ∏ c, ν {ξ c} := by
  classical
  have hset : {u : Vertex → C |
      ∀ a, u (v (Quotient.mk R a)) = ξ (Quotient.mk R a)} =
      {u : Vertex → C | ∀ c : Quotient R, u (v c) = ξ c} := by
    ext u
    constructor
    · intro h c
      obtain ⟨a, rfl⟩ := Quotient.exists_rep c
      exact h a
    · grind
  rw [hset]
  exact iidFieldMeasure_injective_cylinder ν v hv ξ

/-- Conditional cylinder probability for coordinates indexed by the classes of
a finite observed relation, represented by distinct lattice sites. -/
theorem iidFieldMeasure_observedColoring_of_compatible {A C : Type*} [Fintype A]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (R : Setoid A) [Fintype (Quotient R)] (rep : A → Vertex)
    (hrep : ∀ a b, R a b ↔ rep a = rep b) {ξ : A → C}
    (hξ : R ≤ Setoid.ker ξ) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (rep a) = ξ a} =
      ∏ c : Quotient R, ν {ξ (Classical.choose (Quotient.exists_rep c))} := by
  classical
  let repQ := Quotient.lift rep (fun a b hab => (hrep a b).mp hab)
  have hrepQ (a : A) : repQ (Quotient.mk R a) = rep a := rfl
  let ξQ := Quotient.lift ξ (fun a b hab => hξ hab)
  have hξQ (a : A) : ξQ (Quotient.mk R a) = ξ a := rfl
  have hset : {u : Vertex → C | ∀ a, u (rep a) = ξ a} =
      {u : Vertex → C | ∀ c : Quotient R, u (repQ c) = ξQ c} := by
    ext u
    constructor
    · intro h c
      obtain ⟨a, rfl⟩ := Quotient.exists_rep c
      grind
    · grind
  have hprob := iidFieldMeasure_quotient_cylinder ν R repQ (by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    apply Quotient.sound
    simp_all) ξQ
  grind

/-- An incompatible observed pattern has zero iid coloring probability. -/
theorem iidFieldMeasure_observedColoring_of_incompatible {A C : Type*} [Fintype A]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (R : Setoid A) (rep : A → Vertex)
    (hrep : ∀ a b, R a b ↔ rep a = rep b) {ξ : A → C}
    (hξ : ¬ R ≤ Setoid.ker ξ) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (rep a) = ξ a} = 0 := by
  classical
  obtain ⟨a, b, hab, hcolors⟩ : ∃ a b, R a b ∧ ξ a ≠ ξ b := by
    by_contra h
    apply hξ
    intro a b hab
    by_contra hne
    exact h ⟨a, b, hab, hne⟩
  have hempty : {u : Vertex → C | ∀ a, u (rep a) = ξ a} = ∅ := by
    grind
  simp_all

theorem pottsUniformColor_singleton (q : ℕ)
    (c : Set.Icc 1 q) :
    ProbabilityTheory.uniformOn Set.univ {c} =
      (q : ℝ≥0∞)⁻¹ := by
  classical
  simpa using (ProbabilityTheory.uniformOn_apply_finset (s := Finset.univ) (t := {c}))

/-- For a fixed free bond configuration with finite clusters, the iid
representative coloring has the free Edwards--Sokal cylinder kernel. -/
theorem freeClusterColoring_fiber_cylinder_uniform (q : ℕ) (hq : 0 < q)
    (ω : LatticeConfiguration) (A : Finset Vertex) (ξ : SpinSpace q)
    [Fintype (Quotient (infiniteFreePartition (fun a : ↥A => a.val) ω))]
    (hfinite : ∀ x, (cluster ω x).Finite) :
    iidFieldMeasure (ProbabilityTheory.uniformOn Set.univ)
      {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
        clusterColoring ⟨1, le_rfl, by omega⟩ (ω, u) a.val = ξ a.val} =
      ENNReal.ofReal (clusterCylinderProbability
        (infiniteFreePartition (fun a : ↥A => a.val) ω) id
        (fun a : ↥A => ξ a.val)) := by
  classical
  let R := infiniteFreePartition (fun a : ↥A => a.val) ω
  let : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have hrepExists (a : ↥A) : ∃ y, clusterRepresentative ω a.val = some y := by
    simp [clusterRepresentative, hfinite a.val]
  let repA (a : ↥A) := Classical.choose (hrepExists a)
  have hrepA (a : ↥A) : clusterRepresentative ω a.val = some (repA a) :=
    Classical.choose_spec (hrepExists a)
  have hrep (a b : ↥A) : R a b ↔ repA a = repA b := (clusterRepresentative_eq_iff_reachable ω
      (hfinite a.val) (hfinite b.val)).symm.trans (by simp [hrepA])
  have hset : {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
      clusterColoring ⟨1, le_rfl, by omega⟩ (ω, u) a.val = ξ a.val} =
      {u : Vertex → Set.Icc 1 q | ∀ a : ↥A, u (repA a) = ξ a.val} := by
    ext u
    simp [clusterColoring, hrepA]
  rw [hset]
  by_cases hcompat : R ≤ Setoid.ker (fun a : ↥A => ξ a.val)
  · rw [iidFieldMeasure_observedColoring_of_compatible
      (ProbabilityTheory.uniformOn Set.univ) R repA hrep hcompat]
    have hatom (c : Set.Icc 1 q) := pottsUniformColor_singleton q c
    simp_rw [hatom]
    rw [Finset.prod_const]
    have hcount : observedClassCount R id = Nat.card (Quotient R) := rfl
    unfold PottsDiscontinuity.Potts.clusterCylinderProbability
    rw [ite_eq_left (by exact hcompat), hcount,
      PottsDiscontinuity.Potts.card_pottsColors]
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
    rw [ENNReal.ofReal_inv_of_pos (pow_pos hqreal _), ENNReal.ofReal_pow hqreal.le, ENNReal.ofReal_natCast]
    exact ENNReal.inv_pow.symm
  · rw [iidFieldMeasure_observedColoring_of_incompatible
      (ProbabilityTheory.uniformOn Set.univ) R repA hrep hcompat]
    simp [PottsDiscontinuity.Potts.clusterCylinderProbability,
      Setoid.comap_id, R, hcompat]

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
  let Q := Quotient R
  let ghost := Quotient.mk R none
  let repQ := Quotient.lift rep
    (fun a b hab => (hrep a b).mp hab)
  have hrepQ (a : Option A) : repQ (Quotient.mk R a) = rep a := rfl
  have hinj : Function.Injective repQ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    apply Quotient.sound
    simp_all
  let ξQ := Quotient.lift ξ (fun a b hab => hcompat hab)
  have hξQ (a : Option A) : ξQ (Quotient.mk R a) = ξ a := rfl
  let Qnz := {c : Q // c ≠ ghost}
  have hrepExists (c : Qnz) : ∃ v, repQ c.val = some v := by
    cases h : repQ c.val with
    | none =>
      grind
    | some v => grind
  let repNz (c : Qnz) := Classical.choose (hrepExists c)
  have hrepNz (c : Qnz) : repQ c.val = some (repNz c) :=
    Classical.choose_spec (hrepExists c)
  have heventQ : {u : Vertex → C | ∀ a : Option A,
      (rep a).elim c₀ u = ξ a} =
      {u : Vertex → C | ∀ c : Q, (repQ c).elim c₀ u = ξQ c} := by
    ext u
    constructor
    · intro hu c
      obtain ⟨a, rfl⟩ := Quotient.exists_rep c
      grind
    · grind
  have heventNz : {u : Vertex → C | ∀ c : Q,
      (repQ c).elim c₀ u = ξQ c} =
      {u : Vertex → C | ∀ c : Qnz, u (repNz c) = ξQ c.val} := by
    ext u
    constructor
    · grind
    · intro hu c
      by_cases hc : c = ghost
      · grind
      · simpa [hrepNz ⟨c, hc⟩] using hu ⟨c, hc⟩
  rw [heventQ, heventNz]
  rw [iidFieldMeasure_injective_cylinder ν repNz (by
    intro c d hcd
    grind)
    (fun c : Qnz => ξQ c.val)]
  grind

/-- The representative of an observed wired class is the ghost point for the
distinguished class and the lexicographic representative otherwise. -/
def wiredObservedRepresentative {A : Type*} (ω : LatticeConfiguration)
    (v : A → Vertex) (a : Option A) : Option Vertex :=
  a.elim none (fun x => clusterRepresentative ω (v x))

private theorem rcCluster_eq_of_reachable (ω : LatticeConfiguration) {x y : Vertex}
    (hxy : (rcInfiniteOpenGraph ω).Reachable x y) :
    RCInfinite.cluster ω x = RCInfinite.cluster ω y := by
  ext z
  solve_by_elim [hxy.symm.trans, hxy.trans]

theorem wiredObservedRepresentative_eq_iff {A : Type*} [Fintype A]
    (ω : LatticeConfiguration) (v : A → Vertex) (a b : Option A) :
    infiniteWiredPartition (Option.map v) ω a b ↔
      wiredObservedRepresentative ω v a = wiredObservedRepresentative ω v b := by
  classical
  let H := rcInfiniteOpenGraph ω
  cases a with
  | none =>
    cases b with
    | none => simp
    | some b =>
      constructor
      · intro hab
        have hinf := (infiniteMergedSetoid_some_none H _).mp ((infiniteMergedSetoid H).symm hab)
        simp [wiredObservedRepresentative, ((clusterRepresentative_none_iff ω _).2 (by assumption))]
      · intro hrep
        exact (infiniteMergedSetoid H).symm
          ((infiniteMergedSetoid_some_none H _).mpr (by
            simpa [clusterIsInfinite, H, RCInfinite.cluster] using
              (clusterRepresentative_none_iff ω _).1 (by simpa [wiredObservedRepresentative] using hrep.symm)))
  | some a =>
    cases b with
    | none =>
      constructor
      · intro hab
        have hinf := (infiniteMergedSetoid_some_none H _).mp hab
        exact (clusterRepresentative_none_iff ω _).2 (by assumption)
      · intro hrep
        exact (infiniteMergedSetoid_some_none H _).mpr (by
          simpa [clusterIsInfinite, H, RCInfinite.cluster] using
            (clusterRepresentative_none_iff ω _).1 (by assumption))
    | some b =>
      change infiniteMergedSetoid H (some (v a)) (some (v b)) ↔ _
      have hia : clusterIsInfinite H (v a) ↔ (RCInfinite.cluster ω (v a)).Infinite := by
        rfl
      have hib : clusterIsInfinite H (v b) ↔ (RCInfinite.cluster ω (v b)).Infinite := by
        rfl
      by_cases hfa : (RCInfinite.cluster ω (v a)).Finite
      · by_cases hfb : (RCInfinite.cluster ω (v b)).Finite
        · rw [infiniteMergedSetoid_some_some]
          simpa [wiredObservedRepresentative, hia, hib, hfa, hfb] using (clusterRepresentative_eq_iff_reachable ω hfa hfb).symm
        · rw [infiniteMergedSetoid_some_some]
          have hnotReach : ¬ H.Reachable (v a) (v b) := by
            grind [rcCluster_eq_of_reachable]
          have hxrep : clusterRepresentative ω (v a) ≠ none := by
            simp [clusterRepresentative, hfa]
          have hyrep :=
            (clusterRepresentative_none_iff ω _).2 hfb
          have hrepNe : clusterRepresentative ω (v a) ≠ clusterRepresentative ω (v b) := by
            grind
          tauto
      · by_cases hfb : (RCInfinite.cluster ω (v b)).Finite
        · rw [infiniteMergedSetoid_some_some]
          have hnotReach : ¬ H.Reachable (v a) (v b) := by
            grind [rcCluster_eq_of_reachable]
          have hxrep :=
            (clusterRepresentative_none_iff ω _).2 hfa
          have hyrep : clusterRepresentative ω (v b) ≠ none := by
            simp [clusterRepresentative, hfb]
          have hrepNe : clusterRepresentative ω (v a) ≠ clusterRepresentative ω (v b) := by
            grind
          tauto
        · rw [infiniteMergedSetoid_some_some]
          have hinfa : clusterIsInfinite H (v a) := hfa
          have hinfb : clusterIsInfinite H (v b) := hfb
          constructor
          · intro _
            exact ((clusterRepresentative_none_iff ω _).2 hfa).trans ((clusterRepresentative_none_iff ω _).2 hfb).symm
          · grind

/-- For a fixed wired configuration, canonical coloring by iid colors on
finite clusters and the boundary color on all infinite clusters has the
pinned Edwards--Sokal cylinder probability. -/
theorem wiredClusterColoring_fiber_cylinder_uniform (q : ℕ) (hq : 0 < q)
    (ω : LatticeConfiguration) (A : Finset Vertex) (ξ : SpinSpace q)
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) :
    iidFieldMeasure (ProbabilityTheory.uniformOn Set.univ)
      {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
        clusterColoring (boundaryColor hi) (ω, u) a.val = ξ a.val} =
      ENNReal.ofReal (pinnedClusterCylinderProbability
        (infiniteWiredPartition (Option.map (fun a : ↥A => a.val)) ω)
        some (fun a : ↥A => ξ a.val) none (boundaryColor hi)) := by
  classical
  let ν :=
    ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))
  let c₀ := boundaryColor hi
  let v : ↥A → Vertex := fun a => a.val
  let R := infiniteWiredPartition (Option.map v) ω
  let rep := wiredObservedRepresentative ω v
  let ξ' := markedMap (fun a : ↥A => ξ a.val) c₀
  let Q := Quotient R
  let ghost := Quotient.mk R none
  let Qnz := {c : Q // c ≠ ghost}
  let : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have hrep : ∀ a b, R a b ↔ rep a = rep b := by
    solve_by_elim [wiredObservedRepresentative_eq_iff]
  have hcomap (a b : Option ↥A) :
      R.comap (markedMap some none) a b ↔ R a b := by
    cases a <;> cases b <;> rfl
  have hcompKernel :
      (R.comap (markedMap some none) ≤ Setoid.ker ξ') ↔
        R ≤ Setoid.ker ξ' := { mp := fun h ⦃a b⦄ hab => h ((hcomap a b).mpr hab), mpr := fun h ⦃a b⦄ hab => h ((hcomap a b).mp hab) }
  let E :=
    {u | ∀ a : Option ↥A, (rep a).elim c₀ u = ξ' a}
  have hE : E = {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
      clusterColoring c₀ (ω, u) a.val = ξ a.val} := by
    ext u
    constructor
    · intro hu a
      exact hu (some a)
    · intro hu a
      cases a with
      | none => rfl
      | some a =>
        exact hu a
  rw [← hE]
  by_cases hcompat : R ≤ Setoid.ker ξ'
  · rw [iidFieldMeasure_pinnedObservedColoring_of_compatible ν R rep hrep
      rfl c₀ ξ' rfl hcompat]
    have hatom (c : Set.Icc 1 q) : ν {c} = (q : ℝ≥0∞)⁻¹ := pottsUniformColor_singleton q c
    simp_rw [hatom]
    rw [Finset.prod_const]
    have hcardF :=
      Nat.card_eq_fintype_card.symm.trans (by
        calc
          _ = Fintype.card Qnz := Nat.card_eq_fintype_card
          _ = Fintype.card Q - Fintype.card {c : Q // c = ghost} :=
            Fintype.card_subtype_compl _
          _ = Nat.card Q - 1 := by simp)
    have hcount : observedClassCount R (markedMap some none) = Nat.card Q := by
      rw [observedClassCount_eq_range]
      have hrange : Set.range (Quotient.mk R ∘ markedMap some none) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro c
        obtain ⟨a, rfl⟩ := Quotient.exists_rep c
        exact ⟨a, by
          cases a <;> rfl⟩
      simp [hrange, Q]
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_left (hcompKernel.2 hcompat), hcount]
    rw [PottsDiscontinuity.Potts.card_pottsColors, Finset.card_univ, hcardF]
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
    rw [ENNReal.ofReal_inv_of_pos (pow_pos hqreal _), ENNReal.ofReal_pow hqreal.le,
      ENNReal.ofReal_natCast]
    exact ENNReal.inv_pow.symm
  · have hEmpty : E = ∅ := by
      ext u
      simp only [E, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hu
      apply hcompat
      intro a b hab
      calc
        _ = (rep a).elim c₀ u := (hu a).symm
        _ = (rep b).elim c₀ u := by grind
        _ = _ := hu b
    rw [hEmpty]
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_right (fun hk => hcompat (hcompKernel.1 hk))]
    simp

variable {Ω A : Type*}

/-- Integrating a finite partition kernel over the first factor gives its
finite weighted sum. -/
theorem lintegral_finitePartitionKernel [MeasurableSpace Ω]
    [Fintype A] [Fintype (Setoid A)] (μ : Measure Ω)
    (r : Ω → Setoid A) (K : Setoid A → ℝ≥0∞)
    (hr : ∀ R, MeasurableSet {ω | r ω = R}) :
    ∫⁻ ω, K (r ω) ∂μ =
      ∑ R, K R * μ {ω | r ω = R} := by
  classical
  let f := fun R =>
    {ω | r ω = R}.indicator (fun _ => K R)
  have hf : (fun ω => K (r ω)) = fun ω => ∑ R, f R ω := by
    funext ω
    dsimp [f]
    rw [Finset.sum_eq_single (r ω)]
    · simp
    · intro R _ hR
      simp [hR.symm]
    · simp
  rw [hf, lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro R hR
    rw [lintegral_indicator_const (hr R)]
  · solve_by_elim [measurable_const.indicator]

theorem toReal_lintegral_finitePartitionKernel [MeasurableSpace Ω]
    [Finite A] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Setoid A) (K : Setoid A → ℝ)
    (hK : ∀ R, 0 ≤ K R)
    (hr : ∀ R, MeasurableSet {ω | r ω = R}) :
    (∫⁻ ω, ENNReal.ofReal (K (r ω)) ∂μ).toReal =
      PottsDiscontinuity.Potts.partitionExpectation μ r K := by
  classical
  let  := Fintype.ofFinite A
  let  := Fintype.ofFinite (Setoid A)
  rw [lintegral_finitePartitionKernel μ r (fun R => ENNReal.ofReal (K R)) hr, ENNReal.toReal_sum (fun R hR => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _))]
  apply Finset.sum_congr rfl
  intro R hR
  calc
    _ =
        K R * (μ {ω | r ω = R}).toReal := by simp_all
    _ = _ := mul_comm _ _

end
end PottsDiscontinuity.PottsThm
