module

public import PottsDiscontinuity.Potts.CylinderColoring
public import PottsDiscontinuity.Potts.LimitCompactness
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

theorem iidFieldMeasure_injective_cylinder {A C : Type*} [Fintype A]
    [DecidableEq A] [MeasurableSpace C] [MeasurableSingletonClass C]
    [Finite C] [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (v : A → Vertex) (hv : Function.Injective v) (ξ : A → C) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (v a) = ξ a} =
      ∏ a : A, ν {ξ a} := by
  classical
  let S : Finset Vertex := Finset.univ.image v
  let rep (y : ↥S) : A := Classical.choose (Finset.mem_image.mp y.2)
  have hrep (y : ↥S) : v (rep y) = y.1 := (Finset.mem_image.mp y.2).choose_spec.2
  let t : Vertex → Set C := fun y => if hy : y ∈ S then {ξ (rep ⟨y, hy⟩)} else Set.univ
  have hevent : {u : Vertex → C | ∀ a, u (v a) = ξ a} = Set.pi S t := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe]
    refine ⟨fun hu y hy => ?_, fun hu a => ?_⟩
    · simp only [t, hy, ↓reduceDIte, Set.mem_singleton_iff]
      simpa [hrep ⟨y, hy⟩] using hu (rep ⟨y, hy⟩)
    · have ha : v a ∈ S := Finset.mem_image_of_mem v (Finset.mem_univ a)
      have hu' := hu (v a) ha
      simp only [t, ha, ↓reduceDIte, Set.mem_singleton_iff, hv (hrep ⟨v a, ha⟩)] at hu'
      exact hu'
  rw [hevent]
  change Measure.infinitePi (fun _ : Vertex => ν) (Set.pi S t) = _
  rw [Measure.infinitePi_pi (μ := fun _ : Vertex => ν) (s := S) (t := t)
    (fun y hy => by simp [t, hy]), Finset.prod_image hv.injOn]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hmem : v a ∈ S := Finset.mem_image_of_mem v (Finset.mem_univ a)
  simp [t, hmem, hv (hrep ⟨v a, hmem⟩)]

theorem iidFieldMeasure_observedColoring_of_compatible {A C : Type*} [Fintype A]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (R : Setoid A) [Fintype (Quotient R)] (rep : A → Vertex)
    (hrep : ∀ a b, R a b ↔ rep a = rep b) (ξ : A → C)
    (hξ : R ≤ Setoid.ker ξ) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (rep a) = ξ a} =
      ∏ c : Quotient R, ν {ξ (Classical.choose (Quotient.exists_rep c))} := by
  classical
  let : DecidableEq (Quotient R) := Classical.decEq _
  let repQ : Quotient R → Vertex := Quotient.lift rep fun a b hab => (hrep a b).mp hab
  have hinj : Function.Injective repQ := by
    rintro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    exact Quotient.sound ((hrep a b).mpr hxy)
  let ξQ : Quotient R → C := Quotient.lift ξ fun a b hab => hξ hab
  have hset : {u : Vertex → C | ∀ a, u (rep a) = ξ a} =
      {u : Vertex → C | ∀ c : Quotient R, u (repQ c) = ξQ c} := by
    ext u; simp only [Set.mem_ofPred_eq, Quotient.forall]; rfl
  rw [hset, iidFieldMeasure_injective_cylinder ν repQ hinj ξQ]
  refine Finset.prod_congr rfl fun c _ => ?_
  have hchoose := Classical.choose_spec (Quotient.exists_rep c)
  exact congrArg (fun x => ν {x}) (congrArg ξQ hchoose.symm)

theorem iidFieldMeasure_observedColoring_of_incompatible {A C : Type*} [Fintype A]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (R : Setoid A) (rep : A → Vertex)
    (hrep : ∀ a b, R a b ↔ rep a = rep b) (ξ : A → C)
    (hξ : ¬ R ≤ Setoid.ker ξ) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (rep a) = ξ a} = 0 := by
  have hempty : {u : Vertex → C | ∀ a, u (rep a) = ξ a} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun u hu =>
      hξ fun a b hab => (hu a).symm.trans ((congrArg u ((hrep a b).mp hab)).trans (hu b))
  simp [hempty]

theorem pottsUniformColor_singleton (q : ℕ) (c : Set.Icc 1 q) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)) {c} =
      (q : ℝ≥0∞)⁻¹ := by
  classical
  have h := ProbabilityTheory.uniformOn_apply_finset
    (s := (Finset.univ : Finset (Set.Icc 1 q))) (t := {c})
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_pottsColors] at h
  simpa using h

theorem freeClusterColoring_fiber_cylinder_uniform (q : ℕ) (hq : 0 < q)
    (ω : LatticeConfiguration) (A : Finset Vertex) (ξ : SpinSpace q)
    [Fintype (Quotient (infiniteFreePartition (fun a : ↥A => a.val) ω))]
    (hfinite : ∀ x, (cluster ω x).Finite) :
    iidFieldMeasure (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)))
      {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
        clusterColoring ⟨1, le_rfl, by omega⟩ (ω, u) a.val = ξ a.val} =
      ENNReal.ofReal (clusterCylinderProbability
        (infiniteFreePartition (fun a : ↥A => a.val) ω) id
        (fun a : ↥A => ξ a.val)) := by
  classical
  let R := infiniteFreePartition (fun a : ↥A => a.val) ω
  let : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have : Finite (Set.Icc 1 q) := Finite.of_fintype _
  have hrepExists (a : ↥A) : ∃ y, clusterRepresentative ω a.val = some y :=
    Option.ne_none_iff_exists'.mp (by simp [clusterRepresentative, hfinite a.val])
  let repA (a : ↥A) : Vertex := Classical.choose (hrepExists a)
  have hrepA (a : ↥A) : clusterRepresentative ω a.val = some (repA a) :=
    Classical.choose_spec (hrepExists a)
  have hrep (a b : ↥A) : R a b ↔ repA a = repA b :=
    (clusterRepresentative_eq_iff_reachable ω a.val b.val
      (hfinite a.val) (hfinite b.val)).symm.trans (by simp [hrepA])
  have hset : {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
      clusterColoring ⟨1, le_rfl, by omega⟩ (ω, u) a.val = ξ a.val} =
      {u : Vertex → Set.Icc 1 q | ∀ a : ↥A, u (repA a) = ξ a.val} := by
    ext u; simp [clusterColoring, hrepA]
  rw [hset]
  by_cases hcompat : R ≤ Setoid.ker (fun a : ↥A => ξ a.val)
  · rw [iidFieldMeasure_observedColoring_of_compatible _ R repA hrep _ hcompat]
    simp_rw [pottsUniformColor_singleton q]
    rw [Finset.prod_const]
    have hcompatId : R.comap id ≤ Setoid.ker (fun a : ↥A => ξ a.val) := hcompat
    unfold clusterCylinderProbability
    rw [ite_eq_left hcompatId, show observedClassCount R id = Nat.card (Quotient R) from rfl,
      card_pottsColors, Finset.card_univ, ← Nat.card_eq_fintype_card]
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
    rw [ENNReal.ofReal_inv_of_pos (pow_pos hqreal _), ENNReal.ofReal_pow hqreal.le,
      ENNReal.ofReal_natCast, ENNReal.inv_pow]
  · rw [iidFieldMeasure_observedColoring_of_incompatible _ R repA hrep _ hcompat]
    simp [clusterCylinderProbability, Setoid.comap_id, R, hcompat]

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
  let ghost : Q := Quotient.mk R none
  let repQ : Q → Option Vertex := Quotient.lift rep fun a b hab => (hrep a b).mp hab
  have hrepQGhost : repQ ghost = none := hrepGhost
  have hinj : Function.Injective repQ := by
    rintro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    exact Quotient.sound ((hrep a b).mpr hxy)
  let ξQ : Q → C := Quotient.lift ξ fun a b hab => hcompat hab
  have hξQGhost : ξQ ghost = c₀ := hξGhost
  let Qnz := {c : Q // c ≠ ghost}
  have hrepExists (c : Qnz) : ∃ v, repQ c.val = some v :=
    Option.ne_none_iff_exists'.mp fun h => c.2 (hinj (h.trans hrepQGhost.symm))
  let repNz (c : Qnz) : Vertex := Classical.choose (hrepExists c)
  have hrepNz (c : Qnz) : repQ c.val = some (repNz c) := Classical.choose_spec (hrepExists c)
  have hinjNz : Function.Injective repNz := fun c d hcd =>
    Subtype.ext (hinj (by rw [hrepNz c, hrepNz d, hcd]))
  have hevent : {u : Vertex → C | ∀ a : Option A, (rep a).elim c₀ u = ξ a} =
      {u : Vertex → C | ∀ c : Qnz, u (repNz c) = ξQ c.val} := by
    ext u
    simp only [Set.mem_ofPred_eq]
    refine (Quotient.forall (p := fun c : Q => (repQ c).elim c₀ u = ξQ c)).symm.trans
      ⟨fun hu c => by simpa [hrepNz c] using hu c.val, fun hu c => ?_⟩
    by_cases hc : c = ghost
    · subst c; simp [hrepQGhost, hξQGhost]
    · simpa [hrepNz ⟨c, hc⟩] using hu ⟨c, hc⟩
  rw [hevent, iidFieldMeasure_injective_cylinder ν repNz hinjNz (fun c : Qnz => ξQ c.val)]
  refine Finset.prod_congr rfl fun c _ => ?_
  have hchoose := Classical.choose_spec (Quotient.exists_rep c.val)
  exact congrArg (fun x => ν {x}) (congrArg ξQ hchoose.symm)

def wiredObservedRepresentative {A : Type*} (ω : LatticeConfiguration)
    (v : A → Vertex) (a : Option A) : Option Vertex :=
  a.elim none (fun x => clusterRepresentative ω (v x))

private theorem wiredObservedRepresentative_eq_none_iff {A : Type*}
    (ω : LatticeConfiguration) (v : A → Vertex) (a : Option A) :
    wiredObservedRepresentative ω v a = none ↔
      infiniteMergedSetoid (rcInfiniteOpenGraph ω) (Option.map v a) none := by
  cases a with
  | none =>
    simp only [wiredObservedRepresentative, Option.elim_none, Option.map_none, true_iff]
    exact (infiniteMergedSetoid _).refl _
  | some a =>
    simp only [wiredObservedRepresentative, Option.elim_some, Option.map_some,
      clusterRepresentative_none_iff]
    exact (infiniteMergedSetoid_some_none (rcInfiniteOpenGraph ω) (v a)).symm

theorem wiredObservedRepresentative_eq_iff {A : Type*} [Fintype A]
    (ω : LatticeConfiguration) (v : A → Vertex) (a b : Option A) :
    infiniteWiredPartition (Option.map v) ω a b ↔
      wiredObservedRepresentative ω v a = wiredObservedRepresentative ω v b := by
  classical
  let H := rcInfiniteOpenGraph ω
  change infiniteMergedSetoid H (Option.map v a) (Option.map v b) ↔ _
  by_cases ha : wiredObservedRepresentative ω v a = none
  · have ha' := (wiredObservedRepresentative_eq_none_iff ω v a).mp ha
    rw [ha, eq_comm, wiredObservedRepresentative_eq_none_iff]
    exact ⟨fun hab => (infiniteMergedSetoid H).trans ((infiniteMergedSetoid H).symm hab) ha',
      fun hb' => (infiniteMergedSetoid H).trans ha' ((infiniteMergedSetoid H).symm hb')⟩
  · by_cases hb : wiredObservedRepresentative ω v b = none
    · have hb' := (wiredObservedRepresentative_eq_none_iff ω v b).mp hb
      rw [hb]
      exact ⟨fun hab => False.elim (ha ((wiredObservedRepresentative_eq_none_iff ω v a).mpr
        ((infiniteMergedSetoid H).trans hab hb'))), fun h => False.elim (ha h)⟩
    · cases a with
      | none => exact False.elim (ha rfl)
      | some a =>
        cases b with
        | none => exact False.elim (hb rfl)
        | some b =>
          have hfa : (RCInfinite.cluster ω (v a)).Finite :=
            not_not.mp (mt (clusterRepresentative_none_iff ω (v a)).mpr ha)
          have hfb : (RCInfinite.cluster ω (v b)).Finite :=
            not_not.mp (mt (clusterRepresentative_none_iff ω (v b)).mpr hb)
          have hna : ¬ clusterIsInfinite H (v a) := by
            simpa [clusterIsInfinite, H, RCInfinite.cluster] using hfa
          dsimp only [Option.map_some]
          rw [infiniteMergedSetoid_some_some]
          simp only [wiredObservedRepresentative, Option.elim_some, hna, false_and, or_false]
          exact (clusterRepresentative_eq_iff_reachable ω (v a) (v b) hfa hfb).symm

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
  let ν : Measure (Set.Icc 1 q) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))
  let c₀ : Set.Icc 1 q := boundaryColor q i hi
  let v : ↥A → Vertex := fun a => a.val
  let R : Setoid (Option ↥A) := infiniteWiredPartition (Option.map v) ω
  let rep : Option ↥A → Option Vertex := wiredObservedRepresentative ω v
  let ξ' : Option ↥A → Set.Icc 1 q := markedMap (fun a : ↥A => ξ a.val) c₀
  let Q := Quotient R
  let ghost : Q := Quotient.mk R none
  let Qnz := {c : Q // c ≠ ghost}
  let : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (ProbabilityTheory.uniformOn _))
  have : Finite (Set.Icc 1 q) := Finite.of_fintype _
  have : Fintype Q := Fintype.ofFinite _
  have : Fintype Qnz := Fintype.ofFinite _
  have hrep : ∀ a b, R a b ↔ rep a = rep b := wiredObservedRepresentative_eq_iff ω v
  have hmark_id : markedMap (some : ↥A → Option ↥A) none = id := by funext a; cases a <;> rfl
  let E : Set (Vertex → Set.Icc 1 q) := {u | ∀ a : Option ↥A, (rep a).elim c₀ u = ξ' a}
  have hE : E = {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
      clusterColoring c₀ (ω, u) a.val = ξ a.val} := by
    ext u; simp [E, Option.forall, rep, ξ', wiredObservedRepresentative, clusterColoring, v, markedMap]
  rw [← hE]
  unfold pinnedClusterCylinderProbability
  rw [hmark_id, Setoid.comap_id, show observedClassCount R id = Nat.card Q from rfl]
  by_cases hcompat : R ≤ Setoid.ker ξ'
  · rw [ite_eq_left hcompat, iidFieldMeasure_pinnedObservedColoring_of_compatible ν R rep hrep
      rfl c₀ ξ' rfl hcompat]
    simp_rw [show ∀ c, ν {c} = (q : ℝ≥0∞)⁻¹ from pottsUniformColor_singleton q]
    have hcardF : Fintype.card Qnz = Nat.card Q - 1 := by
      calc Fintype.card Qnz
        _ = Fintype.card Q - Fintype.card {c : Q // c = ghost} :=
            Fintype.card_subtype_compl (fun c : Q => c = ghost)
        _ = Nat.card Q - 1 := by simp [ghost, Nat.card_eq_fintype_card]
    rw [Finset.prod_const, Finset.card_univ, hcardF, card_pottsColors]
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
    rw [ENNReal.ofReal_inv_of_pos (pow_pos hqreal _), ENNReal.ofReal_pow hqreal.le,
      ENNReal.ofReal_natCast, ENNReal.inv_pow]
  · rw [ite_eq_right hcompat]
    have hEmpty : E = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun u hu =>
      hcompat fun a b hab => (hu a).symm.trans
        ((congrArg (fun x : Option Vertex => x.elim c₀ u) ((hrep a b).mp hab)).trans (hu b))
    simp [hEmpty]

theorem lintegral_finitePartitionKernel {Ω A : Type*} [MeasurableSpace Ω]
    [Fintype A] [Fintype (Setoid A)] (μ : Measure Ω)
    (r : Ω → Setoid A) (K : Setoid A → ℝ≥0∞)
    (hr : ∀ R, MeasurableSet {ω | r ω = R}) :
    ∫⁻ ω, K (r ω) ∂μ =
      ∑ R : Setoid A, K R * μ {ω | r ω = R} := by
  classical
  have hf : (fun ω => K (r ω)) =
      fun ω => ∑ R : Setoid A, ({ω' | r ω' = R}.indicator (fun _ => K R)) ω := by
    funext ω
    rw [Finset.sum_eq_single (r ω)]
    · simp
    · intro R _ hR; simp [hR.symm]
    · simp
  rw [hf, lintegral_finsetSum _ fun R _ => measurable_const.indicator (hr R)]
  exact Finset.sum_congr rfl fun R _ => lintegral_indicator_const (hr R) _

theorem toReal_lintegral_finitePartitionKernel {Ω A : Type*} [MeasurableSpace Ω]
    [Finite A] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Setoid A) (K : Setoid A → ℝ)
    (hK : ∀ R, 0 ≤ K R)
    (hr : ∀ R, MeasurableSet {ω | r ω = R}) :
    (∫⁻ ω, ENNReal.ofReal (K (r ω)) ∂μ).toReal =
      PottsDiscontinuity.Potts.partitionExpectation μ r K := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype (Setoid A) := Fintype.ofFinite (Setoid A)
  rw [lintegral_finitePartitionKernel μ r (fun R => ENNReal.ofReal (K R)) hr,
    partitionExpectation, ENNReal.toReal_sum fun R _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hK R), mul_comm]
  rfl

end
end PottsDiscontinuity.PottsThm
