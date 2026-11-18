module

public import PottsDiscontinuity.Potts.CylinderColoring
public import PottsDiscontinuity.Potts.LimitCompactness
public import PottsDiscontinuity.Potts.ObservedPartitionLimits
public import PottsDiscontinuity.PottsThm.ColoringFactor

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory
open PottsDiscontinuity.FK PottsDiscontinuity.Potts PottsDiscontinuity.RCInfinite
open scoped ENNReal

noncomputable section

private theorem iidFieldMeasure_injective_cylinder {A C : Type*} [Fintype A]
    [DecidableEq A] [MeasurableSpace C] [MeasurableSingletonClass C]
    [Finite C] [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (v : A → Vertex) (hv : Function.Injective v) (ξ : A → C) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (v a) = ξ a} = ∏ a : A, ν {ξ a} := by
  classical
  let S : Finset Vertex := Finset.univ.image v
  let rep (y : ↥S) : A := (Finset.mem_image.mp y.2).choose
  have hrep (y : ↥S) : v (rep y) = y.1 := (Finset.mem_image.mp y.2).choose_spec.2
  let t (y : Vertex) : Set C := if hy : y ∈ S then {ξ (rep ⟨y, hy⟩)} else Set.univ
  have hevent : {u : Vertex → C | ∀ a, u (v a) = ξ a} = Set.pi S t := by
    ext u; simp only [Set.mem_ofPred_eq, Set.mem_pi]
    refine ⟨fun hu y hy => ?_, fun hu a => ?_⟩
    · have hyS : y ∈ S := hy; simp [t, hyS, ← hu (rep ⟨y, hyS⟩), hrep ⟨y, hyS⟩]
    · have ha : v a ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ a)
      simpa [t, ha, hv (hrep ⟨v a, ha⟩)] using hu (v a) ha
  have hpi : Measure.infinitePi (fun _ : Vertex => ν) (Set.pi S t) = ∏ y ∈ S, ν (t y) := by
    apply Measure.infinitePi_pi
    intro y hy; simp [t, hy]
  rw [hevent]
  change Measure.infinitePi (fun _ : Vertex => ν) (Set.pi S t) = _
  rw [hpi, Finset.prod_image hv.injOn]
  exact Finset.prod_congr rfl fun a _ => by
    have ha : v a ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ a)
    simp [t, ha, hv (hrep ⟨v a, ha⟩)]

private theorem pottsUniformColor_singleton (q : ℕ) (c : Set.Icc 1 q) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)) {c} = (q : ℝ≥0∞)⁻¹ := by
  classical
  have h := ProbabilityTheory.uniformOn_apply_finset (s := (Finset.univ : Finset (Set.Icc 1 q))) (t := {c})
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_pottsColors] at h
  simpa using h

/-- For a fixed free bond configuration with finite clusters, the iid
representative coloring has the free Edwards--Sokal cylinder kernel. -/
theorem freeClusterColoring_fiber_cylinder_uniform (q : ℕ) (hq : 0 < q)
    (ω : LatticeConfiguration) (A : Finset Vertex) (ξ : SpinSpace q)
    [Fintype (Quotient (infiniteFreePartition (fun a : ↥A => a.val) ω))]
    (hfinite : ∀ x, (cluster ω x).Finite) :
    iidFieldMeasure (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)))
      {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
        clusterColoring ⟨1, le_rfl, by omega⟩ (ω, u) a.val = ξ a.val} =
      ENNReal.ofReal (clusterCylinderProbability
        (infiniteFreePartition (fun a : ↥A => a.val) ω) id (fun a : ↥A => ξ a.val)) := by
  classical
  let ν := ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))
  let R := infiniteFreePartition (fun a : ↥A => a.val) ω
  let : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have : IsProbabilityMeasure ν := inferInstance
  have : Finite (Set.Icc 1 q) := Finite.of_fintype _
  have hrepEx (a : ↥A) : ∃ y, clusterRepresentative ω a.val = some y :=
    Option.ne_none_iff_exists'.mp (by simp [clusterRepresentative, hfinite a.val])
  let repA (a : ↥A) := (hrepEx a).choose
  have hrepA (a : ↥A) : clusterRepresentative ω a.val = some (repA a) := (hrepEx a).choose_spec
  have hrep (a b : ↥A) : R a b ↔ repA a = repA b :=
    (clusterRepresentative_eq_iff_reachable ω a.val b.val (hfinite a.val) (hfinite b.val)).symm.trans (by simp [hrepA])
  rw [show {u : Vertex → Set.Icc 1 q | ∀ a : ↥A, clusterColoring ⟨1, le_rfl, by omega⟩ (ω, u) a.val = ξ a.val} =
    {u | ∀ a : ↥A, u (repA a) = ξ a.val} by ext; simp [clusterColoring, hrepA]]
  by_cases hcompat : R ≤ Setoid.ker (fun a : ↥A => ξ a.val)
  · let repQ : Quotient R → Vertex := Quotient.lift repA fun a b h => (hrep a b).mp h
    let ξQ : Quotient R → Set.Icc 1 q := Quotient.lift (fun a : ↥A => ξ a.val) hcompat
    have hinj : Function.Injective repQ := by
      rintro ⟨a⟩ ⟨b⟩ h; exact Quotient.sound ((hrep a b).mpr h)
    have hset : {u : Vertex → Set.Icc 1 q | ∀ a : ↥A, u (repA a) = ξ a.val} = {u | ∀ c : Quotient R, u (repQ c) = ξQ c} := by
      ext u; exact ⟨fun h c => Quotient.inductionOn c h, fun h a => h (Quotient.mk R a)⟩
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
    rw [hset, iidFieldMeasure_injective_cylinder ν repQ hinj ξQ]
    simp_rw [show ∀ c, ν {ξQ c} = (q : ℝ≥0∞)⁻¹ from fun c => pottsUniformColor_singleton q (ξQ c)]
    unfold clusterCylinderProbability
    rw [Finset.prod_const, ite_eq_left (by simpa using hcompat), show observedClassCount R id = Nat.card (Quotient R) from rfl,
      card_pottsColors, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ENNReal.ofReal_inv_of_pos (pow_pos hqreal _), ENNReal.ofReal_pow hqreal.le, ENNReal.ofReal_natCast, ENNReal.inv_pow]
  · have hemp : {u : Vertex → Set.Icc 1 q | ∀ a : ↥A, u (repA a) = ξ a.val} = ∅ := by
      ext u; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; intro hu
      exact hcompat fun a b hab => (hu a).symm.trans ((congrArg u ((hrep a b).mp hab)).trans (hu b))
    rw [hemp, measure_empty]; simp [clusterCylinderProbability, Setoid.comap_id, R, hcompat]

private theorem wiredObservedRepresentative_eq_iff {A : Type*} [Fintype A]
    (ω : LatticeConfiguration) (v : A → Vertex) (a b : Option A) :
    infiniteWiredPartition (Option.map v) ω a b ↔
      a.elim none (fun x => clusterRepresentative ω (v x)) =
        b.elim none (fun x => clusterRepresentative ω (v x)) := by
  let H := rcInfiniteOpenGraph ω
  have hsn (x : A) : infiniteMergedSetoid H (some (v x)) none ↔ clusterRepresentative ω (v x) = none :=
    (infiniteMergedSetoid_some_none H (v x)).trans
      ((by simp [clusterIsInfinite, H, RCInfinite.cluster] : _ ↔ (RCInfinite.cluster ω (v x)).Infinite).trans
        (clusterRepresentative_none_iff ω (v x)).symm)
  cases a with
  | none =>
    cases b with
    | none => simp
    | some b =>
      exact ⟨fun h => ((hsn b).mp ((infiniteMergedSetoid H).symm h)).symm,
        fun h => (infiniteMergedSetoid H).symm ((hsn b).mpr h.symm)⟩
  | some a =>
    cases b with
    | none => exact hsn a
    | some b =>
      change infiniteMergedSetoid H (some (v a)) (some (v b)) ↔
        clusterRepresentative ω (v a) = clusterRepresentative ω (v b)
      rw [infiniteMergedSetoid_some_some]
      by_cases hfa : (RCInfinite.cluster ω (v a)).Finite <;> by_cases hfb : (RCInfinite.cluster ω (v b)).Finite
      · have hia : ¬ clusterIsInfinite H (v a) := by simpa [clusterIsInfinite, H, RCInfinite.cluster] using hfa
        have hib : ¬ clusterIsInfinite H (v b) := by simpa [clusterIsInfinite, H, RCInfinite.cluster] using hfb
        simp only [hia, hib, and_false, or_false]
        exact (clusterRepresentative_eq_iff_reachable ω (v a) (v b) hfa hfb).symm
      · have hia : ¬ clusterIsInfinite H (v a) := by simpa [clusterIsInfinite, H, RCInfinite.cluster] using hfa
        have hnR : ¬ H.Reachable (v a) (v b) := fun hr => hfb (by convert hfa using 1; ext; exact ⟨hr.trans, hr.symm.trans⟩)
        have hnone := (clusterRepresentative_none_iff ω (v b)).2 hfb
        have hne : clusterRepresentative ω (v a) ≠ none := by simp [clusterRepresentative, hfa]
        exact ⟨fun h => h.elim (fun hr => absurd hr hnR) fun ⟨hi, _⟩ => absurd hi hia, fun heq => absurd (heq.trans hnone) hne⟩
      · have hib : ¬ clusterIsInfinite H (v b) := by simpa [clusterIsInfinite, H, RCInfinite.cluster] using hfb
        have hnR : ¬ H.Reachable (v a) (v b) := fun hr => hfa (by convert hfb using 1; ext; exact ⟨hr.symm.trans, hr.trans⟩)
        have hnone := (clusterRepresentative_none_iff ω (v a)).2 hfa
        have hne : clusterRepresentative ω (v b) ≠ none := by simp [clusterRepresentative, hfb]
        exact ⟨fun h => h.elim (fun hr => absurd hr hnR) fun ⟨_, hi⟩ => absurd hi hib, fun heq => absurd (heq.symm.trans hnone) hne⟩
      · have hia : clusterIsInfinite H (v a) := hfa
        have hib : clusterIsInfinite H (v b) := hfb
        simp [(clusterRepresentative_none_iff ω (v a)).2 hfa, (clusterRepresentative_none_iff ω (v b)).2 hfb, hia, hib]

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
  let ν := ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q))
  let c₀ := boundaryColor q i hi
  let v (a : ↥A) := a.val
  let R := infiniteWiredPartition (Option.map v) ω
  let rep (a : Option ↥A) : Option Vertex := a.elim none fun x => clusterRepresentative ω (v x)
  let ξ' := markedMap (fun a : ↥A => ξ a.val) c₀
  let Q := Quotient R; let ghost : Q := Quotient.mk R none; let Qnz := {c : Q // c ≠ ghost}
  let : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have : IsProbabilityMeasure ν := inferInstance
  have : Finite (Set.Icc 1 q) := Finite.of_fintype _
  have : Fintype Q := Fintype.ofFinite _; have : Fintype Qnz := Fintype.ofFinite _
  have hrep (a b : Option ↥A) : R a b ↔ rep a = rep b := wiredObservedRepresentative_eq_iff ω v a b
  have hcompK : (R.comap (markedMap some none) ≤ Setoid.ker ξ') ↔ R ≤ Setoid.ker ξ' := by
    have hc (a b : Option ↥A) : R.comap (markedMap some none) a b ↔ R a b := by cases a <;> cases b <;> rfl
    exact ⟨fun h a b hab => h ((hc a b).2 hab), fun h a b hab => h ((hc a b).1 hab)⟩
  have hE : {u : Vertex → Set.Icc 1 q | ∀ a : ↥A, clusterColoring c₀ (ω, u) a.val = ξ a.val} =
      {u | ∀ a : Option ↥A, (rep a).elim c₀ u = ξ' a} := by
    ext u; simp only [Set.mem_ofPred_eq]
    exact ⟨fun hu a => by cases a with
        | none => simp [rep, ξ', markedMap]
        | some a => simpa [rep, ξ', markedMap, clusterColoring, v] using hu a,
      fun hu a => by simpa [rep, ξ', markedMap, clusterColoring, v] using hu (some a)⟩
  rw [hE]
  by_cases hcompat : R ≤ Setoid.ker ξ'
  · let repQ : Q → Option Vertex := Quotient.lift rep fun a b h => (hrep a b).mp h
    let ξQ : Q → Set.Icc 1 q := Quotient.lift ξ' hcompat
    have hinj : Function.Injective repQ := by rintro ⟨a⟩ ⟨b⟩ h; exact Quotient.sound ((hrep a b).mpr h)
    have hEx (c : Qnz) : ∃ y, repQ c.val = some y := Option.ne_none_iff_exists'.mp fun h =>
      c.property (hinj (h.trans (by rfl : repQ ghost = none).symm))
    let repNz (c : Qnz) := (hEx c).choose
    have hrepNz (c : Qnz) : repQ c.val = some (repNz c) := (hEx c).choose_spec
    have hinjNz : Function.Injective repNz := fun c d h => Subtype.ext (hinj (by rw [hrepNz c, hrepNz d, h]))
    have hev : {u : Vertex → Set.Icc 1 q | ∀ a : Option ↥A, (rep a).elim c₀ u = ξ' a} =
        {u | ∀ c : Qnz, u (repNz c) = ξQ c.val} := by
      ext u; simp only [Set.mem_ofPred_eq]
      refine ⟨fun hu c => ?_, fun hu a => ?_⟩
      · obtain ⟨a, ha⟩ := Quotient.exists_rep c.val
        have := hu a; rwa [show rep a = repQ c.val from ha ▸ rfl, hrepNz c, show ξ' a = ξQ c.val from ha ▸ rfl] at this
      · by_cases hc : Quotient.mk R a = ghost
        · have : rep a = none := (hrep a none).mp (Quotient.exact hc)
          have hξa : ξ' a = c₀ := hcompat (Quotient.exact hc)
          simp [this, hξa]
        · have h1 : rep a = some (repNz ⟨Quotient.mk R a, hc⟩) := hrepNz ⟨Quotient.mk R a, hc⟩
          have h2 : ξ' a = ξQ (Quotient.mk R a) := rfl
          rw [h1, h2]; exact hu ⟨Quotient.mk R a, hc⟩
    have hcount : observedClassCount R (markedMap some none) = Nat.card Q := by
      rw [observedClassCount_eq_range, show Set.range (Quotient.mk R ∘ markedMap some none) = Set.univ from
        Set.eq_univ_of_forall fun c => by obtain ⟨a, rfl⟩ := Quotient.exists_rep c; exact ⟨a, by cases a <;> rfl⟩]; simp [Q]
    have hcardF : Fintype.card Qnz = Nat.card Q - 1 := by
      rw [Fintype.card_subtype_compl (· = ghost)]; simp [ghost, Nat.card_eq_fintype_card]
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
    rw [hev, iidFieldMeasure_injective_cylinder ν repNz hinjNz (fun c => ξQ c.val)]
    simp_rw [show ∀ c : Qnz, ν {ξQ c.val} = (q : ℝ≥0∞)⁻¹ from fun c => pottsUniformColor_singleton q _]
    unfold pinnedClusterCylinderProbability
    rw [Finset.prod_const, ite_eq_left (hcompK.2 hcompat), hcount, card_pottsColors,
      Finset.card_univ, hcardF, ENNReal.ofReal_inv_of_pos (pow_pos hqreal _),
      ENNReal.ofReal_pow hqreal.le, ENNReal.ofReal_natCast, ENNReal.inv_pow]
  · have hemp : {u : Vertex → Set.Icc 1 q | ∀ a : Option ↥A, (rep a).elim c₀ u = ξ' a} = ∅ := by
      ext u; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; intro hu
      exact hcompat fun a b hab => (hu a).symm.trans ((congrArg (·.elim c₀ u) ((hrep a b).mp hab)).trans (hu b))
    rw [hemp, measure_empty]; unfold pinnedClusterCylinderProbability
    rw [ite_eq_right (mt hcompK.1 hcompat)]; simp

theorem toReal_lintegral_finitePartitionKernel {Ω A : Type*} [MeasurableSpace Ω]
    [Finite A] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Setoid A) (K : Setoid A → ℝ) (hK : ∀ R, 0 ≤ K R)
    (hr : ∀ R, MeasurableSet {ω | r ω = R}) :
    (∫⁻ ω, ENNReal.ofReal (K (r ω)) ∂μ).toReal = partitionExpectation μ r K := by
  classical
  let : Fintype A := Fintype.ofFinite A; let : Fintype (Setoid A) := Fintype.ofFinite (Setoid A)
  have hf : (fun ω => ENNReal.ofReal (K (r ω))) =
      fun ω => ∑ R : Setoid A, {ω' | r ω' = R}.indicator (fun _ => ENNReal.ofReal (K R)) ω :=
    funext fun ω => by rw [Finset.sum_eq_single (r ω) (fun R _ hne => by simp [hne.symm]) (by simp)]; simp
  have hsum : ∫⁻ ω, ENNReal.ofReal (K (r ω)) ∂μ = ∑ R : Setoid A, ENNReal.ofReal (K R) * μ {ω | r ω = R} := by
    rw [hf, lintegral_finsetSum _ fun R _ => measurable_const.indicator (hr R)]
    exact Finset.sum_congr rfl fun R _ => lintegral_indicator_const (hr R) (ENNReal.ofReal (K R))
  rw [hsum, ENNReal.toReal_sum fun R _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)]
  unfold partitionExpectation
  refine Finset.sum_congr rfl fun R _ => ?_
  calc (ENNReal.ofReal (K R) * μ {ω | r ω = R}).toReal
      = K R * (μ {ω | r ω = R}).toReal := by simp [ENNReal.toReal_mul, hK R]
    _ = (μ {ω | r ω = R}).toReal * K R := mul_comm _ _

end
end PottsDiscontinuity.PottsThm
