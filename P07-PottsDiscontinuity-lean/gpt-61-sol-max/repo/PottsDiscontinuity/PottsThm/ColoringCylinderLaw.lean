module
public import Mathlib

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

section

variable {A C : Type*}
include A C

/-- An iid field assigns independent coordinate values at any finite family
of distinct sites. -/
theorem iidFieldMeasure_injective_cylinder  [Fintype A]
    [DecidableEq A] [MeasurableSpace C] [MeasurableSingletonClass C]
    [Finite C] [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (v : A → Vertex) (hv : Function.Injective v) (ξ : A → C) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (v a) = ξ a} =
      ∏ a : A, ν {ξ a} := by
  
  let S  := Finset.univ.image v
  
  
  let t  := fun y => if hy : y ∈ S then {ξ ((fun (y : ↥S) => Classical.choose (Finset.mem_image.mp y.2)) ⟨y, hy⟩)} else Set.univ
  have hevent : {u : Vertex → C | ∀ a, u (v a) = ξ a} = Set.pi S t := by
    grind
  rw [hevent]
  change Measure.infinitePi (fun _  => ν) (Set.pi S t) = _
  have hpi : Measure.infinitePi (fun _  => ν) (Set.pi S t) =
      ∏ y ∈ S, ν (t y) := by
    apply Measure.infinitePi_pi
    intro y hy
    simp [t, hy]
  rw [hpi]
  rw [Finset.prod_image hv.injOn]
  grind

/-- Distinct iid coordinates attached to the classes of a finite observed
partition have the ordinary product law. -/
theorem iidFieldMeasure_quotient_cylinder  [Fintype A]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (R : Setoid A) [Fintype (Quotient R)]
    (v : Quotient R → Vertex) (hv : Function.Injective v)
    (ξ : Quotient R → C) :
    iidFieldMeasure ν
        {u : Vertex → C | ∀ a, u (v (Quotient.mk R a)) = ξ (Quotient.mk R a)} =
      ∏ c : Quotient R, ν {ξ c} := by
  classical
  
  have hset : {u : Vertex → C |
      ∀ a, u (v (Quotient.mk R a)) = ξ (Quotient.mk R a)} =
      {u : Vertex → C | ∀ c , u (v c) = ξ c} := by
    ext u
    constructor
    · intro h c
      obtain ⟨a, rfl⟩ := Quotient.exists_rep c
      exact h a
    · simp_all
  rw [hset]
  exact iidFieldMeasure_injective_cylinder ν v hv ξ

/-- Conditional cylinder probability for coordinates indexed by the classes of
a finite observed relation, represented by distinct lattice sites. -/
theorem iidFieldMeasure_observedColoring_of_compatible  [Fintype A]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (R : Setoid A) [Fintype (Quotient R)] (rep : A → Vertex)
    (hrep : ∀ a b, R a b ↔ rep a = rep b) (ξ : A → C)
    (hξ : R ≤ Setoid.ker ξ) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (rep a) = ξ a} =
      ∏ c : Quotient R, ν {ξ (Classical.choose (Quotient.exists_rep c))} := by
  
  let repQ  := Quotient.lift rep  fun a b hab => (hrep a b).mp hab 
  have hrepQ (a : A) : repQ (Quotient.mk R a) = rep a := rfl
  
  let ξQ  := Quotient.lift ξ  fun a b hab => hξ hab 
  have hξQ (a : A) : ξQ (Quotient.mk R a) = ξ a := rfl
  
  
  
  
  have hprob := iidFieldMeasure_quotient_cylinder ν R repQ (by
                                                              intro x y hxy
                                                              obtain ⟨a, rfl⟩ := Quotient.exists_rep x
                                                              obtain ⟨b, rfl⟩ := Quotient.exists_rep y
                                                              apply Quotient.sound
                                                              simp_all) ξQ
  grind

/-- An incompatible observed pattern has zero iid coloring probability. -/
theorem iidFieldMeasure_observedColoring_of_incompatible  [Fintype A]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Finite C]
    [DecidableEq Vertex] (ν : Measure C) [IsProbabilityMeasure ν]
    (R : Setoid A) (rep : A → Vertex)
    (hrep : ∀ a b, R a b ↔ rep a = rep b) (ξ : A → C)
    (hξ : ¬ R ≤ Setoid.ker ξ) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (rep a) = ξ a} = 0 := by
  
  obtain ⟨a, b, hab, hcolors⟩ : ∃ a b, R a b ∧ ξ a ≠ ξ b := by
    by_contra h
    apply hξ
    intro a b hab
    aesop
  have hempty : {u : Vertex → C | ∀ a, u (rep a) = ξ a} = ∅ := by
    grind
  rw [hempty]
  simp

end

theorem pottsUniformColor_singleton (q : ℕ)
    (c : Set.Icc 1 q) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)) {c} =
      (q : ℝ≥0∞)⁻¹ := by
  
  have h := ProbabilityTheory.uniformOn_apply_finset
    (s :=  Finset.univ ) (t := {c})
  
  
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
        (infiniteFreePartition (fun a : ↥A => a.val) ω) id
         fun a : ↥A => ξ a.val ) := by
  
  let R := infiniteFreePartition (fun a : ↥A => a.val) ω
  let : Nonempty (Set.Icc 1 q) := by
                                    aesop
  
  
  
  have hrepExists (a : ↥A) : ∃ y, clusterRepresentative ω a.val = some y := by
    simp_all [clusterRepresentative]
  let repA (a : ↥A)  := Classical.choose (hrepExists a)
  have hrepA (a : ↥A) : clusterRepresentative ω a.val = some (repA a) :=
    Classical.choose_spec (hrepExists a)
  have hrep (a b : ↥A) : R a b ↔ repA a = repA b := by
    
    exact (clusterRepresentative_eq_iff_reachable ω a.val b.val
      (hfinite a.val) (hfinite b.val)).symm.trans (by simp [hrepA])
  have hset : {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
      clusterColoring ⟨1, le_rfl, by omega⟩ (ω, u) a.val = ξ a.val} =
      {u : Vertex → Set.Icc 1 q | ∀ a , u (repA a) = ξ a.val} := by
    
    simp [clusterColoring, hrepA]
  rw [hset]
  by_cases hcompat : R ≤ Setoid.ker  fun a  => ξ a.val 
  · rw [iidFieldMeasure_observedColoring_of_compatible
      (ProbabilityTheory.uniformOn  Set.univ ) R repA hrep
      (fun a  => ξ a.val) hcompat]
    have hatom (c : Set.Icc 1 q)  := pottsUniformColor_singleton q c
    simp_rw [hatom]
    rw [Finset.prod_const]
    have hcount : observedClassCount R id = Nat.card (Quotient R) := rfl
    have hcompatId : R.comap id ≤ Setoid.ker  fun a  => ξ a.val  := hcompat
    unfold PottsDiscontinuity.Potts.clusterCylinderProbability
    rw [ite_eq_left hcompatId, PottsDiscontinuity.Potts.card_pottsColors]
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
    rw [ENNReal.ofReal_inv_of_pos (pow_pos hqreal _)]
    rw [ENNReal.ofReal_pow hqreal.le, ENNReal.ofReal_natCast]
    exact ENNReal.inv_pow.symm
  · rw [iidFieldMeasure_observedColoring_of_incompatible
      (ProbabilityTheory.uniformOn  Set.univ ) R repA hrep
      (fun a  => ξ a.val) hcompat]
    simp [PottsDiscontinuity.Potts.clusterCylinderProbability, R, hcompat]

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
  let ghost : Q := Quotient.mk R none
  let repQ : Q → Option Vertex := Quotient.lift rep
     fun a b hab => (hrep a b).mp hab 
  have hrepQ (a : Option A) : repQ (Quotient.mk R a) = rep a := rfl
  have hrepQGhost : repQ ghost = none := by simp [ghost, hrepQ, hrepGhost]
  have hinj : Function.Injective repQ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Quotient.exists_rep x
    obtain ⟨b, rfl⟩ := Quotient.exists_rep y
    apply Quotient.sound
    simp_all
  let ξQ : Q → C := Quotient.lift ξ  fun a b hab => hcompat hab 
  have hξQ (a : Option A) : ξQ (Quotient.mk R a) = ξ a := rfl
  have hξQGhost : ξQ ghost = c₀ := by simp [ghost, hξQ, hξGhost]
  let Qnz := {c : Q // c ≠ ghost}
  have hrepExists (c : Qnz) : ∃ v, repQ c.val = some v := by
    cases h : repQ c.val with
    | none =>
      grind
    | some v => exact ⟨v, rfl⟩
  let repNz (c : Qnz)  := Classical.choose (hrepExists c)
  have hrepNz (c : Qnz) : repQ c.val = some (repNz c) :=
    Classical.choose_spec (hrepExists c)
  
  have heventQ : {u : Vertex → C | ∀ a ,
      (rep a).elim c₀ u = ξ a} =
      {u : Vertex → C | ∀ c , (repQ c).elim c₀ u = ξQ c} := by
    ext u
    constructor
    · intro hu c
      obtain ⟨a, rfl⟩ := Quotient.exists_rep c
      simp_all
    · grind
  have heventNz : {u : Vertex → C | ∀ c ,
      (repQ c).elim c₀ u = ξQ c} =
      {u : Vertex → C | ∀ c , u (repNz c) = ξQ c.val} := by
    ext u
    constructor
    · grind
    · intro hu c
      by_cases hc : c = ghost
      · subst c
        simp [hrepQGhost, hξQGhost]
      · simpa [hrepNz ⟨c, hc⟩] using hu ⟨c, hc⟩
  rw [heventQ, heventNz]
  rw [iidFieldMeasure_injective_cylinder ν repNz (by
                                                    intro c d hcd
                                                    grind)
     fun c  => ξQ c.val ]
  grind

/-- The representative of an observed wired class is the ghost point for the
distinguished class and the lexicographic representative otherwise. -/
def wiredObservedRepresentative {A : Type*} (ω : LatticeConfiguration)
    (v : A → Vertex) (a : Option A)  :=
  a.elim none  fun x => clusterRepresentative ω (v x) 

private theorem rcCluster_eq_of_reachable (ω : LatticeConfiguration) {x y : Vertex}
    (hxy : (rcInfiniteOpenGraph ω).Reachable x y) :
    RCInfinite.cluster ω x = RCInfinite.cluster ω y := Set.ext fun z =>
                                                         { mp := SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm hxy), mpr := SimpleGraph.Reachable.trans hxy }

theorem wiredObservedRepresentative_eq_iff {A : Type*} [Fintype A]
    (ω : LatticeConfiguration) (v : A → Vertex) (a b : Option A) :
    infiniteWiredPartition (Option.map v) ω a b ↔
      wiredObservedRepresentative ω v a = wiredObservedRepresentative ω v b := by
  
  let H := rcInfiniteOpenGraph ω
  cases a with
  | none =>
    cases b with
    | none => simp 
    | some b =>
      
      constructor
      · intro hab
        
        
        
        simp [wiredObservedRepresentative,  (clusterRepresentative_none_iff ω (v b)).2  ((infiniteMergedSetoid_some_none H (v b)).mp ((infiniteMergedSetoid H).symm hab))  ]
      · intro hrep
        
        
        exact (infiniteMergedSetoid H).symm
          ((infiniteMergedSetoid_some_none H (v b)).mpr ((clusterRepresentative_none_iff ω (v b)).mp (Eq.symm hrep)))
  | some a =>
    cases b with
    | none =>
      
      constructor
      · intro hab
        
         
        simp [wiredObservedRepresentative,  (clusterRepresentative_none_iff ω (v a)).2  ((infiniteMergedSetoid_some_none H (v a)).mp hab) ]
      · intro hrep
        
        have hinf  := (clusterRepresentative_none_iff ω (v a)).mp  hrep 
        exact (infiniteMergedSetoid_some_none H (v a)).mpr hinf
    | some b =>
      change infiniteMergedSetoid H (some (v a)) (some (v b)) ↔ _
      have hia : clusterIsInfinite H (v a) ↔ (RCInfinite.cluster ω (v a)).Infinite := by
        simp [clusterIsInfinite, H, RCInfinite.cluster]
      have hib : clusterIsInfinite H (v b) ↔ (RCInfinite.cluster ω (v b)).Infinite := by
        simp [clusterIsInfinite, H, RCInfinite.cluster]
      by_cases hfa : (RCInfinite.cluster ω (v a)).Finite
      · by_cases hfb : (RCInfinite.cluster ω (v b)).Finite
        · rw [infiniteMergedSetoid_some_some]
          
          simpa [wiredObservedRepresentative, hia, hfa] using (clusterRepresentative_eq_iff_reachable ω (v a) (v b) hfa hfb).symm
        · rw [infiniteMergedSetoid_some_some]
          have hnotReach : ¬ H.Reachable (v a) (v b) := by
            grind [rcCluster_eq_of_reachable]
          have hxrep : clusterRepresentative ω (v a) ≠ none := by
            simp [clusterRepresentative, hfa]
          have hyrep  :=
            (clusterRepresentative_none_iff ω (v b)).2 hfb
          have hrepNe : clusterRepresentative ω (v a) ≠ clusterRepresentative ω (v b) := by
            simp_all
          constructor
          · simp_all
          · exact fun heq => (hrepNe heq).elim
      · by_cases hfb : (RCInfinite.cluster ω (v b)).Finite
        · rw [infiniteMergedSetoid_some_some]
          have hnotReach : ¬ H.Reachable (v a) (v b) := by
            grind [rcCluster_eq_of_reachable]
          have hxrep  :=
            (clusterRepresentative_none_iff ω (v a)).2 hfa
          have hyrep : clusterRepresentative ω (v b) ≠ none := by
            simp [clusterRepresentative, hfb]
          have hrepNe : clusterRepresentative ω (v a) ≠ clusterRepresentative ω (v b) := by
            grind
          constructor
          · simp_all
          · exact fun heq => (hrepNe heq).elim
        · rw [infiniteMergedSetoid_some_some]
          
          
          
          
          constructor
          · intro _
            exact ((clusterRepresentative_none_iff ω (v a)).2 hfa).trans ((clusterRepresentative_none_iff ω (v b)).2 hfb).symm
          · simp_all

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
        (infiniteWiredPartition (Option.map  fun a : ↥A => a.val ) ω)
        some (fun a : ↥A => ξ a.val) none (boundaryColor q i hi)) := by
  classical
  let ν : Measure (Set.Icc 1 q) :=
    ProbabilityTheory.uniformOn Set.univ
  let c₀  := boundaryColor q i hi
  let v : ↥A → Vertex := fun a => a.val
  let R  := infiniteWiredPartition (Option.map v) ω
  let rep  := wiredObservedRepresentative ω v
  let ξ'  := markedMap (fun a : ↥A => ξ a.val) c₀
  let Q := Quotient R
  let ghost : Q := Quotient.mk R none
  let Qnz := {c : Q // c ≠ ghost}
  let : Nonempty (Set.Icc 1 q) := by
                                    aesop
  
  
  
  
  
  
  
  have hcomap (a b : Option ↥A) :
      R.comap (markedMap some none) a b ↔ R a b := by
    cases a <;> cases b <;> rfl
  have hcompKernel :
       R.comap (markedMap some none) ≤ Setoid.ker (markedMap (fun a  => ξ a.val) c₀)  ↔
        R ≤ Setoid.ker ξ' := by
    constructor
    · intro h a b hab
      
      simpa  using  h (x := a) (y := b) ((hcomap a b).2 hab) 
    · intro h a b hab
      
      simpa  using  h (x := a) (y := b) ((hcomap a b).1 hab) 
  let E  :=
    {u | ∀ a , (rep a).elim c₀ u = ξ' a}
  have hE : E = {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
      clusterColoring c₀ (ω, u) a.val = ξ a.val} := by
    ext u
    
    constructor
    · intro hu a
      simpa [rep, ξ', wiredObservedRepresentative, clusterColoring, markedMap] using
        hu (some a)
    · intro hu a
      cases a with
      | none => rfl
      | some a =>
        grind [wiredObservedRepresentative, clusterColoring, markedMap]
  rw [← hE]
  by_cases hcompat : R ≤ Setoid.ker ξ'
  · 
    rw [iidFieldMeasure_pinnedObservedColoring_of_compatible ν R rep (wiredObservedRepresentative_eq_iff ω v)
      (by
         simp [rep, wiredObservedRepresentative]) c₀ ξ'  rfl  hcompat]
    have hatom (c : Set.Icc 1 q) : ν {c} = (q : ℝ≥0∞)⁻¹ := pottsUniformColor_singleton q c
    simp_rw [hatom]
    rw [Finset.prod_const]
    
    have hcardF  :=
      Nat.card_eq_fintype_card.symm.trans (by
                                             calc
                                               Nat.card Qnz = Fintype.card Qnz := Nat.card_eq_fintype_card
                                               _ = Fintype.card Q - Fintype.card {c : Q // c = ghost} :=
                                                 Fintype.card_subtype_compl  fun c : Q => c = ghost 
                                               _ = Nat.card Q - 1 := by simp )
    have hcount : observedClassCount R (markedMap some none) = Nat.card Q := by
      rw [observedClassCount_eq_range]
      have hrange : Set.range (Quotient.mk R ∘ markedMap some none) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro c
        obtain ⟨a, rfl⟩ := Quotient.exists_rep c
        exact ⟨a, by
          
          cases a <;> rfl⟩
      rw [hrange]
      simp [Q]
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_left ((hcompKernel).2 hcompat), hcount]
    rw [PottsDiscontinuity.Potts.card_pottsColors]
    rw [Finset.card_univ, hcardF]
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
    rw [ENNReal.ofReal_inv_of_pos (pow_pos hqreal _), ENNReal.ofReal_pow hqreal.le,
      ENNReal.ofReal_natCast]
    exact ENNReal.inv_pow.symm
  · 
    have hEmpty : E = ∅ := by
      ext u
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hu
      apply hcompat
      intro a b hab
      calc
        ξ' a = (rep a).elim c₀ u := (hu a).symm
        _ = (rep b).elim c₀ u := congrArg (fun x  => x.elim c₀ u)
          (((wiredObservedRepresentative_eq_iff ω v) a b).mp hab)
        _ = ξ' b := hu b
    rw [hEmpty]
    
    
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_right  fun hk => hcompat ((hcompKernel).1 hk) ]
    simp

/-- Integrating a finite partition kernel over the first factor gives its
finite weighted sum. -/
theorem lintegral_finitePartitionKernel {Ω A : Type*} [MeasurableSpace Ω]
    [Fintype A] [Fintype (Setoid A)] (μ : Measure Ω)
    (r : Ω → Setoid A) (K : Setoid A → ℝ≥0∞)
    (hr : ∀ R, MeasurableSet {ω | r ω = R}) :
    ∫⁻ ω, K (r ω) ∂μ =
      ∑ R : Setoid A, K R * μ {ω | r ω = R} := by
  
  let f  := fun R =>
    {ω | r ω = R}.indicator  fun _ => K R 
  have hf : (fun ω => K (r ω)) = fun ω => ∑ R : Setoid A, f R ω := by
    funext ω
    
    rw [Finset.sum_eq_single (r ω)]
    all_goals aesop
  rw [hf, lintegral_finsetSum]
  · aesop
  · intro R hR
    exact measurable_const.indicator (hr R)

theorem toReal_lintegral_finitePartitionKernel {Ω A : Type*} [MeasurableSpace Ω]
    [Finite A] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Setoid A) (K : Setoid A → ℝ)
    (hK : ∀ R, 0 ≤ K R)
    (hr : ∀ R, MeasurableSet {ω | r ω = R}) :
    (∫⁻ ω, ENNReal.ofReal (K (r ω)) ∂μ).toReal =
      PottsDiscontinuity.Potts.partitionExpectation μ r K := by
  
  let : Fintype A := Fintype.ofFinite A
  let : Fintype (Setoid A) := Fintype.ofFinite (Setoid A)
  rw [lintegral_finitePartitionKernel μ r (fun R => ENNReal.ofReal (K R)) hr]
  
  rw [ENNReal.toReal_sum  fun R hR =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _) ]
  apply Finset.sum_congr rfl
  intro R hR
  calc
    (ENNReal.ofReal (K R) * μ {ω | r ω = R}).toReal =
        K R * (μ {ω | r ω = R}).toReal := by simp [hK R]
    _ = (μ {ω | r ω = R}).toReal * K R := mul_comm _ _

end
end PottsDiscontinuity.PottsThm
