module

public import Mathlib
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Tactic
public import proofs.RAF.Asymptotics.RAFAsymptoticsAll
public import proofs.RAF.Concrete.RAFConcreteAll
public import proofs.RAF.Core.RAFAll
public import proofs.RAF.Polymer.RAFPolymerAll

@[expose] public section

namespace HordijkSteelThreshold

section
open RAF RAF.Polymer RAF.Concrete

/-- In the concrete reversible polymer model, the apparent extra class of
reverse-food gateways adds nothing: a reaction is a gateway exactly when both
canonical split factors are food molecules. -/
theorem revSeedReaction_iff_food_factors {n t : Nat} (r : Reaction n) :
    RevSeedReaction (binaryPolymerCRS n t) r ↔
      reactionLeft r ∈ binaryFood n t ∧ reactionRight r ∈ binaryFood n t := by
    constructor
    · intro h
      rcases h with hl | hr
      · constructor
        · exact hl (by simp [binaryPolymerCRS])
        · exact hl (by simp [binaryPolymerCRS])
      · have hp : reactionProduct r ∈ binaryFood n t :=
          hr (by simp [binaryPolymerCRS])
        have hp_len : reactionProductLength r ≤ t := by
          simpa [binaryFood] using hp
        constructor <;> simp only [binaryFood, Finset.mem_filter, Finset.mem_univ, true_and]
        · rw [molLength_reactionLeft]
          linarith [reaction_length_add r]
        · rw [molLength_reactionRight]
          linarith [reaction_length_add r]
    · rintro ⟨hl, hr⟩
      refine Or.inl ?_
      intro x hx
      simp [binaryPolymerCRS, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · simpa [binaryPolymerCRS, hx] using hl
      · simpa [binaryPolymerCRS, hx] using hr
theorem revSeedReaction_iff_factor_lengths {n t : Nat} (r : Reaction n) :
    RevSeedReaction (binaryPolymerCRS n t) r ↔
      reactionLeftLength r ≤ t ∧ reactionRightLength r ≤ t := by
  rw [revSeedReaction_iff_food_factors]
  simp [binaryFood]

theorem card_gateway_four_binary_t2 :
    Fintype.card (PolymerSeedReaction 4 2) = 36 := by
  decide

private def restrictReactionFour {n : Nat} (r : PolymerSeedReaction n 2) :
    Reaction 4 :=
  ⟨⟨r.1.1.val, by
      have h := (revSeedReaction_iff_factor_lengths r.1).mp r.2
      change r.1.2.2.val + 1 ≤ 2 ∧ r.1.1.val - r.1.2.2.val ≤ 2 at h
      omega⟩, r.1.2⟩

private theorem restrictReactionFour_lengths {n : Nat}
    (r : PolymerSeedReaction n 2) :
    reactionLeftLength (restrictReactionFour r) = reactionLeftLength r.1 ∧
      reactionRightLength (restrictReactionFour r) = reactionRightLength r.1 := by
  constructor <;> rfl

private def restrictGatewayFour {n : Nat} (r : PolymerSeedReaction n 2) :
    PolymerSeedReaction 4 2 :=
  ⟨restrictReactionFour r, by
    rw [revSeedReaction_iff_factor_lengths]
    rw [(restrictReactionFour_lengths r).1, (restrictReactionFour_lengths r).2]
    exact (revSeedReaction_iff_factor_lengths r.1).mp r.2⟩

private theorem restrictGatewayFour_injective {n : Nat} :
    Function.Injective (restrictGatewayFour (n := n)) := by
  intro a b hab
  apply Subtype.ext
  apply Sigma.ext
  · exact Fin.ext (congrArg (fun z : PolymerSeedReaction 4 2 => z.1.1.val) hab)
  · cases a with
    | mk a ha =>
      cases b with
      | mk b hb =>
        cases a with
        | mk ai ad =>
          cases b with
          | mk bi bd =>
            simp_all [restrictGatewayFour, restrictReactionFour]

private def liftReactionFour {n : Nat} (hn : 4 ≤ n) (r : Reaction 4) :
    Reaction n :=
  ⟨⟨r.1.val, lt_of_lt_of_le r.1.isLt hn⟩, r.2⟩

private theorem liftReactionFour_lengths {n : Nat} (hn : 4 ≤ n)
    (r : Reaction 4) :
    reactionLeftLength (liftReactionFour hn r) = reactionLeftLength r ∧
      reactionRightLength (liftReactionFour hn r) = reactionRightLength r := by
  constructor <;> rfl

private def liftGatewayFour {n : Nat} (hn : 4 ≤ n)
    (r : PolymerSeedReaction 4 2) : PolymerSeedReaction n 2 :=
  ⟨liftReactionFour hn r.1, by
    rw [revSeedReaction_iff_factor_lengths]
    rw [(liftReactionFour_lengths hn r.1).1, (liftReactionFour_lengths hn r.1).2]
    exact (revSeedReaction_iff_factor_lengths r.1).mp r.2⟩

private theorem liftGatewayFour_injective {n : Nat} (hn : 4 ≤ n) :
    Function.Injective (liftGatewayFour hn) := by
  intro a b hab
  apply Subtype.ext
  apply Sigma.ext
  · exact Fin.ext (congrArg (fun z : PolymerSeedReaction n 2 => z.1.1.val) hab)
  · cases a with
    | mk a ha =>
      cases b with
      | mk b hb =>
        cases a with
        | mk ai ad =>
          cases b with
          | mk bi bd =>
            simp_all [liftGatewayFour, liftReactionFour]

/-- The exact concrete gateway count.  It is stable once all products of two
food molecules (length at most four) are present. -/
theorem card_concrete_gateway_binary_t2 {n : Nat} (hn : 4 ≤ n) :
    Fintype.card (PolymerSeedReaction n 2) = 36 := by
  have hle : Fintype.card (PolymerSeedReaction n 2) ≤
      Fintype.card (PolymerSeedReaction 4 2) :=
    Fintype.card_le_of_injective restrictGatewayFour restrictGatewayFour_injective
  have hge : Fintype.card (PolymerSeedReaction 4 2) ≤
      Fintype.card (PolymerSeedReaction n 2) :=
    Fintype.card_le_of_injective (liftGatewayFour hn) (liftGatewayFour_injective hn)
  rw [card_gateway_four_binary_t2] at hle hge
  omega

end

section
open RAF.Polymer

private theorem sum_binary_words (n : Nat) :
    (∑ k ∈ Finset.range n, 2 ^ (k + 1)) = 2 ^ (n + 1) - 2 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      omega
/-- Exact number of nonempty binary words of length at most `n`. -/
theorem card_molecules_exact (n : Nat) :
    Fintype.card (Molecule n) = 2 ^ (n + 1) - 2 := by
      rw [card_molecule_sigma, Fin.sum_univ_eq_sum_range fun k : Nat => 2 ^ (k + 1)]
      exact sum_binary_words n
private theorem sum_binary_reactions_shift (m : Nat) :
    (∑ k ∈ Finset.range (m + 2), 2 ^ (k + 1) * k) =
      m * 2 ^ (m + 3) + 4 := by
      induction m with
      | zero => norm_num
      | succ m ih =>
        rw [show m + 1 + 2 = (m + 2) + 1 by omega, Finset.sum_range_succ, ih, show m + 2 + 1 = m + 3 by omega, show m + 1 + 3 = m + 4 by omega, pow_succ]
        ring
/-- Exact split-position reversible reaction count. -/
theorem card_reactions_exact {n : Nat} (hn : 2 ≤ n) :
    Fintype.card (Reaction n) = (n - 2) * 2 ^ (n + 1) + 4 := by
      rw [card_reaction_sigma, Fin.sum_univ_eq_sum_range fun k : Nat => 2 ^ (k + 1) * k]
      have h := sum_binary_reactions_shift (n - 2)
      have hn2 : n - 2 + 2 = n := by omega
      have hn3 : n - 2 + 3 = n + 1 := by omega
      simpa [hn2, hn3] using h
end

section
open Filter Topology
open RAF.Polymer RAF.Concrete

theorem card_molecule_tendsto_atTop :
    Tendsto (fun n : Nat => Fintype.card (Molecule n)) atTop atTop := by
  refine Tendsto.congr' ?_ RAF.Asymptotics.binaryCardX_tendsto
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [card_molecules_exact]
  rfl

end

section
open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer

abbrev AmbientCoord (n : Nat) := Molecule n × Reaction n

/-- The one-coordinate law underlying the set-Bernoulli catalysis sample. -/
noncomputable def ambientCoordLaw (p : I) : Measure Prop :=
  toNNReal p • Measure.dirac True + toNNReal (σ p) • Measure.dirac False

noncomputable instance ambientCoordLaw_isProbability (p : I) :
    IsProbabilityMeasure (ambientCoordLaw p) := by
  constructor
  simp [ambientCoordLaw]

/-- The uncurried product presentation of uniform catalysis coordinates. -/
noncomputable def ambientPiMeasure (n : Nat) (lambda : ℝ) :
    Measure (AmbientCoord n → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw (RAF.Concrete.catalysisP n lambda))

noncomputable instance ambientPiMeasure_isProbability (n : Nat) (lambda : ℝ) :
    IsProbabilityMeasure (ambientPiMeasure n lambda) := by
  unfold ambientPiMeasure
  infer_instance

theorem ambientCoordinate_iIndep (n : Nat) (lambda : ℝ) :
    iIndepFun (fun z (ω : AmbientCoord n → Prop) => ω z)
      (ambientPiMeasure n lambda) := by
    unfold ambientPiMeasure
    exact iIndepFun_infinitePi fun _ => measurable_id
end

section
open Filter Topology MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- A reaction is open relative to a specified prospective internal catalyst
pool.  Unlike ambient openness, this predicate retains the catalyst pool that
must eventually lie in the marked core. -/
def catalystPoolOpen {n : Nat} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) (r : Reaction n) : Prop :=
  ∃ x ∈ C, ω (x, r)

end

section
open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- Coordinate block queried by a finite family of reactions against a fixed
prospective catalyst pool. -/
def catalystPoolFamilyBlock {n : Nat} (C : Finset (Molecule n))
    (R : Finset (Reaction n)) : Finset (AmbientCoord n) :=
  C.product R

/-- At least one reaction in a finite family is catalyzed by the prospective
internal pool. -/
def catalystPoolFamilyOpen {n : Nat} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) (R : Finset (Reaction n)) : Prop :=
  ∃ r ∈ R, catalystPoolOpen ω C r

theorem catalystPoolFamilyBlock_disjoint {n : Nat}
    (C : Finset (Molecule n)) {R S : Finset (Reaction n)}
    (hRS : Disjoint R S) :
    Disjoint (catalystPoolFamilyBlock C R)
      (catalystPoolFamilyBlock C S) := by
    rw [Finset.disjoint_left]
    intro z hzR hzS
    exact Finset.disjoint_left.mp hRS ((Finset.mem_product.mp hzR).2) ((Finset.mem_product.mp hzS).2)

/-- An arbitrary measurable predicate on one complete reaction column is
independent of arbitrary predicates on a disjoint family of other columns. -/
theorem columnEvent_indep_remaining {n : ℕ} (lambda : ℝ)
    (E : Reaction n → (Molecule n → Prop) → Prop)
    (r : Reaction n) (S : Finset (Reaction n)) (hr : r ∉ S) :
    IndepFun (fun ω : AmbientCoord n → Prop => E r (fun x => ω (x, r)))
      (fun ω => ∀ s ∈ S, E s (fun x => ω (x, s)))
      (ambientPiMeasure n lambda) := by
          let B := catalystPoolFamilyBlock (Finset.univ : Finset (Molecule n)) {r}
          let D := catalystPoolFamilyBlock (Finset.univ : Finset (Molecule n)) S
          have hdis : Disjoint B D :=
            catalystPoolFamilyBlock_disjoint Finset.univ (Finset.disjoint_singleton_left.mpr hr)
          have ht := (ambientCoordinate_iIndep n lambda).indepFun_finset B D hdis
            fun _ => measurable_pi_apply _
          let f : (B → Prop) → Prop := fun v =>
            E r fun x => v ⟨(x, r), by simp [B, catalystPoolFamilyBlock]⟩
          let g : (D → Prop) → Prop := fun v =>
            ∀ s, ∀ hs : s ∈ S,
              E s fun x => v ⟨(x, s), by simp [D, catalystPoolFamilyBlock, hs]⟩
          exact ht.comp (measurable_of_finite f) (measurable_of_finite g)
/-- Full product formula, not just pairwise independence. Predicates may
encode an entire fixed history of nested-pool observations in each column. -/
theorem measure_columnEvents {n : ℕ} (lambda : ℝ)
    (E : Reaction n → (Molecule n → Prop) → Prop) (S : Finset (Reaction n)) :
    ambientPiMeasure n lambda {ω | ∀ r ∈ S, E r (fun x => ω (x, r))} =
      ∏ r ∈ S, ambientPiMeasure n lambda {ω | E r (fun x => ω (x, r))} := by
            induction S using Finset.induction_on with
            | empty => simp
            | @insert r S hr ih =>
              have hi := (columnEvent_indep_remaining lambda E r S hr).measure_inter_preimage_eq_mul
                  {True} {True}
                  (MeasurableSet.singleton True) (MeasurableSet.singleton True)
              have he : {ω : AmbientCoord n → Prop | ∀ s ∈ insert r S, E s fun x => ω (x, s)} =
                  {ω | E r fun x => ω (x, r)} ∩
                  {ω | ∀ s ∈ S, E s fun x => ω (x, s)} := by
                ext ω
                simp
              rw [he, Finset.prod_insert hr]
              simpa [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true,
                ih] using hi
end

section
open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

@[simp] theorem ambientCoordLaw_false (p : I) :
    ambientCoordLaw p {False} = toNNReal (σ p) := by
  simp [ambientCoordLaw]

/-- Every coordinate in a finite block is closed. -/
def catalystBlockClosed {n : Nat} (ω : AmbientCoord n → Prop)
    (B : Finset (AmbientCoord n)) : Prop :=
  ∀ z ∈ B, ω z = False

/-- Exact finite-cylinder probability of a closed catalysis block. -/
theorem measure_catalystBlockClosed {n : Nat} (lambda : ℝ)
    (B : Finset (AmbientCoord n)) :
    ambientPiMeasure n lambda {ω | catalystBlockClosed ω B} =
      ∏ _z ∈ B, (toNNReal (σ (catalysisP n lambda)) : ENNReal) := by
    have hprod := (ambientCoordinate_iIndep n lambda).measure_inter_preimage_eq_mul B
        (sets := fun _z : AmbientCoord n => ({False} : Set Prop))
        fun _ _ => MeasurableSet.singleton False
    rw [show {ω | catalystBlockClosed ω B} =
        ⋂ z ∈ B, (fun ω : AmbientCoord n → Prop => ω z) ⁻¹' {False} by
          ext ω
          simp [catalystBlockClosed]]
    rw [hprod]
    apply Finset.prod_congr rfl
    intro z hz
    rw [ambientPiMeasure, ← Measure.map_apply (measurable_pi_apply z)
      (MeasurableSet.singleton False), Measure.infinitePi_map_eval]
    exact ambientCoordLaw_false (catalysisP n lambda)
theorem measure_catalystBlockClosed_card {n : Nat} (lambda : ℝ)
    (B : Finset (AmbientCoord n)) :
    ambientPiMeasure n lambda {ω | catalystBlockClosed ω B} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ B.card := by
  rw [measure_catalystBlockClosed]
  simp

/-- Exact probability that at least one coordinate in a fixed catalyst-pool
reaction-family block is open. -/
theorem measure_catalystPoolFamilyOpen {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) (R : Finset (Reaction n)) :
    ambientPiMeasure n lambda {ω | catalystPoolFamilyOpen ω C R} =
      1 - ∏ _z ∈ catalystPoolFamilyBlock C R,
        (toNNReal (σ (catalysisP n lambda)) : ENNReal) := by
      let B := catalystPoolFamilyBlock C R
      have hevent : {ω | catalystPoolFamilyOpen ω C R} =
          ({ω | catalystBlockClosed ω B})ᶜ := by
        ext ω
        simp [Set.mem_ofPred_eq, Set.mem_compl_iff]
        constructor
        · rintro ⟨r, hr, x, hx, hω⟩ hclosed
          have hz := hclosed (x, r) (by
            simp [B, catalystPoolFamilyBlock, hx, hr])
          exact hz ▸ hω
        · intro hnotClosed
          by_contra hnotOpen
          apply hnotClosed
          intro z hz
          have hzmem := Finset.mem_product.mp hz
          have hfalse : ¬ω (z.1, z.2) := by
            intro hω
            apply hnotOpen
            exact ⟨z.2, hzmem.2, z.1, hzmem.1, hω⟩
          exact propext ⟨fun h => (hfalse h).elim, fun h => h.elim⟩
      have hclosed : MeasurableSet {ω | catalystBlockClosed ω B} := by
        have hpre := (measurable_of_finite
          fun ω => catalystBlockClosed ω B) (MeasurableSet.singleton True)
        convert hpre using 1
        ext ω
        simp
      rw [hevent, measure_compl hclosed (by simp), measure_univ,
        measure_catalystBlockClosed]
/-- Cardinality form of the exact family-open law.  This is the expression
used by the shell estimates: a family has `|C| |R|` fresh coordinates. -/
theorem measure_catalystPoolFamilyOpen_card {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) (R : Finset (Reaction n)) :
    ambientPiMeasure n lambda {ω | catalystPoolFamilyOpen ω C R} =
      1 - (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (C.card * R.card) := by
  rw [measure_catalystPoolFamilyOpen]
  simp [catalystPoolFamilyBlock]

/-- Simultaneous failure of all target-indexed reaction families.  This is the
exact closed-coordinate event carried by a fixed first-barrier witness. -/
def catalystPoolFamiliesClosed {n : Nat} {ι : Type*}
    (ω : AmbientCoord n → Prop) (C : Finset (Molecule n))
    (T : Finset ι) (R : ι → Finset (Reaction n)) : Prop :=
  ∀ i ∈ T, ¬ catalystPoolFamilyOpen ω C (R i)

/-- Exact probability cost of a fixed first-barrier witness.  No independence
between target histories is assumed: their actual reaction union determines
the number of distinct coordinates that the witness closes. -/
theorem measure_catalystPoolFamiliesClosed {n : Nat} {ι : Type*}
    [DecidableEq ι] (lambda : ℝ) (C : Finset (Molecule n))
    (T : Finset ι) (R : ι → Finset (Reaction n)) :
    ambientPiMeasure n lambda
        {ω | catalystPoolFamiliesClosed ω C T R} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (C.card * (T.biUnion R).card) := by
      rw [show {ω | catalystPoolFamiliesClosed ω C T R} =
          {ω | catalystBlockClosed ω (C.product (T.biUnion R))} by
            ext ω
            simp [Set.mem_ofPred_eq]
            constructor
            · intro h z hz
              have hzprod := Finset.mem_product.mp hz
              obtain ⟨i, hi, hr⟩ := Finset.mem_biUnion.mp hzprod.2
              have hnot : ¬ω (z.1, z.2) := by
                intro hω
                apply h i hi
                exact ⟨z.2, hr, z.1, hzprod.1, hω⟩
              exact propext ⟨fun hω => (hnot hω).elim, fun hf => hf.elim⟩
            · intro hclosed i hi hopen
              obtain ⟨r, hr, x, hx, hω⟩ := hopen
              have hz : (x, r) ∈ C.product (T.biUnion R) := by
                exact Finset.mem_product.mpr
                  ⟨hx, Finset.mem_biUnion.mpr ⟨i, hi, hr⟩⟩
              have hfalse := hclosed (x, r) hz
              exact hfalse ▸ hω]
      rw [measure_catalystBlockClosed_card]
      simp
/-- Exact closed probability for one fixed reaction family. -/
theorem measure_catalystPoolFamilyClosed {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) (R : Finset (Reaction n)) :
    ambientPiMeasure n lambda {ω | ¬catalystPoolFamilyOpen ω C R} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (C.card * R.card) := by
    simpa [catalystPoolFamiliesClosed] using
      (measure_catalystPoolFamiliesClosed (ι := Unit) lambda C
        ({()} : Finset Unit) fun _ => R)
end

section

/-- Deterministic nested sets realizing every possible finite pool size. -/
noncomputable def finiteInitialSegment (X : Type*) [Fintype X] (k : ℕ) : Finset X :=
  (Finset.univ.filter (fun i : Fin (Fintype.card X) => i.val < k)).map
    (Fintype.equivFin X).symm.toEmbedding

theorem finiteInitialSegment_mono (X : Type*) [Fintype X] :
    Monotone (finiteInitialSegment X) := by
  intro a b hab
  apply Finset.map_subset_map.mpr
  intro i hi
  have hp := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hp.1, hp.2.trans_le hab⟩

theorem card_finiteInitialSegment (X : Type*) [Fintype X]
    (k : ℕ) (hk : k ≤ Fintype.card X) :
    (finiteInitialSegment X k).card = k := by
  rw [finiteInitialSegment, Finset.card_map, Fin.card_filter_val_lt, min_eq_right hk]

end

section
open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- A fixed reaction family has no retained catalyst but has a catalyst in the
preceding deleted cohort. Pools here are deterministic, not conditionally sampled. -/
def cohortFamilyLost {n : Nat} (ω : AmbientCoord n → Prop)
    (K D : Finset (Molecule n)) (R : Finset (Reaction n)) : Prop :=
  ¬ catalystPoolFamilyOpen ω K R ∧ catalystPoolFamilyOpen ω D R

theorem catalystPoolFamilyOpen_union {n : Nat} (ω : AmbientCoord n → Prop)
    (K D : Finset (Molecule n)) (R : Finset (Reaction n)) :
    catalystPoolFamilyOpen ω (K ∪ D) R ↔
      catalystPoolFamilyOpen ω K R ∨ catalystPoolFamilyOpen ω D R := by
    simp [catalystPoolFamilyOpen, catalystPoolOpen, Finset.mem_union]
    aesop
/-- Exact fixed-cohort cost, valid even for overlapping pools. The family event
requires one deleted-cohort witness somewhere in R, not one for every r in R. -/
theorem measure_cohortFamilyLost {n : Nat} (lambda : ℝ)
    (K D : Finset (Molecule n)) (R : Finset (Reaction n)) :
    ambientPiMeasure n lambda {ω | cohortFamilyLost ω K D R} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (K.card * R.card) -
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ ((K ∪ D).card * R.card) := by
    have he : {ω : AmbientCoord n → Prop | cohortFamilyLost ω K D R} =
        {ω | ¬ catalystPoolFamilyOpen ω K R} \
        {ω | ¬ catalystPoolFamilyOpen ω (K ∪ D) R} := by
      ext ω
      simp [Set.mem_ofPred_eq, Set.mem_sdiff, cohortFamilyLost,
        catalystPoolFamilyOpen_union]
      tauto
    have hs : {ω : AmbientCoord n → Prop | ¬ catalystPoolFamilyOpen ω (K ∪ D) R} ⊆
        {ω | ¬ catalystPoolFamilyOpen ω K R} := by
      intro ω h hk
      exact h ((catalystPoolFamilyOpen_union ω K D R).mpr (Or.inl hk))
    have hm : MeasurableSet
        {ω : AmbientCoord n → Prop | ¬ catalystPoolFamilyOpen ω (K ∪ D) R} := by
      exact Set.Finite.measurableSet (Set.toFinite _)
    rw [he, measure_sdiff hs hm.nullMeasurableSet (measure_ne_top _ _),
      measure_catalystPoolFamilyClosed, measure_catalystPoolFamilyClosed]
/-- A decreasing Boolean history is on exactly before its death index.
Death zero means initially absent; death T+1 means surviving the horizon. -/
def decreasingHistory (P : ℕ → Prop) (T d : ℕ) : Prop :=
  ∀ t ≤ T, P t ↔ t < d

theorem decreasingHistory_zero_iff (P : ℕ → Prop) (T : ℕ)
    (hP : ∀ a b, a ≤ b → P b → P a) :
    decreasingHistory P T 0 ↔ ¬ P 0 := by
  constructor
  · intro h hp
    exact Nat.not_lt_zero 0 ((h 0 (Nat.zero_le T)).mp hp)
  · intro h t _
    constructor
    · intro hp
      exact (h (hP 0 t (Nat.zero_le t) hp)).elim
    · omega

theorem decreasingHistory_survives_iff (P : ℕ → Prop) (T : ℕ)
    (hP : ∀ a b, a ≤ b → P b → P a) :
    decreasingHistory P T (T + 1) ↔ P T := by
  constructor
  · intro h
    exact (h T le_rfl).mpr (Nat.lt_succ_self T)
  · intro h t ht
    exact ⟨fun _ => by omega, fun _ => hP t T ht h⟩

theorem decreasingHistory_dies_iff (P : ℕ → Prop) (T d : ℕ)
    (hd : 0 < d) (hdT : d ≤ T)
    (hP : ∀ a b, a ≤ b → P b → P a) :
    decreasingHistory P T d ↔ ¬ P d ∧ P (d - 1) := by
  constructor
  · intro h
    exact ⟨fun hp => (Nat.lt_irrefl d) ((h d hdT).mp hp),
      (h (d - 1) (by omega)).mpr (by omega)⟩
  · rintro ⟨hoff, hon⟩ t _
    constructor
    · intro hp
      by_contra h
      exact hoff (hP d t (by omega) hp)
    · intro ht
      exact hP t (d - 1) (by omega) hon

def catalystColumnHistory {n : ℕ} (ω : AmbientCoord n → Prop)
    (C : ℕ → Finset (Molecule n)) (r : Reaction n) (T d : ℕ) : Prop :=
  decreasingHistory (fun t => catalystPoolOpen ω (C t) r) T d

theorem catalystPoolOpen_of_antitone {n : ℕ} (ω : AmbientCoord n → Prop)
    (C : ℕ → Finset (Molecule n)) (hC : Antitone C) (r : Reaction n)
    (a b : ℕ) (hab : a ≤ b) :
    catalystPoolOpen ω (C b) r → catalystPoolOpen ω (C a) r := by
  rintro ⟨x, hx, hω⟩
  exact ⟨x, hC hab hx, hω⟩

theorem measure_catalystColumnHistory_zero {n : ℕ} (lambda : ℝ)
    (C : ℕ → Finset (Molecule n)) (hC : Antitone C) (r : Reaction n) (T : ℕ) :
    ambientPiMeasure n lambda {ω | catalystColumnHistory ω C r T 0} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (C 0).card := by
    have he : {ω | catalystColumnHistory ω C r T 0} =
        {ω | ¬ catalystPoolFamilyOpen ω (C 0) {r}} := by
      ext ω
      simpa [Set.mem_ofPred_eq, catalystColumnHistory,
        catalystPoolFamilyOpen, Finset.mem_singleton, exists_eq_left] using
        decreasingHistory_zero_iff (fun t => catalystPoolOpen ω (C t) r) T
          (catalystPoolOpen_of_antitone ω C hC r)
    rw [he, measure_catalystPoolFamilyClosed]
    simp
theorem measure_catalystColumnHistory_survives {n : ℕ} (lambda : ℝ)
    (C : ℕ → Finset (Molecule n)) (hC : Antitone C) (r : Reaction n) (T : ℕ) :
    ambientPiMeasure n lambda {ω | catalystColumnHistory ω C r T (T + 1)} =
      1 - (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (C T).card := by
    have he : {ω | catalystColumnHistory ω C r T (T + 1)} =
        {ω | catalystPoolFamilyOpen ω (C T) {r}} := by
      ext ω
      simpa [Set.mem_ofPred_eq, catalystColumnHistory,
        catalystPoolFamilyOpen, Finset.mem_singleton, exists_eq_left] using
        decreasingHistory_survives_iff (fun t => catalystPoolOpen ω (C t) r) T
          (catalystPoolOpen_of_antitone ω C hC r)
    rw [he, measure_catalystPoolFamilyOpen_card]
    simp
/-- The full nested history imposes only the last positive and first negative
column observations. Its exact probability depends only on those pool sizes. -/
theorem measure_catalystColumnHistory_dies {n : ℕ} (lambda : ℝ)
    (C : ℕ → Finset (Molecule n)) (hC : Antitone C) (r : Reaction n)
    (T d : ℕ) (hd : 0 < d) (hdT : d ≤ T) :
    ambientPiMeasure n lambda {ω | catalystColumnHistory ω C r T d} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (C d).card -
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^ (C (d - 1)).card := by
    have he : {ω | catalystColumnHistory ω C r T d} =
        {ω | cohortFamilyLost ω (C d) (C (d - 1)) {r}} := by
      ext ω
      simpa [Set.mem_ofPred_eq, catalystColumnHistory, cohortFamilyLost,
        catalystPoolFamilyOpen, Finset.mem_singleton, exists_eq_left] using
        decreasingHistory_dies_iff (fun t => catalystPoolOpen ω (C t) r) T d hd hdT
          (catalystPoolOpen_of_antitone ω C hC r)
    rw [he, measure_cohortFamilyLost,
      Finset.union_eq_right.mpr (hC (by omega : d - 1 ≤ d))]
    simp
/-- Exact column weight, including initially absent and horizon-surviving
columns. Only cardinalities of deterministic nested pools enter. -/
noncomputable def columnHistoryWeight (q : ENNReal) (sizes : ℕ → ℕ) (T d : ℕ) : ENNReal :=
  if d = 0 then q ^ sizes 0
  else if T < d then 1 - q ^ sizes T
  else q ^ sizes d - q ^ sizes (d - 1)

theorem measure_catalystColumnHistory {n : ℕ} (lambda : ℝ)
    (C : ℕ → Finset (Molecule n)) (hC : Antitone C) (r : Reaction n)
    (T d : ℕ) (hd : d ≤ T + 1) :
    ambientPiMeasure n lambda {ω | catalystColumnHistory ω C r T d} =
      columnHistoryWeight (toNNReal (σ (catalysisP n lambda)))
        (fun t => (C t).card) T d := by
      by_cases hz : d = 0
      · subst d
        simpa only [columnHistoryWeight, ite_true] using
          measure_catalystColumnHistory_zero lambda C hC r T
      · by_cases hs : T < d
        · have hd' : d = T + 1 := by omega
          subst d
          simpa [columnHistoryWeight, ite_eq_right hz, ite_eq_left hs] using
            measure_catalystColumnHistory_survives lambda C hC r T
        · simpa [columnHistoryWeight, ite_eq_right hz, ite_eq_right hs] using
            measure_catalystColumnHistory_dies lambda C hC r T d (by omega) (by omega)
/-- Probability of an entire fixed nested-pool history, with independent
reaction columns but no independence assumption between time steps. -/
theorem measure_catalystHistories {n : ℕ} (lambda : ℝ)
    (C : ℕ → Finset (Molecule n)) (hC : Antitone C)
    (S : Finset (Reaction n)) (T : ℕ) (death : Reaction n → ℕ)
    (hdeath : ∀ r ∈ S, death r ≤ T + 1) :
    ambientPiMeasure n lambda {ω | ∀ r ∈ S, catalystColumnHistory ω C r T (death r)} =
      ∏ r ∈ S, columnHistoryWeight (toNNReal (σ (catalysisP n lambda)))
        (fun t => (C t).card) T (death r) := by
    have hp := measure_columnEvents lambda
      (fun r v => decreasingHistory (fun t => ∃ x ∈ C t, v x) T (death r)) S
    change ambientPiMeasure n lambda
        {ω | ∀ r ∈ S, catalystColumnHistory ω C r T (death r)} =
        ∏ r ∈ S, ambientPiMeasure n lambda
          {ω | catalystColumnHistory ω C r T (death r)} at hp
    rw [hp]
    exact Finset.prod_congr rfl fun r hr =>
      measure_catalystColumnHistory lambda C hC r T (death r) (hdeath r hr)
/-- Cardinality-preserving replacement of deterministic nested pools leaves
every complete column history probability unchanged. This is the source-side
identity required to replace prescribed pools by ordered prefixes. -/
theorem measure_catalystHistories_eq_of_card {n : ℕ} (lambda : ℝ)
    (C D : ℕ → Finset (Molecule n)) (hC : Antitone C) (hD : Antitone D)
    (hcard : ∀ t, (C t).card = (D t).card)
    (S : Finset (Reaction n)) (T : ℕ) (death : Reaction n → ℕ)
    (hdeath : ∀ r ∈ S, death r ≤ T + 1) :
    ambientPiMeasure n lambda {ω | ∀ r ∈ S, catalystColumnHistory ω C r T (death r)} =
      ambientPiMeasure n lambda {ω | ∀ r ∈ S, catalystColumnHistory ω D r T (death r)} := by
    rw [measure_catalystHistories lambda C hC S T death hdeath,
      measure_catalystHistories lambda D hD S T death hdeath]
    rw [(funext hcard)]

end

section

/-- Active reaction history for a deterministic pool-response map. -/
def peelingActiveAt {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X) :
    ℕ → Finset R
  | 0 => response Finset.univ
  | t + 1 => response (closure (peelingActiveAt response closure t))

/-- Pools computed from a prescribed active-set history, before testing it
against a random field. These are deterministic when the history is fixed. -/
def prescribedPoolAt {X R : Type*} [Fintype X]
    (closure : Finset R → Finset X) (history : ℕ → Finset R) : ℕ → Finset X
  | 0 => Finset.univ
  | t + 1 => closure (history t)

/-- A history event is exactly the intersection of its fixed-pool response
constraints. There is no extra random closure-consistency condition. -/
theorem peeling_history_iff {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X)
    (history : ℕ → Finset R) (T : ℕ) :
    (∀ t ≤ T, peelingActiveAt response closure t = history t) ↔
      ∀ t ≤ T, response (prescribedPoolAt closure history t) = history t := by
      constructor
      · intro h t ht
        cases t with
        | zero => exact h 0 ht
        | succ t =>
          have hp := h t (by omega)
          simpa [peelingActiveAt, hp, prescribedPoolAt] using h (t + 1) ht
      · intro h t
        induction t with
        | zero => exact h 0
        | succ t ih =>
          intro ht
          have hp := ih (by omega)
          simpa [peelingActiveAt, hp, prescribedPoolAt] using h (t + 1) ht
theorem peelingActiveAt_antitone {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X)
    (hresponse : Monotone response) (hclosure : Monotone closure) :
    Antitone (peelingActiveAt response closure) := by
  apply antitone_nat_of_succ_le
  intro t
  induction t with
  | zero => exact hresponse (Finset.subset_univ _)
  | succ t ih => exact hresponse (hclosure ih)

theorem prescribedPoolAt_antitone {X R : Type*} [Fintype X]
    (closure : Finset R → Finset X) (hclosure : Monotone closure)
    (history : ℕ → Finset R) (hhistory : Antitone history) :
    Antitone (prescribedPoolAt closure history) := by
  apply antitone_nat_of_succ_le
  intro t
  cases t with
  | zero => exact Finset.subset_univ _
  | succ t => exact hclosure (hhistory (Nat.le_succ t))

end

section
open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- Every decreasing finite Boolean history has a bounded death index. -/
theorem exists_history_death (P : ℕ → Prop) (T : ℕ)
    (hP : ∀ a b, a ≤ b → P b → P a) :
    ∃ d ≤ T + 1, ∀ t ≤ T, P t ↔ t < d := by
  classical
  by_cases h : ∃ t, t ≤ T ∧ ¬ P t
  · refine ⟨Nat.find h, (Nat.find_spec h).1.trans (Nat.le_succ T), ?_⟩
    intro t ht
    constructor
    · intro hp
      by_contra hn
      exact (Nat.find_spec h).2 (hP (Nat.find h) t (by omega) hp)
    · intro ht'
      by_contra hn
      exact (Nat.find_min h ht') ⟨ht, hn⟩
  · refine ⟨T + 1, le_rfl, ?_⟩
    intro t ht
    exact ⟨fun _ => by omega, fun _ => by
      by_contra hn
      exact h ⟨t, ht, hn⟩⟩

noncomputable def catalystActive {n : ℕ} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) : Finset (Reaction n) := by
  classical
  exact Finset.univ.filter (catalystPoolOpen ω C)

@[simp] theorem mem_catalystActive {n : ℕ} (ω : AmbientCoord n → Prop)
    (C : Finset (Molecule n)) (r : Reaction n) :
    r ∈ catalystActive ω C ↔ catalystPoolOpen ω C r := by
    simp [catalystActive]
theorem catalystActive_mono {n : ℕ} (ω : AmbientCoord n → Prop) :
    Monotone (catalystActive ω) := by
  intro C D h r hr
  obtain ⟨x, hx, hω⟩ := (mem_catalystActive ω C r).mp hr
  exact (mem_catalystActive ω D r).mpr ⟨x, h hx, hω⟩

/-- Convert a prescribed process history into fixed column constraints.
The transform can be identity (source) or cardinality-indexed prefixes. -/
theorem peeling_event_eq_column_histories {n : ℕ}
    (transform : Finset (Molecule n) → Finset (Molecule n))
    (closure : Finset (Reaction n) → Finset (Molecule n))
    (history : ℕ → Finset (Reaction n)) (T : ℕ) (death : Reaction n → ℕ)
    (hdeath : ∀ r t, t ≤ T → (r ∈ history t ↔ t < death r)) :
    {ω : AmbientCoord n → Prop | ∀ t ≤ T,
      peelingActiveAt (fun C => catalystActive ω (transform C)) closure t = history t} =
    {ω | ∀ r ∈ (Finset.univ : Finset (Reaction n)),
      catalystColumnHistory ω (fun t => transform (prescribedPoolAt closure history t))
        r T (death r)} := by
    ext ω
    simp [Set.mem_ofPred_eq, peeling_history_iff, Finset.mem_univ, forall_const]
    constructor
    · intro h r t ht
      rw [← hdeath r t ht, ← h t ht, mem_catalystActive]
    · intro h t ht
      apply Finset.ext
      intro r
      rw [mem_catalystActive]
      exact (h r t ht).trans (hdeath r t ht).symm
/-- The source process and its ordered-initialSegment replacement give exactly the
same probability to every prescribed decreasing active-set history.
The initialSegment assumptions are deterministic; adaptive independence is not assumed. -/
theorem peeling_history_probability_eq_prefix {n : ℕ} (lambda : ℝ)
    (closure : Finset (Reaction n) → Finset (Molecule n)) (hclosure : Monotone closure)
    (initialSegment : ℕ → Finset (Molecule n)) (hprefix : Monotone initialSegment)
    (hcard : ∀ k ≤ Fintype.card (Molecule n), (initialSegment k).card = k)
    (history : ℕ → Finset (Reaction n)) (hhistory : Antitone history) (T : ℕ) :
    ambientPiMeasure n lambda {ω | ∀ t ≤ T,
      peelingActiveAt (catalystActive ω) closure t = history t} =
    ambientPiMeasure n lambda {ω | ∀ t ≤ T,
      peelingActiveAt (fun C => catalystActive ω (initialSegment C.card)) closure t = history t} := by
      have hd : ∀ r : Reaction n, ∃ d ≤ T + 1,
          ∀ t ≤ T, r ∈ history t ↔ t < d := by
        intro r
        exact exists_history_death (fun t => r ∈ history t) T
          fun _ _ hab hr => hhistory hab hr
      choose death hbound hpattern using hd
      have he := peeling_event_eq_column_histories (n := n) id closure history T death hpattern
      have hp := peeling_event_eq_column_histories (n := n)
        (fun C => initialSegment C.card) closure history T death hpattern
      change {ω | ∀ t ≤ T, peelingActiveAt (catalystActive ω) closure t = history t} =
          {ω | ∀ r ∈ (Finset.univ : Finset (Reaction n)),
            catalystColumnHistory ω (prescribedPoolAt closure history) r T (death r)} at he
      rw [he, hp]
      have hc := prescribedPoolAt_antitone closure hclosure history hhistory
      apply measure_catalystHistories_eq_of_card lambda _ _ hc
      · intro a b hab
        exact hprefix (Finset.card_le_card (hc hab))
      · intro t
        exact (hcard _ (Finset.card_le_univ _)).symm
      · intro r _
        exact hbound r
theorem history_clamp_antitone_of_match {R : Type*}
    (A H : ℕ → Finset R) (hA : Antitone A) (T : ℕ)
    (hmatch : ∀ t ≤ T, A t = H t) :
    Antitone (fun t => H (min t T)) := by
  intro a b hab
  change H (min b T) ⊆ H (min a T)
  rw [← hmatch (min b T) (min_le_right _ _),
    ← hmatch (min a T) (min_le_right _ _)]
  exact hA (min_le_min_right T hab)

/-- Equality for arbitrary prescribed histories. Nondecreasing histories on
the finite horizon have probability zero for both processes. -/
theorem peeling_history_probability_eq_prefix_any {n : ℕ} (lambda : ℝ)
    (closure : Finset (Reaction n) → Finset (Molecule n)) (hclosure : Monotone closure)
    (initialSegment : ℕ → Finset (Molecule n)) (hprefix : Monotone initialSegment)
    (hcard : ∀ k ≤ Fintype.card (Molecule n), (initialSegment k).card = k)
    (history : ℕ → Finset (Reaction n)) (T : ℕ) :
    ambientPiMeasure n lambda {ω | ∀ t ≤ T,
      peelingActiveAt (catalystActive ω) closure t = history t} =
    ambientPiMeasure n lambda {ω | ∀ t ≤ T,
      peelingActiveAt (fun C => catalystActive ω (initialSegment C.card)) closure t = history t} := by
            by_cases hg : Antitone fun t => history (min t T)
            · have h := peeling_history_probability_eq_prefix lambda closure hclosure
                initialSegment hprefix hcard (fun t => history (min t T)) hg T
              have he (A : ℕ → Finset (Reaction n)) :
                  (∀ t ≤ T, A t = history (min t T)) ↔ (∀ t ≤ T, A t = history t) := by
                constructor <;> intro h t ht <;> simpa [min_eq_left ht] using h t ht
              simpa [he] using h
            · have hs : {ω : AmbientCoord n → Prop | ∀ t ≤ T,
                  peelingActiveAt (catalystActive ω) closure t = history t} = ∅ := by
                apply Set.eq_empty_iff_forall_notMem.mpr
                intro ω h
                exact hg (history_clamp_antitone_of_match _ history
                  (peelingActiveAt_antitone _ closure (catalystActive_mono ω) hclosure) T h)
              have hp : {ω : AmbientCoord n → Prop | ∀ t ≤ T,
                  peelingActiveAt (fun C => catalystActive ω (initialSegment C.card)) closure t = history t} = ∅ := by
                apply Set.eq_empty_iff_forall_notMem.mpr
                intro ω h
                have hm : Monotone fun C : Finset (Molecule n) =>
                    catalystActive ω (initialSegment C.card) := by
                  intro C D hCD
                  exact catalystActive_mono ω (hprefix (Finset.card_le_card hCD))
                exact hg (history_clamp_antitone_of_match _ history
                  (peelingActiveAt_antitone _ closure hm hclosure) T h)
              rw [hs, hp]
def activeTrace {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X) (T : ℕ) :
    Fin (T + 1) → R → Prop :=
  fun t r => r ∈ peelingActiveAt response closure t.val

noncomputable def traceHistory {R : Type*} [Fintype R] {T : ℕ}
    (H : Fin (T + 1) → R → Prop) (t : ℕ) : Finset R := by
  classical
  exact if ht : t < T + 1 then Finset.univ.filter (H ⟨t, ht⟩) else ∅

theorem activeTrace_eq_iff {X R : Type*} [Fintype X] [Fintype R]
    (response : Finset X → Finset R) (closure : Finset R → Finset X) (T : ℕ)
    (H : Fin (T + 1) → R → Prop) :
    activeTrace response closure T = H ↔
      ∀ t ≤ T, peelingActiveAt response closure t = traceHistory H t := by
    constructor
    · intro h t ht
      apply Finset.ext
      intro r
      have he := congrFun (congrFun h ⟨t, by omega⟩) r
      simpa only [traceHistory, dite_eq_left (by omega : t < T + 1),
        Finset.mem_filter, Finset.mem_univ, true_and, activeTrace] using
        (eq_iff_iff.mp he)
    · intro h
      funext t r
      apply propext
      change r ∈ peelingActiveAt response closure t.val ↔ H t r
      rw [h t.val (by omega)]
      simp only [traceHistory, dite_eq_left t.isLt, Finset.mem_filter,
        Finset.mem_univ, true_and]
/-- Exact finite-dimensional distributional replacement in the literal
molecule-reaction product measure, with a constructed ordered-prefix model.
This asserts equality in law, not equality for the same catalyst sample. -/
theorem activeTrace_map_eq_scalar {n : ℕ} (lambda : ℝ)
    (closure : Finset (Reaction n) → Finset (Molecule n))
    (hclosure : Monotone closure) (T : ℕ) :
    (ambientPiMeasure n lambda).map (fun ω => activeTrace (catalystActive ω) closure T) =
      (ambientPiMeasure n lambda).map (fun ω => activeTrace
        (fun C => catalystActive ω (finiteInitialSegment (Molecule n) C.card)) closure T) := by
    apply Measure.ext_of_singleton
    intro H
    rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton H),
      Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton H)]
    have hs := peeling_history_probability_eq_prefix_any lambda closure hclosure
      (finiteInitialSegment (Molecule n)) (finiteInitialSegment_mono (Molecule n))
      (card_finiteInitialSegment (Molecule n)) (traceHistory H) T
    simpa [Set.preimage, Set.mem_singleton_iff, activeTrace_eq_iff] using hs

/-- Every statistic of the active set at a fixed time transfers through the
compiled trace law. No measurable structure on finsets needs to be chosen. -/
theorem measure_peeling_statistic_eq_scalar {n : ℕ} (lambda : ℝ)
    (closure : Finset (Reaction n) → Finset (Molecule n)) (hclosure : Monotone closure)
    (T : ℕ) (stat : Finset (Reaction n) → Prop) :
    ambientPiMeasure n lambda {ω | stat (peelingActiveAt (catalystActive ω) closure T)} =
    ambientPiMeasure n lambda {ω | stat (peelingActiveAt
      (fun C => catalystActive ω (finiteInitialSegment (Molecule n) C.card)) closure T)} := by
      classical
      let E : Set (Fin (T + 1) → Reaction n → Prop) :=
        {H | stat (Finset.univ.filter (H ⟨T, Nat.lt_succ_self T⟩))}
      have hfilterActive
          (response : Finset (Molecule n) → Finset (Reaction n)) :
          Finset.univ.filter
              (activeTrace response closure T ⟨T, Nat.lt_succ_self T⟩) =
            peelingActiveAt response closure T := by
        ext r
        simp [Finset.mem_filter, Finset.mem_univ, true_and, activeTrace]
      have he := congrArg (fun μ : Measure (Fin (T + 1) → Reaction n → Prop) => μ E)
        (activeTrace_map_eq_scalar lambda closure hclosure T)
      rw [Measure.map_apply (measurable_of_finite _) (Set.Finite.measurableSet (Set.toFinite E)),
        Measure.map_apply (measurable_of_finite _) (Set.Finite.measurableSet (Set.toFinite E))] at he
      simpa [E, Set.preimage, Set.mem_ofPred_eq, hfilterActive] using he
theorem prefix_static_barrier {n : ℕ} (ω : AmbientCoord n → Prop)
    (closure : Finset (Reaction n) → Finset (Molecule n)) (hclosure : Monotone closure)
    (k : ℕ) (hk : k ≤ (closure
      (catalystActive ω (finiteInitialSegment (Molecule n) k))).card) (T : ℕ) :
    closure (catalystActive ω (finiteInitialSegment (Molecule n) k)) ⊆
      closure (peelingActiveAt
        (fun C => catalystActive ω (finiteInitialSegment (Molecule n) C.card)) closure T) := by
        have hq : Monotone fun j => catalystActive ω (finiteInitialSegment (Molecule n) j) :=
          (catalystActive_mono ω).comp (finiteInitialSegment_mono (Molecule n))
        induction T with
        | zero =>
          have hb := hk.trans (Finset.card_le_univ _)
          simpa [peelingActiveAt, Finset.card_univ] using hclosure (hq hb)
        | succ T ih =>
          exact hclosure (hq (hk.trans (Finset.card_le_card ih)))
/-- A static iid reaction field tested against a deterministic k-element
catalyst pool lower-bounds source closure mass at every peeling time. -/
theorem measure_source_mass_ge_static {n : ℕ} (lambda : ℝ)
    (closure : Finset (Reaction n) → Finset (Molecule n)) (hclosure : Monotone closure)
    (k T : ℕ) :
    ambientPiMeasure n lambda {ω | k ≤ (closure
      (catalystActive ω (finiteInitialSegment (Molecule n) k))).card} ≤
    ambientPiMeasure n lambda {ω | k ≤
      (closure (peelingActiveAt (catalystActive ω) closure T)).card} := by
    rw [measure_peeling_statistic_eq_scalar lambda closure hclosure T
      fun A => k ≤ (closure A).card]
    apply measure_mono
    intro ω hω
    exact hω.trans (Finset.card_le_card (prefix_static_barrier ω closure hclosure k hω T))
end

section
open Classical MeasureTheory ProbabilityTheory

def detourFailed {R Ω : Type*} (field : R → Ω → Prop) (B : Finset R) (ω : Ω) : Prop :=
  ¬ ∀ r ∈ B, field r ω

theorem measure_detourOpen {R Ω : Type*} [Fintype R] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (field : R → Ω → Prop)
    (hind : iIndepFun field μ) (a : ENNReal)
    (hmarg : ∀ r, μ {ω | field r ω} = a) (B : Finset R) :
    μ {ω | ∀ r ∈ B, field r ω} = a^B.card := by
      have hprod := hind.measure_inter_preimage_eq_mul B
        (sets := fun _ : R => ({True} : Set Prop)) fun _ _ => MeasurableSet.singleton True
      have he : {ω | ∀ r ∈ B, field r ω} = ⋂ r ∈ B, (field r) ⁻¹' {True} := by
        ext ω
        simp
      rw [he, hprod]
      have hsingle (r : R) : μ ((field r) ⁻¹' {True}) = a := by
        simpa [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true] using hmarg r
      simp only [hsingle, Finset.prod_const]
theorem measure_detourFailed {R Ω : Type*} [Fintype R] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (field : R → Ω → Prop)
    (hind : iIndepFun field μ) (hmeas : ∀ r, Measurable (field r)) (a : ENNReal)
    (hmarg : ∀ r, μ {ω | field r ω} = a) (B : Finset R) :
    μ {ω | detourFailed field B ω} = 1-a^B.card := by
      have hm : MeasurableSet {ω | ∀ r ∈ B, field r ω} := by
        have he : {ω | ∀ r ∈ B, field r ω} = ⋂ r ∈ B, (field r) ⁻¹' {True} := by
          ext ω
          simp
        rw [he]
        exact MeasurableSet.iInter fun r => MeasurableSet.iInter fun _ =>
          (MeasurableSet.singleton True).preimage (hmeas r)
      change μ ({ω | ∀ r ∈ B, field r ω}ᶜ) = _
      rw [measure_compl hm (measure_ne_top _ _), measure_univ,
        measure_detourOpen μ field hind a hmarg B]
theorem detourFailed_indep_remaining {I R Ω : Type*} [Fintype R] [MeasurableSpace Ω]
    (μ : Measure Ω) (field : R → Ω → Prop) (hind : iIndepFun field μ)
    (hmeas : ∀ r, Measurable (field r)) (support : I → Finset R)
    (i : I) (T : Finset I) (hdis : ∀ j ∈ T, Disjoint (support i) (support j)) :
    IndepFun (detourFailed field (support i))
      (fun ω => ∀ j ∈ T, detourFailed field (support j) ω) μ := by
      let D := T.biUnion support
      have hBD : Disjoint (support i) D := by
        apply Finset.disjoint_left.mpr
        intro r hri hrD
        obtain ⟨j, hj, hrj⟩ := Finset.mem_biUnion.mp hrD
        exact Finset.disjoint_left.mp (hdis j hj) hri hrj
      let f : (support i → Prop) → Prop := fun v => ¬ ∀ r, ∀ hr : r ∈ support i, v ⟨r,hr⟩
      let g : (D → Prop) → Prop := fun v => ∀ j, ∀ hj : j ∈ T,
        ¬ ∀ r, ∀ hr : r ∈ support j, v ⟨r, Finset.mem_biUnion.mpr ⟨j,hj,hr⟩⟩
      exact (hind.indepFun_finset (support i) D hBD hmeas).comp (measurable_of_finite f) (measurable_of_finite g)
/-- Full product formula for disjoint fixed reaction supports. Selection has
already occurred deterministically; no independence of effective basic edges is used. -/
theorem measure_disjoint_detours_failed {I R Ω : Type*} [Fintype R] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (field : R → Ω → Prop)
    (hind : iIndepFun field μ) (hmeas : ∀ r, Measurable (field r))
    (a : ENNReal) (hmarg : ∀ r, μ {ω | field r ω} = a)
    (support : I → Finset R) (T : Finset I)
    (hdis : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j)) :
    μ {ω | ∀ i ∈ T, detourFailed field (support i) ω} =
      ∏ i ∈ T, (1-a^(support i).card) := by
      induction T using Finset.induction_on with
      | empty => simp
      | @insert i T hi ih =>
        have hsep : ∀ j ∈ T, Disjoint (support i) (support j) := by
          intro j hj
          exact hdis i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
            (by intro he; exact hi (he ▸ hj))
        have ht : ∀ j ∈ T, ∀ k ∈ T, j ≠ k → Disjoint (support j) (support k) := by
          intro j hj k hk hne
          exact hdis j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne
        have hp := (detourFailed_indep_remaining μ field hind hmeas support i T hsep).measure_inter_preimage_eq_mul {True} {True}
            (MeasurableSet.singleton True) (MeasurableSet.singleton True)
        have he : {ω | ∀ j ∈ insert i T, detourFailed field (support j) ω} =
            {ω | detourFailed field (support i) ω} ∩
            {ω | ∀ j ∈ T, detourFailed field (support j) ω} := by ext ω; simp
        rw [he, Finset.prod_insert hi]
        simpa [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true,
          ih ht, measure_detourFailed μ field hind hmeas a hmarg] using hp
theorem measure_disjoint_detours_failed_le {I R Ω : Type*} [Fintype R] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (field : R → Ω → Prop)
    (hind : iIndepFun field μ) (hmeas : ∀ r, Measurable (field r))
    (a : ENNReal) (ha : a ≤ 1) (hmarg : ∀ r, μ {ω | field r ω} = a)
    (support : I → Finset R) (T : Finset I)
    (hdis : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j))
    (hsize : ∀ i ∈ T, (support i).card ≤ 2) :
    μ {ω | ∀ i ∈ T, detourFailed field (support i) ω} ≤ (1-a^2)^T.card := by
  rw [measure_disjoint_detours_failed μ field hind hmeas a hmarg support T hdis]
  calc
    _ ≤ ∏ _i ∈ T, (1-a^2) := by
      apply Finset.prod_le_prod
      intro i hi
      apply tsub_le_tsub_left
      exact pow_le_pow_of_le_one (zero_le : 0 ≤ a) ha (hsize i hi)
    _ = _ := by simp

end

section
open Classical

noncomputable def detourConflicts {I R : Type*} (S : Finset I)
    (support : I → Finset R) (i : I) : Finset I :=
  (S.erase i).filter (fun j => ¬ Disjoint (support i) (support j))

/-- Two coordinates per support and incidence three give at most four other conflicts. -/
theorem detourConflicts_card {I R : Type*} (S : Finset I) (support : I → Finset R)
    (i : I) (hi : i ∈ S) (hsize : (support i).card ≤ 2)
    (huse : ∀ r, (S.filter (fun j => r ∈ support j)).card ≤ 3) :
    (detourConflicts S support i).card ≤ 4 := by
                have hsub : detourConflicts S support i ⊆
                    (support i).biUnion fun r => (S.filter fun j => r ∈ support j).erase i := by
                  intro j hj
                  obtain ⟨hjS, hnot⟩ := Finset.mem_filter.mp hj
                  obtain ⟨r, hri, hrj⟩ := Finset.not_disjoint_iff.mp hnot
                  exact Finset.mem_biUnion.mpr ⟨r, hri, Finset.mem_erase.mpr
                    ⟨(Finset.mem_erase.mp hjS).1, Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hjS).2, hrj⟩⟩⟩
                calc
                  _ ≤ ((support i).biUnion fun r => (S.filter fun j => r ∈ support j).erase i).card :=
                    Finset.card_le_card hsub
                  _ ≤ ∑ r ∈ support i, ((S.filter fun j => r ∈ support j).erase i).card :=
                    Finset.card_biUnion_le
                  _ ≤ ∑ _r ∈ support i, 2 := by
                    apply Finset.sum_le_sum
                    intro r hr
                    have hm : i ∈ S.filter fun j => r ∈ support j := Finset.mem_filter.mpr ⟨hi, hr⟩
                    have hc := Finset.card_erase_add_one hm
                    have hu := huse r
                    omega
                  _ ≤ 4 := by simp only [Finset.sum_const, Nat.nsmul_eq_mul]; omega
/-- A finite family of supports of size at most two, each coordinate used at
most three times, has a pairwise-disjoint subfamily of at least one fifth its size. -/
theorem exists_disjoint_detours {I R : Type*} (S : Finset I) (support : I → Finset R)
    (hsize : ∀ i ∈ S, (support i).card ≤ 2)
    (huse : ∀ r, (S.filter (fun j => r ∈ support j)).card ≤ 3) :
    ∃ T ⊆ S, (∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j)) ∧
      S.card ≤ 5*T.card := by
            let family := S.powerset.filter fun T =>
              decide (∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j)) = true
            have hempty : ∅ ∈ family := by simp [family]
            obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image family Finset.card ⟨∅, hempty⟩
            obtain ⟨hTS, hdisBool⟩ := Finset.mem_filter.mp hT
            have hdis := of_decide_eq_true hdisBool
            have hsub := Finset.mem_powerset.mp hTS
            refine ⟨T, hsub, hdis, ?_⟩
            have hcover : S ⊆ T.biUnion fun j => insert j (detourConflicts S support j) := by
              intro i hi
              by_cases hiT : i ∈ T
              · exact Finset.mem_biUnion.mpr ⟨i, hiT, Finset.mem_insert_self _ _⟩
              · have hex : ∃ j ∈ T, ¬ Disjoint (support i) (support j) := by
                  by_contra hn
                  push Not at hn
                  have hnew : insert i T ∈ family := by
                    apply Finset.mem_filter.mpr
                    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi hsub), ?_⟩
                    apply decide_eq_true
                    intro j hj k hk hne
                    rcases Finset.mem_insert.mp hj with hji | hjT
                    · rcases Finset.mem_insert.mp hk with hki | hkT
                      · exact False.elim (hne (hji.trans hki.symm))
                      · rw [hji]
                        exact hn k hkT
                    · rcases Finset.mem_insert.mp hk with hki | hkT
                      · rw [hki]
                        exact (hn j hjT).symm
                      · exact hdis j hjT k hkT hne
                  have hc := hmax (insert i T) hnew
                  rw [Finset.card_insert_of_notMem hiT] at hc
                  omega
                obtain ⟨j, hj, hij⟩ := hex
                apply Finset.mem_biUnion.mpr
                refine ⟨j, hj, Finset.mem_insert_of_mem ?_⟩
                apply Finset.mem_filter.mpr
                refine ⟨Finset.mem_erase.mpr ⟨?_, hi⟩, ?_⟩
                · intro he
                  exact hiT (he ▸ hj)
                · intro h
                  exact hij h.symm
            calc
              S.card ≤ (T.biUnion fun j => insert j (detourConflicts S support j)).card :=
                Finset.card_le_card hcover
              _ ≤ ∑ j ∈ T, (insert j (detourConflicts S support j)).card := Finset.card_biUnion_le
              _ ≤ ∑ _j ∈ T, 5 := by
                apply Finset.sum_le_sum
                intro j hj
                have hc := detourConflicts_card S support j (hsub hj) (hsize j (hsub hj)) huse
                exact (Finset.card_insert_le _ _).trans (by omega)
              _ = 5*T.card := by simp [Nat.mul_comm]
end

section

/-- Big-endian code, matching the source's mixed-radix concatenation. -/
def binaryWordCode : List Bool → ℕ
  | [] => 0
  | b :: s => (if b then 2 ^ s.length else 0) + binaryWordCode s

theorem binaryWordCode_lt (s : List Bool) : binaryWordCode s < 2 ^ s.length := by
  induction s with
  | nil => simp [binaryWordCode]
  | cons b s ih =>
    cases b <;> simp only [binaryWordCode, Bool.false_eq_true, ite_false,
      ite_true, zero_add, List.length_cons, pow_succ] <;> omega

theorem binaryWordCode_append (s t : List Bool) :
    binaryWordCode (s ++ t) = binaryWordCode s * 2 ^ t.length + binaryWordCode t := by
  induction s with
  | nil => simp [binaryWordCode]
  | cons b s ih =>
    cases b <;> simp [binaryWordCode, ih, List.length_append, pow_add, Nat.add_mul, Nat.add_assoc]

def listWord (s : List Bool) : RAF.Polymer.Word s.length :=
  ⟨binaryWordCode s, binaryWordCode_lt s⟩

theorem binaryWordCode_append_div (s t : List Bool) :
    binaryWordCode (s ++ t) / 2 ^ t.length = binaryWordCode s := by
  rw [binaryWordCode_append, Nat.mul_comm, Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt (binaryWordCode_lt t), Nat.add_zero]

theorem binaryWordCode_append_mod (s t : List Bool) :
    binaryWordCode (s ++ t) % 2 ^ t.length = binaryWordCode t := by
  rw [binaryWordCode_append, Nat.mul_add_mod_self_right,
    Nat.mod_eq_of_lt (binaryWordCode_lt t)]

/-- Length together with code uniquely determines the binary word. -/
theorem binaryWordCode_injective_length {s t : List Bool}
    (hlen : s.length = t.length) (hcode : binaryWordCode s = binaryWordCode t) : s = t := by
  induction s generalizing t with
  | nil => cases t <;> simp_all
  | cons b s ih =>
    cases t with
    | nil => simp at hlen
    | cons c t =>
      have hst : s.length = t.length := by simpa using hlen
      have hs := binaryWordCode_lt s
      have ht := binaryWordCode_lt t
      rw [← hst] at ht
      cases b <;> cases c <;> simp only [binaryWordCode, Bool.false_eq_true,
        ite_false, ite_true, zero_add, ← hst] at hcode
      · exact congrArg (List.cons false) (ih hst hcode)
      · omega
      · omega
      · exact congrArg (List.cons true) (ih hst (by omega))

theorem exists_binaryWordCode (m k : ℕ) (hk : k < 2 ^ m) :
    ∃ s : List Bool, s.length = m ∧ binaryWordCode s = k := by
  induction m generalizing k with
  | zero =>
    have he : k = 0 := by simpa using hk
    exact ⟨[], rfl, he.symm⟩
  | succ m ih =>
    by_cases hlow : k < 2 ^ m
    · obtain ⟨s, hs, hc⟩ := ih k hlow
      refine ⟨false :: s, by simp [hs], ?_⟩
      simpa [binaryWordCode] using hc
    · have ht : k - 2 ^ m < 2 ^ m := by
        rw [pow_succ] at hk
        omega
      obtain ⟨s, hs, hc⟩ := ih (k - 2 ^ m) ht
      refine ⟨true :: s, by simp [hs], ?_⟩
      simp only [binaryWordCode, ite_true, hs, hc]
      omega

/-- A length-preserving bijection with the source's actual fixed-length
word type. This prevents dropping leading zeros or losing source words. -/
noncomputable def binaryListWordEquiv (m : ℕ) :
    {s : List Bool // s.length = m} ≃ RAF.Polymer.Word m :=
  Equiv.ofBijective
    (fun s => ⟨binaryWordCode s.val, by simpa only [s.property] using binaryWordCode_lt s.val⟩)
    (by
      constructor
      · intro s t h
        apply Subtype.ext
        exact binaryWordCode_injective_length (s.property.trans t.property.symm)
          (congrArg Fin.val h)
      · intro k
        obtain ⟨s, hs, hc⟩ := exists_binaryWordCode m k.val k.isLt
        exact ⟨⟨s, hs⟩, Fin.ext hc⟩)

end

section
open RAF.Polymer RAF.Concrete

noncomputable def moleculeWord {n : ℕ} (x : Molecule n) : List Bool :=
  ((binaryListWordEquiv (molLength x)).symm x.2).val

theorem moleculeWord_length {n : ℕ} (x : Molecule n) :
    (moleculeWord x).length = molLength x :=
  ((binaryListWordEquiv (molLength x)).symm x.2).property

theorem binaryWordCode_moleculeWord {n : ℕ} (x : Molecule n) :
    binaryWordCode (moleculeWord x) = x.2.val := by
  exact congrArg Fin.val ((binaryListWordEquiv (molLength x)).apply_symm_apply x.2)

theorem reactionLeft_code_div {n : ℕ} (r : Reaction n) :
    (reactionLeft r).2.val = r.2.1.val / 2 ^ reactionRightLength r := by
  rfl

theorem reactionRight_code_mod {n : ℕ} (r : Reaction n) :
    (reactionRight r).2.val = r.2.1.val % 2 ^ reactionRightLength r := by
  rfl

/-- Decoding a literal source reaction gives exactly its recorded left
substring; split-position identities have not been quotiented. -/
theorem moleculeWord_reactionLeft {n : ℕ} (r : Reaction n) :
    moleculeWord (reactionLeft r) =
      (moleculeWord (reactionProduct r)).take (reactionLeftLength r) := by
  let s := moleculeWord (reactionProduct r)
  have hlen : s.length = reactionProductLength r := moleculeWord_length _
  have hdrop : (s.drop (reactionLeftLength r)).length = reactionRightLength r := by
    rw [List.length_drop, hlen]
    have h := reaction_length_add r
    omega
  apply binaryWordCode_injective_length
  · rw [moleculeWord_length, molLength_reactionLeft, List.length_take]
    change reactionLeftLength r = min (reactionLeftLength r) s.length
    rw [hlen, min_eq_left (by have h := reaction_length_add r; omega)]
  · rw [binaryWordCode_moleculeWord, reactionLeft_code_div]
    have hc := binaryWordCode_append_div (s.take (reactionLeftLength r))
      (s.drop (reactionLeftLength r))
    rw [List.take_append_drop, hdrop] at hc
    rw [show binaryWordCode s = r.2.1.val from binaryWordCode_moleculeWord _] at hc
    exact hc

/-- The right endpoint is exactly the complementary source substring. -/
theorem moleculeWord_reactionRight {n : ℕ} (r : Reaction n) :
    moleculeWord (reactionRight r) =
      (moleculeWord (reactionProduct r)).drop (reactionLeftLength r) := by
  let s := moleculeWord (reactionProduct r)
  have hdrop : (s.drop (reactionLeftLength r)).length = reactionRightLength r := by
    rw [List.length_drop, moleculeWord_length, molLength_reactionProduct]
    have h := reaction_length_add r
    omega
  apply binaryWordCode_injective_length
  · rw [moleculeWord_length, molLength_reactionRight]
    exact hdrop.symm
  · rw [binaryWordCode_moleculeWord, reactionRight_code_mod]
    have hc := binaryWordCode_append_mod (s.take (reactionLeftLength r))
      (s.drop (reactionLeftLength r))
    rw [List.take_append_drop, hdrop] at hc
    rw [show binaryWordCode s = r.2.1.val from binaryWordCode_moleculeWord _] at hc
    exact hc

end

section

private theorem xor_pair_cancel (a b c : Bool) :
    ((a ^^ b) ^^ ((b ^^ c) ^^ c)) = a := by
  simp_all
private theorem xor_diamond_left (a b c d e f : Bool)
    (hcd : (c ^^ d) = e) (hdiamond : (((f ^^ a) ^^ e) ^^ b) = false) :
    ((a ^^ c) ^^ (b ^^ d)) = f := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    simp_all

/-- Label a vertex by parity along its right-parent path. Root edges carry
zero, so extra recursion depth does not alter the intended path parity. -/
def diamondPotential {V : Type*} (right : V → V) (rightEdge : V → Bool) :
    ℕ → V → Bool
  | 0, _ => false
  | k + 1, v => rightEdge v ^^ diamondPotential right rightEdge k (right v)

/-- Local diamond parity integrates to a vertex potential. This gives an
explicit cut certificate, without cycle-space dimensions or linear algebra.
For word truncations, height is nonfood length and the parents commute. -/
theorem diamondPotential_edges {V : Type*}
    (left right : V → V) (height : V → ℕ)
    (leftEdge rightEdge : V → Bool)
    (hheight : ∀ v, height (right v) ≤ height v - 1)
    (hcommute : ∀ v, left (right v) = right (left v))
    (hroot : ∀ v, height v = 0 → leftEdge v = false ∧ rightEdge v = false)
    (hdiamond : ∀ v, (((leftEdge v ^^ rightEdge v) ^^ leftEdge (right v)) ^^
      rightEdge (left v)) = false)
    (k : ℕ) (v : V) (hv : height v ≤ k) :
    ((diamondPotential right rightEdge k v ^^
      diamondPotential right rightEdge k (left v)) = leftEdge v) ∧
    ((diamondPotential right rightEdge k v ^^
      diamondPotential right rightEdge k (right v)) = rightEdge v) := by
    induction k generalizing v with
    | zero =>
      obtain ⟨hl, hr⟩ := hroot v (by omega)
      simp [diamondPotential, hl, hr]
    | succ k ih =>
      have hp : height (right v) ≤ k := by
        have hh := hheight v
        omega
      obtain ⟨hil, hir⟩ := ih (right v) hp
      constructor
      · simp only [diamondPotential]
        apply xor_diamond_left _ _ _ _ (leftEdge (right v)) _
        · simpa [hcommute v] using hil
        · exact hdiamond v
      · simp only [diamondPotential]
        rw [← hir]
        exact xor_pair_cancel _ _ _
/-- Empty list represents the contracted food root. Nonfood parents remove
one end bit; a parent reaching the food cutoff is sent to that root. -/
def foodWordLeft (L : ℕ) (s : List Bool) : List Bool :=
  if s.length ≤ L + 1 then [] else s.tail

def foodWordRight (L : ℕ) (s : List Bool) : List Bool :=
  if s.length ≤ L + 1 then [] else s.dropLast

def foodWordHeight (L : ℕ) (s : List Bool) : ℕ := s.length - L

theorem foodWordParents_commute (L : ℕ) (s : List Bool) :
    foodWordLeft L (foodWordRight L s) = foodWordRight L (foodWordLeft L s) := by
    by_cases h : s.length ≤ L + 1
    · simp [foodWordLeft, foodWordRight, h]
    · simp [foodWordLeft, foodWordRight, ite_eq_right h, List.length_dropLast,
        List.length_tail]
      split_ifs <;> simp [List.tail_dropLast]
theorem foodWordRight_height (L : ℕ) (s : List Bool) :
    foodWordHeight L (foodWordRight L s) ≤ foodWordHeight L s - 1 := by
    simp [foodWordHeight, foodWordRight]
    split_ifs <;> simp only [List.length_nil, List.length_dropLast] <;> omega

end

section
open RAF.Polymer RAF.Concrete

def contractFoodWord (L : ℕ) (s : List Bool) : List Bool :=
  if s.length ≤ L then [] else s

theorem contractFoodWord_tail (L : ℕ) (s : List Bool) :
    contractFoodWord L s.tail = foodWordLeft L s := by
    have h : s.length - 1 ≤ L ↔ s.length ≤ L + 1 := by omega
    simp [contractFoodWord, foodWordLeft, List.length_tail, h]
theorem contractFoodWord_dropLast (L : ℕ) (s : List Bool) :
    contractFoodWord L s.dropLast = foodWordRight L s := by
    have h : s.length - 1 ≤ L ↔ s.length ≤ L + 1 := by omega
    simp [contractFoodWord, foodWordRight, List.length_dropLast, h]

/-- Arbitrary literal split, retaining its product and split-position identity. -/
def sourceSplitReaction {n : ℕ} (x : Molecule n) (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) : Reaction n :=
  ⟨x.1, x.2, ⟨k - 1, by unfold molLength at hkm; omega⟩⟩

@[simp] theorem sourceSplitReaction_product {n : ℕ} (x : Molecule n) (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) :
    reactionProduct (sourceSplitReaction x k hk hkm) = x := rfl

@[simp] theorem sourceSplitReaction_leftLength {n : ℕ} (x : Molecule n) (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) :
    reactionLeftLength (sourceSplitReaction x k hk hkm) = k := by
  change k - 1 + 1 = k
  omega

/-- The side indicates deletion of a short suffix (true) or prefix (false). -/
def sourceShortSplit {n : ℕ} (x : Molecule n) (side : Bool) (k : ℕ) : ℕ :=
  if side then molLength x - k else k

def sourceShortReaction {n : ℕ} (x : Molecule n) (side : Bool) (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) : Reaction n :=
  sourceSplitReaction x (sourceShortSplit x side k)
    (by cases side <;> simp only [sourceShortSplit, Bool.false_eq_true, ↓reduceIte] <;> omega)
    (by cases side <;> simp only [sourceShortSplit, Bool.false_eq_true, ↓reduceIte] <;> omega)

@[simp] theorem sourceShortReaction_product {n : ℕ} (x : Molecule n)
    (side : Bool) (k : ℕ) (hk : 0 < k) (hkm : k < molLength x) :
    reactionProduct (sourceShortReaction x side k hk hkm) = x := rfl

@[simp] theorem sourceShortReaction_leftLength {n : ℕ} (x : Molecule n)
    (side : Bool) (k : ℕ) (hk : 0 < k) (hkm : k < molLength x) :
    reactionLeftLength (sourceShortReaction x side k hk hkm) =
      sourceShortSplit x side k := sourceSplitReaction_leftLength _ _ _ _

/-- A width smaller than half the product separates the two orientations.
Thus the normalized short-edge coordinates do not create fictitious independent IDs. -/
theorem sourceShortReaction_coordinates {n w : ℕ} (x y : Molecule n)
    (sx sy : Bool) (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (hkw : k ≤ w) (hlw : l ≤ w) (hx : 2*w < molLength x)
    (hy : 2*w < molLength y)
    (he : sourceShortReaction x sx k hk (by omega) =
      sourceShortReaction y sy l hl (by omega)) :
    x = y ∧ sx = sy ∧ k = l := by
      have hxy := congrArg reactionProduct he
      simp [sourceShortReaction_product] at hxy
      subst y
      have hs := congrArg reactionLeftLength he
      simp [sourceShortReaction_leftLength] at hs
      refine ⟨rfl, ?_⟩
      cases sx <;> cases sy <;> simp_all [sourceShortSplit] <;> omega
end

section

/-- The actual finite word-graph vertex domain: one food root and only
nonfood words inside the ambient cap. No parity condition above N is needed. -/
def BoundedFoodWord (L N : ℕ) :=
  {s : List Bool // s = [] ∨ (L < s.length ∧ s.length ≤ N)}

theorem boundedFoodWord_length_le {L N : ℕ} (v : BoundedFoodWord L N) :
    v.val.length ≤ N := by
  rcases v.property with h | h
  · simp [h]
  · exact h.2

instance boundedFoodWord_finite (L N : ℕ) : Finite (BoundedFoodWord L N) := by
  let encode : BoundedFoodWord L N → (Σ m : Fin (N + 1), RAF.Polymer.Word m.val) :=
    fun v => ⟨⟨v.val.length, Nat.lt_succ_of_le (boundedFoodWord_length_le v)⟩, listWord v.val⟩
  apply Finite.of_injective encode
  intro u v h
  apply Subtype.ext
  apply binaryWordCode_injective_length
  · exact congrArg (fun z => z.1.val) h
  · exact congrArg (fun z => z.2.val) h

noncomputable instance boundedFoodWord_fintype (L N : ℕ) : Fintype (BoundedFoodWord L N) :=
  Fintype.ofFinite _

def boundedFoodRoot (L N : ℕ) : BoundedFoodWord L N := ⟨[], Or.inl rfl⟩

def boundedFoodLeft {L N : ℕ} (v : BoundedFoodWord L N) : BoundedFoodWord L N :=
  ⟨foodWordLeft L v.val, by
    by_cases h : v.val.length ≤ L + 1
    · left
      simp [foodWordLeft, h]
    · right
      have hv := boundedFoodWord_length_le v
      simp only [foodWordLeft, ite_eq_right h, List.length_tail]
      omega⟩

def boundedFoodRight {L N : ℕ} (v : BoundedFoodWord L N) : BoundedFoodWord L N :=
  ⟨foodWordRight L v.val, by
    by_cases h : v.val.length ≤ L + 1
    · left
      simp [foodWordRight, h]
    · right
      have hv := boundedFoodWord_length_le v
      simp only [foodWordRight, ite_eq_right h, List.length_dropLast]
      omega⟩

theorem boundedFoodParents_commute {L N : ℕ} (v : BoundedFoodWord L N) :
    boundedFoodLeft (boundedFoodRight v) = boundedFoodRight (boundedFoodLeft v) := by
  apply Subtype.ext
  exact foodWordParents_commute L v.val

theorem boundedFood_zero_height {L N : ℕ} (v : BoundedFoodWord L N)
    (h : foodWordHeight L v.val = 0) : v = boundedFoodRoot L N := by
  apply Subtype.ext
  rcases v.property with hv | hv
  · exact hv
  · unfold foodWordHeight at h
    omega

/-- Diamond parity only on the finite source domain suffices to integrate
edge labels. This avoids the false zero-extension premise above the cap. -/
theorem boundedFood_diamond_cut (L N : ℕ)
    (leftEdge rightEdge : BoundedFoodWord L N → Bool)
    (hroot : leftEdge (boundedFoodRoot L N) = false ∧
      rightEdge (boundedFoodRoot L N) = false)
    (hdiamond : ∀ v, (((leftEdge v ^^ rightEdge v) ^^ leftEdge (boundedFoodRight v)) ^^
      rightEdge (boundedFoodLeft v)) = false)
    (v : BoundedFoodWord L N) :
    ((diamondPotential boundedFoodRight rightEdge N v ^^
      diamondPotential boundedFoodRight rightEdge N (boundedFoodLeft v)) = leftEdge v) ∧
    ((diamondPotential boundedFoodRight rightEdge N v ^^
      diamondPotential boundedFoodRight rightEdge N (boundedFoodRight v)) = rightEdge v) := by
  apply diamondPotential_edges boundedFoodLeft boundedFoodRight
    (fun v : BoundedFoodWord L N => foodWordHeight L v.val) leftEdge rightEdge
  · intro u
    exact foodWordRight_height L u.val
  · exact boundedFoodParents_commute
  · intro u hu
    rw [boundedFood_zero_height u hu]
    exact hroot
  · exact hdiamond
  · have hv := boundedFoodWord_length_le v
    unfold foodWordHeight
    omega

/-- A cut in a finite graph with separately indexed edges, including parallel
edges. Its definition never identifies edges with equal endpoints. -/
def booleanEdgeCut {V E : Type*} (edges : Finset E) (a b : E → V)
    (label : V → Bool) : Finset E := edges.filter (fun e => label (a e) ≠ label (b e))

theorem booleanEdgeCut_xor_of_subset {V E : Type*} [DecidableEq E]
    (edges : Finset E) (a b : E → V) (f g : V → Bool)
    (hsub : booleanEdgeCut edges a b g ⊆ booleanEdgeCut edges a b f) :
    booleanEdgeCut edges a b (fun v => f v ^^ g v) =
      booleanEdgeCut edges a b f \ booleanEdgeCut edges a b g := by
  ext e
  by_cases he : e ∈ edges
  · have hi : g (a e) ≠ g (b e) → f (a e) ≠ f (b e) := by
      intro hg
      exact (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨he, hg⟩))).2
    cases hfa : f (a e) <;> cases hfb : f (b e) <;>
      cases hga : g (a e) <;> cases hgb : g (b e) <;>
      simp_all [booleanEdgeCut]
  · simp [booleanEdgeCut, he]

/-- Minimality among cuts separating a fixed pair implies minimality among
all nonempty cuts: remove a smaller nonseparating cut by XOR. -/
theorem minimal_separating_cut_is_bond {V E : Type*} [DecidableEq E]
    (edges : Finset E) (a b : E → V) (closed : Finset E)
    (x y : V) (f : V → Bool) (hf : f x ≠ f y)
    (hfclosed : booleanEdgeCut edges a b f ⊆ closed)
    (hmin : ∀ g : V → Bool, g x ≠ g y → booleanEdgeCut edges a b g ⊆ closed →
      (booleanEdgeCut edges a b f).card ≤ (booleanEdgeCut edges a b g).card)
    (g : V → Bool) (hgne : (booleanEdgeCut edges a b g).Nonempty)
    (hgsub : booleanEdgeCut edges a b g ⊆ booleanEdgeCut edges a b f) :
    booleanEdgeCut edges a b g = booleanEdgeCut edges a b f := by
  by_cases hsep : g x ≠ g y
  · exact Finset.eq_of_subset_of_card_le hgsub (hmin g hsep (hgsub.trans hfclosed))
  · have heq : g x = g y := not_ne_iff.mp hsep
    have hxor : (f x ^^ g x) ≠ (f y ^^ g y) := by
      rw [heq]
      cases hx : f x <;> cases hy : f y <;> cases hg : g y <;> simp_all
    have hc := booleanEdgeCut_xor_of_subset edges a b f g hgsub
    have hsmall := Finset.card_lt_card (Finset.sdiff_ssubset hgsub hgne)
    have hm := hmin (fun v => f v ^^ g v) hxor (by
      rw [hc]
      exact Finset.sdiff_subset.trans hfclosed)
    rw [hc] at hm
    omega

def indexedEdgeStep {V E : Type*} (active : Finset E) (a b : E → V) (x y : V) : Prop :=
  ∃ e ∈ active, a e = x ∧ b e = y

def indexedEdgeReach {V E : Type*} (active : Finset E) (a b : E → V) : V → V → Prop :=
  Relation.EqvGen (indexedEdgeStep active a b)

theorem indexedEdgeReach_label {V E : Type*}
    (active : Finset E) (a b : E → V) (label : V → Bool)
    (hedge : ∀ e ∈ active, label (a e) = label (b e))
    {x y : V} (h : indexedEdgeReach active a b x y) : label x = label y := by
  induction h with
  | rel x y h =>
    obtain ⟨e, he, ha, hb⟩ := h
    rw [← ha, ← hb]
    exact hedge e he
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem closed_cut_of_unreachable {V E : Type*} [DecidableEq E]
    (edges active : Finset E) (a b : E → V) (x y : V)
    (hxy : ¬ indexedEdgeReach active a b x y) :
    ∃ label : V → Bool, label x ≠ label y ∧
      booleanEdgeCut edges a b label ⊆ edges \ active := by
    classical
    let f := fun v => decide (indexedEdgeReach active a b x v)
    refine ⟨f, ?_, ?_⟩
    · have hx : indexedEdgeReach active a b x x := Relation.EqvGen.refl x
      simp [f, hx, hxy]
    · intro e he
      obtain ⟨heE, hdiff⟩ := Finset.mem_filter.mp he
      refine Finset.mem_sdiff.mpr ⟨heE, ?_⟩
      intro heA
      have hab : indexedEdgeReach active a b (a e) (b e) :=
        Relation.EqvGen.rel _ _ ⟨e, heA, rfl, rfl⟩
      have hi : indexedEdgeReach active a b x (a e) ↔ indexedEdgeReach active a b x (b e) :=
        ⟨fun h => Relation.EqvGen.trans _ _ _ h hab,
         fun h => Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ hab)⟩
      exact hdiff (by simp only [f, hi])
theorem exists_minimum_separating_cut {V E : Type*}
    (edges : Finset E) (a b : E → V) (closed : Finset E) (x y : V)
    (hex : ∃ f : V → Bool, f x ≠ f y ∧ booleanEdgeCut edges a b f ⊆ closed) :
    ∃ f : V → Bool, f x ≠ f y ∧ booleanEdgeCut edges a b f ⊆ closed ∧
      ∀ g : V → Bool, g x ≠ g y → booleanEdgeCut edges a b g ⊆ closed →
        (booleanEdgeCut edges a b f).card ≤ (booleanEdgeCut edges a b g).card := by
  classical
  have hn : ∃ k : ℕ, ∃ f : V → Bool, f x ≠ f y ∧
      booleanEdgeCut edges a b f ⊆ closed ∧ (booleanEdgeCut edges a b f).card = k := by
    obtain ⟨f, hf, hc⟩ := hex
    exact ⟨_, f, hf, hc, rfl⟩
  obtain ⟨f, hf, hc, hcard⟩ := Nat.find_spec hn
  refine ⟨f, hf, hc, ?_⟩
  intro g hg hgc
  rw [hcard]
  exact Nat.find_min' hn ⟨g, hg, hgc, rfl⟩

/-- Any pair connected in the host but disconnected by the enabled edges
has a disabled separating bond. The conclusion gives global cut minimality,
which is what the diamond-potential argument requires. -/
theorem exists_disabled_separating_bond {V E : Type*} [DecidableEq E]
    (edges active : Finset E) (a b : E → V) (x y : V)
    (hhost : indexedEdgeReach edges a b x y)
    (hxy : ¬ indexedEdgeReach active a b x y) :
    ∃ f : V → Bool, f x ≠ f y ∧
      booleanEdgeCut edges a b f ⊆ edges \ active ∧
      (booleanEdgeCut edges a b f).Nonempty ∧
      ∀ g : V → Bool, (booleanEdgeCut edges a b g).Nonempty →
        booleanEdgeCut edges a b g ⊆ booleanEdgeCut edges a b f →
        booleanEdgeCut edges a b g = booleanEdgeCut edges a b f := by
    obtain ⟨f, hf, hc, hmin⟩ := exists_minimum_separating_cut edges a b (edges \ active) x y
      (closed_cut_of_unreachable edges active a b x y hxy)
    refine ⟨f, hf, hc, ?_, ?_⟩
    · by_contra hn
      have hedge : ∀ e ∈ edges, f (a e) = f (b e) := by
        intro e he
        by_contra hd
        exact hn ⟨e, Finset.mem_filter.mpr ⟨he, hd⟩⟩
      exact hf (indexedEdgeReach_label edges a b f hedge hhost)
    · exact minimal_separating_cut_is_bond edges a b (edges \ active) x y f hf hc hmin

end

section
open Classical

abbrev WordBasicEdge (L N : ℕ) := BoundedFoodWord L N × Bool

noncomputable def wordBasicEdges (L N : ℕ) : Finset (WordBasicEdge L N) := by
      exact Finset.univ.filter fun e => e.1 ≠ boundedFoodRoot L N
def wordEdgeParent {L N : ℕ} (e : WordBasicEdge L N) : BoundedFoodWord L N :=
  if e.2 then boundedFoodRight e.1 else boundedFoodLeft e.1

theorem wordGraph_reaches_root (L N : ℕ) (v : BoundedFoodWord L N) :
    indexedEdgeReach (wordBasicEdges L N) Prod.fst wordEdgeParent v (boundedFoodRoot L N) := by
    suffices ∀ k (u : BoundedFoodWord L N), foodWordHeight L u.val ≤ k →
        indexedEdgeReach (wordBasicEdges L N) Prod.fst wordEdgeParent u (boundedFoodRoot L N) by
      exact this N v (by have h := boundedFoodWord_length_le v; unfold foodWordHeight; omega)
    intro k
    induction k with
    | zero =>
      intro u hu
      rw [boundedFood_zero_height u (by omega)]
      exact Relation.EqvGen.refl _
    | succ k ih =>
      intro u hu
      by_cases hr : u = boundedFoodRoot L N
      · rw [hr]
        exact Relation.EqvGen.refl _
      · have he : (u, true) ∈ wordBasicEdges L N := by simp [wordBasicEdges, hr]
        have hs : indexedEdgeReach (wordBasicEdges L N) Prod.fst wordEdgeParent u
            (boundedFoodRight u) := Relation.EqvGen.rel _ _ ⟨(u, true), he, rfl, rfl⟩
        have hp : foodWordHeight L (boundedFoodRight u).val ≤ k := by
          have hh := foodWordRight_height L u.val
          change foodWordHeight L (foodWordRight L u.val) ≤ k
          omega
        exact Relation.EqvGen.trans _ _ _ hs (ih _ hp)
theorem wordGraph_connected (L N : ℕ) (u v : BoundedFoodWord L N) :
    indexedEdgeReach (wordBasicEdges L N) Prod.fst wordEdgeParent u v :=
  Relation.EqvGen.trans _ _ _ (wordGraph_reaches_root L N u)
    (Relation.EqvGen.symm _ _ (wordGraph_reaches_root L N v))

noncomputable def wordGraphCut {L N : ℕ} (f : BoundedFoodWord L N → Bool) :
    Finset (WordBasicEdge L N) := booleanEdgeCut (wordBasicEdges L N) Prod.fst wordEdgeParent f

/-- Source-domain host connectivity discharges the premise of the general
disabled-bond theorem. Only enabled disconnection remains as a hypothesis. -/
theorem wordGraph_disabled_bond (L N : ℕ) (active : Finset (WordBasicEdge L N))
    (u v : BoundedFoodWord L N)
    (h : ¬ indexedEdgeReach active Prod.fst wordEdgeParent u v) :
    ∃ f : BoundedFoodWord L N → Bool, f u ≠ f v ∧
      wordGraphCut f ⊆ wordBasicEdges L N \ active ∧ (wordGraphCut f).Nonempty ∧
      ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
        wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f := by
    exact exists_disabled_separating_bond (wordBasicEdges L N) active Prod.fst wordEdgeParent
      u v (wordGraph_connected L N u v) h

theorem nonroot_word_ne_nil {L N : ℕ} (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) : v.val ≠ [] := by
  intro h
  exact hv (Subtype.ext h)

theorem boundedFoodLeft_preimage {L N : ℕ} (u v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) (hp : boundedFoodLeft u = v) :
    ∃ b : Bool, u.val = b :: v.val := by
    have he := congrArg Subtype.val hp
    change foodWordLeft L u.val = v.val at he
    have hs : ¬ u.val.length ≤ L + 1 := by
      intro h
      have hn := nonroot_word_ne_nil v hv
      simp [foodWordLeft, h] at he
      exact hn he
    rw [foodWordLeft, ite_eq_right hs] at he
    cases hu : u.val with
    | nil => simp [hu] at hs
    | cons b t =>
      refine ⟨b, ?_⟩
      simp [hu, List.tail_cons] at he
      rw [he]
theorem boundedFoodRight_preimage {L N : ℕ} (u v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) (hp : boundedFoodRight u = v) :
    ∃ b : Bool, u.val = v.val ++ [b] := by
  have he := congrArg Subtype.val hp
  change foodWordRight L u.val = v.val at he
  have hs : ¬ u.val.length ≤ L + 1 := by
    intro h
    have hn := nonroot_word_ne_nil v hv
    simp [foodWordRight, h] at he
    exact hn he
  rw [foodWordRight, ite_eq_right hs] at he
  have hu : u.val ≠ [] := by intro h; simp [h] at hs
  refine ⟨u.val.getLast hu, ?_⟩
  rw [← he]
  exact (List.dropLast_append_getLast hu).symm

/-- Only nonroot fibers are bounded: contraction gives the food root a large fiber. -/
theorem boundedFoodLeft_fiber_card {L N : ℕ} (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) :
    (Finset.univ.filter (fun u : BoundedFoodWord L N => boundedFoodLeft u = v)).card ≤ 2 := by
      let target := (Finset.univ : Finset Bool).image fun b => b :: v.val
      have hc : (Finset.univ.filter fun u : BoundedFoodWord L N => boundedFoodLeft u = v).card ≤
          target.card := by
        apply Finset.card_le_card_of_injOn Subtype.val
        · intro u hu
          obtain ⟨b, hb⟩ := boundedFoodLeft_preimage u v hv (Finset.mem_filter.mp hu).2
          exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, hb.symm⟩
        · intro u _ w _ h
          exact Subtype.ext h
      exact hc.trans ((Finset.card_image_le).trans (by decide))
theorem boundedFoodRight_fiber_card {L N : ℕ} (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) :
    (Finset.univ.filter (fun u : BoundedFoodWord L N => boundedFoodRight u = v)).card ≤ 2 := by
      let target := (Finset.univ : Finset Bool).image fun b => v.val ++ [b]
      have hc : (Finset.univ.filter fun u : BoundedFoodWord L N => boundedFoodRight u = v).card ≤
          target.card := by
        apply Finset.card_le_card_of_injOn Subtype.val
        · intro u hu
          obtain ⟨b, hb⟩ := boundedFoodRight_preimage u v hv (Finset.mem_filter.mp hu).2
          exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, hb.symm⟩
        · intro u _ w _ h
          exact Subtype.ext h
      exact hc.trans ((Finset.card_image_le).trans (by decide))
/-- The final index j represents a short factor of length j+1. -/
abbrev WordShortKey (L N w : ℕ) := WordBasicEdge L N × Fin w

/-- Owner (edge,j) uses its own upper short reaction and, when needed,
the parent's short reaction of length j. Food parents need no lower reaction. -/
noncomputable def wordDetourLower {L N w : ℕ} (d : WordShortKey L N w) :
    Option (WordShortKey L N w) :=
  if d.2.val = 0 ∨ wordEdgeParent d.1 = boundedFoodRoot L N then none
  else some ((wordEdgeParent d.1, d.1.2),
    ⟨d.2.val-1, lt_of_le_of_lt (Nat.sub_le _ _) d.2.isLt⟩)

noncomputable def wordDetourKeys {L N w : ℕ} (d : WordShortKey L N w) :
    Finset (WordShortKey L N w) := {d} ∪ (wordDetourLower d).toFinset

theorem wordDetourKeys_card {L N w : ℕ} (d : WordShortKey L N w) :
    (wordDetourKeys d).card ≤ 2 := by
  unfold wordDetourKeys
  have hc : (wordDetourLower d).toFinset.card ≤ 1 := by
    cases wordDetourLower d <;> simp
  exact (Finset.card_union_le _ _).trans (by simp only [Finset.card_singleton]; omega)

theorem wordDetourLower_details {L N w : ℕ} (d r : WordShortKey L N w)
    (h : wordDetourLower d = some r) :
    wordEdgeParent d.1 = r.1.1 ∧ d.1.2 = r.1.2 ∧
      d.2.val = r.2.val+1 ∧ r.1.1 ≠ boundedFoodRoot L N := by
    unfold wordDetourLower at h
    by_cases hz : d.2.val = 0 ∨ wordEdgeParent d.1 = boundedFoodRoot L N
    · rw [ite_eq_left hz] at h
      contradiction
    · rw [ite_eq_right hz] at h
      have he := Option.some.inj h
      have hp := congrArg (fun x : WordShortKey L N w => x.1.1) he
      have hs := congrArg (fun x : WordShortKey L N w => x.1.2) he
      have hj := congrArg (fun x : WordShortKey L N w => x.2.val) he
      dsimp at hp hs hj
      simp [not_or] at hz
      exact ⟨hp, hs, by omega, by rw [← hp]; exact hz.2⟩
theorem wordParent_fixedSide_fiber_card {L N : ℕ} (v : BoundedFoodWord L N)
    (side : Bool) (hv : v ≠ boundedFoodRoot L N) :
    (Finset.univ.filter (fun u : BoundedFoodWord L N =>
      wordEdgeParent (u,side) = v)).card ≤ 2 := by
      cases side
      · simpa [wordEdgeParent, Bool.false_eq_true, ↓reduceIte] using
          boundedFoodLeft_fiber_card v hv
      · simpa [wordEdgeParent, ↓reduceIte] using boundedFoodRight_fiber_card v hv
/-- A lower reaction has at most two owners: its product's two children on
its fixed side. The food root is excluded by the definition, not assumed small. -/
theorem wordDetourLower_fiber_card {L N w : ℕ} (r : WordShortKey L N w) :
    (Finset.univ.filter (fun d : WordShortKey L N w =>
      wordDetourLower d = some r)).card ≤ 2 := by
            by_cases hr : r.1.1 = boundedFoodRoot L N
            · have he : (Finset.univ.filter fun d : WordShortKey L N w =>
                  wordDetourLower d = some r) = ∅ := by
                apply Finset.eq_empty_iff_forall_notMem.mpr
                intro d hd
                exact (wordDetourLower_details d r (Finset.mem_filter.mp hd).2).2.2.2 hr
              rw [he]
              simp
            · let target := Finset.univ.filter fun u : BoundedFoodWord L N =>
                  wordEdgeParent (u,r.1.2) = r.1.1
              have hc : (Finset.univ.filter fun d : WordShortKey L N w =>
                  wordDetourLower d = some r).card ≤ target.card := by
                apply Finset.card_le_card_of_injOn fun d : WordShortKey L N w => d.1.1
                · intro d hd
                  obtain ⟨hp, hs, _, _⟩ := wordDetourLower_details d r (Finset.mem_filter.mp hd).2
                  apply Finset.mem_filter.mpr
                  refine ⟨Finset.mem_univ _, ?_⟩
                  simpa [← hs, Prod.mk.eta] using hp
                · intro d hd e he hde
                  obtain ⟨_, hs, hj, _⟩ := wordDetourLower_details d r (Finset.mem_filter.mp hd).2
                  obtain ⟨_, ht, hk, _⟩ := wordDetourLower_details e r (Finset.mem_filter.mp he).2
                  apply Prod.ext
                  · exact Prod.ext hde (hs.trans ht.symm)
                  · apply Fin.ext
                    omega
              exact hc.trans (wordParent_fixedSide_fiber_card r.1.1 r.1.2 hr)
/-- At most three detours use a normalized short reaction. This counts all
owners, even the unused root owners, and is uniform in cap and width. -/
theorem wordDetourKeys_incidence {L N w : ℕ} (r : WordShortKey L N w) :
    (Finset.univ.filter (fun d : WordShortKey L N w => r ∈ wordDetourKeys d)).card ≤ 3 := by
          have hsub : (Finset.univ.filter fun d : WordShortKey L N w => r ∈ wordDetourKeys d) ⊆
              {r} ∪ (Finset.univ.filter fun d : WordShortKey L N w => wordDetourLower d = some r) := by
            intro d hd
            have hm := (Finset.mem_filter.mp hd).2
            simp only [wordDetourKeys, Finset.mem_union, Finset.mem_singleton,
              Option.mem_toFinset] at hm
            rcases hm with hm | hm
            · exact Finset.mem_union_left _ (Finset.mem_singleton.mpr hm.symm)
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)
          calc
            _ ≤ ({r} ∪ (Finset.univ.filter fun d : WordShortKey L N w =>
              wordDetourLower d = some r)).card := Finset.card_le_card hsub
            _ ≤ 1 + (Finset.univ.filter fun d : WordShortKey L N w =>
              wordDetourLower d = some r).card := by simpa using Finset.card_union_le {r} _
            _ ≤ 3 := by have h := wordDetourLower_fiber_card r; omega
end

section
open Classical RAF.Polymer RAF.Concrete

def sourceWordMolecule {N : ℕ} (s : List Bool) (hs : 0 < s.length)
    (hN : s.length ≤ N) : Molecule N := moleculeOfCode hs hN (listWord s)

@[simp] theorem sourceWordMolecule_length {N : ℕ} (s : List Bool)
    (hs : 0 < s.length) (hN : s.length ≤ N) :
    molLength (sourceWordMolecule s hs hN) = s.length := by
  simp [sourceWordMolecule]

@[simp] theorem sourceWordMolecule_word {N : ℕ} (s : List Bool)
    (hs : 0 < s.length) (hN : s.length ≤ N) :
    moleculeWord (sourceWordMolecule s hs hN) = s := by
  apply binaryWordCode_injective_length
  · rw [moleculeWord_length, sourceWordMolecule_length]
  · rw [binaryWordCode_moleculeWord]
    rfl

theorem boundedFoodWord_nonroot_length {L N : ℕ} (v : BoundedFoodWord L N)
    (hv : v ≠ boundedFoodRoot L N) : L < v.val.length := by
  rcases v.property with h | h
  · exact False.elim (hv (Subtype.ext h))
  · exact h.1

/-- Literal source realization of each nonfood short key. Root keys produce no reaction. -/
noncomputable def wordShortSourceOption {L N w : ℕ} (hL : 2*w ≤ L)
    (r : WordShortKey L N w) : Option (Reaction N) :=
  if hr : r.1.1 = boundedFoodRoot L N then none else
    let x := sourceWordMolecule r.1.1.val
      (by have h := boundedFoodWord_nonroot_length r.1.1 hr; omega)
      (boundedFoodWord_length_le r.1.1)
    some (sourceShortReaction x r.1.2 (r.2.val+1) (by omega)
      (by have h := boundedFoodWord_nonroot_length r.1.1 hr
          have hj := r.2.isLt
          simp only [x, sourceWordMolecule_length]
          omega))

theorem wordShortSourceOption_injective {L N w : ℕ} (hL : 2*w ≤ L)
    (r s : WordShortKey L N w) (a : Reaction N)
    (hr : wordShortSourceOption hL r = some a)
    (hs : wordShortSourceOption hL s = some a) : r = s := by
      have hrn : r.1.1 ≠ boundedFoodRoot L N := by
        intro hn
        simp [wordShortSourceOption, hn] at hr
      have hsn : s.1.1 ≠ boundedFoodRoot L N := by
        intro hn
        simp [wordShortSourceOption, hn] at hs
      unfold wordShortSourceOption at hr hs
      rw [dite_eq_right hrn] at hr
      rw [dite_eq_right hsn] at hs
      have he := (Option.some.inj hr).trans (Option.some.inj hs).symm
      have hrl := boundedFoodWord_nonroot_length r.1.1 hrn
      have hsl := boundedFoodWord_nonroot_length s.1.1 hsn
      obtain ⟨hp, hb, hk⟩ := sourceShortReaction_coordinates (w := w) _ _ r.1.2 s.1.2
        (r.2.val+1) (s.2.val+1) (by omega) (by omega)
        (by omega) (by omega)
        (by simp only [sourceWordMolecule_length]; omega)
        (by simp [sourceWordMolecule_length]; omega) he
      have hw := congrArg moleculeWord hp
      simp [sourceWordMolecule_word] at hw
      exact Prod.ext (Prod.ext (Subtype.ext hw) hb) (Fin.ext (by omega))
noncomputable def wordDetourSourceReactions {L N w : ℕ} (hL : 2*w ≤ L)
    (d : WordShortKey L N w) : Finset (Reaction N) :=
  (wordDetourKeys d).biUnion (fun r => (wordShortSourceOption hL r).toFinset)

theorem wordDetourSourceReactions_card {L N w : ℕ} (hL : 2*w ≤ L)
    (d : WordShortKey L N w) : (wordDetourSourceReactions hL d).card ≤ 2 := by
  unfold wordDetourSourceReactions
  calc
    _ ≤ ∑ r ∈ wordDetourKeys d, (wordShortSourceOption hL r).toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ wordDetourKeys d, 1 := by
      apply Finset.sum_le_sum
      intro r _
      cases wordShortSourceOption hL r <;> simp
    _ = (wordDetourKeys d).card := by simp
    _ ≤ 2 := wordDetourKeys_card d

/-- The actual source ID overlap bound, without an independence assumption on
basic edges or a quotient of coincident reaction IDs. -/
theorem wordDetourSourceReactions_incidence {L N w : ℕ} (hL : 2*w ≤ L)
    (a : Reaction N) :
    (Finset.univ.filter (fun d : WordShortKey L N w =>
      a ∈ wordDetourSourceReactions hL d)).card ≤ 3 := by
          by_cases ha : ∃ r : WordShortKey L N w, wordShortSourceOption hL r = some a
          · obtain ⟨r, hr⟩ := ha
            have hsub : (Finset.univ.filter fun d : WordShortKey L N w =>
                a ∈ wordDetourSourceReactions hL d) ⊆
                (Finset.univ.filter fun d : WordShortKey L N w => r ∈ wordDetourKeys d) := by
              intro d hd
              obtain ⟨s, hs, hsa⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hd).2
              have he := Option.mem_toFinset.mp hsa
              have hsr := wordShortSourceOption_injective hL s r a he hr
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsr ▸ hs⟩
            exact (Finset.card_le_card hsub).trans (wordDetourKeys_incidence r)
          · have he : (Finset.univ.filter fun d : WordShortKey L N w =>
                a ∈ wordDetourSourceReactions hL d) = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro d hd
              obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hd).2
              exact ha ⟨r, Option.mem_toFinset.mp hr⟩
            rw [he]
            simp
end

section
open Classical

noncomputable def wordContourDetours {L N : ℕ} (w : ℕ)
    (C : Finset (WordBasicEdge L N)) : Finset (WordShortKey L N w) :=
  C.product Finset.univ

@[simp] theorem wordContourDetours_card {L N w : ℕ} (C : Finset (WordBasicEdge L N)) :
    (wordContourDetours w C).card = w*C.card := by
  simp [wordContourDetours, Nat.mul_comm]

theorem wordContour_disjoint_detours {L N w : ℕ} (hL : 2*w ≤ L)
    (C : Finset (WordBasicEdge L N)) :
    ∃ T ⊆ wordContourDetours w C,
      (∀ d ∈ T, ∀ e ∈ T, d ≠ e →
        Disjoint (wordDetourSourceReactions hL d) (wordDetourSourceReactions hL e)) ∧
      w*C.card ≤ 5*T.card := by
          obtain ⟨T, hT, hd, hc⟩ := exists_disjoint_detours (wordContourDetours w C)
            (wordDetourSourceReactions hL)
            (fun d _ => wordDetourSourceReactions_card hL d) (by
              intro a
              have hsub : ((wordContourDetours w C).filter fun d =>
                  a ∈ wordDetourSourceReactions hL d) ⊆
                  (Finset.univ.filter fun d => a ∈ wordDetourSourceReactions hL d) := by
                intro d hd
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2⟩
              convert (Finset.card_le_card hsub).trans (wordDetourSourceReactions_incidence hL a) using 1
              congr 1
              ext d
              simp)
          exact ⟨T, hT, hd, by simpa [wordContourDetours_card] using hc⟩
end

section
open Classical MeasureTheory ProbabilityTheory RAF.Polymer unitInterval

/-- All w detours for every edge of the fixed contour fail. -/
def contourDetoursFailed {L N w : ℕ} {Ω : Type*} (hL : 2*w ≤ L)
    (C : Finset (WordBasicEdge L N)) (field : Reaction N → Ω → Prop) (ω : Ω) : Prop :=
  ∀ d ∈ wordContourDetours w C, detourFailed field (wordDetourSourceReactions hL d) ω

/-- Integer amplification k avoids fractional-power rounding: choose w>=5*k.
At w=5*k this is the paper exponent w*|C|/5 exactly. -/
theorem measure_contourDetoursFailed_le {L N w k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hL : 2*w ≤ L) (hk : 5*k ≤ w) (C : Finset (WordBasicEdge L N))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (field : Reaction N → Ω → Prop)
    (hind : iIndepFun field μ) (hmeas : ∀ r, Measurable (field r))
    (a : ENNReal) (ha : a ≤ 1) (hmarg : ∀ r, μ {ω | field r ω} = a) :
    μ {ω | contourDetoursFailed hL C field ω} ≤ ((1-a^2)^k)^C.card := by
      obtain ⟨T, hT, hd, hc⟩ := wordContour_disjoint_detours hL C
      have hkt : k*C.card ≤ T.card := by
        nlinarith
      calc
        _ ≤ μ {ω | ∀ d ∈ T, detourFailed field (wordDetourSourceReactions hL d) ω} := by
          apply measure_mono
          intro ω h d hdT
          exact h d (hT hdT)
        _ ≤ (1-a^2)^T.card := measure_disjoint_detours_failed_le μ field hind hmeas
          a ha hmarg (wordDetourSourceReactions hL) T hd
          fun d _ => wordDetourSourceReactions_card hL d
        _ ≤ (1-a^2)^(k*C.card) := pow_le_pow_of_le_one (zero_le : 0 ≤ 1-a^2)
          (tsub_le_self : 1-a^2 ≤ 1) hkt
        _ = _ := pow_mul _ _ _
/-- The literal iid static reaction field; distinct split-position IDs are coordinates. -/
noncomputable def staticReactionMeasure (N : ℕ) (a : I) : Measure (Reaction N → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw a)

noncomputable instance staticReactionMeasure_probability (N : ℕ) (a : I) :
    IsProbabilityMeasure (staticReactionMeasure N a) := by
  unfold staticReactionMeasure
  infer_instance

theorem staticReactionMeasure_indep (N : ℕ) (a : I) :
    iIndepFun (fun r (ω : Reaction N → Prop) => ω r) (staticReactionMeasure N a) := by
    exact iIndepFun_infinitePi fun _ => measurable_id
theorem staticReactionMeasure_open {N : ℕ} (a : I) (r : Reaction N) :
    staticReactionMeasure N a {ω | ω r} = (toNNReal a : ENNReal) := by
    have h : staticReactionMeasure N a ((fun ω => ω r) ⁻¹' {True}) =
        (toNNReal a : ENNReal) := by
      rw [staticReactionMeasure, ← Measure.map_apply (measurable_pi_apply r)
        (MeasurableSet.singleton True), Measure.infinitePi_map_eval]
      simp [ambientCoordLaw]
    simpa [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true] using h
/-- Unconditional fixed-contour failure estimate in the actual iid source field. -/
theorem staticReaction_contour_failure {L N w k : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (C : Finset (WordBasicEdge L N)) (a : I) :
    staticReactionMeasure N a {ω | contourDetoursFailed hL C (fun r ω => ω r) ω} ≤
      ((1-(toNNReal a : ENNReal)^2)^k)^C.card := by
  apply measure_contourDetoursFailed_le hL hk C (staticReactionMeasure N a)
    (fun r ω => ω r) (staticReactionMeasure_indep N a) (fun r => measurable_pi_apply r)
    (toNNReal a : ENNReal) _ (staticReactionMeasure_open a)
  exact_mod_cast a.property.2

end

section
open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

theorem revClosureStep_mono {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} {A B : Finset M}
    (hST : S ⊆ T) (hAB : A ⊆ B) :
    revClosureStep Q S A ⊆ revClosureStep Q T B := by
    intro x hx
    simp [revClosureStep, Finset.mem_union, Finset.mem_biUnion] at hx ⊢
    rcases hx with hxA | ⟨r, hrS, hx⟩
    · exact Or.inl (hAB hxA)
    · right
      refine ⟨r, hST hrS, ?_⟩
      rcases hx with hx | hx
      · by_cases hEnabled : RevEnabledLhs Q A r
        · have hEnabled' : RevEnabledLhs Q B r := fun y hy => hAB (hEnabled hy)
          simp [hEnabled] at hx
          simp [hEnabled', hx]
        · simp [hEnabled] at hx
      · by_cases hEnabled : RevEnabledRhs Q A r
        · have hEnabled' : RevEnabledRhs Q B r := fun y hy => hAB (hEnabled hy)
          simp [hEnabled] at hx
          simp [hEnabled', hx]
        · simp [hEnabled] at hx
theorem revClosureAt_mono_reactions {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} (hST : S ⊆ T) :
    ∀ k, revClosureAt Q S k ⊆ revClosureAt Q T k := by
  intro k
  induction k with
  | zero => exact Finset.Subset.rfl
  | succ k ih =>
      exact revClosureStep_mono Q hST ih

end

section

/-- An infinite split-position environment. `openAt w k` records openness of
the ligation producing `w` at split position `k`. -/
abbrev InfiniteSplitEnvironment := List Bool → Nat → Prop

end

section
open RAF RAF.Polymer RAF.Concrete

theorem revClosureAt_subset_succ {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (k : Nat) :
    revClosureAt Q S k ⊆ revClosureAt Q S (k + 1) := by
  intro x hx
  change x ∈ revClosureStep Q S (revClosureAt Q S k)
  exact Finset.mem_union_left _ hx

theorem revClosureAt_mono_stage {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) {i j : Nat} (hij : i ≤ j) :
    revClosureAt Q S i ⊆ revClosureAt Q S j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ j hij ih => exact ih.trans (revClosureAt_subset_succ Q S j)

end

section
open Classical

def wordDropShort (s : List Bool) (side : Bool) (k : ℕ) : List Bool :=
  if side then s.take (s.length-k) else s.drop k

theorem wordDropShort_length (s : List Bool) (side : Bool) (k : ℕ) :
    (wordDropShort s side k).length = s.length-k := by
  cases side <;> simp [wordDropShort]

theorem wordDropShort_one (s : List Bool) (side : Bool) :
    wordDropShort s side 1 = if side then s.dropLast else s.tail := by
  cases side <;> simp [wordDropShort, List.dropLast_eq_take]

theorem wordDropShort_comp (s : List Bool) (side : Bool) (j : ℕ) :
    wordDropShort (wordDropShort s side 1) side j =
      wordDropShort s side (j+1) := by
  cases side
  · simp [wordDropShort]
  · simp only [wordDropShort, ↓reduceIte, List.length_take, List.take_take]
    congr 1
    omega

theorem contract_wordDropShort_one {L N : ℕ} (e : WordBasicEdge L N) :
    contractFoodWord L (wordDropShort e.1.val e.2 1) = (wordEdgeParent e).val := by
  rw [wordDropShort_one]
  rcases e with ⟨v, side⟩
  cases side
  · exact contractFoodWord_tail L v.val
  · exact contractFoodWord_dropLast L v.val

theorem wordEdgeParent_nonroot_word {L N : ℕ} (e : WordBasicEdge L N)
    (h : wordEdgeParent e ≠ boundedFoodRoot L N) :
    (wordEdgeParent e).val = wordDropShort e.1.val e.2 1 := by
  have he := contract_wordDropShort_one e
  unfold contractFoodWord at he
  split_ifs at he with hs
  · exact False.elim (h (Subtype.ext he.symm))
  · exact he.symm

theorem wordEdgeParent_root_length {L N : ℕ} (e : WordBasicEdge L N)
    (h : wordEdgeParent e = boundedFoodRoot L N) : e.1.val.length ≤ L+1 := by
    have he := contract_wordDropShort_one e
    rw [h] at he
    change contractFoodWord L (wordDropShort e.1.val e.2 1) = [] at he
    unfold contractFoodWord at he
    by_cases hs : (wordDropShort e.1.val e.2 1).length ≤ L
    · rw [wordDropShort_length] at hs
      omega
    · rw [ite_eq_right hs] at he
      have hz := congrArg List.length he
      simp [wordDropShort_length, List.length_nil] at hz
      rw [wordDropShort_length] at hs
      omega
def wordShortStart {L N w : ℕ} (r : WordShortKey L N w) : List Bool :=
  contractFoodWord L r.1.1.val

def wordShortEnd {L N w : ℕ} (r : WordShortKey L N w) : List Bool :=
  contractFoodWord L (wordDropShort r.1.1.val r.1.2 (r.2.val+1))

/-- Every detour is a genuine one- or two-edge path after food contraction.
No assertion of reaction openness or catalytic support is assumed here. -/
theorem wordDetourKeys_reach_parent {L N w : ℕ} (d : WordShortKey L N w) :
    indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd
      (wordShortStart d) (wordEdgeParent d.1).val := by
      have hd : d ∈ wordDetourKeys d := by simp [wordDetourKeys]
      have upper : indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd
          (wordShortStart d) (wordShortEnd d) :=
        Relation.EqvGen.rel _ _ ⟨d, hd, rfl, rfl⟩
      by_cases hj : d.2.val = 0
      · have he : wordShortEnd d = (wordEdgeParent d.1).val := by
          simpa [wordShortEnd, hj, zero_add] using contract_wordDropShort_one d.1
        exact he ▸ upper
      · by_cases hp : wordEdgeParent d.1 = boundedFoodRoot L N
        · have hm := wordEdgeParent_root_length d.1 hp
          have he : wordShortEnd d = (wordEdgeParent d.1).val := by
            rw [hp]
            change contractFoodWord L (wordDropShort d.1.1.val d.1.2 (d.2.val+1)) = []
            apply ite_eq_left
            rw [wordDropShort_length]
            omega
          exact he ▸ upper
        · let r : WordShortKey L N w :=
            ((wordEdgeParent d.1, d.1.2), ⟨d.2.val-1, lt_of_le_of_lt (Nat.sub_le _ _) d.2.isLt⟩)
          have hlower : wordDetourLower d = some r := by
            simp [wordDetourLower, hj, hp, or_self, ↓reduceIte]
            rfl
          have hr : r ∈ wordDetourKeys d := by simp [wordDetourKeys, hlower]
          have hrs : wordShortStart r = (wordEdgeParent d.1).val := by
            change contractFoodWord L (wordEdgeParent d.1).val = (wordEdgeParent d.1).val
            apply ite_eq_right
            intro hh
            rcases (wordEdgeParent d.1).property with hnil | hlen
            · exact hp (Subtype.ext hnil)
            · omega
          have hre : wordShortEnd r = wordShortEnd d := by
            have hjr : d.2.val-1+1 = d.2.val := by omega
            change contractFoodWord L (wordDropShort (wordEdgeParent d.1).val d.1.2
              (d.2.val-1+1)) = wordShortEnd d
            rw [hjr, wordEdgeParent_nonroot_word d.1 hp, wordDropShort_comp]
            rfl
          have lower : indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd
              (wordEdgeParent d.1).val (wordShortEnd d) :=
            Relation.EqvGen.rel _ _ ⟨r, hr, hrs, hre⟩
          exact Relation.EqvGen.trans _ _ _ upper (Relation.EqvGen.symm _ _ lower)

end

section
open Classical RAF.Polymer RAF.Concrete

/-- One reversible source step after food contraction, with the other factor
explicitly supplied by food. Reaction IDs remain the literal source IDs. -/
def literalFoodEdge {N : ℕ} (L : ℕ) (S : Finset (Reaction N))
    (u v : List Bool) : Prop :=
  ∃ a ∈ S, contractFoodWord L (moleculeWord (reactionProduct a)) = u ∧
    ((molLength (reactionLeft a) ≤ L ∧
      contractFoodWord L (moleculeWord (reactionRight a)) = v) ∨
     (molLength (reactionRight a) ≤ L ∧
      contractFoodWord L (moleculeWord (reactionLeft a)) = v))

theorem wordShortSourceOption_spec {L N w : ℕ} (hL : 2*w ≤ L)
    (r : WordShortKey L N w) (hr : r.1.1 ≠ boundedFoodRoot L N) :
    ∃ a, wordShortSourceOption hL r = some a ∧
      contractFoodWord L (moleculeWord (reactionProduct a)) = wordShortStart r ∧
      ((molLength (reactionLeft a) ≤ L ∧
        contractFoodWord L (moleculeWord (reactionRight a)) = wordShortEnd r) ∨
       (molLength (reactionRight a) ≤ L ∧
        contractFoodWord L (moleculeWord (reactionLeft a)) = wordShortEnd r)) := by
          unfold wordShortSourceOption
          rw [dite_eq_right hr]
          dsimp only
          refine ⟨_, rfl, ?_, ?_⟩
          · simp [sourceShortReaction_product, sourceWordMolecule_word, wordShortStart]
          · have hv := boundedFoodWord_nonroot_length r.1.1 hr
            rcases r with ⟨⟨v, side⟩, j⟩
            cases side
            · left
              constructor
              · simp [molLength_reactionLeft, sourceShortReaction_leftLength,
                  sourceShortSplit, Bool.false_eq_true, ↓reduceIte]
                omega
              · simp [moleculeWord_reactionRight, sourceShortReaction_product,
                  sourceShortReaction_leftLength, sourceShortSplit, Bool.false_eq_true,
                  ↓reduceIte, sourceWordMolecule_word, wordShortEnd, wordDropShort]
            · right
              constructor
              · rw [← moleculeWord_length]
                simp only [moleculeWord_reactionRight, sourceShortReaction_product,
                  sourceShortReaction_leftLength, sourceShortSplit, ↓reduceIte,
                  sourceWordMolecule_length, sourceWordMolecule_word, List.length_drop]
                omega
              · simp only [moleculeWord_reactionLeft, sourceShortReaction_product,
                  sourceShortReaction_leftLength, sourceShortSplit, ↓reduceIte,
                  sourceWordMolecule_length, sourceWordMolecule_word, wordShortEnd, wordDropShort]
theorem wordDetourKeys_nonroot {L N w : ℕ} (d r : WordShortKey L N w)
    (hd : d.1.1 ≠ boundedFoodRoot L N) (hr : r ∈ wordDetourKeys d) :
    r.1.1 ≠ boundedFoodRoot L N := by
  simp only [wordDetourKeys, Finset.mem_union, Finset.mem_singleton,
    Option.mem_toFinset] at hr
  rcases hr with hr | hr
  · exact hr ▸ hd
  · exact (wordDetourLower_details d r hr).2.2.2

/-- The detour path is realized entirely by its own literal reversible source
reactions with supplied food factors. No probabilistic assumptions occur. -/
theorem wordDetourSource_reach_parent {L N w : ℕ} (hL : 2*w ≤ L)
    (d : WordShortKey L N w) (hd : d.1.1 ≠ boundedFoodRoot L N) :
    Relation.EqvGen (literalFoodEdge L (wordDetourSourceReactions hL d))
      (wordShortStart d) (wordEdgeParent d.1).val := by
  suffices ∀ u v, indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd u v →
      Relation.EqvGen (literalFoodEdge L (wordDetourSourceReactions hL d)) u v by
    exact this _ _ (wordDetourKeys_reach_parent d)
  intro u v path
  induction path with
  | rel u v h =>
    obtain ⟨r, hr, hu, hv⟩ := h
    obtain ⟨a, ha, hp, hf⟩ := wordShortSourceOption_spec hL r
      (wordDetourKeys_nonroot d r hd hr)
    apply Relation.EqvGen.rel
    refine ⟨a, ?_, hp.trans hu, ?_⟩
    · apply Finset.mem_biUnion.mpr
      exact ⟨r, hr, Option.mem_toFinset.mpr ha⟩
    · rcases hf with hf | hf
      · exact Or.inl ⟨hf.1, hf.2.trans hv⟩
      · exact Or.inr ⟨hf.1, hf.2.trans hv⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The ordinary literal reversible closure, with arbitrary temporary food cutoff. -/
noncomputable def temporaryReactionClosure {N : ℕ} (L : ℕ) (S : Finset (Reaction N)) :
    Finset (Molecule N) := Finset.univ.filter (fun x => ∃ k,
      x ∈ revClosureAt (binaryPolymerCRS N L) S k)

@[simp] theorem mem_temporaryReactionClosure {N L : ℕ} (S : Finset (Reaction N))
    (x : Molecule N) : x ∈ temporaryReactionClosure L S ↔
      ∃ k, x ∈ revClosureAt (binaryPolymerCRS N L) S k := by
  simp [temporaryReactionClosure]

theorem temporaryReactionClosure_mono {N L : ℕ} {S T : Finset (Reaction N)}
    (hST : S ⊆ T) : temporaryReactionClosure L S ⊆ temporaryReactionClosure L T := by
  intro x hx
  obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure S x).mp hx
  exact (mem_temporaryReactionClosure T x).mpr ⟨k, revClosureAt_mono_reactions _ hST k hk⟩

theorem temporaryReactionClosure_food {N L : ℕ} (S : Finset (Reaction N))
    (x : Molecule N) (hx : molLength x ≤ L) : x ∈ temporaryReactionClosure L S := by
  apply (mem_temporaryReactionClosure S x).mpr
  exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩

theorem temporaryReactionClosure_ligation {N L : ℕ} (S : Finset (Reaction N))
    (r : Reaction N) (hr : r ∈ S)
    (hl : reactionLeft r ∈ temporaryReactionClosure L S)
    (hh : reactionRight r ∈ temporaryReactionClosure L S) :
    reactionProduct r ∈ temporaryReactionClosure L S := by
  obtain ⟨kl, hkl⟩ := (mem_temporaryReactionClosure S _).mp hl
  obtain ⟨kr, hkr⟩ := (mem_temporaryReactionClosure S _).mp hh
  have hl' := revClosureAt_mono_stage (binaryPolymerCRS N L) S (Nat.le_max_left kl kr) hkl
  have hr' := revClosureAt_mono_stage (binaryPolymerCRS N L) S (Nat.le_max_right kl kr) hkr
  apply (mem_temporaryReactionClosure S _).mpr
  refine ⟨max kl kr+1, ?_⟩
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨r, hr, Finset.mem_union_left _ ?_⟩
  have hen : RevEnabledLhs (binaryPolymerCRS N L)
      (revClosureAt (binaryPolymerCRS N L) S (max kl kr)) r := by
    simpa [RevEnabledLhs, binaryPolymerCRS, Finset.insert_subset_iff,
      Finset.singleton_subset_iff] using And.intro hl' hr'
  rw [ite_eq_left hen]
  exact Finset.mem_singleton_self _

theorem temporaryReactionClosure_cleavage {N L : ℕ} (S : Finset (Reaction N))
    (r : Reaction N) (hr : r ∈ S)
    (hp : reactionProduct r ∈ temporaryReactionClosure L S) :
    reactionLeft r ∈ temporaryReactionClosure L S ∧
      reactionRight r ∈ temporaryReactionClosure L S := by
  obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure S _).mp hp
  have hen : RevEnabledRhs (binaryPolymerCRS N L) (revClosureAt (binaryPolymerCRS N L) S k) r := by
    simpa [RevEnabledRhs, binaryPolymerCRS] using hk
  have hadd : {reactionLeft r, reactionRight r} ⊆
      revClosureAt (binaryPolymerCRS N L) S (k+1) := by
    intro x hx
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨r, hr, Finset.mem_union_right _ ?_⟩
    rw [ite_eq_left hen]
    exact hx
  exact ⟨(mem_temporaryReactionClosure S _).mpr ⟨k+1,hadd (by simp)⟩,
    (mem_temporaryReactionClosure S _).mpr ⟨k+1,hadd (by simp)⟩⟩

theorem moleculeWord_injective {N : ℕ} : Function.Injective (@moleculeWord N) := by
  intro x y h
  obtain ⟨kx, vx⟩ := x
  obtain ⟨ky, vy⟩ := y
  have hh := congrArg List.length h
  rw [moleculeWord_length, moleculeWord_length] at hh
  have hidx : kx = ky := Fin.ext (by unfold molLength at hh; dsimp at hh; omega)
  subst ky
  have hc := congrArg binaryWordCode h
  rw [binaryWordCode_moleculeWord, binaryWordCode_moleculeWord] at hc
  exact Sigma.ext rfl (heq_of_eq (Fin.ext hc))

/-- Generability is well defined on contracted words: every representative of
food is generated, while a nonfood word has a unique source molecule. -/
def contractedWordGenerated {N : ℕ} (L : ℕ) (S : Finset (Reaction N)) (s : List Bool) : Prop :=
  ∀ x : Molecule N, contractFoodWord L (moleculeWord x) = s → x ∈ temporaryReactionClosure L S

theorem contractedWordGenerated_root {N L : ℕ} (S : Finset (Reaction N)) :
    contractedWordGenerated L S [] := by
    intro x hx
    by_cases hlen : (moleculeWord x).length ≤ L
    · exact temporaryReactionClosure_food S x (by rwa [moleculeWord_length] at hlen)
    · rw [contractFoodWord, ite_eq_right hlen] at hx
      have he := congrArg List.length hx
      rw [moleculeWord_length] at he
      simp [List.length_nil] at he
      unfold molLength at he
      omega
theorem contractedWordGenerated_iff {N L : ℕ} (S : Finset (Reaction N)) (x : Molecule N) :
    contractedWordGenerated L S (contractFoodWord L (moleculeWord x)) ↔
      x ∈ temporaryReactionClosure L S := by
    constructor
    · intro h
      exact h x rfl
    · intro hx y hy
      by_cases hyl : (moleculeWord y).length ≤ L
      · exact temporaryReactionClosure_food S y (by rwa [moleculeWord_length] at hyl)
      · by_cases hxl : (moleculeWord x).length ≤ L
        · rw [contractFoodWord, ite_eq_right hyl, contractFoodWord, ite_eq_left hxl] at hy
          have he := congrArg List.length hy
          simp [moleculeWord_length, List.length_nil] at he
          unfold molLength at he
          omega
        · rw [contractFoodWord, ite_eq_right hyl, contractFoodWord, ite_eq_right hxl] at hy
          exact moleculeWord_injective hy ▸ hx
end

section
open MeasureTheory

/-- Outside a bad set, every vertex reaches food; hence all lost mass is
charged to that bad set when food itself is good. Counts use actual vertices. -/
theorem card_le_bad_add_pool {X : Type*} [Fintype X] [DecidableEq X]
    (bad pool : Finset X) (hcover : ∀ x, x ∉ bad → x ∈ pool) :
    Fintype.card X ≤ bad.card + pool.card := by
  have hu : bad ∪ pool = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ bad
    · exact Finset.mem_union_left pool hx
    · exact Finset.mem_union_right bad (hcover x hx)
  calc
    Fintype.card X = (bad ∪ pool).card := by rw [hu, Finset.card_univ]
    _ ≤ bad.card + pool.card := Finset.card_union_le bad pool

/-- Expected bad mass is the sum of individual bad probabilities. No
independence of contour events or vertex indicators is assumed. -/
theorem lintegral_bad_card {Ω X : Type*} [Fintype Ω] [Fintype X]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (bad : Ω → Finset X) :
    (∫⁻ ω, ((bad ω).card : ENNReal) ∂μ) = ∑ x : X, μ {ω | x ∈ bad ω} := by
        classical
        have he (ω : Ω) : ((bad ω).card : ENNReal) =
            ∑ x : X, if x ∈ bad ω then (1 : ENNReal) else 0 := by simp
        simp_rw [he]
        rw [lintegral_finsetSum Finset.univ fun _ _ => measurable_of_finite _]
        apply Finset.sum_congr rfl
        intro x _
        have hf : (fun ω => if x ∈ bad ω then (1 : ENNReal) else 0) =
            Set.indicator {ω | x ∈ bad ω} fun _ => (1 : ENNReal) := by
          funext ω
          simp [Set.indicator_apply, Set.mem_ofPred_eq]
        rw [hf]
        exact lintegral_indicator_one (Set.Finite.measurableSet (Set.toFinite _))
/-- Root failure plus a first-moment mass bound. The deterministic cover
and per-vertex marginal estimates are the exact remaining source inputs. -/
theorem measure_pool_deficit_le {Ω X : Type*} [Fintype Ω] [Fintype X]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [DecidableEq X]
    (μ : Measure Ω) (bad pool : Ω → Finset X) (root : X)
    (hcover : ∀ ω, root ∉ bad ω → ∀ x, x ∉ bad ω → x ∈ pool ω)
    (δ : ENNReal) (hbad : ∀ x, μ {ω | x ∈ bad ω} ≤ δ)
    (k : ℕ) (hk : 0 < k) :
    μ {ω | (pool ω).card + k ≤ Fintype.card X} ≤
      δ + (Fintype.card X : ENNReal) * δ / k := by
      have hsub : {ω | (pool ω).card + k ≤ Fintype.card X} ⊆
          {ω | root ∈ bad ω} ∪ {ω | k ≤ (bad ω).card} := by
        intro ω hω
        by_cases hr : root ∈ bad ω
        · exact Or.inl hr
        · right
          change (pool ω).card + k ≤ Fintype.card X at hω
          change k ≤ (bad ω).card
          have hc := card_le_bad_add_pool (bad ω) (pool ω) (hcover ω hr)
          omega
      have hm : μ {ω | k ≤ (bad ω).card} ≤
          (Fintype.card X : ENNReal) * δ / k := by
        have hmark := meas_ge_le_lintegral_div
          (μ := μ) (f := fun ω => ((bad ω).card : ENNReal))
          (measurable_of_finite _).aemeasurable
          (ε := (k : ENNReal)) (by exact_mod_cast Nat.ne_of_gt hk) (by simp)
        have hint : (∫⁻ ω, ((bad ω).card : ENNReal) ∂μ) ≤
            (Fintype.card X : ENNReal) * δ := by
          rw [lintegral_bad_card]
          simpa using Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hbad x
        have hmark' : μ {ω | k ≤ (bad ω).card} ≤
            (∫⁻ ω, ((bad ω).card : ENNReal) ∂μ) / k := by
          simpa [Nat.cast_le] using hmark
        exact hmark'.trans (ENNReal.div_le_div_right hint _)
      exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add (hbad root) hm))
end

section
open Classical

def shortBinaryWords : ℕ → Finset (List Bool)
  | 0 => {[]}
  | k + 1 => insert [] ((Finset.univ : Finset Bool).biUnion
      (fun b => (shortBinaryWords k).image (List.cons b)))

theorem mem_shortBinaryWords (s : List Bool) (k : ℕ) :
    s ∈ shortBinaryWords k ↔ s.length ≤ k := by
  induction k generalizing s with
  | zero => simp [shortBinaryWords]
  | succ k ih =>
    cases s with
    | nil => simp [shortBinaryWords]
    | cons b t => cases b <;> simp [shortBinaryWords, ih]

theorem shortBinaryWords_card_lt (k : ℕ) : (shortBinaryWords k).card < 2 ^ (k + 1) := by
        induction k with
        | zero => simp [shortBinaryWords]
        | succ k ih =>
          have hc : ((Finset.univ : Finset Bool).biUnion
              fun b => (shortBinaryWords k).image (List.cons b)).card ≤
              2 * (shortBinaryWords k).card := by
            calc
              _ ≤ ∑ b : Bool, ((shortBinaryWords k).image (List.cons b)).card := Finset.card_biUnion_le
              _ ≤ ∑ _b : Bool, (shortBinaryWords k).card :=
                Finset.sum_le_sum fun _ _ => Finset.card_image_le
              _ = 2 * (shortBinaryWords k).card := by simp [two_mul]
          have hi := Finset.card_insert_le [] ((Finset.univ : Finset Bool).biUnion
            fun b => (shortBinaryWords k).image (List.cons b))
          simp only [shortBinaryWords]
          rw [pow_succ]
          omega
/-- A deliberately loose core envelope; counting both paddings separately removes
dependence on the length of the core and on the ambient molecular universe. -/
def coreWordEnvelope (core : List Bool) (k : ℕ) : Finset (List Bool) :=
  ((shortBinaryWords k) ×ˢ (shortBinaryWords k)).image (fun lr => lr.1 ++ core ++ lr.2)

theorem coreWordEnvelope_contains (core s : List Bool) (k : ℕ)
    (hs : ∃ l r : List Bool, s = l ++ core ++ r)
    (hlen : s.length ≤ core.length + k) : s ∈ coreWordEnvelope core k := by
  obtain ⟨l, r, h⟩ := hs
  have hh := congrArg List.length h
  simp only [List.length_append] at hh
  apply Finset.mem_image.mpr
  refine ⟨(l,r), Finset.mem_product.mpr ⟨?_, ?_⟩, h.symm⟩
  · exact (mem_shortBinaryWords l k).mpr (by omega)
  · exact (mem_shortBinaryWords r k).mpr (by omega)

/-- Uniform exponential bound in extra length, not core length. -/
theorem core_containing_words_card_lt (S : Finset (List Bool)) (core : List Bool) (k : ℕ)
    (hc : ∀ s ∈ S, ∃ l r : List Bool, s = l ++ core ++ r)
    (hl : ∀ s ∈ S, s.length ≤ core.length + k) : S.card < 2 ^ (2 * (k + 1)) := by
  have hs : S ⊆ coreWordEnvelope core k := fun s h =>
    coreWordEnvelope_contains core s k (hc s h) (hl s h)
  have hp := shortBinaryWords_card_lt k
  have hprod : (shortBinaryWords k).card * (shortBinaryWords k).card <
      2 ^ (k + 1) * 2 ^ (k + 1) := Nat.mul_self_lt_mul_self hp
  calc
    S.card ≤ (coreWordEnvelope core k).card := Finset.card_le_card hs
    _ ≤ (shortBinaryWords k).card * (shortBinaryWords k).card := by
      exact Finset.card_image_le.trans (by rw [Finset.card_product])
    _ < 2 ^ (k + 1) * 2 ^ (k + 1) := hprod
    _ = 2 ^ (2 * (k + 1)) := by rw [← pow_add, two_mul]

end

section
open Classical SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- Insert an out-and-back excursion at a visited vertex. -/
theorem walk_insert_excursion {r : V} (p : G.Walk r r) {u v : V}
    (hu : u ∈ p.support) (huv : G.Adj u v) :
    ∃ q : G.Walk r r, q.length = p.length + 2 ∧
      q.support.toFinset = insert v p.support.toFinset := by
    let q := (p.takeUntil u hu).append
      ((Walk.cons huv (Walk.cons huv.symm Walk.nil)).append (p.dropUntil u hu))
    refine ⟨q, ?_, ?_⟩
    · have h := congrArg Walk.length (p.take_spec hu)
      simp only [Walk.length_append] at h
      simp only [q, Walk.length_append, Walk.length_cons, Walk.length_nil]
      omega
    · ext x
      have h : x ∈ p.support ↔ x ∈ (p.takeUntil u hu).support ∨
          x ∈ (p.dropUntil u hu).support := by
        conv_lhs => rw [← p.take_spec hu]
        exact Walk.mem_support_append_iff _ _
      simp only [q, List.mem_toFinset, Finset.mem_insert, Walk.mem_support_append_iff,
        Walk.support_cons, Walk.support_nil, List.mem_cons]
      grind
/-- A cut-crossing property constructs a covering closed walk of optimal tree-tour length.
The property will be supplied by connectedness of the actual contour. -/
theorem finite_connected_covering_tour (C : Finset V) (r : V) (hr : r ∈ C)
    (hcross : ∀ S : Finset V, S ⊆ C → r ∈ S → S ≠ C →
      ∃ u ∈ S, ∃ v ∈ C, v ∉ S ∧ G.Adj u v) :
    ∃ p : G.Walk r r, p.support.toFinset = C ∧ p.length = 2 * (C.card - 1) := by
    have extend : ∀ k : ℕ, ∀ p : G.Walk r r,
        p.support.toFinset ⊆ C →
        p.length = 2 * (p.support.toFinset.card - 1) →
        (C \ p.support.toFinset).card = k →
        ∃ q : G.Walk r r, q.support.toFinset = C ∧ q.length = 2 * (C.card - 1) := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro p hp hl hk
        by_cases he : p.support.toFinset = C
        · exact ⟨p, he, by simpa [he] using hl⟩
        · have hrp : r ∈ p.support.toFinset := List.mem_toFinset.mpr p.start_mem_support
          obtain ⟨u, hu, v, hv, hvs, huv⟩ := hcross _ hp hrp he
          obtain ⟨q, hql, hqs⟩ := walk_insert_excursion G p (List.mem_toFinset.mp hu) huv
          have hqsub : q.support.toFinset ⊆ C := by
            rw [hqs]
            exact Finset.insert_subset hv hp
          have hc : q.support.toFinset.card = p.support.toFinset.card + 1 := by
            rw [hqs, Finset.card_insert_of_notMem hvs]
          have hpos := Finset.card_pos.mpr ⟨r, hrp⟩
          have hqlen : q.length = 2 * (q.support.toFinset.card - 1) := by omega
          have hsmall : (C \ q.support.toFinset).card < k := by
            have h1 := Finset.card_sdiff_add_card_eq_card hp
            have h2 := Finset.card_sdiff_add_card_eq_card hqsub
            omega
          exact ih _ hsmall q hqsub hqlen rfl
    apply extend _ Walk.nil
    · simpa using hr
    · simp
    · rfl
variable [Fintype V] [DecidableRel G.Adj]

/-- Specifying both endpoints cannot increase the degree-based walk count. -/
theorem card_walks_le_degree_pow (d : ℕ) (hd : ∀ v, (G.neighborFinset v).card ≤ d)
    (n : ℕ) (u v : V) : (G.finsetWalkLength n u v).card ≤ d ^ n := by
            induction n generalizing u v with
            | zero =>
              simp [finsetWalkLength]
              split
              · rename_i h
                subst v
                simp
              · simp
            | succ n ih =>
              simp [finsetWalkLength]
              refine Finset.card_biUnion_le.trans ?_
              simp [Finset.card_map]
              calc
                ∑ w : G.neighborSet u, (G.finsetWalkLength n w v).card
                    ≤ ∑ _w : G.neighborSet u, d ^ n := Finset.sum_le_sum fun w _ => ih w v
                _ ≤ d * d ^ n := by
                  simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]
                  apply Nat.mul_le_mul_right
                  simpa [SimpleGraph.neighborFinset] using hd u
                _ = d ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
/-- Fixed-anchor connected contours are encoded by walks, with no ambient vertex factor. -/
theorem card_connected_contours_le (d b : ℕ)
    (hd : ∀ v, (G.neighborFinset v).card ≤ d) (r : V)
    (family : Finset (Finset V))
    (hfamily : ∀ C ∈ family, C.card = b ∧ r ∈ C ∧
      ∀ S : Finset V, S ⊆ C → r ∈ S → S ≠ C →
        ∃ u ∈ S, ∃ v ∈ C, v ∉ S ∧ G.Adj u v) :
    family.card ≤ d ^ (2 * (b - 1)) := by
    have hs : family ⊆ (G.finsetWalkLength (2 * (b - 1)) r r).image
        fun p => p.support.toFinset := by
      intro C hC
      obtain ⟨hb, hr, hc⟩ := hfamily C hC
      obtain ⟨p, hp, hl⟩ := finite_connected_covering_tour G C r hr hc
      exact Finset.mem_image.mpr ⟨p, mem_finsetWalkLength_iff.mpr (by simpa [hb] using hl), hp⟩
    exact (Finset.card_le_card hs).trans
      (Finset.card_image_le.trans (card_walks_le_degree_pow G d hd _ r r))
end

section

def quadParity (f : Fin 4 → Bool) : Bool := ((f 0 ^^ f 1) ^^ f 2) ^^ f 3

/-- In a diamond, a subset closed under sharing that diamond either contains
every ambient cut edge or contains none. It therefore inherits even parity.
The four slots need not name distinct edges. -/
theorem quadParity_closed_subset (F C : Fin 4 → Bool)
    (hsub : ∀ i, F i = true → C i = true)
    (hclosed : ∀ i j, F i = true → C j = true → F j = true)
    (hC : quadParity C = false) : quadParity F = false := by
    by_cases h : ∃ i, F i = true
    · obtain ⟨i, hi⟩ := h
      have he : F = C := by
        funext j
        have hc := hclosed i j hi
        cases hf : F j <;> cases hc : C j <;> simp_all
      rw [he]
      exact hC
    · have he : F = fun _ => false := by
        funext i
        cases hi : F i
        · rfl
        · exact (h ⟨i, hi⟩).elim
      rw [he]
      rfl

end

section
open Classical

def wordDiamondSlot {L N : ℕ} (v : BoundedFoodWord L N) : Fin 4 → WordBasicEdge L N :=
  ![(v, false), (v, true), (boundedFoodRight v, false), (boundedFoodLeft v, true)]

noncomputable def wordEdgeIndicator {L N : ℕ} (F : Finset (WordBasicEdge L N))
    (e : WordBasicEdge L N) : Bool := decide (e ∈ F)

theorem wordParents_root (L N : ℕ) :
    boundedFoodLeft (boundedFoodRoot L N) = boundedFoodRoot L N ∧
    boundedFoodRight (boundedFoodRoot L N) = boundedFoodRoot L N := by
  constructor <;> apply Subtype.ext <;>
    simp [boundedFoodLeft, boundedFoodRight, boundedFoodRoot, foodWordLeft, foodWordRight]

theorem wordCut_indicator {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (e : WordBasicEdge L N) :
    wordEdgeIndicator (wordGraphCut f) e = (f e.1 ^^ f (wordEdgeParent e)) := by
  by_cases hr : e.1 = boundedFoodRoot L N
  · have hp : wordEdgeParent e = e.1 := by
      unfold wordEdgeParent
      rw [hr]
      split
      · exact (wordParents_root L N).2
      · exact (wordParents_root L N).1
    simp [wordEdgeIndicator, wordGraphCut, booleanEdgeCut, wordBasicEdges, hr, hp]
  · cases ha : f e.1 <;> cases hb : f (wordEdgeParent e) <;>
      simp [wordEdgeIndicator, wordGraphCut, booleanEdgeCut, wordBasicEdges, hr, ha, hb]

theorem wordCut_diamond_parity {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (v : BoundedFoodWord L N) :
    quadParity (fun i => wordEdgeIndicator (wordGraphCut f) (wordDiamondSlot v i)) = false := by
  simp only [quadParity, wordCut_indicator, wordDiamondSlot, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, wordEdgeParent,
    Bool.false_eq_true, ite_false, ite_true]
  rw [boundedFoodParents_commute]
  cases f v <;> cases f (boundedFoodLeft v) <;> cases f (boundedFoodRight v) <;>
    cases f (boundedFoodRight (boundedFoodLeft v)) <;> rfl

/-- An edge subset with even parity in each finite diamond is an actual cut. -/
theorem wordDiamond_integrate {L N : ℕ} (F : Finset (WordBasicEdge L N))
    (hsub : F ⊆ wordBasicEdges L N)
    (hpar : ∀ v, quadParity (fun i => wordEdgeIndicator F (wordDiamondSlot v i)) = false) :
    ∃ f : BoundedFoodWord L N → Bool, wordGraphCut f = F := by
  let le := fun v => wordEdgeIndicator F (v, false)
  let re := fun v => wordEdgeIndicator F (v, true)
  have hr : le (boundedFoodRoot L N) = false ∧ re (boundedFoodRoot L N) = false := by
    have hn (b : Bool) : (boundedFoodRoot L N, b) ∉ F := by
      intro h
      have := hsub h
      simp [wordBasicEdges] at this
    simp [le, re, wordEdgeIndicator, hn]
  have hd : ∀ v, (((le v ^^ re v) ^^ le (boundedFoodRight v)) ^^
      re (boundedFoodLeft v)) = false := by
    intro v
    exact hpar v
  let f := diamondPotential boundedFoodRight re N
  refine ⟨f, ?_⟩
  ext e
  have hp := boundedFood_diamond_cut L N le re hr hd e.1
  have he : (f e.1 ^^ f (wordEdgeParent e)) = wordEdgeIndicator F e := by
    rcases e with ⟨v, b⟩
    cases b
    · exact hp.1
    · exact hp.2
  have hi := wordCut_indicator f e
  rw [he] at hi
  constructor
  · intro h
    have ht : wordEdgeIndicator (wordGraphCut f) e = true := decide_eq_true h
    rw [hi] at ht
    exact of_decide_eq_true ht
  · intro h
    have ht : wordEdgeIndicator F e = true := decide_eq_true h
    rw [← hi] at ht
    exact of_decide_eq_true ht

/-- Sharing a diamond transfers ambient cut parity, hence a closed subset
of a word cut is itself a word cut. -/
theorem wordDiamond_closed_subset_cut {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (F : Finset (WordBasicEdge L N)) (hsub : F ⊆ wordGraphCut f)
    (hclosed : ∀ v i j, wordDiamondSlot v i ∈ F →
      wordDiamondSlot v j ∈ wordGraphCut f → wordDiamondSlot v j ∈ F) :
    ∃ g : BoundedFoodWord L N → Bool, wordGraphCut g = F := by
    apply wordDiamond_integrate F
    · exact hsub.trans (Finset.filter_subset _ _)
    · intro v
      apply quadParity_closed_subset _ fun i => wordEdgeIndicator (wordGraphCut f) (wordDiamondSlot v i)
      · intro i hi
        exact decide_eq_true (hsub (of_decide_eq_true hi))
      · intro i j hi hj
        exact decide_eq_true (hclosed v i j (of_decide_eq_true hi) (of_decide_eq_true hj))
      · exact wordCut_diamond_parity f v
/-- Two indexed edges share a finite diamond; loops are harmless for reachability. -/
def wordDiamondAdjacent {L N : ℕ} (e d : WordBasicEdge L N) : Prop :=
  ∃ v i j, wordDiamondSlot v i = e ∧ wordDiamondSlot v j = d

def wordContourReach {L N : ℕ} (C : Finset (WordBasicEdge L N)) :=
  Relation.EqvGen (fun e d => e ∈ C ∧ d ∈ C ∧ wordDiamondAdjacent e d)

/-- A nonempty cut minimal among nonempty cuts is connected through diamonds.
This is the contour theorem used before counting connected edge sets. -/
theorem wordBond_diamond_connected {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (e d : WordBasicEdge L N) (he : e ∈ wordGraphCut f) (hd : d ∈ wordGraphCut f) :
    wordContourReach (wordGraphCut f) e d := by
    let F := (wordGraphCut f).filter fun a => wordContourReach (wordGraphCut f) e a
    have hsub : F ⊆ wordGraphCut f := Finset.filter_subset _ _
    have heF : e ∈ F := Finset.mem_filter.mpr ⟨he, Relation.EqvGen.refl e⟩
    have hc : ∀ v i j, wordDiamondSlot v i ∈ F →
        wordDiamondSlot v j ∈ wordGraphCut f → wordDiamondSlot v j ∈ F := by
      intro v i j hi hj
      obtain ⟨hiC, hiR⟩ := Finset.mem_filter.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨hj, Relation.EqvGen.trans _ _ _ hiR ?_⟩
      exact Relation.EqvGen.rel _ _ ⟨hiC, hj, v, i, j, rfl, rfl⟩
    obtain ⟨g, hg⟩ := wordDiamond_closed_subset_cut f F hsub hc
    have hEq : F = wordGraphCut f := by
      rw [← hg]
      apply hmin g
      · rw [hg]
        exact ⟨e, heF⟩
      · rw [hg]
        exact hsub
    have hdF : d ∈ F := by rw [hEq]; exact hd
    exact (Finset.mem_filter.mp hdF).2
noncomputable def wordDiamondIncidence {L N : ℕ} (e : WordBasicEdge L N) :=
  Finset.univ.filter (fun v : BoundedFoodWord L N => ∃ i, wordDiamondSlot v i = e)

theorem wordDiamond_incidence_false {L N : ℕ} (u v : BoundedFoodWord L N) :
    (∃ i, wordDiamondSlot v i = (u, false)) ↔ v = u ∨ boundedFoodRight v = u := by
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [wordDiamondSlot]
  · rintro (h | h)
    · exact ⟨0, by simp [wordDiamondSlot, h]⟩
    · exact ⟨2, by simp [wordDiamondSlot, h]⟩

theorem wordDiamond_incidence_true {L N : ℕ} (u v : BoundedFoodWord L N) :
    (∃ i, wordDiamondSlot v i = (u, true)) ↔ v = u ∨ boundedFoodLeft v = u := by
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [wordDiamondSlot]
  · rintro (h | h)
    · exact ⟨1, by simp [wordDiamondSlot, h]⟩
    · exact ⟨3, by simp [wordDiamondSlot, h]⟩

theorem wordDiamond_incidence_card {L N : ℕ} (e : WordBasicEdge L N)
    (he : e ∈ wordBasicEdges L N) : (wordDiamondIncidence e).card ≤ 3 := by
      have hn : e.1 ≠ boundedFoodRoot L N := by simpa [wordBasicEdges] using he
      rcases e with ⟨u, b⟩
      cases b
      · have hs : wordDiamondIncidence (u, false) ⊆
            insert u (Finset.univ.filter fun v => boundedFoodRight v = u) := by
          intro v hv
          have h := (wordDiamond_incidence_false u v).mp (Finset.mem_filter.mp hv).2
          simpa using h
        have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
        have hf := boundedFoodRight_fiber_card u hn
        omega
      · have hs : wordDiamondIncidence (u, true) ⊆
            insert u (Finset.univ.filter fun v => boundedFoodLeft v = u) := by
          intro v hv
          have h := (wordDiamond_incidence_true u v).mp (Finset.mem_filter.mp hv).2
          simpa using h
        have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
        have hf := boundedFoodLeft_fiber_card u hn
        omega
noncomputable def wordDiamondEdges {L N : ℕ} (v : BoundedFoodWord L N) :=
  (Finset.univ : Finset (Fin 4)).image (wordDiamondSlot v)

noncomputable def wordDiamondNeighbors {L N : ℕ} (e : WordBasicEdge L N) :=
  (wordDiamondIncidence e).biUnion (fun v => (wordDiamondEdges v).erase e)

theorem wordDiamond_neighbors_card {L N : ℕ} (e : WordBasicEdge L N)
    (he : e ∈ wordBasicEdges L N) : (wordDiamondNeighbors e).card ≤ 9 := by
  have hb : ∀ v ∈ wordDiamondIncidence e, ((wordDiamondEdges v).erase e).card ≤ 3 := by
    intro v hv
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hv).2
    have hm : e ∈ wordDiamondEdges v := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
    have hc : (wordDiamondEdges v).card ≤ 4 := Finset.card_image_le.trans (by decide)
    rw [Finset.card_erase_of_mem hm]
    omega
  have hc := wordDiamond_incidence_card e he
  calc
    (wordDiamondNeighbors e).card ≤ ∑ v ∈ wordDiamondIncidence e, ((wordDiamondEdges v).erase e).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ wordDiamondIncidence e, 3 := Finset.sum_le_sum hb
    _ ≤ 9 := by simp; omega

theorem wordDiamond_neighbor_iff {L N : ℕ} (e d : WordBasicEdge L N) :
    d ∈ wordDiamondNeighbors e ↔ d ≠ e ∧ wordDiamondAdjacent e d := by
    simp [wordDiamondNeighbors, Finset.mem_biUnion, Finset.mem_erase,
      wordDiamondIncidence, Finset.mem_filter, Finset.mem_univ, true_and,
      wordDiamondEdges, Finset.mem_image]
    constructor
    · rintro ⟨v, ⟨i, hi⟩, hd, j, hj⟩
      exact ⟨hd, v, i, j, hi, hj⟩
    · rintro ⟨hd, v, i, j, hi, hj⟩
      exact ⟨v, ⟨i, hi⟩, hd, j, hj⟩
end

section
open Classical SimpleGraph

def wordContourGraph (L N : ℕ) : SimpleGraph (WordBasicEdge L N) where
  Adj e d := e ∈ wordBasicEdges L N ∧ d ∈ wordBasicEdges L N ∧
    e ≠ d ∧ wordDiamondAdjacent e d
  symm := ⟨fun _ _ ⟨he, hd, hn, v, i, j, hi, hj⟩ => ⟨hd, he, hn.symm, v, j, i, hj, hi⟩⟩
  loopless := ⟨fun _ h => h.2.2.1 rfl⟩

theorem wordContourGraph_degree (L N : ℕ) (e : WordBasicEdge L N) :
    ((wordContourGraph L N).neighborFinset e).card ≤ 9 := by
  by_cases he : e ∈ wordBasicEdges L N
  · have hs : (wordContourGraph L N).neighborFinset e ⊆ wordDiamondNeighbors e := by
      intro d hd
      obtain ⟨_, _, hn, ha⟩ := (mem_neighborFinset _ _ _).mp hd
      exact wordDiamond_neighbor_iff e d |>.mpr ⟨hn.symm, ha⟩
    exact (Finset.card_le_card hs).trans (wordDiamond_neighbors_card e he)
  · have hz : (wordContourGraph L N).neighborFinset e = ∅ := by
      ext d
      simp only [Finset.notMem_empty, iff_false]
      intro hd
      exact he ((mem_neighborFinset _ _ _).mp hd).1
    simp [hz]

theorem wordContour_crossing {L N : ℕ} (C : Finset (WordBasicEdge L N))
    (hsub : C ⊆ wordBasicEdges L N) (r : WordBasicEdge L N)
    (hconn : ∀ d ∈ C, wordContourReach C r d)
    (S : Finset (WordBasicEdge L N)) (hs : S ⊆ C) (hr : r ∈ S) (hne : S ≠ C) :
    ∃ u ∈ S, ∃ v ∈ C, v ∉ S ∧ (wordContourGraph L N).Adj u v := by
    by_contra h
    have closed : ∀ u ∈ C, ∀ v ∈ C, wordDiamondAdjacent u v → u ∈ S → v ∈ S := by
      intro u hu v hv ha huS
      by_contra hvS
      exact h ⟨u, huS, v, hv, hvS, hsub hu, hsub hv,
        by intro he; subst v; exact hvS huS, ha⟩
    have inv : ∀ u v, wordContourReach C u v → (u ∈ S ↔ v ∈ S) := by
      intro u v hp
      induction hp with
      | rel u v hrel =>
        obtain ⟨hu, hv, ha⟩ := hrel
        constructor
        · exact closed u hu v hv ha
        · obtain ⟨w, i, j, hi, hj⟩ := ha
          exact closed v hv u hu ⟨w, j, i, hj, hi⟩
      | refl u => rfl
      | symm u v _ ih => exact ih.symm
      | trans u v w _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    apply hne
    apply Finset.Subset.antisymm hs
    intro d hd
    exact (inv r d (hconn d hd)).mp hr
noncomputable def wordAnchoredContours (L N : ℕ) (r : WordBasicEdge L N) (b : ℕ) :=
  (wordBasicEdges L N).powerset.filter (fun C => C.card = b ∧ r ∈ C ∧
    ∀ d ∈ C, wordContourReach C r d)

/-- Literal indexed-edge contour count, uniform in the ambient word cap. -/
theorem wordAnchoredContours_card (L N : ℕ) (r : WordBasicEdge L N) (b : ℕ) :
    (wordAnchoredContours L N r b).card ≤ 81 ^ (b - 1) := by
  have h := card_connected_contours_le (wordContourGraph L N) 9 b
    (wordContourGraph_degree L N) r (wordAnchoredContours L N r b) (by
      intro C hC
      obtain ⟨hpow, hb, hr, hc⟩ := Finset.mem_filter.mp hC
      exact ⟨hb, hr, wordContour_crossing C (Finset.mem_powerset.mp hpow) r hc⟩)
  simpa [pow_mul] using h

/-- Every nonempty minimal word cut containing the anchor is counted. -/
theorem wordBond_mem_anchored {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (r : WordBasicEdge L N) (hr : r ∈ wordGraphCut f) :
    wordGraphCut f ∈ wordAnchoredContours L N r (wordGraphCut f).card := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr ?_, rfl, hr, ?_⟩
  · exact Finset.filter_subset _ _
  · intro d hd
    exact wordBond_diamond_connected f hmin r d hr hd

/-- End insertion/deletion on uncontracted words, including the empty word. -/
def endWordGraph : SimpleGraph (List Bool) where
  Adj u v := ∃ b : Bool, v = b :: u ∨ u = b :: v ∨
    v = u ++ [b] ∨ u = v ++ [b]
  symm := ⟨by
    rintro u v ⟨b, h | h | h | h⟩
    · exact ⟨b, Or.inr (Or.inl h)⟩
    · exact ⟨b, Or.inl h⟩
    · exact ⟨b, Or.inr (Or.inr (Or.inr h))⟩
    · exact ⟨b, Or.inr (Or.inr (Or.inl h))⟩⟩
  loopless := ⟨by
    rintro u ⟨b, h | h | h | h⟩ <;>
      have hh := congrArg List.length h <;> simp at hh⟩

/-- A slot belonging to an actual edge is at most one end edit from its diamond product.
The actual-edge premise prevents a contracted-root jump. -/
theorem wordDiamondSlot_product_walk {L N : ℕ} (v : BoundedFoodWord L N) (i : Fin 4)
    (he : wordDiamondSlot v i ∈ wordBasicEdges L N) :
    ∃ p : endWordGraph.Walk (wordDiamondSlot v i).1.val v.val, p.length ≤ 1 := by
    fin_cases i
    · exact ⟨Walk.nil, Nat.zero_le 1⟩
    · exact ⟨Walk.nil, Nat.zero_le 1⟩
    · have hn : boundedFoodRight v ≠ boundedFoodRoot L N := by
        simpa [wordBasicEdges, wordDiamondSlot] using he
      obtain ⟨b, hb⟩ := boundedFoodRight_preimage v (boundedFoodRight v) hn rfl
      have ha : endWordGraph.Adj (boundedFoodRight v).val v.val :=
        ⟨b, Or.inr (Or.inr (Or.inl hb))⟩
      exact ⟨Walk.cons ha Walk.nil, Nat.le_refl _⟩
    · have hn : boundedFoodLeft v ≠ boundedFoodRoot L N := by
        simpa [wordBasicEdges, wordDiamondSlot] using he
      obtain ⟨b, hb⟩ := boundedFoodLeft_preimage v (boundedFoodLeft v) hn rfl
      exact ⟨Walk.cons (⟨b, Or.inl hb⟩) Walk.nil, Nat.le_refl _⟩
theorem wordDiamond_products_walk {L N : ℕ} (e d : WordBasicEdge L N)
    (he : e ∈ wordBasicEdges L N) (hd : d ∈ wordBasicEdges L N)
    (ha : wordDiamondAdjacent e d) :
    ∃ p : endWordGraph.Walk e.1.val d.1.val, p.length ≤ 2 := by
    obtain ⟨v, i, j, hi, hj⟩ := ha
    subst e
    subst d
    obtain ⟨p, hp⟩ := wordDiamondSlot_product_walk v i he
    obtain ⟨q, hq⟩ := wordDiamondSlot_product_walk v j hd
    refine ⟨p.append q.reverse, ?_⟩
    simp [Walk.length_append, Walk.length_reverse]
    omega
/-- Lift a contour walk to literal end edits, paying at most two per diamond step. -/
theorem wordContour_walk_lift {L N : ℕ} {e d : WordBasicEdge L N}
    (p : (wordContourGraph L N).Walk e d) :
    ∃ q : endWordGraph.Walk e.1.val d.1.val, q.length ≤ 2 * p.length := by
    induction p with
    | nil => exact ⟨Walk.nil, by simp⟩
    | @cons u v w huv p ih =>
      obtain ⟨q, hq⟩ := wordDiamond_products_walk u v huv.1 huv.2.1 huv.2.2.2
      obtain ⟨s, hs⟩ := ih
      refine ⟨q.append s, ?_⟩
      simp [Walk.length_append, Walk.length_cons]
      omega
/-- Every boundary product is within 4(b-1) end edits of any chosen boundary product.
This is contour localization, not yet molecule-to-contour anchoring. -/
theorem wordContour_product_locality {L N : ℕ} (C : Finset (WordBasicEdge L N))
    (hsub : C ⊆ wordBasicEdges L N) (e : WordBasicEdge L N) (he : e ∈ C)
    (hconn : ∀ d ∈ C, wordContourReach C e d)
    (d : WordBasicEdge L N) (hd : d ∈ C) :
    ∃ q : endWordGraph.Walk e.1.val d.1.val, q.length ≤ 4 * (C.card - 1) := by
  obtain ⟨p, hp, hl⟩ := finite_connected_covering_tour (wordContourGraph L N) C e he
    (wordContour_crossing C hsub e hconn)
  have hdp : d ∈ p.support := by
    apply List.mem_toFinset.mp
    rw [hp]
    exact hd
  obtain ⟨q, hq⟩ := wordContour_walk_lift (p.takeUntil d hdp)
  refine ⟨q, ?_⟩
  have ht := p.length_takeUntil_le_length hdp
  omega

/-- One end edit consumes at most one symbol of padding on either side. -/
theorem endWord_padding_step {u v core left right : List Bool} {k : ℕ}
    (hu : u = left ++ core ++ right) (hl : k + 1 ≤ left.length)
    (hr : k + 1 ≤ right.length) (ha : endWordGraph.Adj u v) :
    ∃ l r : List Bool, v = l ++ core ++ r ∧ k ≤ l.length ∧ k ≤ r.length := by
        obtain ⟨b, h | h | h | h⟩ := ha
        · refine ⟨b :: left, right, ?_, ?_, by omega⟩
          · simp [h, hu]
          · simp [List.length_cons]; omega
        · cases left with
          | nil => simp at hl
          | cons c t =>
            have hv := congrArg List.tail h
            simp [hu] at hv
            refine ⟨t, right, by simpa [List.append_assoc] using hv.symm, ?_, by omega⟩
            simp [List.length_cons] at hl
            omega
        · refine ⟨left, right ++ [b], ?_, by omega, ?_⟩
          · simp [h, hu, List.append_assoc]
          · simp only [List.length_append, List.length_singleton]; omega
        · have hn : right ≠ [] := by intro he; simp [he] at hr
          have he : right = right.dropLast ++ [right.getLast hn] :=
            (List.dropLast_append_getLast hn).symm
          have hv := congrArg List.dropLast h
          rw [hu, he] at hv
          simp only [← List.append_assoc, List.dropLast_concat] at hv
          refine ⟨left, right.dropLast, hv.symm, by omega, ?_⟩
          simp [List.length_dropLast]
          omega
/-- A central word with padding at least the walk length cannot be erased by end edits. -/
theorem endWord_walk_protects_core {u v : List Bool} (p : endWordGraph.Walk u v)
    (core left right : List Bool) (hu : u = left ++ core ++ right)
    (hl : p.length ≤ left.length) (hr : p.length ≤ right.length) :
    ∃ l r : List Bool, v = l ++ core ++ r := by
  induction p generalizing left right with
  | nil => exact ⟨left, right, hu⟩
  | @cons u v w ha p ih =>
    obtain ⟨l, r, hv, hpl, hpr⟩ := endWord_padding_step hu hl hr ha
    exact ih l r hv hpl hpr

/-- The protected-core input to contour anchoring, now for actual word contours. -/
theorem wordContour_protected_core {L N : ℕ} (C : Finset (WordBasicEdge L N))
    (hsub : C ⊆ wordBasicEdges L N) (e : WordBasicEdge L N) (he : e ∈ C)
    (hconn : ∀ d ∈ C, wordContourReach C e d)
    (core left right : List Bool) (ha : e.1.val = left ++ core ++ right)
    (hl : 4 * (C.card - 1) ≤ left.length) (hr : 4 * (C.card - 1) ≤ right.length)
    (d : WordBasicEdge L N) (hd : d ∈ C) :
    ∃ l r : List Bool, d.1.val = l ++ core ++ r := by
  obtain ⟨p, hp⟩ := wordContour_product_locality C hsub e he hconn d hd
  exact endWord_walk_protects_core p core left right ha (hp.trans hl) (hp.trans hr)

end

section
open Classical

/-- A word avoiding the core of every boundary product lies on the food side.
Right truncation cannot cross such a boundary before reaching food. -/
theorem wordCut_core_avoiding_root {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (core : List Bool)
    (hc : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (v : BoundedFoodWord L N)
    (hv : ¬ ∃ l r : List Bool, v.val = l ++ core ++ r) :
    f v = f (boundedFoodRoot L N) := by
  suffices ∀ k (u : BoundedFoodWord L N), foodWordHeight L u.val ≤ k →
      (¬ ∃ l r : List Bool, u.val = l ++ core ++ r) →
      f u = f (boundedFoodRoot L N) by
    exact this N v (by
      have hn := boundedFoodWord_length_le v
      unfold foodWordHeight
      omega) hv
  intro k
  induction k with
  | zero =>
    intro u hu _
    rw [boundedFood_zero_height u (by omega)]
  | succ k ih =>
    intro u hu havoid
    by_cases hr : u = boundedFoodRoot L N
    · rw [hr]
    have heq : f u = f (boundedFoodRight u) := by
      by_contra hneq
      have he : (u, true) ∈ wordGraphCut f := by
        simp [wordGraphCut, booleanEdgeCut, wordBasicEdges, wordEdgeParent, hr, hneq]
      exact havoid (hc (u, true) he)
    rw [heq]
    by_cases hp : boundedFoodRight u = boundedFoodRoot L N
    · rw [hp]
    have havp : ¬ ∃ l r : List Bool, (boundedFoodRight u).val = l ++ core ++ r := by
      rintro ⟨l, r, hparent⟩
      obtain ⟨b, hb⟩ := boundedFoodRight_preimage u (boundedFoodRight u) hp rfl
      apply havoid
      exact ⟨l, r ++ [b], by simp [hb, hparent, List.append_assoc]⟩
    apply ih _ ?_ havp
    have hh := foodWordRight_height L u.val
    change foodWordHeight L (foodWordRight L u.val) ≤ k
    omega

/-- Consequently every molecule on the opposite side contains the protected core. -/
theorem wordCut_nonfood_side_contains_core {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (core : List Bool)
    (hc : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (v : BoundedFoodWord L N) (hv : f v ≠ f (boundedFoodRoot L N)) :
    ∃ l r : List Bool, v.val = l ++ core ++ r := by
  by_contra h
  exact hv (wordCut_core_avoiding_root f core hc v h)

end

section

/-- Sliding one letter through a fixed-length word makes its label independent of the word. -/
theorem fixedLength_shift_constant {A : Type*} (g : List Bool → A) (M : ℕ)
    (hshift : ∀ (a b : Bool) (t : List Bool), t.length + 1 = M →
      g (a :: t) = g (t ++ [b]))
    (u v : List Bool) (hu : u.length = M) (hv : v.length = M) : g u = g v := by
      have rotate : ∀ front : List Bool, ∀ middle suffix : List Bool,
          front.length = suffix.length → front.length + middle.length = M →
          g (front ++ middle) = g (middle ++ suffix) := by
        intro front
        induction front with
        | nil =>
          intro middle suffix hs _
          cases suffix <;> simp_all
        | cons a front ih =>
          intro middle suffix hs ht
          cases suffix with
          | nil => simp at hs
          | cons b suffix =>
            have h1 := hshift a b (front ++ middle) (by
              simp only [List.length_cons, List.length_append] at *
              omega)
            have h2 := ih (middle ++ [b]) suffix (by simpa using hs) (by
              simp [List.length_append, List.length_cons, List.length_nil] at *
              omega)
            rw [List.append_assoc] at h1
            simpa [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using h1.trans h2
      simpa using rotate u [] v (hu.trans hv.symm) (by simpa using hu)
/-- If both parent moves above M preserve labels, all words from M through N share a label.
The spare level M+1 is essential. -/
theorem highBand_label_constant {A : Type*} (g : List Bool → A) (M N : ℕ)
    (hMN : M < N)
    (hparent : ∀ s : List Bool, M < s.length → s.length ≤ N →
      g s = g s.tail ∧ g s = g s.dropLast)
    (u v : List Bool) (hu : M ≤ u.length ∧ u.length ≤ N)
    (hv : M ≤ v.length ∧ v.length ≤ N) : g u = g v := by
    have hshift : ∀ (a b : Bool) (t : List Bool), t.length + 1 = M →
        g (a :: t) = g (t ++ [b]) := by
      intro a b t ht
      have h := hparent ((a :: t) ++ [b]) (by simp; omega) (by simp; omega)
      simp only [List.dropLast_concat] at h
      simpa [List.cons_append, List.tail_cons] using h.2.symm.trans h.1
    let base := List.replicate M false
    have descend : ∀ n : ℕ, ∀ s : List Bool, s.length = n → M ≤ n → n ≤ N → g s = g base := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro s hs hlo hhi
        by_cases he : n = M
        · exact fixedLength_shift_constant g M hshift s base (hs.trans he) (by simp [base])
        · have hlt : M < s.length := by omega
          have hlen : s.dropLast.length < n := by simp; omega
          exact (hparent s hlt (by omega)).2.trans
            (ih _ hlen s.dropLast rfl (by simp; omega) (by simp; omega))
    exact (descend _ u rfl hu.1 hu.2).trans (descend _ v rfl hv.1 hv.2).symm

end

section
open Classical

noncomputable def boundedWordLabel {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (s : List Bool) : Bool :=
  if hs : s = [] ∨ (L < s.length ∧ s.length ≤ N) then f ⟨s, hs⟩
  else f (boundedFoodRoot L N)

theorem boundedWordLabel_eq {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (u : BoundedFoodWord L N) : boundedWordLabel f u.val = f u := by
  unfold boundedWordLabel; exact dite_eq_left u.property

/-- Above every boundary product, both literal parents preserve the cut label. -/
theorem wordCut_above_boundary_parents {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (s : List Bool) (hs : M < s.length) (hN : s.length ≤ N) :
    boundedWordLabel f s = boundedWordLabel f s.tail ∧
    boundedWordLabel f s = boundedWordLabel f s.dropLast := by
  let u : BoundedFoodWord L N := ⟨s, Or.inr ⟨by omega, hN⟩⟩
  have hn : u ≠ boundedFoodRoot L N := by
    intro h
    have hh := congrArg (fun v : BoundedFoodWord L N => v.val.length) h
    change s.length = 0 at hh
    omega
  have heq (b : Bool) : f u = f (wordEdgeParent (u, b)) := by
    by_contra h
    have hm : (u, b) ∈ wordGraphCut f := by
      simp [wordGraphCut, booleanEdgeCut, wordBasicEdges, hn, h]
    have hh := hcut (u, b) hm
    change s.length ≤ M at hh
    omega
  have hlong : ¬ s.length ≤ L + 1 := by omega
  constructor
  · calc
      boundedWordLabel f s = f u := boundedWordLabel_eq f u
      _ = f (boundedFoodLeft u) := heq false
      _ = boundedWordLabel f s.tail := by
        rw [← boundedWordLabel_eq f (boundedFoodLeft u)]
        change boundedWordLabel f (foodWordLeft L s) = _
        simp [foodWordLeft, hlong]
  · calc
      boundedWordLabel f s = f u := boundedWordLabel_eq f u
      _ = f (boundedFoodRight u) := heq true
      _ = boundedWordLabel f s.dropLast := by
        rw [← boundedWordLabel_eq f (boundedFoodRight u)]
        change boundedWordLabel f (foodWordRight L s) = _
        simp [foodWordRight, hlong]

/-- All source vertices in the high band have the same cut label. -/
theorem wordCut_high_band_constant {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hMN : M < N)
    (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (u v : BoundedFoodWord L N) (hu : M ≤ u.val.length) (hv : M ≤ v.val.length) :
    f u = f v := by
    have h := highBand_label_constant (boundedWordLabel f) M N hMN
      (wordCut_above_boundary_parents f hLM hcut) u.val v.val
      ⟨hu, boundedFoodWord_length_le u⟩ ⟨hv, boundedFoodWord_length_le v⟩
    simpa [boundedWordLabel_eq] using h
/-- One core-avoiding high-band vertex places the entire high band on the food side. -/
theorem wordCut_high_band_food {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hMN : M < N)
    (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (core : List Bool)
    (hcore : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (v : BoundedFoodWord L N) (hv : M ≤ v.val.length)
    (havoid : ¬ ∃ l r : List Bool, v.val = l ++ core ++ r)
    (u : BoundedFoodWord L N) (hu : M ≤ u.val.length) :
    f u = f (boundedFoodRoot L N) :=
  (wordCut_high_band_constant f hLM hMN hcut u v hu hv).trans
    (wordCut_core_avoiding_root f core hcore v havoid)

/-- A constant word opposite to the first core bit avoids every nonempty core. -/
theorem exists_core_avoiding_word {L N M : ℕ} (hLM : L < M) (hMN : M ≤ N)
    (core : List Bool) (hne : core ≠ []) :
    ∃ v : BoundedFoodWord L N, v.val.length = M ∧
      ¬ ∃ l r : List Bool, v.val = l ++ core ++ r := by
  cases core with
  | nil => exact (hne rfl).elim
  | cons a t =>
    let v : BoundedFoodWord L N := ⟨List.replicate M (!a), Or.inr (by simpa using And.intro hLM hMN)⟩
    refine ⟨v, by simp [v], ?_⟩
    rintro ⟨l, r, he⟩
    have hm : a ∈ v.val := by rw [he]; simp
    change a ∈ List.replicate M (!a) at hm
    cases a <;> simp at hm

/-- A nonfood-side word cannot be longer than all boundary products when they share a core. -/
theorem wordCut_nonfood_length_le {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (core : List Bool) (hne : core ≠ [])
    (hcore : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (u : BoundedFoodWord L N) (hu : f u ≠ f (boundedFoodRoot L N)) :
    u.val.length ≤ M := by
  by_contra h
  have hN := boundedFoodWord_length_le u
  have hMN : M < N := by omega
  obtain ⟨v, hv, ha⟩ := exists_core_avoiding_word hLM hMN.le core hne
  exact hu (wordCut_high_band_food f hLM hMN hcut core hcore v (by omega) ha u (by omega))

end

section

noncomputable def wordNonfoodSide {L N : ℕ} (f : BoundedFoodWord L N → Bool) :=
  Finset.univ.filter (fun u => f u ≠ f (boundedFoodRoot L N))

/-- Count actual nonfood-side molecules, not the weight-one contracted food vertex. -/
theorem wordNonfoodSide_card_lt {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (core : List Bool) (hne : core ≠ [])
    (hcore : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (k : ℕ) (hM : M ≤ core.length + k) :
    (wordNonfoodSide f).card < 2 ^ (2 * (k + 1)) := by
  let S := (wordNonfoodSide f).image Subtype.val
  have hS : S.card = (wordNonfoodSide f).card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  rw [← hS]
  apply core_containing_words_card_lt S core k
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    exact wordCut_nonfood_side_contains_core f core hcore u (@Finset.mem_filter _ (fun a => f a ≠ f (boundedFoodRoot L N)) (fun a => @instDecidableNot _ (instDecidableEqBool _ _)) _ _ |>.mp hu).2
  · intro s hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    exact (wordCut_nonfood_length_le f hLM hcut core hne hcore u
      (@Finset.mem_filter _ (fun a => f a ≠ f (boundedFoodRoot L N)) (fun a => @instDecidableNot _ (instDecidableEqBool _ _)) _ _ |>.mp hu).2).trans hM

/-- If the food-containing side is the smaller molecular side, a small core envelope
forces the ambient cap itself to be small. Total molecular mass is 2^(N+1)-2. -/
theorem wordFoodSide_minor_cap_bound {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (core : List Bool) (hne : core ≠ [])
    (hcore : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (k : ℕ) (hM : M ≤ core.length + k)
    (hminor : (2 ^ (N + 1) - 2) - (wordNonfoodSide f).card ≤ (wordNonfoodSide f).card) :
    N ≤ 2 * (k + 1) := by
    have hc := wordNonfoodSide_card_lt f hLM hcut core hne hcore k hM
    have hb : (2 : ℕ) ^ N ≤ 2 ^ (2 * (k + 1)) := by
      rw [pow_succ] at hminor
      omega
    exact (pow_le_pow_iff_right₀ (by decide : (1 : ℕ) < 2)).mp hb

end

section
open Classical SimpleGraph

theorem endWord_strip_left (l s : List Bool) :
    ∃ p : endWordGraph.Walk (l ++ s) s, p.length = l.length := by
  induction l with
  | nil => exact ⟨Walk.nil, rfl⟩
  | cons b l ih =>
    obtain ⟨p, hp⟩ := ih
    have ha : endWordGraph.Adj (b :: (l ++ s)) (l ++ s) := ⟨b, Or.inr (Or.inl rfl)⟩
    exact ⟨Walk.cons ha p, by simpa using congrArg Nat.succ hp⟩

theorem endWord_append_right (s r : List Bool) :
    ∃ p : endWordGraph.Walk s (s ++ r), p.length = r.length := by
  induction r generalizing s with
  | nil => rw [List.append_nil]; exact ⟨Walk.nil, rfl⟩
  | cons b r ih =>
    obtain ⟨p, hp⟩ := ih (s ++ [b])
    have ha : endWordGraph.Adj s (s ++ [b]) := ⟨b, Or.inr (Or.inr (Or.inl rfl))⟩
    have h : ∃ q : endWordGraph.Walk s ((s ++ [b]) ++ r), q.length = (b :: r).length :=
      ⟨Walk.cons ha p, by simpa using congrArg Nat.succ hp⟩
    obtain ⟨q, hq⟩ := h
    exact ⟨q.copy rfl (by simp only [List.append_assoc, List.singleton_append]), by simpa using hq⟩

theorem endWord_strip_padding (l core r : List Bool) :
    ∃ p : endWordGraph.Walk (l ++ core ++ r) core, p.length = l.length + r.length := by
    obtain ⟨p, hp⟩ := endWord_strip_left l (core ++ r)
    obtain ⟨q, hq⟩ := endWord_append_right core r
    have h : ∃ w : endWordGraph.Walk (l ++ (core ++ r)) core,
        w.length = l.length + r.length :=
      ⟨p.append q.reverse, by simp [Walk.length_append, Walk.length_reverse, hp, hq]⟩
    obtain ⟨w, hw⟩ := h
    exact ⟨w.copy (List.append_assoc l core r).symm rfl, by simpa using hw⟩
/-- Explicit path through a common core, with an exact cancellation-free length identity. -/
theorem endWord_common_core_walk (u v core : List Bool)
    (hu : ∃ l r : List Bool, u = l ++ core ++ r)
    (hv : ∃ l r : List Bool, v = l ++ core ++ r) :
    ∃ p : endWordGraph.Walk u v, p.length + 2 * core.length = u.length + v.length := by
    obtain ⟨l, r, rfl⟩ := hu
    obtain ⟨a, b, rfl⟩ := hv
    obtain ⟨p, hp⟩ := endWord_strip_padding l core r
    obtain ⟨q, hq⟩ := endWord_strip_padding a core b
    refine ⟨p.append q.reverse, ?_⟩
    simp [Walk.length_append, Walk.length_reverse, hp, hq, List.length_append]
    omega
theorem endWord_walk_length_bound {u v : List Bool} (p : endWordGraph.Walk u v) :
    v.length ≤ u.length + p.length := by
      induction p with
      | nil => simp
      | @cons u v w ha p ih =>
        have hv : v.length ≤ u.length + 1 := by
          obtain ⟨b, h | h | h | h⟩ := ha <;>
            have hh := congrArg List.length h <;>
            simp [List.length_append, List.length_cons, List.length_nil] at hh <;> omega
        simp [Walk.length_cons]
        omega
/-- The long-core branch of molecule anchoring, with explicit molecular food-side weight.
Padding r yields a 5r nonfood path or a (12r+4) path when food is the smaller side. -/
theorem wordLongCore_anchors {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (e : WordBasicEdge L N) (he : e ∈ wordGraphCut f)
    (hconn : ∀ d ∈ wordGraphCut f, wordContourReach (wordGraphCut f) e d)
    (core left right : List Bool) (hne : core ≠ [])
    (ha : e.1.val = left ++ core ++ right) (r : ℕ)
    (hl : left.length = r) (hr : right.length = r)
    (hpad : 4 * ((wordGraphCut f).card - 1) ≤ r) :
    (∀ v : BoundedFoodWord L N, f v ≠ f (boundedFoodRoot L N) →
      ∃ p : endWordGraph.Walk v.val e.1.val, p.length ≤ 5 * r) ∧
    (((2 ^ (N + 1) - 2) - (wordNonfoodSide f).card ≤ (wordNonfoodSide f).card) →
      ∀ s : List Bool, s.length ≤ N →
        ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 12 * r + 4) := by
      have hsub : wordGraphCut f ⊆ wordBasicEdges L N := Finset.filter_subset _ _
      have hcore : ∀ d ∈ wordGraphCut f, ∃ a b : List Bool, d.1.val = a ++ core ++ b := by
        intro d hd
        exact wordContour_protected_core (wordGraphCut f) hsub e he hconn core left right ha
          (by omega) (by omega) d hd
      have hcut : ∀ d ∈ wordGraphCut f, d.1.val.length ≤ e.1.val.length + r := by
        intro d hd
        obtain ⟨p, hp⟩ := wordContour_product_locality (wordGraphCut f) hsub e he hconn d hd
        have hh := endWord_walk_length_bound p
        omega
      have hn : e.1 ≠ boundedFoodRoot L N := by simpa [wordBasicEdges] using hsub he
      have hL : L < e.1.val.length := by
        rcases e.1.property with h | h
        · exact (hn (Subtype.ext h)).elim
        · exact h.1
      have hLM : L < e.1.val.length + r := by omega
      have hlen : e.1.val.length = core.length + 2 * r := by
        have h := congrArg List.length ha
        simp [List.length_append] at h
        omega
      constructor
      · intro v hv
        have hvc := wordCut_nonfood_side_contains_core f core hcore v hv
        have hvl := wordCut_nonfood_length_le f hLM hcut core hne hcore v hv
        obtain ⟨p, hp⟩ := endWord_common_core_walk v.val e.1.val core hvc ⟨left, right, ha⟩
        exact ⟨p, by omega⟩
      · intro hminor s hs
        have hN := wordFoodSide_minor_cap_bound f hLM hcut core hne hcore (3 * r)
          (by omega) hminor
        have heN := boundedFoodWord_length_le e.1
        obtain ⟨p, hp⟩ := endWord_common_core_walk s e.1.val []
          ⟨[], s, by simp⟩ ⟨[], e.1.val, by simp⟩
        simp [List.length_nil, mul_zero, add_zero] at hp
        exact ⟨p, by omega⟩
theorem word_exists_padded_core (s : List Bool) (r : ℕ) (h : 2 * r < s.length) :
    ∃ core left right : List Bool, core ≠ [] ∧ s = left ++ core ++ right ∧
      left.length = r ∧ right.length = r := by
          let left := s.take r
          let core := (s.drop r).take (s.length - 2 * r)
          let right := (s.drop r).drop (s.length - 2 * r)
          have hc : core.length = s.length - 2 * r := by
            simp [core, List.length_take, List.length_drop]
            omega
          refine ⟨core, left, right, ?_, ?_, ?_, ?_⟩
          · intro he
            have hh := congrArg List.length he
            simp only [List.length_nil] at hh
            omega
          · simp [left, core, right, List.append_assoc, List.take_append_drop]
          · simp [left, List.length_take]
            omega
          · simp [right, List.length_drop]
            omega
/-- Completed long-anchor branch: both possible smaller-side labels have radius 64b.
The second branch covers actual food molecules through arbitrary lists of length <=N. -/
theorem wordLongAnchor_radius {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (e : WordBasicEdge L N) (he : e ∈ wordGraphCut f)
    (hconn : ∀ d ∈ wordGraphCut f, wordContourReach (wordGraphCut f) e d)
    (hlong : 8 * (wordGraphCut f).card < e.1.val.length) :
    (∀ v : BoundedFoodWord L N, f v ≠ f (boundedFoodRoot L N) →
      ∃ p : endWordGraph.Walk v.val e.1.val, p.length ≤ 64 * (wordGraphCut f).card) ∧
    (((2 ^ (N + 1) - 2) - (wordNonfoodSide f).card ≤ (wordNonfoodSide f).card) →
      ∀ s : List Bool, s.length ≤ N →
        ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 64 * (wordGraphCut f).card) := by
  obtain ⟨core, left, right, hn, ha, hl, hr⟩ :=
    word_exists_padded_core e.1.val (4 * (wordGraphCut f).card) (by omega)
  have h := wordLongCore_anchors f e he hconn core left right hn ha
    (4 * (wordGraphCut f).card) hl hr (by omega)
  have hb : 0 < (wordGraphCut f).card := Finset.card_pos.mpr ⟨e, he⟩
  constructor
  · intro v hv
    obtain ⟨p, hp⟩ := h.1 v hv
    exact ⟨p, by omega⟩
  · intro hm s hs
    obtain ⟨p, hp⟩ := h.2 hm s hs
    exact ⟨p, by omega⟩

end

section
open Classical

theorem shortBinaryWords_card_exact (n : ℕ) :
    (shortBinaryWords n).card + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => simp [shortBinaryWords]
  | succ n ih =>
    have he : shortBinaryWords (n + 1) = insert []
        (((shortBinaryWords n).image (List.cons true)) ∪
         ((shortBinaryWords n).image (List.cons false))) := by
      ext s
      simp [shortBinaryWords]
    have hd : Disjoint ((shortBinaryWords n).image (List.cons true))
        ((shortBinaryWords n).image (List.cons false)) := by
      apply Finset.disjoint_left.mpr
      intro s hs ht
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hs
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp ht
      have h := ha.trans hb.symm
      simp at h
    have hn : [] ∉ ((shortBinaryWords n).image (List.cons true)) ∪
        ((shortBinaryWords n).image (List.cons false)) := by simp
    rw [he, Finset.card_insert_of_notMem hn, Finset.card_union_of_disjoint hd]
    rw [Finset.card_image_of_injective _ List.cons_injective,
      Finset.card_image_of_injective _ List.cons_injective, pow_succ]
    omega

def actualBinaryWords (N : ℕ) : Finset (List Bool) := (shortBinaryWords N).erase []

theorem mem_actualBinaryWords (s : List Bool) (N : ℕ) :
    s ∈ actualBinaryWords N ↔ s ≠ [] ∧ s.length ≤ N := by
    simp [actualBinaryWords, Finset.mem_erase, mem_shortBinaryWords]
theorem actualBinaryWords_card (N : ℕ) : (actualBinaryWords N).card = 2 ^ (N + 1) - 2 := by
    have h := shortBinaryWords_card_exact N
    have hn : [] ∈ shortBinaryWords N := (mem_shortBinaryWords [] N).mpr (by simp)
    simp [actualBinaryWords, Finset.card_erase_of_mem hn]
    omega
/-- A molecularly smaller side cannot contain a constant-label high band with a spare level.
The proof counts the complement below M, rather than the contracted graph vertices. -/
theorem molecular_minor_side_below_band (N M : ℕ) (hMN : M < N)
    (S : Finset (List Bool)) (hsub : S ⊆ actualBinaryWords N)
    (hminor : S.card ≤ (actualBinaryWords N \ S).card)
    (hconstant : ∀ u ∈ actualBinaryWords N, ∀ v ∈ actualBinaryWords N,
      M ≤ u.length → M ≤ v.length → (u ∈ S ↔ v ∈ S))
    (s : List Bool) (hs : s ∈ S) : s.length < M := by
        by_contra h
        have hcomp : actualBinaryWords N \ S ⊆ shortBinaryWords (M - 1) := by
          intro t ht
          obtain ⟨htU, htS⟩ := Finset.mem_sdiff.mp ht
          have hlt : t.length < M := by
            by_contra hge
            exact htS ((hconstant s (hsub hs) t htU (by omega) (by omega)).mp hs)
          exact (mem_shortBinaryWords t (M - 1)).mpr (by omega)
        have hM : 0 < M := by
          by_contra hz
          have hc : actualBinaryWords N \ S = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro t ht
            obtain ⟨htU, htS⟩ := Finset.mem_sdiff.mp ht
            exact htS ((hconstant s (hsub hs) t htU (by omega) (by omega)).mp hs)
          have hp := Finset.card_pos.mpr ⟨s, hs⟩
          simp only [hc, Finset.card_empty] at hminor
          omega
        have hc : (actualBinaryWords N \ S).card < 2 ^ M := by
          have hx := (Finset.card_le_card hcomp).trans_lt (shortBinaryWords_card_lt (M - 1))
          simpa [Nat.sub_add_cancel hM] using hx
        have hp := (pow_lt_pow_iff_right₀ (by decide : (1 : ℕ) < 2)).mpr hMN
        have hpartition := Finset.card_sdiff_add_card_eq_card hsub
        rw [actualBinaryWords_card, pow_succ] at hpartition
        omega

end

section
open Classical SimpleGraph

/-- A cut side counted in actual molecules, including each food word separately. -/
noncomputable def wordMolecularSide {L N : ℕ} (f : BoundedFoodWord L N → Bool) (c : Bool) :=
  (actualBinaryWords N).filter (fun s => boundedWordLabel f s = c)

theorem wordShortAnchor_radius {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (e : WordBasicEdge L N) (he : e ∈ wordGraphCut f)
    (hconn : ∀ d ∈ wordGraphCut f, wordContourReach (wordGraphCut f) e d)
    (hshort : e.1.val.length ≤ 8 * (wordGraphCut f).card)
    (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) :
    ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 64 * (wordGraphCut f).card := by
        let M := e.1.val.length + 4 * (wordGraphCut f).card
        have hsub : wordGraphCut f ⊆ wordBasicEdges L N := Finset.filter_subset _ _
        have hcut : ∀ d ∈ wordGraphCut f, d.1.val.length ≤ M := by
          intro d hd
          obtain ⟨p, hp⟩ := wordContour_product_locality (wordGraphCut f) hsub e he hconn d hd
          have hh := endWord_walk_length_bound p
          dsimp [M]
          omega
        have hn : e.1 ≠ boundedFoodRoot L N := by simpa [wordBasicEdges] using hsub he
        have hLM : L < M := by
          rcases e.1.property with h | h
          · exact (hn (Subtype.ext h)).elim
          · dsimp [M]; omega
        have hsU := (Finset.mem_filter.mp hs).1
        have hsN := ((mem_actualBinaryWords s N).mp hsU).2
        have hsM : s.length ≤ M := by
          by_cases hMN : M < N
          · have hc : ∀ u ∈ actualBinaryWords N, ∀ v ∈ actualBinaryWords N,
                M ≤ u.length → M ≤ v.length → (u ∈ wordMolecularSide f c ↔ v ∈ wordMolecularSide f c) := by
              intro u hu v hv hMu hMv
              have heq := highBand_label_constant (boundedWordLabel f) M N hMN
                (wordCut_above_boundary_parents f hLM hcut) u v
                ⟨hMu, ((mem_actualBinaryWords u N).mp hu).2⟩
                ⟨hMv, ((mem_actualBinaryWords v N).mp hv).2⟩
              simp [wordMolecularSide, Finset.mem_filter, hu, hv, true_and]
              rw [heq]
            exact (molecular_minor_side_below_band N M hMN (wordMolecularSide f c)
              (Finset.filter_subset _ _) hminor hc s hs).le
          · omega
        obtain ⟨p, hp⟩ := endWord_common_core_walk s e.1.val []
          ⟨[], s, by simp⟩ ⟨[], e.1.val, by simp⟩
        simp [List.length_nil, mul_zero, add_zero] at hp
        refine ⟨p, ?_⟩
        dsimp [M] at hsM
        omega
theorem nonfood_label_preimage {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (s : List Bool) (hs : s ∈ actualBinaryWords N)
    (hn : boundedWordLabel f s ≠ f (boundedFoodRoot L N)) :
    ∃ u : BoundedFoodWord L N, u.val = s ∧ f u ≠ f (boundedFoodRoot L N) := by
  obtain ⟨hsnil, hN⟩ := (mem_actualBinaryWords s N).mp hs
  have hL : L < s.length := by
    by_contra h
    exact hn (by simp [boundedWordLabel, hsnil, h])
  let u : BoundedFoodWord L N := ⟨s, Or.inr ⟨hL, hN⟩⟩
  refine ⟨u, rfl, ?_⟩
  rwa [← boundedWordLabel_eq f u]

/-- The complement of the molecular food side is exactly the list image of the nonfood vertices. -/
theorem molecular_food_complement {L N : ℕ} (f : BoundedFoodWord L N → Bool) :
    actualBinaryWords N \ wordMolecularSide f (f (boundedFoodRoot L N)) =
      (wordNonfoodSide f).image Subtype.val := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsU, hsF⟩ := Finset.mem_sdiff.mp hs
    have hn : boundedWordLabel f s ≠ f (boundedFoodRoot L N) := by
      intro h
      exact hsF (Finset.mem_filter.mpr ⟨hsU, h⟩)
    obtain ⟨u, hu, hn⟩ := nonfood_label_preimage f s hsU hn
    exact Finset.mem_image.mpr ⟨u,
      (@Finset.mem_filter _ (fun a => f a ≠ f (boundedFoodRoot L N))
        (fun a => @instDecidableNot _ (instDecidableEqBool _ _)) _ _).mpr
          ⟨Finset.mem_univ u, hn⟩, hu⟩
  · intro hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
    have hn := (@Finset.mem_filter _ (fun a => f a ≠ f (boundedFoodRoot L N))
      (fun a => @instDecidableNot _ (instDecidableEqBool _ _)) _ _ |>.mp hu).2
    have hnil : u.val ≠ [] := by
      intro h
      exact hn (congrArg f (show u = boundedFoodRoot L N from Subtype.ext h))
    have hsU : u.val ∈ actualBinaryWords N :=
      (mem_actualBinaryWords u.val N).mpr ⟨hnil, boundedFoodWord_length_le u⟩
    refine Finset.mem_sdiff.mpr ⟨hsU, ?_⟩
    intro h
    have hh := (Finset.mem_filter.mp h).2
    have heq := boundedWordLabel_eq f (show BoundedFoodWord L N from u)
    exact hn (heq.symm.trans hh)

/-- Uniform molecule anchor radius for a molecularly smaller side of a connected word cut. -/
theorem wordMolecular_anchor_radius {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (e : WordBasicEdge L N) (he : e ∈ wordGraphCut f)
    (hconn : ∀ d ∈ wordGraphCut f, wordContourReach (wordGraphCut f) e d)
    (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) :
    ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 64 * (wordGraphCut f).card := by
    by_cases hshort : e.1.val.length ≤ 8 * (wordGraphCut f).card
    · exact wordShortAnchor_radius f e he hconn hshort c hminor s hs
    have hlong := wordLongAnchor_radius f e he hconn (by omega)
    obtain ⟨hsU, hslabel⟩ := Finset.mem_filter.mp hs
    by_cases hc : c = f (boundedFoodRoot L N)
    · rw [hc] at hminor
      have hcard : (actualBinaryWords N \ wordMolecularSide f (f (boundedFoodRoot L N))).card =
          (wordNonfoodSide f).card := by
        rw [molecular_food_complement]
        exact Finset.card_image_of_injective (wordNonfoodSide f)
          fun _ _ h => Subtype.ext h
      have hp := Finset.card_sdiff_add_card_eq_card
        (show wordMolecularSide f (f (boundedFoodRoot L N)) ⊆ actualBinaryWords N from Finset.filter_subset _ _)
      rw [hcard, actualBinaryWords_card] at hp
      rw [hcard] at hminor
      exact hlong.2 (by omega) s ((mem_actualBinaryWords s N).mp hsU).2
    · have hn : boundedWordLabel f s ≠ f (boundedFoodRoot L N) := by rw [hslabel]; exact hc
      obtain ⟨u, hu, hn⟩ := nonfood_label_preimage f s hsU hn
      obtain ⟨p, hp⟩ := hlong.1 u hn
      exact ⟨p.copy hu rfl, by simpa using hp⟩
/-- Minimal word cuts supply the connectedness premise of the complete anchor theorem. -/
theorem wordBond_molecular_anchor_radius {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (e : WordBasicEdge L N) (he : e ∈ wordGraphCut f) (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) :
    ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 64 * (wordGraphCut f).card :=
  wordMolecular_anchor_radius f e he (fun d hd => wordBond_diamond_connected f hmin e d he hd)
    c hminor s hs

/-- Six end edits and a stay-put choice; duplicates only decrease cardinality. -/
def endWordChoices (s : List Bool) : Finset (List Bool) :=
  insert s (insert s.tail (insert s.dropLast
    (((Finset.univ : Finset Bool).image (fun b => b :: s)) ∪
     ((Finset.univ : Finset Bool).image (fun b => s ++ [b])))))

theorem endWordChoices_card (s : List Bool) : (endWordChoices s).card ≤ 7 := by
                  have h1 := Finset.card_image_le (s := (Finset.univ : Finset Bool)) (f := fun b => b :: s)
                  have h2 := Finset.card_image_le (s := (Finset.univ : Finset Bool)) (f := fun b => s ++ [b])
                  have hu := Finset.card_union_le
                    ((Finset.univ : Finset Bool).image fun b => b :: s)
                    ((Finset.univ : Finset Bool).image fun b => s ++ [b])
                  have ha := Finset.card_insert_le s.dropLast
                    (((Finset.univ : Finset Bool).image fun b => b :: s) ∪
                     ((Finset.univ : Finset Bool).image fun b => s ++ [b]))
                  have hb := Finset.card_insert_le s.tail (insert s.dropLast
                    (((Finset.univ : Finset Bool).image fun b => b :: s) ∪
                     ((Finset.univ : Finset Bool).image fun b => s ++ [b])))
                  have hc := Finset.card_insert_le s (insert s.tail (insert s.dropLast
                    (((Finset.univ : Finset Bool).image fun b => b :: s) ∪
                     ((Finset.univ : Finset Bool).image fun b => s ++ [b]))))
                  simp only [Finset.card_univ, Fintype.card_bool] at h1 h2
                  unfold endWordChoices
                  omega
theorem endWord_adj_mem_choices {u v : List Bool} (h : endWordGraph.Adj u v) :
    v ∈ endWordChoices u := by
  obtain ⟨b, h | h | h | h⟩ := h
  · subst v; cases b <;> simp [endWordChoices]
  · subst u; cases b <;> simp [endWordChoices]
  · subst v; cases b <;> simp [endWordChoices]
  · subst u; cases b <;> simp [endWordChoices]

def endWordBall : ℕ → List Bool → Finset (List Bool)
  | 0, s => {s}
  | k + 1, s => (endWordChoices s).biUnion (endWordBall k)

theorem endWordBall_self (k : ℕ) (s : List Bool) : s ∈ endWordBall k s := by
  induction k with
  | zero => simp [endWordBall]
  | succ k ih =>
    exact Finset.mem_biUnion.mpr ⟨s, by simp [endWordChoices], ih⟩

theorem endWordBall_card (k : ℕ) (s : List Bool) : (endWordBall k s).card ≤ 7 ^ k := by
    induction k generalizing s with
    | zero => simp [endWordBall]
    | succ k ih =>
      calc
        (endWordBall (k + 1) s).card ≤ ∑ v ∈ endWordChoices s, (endWordBall k v).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ endWordChoices s, 7 ^ k := Finset.sum_le_sum fun v _ => ih v
        _ ≤ 7 * 7 ^ k := by
          simp only [Finset.sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (endWordChoices_card s)
        _ = 7 ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
theorem endWord_walk_mem_ball {u v : List Bool} (p : endWordGraph.Walk u v)
    (k : ℕ) (hk : p.length ≤ k) : v ∈ endWordBall k u := by
    induction k generalizing u v with
    | zero =>
      have he := p.eq_of_length_eq_zero (by omega)
      subst v
      exact endWordBall_self 0 u
    | succ k ih =>
      cases p with
      | nil => exact endWordBall_self (k + 1) u
      | @cons u v w ha p =>
        apply Finset.mem_biUnion.mpr
        refine ⟨v, endWord_adj_mem_choices ha, ih p ?_⟩
        simp [Walk.length_cons] at hk
        omega
end

section
open Classical

noncomputable def wordBallEdgeAnchors (L N : ℕ) (s : List Bool) (r : ℕ) :=
  (wordBasicEdges L N).filter (fun e => e.1.val ∈ endWordBall r s)

theorem wordBallEdgeAnchors_card (L N : ℕ) (s : List Bool) (r : ℕ) :
    (wordBallEdgeAnchors L N s r).card ≤ 2 * 7 ^ r := by
    have hc : (wordBallEdgeAnchors L N s r).card ≤
        ((endWordBall r s) ×ˢ (Finset.univ : Finset Bool)).card := by
      apply Finset.card_le_card_of_injOn fun e : WordBasicEdge L N => (e.1.val, e.2)
      · intro e he
        exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp he).2, Finset.mem_univ _⟩
      · intro e _ d _ h
        apply Prod.ext
        · exact Subtype.ext (congrArg (fun x : List Bool × Bool => x.1) h)
        · exact congrArg (fun x : List Bool × Bool => x.2) h
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hc
    have hb := endWordBall_card r s
    omega
/-- A finite envelope for all size-b contours whose smaller side contains molecule s. -/
noncomputable def wordMoleculeContourEnvelope (L N : ℕ) (s : List Bool) (b : ℕ) :=
  (wordBallEdgeAnchors L N s (64 * b)).biUnion (fun e => wordAnchoredContours L N e b)

theorem wordMoleculeContourEnvelope_card_raw (L N : ℕ) (s : List Bool) (b : ℕ) :
    (wordMoleculeContourEnvelope L N s b).card ≤ 2 * 7 ^ (64 * b) * 81 ^ (b - 1) := by
    calc
      _ ≤ ∑ e ∈ wordBallEdgeAnchors L N s (64 * b), (wordAnchoredContours L N e b).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ wordBallEdgeAnchors L N s (64 * b), 81 ^ (b - 1) :=
        Finset.sum_le_sum fun e _ => wordAnchoredContours_card L N e b
      _ ≤ 2 * 7 ^ (64 * b) * 81 ^ (b - 1) := by
        simp only [Finset.sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (wordBallEdgeAnchors_card L N s (64 * b))
def molecularContourConstant : ℕ := 2 * 7 ^ 64 * 81

/-- Uniform per-molecule exponential contour count with an explicit safe constant. -/
theorem wordMoleculeContourEnvelope_card (L N : ℕ) (s : List Bool) (b : ℕ) (hb : 0 < b) :
    (wordMoleculeContourEnvelope L N s b).card ≤ molecularContourConstant ^ b := by
  have h2 : (2 : ℕ) ≤ 2 ^ b := by
    have h := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (show 1 ≤ b by omega)
    simpa using h
  have h81 : (81 : ℕ) ^ (b - 1) ≤ 81 ^ b :=
    pow_le_pow_right₀ (by decide) (Nat.sub_le b 1)
  calc
    _ ≤ 2 * 7 ^ (64 * b) * 81 ^ (b - 1) := wordMoleculeContourEnvelope_card_raw L N s b
    _ ≤ 2 ^ b * 7 ^ (64 * b) * 81 ^ b :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ h2) h81
    _ = molecularContourConstant ^ b := by simp only [molecularContourConstant, mul_pow, pow_mul]

/-- Every relevant literal minimal cut lies in the finite counted envelope. -/
theorem wordBond_mem_molecule_envelope {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (hn : (wordGraphCut f).Nonempty) (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) :
    wordGraphCut f ∈ wordMoleculeContourEnvelope L N s (wordGraphCut f).card := by
  obtain ⟨e, he⟩ := hn
  obtain ⟨p, hp⟩ := wordBond_molecular_anchor_radius f hmin e he c hminor s hs
  have heB : e ∈ wordBallEdgeAnchors L N s (64 * (wordGraphCut f).card) := by
    refine Finset.mem_filter.mpr ⟨?_, endWord_walk_mem_ball p _ hp⟩
    exact (Finset.filter_subset _ _ : wordGraphCut f ⊆ wordBasicEdges L N) he
  exact Finset.mem_biUnion.mpr ⟨e, heB, wordBond_mem_anchored f hmin e he⟩

end

section
open Classical MeasureTheory ProbabilityTheory RAF.Polymer unitInterval

theorem wordMoleculeContourEnvelope_member_card {L N b : ℕ} {s : List Bool}
    {C : Finset (WordBasicEdge L N)} (hC : C ∈ wordMoleculeContourEnvelope L N s b) :
    C.card = b := by
  obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hC
  exact (Finset.mem_filter.mp he).2.1

noncomputable def contourBudget (a : I) (k : ℕ) : ENNReal :=
  (molecularContourConstant : ENNReal) * (1-(toNNReal a : ENNReal)^2)^k

theorem measure_molecule_contours_size_le {L N w k b : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (s : List Bool) (hb : 0 < b) (a : I) :
    staticReactionMeasure N a {ω | ∃ C ∈ wordMoleculeContourEnvelope L N s b,
      contourDetoursFailed hL C (fun r ω => ω r) ω} ≤ (contourBudget a k)^b := by
      let E := wordMoleculeContourEnvelope L N s b
      have hcount : (E.card : ENNReal) ≤ (molecularContourConstant : ENNReal)^b := by
        exact_mod_cast wordMoleculeContourEnvelope_card L N s b hb
      have he : {ω : Reaction N → Prop | ∃ C ∈ E,
          contourDetoursFailed hL C (fun r ω => ω r) ω} =
          ⋃ C ∈ E, {ω | contourDetoursFailed hL C (fun r ω => ω r) ω} := by ext ω; simp
      change staticReactionMeasure N a {ω | ∃ C ∈ E,
        contourDetoursFailed hL C (fun r ω => ω r) ω} ≤ _
      rw [he]
      calc
        _ ≤ ∑ C ∈ E, staticReactionMeasure N a
          {ω | contourDetoursFailed hL C (fun r ω => ω r) ω} := measure_biUnion_finset_le E _
        _ ≤ ∑ _C ∈ E, ((1-(toNNReal a : ENNReal)^2)^k)^b := by
          apply Finset.sum_le_sum
          intro C hC
          have hcard := wordMoleculeContourEnvelope_member_card hC
          simpa [hcard] using staticReaction_contour_failure hL hk C a
        _ = (E.card : ENNReal) * ((1-(toNNReal a : ENNReal)^2)^k)^b := by simp
        _ ≤ (molecularContourConstant : ENNReal)^b * ((1-(toNNReal a : ENNReal)^2)^k)^b := by
          gcongr
        _ = (contourBudget a k)^b := by rw [contourBudget, mul_pow]
/-- A per-molecule envelope of all positive-size disabled contours. Its
probability bounds actual smaller-side membership by the compiled anchor theorem. -/
def moleculeContourBad {L N w : ℕ} (hL : 2*w ≤ L) (s : List Bool)
    (ω : Reaction N → Prop) : Prop :=
  ∃ j : ℕ, ∃ C ∈ wordMoleculeContourEnvelope L N s (j+1),
    contourDetoursFailed hL C (fun r ω => ω r) ω

theorem wordBond_smaller_side_bad {L N w : ℕ} (hL : 2*w ≤ L)
    (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (hn : (wordGraphCut f).Nonempty) (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) (ω : Reaction N → Prop)
    (hfailed : contourDetoursFailed hL (wordGraphCut f) (fun r ω => ω r) ω) :
    moleculeContourBad hL s ω := by
  have hb := Finset.card_pos.mpr hn
  have hcard : (wordGraphCut f).card-1+1 = (wordGraphCut f).card := by omega
  refine ⟨(wordGraphCut f).card-1, wordGraphCut f, ?_, hfailed⟩
  rw [hcard]
  exact wordBond_mem_molecule_envelope f hmin hn c hminor s hs

/-- Uniform bad-side marginal; no independence between contours is required. -/
theorem measure_moleculeContourBad_le {L N w k : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (s : List Bool) (a : I) :
    staticReactionMeasure N a {ω | moleculeContourBad hL s ω} ≤
      contourBudget a k / (1-contourBudget a k) := by
    have he : {ω | moleculeContourBad hL s ω} =
        ⋃ j : ℕ, {ω | ∃ C ∈ wordMoleculeContourEnvelope L N s (j+1),
          contourDetoursFailed hL C (fun r ω => ω r) ω} := by ext ω; simp [moleculeContourBad]
    rw [he]
    calc
      _ ≤ ∑' j : ℕ, staticReactionMeasure N a {ω | ∃ C ∈ wordMoleculeContourEnvelope L N s (j+1),
        contourDetoursFailed hL C (fun r ω => ω r) ω} := measure_iUnion_le _
      _ ≤ ∑' j : ℕ, (contourBudget a k)^(j+1) := ENNReal.tsum_le_tsum
        fun j => measure_molecule_contours_size_le hL hk s (by omega) a
      _ = _ := by rw [ENNReal.tsum_geometric_add_one, div_eq_mul_inv]
end

section
open Classical RAF.Polymer

/-- Project an actual molecule to the finite graph, contracting all food words. -/
noncomputable def molecularWordVertex (L N : ℕ) (s : List Bool) : BoundedFoodWord L N :=
  if h : L < s.length ∧ s.length ≤ N then ⟨s, Or.inr h⟩ else boundedFoodRoot L N

theorem molecularWordVertex_label {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (s : List Bool) : f (molecularWordVertex L N s) = boundedWordLabel f s := by
  by_cases hs : s = []
  · subst s
    simp [molecularWordVertex, boundedWordLabel, boundedFoodRoot]
  · by_cases h : L < s.length ∧ s.length ≤ N
    · simp [molecularWordVertex, boundedWordLabel, hs, h]
    · simp [molecularWordVertex, boundedWordLabel, hs, h]

noncomputable def wordEffectiveEdges {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) : Finset (WordBasicEdge L N) :=
  (wordBasicEdges L N).filter (fun e => ∃ j : Fin w,
    ∀ a ∈ wordDetourSourceReactions hL (e,j), ω a)

theorem wordEffective_disabled_cut {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) (C : Finset (WordBasicEdge L N))
    (hC : C ⊆ wordBasicEdges L N \ wordEffectiveEdges hL ω) :
    contourDetoursFailed hL C (fun r ω => ω r) ω := by
  intro d hd hopen
  obtain ⟨he, _⟩ := Finset.mem_product.mp hd
  obtain ⟨hb, hn⟩ := Finset.mem_sdiff.mp (hC he)
  apply hn
  apply Finset.mem_filter.mpr
  exact ⟨hb, d.2, hopen⟩

theorem wordMolecularSide_complement_of_ne {L N : ℕ}
    (f : BoundedFoodWord L N → Bool) (c d : Bool) (hcd : c ≠ d) :
    actualBinaryWords N \ wordMolecularSide f c = wordMolecularSide f d := by
  ext s
  cases c <;> cases d <;> cases hs : boundedWordLabel f s <;>
    simp_all [wordMolecularSide]

/-- Outside the bad contour envelopes, actual molecules belong to the same
effective component. The proof uses weighted smaller sides, including food. -/
theorem outside_moleculeContourBad_connected {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) (s t : List Bool)
    (hs : s ∈ actualBinaryWords N) (ht : t ∈ actualBinaryWords N)
    (hsg : ¬ moleculeContourBad hL s ω) (htg : ¬ moleculeContourBad hL t ω) :
    indexedEdgeReach (wordEffectiveEdges hL ω) Prod.fst wordEdgeParent
      (molecularWordVertex L N s) (molecularWordVertex L N t) := by
  by_contra hn
  obtain ⟨f, hneq, hcut, hnonempty, hmin⟩ := wordGraph_disabled_bond L N
    (wordEffectiveEdges hL ω) (molecularWordVertex L N s) (molecularWordVertex L N t) hn
  rw [molecularWordVertex_label f s, molecularWordVertex_label f t] at hneq
  have hfailed := wordEffective_disabled_cut hL ω (wordGraphCut f) hcut
  have hsc : s ∈ wordMolecularSide f (boundedWordLabel f s) :=
    Finset.mem_filter.mpr ⟨hs, rfl⟩
  have htc : t ∈ wordMolecularSide f (boundedWordLabel f t) :=
    Finset.mem_filter.mpr ⟨ht, rfl⟩
  have hnotS : ¬ (wordMolecularSide f (boundedWordLabel f s)).card ≤
      (actualBinaryWords N \ wordMolecularSide f (boundedWordLabel f s)).card := by
    intro hminor
    exact hsg (wordBond_smaller_side_bad hL f hmin hnonempty _ hminor s hsc ω hfailed)
  have hnotT : ¬ (wordMolecularSide f (boundedWordLabel f t)).card ≤
      (actualBinaryWords N \ wordMolecularSide f (boundedWordLabel f t)).card := by
    intro hminor
    exact htg (wordBond_smaller_side_bad hL f hmin hnonempty _ hminor t htc ω hfailed)
  rw [wordMolecularSide_complement_of_ne f _ _ hneq] at hnotS
  rw [wordMolecularSide_complement_of_ne f _ _ hneq.symm] at hnotT
  omega

end

section
open Classical MeasureTheory RAF.Polymer unitInterval

abbrev ActualBinaryWord (N : ℕ) := ↥(actualBinaryWords N)

def actualBinaryRoot (N : ℕ) (hN : 0 < N) : ActualBinaryWord N :=
  ⟨[false], (mem_actualBinaryWords [false] N).mpr ⟨by simp,
    by simpa using (show 1 ≤ N by omega)⟩⟩

noncomputable def badMolecularWords {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) : Finset (ActualBinaryWord N) :=
  Finset.univ.filter (fun s => moleculeContourBad hL s.val ω)

noncomputable def rootedMolecularWords {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) : Finset (ActualBinaryWord N) :=
  Finset.univ.filter (fun s => indexedEdgeReach (wordEffectiveEdges hL ω) Prod.fst wordEdgeParent
    (boundedFoodRoot L N) (molecularWordVertex L N s.val))

theorem molecularWordVertex_food {L N : ℕ} (s : List Bool) (hs : s.length ≤ L) :
    molecularWordVertex L N s = boundedFoodRoot L N := by
  simp [molecularWordVertex, not_lt.mpr hs]

theorem rootedMolecularWords_cover {L N w : ℕ} (hL : 2*w ≤ L)
    (hfood : 0 < L) (hN : 0 < N) (ω : Reaction N → Prop)
    (hr : actualBinaryRoot N hN ∉ badMolecularWords hL ω)
    (s : ActualBinaryWord N) (hs : s ∉ badMolecularWords hL ω) :
    s ∈ rootedMolecularWords hL ω := by
      have hrg : ¬ moleculeContourBad hL (actualBinaryRoot N hN).val ω := by
        simpa [badMolecularWords, Finset.mem_filter, Finset.mem_univ, true_and] using hr
      have hsg : ¬ moleculeContourBad hL s.val ω := by
        simpa [badMolecularWords, Finset.mem_filter, Finset.mem_univ, true_and] using hs
      have hp := outside_moleculeContourBad_connected hL ω (actualBinaryRoot N hN).val s.val
        (actualBinaryRoot N hN).property s.property hrg hsg
      have he : molecularWordVertex L N (actualBinaryRoot N hN).val = boundedFoodRoot L N :=
        molecularWordVertex_food _ (by simp [actualBinaryRoot]; omega)
      rw [he] at hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
/-- Unconditional rooted effective-component mass bound, counting every actual
food molecule separately rather than assigning unit weight to the contracted root. -/
theorem measure_rootedMolecularWords_deficit {L N w k : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (hfood : 0 < L) (hN : 0 < N) (a : I) (d : ℕ) (hd : 0 < d) :
    staticReactionMeasure N a {ω | (rootedMolecularWords hL ω).card+d ≤
      (actualBinaryWords N).card} ≤
      contourBudget a k/(1-contourBudget a k) +
      ((actualBinaryWords N).card : ENNReal)*(contourBudget a k/(1-contourBudget a k))/d := by
      have hm := measure_pool_deficit_le (staticReactionMeasure N a)
        (badMolecularWords hL) (rootedMolecularWords hL) (actualBinaryRoot N hN)
        (fun ω hr s hs => rootedMolecularWords_cover hL hfood hN ω hr s hs)
        (contourBudget a k/(1-contourBudget a k)) (by
          intro s
          simpa only [badMolecularWords, Finset.mem_filter, Finset.mem_univ, true_and] using
            measure_moleculeContourBad_le hL hk s.val a) d hd
      simpa [Fintype.card_coe] using hm

end

section
open Classical RAF.Polymer RAF.Concrete

theorem literalFoodEdge_generated_iff {N L : ℕ} (S : Finset (Reaction N))
    {u v : List Bool} (h : literalFoodEdge L S u v) :
    contractedWordGenerated L S u ↔ contractedWordGenerated L S v := by
  obtain ⟨r, hr, hp, hf⟩ := h
  rw [← hp, contractedWordGenerated_iff]
  rcases hf with ⟨hl, he⟩ | ⟨hh, he⟩
  · rw [← he, contractedWordGenerated_iff]
    exact ⟨fun h => (temporaryReactionClosure_cleavage S r hr h).2,
      fun h => temporaryReactionClosure_ligation S r hr (temporaryReactionClosure_food S _ hl) h⟩
  · rw [← he, contractedWordGenerated_iff]
    exact ⟨fun h => (temporaryReactionClosure_cleavage S r hr h).1,
      fun h => temporaryReactionClosure_ligation S r hr h (temporaryReactionClosure_food S _ hh)⟩

theorem literalFoodPath_generated_iff {N L : ℕ} (S : Finset (Reaction N))
    {u v : List Bool} (h : Relation.EqvGen (literalFoodEdge L S) u v) :
    contractedWordGenerated L S u ↔ contractedWordGenerated L S v := by
  induction h with
  | rel _ _ h => exact literalFoodEdge_generated_iff S h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem literalFoodPath_mono {N L : ℕ} {S T : Finset (Reaction N)} (hST : S ⊆ T)
    {u v : List Bool} (h : Relation.EqvGen (literalFoodEdge L S) u v) :
    Relation.EqvGen (literalFoodEdge L T) u v := by
  induction h with
  | rel u v h =>
    obtain ⟨r, hr, hp, hf⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨r, hST hr, hp, hf⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

noncomputable def staticOpenReactions {N : ℕ} (ω : Reaction N → Prop) : Finset (Reaction N) :=
  Finset.univ.filter ω

theorem wordEffective_generated_iff {L N w : ℕ} (hL : 2*w ≤ L) (ω : Reaction N → Prop)
    (e : WordBasicEdge L N) (he : e ∈ wordEffectiveEdges hL ω) :
    contractedWordGenerated L (staticOpenReactions ω) e.1.val ↔
      contractedWordGenerated L (staticOpenReactions ω) (wordEdgeParent e).val := by
      obtain ⟨hb, j, hj⟩ := Finset.mem_filter.mp he
      have hn := (Finset.mem_filter.mp hb).2
      have hp := wordDetourSource_reach_parent hL (e,j) hn
      have hsub : wordDetourSourceReactions hL (e,j) ⊆ staticOpenReactions ω := by
        intro r hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj r hr⟩
      have hf := literalFoodPath_generated_iff (staticOpenReactions ω) (literalFoodPath_mono hsub hp)
      have hlen := boundedFoodWord_nonroot_length e.1 hn
      simpa [wordShortStart, contractFoodWord, ite_eq_right (not_le.mpr hlen)] using hf
theorem wordEffective_reach_generated_iff {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) {u v : BoundedFoodWord L N}
    (h : indexedEdgeReach (wordEffectiveEdges hL ω) Prod.fst wordEdgeParent u v) :
    contractedWordGenerated L (staticOpenReactions ω) u.val ↔
      contractedWordGenerated L (staticOpenReactions ω) v.val := by
  induction h with
  | rel u v h =>
    obtain ⟨e, he, hu, hv⟩ := h
    have hi := wordEffective_generated_iff hL ω e he
    rw [hu, hv] at hi
    exact hi
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem molecularWordVertex_val {L N : ℕ} (s : List Bool) (hN : s.length ≤ N) :
    (molecularWordVertex L N s).val = contractFoodWord L s := by
  by_cases hL : s.length ≤ L
  · simp [molecularWordVertex_food s hL, contractFoodWord, hL, boundedFoodRoot]
  · simp [molecularWordVertex, not_le.mp hL, hN, contractFoodWord, hL]

noncomputable def actualWordSource {N : ℕ} (s : ActualBinaryWord N) : Molecule N :=
  sourceWordMolecule s.val (by
    have h := (mem_actualBinaryWords s.val N).mp s.property
    exact List.length_pos_iff.mpr h.1) ((mem_actualBinaryWords s.val N).mp s.property).2

@[simp] theorem actualWordSource_word {N : ℕ} (s : ActualBinaryWord N) :
    moleculeWord (actualWordSource s) = s.val := sourceWordMolecule_word _ _ _

theorem actualWordSource_injective {N : ℕ} : Function.Injective (@actualWordSource N) := by
    intro s t h
    apply Subtype.ext
    have hw := congrArg moleculeWord h
    simpa [actualWordSource_word] using hw
/-- The rooted effective component really is contained in ordinary reversible
closure from temporary food, using only reactions open in this same field. -/
theorem rootedMolecularWords_source_mem {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) (s : ActualBinaryWord N) (hs : s ∈ rootedMolecularWords hL ω) :
    actualWordSource s ∈ temporaryReactionClosure L (staticOpenReactions ω) := by
    have hp := (Finset.mem_filter.mp hs).2
    have hi := wordEffective_reach_generated_iff hL ω hp
    have hg : contractedWordGenerated L (staticOpenReactions ω)
        (molecularWordVertex L N s.val).val := hi.mp (contractedWordGenerated_root _)
    rw [molecularWordVertex_val s.val ((mem_actualBinaryWords s.val N).mp s.property).2] at hg
    apply (contractedWordGenerated_iff (staticOpenReactions ω) (actualWordSource s)).mp
    simpa [actualWordSource_word] using hg
theorem rootedMolecularWords_card_le_closure {L N w : ℕ} (hL : 2*w ≤ L)
    (ω : Reaction N → Prop) :
    (rootedMolecularWords hL ω).card ≤ (temporaryReactionClosure L (staticOpenReactions ω)).card := by
  apply Finset.card_le_card_of_injOn actualWordSource
  · exact rootedMolecularWords_source_mem hL ω
  · intro s _ t _ h
    exact actualWordSource_injective h

end

section
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

noncomputable def fixedPoolParameter (p : I) (k : ℕ) : I := σ ((σ p)^k)

@[simp] theorem fixedPoolParameter_coe (p : I) (k : ℕ) :
    (fixedPoolParameter p k : ℝ) = 1-(1-(p : ℝ))^k := by
  simp [fixedPoolParameter]

theorem fixedPoolParameter_ennreal (p : I) (k : ℕ) :
    (toNNReal (fixedPoolParameter p k) : ENNReal) =
      1-(toNNReal (σ p) : ENNReal)^k := by
  have hpow : toNNReal ((σ p)^k) = (toNNReal (σ p))^k := by
    apply NNReal.eq
    simp
  apply ENNReal.eq_sub_of_add_eq (by simp)
  rw [← ENNReal.coe_pow, ← hpow, ← ENNReal.coe_add]
  simp [fixedPoolParameter]

theorem fixedPool_iIndep {n : ℕ} (lambda : ℝ) (C : Finset (Molecule n)) :
    iIndepFun (fun r (ω : AmbientCoord n → Prop) => catalystPoolOpen ω C r)
      (ambientPiMeasure n lambda) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _hsets
  have hh := measure_columnEvents lambda
    (fun r col => (∃ x ∈ C, col x) ∈ sets r) S
  have he : (⋂ r ∈ S, (fun ω : AmbientCoord n → Prop => catalystPoolOpen ω C r) ⁻¹' sets r) =
      {ω | ∀ r ∈ S, (∃ x ∈ C, ω (x,r)) ∈ sets r} := by
    ext ω
    simp [catalystPoolOpen]
  rw [he]
  exact hh

theorem fixedPool_open_measure {n : ℕ} (lambda : ℝ) (C : Finset (Molecule n))
    (r : Reaction n) :
    ambientPiMeasure n lambda {ω | catalystPoolOpen ω C r} =
      (toNNReal (fixedPoolParameter (catalysisP n lambda) C.card) : ENNReal) := by
  rw [fixedPoolParameter_ennreal]
  simpa [catalystPoolFamilyOpen] using measure_catalystPoolFamilyOpen_card lambda C {r}

theorem probability_prop_eq_of_true (μ ν : Measure Prop)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ {True} = ν {True}) : μ = ν := by
    apply Measure.ext_of_singleton
    intro q
    by_cases hq : q
    · have he : q = True := propext (iff_true_intro hq)
      simpa [he] using h
    · have he : q = False := propext (iff_false_intro hq)
      have hs : ({False} : Set Prop) = {True}ᶜ := by ext t; simp
      rw [he, hs, measure_compl (MeasurableSet.singleton _) (measure_ne_top _ _),
        measure_compl (MeasurableSet.singleton _) (measure_ne_top _ _), measure_univ, measure_univ, h]
theorem fixedPool_column_map {n : ℕ} (lambda : ℝ) (C : Finset (Molecule n))
    (r : Reaction n) :
    (ambientPiMeasure n lambda).map (fun ω => catalystPoolOpen ω C r) =
      ambientCoordLaw (fixedPoolParameter (catalysisP n lambda) C.card) := by
    have hm := measurable_of_finite fun ω : AmbientCoord n → Prop => catalystPoolOpen ω C r
    apply probability_prop_eq_of_true
    rw [Measure.map_apply hm (MeasurableSet.singleton _)]
    have he : (fun ω : AmbientCoord n → Prop => catalystPoolOpen ω C r) ⁻¹' {True} =
        {ω | catalystPoolOpen ω C r} := by ext ω; simp
    rw [he, fixedPool_open_measure]
    simp [ambientCoordLaw]
/-- Exact full iid law of the field supported by a deterministic catalyst pool.
This does not assert independence for a pool selected from the same sample. -/
theorem fixedPool_reaction_map {n : ℕ} (lambda : ℝ) (C : Finset (Molecule n)) :
    (ambientPiMeasure n lambda).map (fun ω r => catalystPoolOpen ω C r) =
      staticReactionMeasure n (fixedPoolParameter (catalysisP n lambda) C.card) := by
    rw [(fixedPool_iIndep lambda C).map_fun_eq_pi_map
      fun r => (measurable_of_finite _).aemeasurable]
    simp_rw [fixedPool_column_map]
    exact (Measure.infinitePi_eq_pi _).symm
theorem fixedPool_closure_statistic {n : ℕ} (lambda : ℝ) (C : Finset (Molecule n))
    (closure : Finset (Reaction n) → Finset (Molecule n)) (P : Finset (Molecule n) → Prop) :
    ambientPiMeasure n lambda {ω | P (closure (catalystActive ω C))} =
      staticReactionMeasure n (fixedPoolParameter (catalysisP n lambda) C.card)
        {ω | P (closure (staticOpenReactions ω))} := by
  rw [← fixedPool_reaction_map lambda C, Measure.map_apply (measurable_of_finite _)
    (Set.Finite.measurableSet (Set.toFinite _))]
  rfl

theorem source_mass_ge_iid_static {n : ℕ} (lambda : ℝ)
    (closure : Finset (Reaction n) → Finset (Molecule n)) (hclosure : Monotone closure)
    (k T : ℕ) :
    staticReactionMeasure n (fixedPoolParameter (catalysisP n lambda)
      (finiteInitialSegment (Molecule n) k).card) {ω | k ≤ (closure (staticOpenReactions ω)).card} ≤
    ambientPiMeasure n lambda {ω | k ≤ (closure (peelingActiveAt (catalystActive ω) closure T)).card} := by
    rw [← fixedPool_closure_statistic lambda (finiteInitialSegment (Molecule n) k)
      closure fun S => k ≤ S.card]
    exact measure_source_mass_ge_static lambda closure hclosure k T
end

section

/-- Ordinary reversible generation in the countable word universe. Unlike
the older ligation-only exploration, this includes recovery of both factors. -/
inductive InfiniteReversibleGenerated (L : ℕ) (field : InfiniteSplitEnvironment) :
    List Bool → Prop
  | food {w} (hne : w ≠ []) (hL : w.length ≤ L) :
      InfiniteReversibleGenerated L field w
  | ligate {u v} (hu : InfiniteReversibleGenerated L field u)
      (hv : InfiniteReversibleGenerated L field v) (ho : field (u ++ v) u.length) :
      InfiniteReversibleGenerated L field (u ++ v)
  | left {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : InfiniteReversibleGenerated L field (u ++ v))
      (ho : field (u ++ v) u.length) : InfiniteReversibleGenerated L field u
  | right {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : InfiniteReversibleGenerated L field (u ++ v))
      (ho : field (u ++ v) u.length) : InfiniteReversibleGenerated L field v

inductive FiniteReversibleGenerated (N L : ℕ) (field : InfiniteSplitEnvironment) :
    List Bool → Prop
  | food {w} (hne : w ≠ []) (hL : w.length ≤ L) (hN : w.length ≤ N) :
      FiniteReversibleGenerated N L field w
  | ligate {u v} (hu : FiniteReversibleGenerated N L field u)
      (hv : FiniteReversibleGenerated N L field v) (ho : field (u ++ v) u.length)
      (hN : (u ++ v).length ≤ N) : FiniteReversibleGenerated N L field (u ++ v)
  | left {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : FiniteReversibleGenerated N L field (u ++ v))
      (ho : field (u ++ v) u.length) : FiniteReversibleGenerated N L field u
  | right {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : FiniteReversibleGenerated N L field (u ++ v))
      (ho : field (u ++ v) u.length) : FiniteReversibleGenerated N L field v

theorem finiteReversibleGenerated_mono_cap {N M L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool} (hNM : N ≤ M)
    (h : FiniteReversibleGenerated N L field w) :
    FiniteReversibleGenerated M L field w := by
  induction h with
  | food hn hL hN => exact .food hn hL (hN.trans hNM)
  | ligate _ _ ho hN ihu ihv => exact .ligate ihu ihv ho (hN.trans hNM)
  | left hu hv _ ho ih => exact .left hu hv ih ho
  | right hu hv _ ho ih => exact .right hu hv ih ho

theorem finiteReversibleGenerated_to_infinite {N L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : FiniteReversibleGenerated N L field w) : InfiniteReversibleGenerated L field w := by
  induction h with
  | food hn hL _ => exact .food hn hL
  | ligate _ _ ho _ ihu ihv => exact .ligate ihu ihv ho
  | left hu hv _ ho ih => exact .left hu hv ih ho
  | right hu hv _ ho ih => exact .right hu hv ih ho

/-- Every reversible generation has a finite cap certificate, but this cap
need not be the target's length: cleavage can first require a longer product. -/
theorem infiniteReversibleGenerated_finite_certificate {L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : InfiniteReversibleGenerated L field w) :
    ∃ N, FiniteReversibleGenerated N L field w := by
  induction h with
  | @food w hn hL => exact ⟨w.length, .food hn hL le_rfl⟩
  | @ligate u v _ _ ho ihu ihv =>
    obtain ⟨N, hN⟩ := ihu
    obtain ⟨M, hM⟩ := ihv
    refine ⟨max (max N M) (u ++ v).length, .ligate
      (finiteReversibleGenerated_mono_cap (by omega) hN)
      (finiteReversibleGenerated_mono_cap (by omega) hM) ho (by omega)⟩
  | left hu hv _ ho ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨N, .left hu hv hN ho⟩
  | right hu hv _ ho ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨N, .right hu hv hN ho⟩

theorem infiniteReversibleGenerated_iff_finite_certificate {L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool} :
    InfiniteReversibleGenerated L field w ↔ ∃ N, FiniteReversibleGenerated N L field w :=
  ⟨infiniteReversibleGenerated_finite_certificate,
    fun ⟨_, h⟩ => finiteReversibleGenerated_to_infinite h⟩

end

section
open Classical RAF.Polymer RAF.Concrete

/-- Induction over actual reversible generation, including both reaction directions. -/
theorem temporaryReactionClosure_induction {N L : ℕ} (S : Finset (Reaction N))
    (P : Molecule N → Prop)
    (hfood : ∀ x, molLength x ≤ L → P x)
    (hlig : ∀ r ∈ S, P (reactionLeft r) → P (reactionRight r) → P (reactionProduct r))
    (hcleave : ∀ r ∈ S, P (reactionProduct r) → P (reactionLeft r) ∧ P (reactionRight r))
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure L S) : P x := by
    obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure S x).mp hx
    have hall : ∀ k, ∀ x ∈ revClosureAt (binaryPolymerCRS N L) S k, P x := by
      intro k
      induction k with
      | zero =>
        intro x hx
        exact hfood x (by simpa [revClosureAt, binaryPolymerCRS, binaryFood] using hx)
      | succ k ih =>
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact ih x hx
        · obtain ⟨r, hr, hx⟩ := Finset.mem_biUnion.mp hx
          rcases Finset.mem_union.mp hx with hx | hx
          · by_cases hen : RevEnabledLhs (binaryPolymerCRS N L)
                (revClosureAt (binaryPolymerCRS N L) S k) r
            · rw [ite_eq_left hen] at hx
              have he := Finset.mem_singleton.mp hx
              subst x
              have hh : reactionLeft r ∈ revClosureAt (binaryPolymerCRS N L) S k ∧
                  reactionRight r ∈ revClosureAt (binaryPolymerCRS N L) S k := by
                simpa [RevEnabledLhs, binaryPolymerCRS, Finset.insert_subset_iff,
                  Finset.singleton_subset_iff] using hen
              exact hlig r hr (ih _ hh.1) (ih _ hh.2)
            · simp [hen] at hx
          · by_cases hen : RevEnabledRhs (binaryPolymerCRS N L)
                (revClosureAt (binaryPolymerCRS N L) S k) r
            · rw [ite_eq_left hen] at hx
              have hp : reactionProduct r ∈ revClosureAt (binaryPolymerCRS N L) S k := by
                simpa [RevEnabledRhs, binaryPolymerCRS] using hen
              have hh := hcleave r hr (ih _ hp)
              have he : x = reactionLeft r ∨ x = reactionRight r := by
                simpa [binaryPolymerCRS] using hx
              rcases he with rfl | rfl
              · exact hh.1
              · exact hh.2
            · simp [hen] at hx
    exact hall k x hk
/-- Once a smaller-food closure generates the supplied seed, it contains every
generation using that seed and any subset of its reactions. -/
theorem temporaryReactionClosure_seed_transfer {N L K : ℕ}
    {S T : Finset (Reaction N)} (hST : S ⊆ T)
    (hseed : ∀ x, molLength x ≤ L → x ∈ temporaryReactionClosure K T) :
    temporaryReactionClosure L S ⊆ temporaryReactionClosure K T := by
  intro x hx
  exact temporaryReactionClosure_induction S (fun y => y ∈ temporaryReactionClosure K T)
    hseed (fun r hr => temporaryReactionClosure_ligation T r (hST hr))
    (fun r hr => temporaryReactionClosure_cleavage T r (hST hr)) x hx

theorem source_append_split {N : ℕ} (u v : List Bool)
    (hu : 0 < u.length) (hv : 0 < v.length) (hN : u.length + v.length ≤ N) :
    ∃ r : Reaction N,
      moleculeWord (reactionLeft r) = u ∧
      moleculeWord (reactionRight r) = v ∧
      moleculeWord (reactionProduct r) = u ++ v := by
  let x := sourceWordMolecule (u ++ v) (by simp; omega) (by simpa using hN)
  let r := sourceSplitReaction x u.length hu (by simp [x]; omega)
  refine ⟨r, ?_, ?_, ?_⟩
  · simp [r, moleculeWord_reactionLeft, x]
  · simp [r, moleculeWord_reactionRight, x]
  · simp [r, x]

/-- Appending a word needs at most one literal reaction per new letter.
The statement retains its cap and product-length band for disjoint trials. -/
theorem append_trial_support {N : ℕ} (w v : List Bool)
    (hw : 0 < w.length) (hN : w.length + v.length ≤ N) :
    ∃ S : Finset (Reaction N), S.card ≤ v.length ∧
      (∀ r ∈ S, w.length < molLength (reactionProduct r) ∧
        molLength (reactionProduct r) ≤ w.length + v.length) ∧
      ∀ T : Finset (Reaction N), S ⊆ T →
        ∀ x ∈ temporaryReactionClosure 2 T, moleculeWord x = w →
          ∃ y ∈ temporaryReactionClosure 2 T, moleculeWord y = w ++ v := by
    induction v using List.reverseRecOn with
    | nil =>
      refine ⟨∅, by simp, by simp, ?_⟩
      intro T _ x hx he
      exact ⟨x, hx, by simpa using he⟩
    | append_singleton v b ih =>
      have hn : w.length + v.length ≤ N := by
        simp only [List.length_append, List.length_singleton] at hN
        omega
      obtain ⟨S, hcard, hband, hgen⟩ := ih hn
      obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) (w ++ v) [b]
        (by simp; omega) (by simp) (by simpa [List.length_append, Nat.add_assoc] using hN)
      have hlen : molLength (reactionProduct r) = w.length + v.length + 1 := by
        rw [← moleculeWord_length, hp]
        simp [Nat.add_assoc]
      refine ⟨insert r S, ?_, ?_, ?_⟩
      · have hc := Finset.card_insert_le r S
        simp only [List.length_append, List.length_singleton]
        omega
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · simp only [List.length_append, List.length_singleton]
          omega
        · have hh := hband q hq
          simp only [List.length_append, List.length_singleton]
          omega
      · intro T hST x hx he
        obtain ⟨y, hy, hey⟩ := hgen T (fun q hq => hST (Finset.mem_insert_of_mem hq)) x hx he
        have hleft := moleculeWord_injective (hl.trans hey.symm)
        have hright : molLength (reactionRight r) ≤ 2 := by
          rw [← moleculeWord_length, hr]
          simp
        refine ⟨reactionProduct r, temporaryReactionClosure_ligation T r
          (hST (Finset.mem_insert_self _ _)) (hleft.symm ▸ hy)
          (temporaryReactionClosure_food T _ hright), ?_⟩
        simpa [List.append_assoc] using hp
/-- A long generated word can manufacture any nonempty target by a bounded
append-and-cleave trial, without assuming the target is already food. -/
theorem target_trial_support {N : ℕ} (w v : List Bool)
    (hw : 0 < w.length) (hv : 0 < v.length) (hN : w.length + v.length ≤ N) :
    ∃ S : Finset (Reaction N), S.card ≤ v.length + 1 ∧
      (∀ r ∈ S, w.length < molLength (reactionProduct r) ∧
        molLength (reactionProduct r) ≤ w.length + v.length) ∧
      ∀ T : Finset (Reaction N), S ⊆ T →
        ∀ x ∈ temporaryReactionClosure 2 T, moleculeWord x = w →
          ∃ y ∈ temporaryReactionClosure 2 T, moleculeWord y = v := by
    obtain ⟨S, hc, hb, hg⟩ := append_trial_support w v hw hN
    obtain ⟨r, _, hr, hp⟩ := source_append_split (N := N) w v hw hv hN
    have hlen : molLength (reactionProduct r) = w.length + v.length := by
      rw [← moleculeWord_length, hp, List.length_append]
    refine ⟨insert r S, (Finset.card_insert_le r S).trans (by omega), ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · omega
      · exact hb q hq
    · intro T hST x hx he
      obtain ⟨y, hy, hey⟩ := hg T (fun q hq => hST (Finset.mem_insert_of_mem hq)) x hx he
      have heq := moleculeWord_injective (hp.trans hey.symm)
      exact ⟨reactionRight r, (temporaryReactionClosure_cleavage T r
        (hST (Finset.mem_insert_self _ _)) (heq.symm ▸ hy)).2, hr⟩

noncomputable def restrictedSplitReactions (N : ℕ) (field : InfiniteSplitEnvironment) :
    Finset (Reaction N) := Finset.univ.filter
      (fun r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r))

theorem moleculeWord_nonempty {N : ℕ} (x : Molecule N) : moleculeWord x ≠ [] := by
    have h := moleculeWord_length x
    intro he
    rw [he] at h
    simp [List.length_nil] at h
    unfold molLength at h
    omega
theorem moleculeWord_cap {N : ℕ} (x : Molecule N) : (moleculeWord x).length ≤ N := by
    rw [moleculeWord_length]
    unfold molLength
    omega
theorem reaction_words_append {N : ℕ} (r : Reaction N) :
    moleculeWord (reactionLeft r) ++ moleculeWord (reactionRight r) =
      moleculeWord (reactionProduct r) := by
  rw [moleculeWord_reactionLeft, moleculeWord_reactionRight, List.take_append_drop]

theorem literalClosure_to_finiteReversible {N L : ℕ} (field : InfiniteSplitEnvironment)
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure L (restrictedSplitReactions N field)) :
    FiniteReversibleGenerated N L field (moleculeWord x) := by
      apply temporaryReactionClosure_induction (restrictedSplitReactions N field)
        (fun y => FiniteReversibleGenerated N L field (moleculeWord y)) ?_ ?_ ?_ x hx
      · intro y hy
        exact .food (moleculeWord_nonempty y) (by rwa [moleculeWord_length]) (moleculeWord_cap y)
      · intro r hr hl hh
        have ho := (Finset.mem_filter.mp hr).2
        rw [← reaction_words_append r] at ho ⊢
        apply FiniteReversibleGenerated.ligate hl hh
        · simpa [moleculeWord_length, molLength_reactionLeft] using ho
        · rw [reaction_words_append]
          exact moleculeWord_cap _
      · intro r hr hp
        have ho := (Finset.mem_filter.mp hr).2
        rw [← reaction_words_append r] at ho hp
        have hf : field (moleculeWord (reactionLeft r) ++ moleculeWord (reactionRight r))
            (moleculeWord (reactionLeft r)).length := by
          simpa [moleculeWord_length, molLength_reactionLeft] using ho
        exact ⟨.left (moleculeWord_nonempty _) (moleculeWord_nonempty _) hp hf,
          .right (moleculeWord_nonempty _) (moleculeWord_nonempty _) hp hf⟩
theorem finiteReversible_to_literalClosure {N L : ℕ} {field : InfiniteSplitEnvironment}
    {w : List Bool} (hw : FiniteReversibleGenerated N L field w) :
    ∃ x ∈ temporaryReactionClosure L (restrictedSplitReactions N field), moleculeWord x = w := by
  let S := restrictedSplitReactions N field
  have split_mem (u v : List Bool) (r : Reaction N)
      (hl : moleculeWord (reactionLeft r) = u)
      (hp : moleculeWord (reactionProduct r) = u ++ v) (ho : field (u ++ v) u.length) : r ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa [hp, ← molLength_reactionLeft, ← moleculeWord_length, hl] using ho
  induction hw with
  | @food w hn hL hN =>
    exact ⟨sourceWordMolecule w (List.length_pos_iff.mpr hn) hN,
      temporaryReactionClosure_food S _ (by simpa using hL), sourceWordMolecule_word _ _ _⟩
  | @ligate u v _ _ ho hN ihu ihv =>
    obtain ⟨x, hx, hxu⟩ := ihu
    obtain ⟨y, hy, hyv⟩ := ihv
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) u v
      (List.length_pos_iff.mpr (hxu ▸ moleculeWord_nonempty x))
      (List.length_pos_iff.mpr (hyv ▸ moleculeWord_nonempty y)) (by simpa using hN)
    have heL := moleculeWord_injective (hl.trans hxu.symm)
    have heR := moleculeWord_injective (hr.trans hyv.symm)
    exact ⟨reactionProduct r, temporaryReactionClosure_ligation S r (split_mem u v r hl hp ho)
      (heL.symm ▸ hx) (heR.symm ▸ hy), hp⟩
  | @left u v hu hv _ ho ih =>
    obtain ⟨x, hx, hxp⟩ := ih
    obtain ⟨r, hl, _, hp⟩ := source_append_split (N := N) u v
      (List.length_pos_iff.mpr hu) (List.length_pos_iff.mpr hv)
      (by rw [← List.length_append, ← hxp]; exact moleculeWord_cap x)
    exact ⟨reactionLeft r, (temporaryReactionClosure_cleavage S r (split_mem u v r hl hp ho)
      ((moleculeWord_injective (hp.trans hxp.symm)).symm ▸ hx)).1, hl⟩
  | @right u v hu hv _ ho ih =>
    obtain ⟨x, hx, hxp⟩ := ih
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) u v
      (List.length_pos_iff.mpr hu) (List.length_pos_iff.mpr hv)
      (by rw [← List.length_append, ← hxp]; exact moleculeWord_cap x)
    exact ⟨reactionRight r, (temporaryReactionClosure_cleavage S r (split_mem u v r hl hp ho)
      ((moleculeWord_injective (hp.trans hxp.symm)).symm ▸ hx)).2, hr⟩
theorem finiteReversible_iff_literalClosure {N L : ℕ} (field : InfiniteSplitEnvironment)
    (w : List Bool) : FiniteReversibleGenerated N L field w ↔
      ∃ x ∈ temporaryReactionClosure L (restrictedSplitReactions N field), moleculeWord x = w :=
  ⟨finiteReversible_to_literalClosure,
    fun ⟨x, hx, he⟩ => he ▸ literalClosure_to_finiteReversible field x hx⟩

end

section
open Classical MeasureTheory RAF.Polymer RAF.Concrete

theorem measurable_finiteReversibleGenerated (N L : ℕ) (w : List Bool) :
    Measurable (fun field : InfiniteSplitEnvironment => FiniteReversibleGenerated N L field w) := by
  let restrict : InfiniteSplitEnvironment → (Reaction N → Prop) :=
    fun field r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r)
  have hm : Measurable restrict := by
    apply Measurable.of_eval
    intro r
    exact (measurable_pi_apply (reactionLeftLength r)).comp
      (measurable_pi_apply (moleculeWord (reactionProduct r)))
  let event : (Reaction N → Prop) → Prop := fun ω => ∃ x ∈ temporaryReactionClosure L
    (Finset.univ.filter ω), moleculeWord x = w
  have he : (fun field => FiniteReversibleGenerated N L field w) = event ∘ restrict := by
    funext field
    exact propext (finiteReversible_iff_literalClosure field w)
  rw [he]
  exact (measurable_of_finite event).comp hm

theorem measurableSet_finiteReversibleGenerated (N L : ℕ) (w : List Bool) :
    MeasurableSet {field : InfiniteSplitEnvironment | FiniteReversibleGenerated N L field w} := by
  simpa using (MeasurableSet.singleton True).preimage (measurable_finiteReversibleGenerated N L w)

theorem measurableSet_infiniteReversibleGenerated (L : ℕ) (w : List Bool) :
    MeasurableSet {field : InfiniteSplitEnvironment | InfiniteReversibleGenerated L field w} := by
      have he : {field : InfiniteSplitEnvironment | InfiniteReversibleGenerated L field w} =
          ⋃ N : ℕ, {field | FiniteReversibleGenerated N L field w} := by
        ext field
        simp [Set.mem_ofPred_eq, Set.mem_iUnion]
        exact infiniteReversibleGenerated_iff_finite_certificate
      rw [he]
      exact MeasurableSet.iUnion fun N => measurableSet_finiteReversibleGenerated N L w
/-- Any finite collection of infinite generation certificates fits in one cap. -/
theorem finite_seed_common_cap {L : ℕ} {field : InfiniteSplitEnvironment}
    (seed : Finset (List Bool)) :
    (∀ w ∈ seed, InfiniteReversibleGenerated L field w) ↔
      ∃ N, ∀ w ∈ seed, FiniteReversibleGenerated N L field w := by
    constructor
    · induction seed using Finset.induction_on with
      | empty => intro _; exact ⟨0, by simp⟩
      | @insert w seed _ ih =>
        intro h
        obtain ⟨N, hN⟩ := infiniteReversibleGenerated_finite_certificate
          (h w (Finset.mem_insert_self _ _))
        obtain ⟨M, hM⟩ := ih fun v hv => h v (Finset.mem_insert_of_mem hv)
        refine ⟨max N M, ?_⟩
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact finiteReversibleGenerated_mono_cap (Nat.le_max_left _ _) hN
        · exact finiteReversibleGenerated_mono_cap (Nat.le_max_right _ _) (hM v hv)
    · rintro ⟨N, hN⟩ w hw
      exact finiteReversibleGenerated_to_infinite (hN w hw)
theorem measurableSet_finite_seed (N L : ℕ) (seed : Finset (List Bool)) :
    MeasurableSet {field : InfiniteSplitEnvironment |
      ∀ w ∈ seed, FiniteReversibleGenerated N L field w} := by
    have he : {field : InfiniteSplitEnvironment | ∀ w ∈ seed, FiniteReversibleGenerated N L field w} =
        ⋂ w ∈ seed, {field | FiniteReversibleGenerated N L field w} := by ext field; simp
    rw [he]
    exact MeasurableSet.biInter (Finset.countable_toSet seed)
      fun w _ => measurableSet_finiteReversibleGenerated N L w
/-- Finite seed probabilities approximate the infinite seed event under any
fixed measure on the countable split environment. No cap exchange is assumed. -/
theorem finite_seed_probability_tendsto (μ : Measure InfiniteSplitEnvironment)
    (L : ℕ) (seed : Finset (List Bool)) :
    Filter.Tendsto (fun N => μ {field | ∀ w ∈ seed, FiniteReversibleGenerated N L field w})
      Filter.atTop (nhds (μ {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w})) := by
    let E : ℕ → Set InfiniteSplitEnvironment :=
      fun N => {field | ∀ w ∈ seed, FiniteReversibleGenerated N L field w}
    have hm : Monotone E := by
      intro N M hNM field hfield w hw
      exact finiteReversibleGenerated_mono_cap hNM (hfield w hw)
    have he : (⋃ N, E N) = {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w} := by
      ext field
      simp [Set.mem_iUnion, Set.mem_ofPred_eq, E]
      exact (finite_seed_common_cap seed).symm
    have ht := tendsto_measure_iUnion_atTop (μ := μ) hm
    rw [he] at ht
    exact ht

end

section
open Classical

def ReversibleUnbounded (L : ℕ) (field : InfiniteSplitEnvironment) : Prop :=
  ∀ K : ℕ, ∃ w, K < w.length ∧ InfiniteReversibleGenerated L field w

end

section
open Classical MeasureTheory

/-- If generation ever leaves length K, its first escape fits within cap 2K.
Cleavage cannot create the first longer word. -/
theorem reversible_generated_or_escape {L K : ℕ} (hLK : L ≤ K)
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : InfiniteReversibleGenerated L field w) :
    FiniteReversibleGenerated (2*K) L field w ∨
      ∃ v, K < v.length ∧ FiniteReversibleGenerated (2*K) L field v := by
    induction h with
    | food hn hL => exact Or.inl (.food hn hL (by omega))
    | @ligate u v _ _ ho ihu ihv =>
      rcases ihu with hu | he
      · rcases ihv with hv | he
        · by_cases huk : u.length ≤ K
          · by_cases hvk : v.length ≤ K
            · exact Or.inl (.ligate hu hv ho (by simp [List.length_append]; omega))
            · exact Or.inr ⟨v, by omega, hv⟩
          · exact Or.inr ⟨u, by omega, hu⟩
        · exact Or.inr he
      · exact Or.inr he
    | left hu hv _ ho ih =>
      rcases ih with hp | he
      · exact Or.inl (.left hu hv hp ho)
      · exact Or.inr he
    | right hu hv _ ho ih =>
      rcases ih with hp | he
      · exact Or.inl (.right hu hv hp ho)
      · exact Or.inr he
theorem reversible_escape_iff_cap {L K : ℕ} (hLK : L ≤ K)
    (field : InfiniteSplitEnvironment) :
    (∃ w, K < w.length ∧ InfiniteReversibleGenerated L field w) ↔
      ∃ w, K < w.length ∧ FiniteReversibleGenerated (2*K) L field w := by
  constructor
  · rintro ⟨w, hw, hg⟩
    rcases reversible_generated_or_escape hLK hg with hf | he
    · exact ⟨w, hw, hf⟩
    · exact he
  · rintro ⟨w, hw, hg⟩
    exact ⟨w, hw, finiteReversibleGenerated_to_infinite hg⟩

def reversibleEscapeEvent (L K : ℕ) : Set InfiniteSplitEnvironment :=
  {field | ∃ w, K+L < w.length ∧ FiniteReversibleGenerated (2*(K+L)) L field w}

theorem reversibleEscapeEvent_iff (L K : ℕ) (field : InfiniteSplitEnvironment) :
    field ∈ reversibleEscapeEvent L K ↔
      ∃ w, K+L < w.length ∧ InfiniteReversibleGenerated L field w :=
  (reversible_escape_iff_cap (by omega : L ≤ K+L) field).symm

theorem reversibleEscapeEvent_antitone (L : ℕ) : Antitone (reversibleEscapeEvent L) := by
  intro K M hKM field h
  obtain ⟨w, hw, hg⟩ := (reversibleEscapeEvent_iff L M field).mp h
  exact (reversibleEscapeEvent_iff L K field).mpr ⟨w, by omega, hg⟩

theorem reversibleEscapeEvent_inter (L : ℕ) :
    (⋂ K, reversibleEscapeEvent L K) = {field | ReversibleUnbounded L field} := by
    ext field
    simp [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h K
      obtain ⟨w, hw, hg⟩ := (reversibleEscapeEvent_iff L K field).mp (h K)
      exact ⟨w, by omega, hg⟩
    · intro h K
      exact (reversibleEscapeEvent_iff L K field).mpr (h (K+L))
theorem measurableSet_reversibleEscapeEvent (L K : ℕ) :
    MeasurableSet (reversibleEscapeEvent L K) := by
      have he : reversibleEscapeEvent L K = ⋃ w : List Bool,
          ⋃ (_h : K+L < w.length),
            {field | FiniteReversibleGenerated (2*(K+L)) L field w} := by
        ext field
        simp [reversibleEscapeEvent]
      rw [he]
      exact MeasurableSet.iUnion fun w => MeasurableSet.iUnion
        fun _ => measurableSet_finiteReversibleGenerated _ _ w
end

section
open Classical MeasureTheory ProbabilityTheory unitInterval

def sprinklingParameter (a b : I) : I := σ ((σ a) * (σ b))

theorem sprinklingParameter_value (a b : I) :
    (sprinklingParameter a b : ℝ) = (a : ℝ) + (1-(a : ℝ))*(b : ℝ) := by
  change 1-((1-(a : ℝ))*(1-(b : ℝ))) = _
  ring

/-- Exact law of the union of two independent Bernoulli coordinates. -/
theorem ambientCoordLaw_union (a b : I) :
    ((ambientCoordLaw a).prod (ambientCoordLaw b)).map (fun p : Prop × Prop => p.1 ∨ p.2) =
      ambientCoordLaw (sprinklingParameter a b) := by
          let μ := ((ambientCoordLaw a).prod (ambientCoordLaw b)).map
            fun p : Prop × Prop => p.1 ∨ p.2
          have : IsProbabilityMeasure μ := by
            change IsProbabilityMeasure (((ambientCoordLaw a).prod (ambientCoordLaw b)).map
              fun p : Prop × Prop => p.1 ∨ p.2)
            infer_instance
          have hf : μ {False} = ambientCoordLaw (sprinklingParameter a b) {False} := by
            rw [show μ = _ from rfl, Measure.map_apply (measurable_of_finite _)
              (MeasurableSet.singleton False)]
            have he : (fun p : Prop × Prop => p.1 ∨ p.2) ⁻¹' {False} =
                ({False} : Set Prop) ×ˢ {False} := by ext p; simp [Prod.ext_iff]
            rw [he, Measure.prod_prod]
            simp [ambientCoordLaw, sprinklingParameter, ← ENNReal.coe_mul]
            rfl
          have ht : μ {True} = ambientCoordLaw (sprinklingParameter a b) {True} := by
            have he : ({True} : Set Prop) = ({False} : Set Prop)ᶜ := by ext p; simp
            rw [he, measure_compl (MeasurableSet.singleton False) (measure_ne_top _ _),
              measure_compl (MeasurableSet.singleton False) (measure_ne_top _ _), hf]
            simp
          apply Measure.ext_of_singleton
          intro P
          by_cases h : P
          · simpa [show P = True from propext (iff_true_intro h)] using ht
          · simpa [show P = False from propext (iff_false_intro h)] using hf
end

section
open MeasureTheory MeasureTheory.Measure

/-- Reorganizing independent rows as independent columns preserves the full
product law, including dependence within each eventual paired coordinate. -/
theorem infinitePi_transpose {A B X : Type*} [MeasurableSpace X]
    (μ : A → B → Measure X) [∀ a b, IsProbabilityMeasure (μ a b)] :
    (infinitePi (fun a => infinitePi (μ a))).map (fun f b a => f a b) =
      infinitePi (fun b => infinitePi (fun a => μ a b)) := by
                    let U := (MeasurableEquiv.curry A B X).symm
                    let S := MeasurableEquiv.piCongrLeft (fun _ : B × A => X) (Equiv.prodComm A B)
                    let C := MeasurableEquiv.curry B A X
                    have hu : (infinitePi fun a => infinitePi (μ a)).map U =
                        infinitePi fun p : A × B => μ p.1 p.2 := infinitePi_map_curry_symm μ
                    have hs : (infinitePi fun p : A × B => μ p.1 p.2).map S =
                        infinitePi fun p : B × A => μ p.2 p.1 :=
                      infinitePi_map_piCongrLeft (fun p : B × A => μ p.2 p.1) (Equiv.prodComm A B)
                    have hc : (infinitePi fun p : B × A => μ p.2 p.1).map C =
                        infinitePi fun b => infinitePi fun a => μ a b :=
                      infinitePi_map_curry fun b a => μ a b
                    calc
                      _ = (((infinitePi fun a => infinitePi (μ a)).map U).map S).map C := by
                        rw [map_map C.measurable S.measurable, map_map (C.measurable.comp S.measurable) U.measurable]
                        rfl
                      _ = _ := by rw [hu, hs, hc]
end

section
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval

noncomputable def literalSplitCoordinate {N : ℕ} (r : Reaction N) : List Bool × ℕ :=
  (moleculeWord (reactionProduct r), reactionLeftLength r)

theorem literalSplitCoordinate_injective (N : ℕ) : Function.Injective (@literalSplitCoordinate N) := by
  intro r s he
  have hp := moleculeWord_injective (congrArg Prod.fst he)
  have hk := congrArg Prod.snd he
  rcases r with ⟨kr, cr, sr⟩
  rcases s with ⟨ks, cs, ss⟩
  have hidx : kr = ks := congrArg Sigma.fst hp
  subst ks
  have hc : cr = cs := by
    have h := congrArg (fun x : Molecule N => x.2.val) hp
    exact Fin.ext h
  subst cs
  have hs : sr = ss := Fin.ext (by change sr.val + 1 = ss.val + 1 at hk; omega)
  subst ss
  rfl

def currySplitField (ω : (List Bool × ℕ) → Prop) : InfiniteSplitEnvironment :=
  fun w k => ω (w,k)

theorem measurable_currySplitField : Measurable currySplitField := by
  apply Measurable.of_eval
  intro w
  apply Measurable.of_eval
  intro k
  exact measurable_pi_apply (w,k)

noncomputable def infiniteSplitPi (a : I) : Measure ((List Bool × ℕ) → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw a)

noncomputable def infiniteStaticMeasure (a : I) : Measure InfiniteSplitEnvironment :=
  (infiniteSplitPi a).map currySplitField

noncomputable instance infiniteSplitPi_probability (a : I) : IsProbabilityMeasure (infiniteSplitPi a) := by
  unfold infiniteSplitPi
  infer_instance

noncomputable instance infiniteStaticMeasure_probability (a : I) : IsProbabilityMeasure (infiniteStaticMeasure a) := by
  unfold infiniteStaticMeasure
  infer_instance

/-- The infinite iid environment restricts to the exact finite static source
law, with each product/split pair a distinct coordinate. -/
theorem infiniteStatic_restriction_map (N : ℕ) (a : I) :
    (infiniteStaticMeasure a).map
      (fun field r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r)) =
      staticReactionMeasure N a := by
        have hi : iIndepFun (fun z (ω : (List Bool × ℕ) → Prop) => ω z) (infiniteSplitPi a) :=
          iIndepFun_infinitePi fun _ => measurable_id
        have hs := hi.precomp (literalSplitCoordinate_injective N)
        have hm : Measurable fun field : InfiniteSplitEnvironment =>
            fun r : Reaction N => field (moleculeWord (reactionProduct r)) (reactionLeftLength r) := by
          apply Measurable.of_eval
          intro r
          exact (measurable_pi_apply _).comp (measurable_pi_apply _)
        rw [infiniteStaticMeasure, Measure.map_map hm measurable_currySplitField]
        change (infiniteSplitPi a).map (fun ω r => ω (literalSplitCoordinate r)) = _
        rw [hs.map_fun_eq_pi_map fun r => (measurable_pi_apply (literalSplitCoordinate r)).aemeasurable]
        have he (r : Reaction N) : (infiniteSplitPi a).map (fun ω => ω (literalSplitCoordinate r)) =
            ambientCoordLaw a := by rw [infiniteSplitPi, Measure.infinitePi_map_eval]
        simp_rw [he]
        exact (Measure.infinitePi_eq_pi _).symm
theorem finite_static_seed_measure_eq (N L : ℕ) (a : I) (seed : Finset (List Bool)) :
    staticReactionMeasure N a {ω | ∀ w ∈ seed,
      ∃ x ∈ temporaryReactionClosure L (staticOpenReactions ω), moleculeWord x = w} =
    infiniteStaticMeasure a {field | ∀ w ∈ seed, FiniteReversibleGenerated N L field w} := by
  rw [← infiniteStatic_restriction_map N a, Measure.map_apply]
  · congr 1
    ext field
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    apply forall_congr'
    intro w
    apply forall_congr'
    intro _
    exact (finiteReversible_iff_literalClosure field w).symm
  · apply Measurable.of_eval
    intro r
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact Set.Finite.measurableSet (Set.toFinite _)

/-- Actual finite static-source seed probabilities converge to the infinite
reversible seed probability at fixed openness. -/
theorem finite_static_seed_probability_tendsto (L : ℕ) (a : I) (seed : Finset (List Bool)) :
    Filter.Tendsto (fun N => staticReactionMeasure N a {ω | ∀ w ∈ seed,
      ∃ x ∈ temporaryReactionClosure L (staticOpenReactions ω), moleculeWord x = w})
      Filter.atTop (nhds (infiniteStaticMeasure a
        {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w})) := by
  simp_rw [finite_static_seed_measure_eq]
  exact finite_seed_probability_tendsto (infiniteStaticMeasure a) L seed

end

section
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped Topology ENNReal

/-- The effective-component estimate transferred to actual ordinary reversible
closure. The universe cardinality is the literal source molecule count. -/
theorem measure_temporaryClosure_deficit {L N w k : ℕ} (hL : 2*w ≤ L)
    (hk : 5*k ≤ w) (hfood : 0 < L) (hN : 0 < N) (a : I) (d : ℕ) (hd : 0 < d) :
    staticReactionMeasure N a {ω |
      (temporaryReactionClosure L (staticOpenReactions ω)).card+d ≤ Fintype.card (Molecule N)} ≤
      contourBudget a k/(1-contourBudget a k) +
      (Fintype.card (Molecule N) : ENNReal)*(contourBudget a k/(1-contourBudget a k))/d := by
  have hcard : Fintype.card (Molecule N) = (actualBinaryWords N).card := by
    rw [card_molecules_exact, actualBinaryWords_card]
  rw [hcard]
  calc
    _ ≤ staticReactionMeasure N a {ω | (rootedMolecularWords hL ω).card+d ≤
        (actualBinaryWords N).card} := by
      apply measure_mono
      intro ω hω
      have hh := rootedMolecularWords_card_le_closure hL ω
      exact Nat.le_trans (Nat.add_le_add_right hh d) hω
    _ ≤ _ := measure_rootedMolecularWords_deficit hL hk hfood hN a d hd

end

section
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped ENNReal

theorem measurableSet_reversibleUnbounded (L : ℕ) :
    MeasurableSet {field : InfiniteSplitEnvironment | ReversibleUnbounded L field} := by
        have he : {field : InfiniteSplitEnvironment | ReversibleUnbounded L field} =
            ⋂ K : ℕ, ⋃ w : List Bool, ⋃ (_h : K < w.length),
              {field | InfiniteReversibleGenerated L field w} := by
          ext field
          simp [ReversibleUnbounded]
        rw [he]
        exact MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun w =>
          MeasurableSet.iUnion fun _ => measurableSet_infiniteReversibleGenerated L w
end

section
open Classical MeasureTheory ProbabilityTheory unitInterval

theorem iid_union_field_map (C : Type*) (a b : I) :
    ((Measure.infinitePi (fun _ : C => ambientCoordLaw a)).prod
      (Measure.infinitePi (fun _ : C => ambientCoordLaw b))).map
      (fun p c => p.1 c ∨ p.2 c) =
        Measure.infinitePi (fun _ : C => ambientCoordLaw (sprinklingParameter a b)) := by
                    let law : Fin 2 → Measure Prop := fun i => if i = 0 then ambientCoordLaw a else ambientCoordLaw b
                    have : ∀ i, IsProbabilityMeasure (law i) := by intro i; dsimp [law]; split <;> infer_instance
                    let rows := Measure.infinitePi fun i => Measure.infinitePi fun _ : C => law i
                    have hp : rows.map (fun f => (f 0, f 1)) =
                        (Measure.infinitePi fun _ : C => ambientCoordLaw a).prod
                        (Measure.infinitePi fun _ : C => ambientCoordLaw b) := by
                      dsimp only [rows]
                      rw [Measure.infinitePi_eq_pi]
                      simpa [law] using (measurePreserving_piFinTwo
                        fun i => Measure.infinitePi fun _ : C => law i).map_eq
                    have hsingle : (Measure.infinitePi law).map (fun f => f 0 ∨ f 1) =
                        ambientCoordLaw (sprinklingParameter a b) := by
                      have hh := (measurePreserving_piFinTwo law).map_eq
                      have hpair : (Measure.infinitePi law).map (fun f => (f 0, f 1)) =
                          (ambientCoordLaw a).prod (ambientCoordLaw b) := by
                        rw [Measure.infinitePi_eq_pi]
                        simpa [law] using hh
                      rw [← ambientCoordLaw_union a b, ← hpair,
                        Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
                      rfl
                    have ht : rows.map (fun f c i => f i c) =
                        Measure.infinitePi fun _ : C => Measure.infinitePi law :=
                      infinitePi_transpose fun i (_ : C) => law i
                    rw [← hp, Measure.map_map (by fun_prop) (by fun_prop)]
                    change rows.map (fun f c => f 0 c ∨ f 1 c) = _
                    calc
                      _ = (rows.map fun f c i => f i c).map (fun f c => f c 0 ∨ f c 1) := by
                        rw [Measure.map_map (by fun_prop) (by fun_prop)]
                        rfl
                      _ = _ := by
                        rw [ht, Measure.infinitePi_map_pi (fun _ : C => Measure.infinitePi law)
                          (f := fun (_ : C) (f : Fin 2 → Prop) => f 0 ∨ f 1) (fun _ => measurable_of_finite _)]
                        simp_rw [hsingle]
end

section
open Classical MeasureTheory ProbabilityTheory unitInterval Filter
open scoped ENNReal

noncomputable def staticSurvival (a : I) : ENNReal :=
  infiniteStaticMeasure a {field | ReversibleUnbounded 2 field}

end

section
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval

theorem reversible_escape_probability_tendsto
    (μ : Measure InfiniteSplitEnvironment) [IsFiniteMeasure μ] (L : ℕ) :
    Filter.Tendsto (fun K => μ (reversibleEscapeEvent L K)) Filter.atTop
      (nhds (μ {field | ReversibleUnbounded L field})) := by
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun K => (measurableSet_reversibleEscapeEvent L K).nullMeasurableSet)
    (reversibleEscapeEvent_antitone L) ⟨0, measure_ne_top _ _⟩
  rw [reversibleEscapeEvent_inter] at ht
  exact ht

def staticEscapeEvent (L K : ℕ) : Set (Reaction (2*(K+L)) → Prop) :=
  {ω | ∃ x ∈ temporaryReactionClosure L (staticOpenReactions ω),
    K+L < (moleculeWord x).length}

theorem finite_static_escape_measure_eq (L K : ℕ) (a : I) :
    staticReactionMeasure (2*(K+L)) a (staticEscapeEvent L K) =
      infiniteStaticMeasure a (reversibleEscapeEvent L K) := by
  rw [← infiniteStatic_restriction_map (2*(K+L)) a, Measure.map_apply]
  · congr 1
    ext field
    change (∃ x ∈ temporaryReactionClosure L (restrictedSplitReactions _ field),
      K+L < (moleculeWord x).length) ↔
      ∃ w, K+L < w.length ∧ FiniteReversibleGenerated (2*(K+L)) L field w
    constructor
    · rintro ⟨x, hx, hl⟩
      exact ⟨moleculeWord x, hl, literalClosure_to_finiteReversible field x hx⟩
    · rintro ⟨w, hw, hg⟩
      obtain ⟨x, hx, he⟩ := finiteReversible_to_literalClosure hg
      exact ⟨x, hx, by simpa [he] using hw⟩
  · apply Measurable.of_eval
    intro r
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact Set.Finite.measurableSet (Set.toFinite _)

/-- Survival is approximated from above by actual finite static events. -/
theorem finite_static_escape_probability_tendsto (a : I) :
    Filter.Tendsto (fun K => staticReactionMeasure (2*(K+2)) a (staticEscapeEvent 2 K))
      Filter.atTop (nhds (staticSurvival a)) := by
  simp_rw [finite_static_escape_measure_eq]
  exact reversible_escape_probability_tendsto (infiniteStaticMeasure a) 2

theorem static_capped_escape_le (N K : ℕ) (a : I) :
    staticReactionMeasure N a {ω | ∃ x ∈ temporaryReactionClosure 2
      (staticOpenReactions ω), K+2 < molLength x} ≤
      infiniteStaticMeasure a (reversibleEscapeEvent 2 K) := by
    rw [← infiniteStatic_restriction_map N a, Measure.map_apply]
    · apply measure_mono
      intro field h
      change ∃ x ∈ temporaryReactionClosure 2 (restrictedSplitReactions N field),
        K+2 < molLength x at h
      obtain ⟨x,hx,hl⟩ := h
      apply (reversibleEscapeEvent_iff 2 K field).mpr
      exact ⟨moleculeWord x, by simpa [moleculeWord_length] using hl,
        finiteReversibleGenerated_to_infinite (literalClosure_to_finiteReversible field x hx)⟩
    · apply Measurable.of_eval
      intro r
      exact (measurable_pi_apply _).comp (measurable_pi_apply _)
    · exact Set.Finite.measurableSet (Set.toFinite _)
theorem ambient_escape_le_finite_static (n K : ℕ) (lambda : ℝ) :
    ambientPiMeasure n lambda {ω | ∃ x ∈ temporaryReactionClosure 2
      (catalystActive ω Finset.univ), K+2 < molLength x} ≤
    staticReactionMeasure (2*(K+2))
      (fixedPoolParameter (catalysisP n lambda) (Fintype.card (Molecule n)))
      (staticEscapeEvent 2 K) := by
    rw [fixedPool_closure_statistic lambda Finset.univ (temporaryReactionClosure 2)
      fun S => ∃ x ∈ S, K+2 < molLength x, Finset.card_univ,
      finite_static_escape_measure_eq]
    exact static_capped_escape_le n K _
end

section
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped Topology

end

section
open Classical

theorem peelingActiveAt_fixed_persists {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X)
    {t : ℕ} (ht : peelingActiveAt response closure (t+1) = peelingActiveAt response closure t) :
    ∀ j, peelingActiveAt response closure (t+j) = peelingActiveAt response closure t := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      _ = response (closure (peelingActiveAt response closure (t+j))) := by
        rw [Nat.add_succ, peelingActiveAt]
      _ = _ := by rw [ih]; exact ht

/-- A decreasing finite reaction iteration stabilizes by the reaction-cardinality
horizon. This horizon is deterministic and so can be used in a probability bound. -/
theorem peelingActiveAt_stable_card {X R : Type*} [Fintype X] [Fintype R]
    (response : Finset X → Finset R) (closure : Finset R → Finset X)
    (hr : Monotone response) (hc : Monotone closure) :
    peelingActiveAt response closure (Fintype.card R+1) =
      peelingActiveAt response closure (Fintype.card R) := by
    have hanti := peelingActiveAt_antitone response closure hr hc
    by_contra hfail
    have hneq : ∀ t ≤ Fintype.card R,
        peelingActiveAt response closure (t+1) ≠ peelingActiveAt response closure t := by
      intro t ht he
      have h1 := peelingActiveAt_fixed_persists response closure he (Fintype.card R+1-t)
      have h0 := peelingActiveAt_fixed_persists response closure he (Fintype.card R-t)
      have he1 : t+(Fintype.card R+1-t) = Fintype.card R+1 := by omega
      have he0 : t+(Fintype.card R-t) = Fintype.card R := by omega
      rw [he1] at h1
      rw [he0] at h0
      exact hfail (h1.trans h0.symm)
    have hbound : ∀ t ≤ Fintype.card R+1,
        (peelingActiveAt response closure t).card+t ≤ Fintype.card R := by
      intro t
      induction t with
      | zero => intro _; simpa using Finset.card_le_univ (peelingActiveAt response closure 0)
      | succ t ih =>
        intro ht
        have hs := hanti (Nat.le_succ t)
        have hlt : (peelingActiveAt response closure (t+1)).card <
            (peelingActiveAt response closure t).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs,hneq t (by omega)⟩)
        omega
    have hh := hbound (Fintype.card R+1) le_rfl
    omega

end

section
open Classical RAF RAF.Polymer RAF.Concrete

noncomputable def usableClosureReactions {N : ℕ} (L : ℕ) (A : Finset (Reaction N)) :=
  A.filter (fun r => reactionLeft r ∈ temporaryReactionClosure L A ∧
    reactionRight r ∈ temporaryReactionClosure L A ∧
    reactionProduct r ∈ temporaryReactionClosure L A)

/-- Removing reactions whose endpoints are unavailable does not remove any
actual generation step. Both reversible directions are retained. -/
theorem usableClosureReactions_closure {N L : ℕ} (A : Finset (Reaction N)) :
    temporaryReactionClosure L (usableClosureReactions L A) = temporaryReactionClosure L A := by
  have hsub : usableClosureReactions L A ⊆ A := Finset.filter_subset _ _
  have hm := temporaryReactionClosure_mono (L := L) hsub
  apply Finset.Subset.antisymm hm
  intro x hx
  apply temporaryReactionClosure_induction A
    (fun y => y ∈ temporaryReactionClosure L (usableClosureReactions L A)) ?_ ?_ ?_ x hx
  · exact temporaryReactionClosure_food _
  · intro r hr hl hh
    have hp := temporaryReactionClosure_ligation A r hr (hm hl) (hm hh)
    have hr' : r ∈ usableClosureReactions L A :=
      Finset.mem_filter.mpr ⟨hr,hm hl,hm hh,hp⟩
    exact temporaryReactionClosure_ligation _ r hr' hl hh
  · intro r hr hp
    have hh := temporaryReactionClosure_cleavage A r hr (hm hp)
    have hr' : r ∈ usableClosureReactions L A :=
      Finset.mem_filter.mpr ⟨hr,hh.1,hh.2,hm hp⟩
    exact temporaryReactionClosure_cleavage _ r hr' hp

theorem usableClosureReactions_nonempty {N L : ℕ} (A : Finset (Reaction N))
    (hx : ∃ x ∈ temporaryReactionClosure L A, L < molLength x) :
    (usableClosureReactions L A).Nonempty := by
  obtain ⟨x,hx,hxl⟩ := hx
  rw [← usableClosureReactions_closure A] at hx
  by_contra he
  have hempty : usableClosureReactions L A = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
  have hh : molLength x ≤ L := by
    apply temporaryReactionClosure_induction (usableClosureReactions L A)
      (fun y => molLength y ≤ L) (fun _ h => h) ?_ ?_ x hx
    · intro r hr
      simp [hempty] at hr
    · intro r hr
      simp [hempty] at hr
  omega

/-- Internally catalyzed active reactions yield a literal RAF after removal of
unavailable reactions, provided their closure contains a nonfood molecule. -/
theorem usableClosureReactions_isRAF {N L : ℕ} (A : Finset (Reaction N))
    (Cat : Catalysis (Molecule N) (Reaction N))
    (hcat : ∀ r ∈ A, ∃ x ∈ temporaryReactionClosure L A, Cat x r)
    (hx : ∃ x ∈ temporaryReactionClosure L A, L < molLength x) :
    IsRevRAF (binaryPolymerCRS N L) Cat (usableClosureReactions L A) := by
  refine ⟨usableClosureReactions_nonempty A hx, ?_, ?_⟩
  · intro r hr
    have hh := (Finset.mem_filter.mp hr).2
    have he := usableClosureReactions_closure (L := L) A
    have hl : reactionLeft r ∈ temporaryReactionClosure L (usableClosureReactions L A) := by
      rw [he]; exact hh.1
    have hr' : reactionRight r ∈ temporaryReactionClosure L (usableClosureReactions L A) := by
      rw [he]; exact hh.2.1
    have hp : reactionProduct r ∈ temporaryReactionClosure L (usableClosureReactions L A) := by
      rw [he]; exact hh.2.2
    obtain ⟨kl,hkl⟩ := (mem_temporaryReactionClosure _ _).mp hl
    obtain ⟨kr,hkr⟩ := (mem_temporaryReactionClosure _ _).mp hr'
    obtain ⟨kp,hkp⟩ := (mem_temporaryReactionClosure _ _).mp hp
    let k := max kl (max kr kp)
    have hlk := revClosureAt_mono_stage _ _ (Nat.le_max_left kl (max kr kp)) hkl
    have hrk := revClosureAt_mono_stage _ _
      ((Nat.le_max_left kr kp).trans (Nat.le_max_right kl (max kr kp))) hkr
    have hpk := revClosureAt_mono_stage _ _
      ((Nat.le_max_right kr kp).trans (Nat.le_max_right kl (max kr kp))) hkp
    refine ⟨k,?_⟩
    intro y hy
    have hmem : y = reactionLeft r ∨ y = reactionRight r ∨ y = reactionProduct r := by
      simpa [binaryPolymerCRS] using hy
    rcases hmem with rfl | rfl | rfl
    · exact hlk
    · exact hrk
    · exact hpk
  · intro r hr
    obtain ⟨x,hx,hxr⟩ := hcat r (Finset.mem_filter.mp hr).1
    rw [← usableClosureReactions_closure A] at hx
    obtain ⟨k,hk⟩ := (mem_temporaryReactionClosure _ _).mp hx
    exact ⟨x,k,hk,hxr⟩

end

section
open Classical Filter MeasureTheory RAF RAF.Polymer RAF.Concrete
open scoped ENNReal

/-- Reindex actual food molecules into the finite cutoff universe. This is the
same bounded-word injection used in the repository's reversible trace counts. -/
theorem binaryFood_card_le_cutoff (n L : ℕ) :
    (binaryFood n L).card ≤ Fintype.card (Molecule L) := by
  let f : ↥(binaryFood n L) → Molecule L := fun x =>
    ⟨⟨x.val.1.val, by
      have h := (Finset.mem_filter.mp x.property).2
      dsimp [molLength] at h
      omega⟩, x.val.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨ai,aw⟩,ha⟩ ⟨⟨bi,bw⟩,hb⟩ h
    apply Subtype.ext
    have hi : ai = bi := Fin.ext (congrArg (fun z : Molecule L => z.1.val) h)
    subst bi
    congr
    apply Fin.ext
    exact congrArg (fun z : Molecule L => z.2.val) h
  simpa using Fintype.card_le_of_injective f hf

theorem source_terminal_hasRAF {n : ℕ} (ω : AmbientCoord n → Prop)
    (hmass : 6 < (temporaryReactionClosure 2 (peelingActiveAt (catalystActive ω)
      (temporaryReactionClosure 2) (Fintype.card (Reaction n)))).card) :
    ∃ S : Finset (Reaction n), IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S := by
    let A := peelingActiveAt (catalystActive ω) (temporaryReactionClosure 2) (Fintype.card (Reaction n))
    have hm : Monotone (@temporaryReactionClosure n 2) := fun _ _ h => temporaryReactionClosure_mono h
    have hstable : catalystActive ω (temporaryReactionClosure 2 A) = A :=
      peelingActiveAt_stable_card (catalystActive ω) (temporaryReactionClosure 2)
        (catalystActive_mono ω) hm
    have hcat : ∀ r ∈ A, ∃ x ∈ temporaryReactionClosure 2 A, ω (x,r) := by
      intro r hr
      apply (mem_catalystActive ω _ r).mp
      rwa [hstable]
    have hx : ∃ x ∈ temporaryReactionClosure 2 A, 2 < molLength x := by
      by_contra h
      have hs : temporaryReactionClosure 2 A ⊆ binaryFood n 2 := by
        intro x hx
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        by_contra hlen
        exact h ⟨x,hx,Nat.lt_of_not_ge hlen⟩
      have hb : (binaryFood n 2).card ≤ 6 := by
        simpa [show Fintype.card (Molecule 2) = 6 from by decide] using binaryFood_card_le_cutoff n 2
      have hh := (Finset.card_le_card hs).trans hb
      exact (Nat.not_lt_of_ge hh) hmass
    exact ⟨usableClosureReactions 2 A, usableClosureReactions_isRAF A (fun x r => ω (x,r)) hcat hx⟩

end

section
open Classical RAF RAF.Polymer RAF.Concrete

/-- A RAF in a bounded ambient closure has a bounded catalyst for a seed
reaction. This is deterministic and uses no conditional independence. -/
theorem bounded_raf_has_seed_catalyst {n K : ℕ} (ω : AmbientCoord n → Prop)
    (hbounded : ∀ x ∈ temporaryReactionClosure 2 (catalystActive ω Finset.univ),
      molLength x ≤ K)
    (hraf : ∃ S : Finset (Reaction n),
      IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S) :
    ∃ x : Molecule n, ∃ r : Reaction n,
      molLength x ≤ K ∧ RevSeedReaction (binaryPolymerCRS n 2) r ∧ ω (x,r) := by
  obtain ⟨S, hne, hfg, hcat⟩ := hraf
  have hsub : S ⊆ catalystActive ω Finset.univ := by
    intro r hr
    obtain ⟨x, _, _, hx⟩ := hcat r hr
    exact (mem_catalystActive ω Finset.univ r).mpr ⟨x, Finset.mem_univ _, hx⟩
  obtain ⟨r, hr, hseed⟩ := exists_rev_seed_of_foodGenerated _ S hne hfg
  obtain ⟨x, k, hx, hxr⟩ := hcat r hr
  have hxS : x ∈ temporaryReactionClosure 2 S :=
    (mem_temporaryReactionClosure S x).mpr ⟨k, hx⟩
  exact ⟨x, r, hbounded x (temporaryReactionClosure_mono hsub hxS), hseed, hxr⟩

end

section
open Classical MeasureTheory RAF RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

theorem ambient_coordinate_probability (n : ℕ) (lambda : ℝ) (z : AmbientCoord n) :
    ambientPiMeasure n lambda {ω | ω z} = (toNNReal (catalysisP n lambda) : ENNReal) := by
  have hm := Measure.infinitePi_map_eval (fun _ : AmbientCoord n =>
    ambientCoordLaw (catalysisP n lambda)) z
  have he := congrArg (fun μ : Measure Prop => μ {True}) hm
  rw [Measure.map_apply (measurable_pi_apply z) (MeasurableSet.singleton True)] at he
  simpa [ambientPiMeasure, ambientCoordLaw] using he

def boundedSeedCatalystEvent (n K : ℕ) : Set (AmbientCoord n → Prop) :=
  {ω | ∃ x : Molecule n, ∃ r : Reaction n,
    molLength x ≤ K ∧ RevSeedReaction (binaryPolymerCRS n 2) r ∧ ω (x,r)}

end

section
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval

/-- Any injectively selected ambient coordinates have the literal set-Bernoulli law. -/
theorem ambient_subfield_set_map {n : ℕ} (lambda : ℝ) {J : Type*} [Fintype J]
    (f : J → AmbientCoord n) (hf : Function.Injective f) :
    (ambientPiMeasure n lambda).map (fun ω => {j | ω (f j)}) =
      setBernoulli (Set.univ : Set J) (catalysisP n lambda) := by
            have hi := (ambientCoordinate_iIndep n lambda).precomp hf
            have heval (j : J) : (ambientPiMeasure n lambda).map (fun ω => ω (f j)) =
                ambientCoordLaw (catalysisP n lambda) := by
              rw [ambientPiMeasure, Measure.infinitePi_map_eval]
            have hfield : (ambientPiMeasure n lambda).map (fun ω j => ω (f j)) =
                Measure.infinitePi fun _ : J => ambientCoordLaw (catalysisP n lambda) := by
              rw [hi.map_fun_eq_pi_map fun j => (measurable_pi_apply (f j)).aemeasurable]
              simp_rw [heval]
              exact (Measure.infinitePi_eq_pi _).symm
            calc
              _ = ((ambientPiMeasure n lambda).map fun ω j => ω (f j)).map
                  fun v : J → Prop => {j | v j} := by
                rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
                rfl
              _ = _ := by
                rw [hfield, setBernoulli_eq_map]
                simp [Set.mem_univ, ambientCoordLaw, bernoulliMeasure_def]
def ambientPartition {n : ℕ} (ω : AmbientCoord n → Prop) : CatalysisSample n :=
  ({z | ω (z.1,z.2.val)}, {z | ω (z.1,z.2.val)})

theorem ambientPartition_indep (n : ℕ) (lambda : ℝ) :
    IndepFun (fun ω : AmbientCoord n → Prop => (ambientPartition ω).1)
      (fun ω => (ambientPartition ω).2) (ambientPiMeasure n lambda) := by
        let B : Finset (AmbientCoord n) := Finset.univ.filter
          fun z => RevSeedReaction (binaryPolymerCRS n 2) z.2
        let D : Finset (AmbientCoord n) := Finset.univ.filter
          fun z => ¬ RevSeedReaction (binaryPolymerCRS n 2) z.2
        have hd : Disjoint B D := by
          apply Finset.disjoint_left.mpr
          intro z hb hd
          exact (Finset.mem_filter.mp hd).2 (Finset.mem_filter.mp hb).2
        have hi := (ambientCoordinate_iIndep n lambda).indepFun_finset B D hd
          fun z => measurable_pi_apply z
        let f : (B → Prop) → Set (SeedCoord n) := fun v => {z |
          v ⟨(z.1,z.2.val), Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.2.property⟩⟩}
        let g : (D → Prop) → Set (NonseedCoord n) := fun v => {z |
          v ⟨(z.1,z.2.val), Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.2.property⟩⟩}
        exact hi.comp (measurable_of_finite f) (measurable_of_finite g)
/-- The unpartitioned iid presentation is exactly the canonical seed/nonseed
sample measure. It has the same catalysis parameter and literal reaction IDs. -/
theorem ambientPartition_map (n : ℕ) (lambda : ℝ) :
    (ambientPiMeasure n lambda).map ambientPartition = uniformCatalysisMeasure n lambda := by
  have hs : (ambientPiMeasure n lambda).map (fun ω => (ambientPartition ω).1) =
      setBernoulli (Set.univ : Set (SeedCoord n)) (catalysisP n lambda) := by
    apply ambient_subfield_set_map lambda
    intro x y h
    exact Prod.ext (congrArg (fun z : AmbientCoord n => z.1) h)
      (Subtype.ext (congrArg (fun z : AmbientCoord n => z.2) h))
  have hn : (ambientPiMeasure n lambda).map (fun ω => (ambientPartition ω).2) =
      setBernoulli (Set.univ : Set (NonseedCoord n)) (catalysisP n lambda) := by
    apply ambient_subfield_set_map lambda
    intro x y h
    exact Prod.ext (congrArg (fun z : AmbientCoord n => z.1) h)
      (Subtype.ext (congrArg (fun z : AmbientCoord n => z.2) h))
  have hi := (ambientPartition_indep n lambda).map_prod_eq_prod_map_map
    (measurable_of_finite _).aemeasurable (measurable_of_finite _).aemeasurable
  rw [hs,hn] at hi
  exact hi

@[simp] theorem catalysisOf_ambientPartition {n : ℕ} (ω : AmbientCoord n → Prop)
    (x : Molecule n) (r : Reaction n) : catalysisOf (ambientPartition ω) x r ↔ ω (x,r) := by
  by_cases h : RevSeedReaction (binaryPolymerCRS n 2) r <;>
    simp [catalysisOf, ambientPartition, h]

end

section
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped Topology

def nearFullPoolSize (n m : ℕ) : ℕ := (m-1)*(Fintype.card (Molecule n)/m)

theorem nearFullPoolSize_le (n m : ℕ) : nearFullPoolSize n m ≤ Fintype.card (Molecule n) := by
  have h1 := Nat.mul_le_mul_right (Fintype.card (Molecule n)/m) (Nat.sub_le m 1)
  have h2 := Nat.div_mul_le_self (Fintype.card (Molecule n)) m
  dsimp [nearFullPoolSize]
  nlinarith

end

section
open Classical Filter MeasureTheory RAF RAF.Polymer RAF.Concrete
open scoped ENNReal

theorem canonical_raf_measure_eq_ambient (n : ℕ) (lambda : ℝ) :
    uniformCatalysisMeasure n lambda (HasRAFEvent n) =
      ambientPiMeasure n lambda {ω | ∃ S : Finset (Reaction n),
        IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S} := by
      rw [← ambientPartition_map n lambda, Measure.map_apply (measurable_of_finite _)
        (measurableSet_hasRAFEvent n)]
      have hc (ω : AmbientCoord n → Prop) : catalysisOf (ambientPartition ω) =
          fun x r => ω (x,r) := by
        funext x r
        exact propext (catalysisOf_ambientPartition ω x r)
      simp [Set.preimage, HasRAFEvent, Set.mem_ofPred_eq, hc]
end

section
open Classical

theorem finiteReversibleGenerated_length_le {N L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : FiniteReversibleGenerated N L field w) : w.length ≤ N := by
      induction h with
      | food _ _ hN => exact hN
      | ligate _ _ _ hN _ _ => exact hN
      | left _ _ _ _ ih => simp [List.length_append] at ih; omega
      | right _ _ _ _ ih => simp [List.length_append] at ih; omega
end

section
open Classical RAF.Polymer RAF.Concrete

def splitPrefixCoordinates (M : ℕ) : Finset (List Bool × ℕ) :=
  (shortBinaryWords M).product (Finset.range (M+1))

@[simp] theorem mem_splitPrefixCoordinates (M : ℕ) (z : List Bool × ℕ) :
    z ∈ splitPrefixCoordinates M ↔ z.1.length ≤ M ∧ z.2 ≤ M := by
  simp [splitPrefixCoordinates,mem_shortBinaryWords]

end

section
open Classical MeasureTheory

def reversibleRecordEvent (L M : ℕ) : Set InfiniteSplitEnvironment :=
  {field | ∃ w, w.length = M ∧ FiniteReversibleGenerated M L field w}

def firstRecordEvent (L B M : ℕ) : Set InfiniteSplitEnvironment :=
  {field | B < M ∧ field ∈ reversibleRecordEvent L M ∧
    ∀ k, B < k → k < M → field ∉ reversibleRecordEvent L k}

theorem firstRecordEvent_disjoint (L B : ℕ) {M N : ℕ} (hMN : M ≠ N) :
    Disjoint (firstRecordEvent L B M) (firstRecordEvent L B N) := by
  apply Set.disjoint_left.mpr
  intro field hM hN
  rcases lt_or_gt_of_ne hMN with hlt | hgt
  · exact hN.2.2 M hM.1 hlt hM.2.1
  · exact hM.2.2 N hN.1 hgt hN.2.1

/-- Agreement on a finite rectangular prefix suffices. Including unused
split indices is harmless and leaves every later product layer unexposed. -/
theorem finiteReversibleGenerated_transfer_prefix {N M L : ℕ} (hNM : N ≤ M)
    {field other : InfiniteSplitEnvironment}
    (he : ∀ w : List Bool, w.length ≤ M → ∀ k : ℕ, k ≤ M → field w k = other w k)
    {w : List Bool} (h : FiniteReversibleGenerated N L field w) :
    FiniteReversibleGenerated N L other w := by
        induction h with
        | food hn hL hN => exact .food hn hL hN
        | @ligate u v _ _ ho hN ihu ihv =>
          apply FiniteReversibleGenerated.ligate ihu ihv _ hN
          have hk : u.length ≤ M := by simp only [List.length_append] at hN; omega
          exact (he (u++v) (hN.trans hNM) u.length hk) ▸ ho
        | @left u v hu hv hp ho ih =>
          apply FiniteReversibleGenerated.left hu hv ih
          have hlen := finiteReversibleGenerated_length_le hp
          have hk : u.length ≤ M := by simp [List.length_append] at hlen; omega
          exact (he (u++v) (hlen.trans hNM) u.length hk) ▸ ho
        | @right u v hu hv hp ho ih =>
          apply FiniteReversibleGenerated.right hu hv ih
          have hlen := finiteReversibleGenerated_length_le hp
          exact (he (u++v) (hlen.trans hNM) u.length (by simp [List.length_append] at hlen; omega)) ▸ ho
theorem reversibleRecordEvent_congr_prefix {L N M : ℕ} (hNM : N ≤ M)
    {field other : InfiniteSplitEnvironment}
    (he : ∀ w : List Bool, w.length ≤ M → ∀ k : ℕ, k ≤ M → field w k = other w k) :
    field ∈ reversibleRecordEvent L N ↔ other ∈ reversibleRecordEvent L N := by
  constructor
  · rintro ⟨w,hw,hg⟩
    exact ⟨w,hw,finiteReversibleGenerated_transfer_prefix hNM he hg⟩
  · rintro ⟨w,hw,hg⟩
    exact ⟨w,hw,finiteReversibleGenerated_transfer_prefix hNM
      (fun w hw k hk => (he w hw k hk).symm) hg⟩

theorem firstRecordEvent_congr_prefix {L B M : ℕ}
    {field other : InfiniteSplitEnvironment}
    (he : ∀ w : List Bool, w.length ≤ M → ∀ k : ℕ, k ≤ M → field w k = other w k) :
    field ∈ firstRecordEvent L B M ↔ other ∈ firstRecordEvent L B M := by
  have hr (N : ℕ) (hN : N ≤ M) := reversibleRecordEvent_congr_prefix (L := L) hN he
  constructor
  · rintro ⟨hB,hM,hprev⟩
    refine ⟨hB,(hr M le_rfl).mp hM,?_⟩
    intro k hBk hk hrec
    exact hprev k hBk hk ((hr k hk.le).mpr hrec)
  · rintro ⟨hB,hM,hprev⟩
    refine ⟨hB,(hr M le_rfl).mpr hM,?_⟩
    intro k hBk hk hrec
    exact hprev k hBk hk ((hr k hk.le).mp hrec)

end

section
open Classical MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

abbrev SplitField := (List Bool × ℕ) → Prop

def SplitPrefixDetermined (P : Finset (List Bool × ℕ)) (E : Set SplitField) : Prop :=
  ∀ ω η, (∀ z ∈ P, ω z = η z) → (ω ∈ E ↔ η ∈ E)

theorem split_coordinate_measure (a : I) (z : List Bool × ℕ) :
    infiniteSplitPi a {ω | ω z} = (toNNReal a : ENNReal) := by
  have he := congrArg (fun μ : Measure Prop => μ {True})
    (Measure.infinitePi_map_eval (fun _ : List Bool × ℕ => ambientCoordLaw a) z)
  rw [Measure.map_apply (measurable_pi_apply z) (MeasurableSet.singleton True)] at he
  simpa [infiniteSplitPi,ambientCoordLaw] using he

theorem split_support_open_measure (a : I) (T : Finset (List Bool × ℕ)) :
    infiniteSplitPi a {ω | ∀ z ∈ T, ω z} = (toNNReal a : ENNReal)^T.card := by
      have hi : iIndepFun (fun z (ω : SplitField) => ω z) (infiniteSplitPi a) :=
        iIndepFun_infinitePi fun _ => measurable_id
      have hp := hi.measure_inter_preimage_eq_mul T
        (sets := fun _ => ({True} : Set Prop)) fun _ _ => MeasurableSet.singleton True
      have he : {ω : SplitField | ∀ z ∈ T, ω z} =
          ⋂ z ∈ T, (fun ω : SplitField => ω z) ⁻¹' {True} := by ext ω; simp
      rw [he,hp]
      have hs (z : List Bool × ℕ) :
          infiniteSplitPi a ((fun ω : SplitField => ω z) ⁻¹' {True}) = (toNNReal a : ENNReal) := by
        simpa using split_coordinate_measure a z
      simp only [hs,Finset.prod_const]
theorem split_prefix_event_representation (P : Finset (List Bool × ℕ)) (E : Set SplitField)
    (hE : SplitPrefixDetermined P E) :
    ∃ e : (P → Prop) → Prop, E = {ω | e (fun z => ω z.val)} := by
  let extend : (P → Prop) → SplitField := fun η z => if h : z ∈ P then η ⟨z,h⟩ else False
  refine ⟨fun η => extend η ∈ E, ?_⟩
  ext ω
  apply hE
  intro z hz
  simp [extend,hz]

theorem split_prefix_failure_measure (a : I) (P T : Finset (List Bool × ℕ))
    (hPT : Disjoint P T) (E : Set SplitField) (hE : SplitPrefixDetermined P E) :
    infiniteSplitPi a (E ∩ {ω | ¬ ∀ z ∈ T, ω z}) =
      infiniteSplitPi a E * (1-(toNNReal a : ENNReal)^T.card) := by
          obtain ⟨e,he⟩ := split_prefix_event_representation P E hE
          have hi : iIndepFun (fun z (ω : SplitField) => ω z) (infiniteSplitPi a) :=
            iIndepFun_infinitePi fun _ => measurable_id
          have ht := hi.indepFun_finset P T hPT fun z => measurable_pi_apply z
          let g : (T → Prop) → Prop := fun η => ¬ ∀ z, η z
          have hind := ht.comp (measurable_of_finite e) (measurable_of_finite g)
          have hp := hind.measure_inter_preimage_eq_mul {True} {True}
            (MeasurableSet.singleton True) (MeasurableSet.singleton True)
          have hfail : infiniteSplitPi a {ω | ¬ ∀ z ∈ T, ω z} =
              1-(toNNReal a : ENNReal)^T.card := by
            have hm : MeasurableSet {ω : SplitField | ∀ z ∈ T, ω z} := by
              have hs : {ω : SplitField | ∀ z ∈ T, ω z} =
                  ⋂ z ∈ T, (fun ω : SplitField => ω z) ⁻¹' {True} := by ext ω; simp
              rw [hs]
              exact MeasurableSet.iInter fun z => MeasurableSet.iInter
                fun _ => (MeasurableSet.singleton True).preimage (measurable_pi_apply z)
            change infiniteSplitPi a ({ω | ∀ z ∈ T, ω z}ᶜ) = _
            rw [measure_compl hm (measure_ne_top _ _),measure_univ,split_support_open_measure]
          rw [he] at ⊢
          simp only [Function.comp_def,g,Subtype.forall,Set.preimage,
            Set.mem_singleton_iff,eq_iff_iff,iff_true] at hp
          rw [hfail] at hp
          exact hp
end

section
open Classical

abbrev RecordPrefixIndex := Σ M : ℕ, (splitPrefixCoordinates M → Prop)

def recordPrefixAtom (B : ℕ) (i : RecordPrefixIndex) : Set SplitField :=
  {ω | currySplitField ω ∈ firstRecordEvent 2 B i.1 ∧
    ∀ z : splitPrefixCoordinates i.1, ω z.val = i.2 z}

theorem recordPrefixAtom_determined (B : ℕ) (i : RecordPrefixIndex) :
    SplitPrefixDetermined (splitPrefixCoordinates i.1) (recordPrefixAtom B i) := by
  intro ω η he
  have hrec : currySplitField ω ∈ firstRecordEvent 2 B i.1 ↔
      currySplitField η ∈ firstRecordEvent 2 B i.1 := by
    apply firstRecordEvent_congr_prefix
    intro w hw k hk
    exact he (w,k) ((mem_splitPrefixCoordinates _ _).mpr ⟨hw,hk⟩)
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr hrec
  apply forall_congr'
  intro z
  rw [he z.val z.property]

theorem recordPrefixAtoms_disjoint (B : ℕ) {i j : RecordPrefixIndex} (hij : i ≠ j) :
    Disjoint (recordPrefixAtom B i) (recordPrefixAtom B j) := by
  apply Set.disjoint_left.mpr
  intro ω hi hj
  by_cases hM : i.1 = j.1
  · have he : i = j := by
      rcases i with ⟨M,η⟩
      rcases j with ⟨N,ξ⟩
      dsimp at hM
      subst N
      congr
      funext z
      exact (hi.2 z).symm.trans (hj.2 z)
    exact hij he
  · exact Set.disjoint_left.mp (firstRecordEvent_disjoint 2 B hM) hi.1 hj.1

/-- Each nonempty atom fixes a usable word, chosen pointwise from one
representative. No random measurable word selector is required. -/
theorem recordPrefixAtom_word (B : ℕ) (i : RecordPrefixIndex)
    (hne : (recordPrefixAtom B i).Nonempty) :
    ∃ w : List Bool, w.length = i.1 ∧ B < w.length ∧
      ∀ ω ∈ recordPrefixAtom B i,
        FiniteReversibleGenerated w.length 2 (currySplitField ω) w := by
  obtain ⟨η,hη⟩ := hne
  obtain ⟨w,hw,hg⟩ := hη.1.2.1
  refine ⟨w,hw,by rw [hw]; exact hη.1.1,?_⟩
  intro ω hω
  rw [hw]
  apply finiteReversibleGenerated_transfer_prefix (M := i.1) le_rfl ?_ hg
  intro v hv k hk
  let z : splitPrefixCoordinates i.1 := ⟨(v,k),(mem_splitPrefixCoordinates _ _).mpr ⟨hv,hk⟩⟩
  exact (hη.2 z).trans (hω.2 z).symm

end

section
open Classical MeasureTheory unitInterval
open scoped ENNReal

theorem measurableSet_of_splitPrefixDetermined (P : Finset (List Bool × ℕ))
    (E : Set SplitField) (hE : SplitPrefixDetermined P E) : MeasurableSet E := by
        obtain ⟨e,he⟩ := split_prefix_event_representation P E hE
        rw [he]
        have hm : Measurable fun ω : SplitField => e fun z : P => ω z.val :=
          (measurable_of_finite e).comp (Measurable.of_eval fun z => measurable_pi_apply z.val)
        simpa using (MeasurableSet.singleton True).preimage hm
end

section
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval

theorem exists_sprinkling_increment {a c : I} (hac : a ≤ c) :
    ∃ b : I, sprinklingParameter a b = c := by
  by_cases he : a = c
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    rw [sprinklingParameter_value]
    simp [he]
  · have hltI : a < c := lt_of_le_of_ne hac he
    have hlt : (a : ℝ) < c := hltI
    have hd : 0 < 1-(a : ℝ) := by have hc := c.property.2; linarith
    let b : I := ⟨((c : ℝ)-a)/(1-(a : ℝ)), by
      constructor
      · positivity
      · apply (div_le_one hd).mpr
        have hc := c.property.2
        linarith⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    rw [sprinklingParameter_value]
    dsimp [b]
    field_simp
    nlinarith

theorem static_increasing_event_sprinkling (N : ℕ) (a b : I)
    (P : Finset (Reaction N) → Prop) (hP : Monotone P) :
    staticReactionMeasure N a {ω | P (staticOpenReactions ω)} ≤
      staticReactionMeasure N (sprinklingParameter a b) {ω | P (staticOpenReactions ω)} := by
    have he : staticReactionMeasure N a {ω | P (staticOpenReactions ω)} =
        ((staticReactionMeasure N a).prod (staticReactionMeasure N b))
          {p | P (staticOpenReactions p.1)} := by
      have hs : {p : (Reaction N → Prop) × (Reaction N → Prop) | P (staticOpenReactions p.1)} =
          {ω | P (staticOpenReactions ω)} ×ˢ Set.univ := by ext p; simp
      rw [hs, Measure.prod_prod, measure_univ, mul_one]
    rw [he]
    have hu := iid_union_field_map (Reaction N) a b
    change _ = _ at hu
    rw [show staticReactionMeasure N (sprinklingParameter a b) = _ from hu.symm,
      Measure.map_apply (measurable_of_finite _) (Set.Finite.measurableSet (Set.toFinite _))]
    apply measure_mono
    intro p hp
    apply hP _ hp
    intro r hr
    simp [staticOpenReactions, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact Or.inl hr
theorem static_increasing_event_mono (N : ℕ) {a c : I} (hac : a ≤ c)
    (P : Finset (Reaction N) → Prop) (hP : Monotone P) :
    staticReactionMeasure N a {ω | P (staticOpenReactions ω)} ≤
      staticReactionMeasure N c {ω | P (staticOpenReactions ω)} := by
  obtain ⟨b, rfl⟩ := exists_sprinkling_increment hac
  exact static_increasing_event_sprinkling N a b P hP

/-- Any static pool barrier above food cardinality gives the actual canonical
RAF event, using a deterministic terminal horizon. -/
theorem canonical_raf_ge_static_barrier (n : ℕ) (lambda : ℝ) (k : ℕ) (hk : 6 < k) :
    staticReactionMeasure n (fixedPoolParameter (catalysisP n lambda)
      (finiteInitialSegment (Molecule n) k).card)
      {ω | k ≤ (temporaryReactionClosure 2 (staticOpenReactions ω)).card} ≤
        uniformCatalysisMeasure n lambda (HasRAFEvent n) := by
  rw [canonical_raf_measure_eq_ambient]
  apply (source_mass_ge_iid_static lambda (temporaryReactionClosure 2)
    (fun _ _ h => temporaryReactionClosure_mono h) k (Fintype.card (Reaction n))).trans
  apply measure_mono
  intro ω hω
  exact source_terminal_hasRAF ω (hk.trans_le hω)

/-- Finite quantitative consumer for near-full static mass, with every
parameter comparison and nonfood threshold explicit. -/
theorem canonical_raf_ge_near_full_static (n m : ℕ) (lambda : ℝ) (hm : 0 < m)
    (q : I) (hk : 6 < (m-1)*(Fintype.card (Molecule n)/m))
    (hq : q ≤ fixedPoolParameter (catalysisP n lambda)
      (finiteInitialSegment (Molecule n) ((m-1)*(Fintype.card (Molecule n)/m))).card) :
    staticReactionMeasure n q {ω | (m-1)*Fintype.card (Molecule n) ≤
      m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} ≤
        uniformCatalysisMeasure n lambda (HasRAFEvent n) := by
      let k := (m-1)*(Fintype.card (Molecule n)/m)
      have hmass : staticReactionMeasure n q {ω | (m-1)*Fintype.card (Molecule n) ≤
          m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} ≤
          staticReactionMeasure n q {ω | k ≤ (temporaryReactionClosure 2 (staticOpenReactions ω)).card} := by
        apply measure_mono
        intro ω hω
        change (m-1)*Fintype.card (Molecule n) ≤
          m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card at hω
        have hdiv := Nat.div_mul_le_self (Fintype.card (Molecule n)) m
        dsimp [k]
        nlinarith
      have hmono := static_increasing_event_mono n hq
        (fun S => k ≤ (temporaryReactionClosure 2 S).card)
        fun S T hST hS => hS.trans (Finset.card_le_card (temporaryReactionClosure_mono hST))
      exact hmass.trans (hmono.trans (canonical_raf_ge_static_barrier n lambda k hk))
end

section
open Classical MeasureTheory RAF.Polymer unitInterval

theorem static_decreasing_event_mono (N : ℕ) {a c : I} (hac : a ≤ c)
    (P : Finset (Reaction N) → Prop) (hP : Antitone P) :
    staticReactionMeasure N c {ω | P (staticOpenReactions ω)} ≤
      staticReactionMeasure N a {ω | P (staticOpenReactions ω)} := by
    obtain ⟨b,rfl⟩ := exists_sprinkling_increment hac
    have hu := iid_union_field_map (Reaction N) a b
    change _ = _ at hu
    rw [show staticReactionMeasure N (sprinklingParameter a b) = _ from hu.symm,
      Measure.map_apply (measurable_of_finite _) (Set.Finite.measurableSet (Set.toFinite _))]
    have hs : {p : (Reaction N → Prop) × (Reaction N → Prop) |
        P (staticOpenReactions fun r => p.1 r ∨ p.2 r)} ⊆
        {ω | P (staticOpenReactions ω)} ×ˢ Set.univ := by
      intro p hp
      refine ⟨hP ?_ hp,Set.mem_univ _⟩
      intro r hr
      simp only [staticOpenReactions,Finset.mem_filter,Finset.mem_univ,true_and] at hr ⊢
      exact Or.inl hr
    exact (measure_mono hs).trans_eq (by rw [Measure.prod_prod,measure_univ,mul_one]; rfl)
end

section
open Classical MeasureTheory RAF.Polymer unitInterval
open scoped ENNReal

noncomputable def staticAtomWeight (a : I) (P : Prop) : NNReal :=
  if P then toNNReal a else toNNReal (σ a)

theorem ambientCoordLaw_atom (a : I) (P : Prop) :
    ambientCoordLaw a {P} = (staticAtomWeight a P : ENNReal) := by
  by_cases hp : P
  · have he : P = True := propext (iff_true_intro hp)
    simp [he, ambientCoordLaw, staticAtomWeight]
  · have he : P = False := propext (iff_false_intro hp)
    simp [he, ambientCoordLaw, staticAtomWeight]

end

section
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped ENNReal

/-- Seed and supplied-seed bulk are evaluated in the same field. Their
dependence is harmless: seed probability is bounded by success plus bulk error. -/
theorem same_field_seed_mass_bound (N L m : ℕ) (a : I) :
    staticReactionMeasure N a {ω | ∀ w ∈ actualBinaryWords L,
      ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), moleculeWord x = w} ≤
    staticReactionMeasure N a {ω | (m-1)*Fintype.card (Molecule N) ≤
      m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} +
    staticReactionMeasure N a {ω | m*(temporaryReactionClosure L (staticOpenReactions ω)).card <
      (m-1)*Fintype.card (Molecule N)} := by
  have hsub : {ω : Reaction N → Prop | ∀ w ∈ actualBinaryWords L,
      ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), moleculeWord x = w} ⊆
      {ω | (m-1)*Fintype.card (Molecule N) ≤ m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} ∪
      {ω | m*(temporaryReactionClosure L (staticOpenReactions ω)).card < (m-1)*Fintype.card (Molecule N)} := by
    intro ω hseed
    by_cases hb : m*(temporaryReactionClosure L (staticOpenReactions ω)).card <
        (m-1)*Fintype.card (Molecule N)
    · exact Or.inr hb
    · left
      have hcontain : temporaryReactionClosure L (staticOpenReactions ω) ⊆
          temporaryReactionClosure 2 (staticOpenReactions ω) := by
        apply temporaryReactionClosure_seed_transfer Finset.Subset.rfl
        intro x hx
        have hw : moleculeWord x ∈ actualBinaryWords L :=
          (mem_actualBinaryWords _ _).mpr ⟨moleculeWord_nonempty x, by rwa [moleculeWord_length]⟩
        obtain ⟨y, hy, he⟩ := hseed _ hw
        exact moleculeWord_injective he ▸ hy
      exact (Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card hcontain))
  exact (measure_mono hsub).trans (measure_union_le _ _)

end

section
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal Topology

theorem staticSurvival_le_finite_escape (a : I) (K : ℕ) :
    staticSurvival a ≤ staticReactionMeasure (2*(K+2)) a (staticEscapeEvent 2 K) := by
  rw [finite_static_escape_measure_eq]
  apply measure_mono
  intro field hf
  exact (reversibleEscapeEvent_iff 2 K field).mpr (hf (K+2))

end

end HordijkSteelThreshold
