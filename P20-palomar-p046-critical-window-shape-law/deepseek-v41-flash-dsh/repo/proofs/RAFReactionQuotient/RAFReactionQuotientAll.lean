module

public import Mathlib
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Topology.Sequences
public import proofs.HordijkSteelThreshold.HordijkSteelThresholdAll
public import proofs.OverlapCorrectedRAF.Source.OverlapCorrectedRAFSourceAll
public import proofs.RAF.Concrete.RAFConcreteAll
public import proofs.RAFEmergenceApprox.RAFEmergenceApproxAll
public import proofs.RAFEmergenceApprox.RAFEmergenceApproxGenericAll

@[expose] public section

namespace RAFReactionQuotient

section
open Classical RAF RAF.Concrete

variable {M R J : Type*} [DecidableEq M] [DecidableEq R] [DecidableEq J]

omit [DecidableEq R] in
/-- Identifying reaction descriptions with identical chemistry preserves every
finite stage of ordinary reversible closure. -/
theorem closureAt_image (Q : ReversibleCRS M R) (P : ReversibleCRS M J)
    (π : R → J) (hl : ∀ r, P.lhs (π r) = Q.lhs r)
    (hr : ∀ r, P.rhs (π r) = Q.rhs r) (hf : P.food = Q.food)
    (S : Finset R) (k : ℕ) :
    revClosureAt P (S.image π) k = revClosureAt Q S k := by
    induction k with
    | zero => exact hf
    | succ k ih =>
      simp [revClosureAt, ih, revClosureStep]
      congr 1
      ext x
      simp [Finset.mem_biUnion, RevEnabledLhs, RevEnabledRhs, hl, hr]
def orCatalysis (π : R → J) (C : Catalysis M R) : Catalysis M J :=
  fun x j => ∃ r, π r = j ∧ C x r

omit [DecidableEq R] in
/-- Projection of a RAF retains its catalytic witnesses. -/
theorem raf_image (Q : ReversibleCRS M R) (P : ReversibleCRS M J)
    (π : R → J) (hl : ∀ r, P.lhs (π r) = Q.lhs r)
    (hr : ∀ r, P.rhs (π r) = Q.rhs r) (hf : P.food = Q.food)
    (C : Catalysis M R) (S : Finset R) (hS : IsRevRAF Q C S) :
    IsRevRAF P (orCatalysis π C) (S.image π) := by
    refine ⟨hS.1.image π, ?_, ?_⟩
    · intro j hj
      obtain ⟨r, hmem, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨k, hk⟩ := hS.2.1 r hmem
      exact ⟨k, by simpa [hl, hr, closureAt_image Q P π hl hr hf] using hk⟩
    · intro j hj
      obtain ⟨r, hmem, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨x, k, hx, hc⟩ := hS.2.2 r hmem
      exact ⟨x, k, by rwa [closureAt_image Q P π hl hr hf], r, rfl, hc⟩
end

section
open Classical RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

abbrev OrderedChannel (n : ℕ) :=
  {uv : Molecule n × Molecule n // molLength uv.1 + molLength uv.2 ≤ n}

def orderedCRS (n t : ℕ) : ReversibleCRS (Molecule n) (OrderedChannel n) where
  lhs r := {r.val.1, r.val.2}
  rhs r := {concatMolecule r.val.1 r.val.2 r.property}
  food := binaryFood n t

theorem precedes_total {n : ℕ} (u v : Molecule n) :
    moleculePrecedes u v ∨ moleculePrecedes v u := by
  unfold moleculePrecedes
  omega

def canonical {n : ℕ} (r : OrderedChannel n) : RepositoryChannel n :=
  if h : displayedConcat r.val.1 r.val.2 ≠ displayedConcat r.val.2 r.val.1 ∨
      moleculePrecedes r.val.1 r.val.2 then
    ⟨r.val, r.property, h⟩
  else
    ⟨(r.val.2, r.val.1), (Nat.add_comm (molLength r.val.2) (molLength r.val.1)).le.trans r.property,
      Or.inr ((precedes_total r.val.1 r.val.2).resolve_left (fun hp => h (Or.inr hp)))⟩

theorem molecule_ext {n : ℕ} {x y : Molecule n}
    (hl : molLength x = molLength y) (hc : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  have hij : i = j := by apply Fin.ext; dsimp [molLength] at hl; omega
  subst j
  exact congrArg (Sigma.mk i) (Fin.ext hc)

theorem concat_code {n : ℕ} (u v : Molecule n)
    (h : molLength u + molLength v ≤ n) :
    (concatMolecule u v h).2.val = displayedConcat u v := by
  simp [concatMolecule, moleculeOfCode, concatCode, displayedConcat,
    finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

theorem concat_comm_of_code {n : ℕ} (u v : Molecule n)
    (h : molLength u + molLength v ≤ n)
    (hc : displayedConcat u v = displayedConcat v u) :
    concatMolecule u v h = concatMolecule v u (by omega) := by
    apply molecule_ext
    · simp [concatMolecule, Nat.add_comm]
    · simpa [concat_code] using hc
theorem canonical_lhs {n t : ℕ} (r : OrderedChannel n) :
    (repositoryCRS n t).lhs (canonical r) = (orderedCRS n t).lhs r := by
  unfold canonical
  split
  · rfl
  · simp [repositoryCRS, orderedCRS, Finset.pair_comm]

theorem canonical_rhs {n t : ℕ} (r : OrderedChannel n) :
    (repositoryCRS n t).rhs (canonical r) = (orderedCRS n t).rhs r := by
    unfold canonical
    split
    · rfl
    · rename_i h
      have hc : displayedConcat r.val.1 r.val.2 = displayedConcat r.val.2 r.val.1 := by
        by_contra hn
        exact h (Or.inl hn)
      simp [repositoryCRS, orderedCRS]
      rw [concat_comm_of_code r.val.1 r.val.2 r.property hc]
theorem canonical_val_cases {n : ℕ} (r : OrderedChannel n) :
    (canonical r).val = r.val ∨ (canonical r).val = r.val.swap := by
  unfold canonical
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem canonical_surjective (n : ℕ) : Function.Surjective (@canonical n) := by
    intro j
    refine ⟨⟨j.val,j.property.1⟩, ?_⟩
    simp [canonical, dite_eq_left j.property.2]
theorem canonical_fibre_le_two {n : ℕ} (j : RepositoryChannel n) :
    (Finset.univ.filter (fun r : OrderedChannel n => canonical r = j)).card ≤ 2 := by
    let a : OrderedChannel n := ⟨j.val,j.property.1⟩
    let b : OrderedChannel n := ⟨j.val.swap, by have := j.property.1; dsimp; omega⟩
    have hs : Finset.univ.filter fun r : OrderedChannel n => canonical r = j ⊆ {a,b} := by
      intro r hr
      have he := (Finset.mem_filter.mp hr).2
      have hv := canonical_val_cases r
      rw [he] at hv
      rcases hv with hv | hv
      · have : r = a := Subtype.ext hv.symm
        simp [this]
      · have : r = b := by
          apply Subtype.ext
          exact (congrArg Prod.swap hv).symm
        simp [this]
    exact (Finset.card_le_card hs).trans (by
      calc
        ({a,b} : Finset (OrderedChannel n)).card ≤ ({b} : Finset (OrderedChannel n)).card + 1 :=
          Finset.card_insert_le _ _
        _ = 2 := by simp)
end

section
open Classical RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

end

section
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

/-- Fixing one nonempty factor and the other factor's length determines the
commuting word uniquely. Binary positional arithmetic avoids primitive roots. -/
theorem commuting_factor_unique {n : ℕ} (u v w : Molecule n)
    (hlen : molLength v = molLength w)
    (hv : displayedConcat u v = displayedConcat v u)
    (hw : displayedConcat u w = displayedConcat w u) : v = w := by
  apply molecule_ext hlen
  have hp : 1 < 2 ^ molLength u := by
    unfold molLength
    rw [pow_succ]
    have hh : 0 < 2 ^ u.1.val := by positivity
    omega
  unfold displayedConcat at hv hw
  rw [hlen] at hv
  nlinarith

theorem commuting_equal_length {n : ℕ} (u v : Molecule n)
    (hlen : molLength u = molLength v)
    (hv : displayedConcat u v = displayedConcat v u) : u = v := by
  exact (commuting_factor_unique u v u hlen.symm hv rfl).symm

theorem noncanonical_strict_lengths {n : ℕ} (r : OrderedChannel n)
    (h : ¬ (displayedConcat r.val.1 r.val.2 ≠ displayedConcat r.val.2 r.val.1 ∨
      moleculePrecedes r.val.1 r.val.2)) : molLength r.val.2 < molLength r.val.1 := by
    have hc : displayedConcat r.val.1 r.val.2 = displayedConcat r.val.2 r.val.1 :=
      Classical.byContradiction fun hn => h (Or.inl hn)
    have hn : ¬ moleculePrecedes r.val.1 r.val.2 := fun hp => h (Or.inr hp)
    have he : molLength r.val.1 ≠ molLength r.val.2 := by
      intro he
      have hv := commuting_equal_length r.val.1 r.val.2 he hc
      apply hn
      rw [hv]
      exact Or.inr ⟨rfl,le_rfl⟩
    unfold moleculePrecedes at hn
    omega
end

section
open Classical MeasureTheory unitInterval HordijkSteelThreshold

/-- Canonicalize a valid split only when the factors commute and the right
factor is shorter. Equal-length commuting factors are identical, so there is
no separate tie to collapse. Invalid coordinates are harmless unused marks. -/
def canonicalIndex (z : List Bool × ℕ) : List Bool × ℕ :=
  if 0 < z.2 ∧ z.2 < z.1.length ∧ z.1.length-z.2 < z.2 ∧
      z.1.take z.2 ++ z.1.drop z.2 = z.1.drop z.2 ++ z.1.take z.2 then
    (z.1,z.1.length-z.2)
  else z

@[simp] theorem canonicalIndex_product (z : List Bool × ℕ) :
    (canonicalIndex z).1 = z.1 := by unfold canonicalIndex; split <;> rfl

theorem canonicalIndex_prefix {B : ℕ} {z : List Bool × ℕ}
    (hz : z ∈ splitPrefixCoordinates B) : canonicalIndex z ∈ splitPrefixCoordinates B := by
  have hz' := (mem_splitPrefixCoordinates B z).mp hz
  apply (mem_splitPrefixCoordinates B _).mpr
  unfold canonicalIndex
  split
  · dsimp
    exact ⟨hz'.1,(Nat.sub_le _ _).trans hz'.1⟩
  · exact hz'

def quotientField (ω : SplitField) : InfiniteSplitEnvironment :=
  fun w k => ω (canonicalIndex (w,k))

theorem quotientField_measurable : Measurable quotientField := by
  apply Measurable.of_eval
  intro w
  apply Measurable.of_eval
  intro k
  exact measurable_pi_apply _

/-- Infinite reversible quotient survival, realized by iid marks on canonical
coordinates. Noncanonical and invalid latent coordinates do not affect it. -/
noncomputable def quotientSurvival (a : I) : ENNReal :=
  infiniteSplitPi a {ω | ReversibleUnbounded 2 (quotientField ω)}

end

section
open Classical RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

def splitToOrdered {n : ℕ} (r : Reaction n) : OrderedChannel n :=
  ⟨(reactionLeft r, reactionRight r), by
    simp only [molLength_reactionLeft, molLength_reactionRight, reaction_length_add]
    exact Nat.succ_le_of_lt r.1.isLt⟩

theorem split_concat {n : ℕ} (r : Reaction n) :
    concatMolecule (reactionLeft r) (reactionRight r) (splitToOrdered r).property =
      reactionProduct r := by
    apply molecule_ext
    · calc
        molLength (concatMolecule (reactionLeft r) (reactionRight r)
            (splitToOrdered r).property) =
            molLength (reactionLeft r) + molLength (reactionRight r) := by
              unfold concatMolecule
              apply molLength_moleculeOfCode
        _ = reactionLeftLength r + reactionRightLength r := by
          rw [molLength_reactionLeft, molLength_reactionRight]
        _ = reactionProductLength r := reaction_length_add r
        _ = molLength (reactionProduct r) := (molLength_reactionProduct r).symm
    · have hc := concat_code (reactionLeft r) (reactionRight r)
        (splitToOrdered r).property
      rw [hc]
      unfold displayedConcat
      rw [molLength_reactionRight]
      change r.2.1.val / 2 ^ reactionRightLength r * 2 ^ reactionRightLength r +
        r.2.1.val % 2 ^ reactionRightLength r = r.2.1.val
      simpa [Nat.mul_comm] using Nat.div_add_mod r.2.1.val (2 ^ reactionRightLength r)
def splitToQuotient {n : ℕ} (r : Reaction n) : RepositoryChannel n :=
  canonical (splitToOrdered r)

theorem splitToQuotient_lhs {n t : ℕ} (r : Reaction n) :
    (repositoryCRS n t).lhs (splitToQuotient r) = (binaryPolymerCRS n t).lhs r :=
  canonical_lhs (splitToOrdered r)

theorem splitToQuotient_rhs {n t : ℕ} (r : Reaction n) :
    (repositoryCRS n t).rhs (splitToQuotient r) = (binaryPolymerCRS n t).rhs r := by
  rw [splitToQuotient, canonical_rhs]
  change {concatMolecule (reactionLeft r) (reactionRight r) _} = {reactionProduct r}
  rw [split_concat]

theorem split_closure_eq_quotient {n : ℕ} (t : ℕ)
    (S : Finset (Reaction n)) (k : ℕ) :
    revClosureAt (repositoryCRS n t) (S.image splitToQuotient) k =
      revClosureAt (binaryPolymerCRS n t) S k :=
  closureAt_image _ _ splitToQuotient splitToQuotient_lhs splitToQuotient_rhs rfl S k

theorem split_raf_image {n : ℕ} (t : ℕ)
    (C : Catalysis (Molecule n) (Reaction n)) :
    (∃ S, IsRevRAF (binaryPolymerCRS n t) C S) →
      ∃ T, IsRevRAF (repositoryCRS n t) (orCatalysis splitToQuotient C) T := by
  rintro ⟨S, hS⟩
  exact ⟨S.image splitToQuotient, raf_image (binaryPolymerCRS n t) (repositoryCRS n t)
    splitToQuotient splitToQuotient_lhs splitToQuotient_rhs rfl C S hS⟩

end

section
open Classical RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

theorem splitToOrdered_injective (n : ℕ) : Function.Injective (@splitToOrdered n) := by
    intro r s he
    have hp : reactionProduct r = reactionProduct s := by
      rw [← split_concat r, ← split_concat s]
      exact congrArg (fun q : OrderedChannel n => concatMolecule q.val.1 q.val.2 q.property) he
    have hl : reactionLeftLength r = reactionLeftLength s := by
      simpa [splitToOrdered, molLength_reactionLeft] using
        congrArg (fun q : OrderedChannel n => molLength q.val.1) he
    rcases r with ⟨ri, rw, rk⟩
    rcases s with ⟨si, sw, sk⟩
    have hi : ri = si := congrArg Sigma.fst hp
    subst si
    have hw : rw = sw := Fin.ext (congrArg (fun x : Molecule n => x.2.val) hp)
    subst sw
    have hk : rk = sk := by
      apply Fin.ext
      dsimp [reactionLeftLength] at hl
      omega
    subst sk
    rfl
theorem split_fibre_le_two {n : ℕ} (j : RepositoryChannel n) :
    (Finset.univ.filter (fun r : Reaction n => splitToQuotient r = j)).card ≤ 2 := by
      let S := Finset.univ.filter fun r : Reaction n => splitToQuotient r = j
      have hs : S.image splitToOrdered ⊆
          Finset.univ.filter fun q : OrderedChannel n => canonical q = j := by
        intro q hq
        obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2⟩
      calc
        S.card = (S.image splitToOrdered).card :=
          (Finset.card_image_of_injective S (splitToOrdered_injective n)).symm
        _ ≤ _ := Finset.card_le_card hs
        _ ≤ 2 := canonical_fibre_le_two j
end

section
open Classical MeasureTheory ProbabilityTheory unitInterval
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold

noncomputable def quotientClosure (n L : ℕ) (S : Finset (RepositoryChannel n)) :
    Finset (Molecule n) := Finset.univ.filter
      (fun x => ∃ k, x ∈ revClosureAt (repositoryCRS n L) S k)

@[simp] theorem mem_quotientClosure {n L : ℕ} (S : Finset (RepositoryChannel n))
    (x : Molecule n) : x ∈ quotientClosure n L S ↔
      ∃ k, x ∈ revClosureAt (repositoryCRS n L) S k := by
  simp [quotientClosure]

theorem quotientClosure_mono (n L : ℕ) : Monotone (quotientClosure n L) := by
  intro S T hST x hx
  obtain ⟨k,hk⟩ := (mem_quotientClosure S x).mp hx
  exact (mem_quotientClosure T x).mpr ⟨k, revClosureAt_mono_reactions _ hST k hk⟩

noncomputable def quotientCatalyticLaw (n : ℕ) (p : I) :=
  RAFEmergenceApprox.Generic.law (X := Molecule n) (fun _ : RepositoryChannel n => p)

/-- Entire adaptive histories, using the actual quotient food closure, have
the same law after replacement by deterministic cardinality prefixes. -/
theorem quotient_history_map (n L : ℕ) (p : I) (T : ℕ) :
    (quotientCatalyticLaw n p).map (fun ω => activeTrace
      (RAFEmergenceApprox.Generic.catalystActive ω) (quotientClosure n L) T) =
    (quotientCatalyticLaw n p).map (fun ω => activeTrace
      (fun C => RAFEmergenceApprox.Generic.catalystActive ω
        (finiteInitialSegment (Molecule n) C.card)) (quotientClosure n L) T) :=
  RAFEmergenceApprox.Generic.activeTrace_map_eq_scalar _ _ (quotientClosure_mono n L) T

end

section
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold

variable {R J : Type*} [Fintype R]

def fieldOR (π : R → J) (ω : R → Prop) (j : J) : Prop :=
  ∃ r, π r = j ∧ ω r

/-- Predicates on disjoint quotient fibres are independent, including a whole
family of other fibres. -/
theorem fibre_event_indep (π : R → J) (p : I) (E : J → Prop → Prop)
    (j : J) (S : Finset J) (hj : j ∉ S) :
    IndepFun (fun ω : R → Prop => E j (fieldOR π ω j))
      (fun ω => ∀ k ∈ S, E k (fieldOR π ω k))
      (RAFEmergenceApprox.Generic.colLaw R p) := by
                    let B := Finset.univ.filter fun r : R => π r = j
                    let D := Finset.univ.filter fun r : R => π r ∈ S
                    have hd : Disjoint B D := by
                      apply Finset.disjoint_left.mpr
                      intro r hr hs
                      exact hj ((Finset.mem_filter.mp hr).2 ▸ (Finset.mem_filter.mp hs).2)
                    have hi := iIndepFun_pi
                      (fun _ : R => (measurable_id : Measurable (id : Prop → Prop)).aemeasurable)
                      (μ := fun _ : R => ambientCoordLaw p)
                    have ht := hi.indepFun_finset B D hd fun _ => measurable_pi_apply _
                    let f : (B → Prop) → Prop := fun v => E j (∃ r : B, v r)
                    let g : (D → Prop) → Prop := fun v => ∀ k ∈ S, E k (∃ r : D, π r.val = k ∧ v r)
                    have he := ht.comp (measurable_of_finite f) (measurable_of_finite g)
                    have hf : (fun ω : R → Prop => f fun r : B => ω r.val) =
                        fun ω => E j (fieldOR π ω j) := by
                      funext ω
                      dsimp [f]
                      congr 1
                      apply propext
                      simp [B, fieldOR]
                    have hg : (fun ω : R → Prop => g fun r : D => ω r.val) =
                        fun ω => ∀ k ∈ S, E k (fieldOR π ω k) := by
                      funext ω
                      apply propext
                      apply forall_congr'
                      intro k
                      apply forall_congr'
                      intro hk
                      have hh : (∃ r : D, π r.val = k ∧ ω r.val) ↔ fieldOR π ω k := by
                        constructor
                        · rintro ⟨r,hr,ho⟩
                          exact ⟨r.val,hr,ho⟩
                        · rintro ⟨r,hr,ho⟩
                          exact ⟨⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr.symm ▸ hk⟩⟩,hr,ho⟩
                      dsimp [g]
                      rw [propext hh]
                    change IndepFun (fun ω : R → Prop => f fun r : B => ω r.val)
                      (fun ω => g fun r : D => ω r.val) _ at he
                    rw [hf,hg] at he
                    exact he
theorem fibre_events_product (π : R → J) (p : I) (E : J → Prop → Prop)
    (S : Finset J) :
    RAFEmergenceApprox.Generic.colLaw R p {ω | ∀ j ∈ S, E j (fieldOR π ω j)} =
      ∏ j ∈ S, RAFEmergenceApprox.Generic.colLaw R p {ω | E j (fieldOR π ω j)} := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      have hi := (fibre_event_indep π p E j S hj).measure_inter_preimage_eq_mul
        {True} {True} (MeasurableSet.singleton True) (MeasurableSet.singleton True)
      have he : {ω : R → Prop | ∀ k ∈ insert j S, E k (fieldOR π ω k)} =
          {ω | E j (fieldOR π ω j)} ∩ {ω | ∀ k ∈ S, E k (fieldOR π ω k)} := by
        ext ω
        simp
      rw [he, Finset.prod_insert hj]
      simpa [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true, ih] using hi
theorem fieldOR_independent (π : R → J) (p : I) :
    iIndepFun (fun j (ω : R → Prop) => fieldOR π ω j)
      (RAFEmergenceApprox.Generic.colLaw R p) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  have he : (⋂ j ∈ S, (fun ω : R → Prop => fieldOR π ω j) ⁻¹' sets j) =
      {ω | ∀ j ∈ S, fieldOR π ω j ∈ sets j} := by
    ext ω
    simp
  rw [he]
  exact fibre_events_product π p (fun j z => z ∈ sets j) S

theorem fieldOR_closed_probability (π : R → J) (p : I) (j : J) :
    RAFEmergenceApprox.Generic.colLaw R p {ω | ¬ fieldOR π ω j} =
      (toNNReal (σ p) : ENNReal) ^ (Finset.univ.filter (fun r => π r = j)).card := by
    have he : {ω : R → Prop | ¬ fieldOR π ω j} =
        {ω | ¬ ∃ r ∈ Finset.univ.filter fun r => π r = j, ω r} := by
      ext ω
      simp [fieldOR]
    rw [he]
    exact RAFEmergenceApprox.Generic.closed_probability _ _
theorem probability_prop_eq_of_false (μ ν : Measure Prop)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ {False} = ν {False}) : μ = ν := by
    apply Measure.ext_of_singleton
    intro q
    by_cases hq : q
    · have he : q = True := propext (iff_true_intro hq)
      have hs : ({True} : Set Prop) = {False}ᶜ := by ext t; simp
      rw [he,hs,measure_compl (MeasurableSet.singleton _) (measure_ne_top _ _),
        measure_compl (MeasurableSet.singleton _) (measure_ne_top _ _),measure_univ,measure_univ,h]
    · have he : q = False := propext (iff_false_intro hq)
      simpa [he] using h
variable {R J : Type*} [Fintype R]

noncomputable def fibreParameter (π : R → J) (p : I) (j : J) : I :=
  σ ((σ p) ^ (Finset.univ.filter (fun r => π r = j)).card)

theorem fibreParameter_value (π : R → J) (p : I) (j : J) :
    (fibreParameter π p j : ℝ) =
      1-(1-(p : ℝ))^(Finset.univ.filter (fun r => π r = j)).card := by
  simp [fibreParameter]

theorem fieldOR_marginal (π : R → J) (p : I) (j : J) :
    (RAFEmergenceApprox.Generic.colLaw R p).map (fun ω => fieldOR π ω j) =
      ambientCoordLaw (fibreParameter π p j) := by
      have hm := measurable_of_finite fun ω : R → Prop => fieldOR π ω j
      apply probability_prop_eq_of_false
      rw [Measure.map_apply hm (MeasurableSet.singleton _)]
      have he : (fun ω : R → Prop => fieldOR π ω j) ⁻¹' {False} =
          {ω | ¬ fieldOR π ω j} := by ext ω; simp
      rw [he,fieldOR_closed_probability,ambientCoordLaw_false]
      simp [fibreParameter, symm_symm]
      rw [← ENNReal.coe_pow]
      congr 1
/-- The complete quotient ensemble is a product law with its actual fibre
probabilities. Singleton and double fibres need not have the same parameter. -/
theorem fieldOR_map [Fintype J] (π : R → J) (p : I) :
    (RAFEmergenceApprox.Generic.colLaw R p).map (fieldOR π) =
      Measure.pi (fun j => ambientCoordLaw (fibreParameter π p j)) := by
    have he := (fieldOR_independent π p).map_fun_eq_pi_map
      fun _ => (measurable_of_finite _).aemeasurable
    change (RAFEmergenceApprox.Generic.colLaw R p).map (fieldOR π) = _ at he
    rw [he]
    congr 1
    funext j
    exact fieldOR_marginal π p j
/-- Finite inhomogeneous Bernoulli product laws are ordered on increasing events. -/
theorem product_increasing_mono {J : Type*} [Fintype J]
    (a c : J → I) (hac : ∀ j, a j ≤ c j)
    (E : (J → Prop) → Prop) (hE : Monotone E) :
    (Measure.pi (fun j => ambientCoordLaw (a j))) {ω | E ω} ≤
      (Measure.pi (fun j => ambientCoordLaw (c j))) {ω | E ω} := by
              choose b hb using fun j => exists_sprinkling_increment (hac j)
              let μ := fun j =>
                (ambientCoordLaw (a j)).prod (ambientCoordLaw (b j))
              have : ∀ j, IsProbabilityMeasure (μ j) := by intro j; dsimp [μ]; infer_instance
              have hleft : (Measure.pi μ).map (fun ω j => (ω j).1) =
                  Measure.pi fun j => ambientCoordLaw (a j) := by
                rw [Measure.pi_map_pi (μ := μ) (f := fun (_ : J) (z : Prop × Prop) => z.1)
                  fun _ => measurable_fst.aemeasurable]
                simp [μ]
              have hunion : (Measure.pi μ).map (fun ω j => (ω j).1 ∨ (ω j).2) =
                  Measure.pi fun j => ambientCoordLaw (c j) := by
                rw [Measure.pi_map_pi (μ := μ) (f := fun _ (z : Prop × Prop) => z.1 ∨ z.2)
                  fun _ => (measurable_of_finite _).aemeasurable]
                simp [μ, ambientCoordLaw_union, hb]
              rw [← hleft, ← hunion,
                Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet,
                Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
              apply measure_mono
              intro ω hω
              exact hE (fun _ h => Or.inl h) hω
noncomputable def halfParameter (a : I) : I := ⟨(a : ℝ)/2, by
  constructor
  · exact div_nonneg a.property.1 (by norm_num)
  · have := a.property.2; linarith⟩

theorem fibreParameter_half_le {R J : Type*} [Fintype R]
    (π : R → J) (a : I) (j : J)
    (hm : (Finset.univ.filter (fun r => π r = j)).card ≤ 2) :
    fibreParameter π (halfParameter a) j ≤ a := by
    change (fibreParameter π (halfParameter a) j : ℝ) ≤ (a : ℝ)
    rw [fibreParameter_value]
    have ha0 := a.property.1
    have ha1 := a.property.2
    let m := (Finset.univ.filter fun r => π r = j).card
    change 1-(1-(a : ℝ)/2)^m ≤ (a : ℝ)
    have hm' : m ≤ 2 := hm
    interval_cases m <;> norm_num <;> nlinarith
end

section
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

theorem product_decreasing_mono {J : Type*} [Fintype J]
    (a c : J → I) (hac : ∀ j, a j ≤ c j)
    (E : (J → Prop) → Prop) (hE : Antitone E) :
    (Measure.pi (fun j => ambientCoordLaw (c j))) {ω | E ω} ≤
      (Measure.pi (fun j => ambientCoordLaw (a j))) {ω | E ω} := by
          have hg : Monotone fun ω => ¬ E ω := by
            intro x y hxy hx hy
            exact hx (hE hxy hy)
          have hc (q : J → I) : (Measure.pi fun j => ambientCoordLaw (q j)) {ω | E ω} =
              1-(Measure.pi fun j => ambientCoordLaw (q j)) {ω | ¬ E ω} := by
            have he : {ω | E ω} = {ω | ¬ E ω}ᶜ := by ext ω; simp
            rw [he,measure_compl (Set.toFinite _).measurableSet (measure_ne_top _ _),measure_univ]
          rw [hc a,hc c]
          exact tsub_le_tsub_left (product_increasing_mono a c hac (fun ω => ¬ E ω) hg) 1
noncomputable def quotientStaticMeasure (n : ℕ) (a : I) :=
  Measure.pi (fun _ : RepositoryChannel n => ambientCoordLaw a)

noncomputable def quotientOpen {n : ℕ} (ω : RepositoryChannel n → Prop) :
    Finset (RepositoryChannel n) := Finset.univ.filter ω

theorem quotientOpen_OR {n : ℕ} (ω : Reaction n → Prop) :
    quotientOpen (fieldOR splitToQuotient ω) =
      (staticOpenReactions ω).image splitToQuotient := by
  ext j
  simp [quotientOpen,fieldOR,staticOpenReactions,and_comm]

theorem quotientClosure_OR {n L : ℕ} (ω : Reaction n → Prop) :
    quotientClosure n L (quotientOpen (fieldOR splitToQuotient ω)) =
      temporaryReactionClosure L (staticOpenReactions ω) := by
    rw [quotientOpen_OR]
    ext x
    simp [mem_quotientClosure,mem_temporaryReactionClosure,split_closure_eq_quotient]
theorem quotient_mass_failure_antitone (n L m : ℕ) :
    Antitone (fun ω : RepositoryChannel n → Prop =>
      m*(quotientClosure n L (quotientOpen ω)).card < (m-1)*Fintype.card (Molecule n)) := by
    intro x y hxy hy
    have hs : quotientOpen x ⊆ quotientOpen y := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy j (Finset.mem_filter.mp hj).2⟩
    exact lt_of_le_of_lt (Nat.mul_le_mul_left m (Finset.card_le_card (quotientClosure_mono n L hs))) hy

end

section
open Classical RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold

theorem splitToOrdered_surjective (n : ℕ) : Function.Surjective (@splitToOrdered n) := by
    intro q
    obtain ⟨r,hl,hr,_⟩ := source_append_split
      (moleculeWord q.val.1) (moleculeWord q.val.2)
      (by rw [moleculeWord_length]; exact Nat.succ_pos _)
      (by rw [moleculeWord_length]; exact Nat.succ_pos _)
      (by simpa [moleculeWord_length] using q.property)
    refine ⟨r, Subtype.ext (Prod.ext ?_ ?_)⟩
    · exact moleculeWord_injective hl
    · exact moleculeWord_injective hr
theorem splitToQuotient_surjective (n : ℕ) : Function.Surjective (@splitToQuotient n) :=
  (canonical_surjective n).comp (splitToOrdered_surjective n)

theorem quotient_mark_pullback_OR {n : ℕ} (ω : RepositoryChannel n → Prop) (j : RepositoryChannel n) :
    (∃ r : Reaction n, splitToQuotient r = j ∧ ω (splitToQuotient r)) ↔ ω j := by
  constructor
  · rintro ⟨r, rfl, hr⟩
    exact hr
  · intro hj
    obtain ⟨r,hr⟩ := splitToQuotient_surjective n j
    exact ⟨r,hr,hr.symm ▸ hj⟩

end

section
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

noncomputable def orderedCoordinate {n : ℕ} (r : OrderedChannel n) : List Bool × ℕ :=
  (moleculeWord r.val.1 ++ moleculeWord r.val.2, molLength r.val.1)

theorem orderedCoordinate_split {n : ℕ} (r : Reaction n) :
    orderedCoordinate (splitToOrdered r) = literalSplitCoordinate r := by
  apply Prod.ext
  · exact reaction_words_append r
  · exact molLength_reactionLeft r

theorem orderedCoordinate_injective (n : ℕ) : Function.Injective (@orderedCoordinate n) := by
  intro q j he
  obtain ⟨r,rfl⟩ := splitToOrdered_surjective n q
  obtain ⟨s,rfl⟩ := splitToOrdered_surjective n j
  rw [orderedCoordinate_split,orderedCoordinate_split] at he
  exact congrArg splitToOrdered (literalSplitCoordinate_injective n he)

noncomputable def quotientCoordinate {n : ℕ} (j : RepositoryChannel n) : List Bool × ℕ :=
  orderedCoordinate ⟨j.val,j.property.1⟩

theorem quotientCoordinate_injective (n : ℕ) : Function.Injective (@quotientCoordinate n) := by
  intro j k he
  exact Subtype.ext (congrArg (fun q : OrderedChannel n => q.val)
    (orderedCoordinate_injective n he))

theorem word_comm_iff {n : ℕ} (u v : Molecule n) :
    moleculeWord u ++ moleculeWord v = moleculeWord v ++ moleculeWord u ↔
      displayedConcat u v = displayedConcat v u := by
      constructor
      · intro he
        have hc := congrArg binaryWordCode he
        simpa [binaryWordCode_append,binaryWordCode_moleculeWord,moleculeWord_length,
          displayedConcat] using hc
      · intro hc
        apply binaryWordCode_injective_length (by simp [Nat.add_comm])
        simpa [binaryWordCode_append,binaryWordCode_moleculeWord,moleculeWord_length,
          displayedConcat] using hc
theorem canonicalIndex_ordered {n : ℕ} (r : OrderedChannel n) :
    canonicalIndex (orderedCoordinate r) = quotientCoordinate (canonical r) := by
        have hu : 0 < molLength r.val.1 := Nat.succ_pos _
        have hv : 0 < molLength r.val.2 := Nat.succ_pos _
        have ht : (moleculeWord r.val.1 ++ moleculeWord r.val.2).take (molLength r.val.1) =
            moleculeWord r.val.1 := by rw [← moleculeWord_length r.val.1]; simp
        have hd : (moleculeWord r.val.1 ++ moleculeWord r.val.2).drop (molLength r.val.1) =
            moleculeWord r.val.2 := by rw [← moleculeWord_length r.val.1]; simp
        unfold canonical
        split
        · rename_i h
          have hn : ¬ (molLength r.val.2 < molLength r.val.1 ∧
              moleculeWord r.val.1 ++ moleculeWord r.val.2 =
                moleculeWord r.val.2 ++ moleculeWord r.val.1) := by
            rintro ⟨hl,hc⟩
            rcases h with h | h
            · exact h ((word_comm_iff _ _).mp hc)
            · unfold moleculePrecedes at h
              omega
          simp only [canonicalIndex,orderedCoordinate,ht,hd,List.length_append,moleculeWord_length, Nat.add_sub_cancel_left]
          rw [ite_eq_right (by intro h; exact hn ⟨h.2.2.1,h.2.2.2⟩)]
          rfl
        · rename_i h
          have hl := noncanonical_strict_lengths r h
          have hc : displayedConcat r.val.1 r.val.2 = displayedConcat r.val.2 r.val.1 :=
            Classical.byContradiction fun hn => h (Or.inl hn)
          have hw := (word_comm_iff _ _).mpr hc
          simp only [canonicalIndex,orderedCoordinate,ht,hd,List.length_append,moleculeWord_length, Nat.add_sub_cancel_left]
          rw [ite_eq_left ⟨hu,by omega,hl,hw⟩]
          exact Prod.ext hw rfl
theorem canonicalIndex_split {n : ℕ} (r : Reaction n) :
    canonicalIndex (literalSplitCoordinate r) = quotientCoordinate (splitToQuotient r) := by
  rw [← orderedCoordinate_split]
  exact canonicalIndex_ordered _

theorem infinite_quotient_restriction_map (n : ℕ) (a : I) :
    (infiniteSplitPi a).map (fun ω j => ω (quotientCoordinate j)) = quotientStaticMeasure n a := by
      have hi : iIndepFun (fun z (ω : SplitField) => ω z) (infiniteSplitPi a) :=
        iIndepFun_infinitePi fun _ => measurable_id
      have hs := hi.precomp (quotientCoordinate_injective n)
      rw [hs.map_fun_eq_pi_map fun j => (measurable_pi_apply (quotientCoordinate j)).aemeasurable]
      have he (j : RepositoryChannel n) : (infiniteSplitPi a).map (fun ω => ω (quotientCoordinate j)) =
          ambientCoordLaw a := by rw [infiniteSplitPi,Measure.infinitePi_map_eval]
      simp_rw [he]
      rfl
end

section
open Classical MeasureTheory unitInterval HordijkSteelThreshold
open scoped ENNReal

def quotientRecordAtom (B : ℕ) (i : RecordPrefixIndex) : Set SplitField :=
  {ω | (fun z => ω (canonicalIndex z)) ∈ recordPrefixAtom B i}

theorem quotientRecordAtom_determined (B : ℕ) (i : RecordPrefixIndex) :
    SplitPrefixDetermined (splitPrefixCoordinates i.1) (quotientRecordAtom B i) := by
  intro ω η he
  apply recordPrefixAtom_determined B i
  intro z hz
  exact he (canonicalIndex z) (canonicalIndex_prefix hz)

theorem quotientRecordAtoms_disjoint (B : ℕ) {i j : RecordPrefixIndex} (hij : i ≠ j) :
    Disjoint (quotientRecordAtom B i) (quotientRecordAtom B j) := by
  apply Set.disjoint_left.mpr
  intro ω hi hj
  exact Set.disjoint_left.mp (recordPrefixAtoms_disjoint B hij) hi hj

end

section
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

noncomputable def quotientInfiniteMeasure (a : I) : Measure InfiniteSplitEnvironment :=
  (infiniteSplitPi a).map quotientField

noncomputable instance quotientInfinite_probability (a : I) :
    IsProbabilityMeasure (quotientInfiniteMeasure a) := by
  unfold quotientInfiniteMeasure
  infer_instance

theorem quotientSurvival_eq (a : I) : quotientSurvival a =
    quotientInfiniteMeasure a {field | ReversibleUnbounded 2 field} := by
  rw [quotientInfiniteMeasure,Measure.map_apply quotientField_measurable
    (measurableSet_reversibleUnbounded 2)]
  rfl

theorem quotientClosure_pullback {n L : ℕ} (q : RepositoryChannel n → Prop) :
    quotientClosure n L (quotientOpen q) =
      temporaryReactionClosure L (staticOpenReactions (fun r => q (splitToQuotient r))) := by
  have he : fieldOR splitToQuotient (fun r => q (splitToQuotient r)) = q := by
    funext j
    exact propext (quotient_mark_pullback_OR q j)
  rw [← quotientClosure_OR,he]

theorem quotientClosure_restriction (n L : ℕ) (ω : SplitField) :
    quotientClosure n L (quotientOpen (fun j => ω (quotientCoordinate j))) =
      temporaryReactionClosure L (restrictedSplitReactions n (quotientField ω)) := by
      rw [quotientClosure_pullback]
      congr 1
      ext r
      simp [staticOpenReactions,restrictedSplitReactions,Finset.mem_filter,Finset.mem_univ,
        true_and]
      unfold quotientField
      apply Iff.of_eq
      simpa [literalSplitCoordinate] using congrArg ω (canonicalIndex_split r).symm
theorem quotient_finite_seed_measure_eq (n L : ℕ) (a : I) (seed : Finset (List Bool)) :
    quotientStaticMeasure n a {q | ∀ w ∈ seed,
      ∃ x ∈ quotientClosure n L (quotientOpen q), moleculeWord x = w} =
    quotientInfiniteMeasure a {field | ∀ w ∈ seed, FiniteReversibleGenerated n L field w} := by
    rw [← infinite_quotient_restriction_map n a,
      Measure.map_apply (Measurable.of_eval fun j => measurable_pi_apply _)
        (Set.toFinite _).measurableSet,
      quotientInfiniteMeasure,Measure.map_apply quotientField_measurable
        (measurableSet_finite_seed n L seed)]
    congr 1
    ext ω
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,quotientClosure_restriction]
    apply forall_congr'
    intro w
    apply forall_congr'
    intro _
    exact (finiteReversible_iff_literalClosure (quotientField ω) w).symm
theorem quotient_finite_seed_tendsto (L : ℕ) (a : I) (seed : Finset (List Bool)) :
    Filter.Tendsto (fun n => quotientStaticMeasure n a {q | ∀ w ∈ seed,
      ∃ x ∈ quotientClosure n L (quotientOpen q), moleculeWord x = w}) Filter.atTop
      (nhds (quotientInfiniteMeasure a {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w})) := by
  simp_rw [quotient_finite_seed_measure_eq]
  exact finite_seed_probability_tendsto (quotientInfiniteMeasure a) L seed

def quotientEscapeEvent (L K : ℕ) : Set (RepositoryChannel (2*(K+L)) → Prop) :=
  {q | ∃ x ∈ quotientClosure (2*(K+L)) L (quotientOpen q), K+L < (moleculeWord x).length}

theorem quotient_escape_measure_eq (L K : ℕ) (a : I) :
    quotientStaticMeasure (2*(K+L)) a (quotientEscapeEvent L K) =
      quotientInfiniteMeasure a (reversibleEscapeEvent L K) := by
      rw [← infinite_quotient_restriction_map (2*(K+L)) a,
        Measure.map_apply (Measurable.of_eval fun j => measurable_pi_apply _)
          (Set.toFinite _).measurableSet,
        quotientInfiniteMeasure,Measure.map_apply quotientField_measurable
          (measurableSet_reversibleEscapeEvent L K)]
      congr 1
      ext ω
      change (∃ x ∈ quotientClosure _ L (quotientOpen fun j => ω (quotientCoordinate j)),
        K+L < (moleculeWord x).length) ↔
        ∃ w, K+L < w.length ∧ FiniteReversibleGenerated (2*(K+L)) L (quotientField ω) w
      rw [quotientClosure_restriction]
      constructor
      · rintro ⟨x,hx,hl⟩
        exact ⟨moleculeWord x,hl,literalClosure_to_finiteReversible _ x hx⟩
      · rintro ⟨w,hw,hg⟩
        obtain ⟨x,hx,he⟩ := finiteReversible_to_literalClosure hg
        exact ⟨x,hx,by simpa [he] using hw⟩
theorem quotient_escape_tendsto (a : I) :
    Filter.Tendsto (fun K => quotientStaticMeasure (2*(K+2)) a (quotientEscapeEvent 2 K))
      Filter.atTop (nhds (quotientSurvival a)) := by
  simp_rw [quotient_escape_measure_eq,quotientSurvival_eq]
  exact reversible_escape_probability_tendsto (quotientInfiniteMeasure a) 2

end

section
open Classical RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold
open RAFEmergenceApprox.Generic

set_option Elab.async false

noncomputable def splitPreimage {n : ℕ} (A : Finset (RepositoryChannel n)) : Finset (Reaction n) :=
  Finset.univ.filter (fun r => splitToQuotient r ∈ A)

theorem quotientClosure_preimage {n L : ℕ} (A : Finset (RepositoryChannel n)) :
    quotientClosure n L A = temporaryReactionClosure L (splitPreimage A) := by
  have he : quotientOpen (fun j => j ∈ A) = A := by ext j; simp [quotientOpen]
  rw [← he,quotientClosure_pullback]
  congr 1
  ext r
  simp [staticOpenReactions,splitPreimage,quotientOpen]

noncomputable def quotientUsable {n : ℕ} (L : ℕ) (A : Finset (RepositoryChannel n)) :=
  (usableClosureReactions L (splitPreimage A)).image splitToQuotient

theorem quotient_usable_hasRAF {n L : ℕ} (A : Finset (RepositoryChannel n))
    (ω : RepositoryChannel n → Molecule n → Prop)
    (hcat : ∀ j ∈ A, ∃ x ∈ quotientClosure n L A, ω j x)
    (hne : (quotientUsable L A).Nonempty) :
    ∃ S, IsRevRAF (repositoryCRS n L) (fun x j => ω j x) S := by
    have hs : IsRevRAF (binaryPolymerCRS n L) (fun x r => ω (splitToQuotient r) x)
        (usableClosureReactions L (splitPreimage A)) := by
      apply RAFEmergenceApprox.usable_isRAF
      · intro r hr
        obtain ⟨x,hx,hc⟩ := hcat _ (Finset.mem_filter.mp hr).2
        exact ⟨x,(quotientClosure_preimage A) ▸ hx,hc⟩
      · exact Finset.image_nonempty.mp hne
    have he : orCatalysis splitToQuotient (fun x r => ω (splitToQuotient r) x) =
        fun x j => ω j x := by
      funext x j
      exact propext (quotient_mark_pullback_OR (fun j => ω j x) j)
    have h := split_raf_image L _ ⟨_,hs⟩
    rwa [he] at h
theorem quotient_raf_subset_peeling {n L : ℕ} (ω : RepositoryChannel n → Molecule n → Prop)
    {S : Finset (RepositoryChannel n)}
    (hS : IsRevRAF (repositoryCRS n L) (fun x j => ω j x) S) (t : ℕ) :
    S ⊆ peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω) (quotientClosure n L) t := by
  induction t with
  | zero =>
    intro r hr
    obtain ⟨x,k,_,hx⟩ := hS.2.2 r hr
    exact (RAFEmergenceApprox.Generic.mem_catalystActive _ _ _).mpr ⟨x,Finset.mem_univ _,hx⟩
  | succ t ih =>
    intro r hr
    obtain ⟨x,k,hx,hcat⟩ := hS.2.2 r hr
    apply (RAFEmergenceApprox.Generic.mem_catalystActive _ _ _).mpr
    exact ⟨x,quotientClosure_mono n L ih ((mem_quotientClosure S x).mpr ⟨k,hx⟩),hcat⟩

theorem quotient_terminal_of_usable {n L : ℕ}
    (ω : RepositoryChannel n → Molecule n → Prop)
    (hne : (quotientUsable L (peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω)
      (quotientClosure n L) (Fintype.card (RepositoryChannel n)))).Nonempty) :
    ∃ S, IsRevRAF (repositoryCRS n L) (fun x j => ω j x) S := by
  let A := peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω) (quotientClosure n L)
    (Fintype.card (RepositoryChannel n))
  have hs : RAFEmergenceApprox.Generic.catalystActive ω (quotientClosure n L A) = A :=
    peelingActiveAt_stable_card _ _ (RAFEmergenceApprox.Generic.catalystActive_mono ω)
      (quotientClosure_mono n L)
  apply quotient_usable_hasRAF A ω _ hne
  intro j hj
  exact (RAFEmergenceApprox.Generic.mem_catalystActive _ _ _).mp (by rw [hs]; exact hj)

theorem quotient_terminal_hasRAF {n : ℕ} (ω : RepositoryChannel n → Molecule n → Prop)
    (hmass : 6 < (quotientClosure n 2 (peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω)
      (quotientClosure n 2) (Fintype.card (RepositoryChannel n)))).card) :
    ∃ S, IsRevRAF (repositoryCRS n 2) (fun x j => ω j x) S := by
    apply quotient_terminal_of_usable ω
    apply Finset.image_nonempty.mpr
    apply usableClosureReactions_nonempty
    rw [← quotientClosure_preimage]
    by_contra h
    have hs : quotientClosure n 2 (peelingActiveAt (RAFEmergenceApprox.Generic.catalystActive ω)
        (quotientClosure n 2) (Fintype.card (RepositoryChannel n))) ⊆ binaryFood n 2 := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.le_of_not_gt fun hl => h ⟨x,hx,hl⟩⟩
    have hc := (Finset.card_le_card hs).trans (binaryFood_card_le_cutoff n 2)
    have h6 : Fintype.card (Molecule 2) = 6 := by decide
    omega
end

section
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

set_option Elab.async false

theorem quotient_pool_column_map (n : ℕ) (p : I) (C : Finset (Molecule n)) :
    (RAFEmergenceApprox.Generic.colLaw (Molecule n) p).map (fun v => ∃ x ∈ C, v x) =
      ambientCoordLaw (fixedPoolParameter p C.card) := by
  apply probability_prop_eq_of_false
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton _)]
  have he : (fun v : Molecule n → Prop => ∃ x ∈ C, v x) ⁻¹' {False} =
      {v | ¬ ∃ x ∈ C, v x} := by ext v; simp
  rw [he,RAFEmergenceApprox.Generic.closed_probability,ambientCoordLaw_false]
  simp [fixedPoolParameter,← ENNReal.coe_pow]
  apply NNReal.eq
  simp

theorem quotient_pool_map (n : ℕ) (p : I) (C : Finset (Molecule n)) :
    (quotientCatalyticLaw n p).map (fun ω j => ∃ x ∈ C, ω j x) =
      quotientStaticMeasure n (fixedPoolParameter p C.card) := by
      change (Measure.pi fun _ : RepositoryChannel n => RAFEmergenceApprox.Generic.colLaw (Molecule n) p).map
          (fun ω j => ∃ x ∈ C, ω j x) = _
      rw [Measure.pi_map_pi
        (μ := fun _ : RepositoryChannel n => RAFEmergenceApprox.Generic.colLaw (Molecule n) p)
        (f := fun (_ : RepositoryChannel n) (v : Molecule n → Prop) => ∃ x ∈ C, v x)
        fun _ => (measurable_of_finite _).aemeasurable]
      simp_rw [quotient_pool_column_map]
      rfl
theorem quotient_pool_statistic (n : ℕ) (p : I) (C : Finset (Molecule n))
    (stat : Finset (RepositoryChannel n) → Prop) :
    quotientCatalyticLaw n p {ω | stat (RAFEmergenceApprox.Generic.catalystActive ω C)} =
      quotientStaticMeasure n (fixedPoolParameter p C.card) {q | stat (quotientOpen q)} := by
  rw [← quotient_pool_map n p C,Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  rfl

theorem quotient_peeling_statistic (n L : ℕ) (p : I) (T : ℕ)
    (stat : Finset (RepositoryChannel n) → Prop) :
    quotientCatalyticLaw n p {ω | stat (peelingActiveAt
      (RAFEmergenceApprox.Generic.catalystActive ω) (quotientClosure n L) T)} =
    quotientCatalyticLaw n p {ω | stat (peelingActiveAt
      (fun C => RAFEmergenceApprox.Generic.catalystActive ω (finiteInitialSegment (Molecule n) C.card))
      (quotientClosure n L) T)} := by
      let E : Set (Fin (T+1) → RepositoryChannel n → Prop) :=
        {H | stat (Finset.univ.filter (H ⟨T,Nat.lt_succ_self T⟩))}
      have he := congrArg (fun μ : Measure (Fin (T+1) → RepositoryChannel n → Prop) => μ E)
        (quotient_history_map n L p T)
      rw [Measure.map_apply (measurable_of_finite _) (Set.toFinite E).measurableSet,
        Measure.map_apply (measurable_of_finite _) (Set.toFinite E).measurableSet] at he
      have hfinal (response : Finset (Molecule n) → Finset (RepositoryChannel n)) :
          Finset.univ.filter (activeTrace response (quotientClosure n L) T
            ⟨T,Nat.lt_succ_self T⟩) = peelingActiveAt response (quotientClosure n L) T := by
        ext r
        simp [Finset.mem_filter,Finset.mem_univ,true_and,activeTrace]
      simpa [E,Set.preimage,Set.mem_ofPred_eq,hfinal] using he
theorem quotient_mass_ge_static (n L : ℕ) (p : I) (k T : ℕ) :
    quotientStaticMeasure n (fixedPoolParameter p (finiteInitialSegment (Molecule n) k).card)
      {q | k ≤ (quotientClosure n L (quotientOpen q)).card} ≤
    quotientCatalyticLaw n p {ω | k ≤ (quotientClosure n L (peelingActiveAt
      (RAFEmergenceApprox.Generic.catalystActive ω) (quotientClosure n L) T)).card} := by
        rw [← quotient_pool_statistic n p (finiteInitialSegment (Molecule n) k)
            fun A => k ≤ (quotientClosure n L A).card,
          quotient_peeling_statistic n L p T fun A => k ≤ (quotientClosure n L A).card]
        apply measure_mono
        intro ω hω
        have hm : Monotone fun k => RAFEmergenceApprox.Generic.catalystActive ω
            (finiteInitialSegment (Molecule n) k) :=
          (RAFEmergenceApprox.Generic.catalystActive_mono ω).comp (finiteInitialSegment_mono _)
        have hs := RAFEmergenceApprox.scalar_barrier_subset _ (quotientClosure n L) hm
          (quotientClosure_mono n L) k (hω.trans (Finset.card_le_univ _)) hω T
        exact hω.trans (Finset.card_le_card (quotientClosure_mono n L hs))
end

section
open Classical Filter MeasureTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

theorem quotient_same_field_seed_mass (N L m : ℕ) (a : I) :
    quotientStaticMeasure N a {q | ∀ w ∈ actualBinaryWords L,
      ∃ x ∈ quotientClosure N 2 (quotientOpen q), moleculeWord x = w} ≤
    quotientStaticMeasure N a {q | (m-1)*Fintype.card (Molecule N) ≤
      m*(quotientClosure N 2 (quotientOpen q)).card} +
    quotientStaticMeasure N a {q | m*(quotientClosure N L (quotientOpen q)).card <
      (m-1)*Fintype.card (Molecule N)} := by
  apply (measure_mono (show {q : RepositoryChannel N → Prop | ∀ w ∈ actualBinaryWords L,
      ∃ x ∈ quotientClosure N 2 (quotientOpen q), moleculeWord x = w} ⊆
      {q | (m-1)*Fintype.card (Molecule N) ≤ m*(quotientClosure N 2 (quotientOpen q)).card} ∪
      {q | m*(quotientClosure N L (quotientOpen q)).card < (m-1)*Fintype.card (Molecule N)} from ?_)).trans
      (measure_union_le _ _)
  intro q hseed
  by_cases hb : m*(quotientClosure N L (quotientOpen q)).card < (m-1)*Fintype.card (Molecule N)
  · exact Or.inr hb
  · left
    have hs : quotientClosure N L (quotientOpen q) ⊆ quotientClosure N 2 (quotientOpen q) := by
      simp only [quotientClosure_pullback] at hseed ⊢
      apply temporaryReactionClosure_seed_transfer Finset.Subset.rfl
      intro x hx
      have hw : moleculeWord x ∈ actualBinaryWords L :=
        (mem_actualBinaryWords _ _).mpr ⟨moleculeWord_nonempty x,by rwa [moleculeWord_length]⟩
      obtain ⟨y,hy,he⟩ := hseed _ hw
      exact moleculeWord_injective he ▸ hy
    exact (Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card hs))

theorem quotient_capped_escape_le (N K : ℕ) (a : I) :
    quotientStaticMeasure N a {q | ∃ x ∈ quotientClosure N 2 (quotientOpen q), K+2 < molLength x} ≤
      quotientInfiniteMeasure a (reversibleEscapeEvent 2 K) := by
        rw [← infinite_quotient_restriction_map N a,
          Measure.map_apply (Measurable.of_eval fun j => measurable_pi_apply _)
            (Set.toFinite _).measurableSet,
          quotientInfiniteMeasure,Measure.map_apply quotientField_measurable
            (measurableSet_reversibleEscapeEvent 2 K)]
        apply measure_mono
        intro ω h
        change ∃ x ∈ quotientClosure N 2 (quotientOpen fun j => ω (quotientCoordinate j)),
          K+2 < molLength x at h
        rw [quotientClosure_restriction] at h
        obtain ⟨x,hx,hl⟩ := h
        apply (reversibleEscapeEvent_iff 2 K (quotientField ω)).mpr
        exact ⟨moleculeWord x,by simpa [moleculeWord_length] using hl,
          finiteReversibleGenerated_to_infinite (literalClosure_to_finiteReversible _ x hx)⟩
end

section
open Classical Filter MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

set_option Elab.async false

def quotientRAFEvent (n : ℕ) : Set (RepositoryChannel n → Molecule n → Prop) :=
  {ω | ∃ S, IsRevRAF (repositoryCRS n 2) (fun x j => ω j x) S}

noncomputable def quotientRAFProbability (n : ℕ) (p : I) : ENNReal :=
  quotientCatalyticLaw n p (quotientRAFEvent n)

theorem quotient_static_barrier (n : ℕ) (p : I) (k : ℕ) (hk : 6 < k) :
    quotientStaticMeasure n (fixedPoolParameter p (finiteInitialSegment (Molecule n) k).card)
      {q | k ≤ (quotientClosure n 2 (quotientOpen q)).card} ≤ quotientRAFProbability n p := by
  apply (quotient_mass_ge_static n 2 p k (Fintype.card (RepositoryChannel n))).trans
  apply measure_mono
  intro ω hω
  exact quotient_terminal_hasRAF ω (hk.trans_le hω)

theorem quotient_near_full_lower (n m : ℕ) (p q : I) (hm : 0 < m)
    (hk : 6 < nearFullPoolSize n m)
    (hq : q ≤ fixedPoolParameter p (nearFullPoolSize n m)) :
    quotientStaticMeasure n q {ω | (m-1)*Fintype.card (Molecule n) ≤
      m*(quotientClosure n 2 (quotientOpen ω)).card} ≤ quotientRAFProbability n p := by
    let k := nearFullPoolSize n m
    have hmass : quotientStaticMeasure n q {ω | (m-1)*Fintype.card (Molecule n) ≤
        m*(quotientClosure n 2 (quotientOpen ω)).card} ≤
        quotientStaticMeasure n q {ω | k ≤ (quotientClosure n 2 (quotientOpen ω)).card} := by
      apply measure_mono
      intro ω hω
      change (m-1)*Fintype.card (Molecule n) ≤ m*(quotientClosure n 2 (quotientOpen ω)).card at hω
      have hd := Nat.div_mul_le_self (Fintype.card (Molecule n)) m
      dsimp [k,nearFullPoolSize]
      nlinarith
    have hmono := product_increasing_mono (fun _ : RepositoryChannel n => q)
      (fun _ => fixedPoolParameter p k) (fun _ => hq)
      (fun ω => k ≤ (quotientClosure n 2 (quotientOpen ω)).card) (by
        intro x y hxy hx
        apply hx.trans
        apply Finset.card_le_card
        apply quotientClosure_mono
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy j (Finset.mem_filter.mp hj).2⟩)
    have he : (finiteInitialSegment (Molecule n) k).card = k :=
      card_finiteInitialSegment _ _ (nearFullPoolSize_le n m)
    have hbar := quotient_static_barrier n p k hk
    rw [he] at hbar
    exact hmass.trans (hmono.trans hbar)
theorem quotient_coordinate_probability (n : ℕ) (p : I) (j : RepositoryChannel n) (x : Molecule n) :
    quotientCatalyticLaw n p {ω | ω j x} = (toNNReal p : ENNReal) := by
  have hj := (measurePreserving_eval
    (fun _ : RepositoryChannel n => RAFEmergenceApprox.Generic.colLaw (Molecule n) p) j).map_eq
  have hx := (measurePreserving_eval (fun _ : Molecule n => ambientCoordLaw p) x).map_eq
  have he := congrArg (fun μ : Measure (Molecule n → Prop) => μ {v | v x}) hj
  rw [Measure.map_apply (measurable_pi_apply _) (Set.toFinite _).measurableSet] at he
  change quotientCatalyticLaw n p {ω | ω j x} =
    RAFEmergenceApprox.Generic.colLaw (Molecule n) p {v | v x} at he
  rw [he]
  have hh := congrArg (fun μ : Measure Prop => μ {True}) hx
  rw [Measure.map_apply (measurable_pi_apply _) (MeasurableSet.singleton _)] at hh
  simpa [RAFEmergenceApprox.Generic.colLaw,ambientCoordLaw] using hh

def quotientBoundedSeed (n K : ℕ) : Set (RepositoryChannel n → Molecule n → Prop) :=
  {ω | ∃ x : Molecule n, ∃ j : RepositoryChannel n,
    molLength x ≤ K ∧ RevSeedReaction (repositoryCRS n 2) j ∧ ω j x}

theorem quotient_bounded_seed_le (n K : ℕ) (p : I) :
    quotientCatalyticLaw n p (quotientBoundedSeed n K) ≤
      (Fintype.card (Molecule K) : ENNReal)*34*(toNNReal p : ENNReal) := by
    let J := ↥(binaryFood n K) × ↥(repositorySeedChannels n 2)
    let E : J → Set (RepositoryChannel n → Molecule n → Prop) := fun j => {ω | ω j.2.val j.1.val}
    have he : quotientBoundedSeed n K = ⋃ j : J, E j := by
      ext ω
      simp only [quotientBoundedSeed,Set.mem_ofPred_eq,Set.mem_iUnion,E]
      constructor
      · rintro ⟨x,r,hx,hr,hω⟩
        exact ⟨(⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩,
          ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩⟩),hω⟩
      · rintro ⟨⟨x,r⟩,hω⟩
        exact ⟨x.val,r.val,(Finset.mem_filter.mp x.property).2,(Finset.mem_filter.mp r.property).2,hω⟩
    rw [he]
    calc
      _ ≤ ∑ j : J, quotientCatalyticLaw n p (E j) := measure_iUnion_fintype_le _ _
      _ = (Fintype.card J : ENNReal)*(toNNReal p : ENNReal) := by
        simp [E,quotient_coordinate_probability,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul_left
        have hc : Fintype.card J ≤ Fintype.card (Molecule K)*34 := by
          dsimp [J]
          rw [Fintype.card_prod,Fintype.card_coe,Fintype.card_coe]
          exact Nat.mul_le_mul (binaryFood_card_le_cutoff n K) (repositorySeedChannels_card_le_34 n)
        exact_mod_cast hc
theorem quotient_raf_upper (n K : ℕ) (p : I) :
    quotientRAFProbability n p ≤
      quotientStaticMeasure (2*(K+2)) (fixedPoolParameter p (Fintype.card (Molecule n)))
        (quotientEscapeEvent 2 K) + (Fintype.card (Molecule (K+2)) : ENNReal)*34*(toNNReal p : ENNReal) := by
      let E : Set (RepositoryChannel n → Molecule n → Prop) := {ω | ∃ x ∈
        quotientClosure n 2 (RAFEmergenceApprox.Generic.catalystActive ω Finset.univ), K+2 < molLength x}
      have hs : quotientRAFEvent n ⊆ E ∪ quotientBoundedSeed n (K+2) := by
        intro ω hraf
        by_cases he : ω ∈ E
        · exact Or.inl he
        · right
          obtain ⟨S,hS⟩ := hraf
          obtain ⟨r,hr,hseed⟩ := exists_rev_seed_of_foodGenerated _ S hS.1 hS.2.1
          obtain ⟨x,k,hx,hcat⟩ := hS.2.2 r hr
          have hsub := quotient_raf_subset_peeling ω hS 0
          have hx' := quotientClosure_mono n 2 hsub ((mem_quotientClosure S x).mpr ⟨k,hx⟩)
          exact ⟨x,r,Nat.le_of_not_gt fun hl => he ⟨x,hx',hl⟩,hseed,hcat⟩
      have hb := (measure_mono hs).trans ((measure_union_le _ _).trans
        (add_le_add_right (quotient_bounded_seed_le n (K+2) p) _))
      apply hb.trans
      apply add_le_add_left
      change quotientCatalyticLaw n p {ω | ∃ x ∈ quotientClosure n 2
        (RAFEmergenceApprox.Generic.catalystActive ω Finset.univ), K+2 < molLength x} ≤ _
      rw [quotient_pool_statistic n p Finset.univ
        fun A => ∃ x ∈ quotientClosure n 2 A, K+2 < molLength x,Finset.card_univ,
        quotient_escape_measure_eq]
      exact quotient_capped_escape_le n K _
end

section
open Classical MeasureTheory unitInterval HordijkSteelThreshold RAF.Polymer
open OverlapCorrectedRAF.Source

set_option Elab.async false

end

section
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval HordijkSteelThreshold
open scoped ENNReal Topology

theorem quotientSurvival_le_finite_escape (a : I) (K : ℕ) :
    quotientSurvival a ≤ quotientStaticMeasure (2*(K+2)) a (quotientEscapeEvent 2 K) := by
  rw [quotient_escape_measure_eq, quotientSurvival_eq]
  apply measure_mono
  intro field hf
  exact (reversibleEscapeEvent_iff 2 K field).mpr (hf (K+2))

end

section
open Classical Filter MeasureTheory unitInterval HordijkSteelThreshold RAF.Polymer
open OverlapCorrectedRAF.Source
open scoped ENNReal Topology

set_option Elab.async false

noncomputable def criticalOpenness (lambda : ℝ) (hlambda : 0 < lambda) : I :=
  ⟨1-Real.exp (-lambda), by
    constructor
    · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    · linarith [Real.exp_pos (-lambda)]⟩

/-- Probability of infinite ordinary reversible closure in the canonical
repository-channel iid field, with all six food molecules. -/
noncomputable def quotientTransitionLimit (lambda : ℝ) (hlambda : 0 < lambda) : ℝ :=
  (quotientSurvival (criticalOpenness lambda hlambda)).toReal

end

end RAFReactionQuotient
