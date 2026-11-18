module

public import proofs.RAF.Core

@[expose] public section

namespace HordijkSteelThreshold
open Filter MeasureTheory ProbabilityTheory unitInterval RAF RAF.Polymer RAF.Concrete
open scoped ENNReal

/-- Exact number of nonempty binary words of length at most `n`. -/
theorem card_molecules_exact (n : Nat) :
    Fintype.card (Molecule n) = 2 ^ (n + 1) - 2 := by
  rw [card_molecule_sigma, Fin.sum_univ_eq_sum_range fun k => 2 ^ (k + 1)]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have : 0 < 2 ^ n := by positivity
    simp only [pow_succ]; omega

/-- Exact split-position reversible reaction count. -/
theorem card_reactions_exact {n : Nat} (hn : 2 ≤ n) :
    Fintype.card (Reaction n) = (n - 2) * 2 ^ (n + 1) + 4 := by
  rw [card_reaction_sigma, Fin.sum_univ_eq_sum_range fun k => 2 ^ (k + 1) * k]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  clear hn; simp only [Nat.add_sub_cancel]
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, Finset.sum_range_succ, ih]
    simp only [pow_succ]; ring

theorem revSeedReaction_iff_factor_lengths {n t : Nat} (r : Reaction n) :
    RevSeedReaction (binaryPolymerCRS n t) r ↔
      reactionLeftLength r ≤ t ∧ reactionRightLength r ≤ t := by
  simp only [RevSeedReaction, binaryPolymerCRS, binaryFood, Finset.subset_iff,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and,
    forall_eq_or_imp, forall_eq, molLength_reactionLeft, molLength_reactionRight]
  have := reaction_length_add r
  change _ ∨ reactionProductLength r ≤ t ↔ _
  omega

theorem card_concrete_gateway_binary_t2 (n : Nat) :
    Fintype.card (PolymerSeedReaction n 2) ≤ 36 := by
  let f : PolymerSeedReaction n 2 → PolymerSeedReaction 4 2 := fun r =>
    ⟨⟨⟨r.1.1.val, by
      have h := (revSeedReaction_iff_factor_lengths r.1).mp r.2
      change r.1.2.2.val + 1 ≤ 2 ∧ r.1.1.val - r.1.2.2.val ≤ 2 at h; omega⟩, r.1.2⟩,
      (revSeedReaction_iff_factor_lengths _).mpr ((revSeedReaction_iff_factor_lengths r.1).mp r.2)⟩
  refine (Fintype.card_le_of_injective f fun ⟨⟨a1, a2⟩, _⟩ ⟨⟨b1, b2⟩, _⟩ h => ?_).trans_eq (by decide)
  obtain rfl : a1 = b1 := Fin.ext (congrArg (·.1.1.val) h)
  exact Subtype.ext (congrArg (Sigma.mk _) (eq_of_heq (Sigma.mk.inj (Subtype.mk.inj h)).2))

theorem card_molecule_tendsto_atTop :
    Tendsto (fun n : Nat => Fintype.card (Molecule n)) atTop atTop := by
  simp_rw [card_molecules_exact]
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp
    (tendsto_add_atTop_nat 1)) (eventually_ge_atTop (b + 2))] with n (hn : b + 2 ≤ 2 ^ (n + 1))
  omega

theorem revClosureStep_mono {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} {A B : Finset M}
    (hST : S ⊆ T) (hAB : A ⊆ B) :
    revClosureStep Q S A ⊆ revClosureStep Q T B := by
  intro x hx
  simp only [revClosureStep, Finset.mem_union, Finset.mem_biUnion] at hx ⊢
  rcases hx with h | ⟨r, hr, h | h⟩
  · exact .inl (hAB h)
  · split_ifs at h with hE
    · exact .inr ⟨r, hST hr, .inl (ite_eq_left (hE.trans hAB) ▸ h)⟩
    · simp at h
  · split_ifs at h with hE
    · exact .inr ⟨r, hST hr, .inr (ite_eq_left (hE.trans hAB) ▸ h)⟩
    · simp at h

theorem revClosureAt_mono_reactions {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} (hST : S ⊆ T) :
    ∀ k, revClosureAt Q S k ⊆ revClosureAt Q T k
  | 0 => Finset.Subset.rfl
  | k + 1 => revClosureStep_mono Q hST (revClosureAt_mono_reactions Q hST k)

/-- The one-coordinate law underlying the set-Bernoulli catalysis sample. -/
noncomputable def ambientCoordLaw (p : I) : Measure Prop :=
  toNNReal p • Measure.dirac True + toNNReal (σ p) • Measure.dirac False

noncomputable instance ambientCoordLaw_isProbability (p : I) :
    IsProbabilityMeasure (ambientCoordLaw p) := by
  constructor; simp [ambientCoordLaw]

@[simp] theorem ambientCoordLaw_false (p : I) :
    ambientCoordLaw p {False} = toNNReal (σ p) := by simp [ambientCoordLaw]

@[simp] theorem ambientCoordLaw_true (p : I) :
    ambientCoordLaw p {True} = toNNReal p := by simp [ambientCoordLaw]

theorem probability_prop_eq_of_false (μ ν : Measure Prop)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ {False} = ν {False}) : μ = ν := by
  refine Measure.ext_of_singleton fun q => ?_
  by_cases hq : q
  · rw [propext (iff_true_intro hq), show ({True} : Set Prop) = {False}ᶜ by ext; simp,
      measure_compl (MeasurableSet.singleton _) (measure_ne_top _ _),
      measure_compl (MeasurableSet.singleton _) (measure_ne_top _ _), measure_univ, measure_univ, h]
  · simpa [propext (iff_false_intro hq)] using h

theorem pi_singleton {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    [∀ i, MeasurableSingletonClass (α i)] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, α i) : Measure.pi μ {f} = ∏ i, μ i {f i} := by
  rw [show ({f} : Set (∀ i, α i)) = Set.univ.pi fun i => {f i} by ext; simp [funext_iff],
    Measure.pi_pi]

noncomputable def fixedPoolParameter (p : I) (k : ℕ) : I := σ ((σ p)^k)

@[simp] theorem fixedPoolParameter_coe (p : I) (k : ℕ) :
    (fixedPoolParameter p k : ℝ) = 1-(1-(p : ℝ))^k := by
  simp [fixedPoolParameter]

/-- An infinite split-position environment. `openAt w k` records openness of
the ligation producing `w` at split position `k`. -/
abbrev InfiniteSplitEnvironment := List Bool → Nat → Prop

theorem revClosureAt_mono_stage {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) {i j : Nat} (hij : i ≤ j) :
    revClosureAt Q S i ⊆ revClosureAt Q S j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ _ _ ih => exact ih.trans Finset.subset_union_left

def nearFullPoolSize (n m : ℕ) : ℕ := (m-1)*(Fintype.card (Molecule n)/m)

theorem nearFullPoolSize_le (n m : ℕ) : nearFullPoolSize n m ≤ Fintype.card (Molecule n) :=
  (Nat.mul_le_mul_right _ (Nat.sub_le m 1)).trans (Nat.mul_div_le _ _)

/-- Big-endian code, matching the source's mixed-radix concatenation. -/
def binaryWordCode : List Bool → ℕ
  | [] => 0
  | b :: s => (if b then 2 ^ s.length else 0) + binaryWordCode s

theorem binaryWordCode_lt : ∀ s : List Bool, binaryWordCode s < 2 ^ s.length
  | [] => Nat.one_pos
  | b :: s => by have := binaryWordCode_lt s; cases b <;> simp [binaryWordCode, pow_succ] <;> omega

theorem binaryWordCode_append (s t : List Bool) :
    binaryWordCode (s ++ t) = binaryWordCode s * 2 ^ t.length + binaryWordCode t := by
  induction s with
  | nil => simp [binaryWordCode]
  | cons b _ ih => cases b <;> simp [binaryWordCode, ih, pow_add, Nat.add_mul, Nat.add_assoc]

def listWord (s : List Bool) : RAF.Polymer.Word s.length :=
  ⟨binaryWordCode s, binaryWordCode_lt s⟩

theorem binaryWordCode_append_div (s t : List Bool) :
    binaryWordCode (s ++ t) / 2 ^ t.length = binaryWordCode s := by
  rw [binaryWordCode_append, Nat.mul_comm, Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt (binaryWordCode_lt t), Nat.add_zero]

theorem binaryWordCode_append_mod (s t : List Bool) :
    binaryWordCode (s ++ t) % 2 ^ t.length = binaryWordCode t := by
  rw [binaryWordCode_append, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (binaryWordCode_lt t)]

/-- Length together with code uniquely determines the binary word. -/
theorem binaryWordCode_injective_length : ∀ {s t : List Bool},
    s.length = t.length → binaryWordCode s = binaryWordCode t → s = t
  | [], [], _, _ => rfl
  | b :: s, c :: t, hlen, hcode => by
    have hst : s.length = t.length := Nat.succ.inj hlen
    have := binaryWordCode_lt s; have := hst ▸ binaryWordCode_lt t
    cases b <;> cases c <;> simp [binaryWordCode, ← hst] at hcode
    · exact congrArg _ (binaryWordCode_injective_length hst hcode)
    · omega
    · omega
    · exact congrArg _ (binaryWordCode_injective_length hst (by omega))

theorem exists_binaryWordCode : ∀ m k : ℕ, k < 2 ^ m →
    ∃ s : List Bool, s.length = m ∧ binaryWordCode s = k
  | 0, k, hk => ⟨[], rfl, by dsimp [binaryWordCode]; omega⟩
  | m + 1, k, hk => by
    by_cases hlow : k < 2 ^ m
    · obtain ⟨s, hs, hc⟩ := exists_binaryWordCode m k hlow
      exact ⟨false :: s, congrArg Nat.succ hs, by simpa [binaryWordCode] using hc⟩
    · obtain ⟨s, hs, hc⟩ := exists_binaryWordCode m (k - 2 ^ m) (by rw [pow_succ] at hk; omega)
      exact ⟨true :: s, congrArg Nat.succ hs, by simp [binaryWordCode, hs, hc]; omega⟩

/-- A length-preserving bijection with the source's actual fixed-length word type. -/
noncomputable def binaryListWordEquiv (m : ℕ) :
    {s : List Bool // s.length = m} ≃ RAF.Polymer.Word m :=
  Equiv.ofBijective
    (fun s => ⟨binaryWordCode s.1, by simpa only [s.2] using binaryWordCode_lt s.1⟩)
    ⟨fun s t h => Subtype.ext (binaryWordCode_injective_length (s.2.trans t.2.symm) (congrArg Fin.val h)),
     fun k => let ⟨s, hs, hc⟩ := exists_binaryWordCode m k.1 k.2; ⟨⟨s, hs⟩, Fin.ext hc⟩⟩

noncomputable def moleculeWord {n : ℕ} (x : Molecule n) : List Bool :=
  ((binaryListWordEquiv (molLength x)).symm x.2).val

theorem moleculeWord_length {n : ℕ} (x : Molecule n) :
    (moleculeWord x).length = molLength x :=
  ((binaryListWordEquiv (molLength x)).symm x.2).property

theorem binaryWordCode_moleculeWord {n : ℕ} (x : Molecule n) :
    binaryWordCode (moleculeWord x) = x.2.val :=
  congrArg Fin.val ((binaryListWordEquiv (molLength x)).apply_symm_apply x.2)

/-- Decoding a literal source reaction gives exactly its recorded left substring. -/
theorem moleculeWord_reactionLeft {n : ℕ} (r : Reaction n) :
    moleculeWord (reactionLeft r) =
      (moleculeWord (reactionProduct r)).take (reactionLeftLength r) := by
  let s := moleculeWord (reactionProduct r)
  have hlen : s.length = reactionProductLength r := moleculeWord_length _
  have hadd := reaction_length_add r
  have hdrop : (s.drop (reactionLeftLength r)).length = reactionRightLength r := by rw [List.length_drop, hlen]; omega
  refine binaryWordCode_injective_length (by rw [moleculeWord_length, molLength_reactionLeft, List.length_take, hlen]; omega) ?_
  have hc := binaryWordCode_append_div (s.take (reactionLeftLength r)) (s.drop (reactionLeftLength r))
  rw [List.take_append_drop, hdrop, binaryWordCode_moleculeWord] at hc
  exact (binaryWordCode_moleculeWord _).trans hc

/-- The right endpoint is exactly the complementary source substring. -/
theorem moleculeWord_reactionRight {n : ℕ} (r : Reaction n) :
    moleculeWord (reactionRight r) =
      (moleculeWord (reactionProduct r)).drop (reactionLeftLength r) := by
  let s := moleculeWord (reactionProduct r)
  have hdrop : (s.drop (reactionLeftLength r)).length = reactionRightLength r := by
    rw [List.length_drop, moleculeWord_length, molLength_reactionProduct]; have := reaction_length_add r; omega
  refine binaryWordCode_injective_length ((moleculeWord_length _).trans ((molLength_reactionRight r).trans hdrop.symm)) ?_
  have hc := binaryWordCode_append_mod (s.take (reactionLeftLength r)) (s.drop (reactionLeftLength r))
  rw [List.take_append_drop, hdrop, binaryWordCode_moleculeWord] at hc
  exact (binaryWordCode_moleculeWord _).trans hc

def sourceSplitReaction {n : ℕ} (x : Molecule n) (k : ℕ) (_ : 0 < k) (hkm : k < molLength x) : Reaction n :=
  ⟨x.1, x.2, ⟨k - 1, by unfold molLength at hkm; omega⟩⟩

@[simp] theorem sourceSplitReaction_leftLength {n : ℕ} (x : Molecule n) (k : ℕ)
    (hk : 0 < k) (hkm : k < molLength x) :
    reactionLeftLength (sourceSplitReaction x k hk hkm) = k := Nat.sub_add_cancel hk

def sourceWordMolecule {N : ℕ} (s : List Bool) (hs : 0 < s.length) (hN : s.length ≤ N) : Molecule N :=
  moleculeOfCode hs hN (listWord s)

@[simp] theorem sourceWordMolecule_length {N : ℕ} (s : List Bool) (hs : 0 < s.length) (hN : s.length ≤ N) :
    molLength (sourceWordMolecule s hs hN) = s.length := by simp [sourceWordMolecule]

@[simp] theorem sourceWordMolecule_word {N : ℕ} (s : List Bool) (hs : 0 < s.length) (hN : s.length ≤ N) :
    moleculeWord (sourceWordMolecule s hs hN) = s :=
  binaryWordCode_injective_length ((moleculeWord_length _).trans (sourceWordMolecule_length _ _ _))
    (binaryWordCode_moleculeWord _)

open Classical

theorem iid_prefix_determined_measurable {Z : Type*} (P : Finset Z) (E : Set (Z → Prop))
    (hE : ∀ ω η, (∀ z ∈ P, ω z = η z) → (ω ∈ E ↔ η ∈ E)) :
    ∃ e : (P → Prop) → Prop, E = {ω | e fun z => ω z.1} :=
  ⟨fun η => (fun z => if h : z ∈ P then η ⟨z, h⟩ else False) ∈ E,
    Set.ext fun _ => hE _ _ fun _ hz => by simp [hz]⟩

theorem iid_prefix_failure_measure {Z : Type*} (a : I) (P T : Finset Z) (hPT : Disjoint P T)
    (E : Set (Z → Prop)) (hE : ∀ ω η, (∀ z ∈ P, ω z = η z) → (ω ∈ E ↔ η ∈ E)) :
    Measure.infinitePi (fun _ : Z => ambientCoordLaw a) (E ∩ {ω | ¬ ∀ z ∈ T, ω z}) =
      Measure.infinitePi (fun _ : Z => ambientCoordLaw a) E * (1 - (toNNReal a : ENNReal) ^ T.card) := by
  let μ := Measure.infinitePi fun _ : Z => ambientCoordLaw a
  obtain ⟨e, rfl⟩ := iid_prefix_determined_measurable P E hE
  have hi : iIndepFun (fun z (ω : Z → Prop) => ω z) μ := iIndepFun_infinitePi fun _ => measurable_id
  have hp := ((hi.indepFun_finset P T hPT fun z => measurable_pi_apply z).comp
    (measurable_of_finite e) (measurable_of_finite fun η : T → Prop => ¬ ∀ z, η z)).measure_inter_preimage_eq_mul
    {True} {True} (MeasurableSet.singleton True) (MeasurableSet.singleton True)
  have hm : MeasurableSet {ω : Z → Prop | ∀ z ∈ T, ω z} := by
    rw [show {ω : Z → Prop | ∀ z ∈ T, ω z} = ⋂ z ∈ T, (fun ω => ω z) ⁻¹' {True} by ext; simp]
    exact MeasurableSet.biInter T.countable_toSet fun z _ => (MeasurableSet.singleton True).preimage (measurable_pi_apply z)
  have hfail : μ {ω | ¬ ∀ z ∈ T, ω z} = 1 - (toNNReal a : ENNReal) ^ T.card := by
    change μ ({ω | ∀ z ∈ T, ω z}ᶜ) = _
    rw [measure_compl hm (measure_ne_top _ _), measure_univ,
      show {ω : Z → Prop | ∀ z ∈ T, ω z} = (T : Set Z).pi fun _ => ({True} : Set Prop) by ext; simp,
      Measure.infinitePi_pi _ fun _ _ => MeasurableSet.singleton True]; simp
  simp only [Function.comp_def, Subtype.forall, Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true] at hp
  rwa [hfail] at hp

def sprinklingParameter (a b : I) : I := σ ((σ a) * (σ b))

theorem sprinklingParameter_value (a b : I) :
    (sprinklingParameter a b : ℝ) = (a : ℝ) + (1-(a : ℝ))*(b : ℝ) := by
  change 1-((1-(a : ℝ))*(1-(b : ℝ))) = _; ring

/-- Exact law of the union of two independent Bernoulli coordinates. -/
theorem ambientCoordLaw_union (a b : I) :
    ((ambientCoordLaw a).prod (ambientCoordLaw b)).map (fun p : Prop × Prop => p.1 ∨ p.2) =
      ambientCoordLaw (sprinklingParameter a b) := by
  have : IsProbabilityMeasure (((ambientCoordLaw a).prod (ambientCoordLaw b)).map
      fun p : Prop × Prop => p.1 ∨ p.2) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_of_finite _).aemeasurable).2 inferInstance
  apply probability_prop_eq_of_false
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton False),
    show (fun p : Prop × Prop => p.1 ∨ p.2) ⁻¹' {False} = ({False} : Set Prop) ×ˢ {False} by
      ext p; simp [Prod.ext_iff],
    Measure.prod_prod]
  simp [sprinklingParameter, ← ENNReal.coe_mul]; rfl

theorem exists_sprinkling_increment {a c : I} (hac : a ≤ c) :
    ∃ b : I, sprinklingParameter a b = c := by
  by_cases he : a = c
  · exact ⟨0, Subtype.ext (by simp [sprinklingParameter_value, he])⟩
  · have hlt : (a : ℝ) < c := lt_of_le_of_ne (a := a) hac he
    have hd : 0 < 1 - (a : ℝ) := by linarith [c.2.2]
    refine ⟨⟨((c : ℝ) - a) / (1 - a), div_nonneg (by linarith) hd.le, (div_le_one hd).mpr (by linarith [c.2.2])⟩,
      Subtype.ext ?_⟩
    rw [sprinklingParameter_value]; dsimp; field_simp; ring

/-- Finite inhomogeneous Bernoulli product laws are ordered on increasing events. -/
theorem product_increasing_mono {J : Type*} [Fintype J]
    (a c : J → I) (hac : ∀ j, a j ≤ c j)
    (E : (J → Prop) → Prop) (hE : Monotone E) :
    Measure.pi (fun j => ambientCoordLaw (a j)) {ω | E ω} ≤
      Measure.pi (fun j => ambientCoordLaw (c j)) {ω | E ω} := by
  choose b hb using fun j => exists_sprinkling_increment (hac j)
  let μ : J → Measure (Prop × Prop) := fun j => (ambientCoordLaw (a j)).prod (ambientCoordLaw (b j))
  have : ∀ j, IsProbabilityMeasure (μ j) := fun _ => inferInstance
  have hleft : (Measure.pi μ).map (fun ω j => (ω j).1) = Measure.pi fun j => ambientCoordLaw (a j) := by
    rw [Measure.pi_map_pi (f := fun _ (z : Prop × Prop) => z.1) fun _ => measurable_fst.aemeasurable]
    simp [μ]
  have hunion : (Measure.pi μ).map (fun ω j => (ω j).1 ∨ (ω j).2) = Measure.pi fun j => ambientCoordLaw (c j) := by
    rw [Measure.pi_map_pi (f := fun _ (z : Prop × Prop) => z.1 ∨ z.2) fun _ => (measurable_of_finite _).aemeasurable]
    simp [μ, ambientCoordLaw_union, hb]
  rw [← hleft, ← hunion,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  exact measure_mono fun _ => hE fun _ => Or.inl

theorem product_decreasing_mono {J : Type*} [Fintype J]
    (a c : J → I) (hac : ∀ j, a j ≤ c j)
    (E : (J → Prop) → Prop) (hE : Antitone E) :
    Measure.pi (fun j => ambientCoordLaw (c j)) {ω | E ω} ≤
      Measure.pi (fun j => ambientCoordLaw (a j)) {ω | E ω} := by
  have hc (q : J → I) : Measure.pi (fun j => ambientCoordLaw (q j)) {ω | E ω} =
      1 - Measure.pi (fun j => ambientCoordLaw (q j)) {ω | ¬ E ω} := by
    rw [show {ω | E ω} = {ω | ¬ E ω}ᶜ by ext; simp,
      measure_compl (Set.toFinite _).measurableSet (measure_ne_top _ _), measure_univ]
  rw [hc a, hc c]
  exact tsub_le_tsub_left (product_increasing_mono a c hac (fun ω => ¬ E ω) fun _ _ h hx hy => hx (hE h hy)) 1

/-- The ordinary literal reversible closure, with arbitrary temporary food cutoff. -/
noncomputable def temporaryReactionClosure {N : ℕ} (L : ℕ) (S : Finset (Reaction N)) :
    Finset (Molecule N) := Finset.univ.filter (fun x => ∃ k,
      x ∈ revClosureAt (binaryPolymerCRS N L) S k)

@[simp] theorem mem_temporaryReactionClosure {N L : ℕ} (S : Finset (Reaction N))
    (x : Molecule N) : x ∈ temporaryReactionClosure L S ↔
      ∃ k, x ∈ revClosureAt (binaryPolymerCRS N L) S k := by
  simp [temporaryReactionClosure]

theorem temporaryReactionClosure_mono {N L : ℕ} {S T : Finset (Reaction N)}
    (hST : S ⊆ T) : temporaryReactionClosure L S ⊆ temporaryReactionClosure L T :=
  fun x hx => let ⟨k, hk⟩ := (mem_temporaryReactionClosure S x).mp hx
    (mem_temporaryReactionClosure T x).mpr ⟨k, revClosureAt_mono_reactions _ hST k hk⟩

theorem temporaryReactionClosure_food {N L : ℕ} (S : Finset (Reaction N))
    (x : Molecule N) (hx : molLength x ≤ L) : x ∈ temporaryReactionClosure L S :=
  (mem_temporaryReactionClosure S x).mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩

theorem temporaryReactionClosure_ligation {N L : ℕ} (S : Finset (Reaction N))
    (r : Reaction N) (hr : r ∈ S)
    (hl : reactionLeft r ∈ temporaryReactionClosure L S)
    (hh : reactionRight r ∈ temporaryReactionClosure L S) :
    reactionProduct r ∈ temporaryReactionClosure L S := by
  obtain ⟨kl, hkl⟩ := (mem_temporaryReactionClosure S _).mp hl
  obtain ⟨kr, hkr⟩ := (mem_temporaryReactionClosure S _).mp hh
  have hen : RevEnabledLhs (binaryPolymerCRS N L) (revClosureAt (binaryPolymerCRS N L) S (max kl kr)) r :=
    Finset.insert_subset (revClosureAt_mono_stage _ S (Nat.le_max_left _ _) hkl)
      (Finset.singleton_subset_iff.mpr (revClosureAt_mono_stage _ S (Nat.le_max_right _ _) hkr))
  exact (mem_temporaryReactionClosure S _).mpr ⟨max kl kr + 1,
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_union_left _ (ite_eq_left hen ▸ Finset.mem_singleton_self _)⟩)⟩

theorem temporaryReactionClosure_cleavage {N L : ℕ} (S : Finset (Reaction N))
    (r : Reaction N) (hr : r ∈ S)
    (hp : reactionProduct r ∈ temporaryReactionClosure L S) :
    reactionLeft r ∈ temporaryReactionClosure L S ∧
      reactionRight r ∈ temporaryReactionClosure L S := by
  obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure S _).mp hp
  have hen : RevEnabledRhs (binaryPolymerCRS N L) (revClosureAt (binaryPolymerCRS N L) S k) r := by
    simpa [RevEnabledRhs, binaryPolymerCRS] using hk
  have hadd {x} (hx : x ∈ ({reactionLeft r, reactionRight r} : Finset _)) : x ∈ temporaryReactionClosure L S :=
    (mem_temporaryReactionClosure S _).mpr ⟨k + 1,
      Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_union_right _ (ite_eq_left hen ▸ hx)⟩)⟩
  exact ⟨hadd (by simp), hadd (by simp)⟩

theorem moleculeWord_injective {N : ℕ} : Function.Injective (@moleculeWord N) := by
  rintro ⟨kx, vx⟩ ⟨ky, vy⟩ h
  have hh := (moleculeWord_length _).symm.trans ((congrArg List.length h).trans (moleculeWord_length _))
  obtain rfl : kx = ky := Fin.ext (by unfold molLength at hh; dsimp at hh; omega)
  exact congrArg (Sigma.mk _) (Fin.ext ((binaryWordCode_moleculeWord _).symm.trans
    ((congrArg binaryWordCode h).trans (binaryWordCode_moleculeWord _))))

theorem temporaryReactionClosure_induction {N L : ℕ} (S : Finset (Reaction N))
    (P : Molecule N → Prop)
    (hfood : ∀ x, molLength x ≤ L → P x)
    (hlig : ∀ r ∈ S, P (reactionLeft r) → P (reactionRight r) → P (reactionProduct r))
    (hcleave : ∀ r ∈ S, P (reactionProduct r) → P (reactionLeft r) ∧ P (reactionRight r))
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure L S) : P x := by
  obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure S x).mp hx
  suffices ∀ m, ∀ y ∈ revClosureAt (binaryPolymerCRS N L) S m, P y from this k x hk
  intro m; induction m with
  | zero => exact fun y hy => hfood y (by simpa [revClosureAt, binaryPolymerCRS, binaryFood] using hy)
  | succ m ih =>
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact ih y hy
    · obtain ⟨r, hr, hy⟩ := Finset.mem_biUnion.mp hy
      rcases Finset.mem_union.mp hy with hy | hy
      · split_ifs at hy with hen
        · obtain rfl : y = reactionProduct r := Finset.mem_singleton.mp hy
          exact hlig r hr (ih _ (hen (by simp [binaryPolymerCRS]))) (ih _ (hen (by simp [binaryPolymerCRS])))
        · simp at hy
      · split_ifs at hy with hen
        · have hh := hcleave r hr (ih _ (hen (Finset.mem_singleton_self _)))
          rcases (by simpa [binaryPolymerCRS] using hy : y = _ ∨ y = _) with rfl | rfl <;> [exact hh.1; exact hh.2]
        · simp at hy

theorem temporaryReactionClosure_seed_transfer {N L K : ℕ}
    {S T : Finset (Reaction N)} (hST : S ⊆ T)
    (hseed : ∀ x, molLength x ≤ L → x ∈ temporaryReactionClosure K T) :
    temporaryReactionClosure L S ⊆ temporaryReactionClosure K T :=
  fun x => temporaryReactionClosure_induction S _ hseed
    (fun r hr => temporaryReactionClosure_ligation T r (hST hr))
    (fun r hr => temporaryReactionClosure_cleavage T r (hST hr)) x

theorem source_append_split {N : ℕ} (u v : List Bool)
    (hu : 0 < u.length) (hv : 0 < v.length) (hN : u.length + v.length ≤ N) :
    ∃ r : Reaction N,
      moleculeWord (reactionLeft r) = u ∧
      moleculeWord (reactionRight r) = v ∧
      moleculeWord (reactionProduct r) = u ++ v :=
  ⟨sourceSplitReaction (sourceWordMolecule (u ++ v) (by simp; omega) (by simpa using hN))
      u.length hu (by simp; omega),
    by simp [moleculeWord_reactionLeft, sourceSplitReaction, reactionProduct, reactionLeftLength, Nat.sub_add_cancel hu],
    by simp [moleculeWord_reactionRight, sourceSplitReaction, reactionProduct, reactionLeftLength, Nat.sub_add_cancel hu],
    by simp [sourceSplitReaction, reactionProduct]⟩

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
  | nil => exact ⟨∅, by simp, by simp, fun _ _ x hx he => ⟨x, hx, by simpa using he⟩⟩
  | append_singleton v b ih =>
    simp only [List.length_append, List.length_singleton] at hN ⊢
    obtain ⟨S, hcard, hband, hgen⟩ := ih (by omega)
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) (w ++ v) [b]
      (by simp; omega) (by simp) (by simpa [Nat.add_assoc] using hN)
    have hlen : molLength (reactionProduct r) = w.length + v.length + 1 := by
      rw [← moleculeWord_length, hp]; simp [Nat.add_assoc]
    refine ⟨insert r S, (Finset.card_insert_le r S).trans (by omega), fun q hq => ?_, fun T hST x hx he => ?_⟩
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · omega
      · have := hband q hq; omega
    · obtain ⟨y, hy, hey⟩ := hgen T (Finset.subset_insert r S |>.trans hST) x hx he
      refine ⟨reactionProduct r, temporaryReactionClosure_ligation T r
        (hST (Finset.mem_insert_self _ _)) (moleculeWord_injective (hl.trans hey.symm) ▸ hy)
        (temporaryReactionClosure_food T _ (by rw [← moleculeWord_length, hr]; simp)), ?_⟩
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
  refine ⟨insert r S, (Finset.card_insert_le r S).trans (by omega), fun q hq => ?_, fun T hST x hx he => ?_⟩
  · rcases Finset.mem_insert.mp hq with rfl | hq <;> [omega; exact hb q hq]
  · obtain ⟨y, hy, hey⟩ := hg T (Finset.subset_insert r S |>.trans hST) x hx he
    exact ⟨reactionRight r, (temporaryReactionClosure_cleavage T r
      (hST (Finset.mem_insert_self _ _)) (moleculeWord_injective (hp.trans hey.symm) ▸ hy)).2, hr⟩

noncomputable def finiteInitialSegment (X : Type*) [Fintype X] (k : ℕ) : Finset X :=
  (Finset.univ.filter fun i : Fin (Fintype.card X) => i.val < k).map (Fintype.equivFin X).symm.toEmbedding

theorem finiteInitialSegment_mono (X : Type*) [Fintype X] : Monotone (finiteInitialSegment X) :=
  fun _ _ hab => Finset.map_subset_map.mpr fun _ hi =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.trans_le hab⟩

theorem card_finiteInitialSegment (X : Type*) [Fintype X] (k : ℕ) (hk : k ≤ Fintype.card X) :
    (finiteInitialSegment X k).card = k := by
  rw [finiteInitialSegment, Finset.card_map, Fin.card_filter_val_lt, min_eq_right hk]

def peelingActiveAt {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X) : ℕ → Finset R
  | 0 => response Finset.univ
  | t + 1 => response (closure (peelingActiveAt response closure t))

def prescribedPoolAt {X R : Type*} [Fintype X]
    (closure : Finset R → Finset X) (history : ℕ → Finset R) : ℕ → Finset X
  | 0 => Finset.univ
  | t + 1 => closure (history t)

theorem peeling_history_iff {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X)
    (history : ℕ → Finset R) (T : ℕ) :
    (∀ t ≤ T, peelingActiveAt response closure t = history t) ↔
      ∀ t ≤ T, response (prescribedPoolAt closure history t) = history t := by
  refine ⟨fun h t ht => ?_, fun h t => ?_⟩
  · cases t with
    | zero => exact h 0 ht
    | succ t => simpa [peelingActiveAt, h t (by omega), prescribedPoolAt] using h (t + 1) ht
  · induction t with
    | zero => exact h 0
    | succ t ih => exact fun ht => by simpa [peelingActiveAt, ih (by omega), prescribedPoolAt] using h (t + 1) ht

theorem peelingActiveAt_antitone {X R : Type*} [Fintype X]
    (response : Finset X → Finset R) (closure : Finset R → Finset X)
    (hresponse : Monotone response) (hclosure : Monotone closure) :
    Antitone (peelingActiveAt response closure) :=
  antitone_nat_of_succ_le fun t => by
    induction t with
    | zero => exact hresponse (Finset.subset_univ _)
    | succ _ ih => exact hresponse (hclosure ih)

theorem peelingActiveAt_stable_card {X R : Type*} [Fintype X] [Fintype R]
    (response : Finset X → Finset R) (closure : Finset R → Finset X)
    (hr : Monotone response) (hc : Monotone closure) :
    peelingActiveAt response closure (Fintype.card R + 1) =
      peelingActiveAt response closure (Fintype.card R) := by
  have hanti := peelingActiveAt_antitone response closure hr hc
  have hor (t : ℕ) : (peelingActiveAt response closure t).card + t ≤ Fintype.card R ∨
      peelingActiveAt response closure (t + 1) = peelingActiveAt response closure t := by
    induction t with
    | zero => exact .inl (Finset.card_le_univ _)
    | succ t ih =>
      by_cases h : peelingActiveAt response closure (t + 1) = peelingActiveAt response closure t
      · exact .inr (by change response (closure _) = _; rwa [h])
      · have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hanti (by omega : t ≤ t + 1), h⟩)
        have := ih.resolve_right h; exact .inl (by omega)
  rcases hor (Fintype.card R) with hb | he
  · exact Finset.Subset.antisymm (hanti (Nat.le_succ _))
      ((Finset.card_eq_zero (s := peelingActiveAt response closure (Fintype.card R))).mp (by omega) ▸ Finset.empty_subset _)
  · exact he

end HordijkSteelThreshold

namespace RAFEmergenceApprox.Generic
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open scoped ENNReal

variable {X R : Type*} [Fintype X] [Fintype R]

noncomputable def colLaw (X : Type*) [Fintype X] (p : I) : Measure (X → Prop) :=
  Measure.pi (fun _ : X => ambientCoordLaw p)

instance colLaw_probability (p : I) : IsProbabilityMeasure (colLaw X p) := by
  unfold colLaw
  infer_instance

noncomputable def law (p : R → I) : Measure (R → X → Prop) :=
  Measure.pi (fun r => colLaw X (p r))

instance law_probability (p : R → I) : IsProbabilityMeasure (law (X := X) p) := by
  unfold law
  infer_instance

def catalystPoolOpen (ω : R → X → Prop) (C : Finset X) (r : R) : Prop := ∃ x ∈ C, ω r x

noncomputable def catalystActive (ω : R → X → Prop) (C : Finset X) : Finset R :=
  Finset.univ.filter (catalystPoolOpen ω C)

omit [Fintype X] in
@[simp] theorem mem_catalystActive (ω : R → X → Prop) (C : Finset X) (r : R) :
    r ∈ catalystActive ω C ↔ catalystPoolOpen ω C r := by simp [catalystActive]

omit [Fintype X] in
theorem catalystActive_mono (ω : R → X → Prop) : Monotone (catalystActive ω) :=
  fun _ _ h _ hr => let ⟨x, hx, hω⟩ := (mem_catalystActive ω _ _).mp hr
    (mem_catalystActive ω _ _).mpr ⟨x, h hx, hω⟩

theorem pool_col_map (p : I) (C : Finset X) :
    (colLaw X p).map (fun v => ∃ x ∈ C, v x) = ambientCoordLaw (fixedPoolParameter p C.card) := by
  apply probability_prop_eq_of_false
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton _),
    show (fun v : X → Prop => ∃ x ∈ C, v x) ⁻¹' {False} = Set.univ.pi fun x => if x ∈ C then {False} else Set.univ by
      ext; simp,
    colLaw, Measure.pi_pi, ambientCoordLaw_false]
  simp [apply_ite (ambientCoordLaw p), fixedPoolParameter, ← ENNReal.coe_pow]
  exact NNReal.eq (by simp)

theorem pool_statistic (p : I) (C : Finset X) (stat : Finset R → Prop) :
    law (X := X) (fun _ : R => p) {ω | stat (catalystActive ω C)} =
      Measure.pi (fun _ : R => ambientCoordLaw (fixedPoolParameter p C.card))
        {q | stat (Finset.univ.filter q)} := by
  have hpm : (law (X := X) fun _ : R => p).map (fun ω r => ∃ x ∈ C, ω r x) =
      Measure.pi fun _ : R => ambientCoordLaw (fixedPoolParameter p C.card) := by
    rw [law, Measure.pi_map_pi (f := fun (_ : R) (v : X → Prop) => ∃ x ∈ C, v x)
      fun _ => (measurable_of_finite _).aemeasurable]
    simp_rw [pool_col_map]
  rw [← hpm, Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]; rfl

private theorem chain_perm (P Q : ℕ → Finset X) (T : ℕ)
    (hP : Antitone P) (hQ : Antitone Q) (hc : ∀ t ≤ T, (P t).card = (Q t).card) :
    ∃ e : X ≃ X, ∀ x, ∀ t ≤ T, e x ∈ Q t ↔ x ∈ P t := by
  let dep (C : ℕ → Finset X) (x : X) : ℕ := ((Finset.range (T + 1)).filter (x ∈ C ·)).card
  have hmem (C : ℕ → Finset X) (hC : Antitone C) (x : X) (t : ℕ) (ht : t ≤ T) :
      x ∈ C t ↔ t + 1 ≤ dep C x := by
    refine ⟨fun hx => ?_, fun hle => ?_⟩
    · simpa using Finset.card_le_card (s := Finset.range (t + 1)) fun s hs =>
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hs; omega),
          hC (by have := Finset.mem_range.mp hs; omega) hx⟩
    · by_contra hx
      have := Finset.card_le_card (s := (Finset.range (T + 1)).filter (x ∈ C ·)) (t := Finset.range t) fun s hs => by
        obtain ⟨_, hxs⟩ := Finset.mem_filter.mp hs
        exact Finset.mem_range.mpr (by by_contra; exact hx (hC (by omega) hxs))
      simp at this; dsimp [dep] at hle; omega
  have hge (C : ℕ → Finset X) (hC : Antitone C) (m : ℕ) :
      (Finset.univ.filter fun x => m ≤ dep C x).card =
        if m = 0 then Fintype.card X else if m ≤ T + 1 then (C (m - 1)).card else 0 := by
    split_ifs with hm0
    · subst hm0; simp
    · congr 1; ext x; simp [hmem C hC x (m - 1) (by omega), show m - 1 + 1 = m by omega]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro x _
      have := (Finset.card_le_card (Finset.filter_subset (x ∈ C ·) (Finset.range (T + 1)))).trans_eq (Finset.card_range _)
      dsimp [dep]; omega
  have heq (k : ℕ) : (Finset.univ.filter fun x => k ≤ dep P x).card = (Finset.univ.filter fun x => k ≤ dep Q x).card := by
    rw [hge P hP, hge Q hQ]; split_ifs <;> [rfl; exact hc _ (by omega); rfl]
  have hfib (m : ℕ) : Fintype.card {x // dep P x = m} = Fintype.card {x // dep Q x = m} := by
    have hsp (C : ℕ → Finset X) :
        (Finset.univ.filter fun x => m + 1 ≤ dep C x).card + (Finset.univ.filter fun x => dep C x = m).card =
          (Finset.univ.filter fun x => m ≤ dep C x).card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun x h1 h2 => by simp at h1 h2; omega)]
      congr 1; ext x; simp; omega
    simp only [Fintype.card_subtype]; have := hsp P; have := hsp Q; have := heq m; have := heq (m + 1); omega
  refine ⟨(Equiv.sigmaFiberEquiv (dep P)).symm.trans
    ((Equiv.sigmaCongrRight fun m => Fintype.equivOfCardEq (hfib m)).trans (Equiv.sigmaFiberEquiv (dep Q))),
    fun x t ht => ?_⟩
  rw [hmem Q hQ _ t ht, hmem P hP _ t ht]
  exact Iff.of_eq (congrArg (t + 1 ≤ ·) (Fintype.equivOfCardEq (hfib (dep P x)) ⟨x, rfl⟩).2)

private theorem peeling_map_eq (p : R → I) (closure : Finset R → Finset X) (hclosure : Monotone closure) (T : ℕ) :
    (law (X := X) p).map (fun ω (t : Fin (T + 1)) => peelingActiveAt (catalystActive ω) closure t.1) =
    (law (X := X) p).map (fun ω (t : Fin (T + 1)) => peelingActiveAt
      (fun C => catalystActive ω (finiteInitialSegment X C.card)) closure t.1) := by
  refine Measure.ext_of_singleton fun H => ?_
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton H),
    Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton H)]
  let Hext (t : ℕ) : Finset R := if h : t ≤ T then H ⟨t, Nat.lt_succ_of_le h⟩ else ∅
  have hev (resp : (R → X → Prop) → Finset X → Finset R) :
      (fun ω : R → X → Prop => fun t : Fin (T + 1) => peelingActiveAt (resp ω) closure t.1) ⁻¹' {H} =
        {ω | ∀ t ≤ T, peelingActiveAt (resp ω) closure t = Hext t} := by
    ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, funext_iff, Fin.forall_iff, Nat.lt_succ_iff]
    exact forall₂_congr fun t ht => by simp [Hext, ht]
  rw [hev, hev]
  by_cases hanti : Antitone Hext
  · let P := prescribedPoolAt closure Hext
    let Q (t : ℕ) := finiteInitialSegment X (P t).card
    have hP : Antitone P := antitone_nat_of_succ_le fun | 0 => Finset.subset_univ _ | t + 1 => hclosure (hanti (Nat.le_succ t))
    have hQ : Antitone Q := fun _ _ hab => finiteInitialSegment_mono X (Finset.card_le_card (hP hab))
    obtain ⟨e, he⟩ := chain_perm P Q T hP hQ fun _ _ => (card_finiteInitialSegment X _ (Finset.card_le_univ _)).symm
    have hperm : (law (X := X) p).map (fun ω r x => ω r (e x)) = law p := by
      rw [law, Measure.pi_map_pi (f := fun _ (v : X → Prop) x => v (e x)) fun _ => (measurable_of_finite _).aemeasurable]
      congr 1; funext r
      exact (measurePreserving_piCongrLeft (fun _ : X => ambientCoordLaw (p r)) e).symm.map_eq
    conv_lhs => rw [← hperm]
    rw [Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
    congr 1; ext ω
    change (∀ t ≤ T, peelingActiveAt (catalystActive fun r x => ω r (e x)) closure t = Hext t) ↔
      ∀ t ≤ T, peelingActiveAt (fun C => catalystActive ω (finiteInitialSegment X C.card)) closure t = Hext t
    rw [peeling_history_iff, peeling_history_iff]
    refine forall₂_congr fun t ht => ?_
    rw [show catalystActive (fun r x => ω r (e x)) (P t) = catalystActive ω (Q t) by
      ext r; simp only [mem_catalystActive, catalystPoolOpen]
      exact ⟨fun ⟨x, hx, hω⟩ => ⟨e x, (he x t ht).mpr hx, hω⟩,
        fun ⟨y, hy, hω⟩ => ⟨e.symm y, (he (e.symm y) t ht).mp (by simpa using hy), by simpa using hω⟩⟩]
  · have hemp (resp : (R → X → Prop) → Finset X → Finset R) (hm : ∀ ω, Monotone (resp ω)) :
        {ω : R → X → Prop | ∀ t ≤ T, peelingActiveAt (resp ω) closure t = Hext t} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun ω h => hanti fun a b hab => by
        by_cases hb : b ≤ T
        · have ha : a ≤ T := hab.trans hb
          simpa [Hext, ha, hb, ← h a ha, ← h b hb] using peelingActiveAt_antitone _ closure (hm ω) hclosure hab
        · simp [Hext, hb]
    rw [hemp _ catalystActive_mono,
      hemp _ fun ω _ _ h => catalystActive_mono ω (finiteInitialSegment_mono X (Finset.card_le_card h))]

theorem mass_ge_static (p : I) (closure : Finset R → Finset X) (hclosure : Monotone closure) (k T : ℕ) :
    Measure.pi (fun _ : R => ambientCoordLaw (fixedPoolParameter p (finiteInitialSegment X k).card))
      {q | k ≤ (closure (Finset.univ.filter q)).card} ≤
    law (X := X) (fun _ : R => p) {ω | k ≤ (closure (peelingActiveAt (catalystActive ω) closure T)).card} := by
  rw [← pool_statistic p (finiteInitialSegment X k) fun A => k ≤ (closure A).card]
  let E : Set (Fin (T + 1) → Finset R) := {H | k ≤ (closure (H ⟨T, Nat.lt_succ_self T⟩)).card}
  have he := congrArg (· E) (peeling_map_eq (fun _ : R => p) closure hclosure T)
  rw [Measure.map_apply (measurable_of_finite _) (Set.toFinite E).measurableSet,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite E).measurableSet] at he
  simp only [E, Set.preimage, Set.mem_ofPred_eq] at he; rw [he]; clear E he
  refine measure_mono fun ω (hω : k ≤ _) => hω.trans (Finset.card_le_card (hclosure ?_))
  have hO : Monotone fun j => catalystActive ω (finiteInitialSegment X j) :=
    (catalystActive_mono ω).comp (finiteInitialSegment_mono X)
  induction T with
  | zero => simpa [peelingActiveAt] using hO (hω.trans (Finset.card_le_univ _))
  | succ _ ih => exact hO (hω.trans (Finset.card_le_card (hclosure ih)))

theorem coordinate_probability (p : I) (r : R) (x : X) :
    law (X := X) (fun _ : R => p) {ω | ω r x} = (toNNReal p : ENNReal) := by
  have hr := congrArg (· {v : X → Prop | v x}) (measurePreserving_eval (fun _ : R => colLaw X p) r).map_eq
  have hx := congrArg (· ({True} : Set Prop)) (measurePreserving_eval (fun _ : X => ambientCoordLaw p) x).map_eq
  rw [Measure.map_apply (measurable_pi_apply _) (Set.toFinite _).measurableSet] at hr
  rw [Measure.map_apply (measurable_pi_apply _) (MeasurableSet.singleton _)] at hx
  exact hr.trans (by simpa [colLaw, ambientCoordLaw] using hx)

end RAFEmergenceApprox.Generic

namespace RAFEmergenceApprox
open RAF.Polymer RAF.Concrete HordijkSteelThreshold unitInterval

theorem catalysisP_covers_probability (n : ℕ) (hn : 2 ≤ n) (p : I) :
    catalysisP n ((p : ℝ) * Fintype.card (Reaction n) / n) = p := by
  have hj : 0 < Fintype.card (Reaction n) := by rw [card_reactions_exact hn]; omega
  apply Subtype.ext
  have he : rawCatalysisP n ((p : ℝ) * Fintype.card (Reaction n) / n) = p := by
    unfold rawCatalysisP; field_simp
  change min 1 (max 0 (rawCatalysisP n _)) = (p : ℝ)
  rw [he, max_eq_right p.2.1, min_eq_right p.2.2]

end RAFEmergenceApprox

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory unitInterval RAF RAF.Polymer RAF.Concrete RAFEmergenceApprox.Generic
open scoped ENNReal

/-- Reindex actual food molecules into the finite cutoff universe. -/
theorem binaryFood_card_le_cutoff (n L : ℕ) :
    (binaryFood n L).card ≤ Fintype.card (Molecule L) := by
  let f : ↥(binaryFood n L) → Molecule L := fun x =>
    ⟨⟨x.1.1.val, by have h := (Finset.mem_filter.mp x.2).2; dsimp [molLength] at h; omega⟩, x.1.2⟩
  simpa using Fintype.card_le_of_injective f fun ⟨⟨ai, aw⟩, _⟩ ⟨⟨bi, bw⟩, _⟩ h => by
    apply Subtype.ext
    obtain rfl : ai = bi := Fin.ext (congrArg (·.1.val) h)
    exact congrArg (Sigma.mk _) (Fin.ext (congrArg (·.2.val) h))

section UsableCRS
variable {M R : Type*} [Fintype M] [DecidableEq M]

noncomputable def crsClosure (Q : ReversibleCRS M R) (S : Finset R) : Finset M :=
  Finset.univ.filter fun x => ∃ k, x ∈ revClosureAt Q S k

theorem crsClosure_mono (Q : ReversibleCRS M R) : Monotone (crsClosure Q) :=
  fun _ _ hST _ hx => let ⟨_, k, hk⟩ := Finset.mem_filter.mp hx
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, revClosureAt_mono_reactions Q hST k hk⟩

noncomputable def usableCRS (Q : ReversibleCRS M R) (A : Finset R) : Finset R :=
  A.filter fun r => Q.lhs r ∪ Q.rhs r ⊆ crsClosure Q A

private theorem subset_revClosureAt_of_crsClosure {Q : ReversibleCRS M R} {S : Finset R} {B : Finset M}
    (hB : B ⊆ crsClosure Q S) : ∃ k, B ⊆ revClosureAt Q S k := by
  choose f hf using fun x : B => (Finset.mem_filter.mp (hB x.2)).2
  exact ⟨B.attach.sup f, fun x hx =>
    revClosureAt_mono_stage Q S (Finset.le_sup (Finset.mem_attach _ ⟨x, hx⟩)) (hf ⟨x, hx⟩)⟩

theorem crsClosure_usableCRS (Q : ReversibleCRS M R) (A : Finset R) :
    crsClosure Q (usableCRS Q A) = crsClosure Q A := by
  refine Finset.Subset.antisymm (crsClosure_mono Q (Finset.filter_subset _ _)) fun x hx => ?_
  obtain ⟨_, k, hk⟩ := Finset.mem_filter.mp hx
  suffices ∀ m, revClosureAt Q A m ⊆ crsClosure Q (usableCRS Q A) from this k hk
  intro m; induction m with
  | zero => exact fun y hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _, 0, hy⟩
  | succ m ih =>
    intro y hy
    simp only [revClosureAt, revClosureStep, Finset.mem_union, Finset.mem_biUnion] at hy
    have hs (n : ℕ) : revClosureAt Q A n ⊆ crsClosure Q A := fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _, n, hz⟩
    rcases hy with hy | ⟨r, hrA, hy | hy⟩
    · exact ih hy
    · split_ifs at hy with hL
      · have hrU : r ∈ usableCRS Q A := Finset.mem_filter.mpr ⟨hrA, Finset.union_subset (hL.trans (hs m)) fun z hz =>
          hs (m + 1) (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hrA, Finset.mem_union_left _ (ite_eq_left hL ▸ hz)⟩))⟩
        obtain ⟨n, hn⟩ := subset_revClosureAt_of_crsClosure (hL.trans ih)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, n + 1,
          Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hrU, Finset.mem_union_left _ (ite_eq_left hn ▸ hy)⟩)⟩
      · simp at hy
    · split_ifs at hy with hR
      · have hrU : r ∈ usableCRS Q A := Finset.mem_filter.mpr ⟨hrA, Finset.union_subset (fun z hz =>
          hs (m + 1) (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hrA, Finset.mem_union_right _ (ite_eq_left hR ▸ hz)⟩)))
          (hR.trans (hs m))⟩
        obtain ⟨n, hn⟩ := subset_revClosureAt_of_crsClosure (hR.trans ih)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, n + 1,
          Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hrU, Finset.mem_union_right _ (ite_eq_left hn ▸ hy)⟩)⟩
      · simp at hy

theorem usableCRS_isRAF (Q : ReversibleCRS M R) (Cat : Catalysis M R) (A : Finset R)
    (hcat : ∀ r ∈ A, ∃ x ∈ crsClosure Q A, Cat x r)
    (hgrow : ¬ crsClosure Q A ⊆ Q.food) :
    IsRevRAF Q Cat (usableCRS Q A) := by
  have hne : (usableCRS Q A).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; rintro he
    apply hgrow; rw [← crsClosure_usableCRS, he]
    rintro x hx; obtain ⟨_, k, hk⟩ := Finset.mem_filter.mp hx
    have h0 : ∀ m, revClosureAt Q ∅ m = Q.food := fun m => by induction m <;> simp [revClosureAt, revClosureStep, *]
    rwa [h0] at hk
  refine ⟨hne, fun r hr => subset_revClosureAt_of_crsClosure (crsClosure_usableCRS Q A ▸ (Finset.mem_filter.mp hr).2),
    fun r hr => ?_⟩
  obtain ⟨x, hx, hc⟩ := hcat r (Finset.mem_filter.mp hr).1
  obtain ⟨_, k, hk⟩ := Finset.mem_filter.mp (crsClosure_usableCRS Q A ▸ hx)
  exact ⟨x, k, hk, hc⟩

end UsableCRS

def crsRAFEvent {n : ℕ} {R : Type*} (Q : ReversibleCRS (Molecule n) R) :
    Set (R → Molecule n → Prop) :=
  {ω | ∃ S, IsRevRAF Q (fun x r => ω r x) S}

theorem crs_near_full_lower {n m : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (Q : ReversibleCRS (Molecule n) R) (hfood : Q.food = binaryFood n 2)
    (p q : I) (hm : 0 < m) (hk : 6 < nearFullPoolSize n m)
    (hq : q ≤ fixedPoolParameter p (nearFullPoolSize n m)) :
    Measure.pi (fun _ : R => ambientCoordLaw q)
      {ω | (m - 1) * Fintype.card (Molecule n) ≤ m * (crsClosure Q (Finset.univ.filter ω)).card} ≤
      law (X := Molecule n) (fun _ : R => p) (crsRAFEvent Q) := by
  let k := nearFullPoolSize n m
  have hmass : Measure.pi (fun _ : R => ambientCoordLaw q)
      {ω | (m - 1) * Fintype.card (Molecule n) ≤ m * (crsClosure Q (Finset.univ.filter ω)).card} ≤
      Measure.pi (fun _ : R => ambientCoordLaw q) {ω | k ≤ (crsClosure Q (Finset.univ.filter ω)).card} :=
    measure_mono fun ω (hω : (m - 1) * _ ≤ _) => by
      have := Nat.mul_le_mul_left (m - 1) (Nat.div_mul_le_self (Fintype.card (Molecule n)) m)
      dsimp [k, nearFullPoolSize]; nlinarith
  have hmono := product_increasing_mono (fun _ : R => q) (fun _ => fixedPoolParameter p k) (fun _ => hq)
    (fun ω => k ≤ (crsClosure Q (Finset.univ.filter ω)).card) fun x y hxy hx =>
      hx.trans (Finset.card_le_card (crsClosure_mono Q fun r hr =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy r (Finset.mem_filter.mp hr).2⟩))
  have hbar := mass_ge_static (X := Molecule n) (R := R) p (crsClosure Q) (crsClosure_mono Q) k (Fintype.card R)
  rw [card_finiteInitialSegment _ _ (nearFullPoolSize_le n m)] at hbar
  refine hmass.trans (hmono.trans (hbar.trans (measure_mono fun ω hω => ?_)))
  let A := peelingActiveAt (catalystActive ω) (crsClosure Q) (Fintype.card R)
  have hs : catalystActive ω (crsClosure Q A) = A :=
    peelingActiveAt_stable_card (catalystActive ω) (crsClosure Q) (catalystActive_mono ω) (crsClosure_mono Q)
  refine ⟨usableCRS Q A, usableCRS_isRAF Q _ A (fun r hr => (mem_catalystActive ω _ _).mp (hs.symm ▸ hr)) fun hsub => ?_⟩
  have h6 : (Q.food).card ≤ 6 := hfood ▸ (binaryFood_card_le_cutoff n 2).trans_eq (by decide)
  have := (Finset.card_le_card hsub).trans h6
  change k ≤ (crsClosure Q A).card at hω; omega

theorem crs_raf_upper {n K G : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (Q : ReversibleCRS (Molecule n) R)
    (hG : (Finset.univ.filter fun r => RevSeedReaction Q r).card ≤ G) (p : I) :
    law (X := Molecule n) (fun _ : R => p) (crsRAFEvent Q) ≤
      Measure.pi (fun _ : R => ambientCoordLaw (fixedPoolParameter p (Fintype.card (Molecule n))))
        {ω | ∃ x ∈ crsClosure Q (Finset.univ.filter ω), K + 2 < molLength x} +
      (Fintype.card (Molecule (K + 2)) : ENNReal) * G * (toNNReal p : ENNReal) := by
  let E : Set (R → Molecule n → Prop) := {ω | ∃ x ∈ crsClosure Q (catalystActive ω Finset.univ), K + 2 < molLength x}
  let B : Set (R → Molecule n → Prop) := {ω | ∃ x : Molecule n, ∃ r : R, molLength x ≤ K + 2 ∧ RevSeedReaction Q r ∧ ω r x}
  have hs : crsRAFEvent Q ⊆ E ∪ B := fun ω ⟨S, hne, hfg, hcat⟩ => by
    by_cases he : ω ∈ E
    · exact .inl he
    · obtain ⟨r, hr, hseed⟩ := exists_rev_seed_of_foodGenerated Q S hne hfg
      obtain ⟨x, k, hx, hxr⟩ := hcat r hr
      have hsub : S ⊆ catalystActive ω Finset.univ := fun q hq =>
        let ⟨y, _, _, hy⟩ := hcat q hq; (mem_catalystActive ω _ _).mpr ⟨y, Finset.mem_univ _, hy⟩
      have hx' : x ∈ crsClosure Q (catalystActive ω Finset.univ) :=
        crsClosure_mono Q hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hx⟩)
      exact .inr ⟨x, r, Nat.le_of_not_gt fun hl => he ⟨x, hx', hl⟩, hseed, hxr⟩
  have hB : law (X := Molecule n) (fun _ : R => p) B ≤
      (Fintype.card (Molecule (K + 2)) : ENNReal) * G * (toNNReal p : ENNReal) := by
    let J := ↥(binaryFood n (K + 2)) × ↥(Finset.univ.filter fun r => RevSeedReaction Q r)
    rw [show B = ⋃ j : J, {ω | ω j.2.1 j.1.1} by
      ext ω; simp only [B, J, Set.mem_ofPred_eq, Set.mem_iUnion, Prod.exists, Subtype.exists,
        binaryFood, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨x, r, hx, hr, hω⟩ => ⟨x, hx, r, hr, hω⟩, fun ⟨x, hx, r, hr, hω⟩ => ⟨x, r, hx, hr, hω⟩⟩]
    refine (measure_iUnion_fintype_le _ _).trans ?_
    simp only [coordinate_probability, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    refine mul_le_mul_left ?_ _
    exact_mod_cast (by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe]
      exact Nat.mul_le_mul (binaryFood_card_le_cutoff n (K + 2)) hG : Fintype.card J ≤ Fintype.card (Molecule (K + 2)) * G)
  refine (measure_mono hs).trans ((measure_union_le _ _).trans (add_le_add ?_ hB))
  dsimp only [E]
  rw [pool_statistic p Finset.univ fun A => ∃ x ∈ crsClosure Q A, K + 2 < molLength x, Finset.card_univ]

end HordijkSteelThreshold
