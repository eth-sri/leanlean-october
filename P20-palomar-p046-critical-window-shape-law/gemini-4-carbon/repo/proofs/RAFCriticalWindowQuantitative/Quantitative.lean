module

public import proofs.RAFReactionQuotient.Quotient

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Filter HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

/-- A finite executable evaluator, using the literal source's closure iteration. -/
def computedClosure (N L : ℕ) (S : Finset (Reaction N)) : Finset (Molecule N) :=
  revClosureAt (binaryPolymerCRS N L) S (Fintype.card (Molecule N))

theorem revClosureAt_stable_of_measure {M R α : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (f : Finset M → Finset α) (B : ℕ)
    (hB : ∀ C, (f C).card ≤ B)
    (hgrow : ∀ C, revClosureStep Q S C ≠ C → (f C).card < (f (revClosureStep Q S C)).card) :
    ∀ {m}, B ≤ m → revClosureAt Q S m = revClosureAt Q S B := by
  have hor (k : ℕ) : k ≤ (f (revClosureAt Q S k)).card ∨ revClosureAt Q S (k + 1) = revClosureAt Q S k := by
    induction k with
    | zero => exact .inl (Nat.zero_le _)
    | succ k ih =>
      by_cases h : revClosureAt Q S (k + 1) = revClosureAt Q S k
      · exact .inr (by change revClosureStep Q S _ = _; rwa [h])
      · exact .inl ((ih.resolve_right h).trans_lt (hgrow _ h))
  have h1 : revClosureAt Q S (B + 1) = revClosureAt Q S B :=
    (hor B).elim (fun hg => by by_contra hne; exact (hg.trans_lt ((hgrow _ hne).trans_le (hB _))).false) id
  have hadd (j : ℕ) : revClosureAt Q S (B + j) = revClosureAt Q S B := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Nat.add_succ, revClosureAt, ih]; exact h1
  intro m hm; rw [show m = B + (m - B) by omega]; exact hadd _

theorem closure_stable_ge_card {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) {m : ℕ} (hm : Fintype.card M ≤ m) :
    revClosureAt Q S m = revClosureAt Q S (Fintype.card M) :=
  revClosureAt_stable_of_measure Q S id (Fintype.card M) Finset.card_le_univ
    (fun _ h => Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, h.symm⟩)) hm

theorem revClosureAt_card_eq_crsClosure {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) :
    revClosureAt Q S (Fintype.card M) = crsClosure Q S := by
  ext x; simp only [crsClosure, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun hx => ⟨_, hx⟩, fun ⟨k, hk⟩ => ?_⟩
  by_cases h : k ≤ Fintype.card M
  · exact revClosureAt_mono_stage Q S h hk
  · rwa [closure_stable_ge_card Q S (by omega)] at hk

/-- Exact semantics: the executable finite iteration equals the existing closure. -/
theorem computedClosure_eq (N L : ℕ) (S : Finset (Reaction N)) :
    computedClosure N L S = temporaryReactionClosure L S :=
  revClosureAt_card_eq_crsClosure _ S

def geometricTest (t c ε : ℚ) (r : ℕ) : Prop := 0 < r ∧ c*t^r ≤ ε

instance (t c ε : ℚ) (r : ℕ) : Decidable (geometricTest t c ε r) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem geometricTest_exists (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) :
    ∃ r, geometricTest t c ε r := by
  have hs := (tendsto_pow_atTop_nhds_zero_of_lt_one (by exact_mod_cast ht0 : (0 : ℝ) ≤ t)
    (by exact_mod_cast ht1)).const_mul (c : ℝ)
  simp only [mul_zero] at hs
  obtain ⟨r, hr, hv⟩ := ((eventually_ge_atTop 1).and (hs.eventually_lt_const (by exact_mod_cast hε : (0 : ℝ) < ε))).exists
  exact ⟨r, hr, by exact_mod_cast hv.le⟩

def geometricIndex (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) : ℕ :=
  Nat.find (geometricTest_exists t c ε ht0 ht1 hε)

theorem geometricIndex_spec (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) :
    geometricTest t c ε (geometricIndex t c ε ht0 ht1 hε) :=
  Nat.find_spec (geometricTest_exists t c ε ht0 ht1 hε)

/-- The repair-failure ratio is a genuine geometric ratio at every positive openness. -/
theorem repair_ratio (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ) :
    0 ≤ 1-q^(L+1) ∧ 1-q^(L+1) < 1 :=
  ⟨sub_nonneg.mpr (pow_le_one₀ hq.le hq1), sub_lt_self _ (pow_pos hq _)⟩



theorem rationalHalf_pos (q : ℚ) (hq : 0 < q) : 0 < q/2 :=
  div_pos hq zero_lt_two

theorem rationalHalf_le_one (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) : q/2 ≤ 1 :=
  (div_le_self hq.le one_le_two).trans hq1

def precisionIndex (ε : ℚ) : ℕ := ⌈4/ε⌉₊+2

def recordIndex (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ)
    (ε : ℚ) (hε : 0 < ε) : ℕ :=
  geometricIndex (1-q^(L+1)) (2^(L+1)) (ε/4)
    (repair_ratio q hq hq1 L).1 (repair_ratio q hq hq1 L).2 (by positivity)

theorem precisionIndex_ge_two (ε : ℚ) : 2 ≤ precisionIndex ε := Nat.le_add_left _ _

theorem precisionIndex_error (ε : ℚ) (hε : 0 < ε) :
    1 / (precisionIndex ε : ℚ) ≤ ε / 4 := by
  have hm : (0 : ℚ) < precisionIndex ε := by exact_mod_cast (Nat.succ_le_of_lt zero_lt_two).trans (precisionIndex_ge_two ε)
  have hb : (4 : ℚ) / ε ≤ precisionIndex ε := (Nat.le_ceil (4 / ε : ℚ)).trans (by unfold precisionIndex; norm_cast; omega)
  have hx := (div_le_iff₀ hε).mp hb
  exact (div_le_iff₀ hm).mpr (by nlinarith)

/-- A decidable rational test, using the source's literal contour constant. -/
def seedTest (b : ℚ) (m k : ℕ) : Prop :=
  0 < k ∧ (molecularContourConstant : ℚ) * (1 - b^2)^k *
    ((m : ℚ) * (m+1) + 1) ≤ 1

instance (b : ℚ) (m k : ℕ) : Decidable (seedTest b m k) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem seedTest_exists (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) :
    ∃ k, seedTest b m k := by
  obtain ⟨k, hk, hv⟩ := geometricTest_exists (1 - b ^ 2)
    ((molecularContourConstant : ℚ) * ((m : ℚ) * (m + 1) + 1)) 1 (by nlinarith) (by nlinarith) one_pos
  exact ⟨k, hk, by linarith⟩

/-- Executable unbounded search; termination is proved from geometric decay. -/
def seedIndex (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) : ℕ :=
  Nat.find (seedTest_exists b hb hb1 m)

theorem seedIndex_spec (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) :
    seedTest b m (seedIndex b hb hb1 m) := Nat.find_spec (seedTest_exists b hb hb1 m)

/-- The exact rational comparison gives the deficit needed by the mass proof. -/
theorem rational_deficit_bound (b : ℚ) (m k : ℕ) (hm : 0 < m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (ht : seedTest b m k) :
    let h := (molecularContourConstant : ℚ) * (1 - b ^ 2) ^ k
    h < 1 ∧ h / (1 - h) ≤ 1 / ((m : ℚ) * (m + 1)) := by
  dsimp
  have hmR : (0 : ℚ) < m := by exact_mod_cast hm
  have hd : (0 : ℚ) < m * (m + 1) := by positivity
  have hh0 : (0 : ℚ) ≤ (molecularContourConstant : ℚ) * (1 - b ^ 2) ^ k :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by nlinarith) _)
  have hh1 : (molecularContourConstant : ℚ) * (1 - b ^ 2) ^ k < 1 := by nlinarith [ht.2]
  exact ⟨hh1, (div_le_div_iff₀ (sub_pos.mpr hh1) hd).mpr (by nlinarith [ht.2])⟩

def rationalParameter (b : ℚ) (hb : 0 ≤ b) (hb1 : b ≤ 1) : I :=
  ⟨b, by constructor <;> exact_mod_cast ‹_›⟩

theorem selected_contour_deficit (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) (hm : 0 < m) :
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    contourBudget a k / (1 - contourBudget a k) ≤ 1 / ((m : ENNReal) * (m + 1)) := by
  dsimp only
  let a := rationalParameter b hb.le hb1
  let k := seedIndex b hb hb1 m
  have hq := rational_deficit_bound b m k hm hb.le hb1 (seedIndex_spec b hb hb1 m)
  have hfin : contourBudget a k ≠ ∞ := by unfold contourBudget; finiteness
  have hreal : (contourBudget a k).toReal = (molecularContourConstant : ℝ) * (1 - (b : ℝ) ^ 2) ^ k := by
    rw [contourBudget, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le (pow_le_one₀ (by positivity) (by exact_mod_cast a.2.2)) (by simp)]
    simp [a, rationalParameter]
  have he : contourBudget a k < 1 :=
    (ENNReal.toReal_lt_toReal hfin (by simp)).mp (by rw [hreal]; exact_mod_cast hq.1)
  refine (ENNReal.toReal_le_toReal (ENNReal.div_ne_top hfin (ne_of_gt (tsub_pos_iff_lt.mpr he))) (by finiteness)).mp ?_
  rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le he.le (by simp), hreal,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_one, ENNReal.toReal_natCast]
  have hc := (Rat.cast_le (K := ℝ)).mpr hq.2
  push_cast at hc; exact hc

def rationalEventProbability (J : Type*) [Fintype J] [DecidableEq J] (q : ℚ)
    (event : (J → Bool) → Bool) : ℚ :=
  ∑ ω : J → Bool, if event ω then ∏ j, if ω j then q else 1-q else 0

section
open Classical

/-- Exact probability semantics for an arbitrary executable Boolean event. -/
theorem rationalEventProbability_correct (J : Type*) [Fintype J] [DecidableEq J] (q : ℚ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (event : (J → Bool) → Bool) :
    (Measure.pi (fun _ : J => ambientCoordLaw (rationalParameter q hq hq1))
      {ω | event fun j => decide (ω j)}).toReal =
      (rationalEventProbability J q event : ℝ) := by
  let a := rationalParameter q hq hq1
  let w (P : Prop) : NNReal := if P then toNNReal a else toNNReal (σ a)
  have hatom (P : Prop) : ambientCoordLaw a {P} = (w P : ENNReal) := by
    by_cases hp : P <;> [simp [propext (iff_true_intro hp), w]; simp [propext (iff_false_intro hp), w]]
  let F : Finset (J → Prop) := Finset.univ.filter fun ω => event (fun j => decide (ω j)) = true
  have he : Measure.pi (fun _ : J => ambientCoordLaw a) {ω | event fun j => decide (ω j)} =
      ((∑ ω ∈ F, ∏ j, w (ω j) : NNReal) : ENNReal) := by
    rw [show {ω : J → Prop | event fun j => decide (ω j)} = (F : Set (J → Prop)) by ext; simp [F],
      ← sum_measure_singleton]
    simp [Measure.pi_singleton, hatom, ENNReal.ofNNReal_finsetProd, ENNReal.ofNNReal_finsetSum]
  rw [he, ENNReal.coe_toReal, NNReal.coe_sum, Finset.sum_filter,
    ← (Equiv.piCongrRight fun _ => Equiv.propEquivBool.symm).sum_comp]
  have hw (P : Prop) : (w P : ℝ) = if P then (q : ℝ) else 1 - q := by
    by_cases hP : P <;> simp [w, hP, a, rationalParameter]
  simp only [NNReal.coe_prod, hw]
  simp [rationalEventProbability, Equiv.propEquivBool]
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs with hev
  · push_cast; exact Finset.prod_congr rfl fun j _ => by cases ω j <;> simp
  · simp

/-- The computed cutoff gives the literal uniform supplied-seed mass guarantee. -/
theorem effective_static_bulk (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) (hm : 0 < m) :
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    ∀ N : ℕ, 0 < N →
      staticReactionMeasure N a {ω |
        m * (temporaryReactionClosure (10 * k) (staticOpenReactions ω)).card <
          (m - 1) * Fintype.card (Molecule N)} ≤ (m : ENNReal)⁻¹ := by
  dsimp only
  let a := rationalParameter b hb.le hb1
  let k := seedIndex b hb hb1 m
  let η : ENNReal := (m : ENNReal)⁻¹ / (m + 1)
  have hk : 0 < k := (seedIndex_spec b hb hb1 m).1
  have hη : contourBudget a k / (1 - contourBudget a k) ≤ η := by
    simpa [η, div_eq_mul_inv, ENNReal.mul_inv] using selected_contour_deficit b hb hb1 m hm
  intro N hN
  let U := Fintype.card (Molecule N)
  let d := U / m + 1
  have hd : 0 < d := Nat.succ_pos _
  have hUd : (U : ENNReal) ≤ (m : ENNReal) * d := by
    exact_mod_cast (by have := (Nat.div_lt_iff_lt_mul hm).mp (Nat.lt_succ_self (U / m)); dsimp [d]; nlinarith : U ≤ m * d)
  have hsub : {ω : Reaction N → Prop | m * (temporaryReactionClosure (10 * k) (staticOpenReactions ω)).card < (m - 1) * U} ⊆
      {ω | (temporaryReactionClosure (10 * k) (staticOpenReactions ω)).card + d ≤ U} := fun _ (hω : m * _ < _) => by
    simp only [Set.mem_ofPred_eq, d]; have := Nat.div_mul_le_self U m; have : m - 1 + 1 = m := (by omega); nlinarith
  calc
    _ ≤ staticReactionMeasure N a {ω | (temporaryReactionClosure (10 * k) (staticOpenReactions ω)).card + d ≤ U} :=
      measure_mono hsub
    _ ≤ η + (U : ENNReal) * η / d :=
      (measure_temporaryClosure_deficit (w := 5 * k) (k := k) (by omega) (by omega) (by omega) hN a d hd).trans
        (by gcongr)
    _ ≤ η + ((m : ENNReal) * d) * η / d := by gcongr
    _ = (m : ENNReal)⁻¹ := by
      rw [mul_right_comm, ENNReal.mul_div_cancel_right (by exact_mod_cast hd.ne') (by simp),
        show η + (m : ENNReal) * η = (m + 1) * η by ring]
      exact ENNReal.mul_div_cancel (by simp) (by simp)

/-- Explicit seed cutoff transported through the source's bounded-fibre domination. -/
theorem effective_quotient_bulk (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (m : ℕ) (hm : 0 < m) :
    let hhalf : 0 < q / 2 := by positivity
    let hhalf1 : q / 2 ≤ 1 := by linarith
    let L := 10 * seedIndex (q / 2) hhalf hhalf1 m
    ∀ a : I, rationalParameter q hq.le hq1 ≤ a → ∀ n : ℕ, 0 < n →
      quotientStaticMeasure n a {ω |
        m * (quotientClosure n L (quotientOpen ω)).card <
          (m - 1) * Fintype.card (Molecule n)} ≤ (m : ENNReal)⁻¹ := by
  dsimp only
  have hh : 0 < q / 2 := by positivity
  have hh1 : q / 2 ≤ 1 := by linarith
  let a0 := rationalParameter q hq.le hq1
  let L := 10 * seedIndex (q / 2) hh hh1 m
  have hbulk := effective_static_bulk (q / 2) hh hh1 m hm
  dsimp only at hbulk
  rw [show rationalParameter (q / 2) hh.le hh1 = halfParameter a0 from Subtype.ext (by simp [rationalParameter, halfParameter, a0])] at hbulk
  intro a ha n hn
  have hi := product_decreasing_mono (fibreParameter (@splitToQuotient n) (halfParameter a0)) (fun _ => a)
    (fun j => (fibreParameter_half_le splitToQuotient a0 j (by convert split_fibre_le_two j using 2; ext; simp)).trans ha)
    _ (quotient_mass_failure_antitone n L m)
  rw [← fieldOR_map (@splitToQuotient n) (halfParameter a0),
    Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at hi
  refine hi.trans ?_
  simpa [Set.preimage, quotientClosure_OR, staticReactionMeasure, Measure.infinitePi_eq_pi,
    RAFEmergenceApprox.Generic.colLaw] using hbulk n hn

private theorem closure_stable_ge_channel_count {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) {m : ℕ} (hm : S.card ≤ m) :
    revClosureAt Q S m = revClosureAt Q S S.card :=
  revClosureAt_stable_of_measure Q S (fun C => S.filter fun r => Q.lhs r ∪ Q.rhs r ⊆ C) S.card
    (fun _ => Finset.card_filter_le _ _)
    (fun C hg => by
      have hold : C ⊆ revClosureStep Q S C := Finset.subset_union_left
      obtain ⟨x, hx, hnot⟩ := Finset.not_subset.mp fun hh => hg (Finset.Subset.antisymm hh hold)
      obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp ((Finset.mem_union.mp hx).resolve_left hnot)
      have hadd {y} (hy : y ∈ (if RevEnabledLhs Q C r then Q.rhs r else ∅) ∪
          (if RevEnabledRhs Q C r then Q.lhs r else ∅)) : y ∈ revClosureStep Q S C :=
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr, hy⟩)
      have hsub : Q.lhs r ∪ Q.rhs r ⊆ revClosureStep Q S C ∧ ¬ Q.lhs r ∪ Q.rhs r ⊆ C := by
        rcases Finset.mem_union.mp hxr with hxL | hxR
        · split_ifs at hxL with hE
          · exact ⟨Finset.union_subset (hE.trans hold) fun _ hy => hadd (Finset.mem_union_left _ (ite_eq_left hE ▸ hy)),
              fun hs => hnot (hs (Finset.mem_union_right _ hxL))⟩
          · simp at hxL
        · split_ifs at hxR with hE
          · exact ⟨Finset.union_subset (fun _ hy => hadd (Finset.mem_union_right _ (ite_eq_left hE ▸ hy))) (hE.trans hold),
              fun hs => hnot (hs (Finset.mem_union_left _ hxR))⟩
          · simp at hxR
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨fun _ hq => let ⟨hqS, h1⟩ := Finset.mem_filter.mp hq; Finset.mem_filter.mpr ⟨hqS, h1.trans hold⟩,
         fun he => by have := Finset.ext_iff.mp he r; simp [hr, hsub.1, hsub.2] at this⟩)) hm

private theorem crs_sparse_length {N : ℕ} {R : Type*} [Fintype R] [DecidableEq R]
    (Q : ReversibleCRS (Molecule N) R) (hf : Q.food = binaryFood N 2)
    (hbin : ∀ r, ∃ u v p, Q.lhs r = {u, v} ∧ Q.rhs r = {p} ∧ molLength u + molLength v = molLength p)
    (S : Finset R) (x : Molecule N) (hx : x ∈ crsClosure Q S) :
    molLength x ≤ 2 ^ (S.card + 1) := by
  obtain ⟨_, m, hm⟩ := Finset.mem_filter.mp hx
  have hst : x ∈ revClosureAt Q S S.card := by
    by_cases h : m ≤ S.card
    · exact revClosureAt_mono_stage Q S h hm
    · rwa [closure_stable_ge_channel_count Q S (by omega)] at hm
  suffices ∀ k y, y ∈ revClosureAt Q S k → molLength y ≤ 2 ^ (k + 1) from this S.card x hst
  intro k; induction k with
  | zero => exact fun y hy => (Finset.mem_filter.mp (hf ▸ hy : y ∈ binaryFood N 2)).2
  | succ k ih =>
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact (ih y hy).trans (Nat.pow_le_pow_right (by omega) (by omega))
    · obtain ⟨r, _, hy⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨u, v, p, hlhs, hrhs, hsum⟩ := hbin r
      rcases Finset.mem_union.mp hy with hy | hy
      · split_ifs at hy with hen
        · obtain rfl : y = p := Finset.mem_singleton.mp (hrhs ▸ hy)
          have hu := ih u (hen (hlhs ▸ by simp))
          have hv := ih v (hen (hlhs ▸ by simp))
          rw [pow_succ]; omega
        · simp at hy
      · split_ifs at hy with hen
        · have hp := ih p (hen (hrhs ▸ Finset.mem_singleton_self _))
          rcases (by simpa [hlhs] using hy : y = u ∨ y = v) with rfl | rfl <;> (rw [pow_succ]; omega)
        · simp at hy

/-- A sparse set of open channels cannot generate an arbitrarily long molecule. -/
theorem sparse_closure_length (N : ℕ) (S : Finset (Reaction N))
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure 2 S) :
    molLength x ≤ 2 ^ (S.card + 1) :=
  crs_sparse_length (binaryPolymerCRS N 2) rfl (fun r => ⟨reactionLeft r, reactionRight r, reactionProduct r,
    rfl, rfl, by simp [molLength_reactionProduct, reaction_length_add]⟩) S x hx

theorem quotient_sparse_closure_length (N : ℕ) (S : Finset (RepositoryChannel N))
    (x : Molecule N) (hx : x ∈ quotientClosure N 2 S) :
    molLength x ≤ 2 ^ (S.card + 1) :=
  crs_sparse_length (repositoryCRS N 2) rfl (fun r => ⟨r.1.1, r.1.2, concatMolecule r.1.1 r.1.2 r.2.1,
    rfl, rfl, by simp [concatMolecule]⟩) S x hx

def fullClosure {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) : Finset M := revClosureAt Q S (Fintype.card M)

inductive ProductiveHistory {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) : ℕ → Finset R → Prop
  | nil : ProductiveHistory Q S 0 ∅
  | step {k T r} : ProductiveHistory Q S k T → r ∈ S → r ∉ T →
      revClosureStep Q {r} (fullClosure Q T) ≠ fullClosure Q T →
      ProductiveHistory Q S (k+1) (insert r T)

theorem productive_extension {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S T : Finset R) (x : M)
    (hx : x ∈ fullClosure Q S) (hnot : x ∉ fullClosure Q T) :
    ∃ r ∈ S, r ∉ T ∧ revClosureStep Q {r} (fullClosure Q T) ≠ fullClosure Q T := by
  let C := fullClosure Q T
  have hg : revClosureStep Q S C ≠ C := fun he => hnot <| by
    have hall (k : ℕ) : revClosureAt Q S k ⊆ C := by
      induction k with
      | zero => exact revClosureAt_mono_stage Q T (Nat.zero_le _)
      | succ _ ih => exact (revClosureStep_mono Q Finset.Subset.rfl ih).trans he.le
    exact hall _ hx
  have hex : ∃ r ∈ S, revClosureStep Q {r} C ≠ C := by
    by_contra! h
    refine hg (Finset.Subset.antisymm (fun y hy => ?_) Finset.subset_union_left)
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hy
    · obtain ⟨r, hr, hy⟩ := Finset.mem_biUnion.mp hy
      exact h r hr ▸ Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_singleton_self _, hy⟩)
  obtain ⟨r, hr, hgrow⟩ := hex
  refine ⟨r, hr, fun hrT => hgrow (Finset.Subset.antisymm ?_ Finset.subset_union_left), hgrow⟩
  exact (revClosureStep_mono Q (Finset.singleton_subset_iff.mpr hrT) Finset.Subset.rfl).trans
    (closure_stable_ge_card Q T (Nat.le_succ _)).le

theorem long_target_productive_history {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (length : M → ℕ)
    (hbound : ∀ T x, x ∈ crsClosure Q T → length x ≤ 2 ^ (T.card + 1))
    (S : Finset R) (k : ℕ) (x : M) (hx : x ∈ crsClosure Q S) (hlen : 2 ^ (k + 1) < length x) :
    ∃ T, ProductiveHistory Q S k T ∧ T.card = k ∧ T ⊆ S := by
  have hx' : x ∈ fullClosure Q S := (revClosureAt_card_eq_crsClosure Q S).symm.subset hx
  induction k with
  | zero => exact ⟨∅, .nil, rfl, Finset.empty_subset _⟩
  | succ k ih =>
    obtain ⟨T, hT, hcard, hTS⟩ := ih ((Nat.pow_le_pow_right (by omega) (by omega)).trans_lt hlen)
    obtain ⟨r, hr, hrT, hgrow⟩ := productive_extension Q S T x hx' fun hh => by
      have := hcard ▸ hbound T x ((revClosureAt_card_eq_crsClosure Q T).subset hh); omega
    exact ⟨insert r T, .step hT hr hrT hgrow, by rw [Finset.card_insert_of_notMem hrT, hcard],
      Finset.insert_subset hr hTS⟩

theorem split_long_target_history (N k : ℕ) (S : Finset (Reaction N)) (x : Molecule N)
    (hx : x ∈ temporaryReactionClosure 2 S) (hlen : 2 ^ (k + 1) < molLength x) :
    ∃ T, ProductiveHistory (binaryPolymerCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S :=
  long_target_productive_history _ molLength (sparse_closure_length N) S k x hx hlen

theorem quotient_long_target_history (N k : ℕ) (S : Finset (RepositoryChannel N)) (x : Molecule N)
    (hx : x ∈ quotientClosure N 2 S) (hlen : 2 ^ (k + 1) < molLength x) :
    ∃ T, ProductiveHistory (repositoryCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S :=
  long_target_productive_history _ molLength (quotient_sparse_closure_length N) S k x hx hlen

def recordCap (ell : ℕ) : ℕ → ℕ :=
  Nat.rec 2 (fun _ cap => 2*cap+ell)

theorem recordCap_ge_two (ell : ℕ) : ∀ j : ℕ, 2 ≤ recordCap ell j
  | 0 => le_rfl
  | j + 1 => by have := recordCap_ge_two ell j; simp only [recordCap] at *; omega

theorem recordCap_mono_length {ell L : ℕ} (h : ell ≤ L) : ∀ j : ℕ, recordCap ell j ≤ recordCap L j
  | 0 => le_rfl
  | j + 1 => by have := recordCap_mono_length h j; simp only [recordCap] at *; omega

theorem escape_has_bounded_record {L B : ℕ} (hLB : L ≤ B)
    {field : InfiniteSplitEnvironment}
    (h : ∃ w, B < w.length ∧ InfiniteReversibleGenerated L field w) :
    ∃ v, B < v.length ∧ v.length ≤ 2 * B ∧ FiniteReversibleGenerated v.length L field v := by
  obtain ⟨w, hw, hg⟩ := h
  refine (generated_or_bounded_record hLB hg).resolve_left fun hf => ?_
  have := finiteReversibleGenerated_length_le hf; omega

def indexedField (idx : List Bool × ℕ → List Bool × ℕ) (ω : SplitField) : InfiniteSplitEnvironment :=
  fun w k => ω (idx (w, k))

private theorem indexed_record_failure_bound (idx : List Bool × ℕ → List Bool × ℕ)
    (h1 : ∀ z, (idx z).1 = z.1) (a : I) (w v : List Bool)
    (hw : 0 < w.length) (hv : 0 < v.length) (N : ℕ) (hN : w.length + v.length ≤ N)
    (E : Set SplitField) (hE : SplitPrefixDetermined (splitPrefixCoordinates w.length) E)
    (hrec : ∀ ω ∈ E, FiniteReversibleGenerated w.length 2 (indexedField idx ω) w) :
    infiniteSplitPi a (E ∩ {ω | ¬ FiniteReversibleGenerated N 2 (indexedField idx ω) v}) ≤
      infiniteSplitPi a E * (1 - (toNNReal a : ENNReal) ^ (v.length + 1)) := by
  obtain ⟨S, hsize, hband, hgen⟩ := target_trial_support (N := w.length + v.length) w v hw hv le_rfl
  let T := S.image (idx ∘ literalSplitCoordinate)
  have hdis : Disjoint (splitPrefixCoordinates w.length) T := Finset.disjoint_left.mpr fun z hz ht => by
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
    have hl := (mem_splitPrefixCoordinates w.length _).mp hz
    have hb := (hband r hr).1
    simp only [Function.comp_apply, h1] at hl
    change (moleculeWord (reactionProduct r)).length ≤ w.length ∧ _ at hl
    rw [moleculeWord_length] at hl; omega
  have hs : E ∩ {ω | ¬ FiniteReversibleGenerated N 2 (indexedField idx ω) v} ⊆ E ∩ {ω | ¬ ∀ z ∈ T, ω z} :=
    fun ω ⟨hωE, hωv⟩ => ⟨hωE, fun hopen => hωv <| finiteReversibleGenerated_mono_cap hN <| by
      obtain ⟨x, hx, he⟩ := finiteReversible_to_literalClosure
        (finiteReversibleGenerated_mono_cap (Nat.le_add_right _ _) (hrec ω hωE))
      obtain ⟨y, hy, hev⟩ := hgen (restrictedSplitReactions _ (indexedField idx ω))
        (fun r hr => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hopen _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)⟩) x hx he
      simpa [hev] using literalClosure_to_finiteReversible (indexedField idx ω) y hy⟩
  refine (measure_mono hs).trans ?_
  rw [split_prefix_failure_measure a _ T hdis E hE]
  exact mul_le_mul_right (tsub_le_tsub_left
    (pow_le_pow_of_le_one zero_le (by exact_mod_cast a.2.2) (Finset.card_image_le.trans hsize)) 1) _

private def wordRank (s : List Bool) : ℕ := 2 ^ s.length + binaryWordCode s

private theorem wordRank_lt_of_length {u v : List Bool} (h : u.length < v.length) : wordRank u < wordRank v := by
  have := binaryWordCode_lt u
  have := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_of_lt h)
  unfold wordRank; rw [pow_succ] at this; omega

private theorem wordRank_injective {u v : List Bool} (h : wordRank u = wordRank v) : u = v := by
  rcases lt_trichotomy u.length v.length with hl | he | hg
  · exact absurd h (wordRank_lt_of_length hl).ne
  · exact binaryWordCode_injective_length he (by unfold wordRank at h; rw [he] at h; omega)
  · exact absurd h (wordRank_lt_of_length hg).ne'

theorem indexed_escaped_missing_contraction (idx : List Bool × ℕ → List Bool × ℕ)
    (h1 : ∀ z, (idx z).1 = z.1)
    (hp : ∀ {B z}, z ∈ splitPrefixCoordinates B → idx z ∈ splitPrefixCoordinates B)
    (a : I) (v : List Bool) (hv : 0 < v.length) (B : ℕ) (hB : 2 ≤ B) :
    let EM (M : ℕ) : Set SplitField :=
      {ω | (∃ w, M < w.length ∧ InfiniteReversibleGenerated 2 (indexedField idx ω) w) ∧
        ¬ FiniteReversibleGenerated M 2 (indexedField idx ω) v}
    infiniteSplitPi a (EM (2 * B + v.length)) ≤
      infiniteSplitPi a (EM B) * (1 - (toNNReal a : ENNReal) ^ (v.length + 1)) := by
  intro EM
  let W := (shortBinaryWords (2 * B)).filter fun w => B < w.length
  let D (w : List Bool) : Set SplitField :=
    {ω | ¬ FiniteReversibleGenerated B 2 (indexedField idx ω) v ∧
      FiniteReversibleGenerated w.length 2 (indexedField idx ω) w ∧
      ∀ u ∈ W, wordRank u < wordRank w → ¬ FiniteReversibleGenerated u.length 2 (indexedField idx ω) u}
  have htr {N M : ℕ} (hNM : N ≤ M) {u : List Bool} {ω η : SplitField}
      (he : ∀ z ∈ splitPrefixCoordinates M, ω z = η z) :
      FiniteReversibleGenerated N 2 (indexedField idx ω) u ↔ FiniteReversibleGenerated N 2 (indexedField idx η) u :=
    ⟨finiteReversibleGenerated_transfer_prefix hNM fun s hs k hk =>
        he (idx (s, k)) (hp ((mem_splitPrefixCoordinates _ _).mpr ⟨hs, hk⟩)),
     finiteReversibleGenerated_transfer_prefix hNM fun s hs k hk =>
        (he (idx (s, k)) (hp ((mem_splitPrefixCoordinates _ _).mpr ⟨hs, hk⟩))).symm⟩
  have hdet {w : List Bool} (hw : w ∈ W) : SplitPrefixDetermined (splitPrefixCoordinates w.length) (D w) :=
    fun ω η he => and_congr (not_congr (htr (Finset.mem_filter.mp hw).2.le he)) <|
      and_congr (htr le_rfl he) <| forall₂_congr fun u _ => imp_congr_right fun hlt =>
        not_congr (htr (not_lt.mp fun hg => not_lt_of_gt (wordRank_lt_of_length hg) hlt) he)
  have hdis : Set.PairwiseDisjoint (W : Set (List Bool)) D := fun x hxW y hyW hxy =>
    Set.disjoint_left.mpr fun _ hx hyD => by
      rcases lt_trichotomy (wordRank x) (wordRank y) with hl | he | hg
      · exact hyD.2.2 x hxW hl hx.2.1
      · exact hxy (wordRank_injective he)
      · exact hx.2.2 y hyW hg hyD.2.1
  have hcover : EM (2 * B + v.length) ⊆ ⋃ w ∈ W, EM (2 * B + v.length) ∩ D w := fun ω hω => by
    obtain ⟨w₀, hw₀, hg₀⟩ := hω.1
    obtain ⟨u, huB, hu2, hgu⟩ := escape_has_bounded_record hB ⟨w₀, by omega, hg₀⟩
    let Wω := W.filter fun s => FiniteReversibleGenerated s.length 2 (indexedField idx ω) s
    obtain ⟨w, hw, hmin⟩ := Finset.exists_min_image Wω wordRank
      ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(mem_shortBinaryWords u _).mpr hu2, huB⟩, hgu⟩⟩
    obtain ⟨hwW, hwg⟩ := Finset.mem_filter.mp hw
    exact Set.mem_iUnion₂.mpr ⟨w, hwW, hω,
      fun hgen => hω.2 (finiteReversibleGenerated_mono_cap (by omega) hgen), hwg,
      fun s hsW hlt hsg => not_le_of_gt hlt (hmin s (Finset.mem_filter.mpr ⟨hsW, hsg⟩))⟩
  calc
    _ ≤ ∑ w ∈ W, infiniteSplitPi a (EM (2 * B + v.length) ∩ D w) :=
      (measure_mono hcover).trans (measure_biUnion_finset_le W _)
    _ ≤ ∑ w ∈ W, infiniteSplitPi a (D w) * (1 - (toNNReal a : ENNReal) ^ (v.length + 1)) :=
      Finset.sum_le_sum fun w hw => by
        obtain ⟨hw2, hwB⟩ := Finset.mem_filter.mp hw
        have := (mem_shortBinaryWords w _).mp hw2
        exact (measure_mono (t := D w ∩ {η | ¬ FiniteReversibleGenerated (2 * B + v.length) 2 (indexedField idx η) v})
            fun _ hη => ⟨hη.2, hη.1.2⟩).trans
          (indexed_record_failure_bound idx h1 a w v (by omega) hv (2 * B + v.length) (by omega)
            (D w) (hdet hw) fun _ hη => hη.2.1)
    _ = infiniteSplitPi a (⋃ w ∈ W, D w) * (1 - (toNNReal a : ENNReal) ^ (v.length + 1)) := by
      rw [← Finset.sum_mul, measure_biUnion_finset hdis fun w hw => measurableSet_of_splitPrefixDetermined _ _ (hdet hw)]
    _ ≤ _ := mul_le_mul_left (measure_mono fun ω hω => by
      obtain ⟨w, hw, hωC, hwg, _⟩ := Set.mem_iUnion₂.mp hω
      exact ⟨⟨w, (Finset.mem_filter.mp hw).2, finiteReversibleGenerated_to_infinite hwg⟩, hωC⟩) _

theorem indexed_finite_seed_failure (idx : List Bool × ℕ → List Bool × ℕ)
    (h1 : ∀ z, (idx z).1 = z.1)
    (hp : ∀ {B z}, z ∈ splitPrefixCoordinates B → idx z ∈ splitPrefixCoordinates B)
    (a : I) (seed : Finset (List Bool)) (L : ℕ)
    (hseed : ∀ v ∈ seed, 0 < v.length ∧ v.length ≤ L) (r : ℕ) :
    infiniteSplitPi a {ω |
      (∃ w, recordCap L r < w.length ∧ InfiniteReversibleGenerated 2 (indexedField idx ω) w) ∧
      ¬ ∀ v ∈ seed, FiniteReversibleGenerated (recordCap L r) 2 (indexedField idx ω) v} ≤
      (seed.card : ENNReal) * (1 - (toNNReal a : ENNReal) ^ (L + 1)) ^ r := by
  let EM (M : ℕ) (v : List Bool) : Set SplitField :=
    {ω | (∃ w, M < w.length ∧ InfiniteReversibleGenerated 2 (indexedField idx ω) w) ∧
      ¬ FiniteReversibleGenerated M 2 (indexedField idx ω) v}
  have hrep (v : List Bool) (hv : 0 < v.length) (j : ℕ) :
      infiniteSplitPi a (EM (recordCap v.length j) v) ≤ (1 - (toNNReal a : ENNReal) ^ (v.length + 1)) ^ j := by
    induction j with
    | zero => simpa using (prob_le_one : infiniteSplitPi a _ ≤ 1)
    | succ j ih =>
      exact ((indexed_escaped_missing_contraction idx h1 hp a v hv _ (recordCap_ge_two _ j)).trans
        (mul_le_mul' ih le_rfl)).trans_eq (pow_succ _ _).symm
  have hsub : {ω : SplitField |
      (∃ w, recordCap L r < w.length ∧ InfiniteReversibleGenerated 2 (indexedField idx ω) w) ∧
      ¬ ∀ v ∈ seed, FiniteReversibleGenerated (recordCap L r) 2 (indexedField idx ω) v} ⊆
      ⋃ v ∈ seed, EM (recordCap L r) v := fun ω ⟨he, hn⟩ => by
    push Not at hn; obtain ⟨v, hv, hm⟩ := hn; exact Set.mem_iUnion₂.mpr ⟨v, hv, he, hm⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  refine (Finset.sum_le_sum (g := fun _ => (1 - (toNNReal a : ENNReal) ^ (L + 1)) ^ r) fun v hv => ?_).trans_eq (by simp)
  obtain ⟨hv0, hvL⟩ := hseed v hv
  have hle := recordCap_mono_length hvL r
  exact ((measure_mono (s := EM (recordCap L r) v) (t := EM (recordCap v.length r) v) fun ω ⟨⟨w, hw, hg⟩, hn⟩ =>
      ⟨⟨w, hle.trans_lt hw, hg⟩, fun h => hn (finiteReversibleGenerated_mono_cap hle h)⟩).trans
    (hrep v hv0 r)).trans (pow_le_pow_left' (tsub_le_tsub_left
      (pow_le_pow_of_le_one zero_le (by exact_mod_cast a.2.2) (by omega)) 1) r)

noncomputable def splitEscapeProbability (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w}

noncomputable def quotientEscapeProbability (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w}

private theorem generic_explicit_truncation (idx : List Bool × ℕ → List Bool × ℕ)
    (h1 : ∀ z, (idx z).1 = z.1)
    (hp : ∀ {B z}, z ∈ splitPrefixCoordinates B → idx z ∈ splitPrefixCoordinates B)
    (hf_meas : Measurable (indexedField idx))
    {a : I} {S : ENNReal} {m L r : ℕ} (hm : 2 ≤ m)
    (hS : infiniteSplitPi a {ω | ReversibleUnbounded 2 (indexedField idx ω)} = S)
    (hbad : ∀ N, 0 < N → infiniteSplitPi a {ω | m * (temporaryReactionClosure L (restrictedSplitReactions N (indexedField idx ω))).card <
      (m - 1) * Fintype.card (Molecule N)} ≤ (m : ENNReal)⁻¹) :
    infiniteSplitPi a {ω | ∃ w, recordCap L r < w.length ∧ InfiniteReversibleGenerated 2 (indexedField idx ω) w} ≤
      S + (m : ENNReal)⁻¹ + ((actualBinaryWords L).card : ENNReal) * (1 - (toNNReal a : ENNReal) ^ (L + 1)) ^ r := by
  let K := recordCap L r
  let E : Set SplitField := {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (indexedField idx ω) w}
  let H : Set SplitField := {ω | ∀ v ∈ actualBinaryWords L, FiniteReversibleGenerated K 2 (indexedField idx ω) v}
  have hgood : infiniteSplitPi a H ≤ S + (m : ENNReal)⁻¹ :=
    (measure_mono (s := H) fun _ hω v hv => finiteReversibleGenerated_to_infinite (hω v hv)).trans
      (hS ▸ infinite_seed_le_survival (infiniteSplitPi a) _ hf_meas hm hbad)
  have hbad' := indexed_finite_seed_failure idx h1 hp a (actualBinaryWords L) L
    (fun v hv => let hh := (mem_actualBinaryWords v L).mp hv; ⟨List.length_pos_iff.mpr hh.1, hh.2⟩) r
  exact (measure_mono (t := H ∪ (E ∩ Hᶜ)) fun ω hω => by by_cases hh : ω ∈ H <;> [exact .inl hh; exact .inr ⟨hω, hh⟩]).trans
    ((measure_union_le _ _).trans (add_le_add hgood hbad'))

theorem explicit_split_truncation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) (r : ℕ) :
    let L := 10 * seedIndex q hq hq1 m
    splitEscapeProbability a (recordCap L r) ≤ staticSurvival a + (m : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) * (1 - (toNNReal a : ENNReal) ^ (L + 1)) ^ r := by
  intro L
  refine generic_explicit_truncation id (fun _ => rfl) id measurable_currySplitField hm
    (Measure.map_apply measurable_currySplitField (measurableSet_reversibleUnbounded 2)).symm fun N hN => ?_
  refine (proj_closure_measure literalSplitCoordinate (literalSplitCoordinate_injective N)
    (fun ω => temporaryReactionClosure L (staticOpenReactions ω)) (indexedField id) (fun _ => rfl) a
    fun C => m * C.card < (m - 1) * Fintype.card (Molecule N)).symm.trans_le ?_
  rw [← Measure.infinitePi_eq_pi]
  exact (static_decreasing_event_mono N ha _ fun _ _ hST hT =>
    (Nat.mul_le_mul_left m (Finset.card_le_card (temporaryReactionClosure_mono hST))).trans_lt hT).trans
    (effective_static_bulk q hq hq1 m (by omega) N hN)

theorem explicit_quotient_truncation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) (r : ℕ) :
    let hhalf : 0 < q / 2 := by positivity
    let hhalf1 : q / 2 ≤ 1 := by linarith
    let L := 10 * seedIndex (q / 2) hhalf hhalf1 m
    quotientEscapeProbability a (recordCap L r) ≤ quotientSurvival a + (m : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) * (1 - (toNNReal a : ENNReal) ^ (L + 1)) ^ r := by
  intro hh hh1 L
  refine generic_explicit_truncation canonicalIndex canonicalIndex_product canonicalIndex_prefix
    quotientField_measurable hm rfl fun N hN => ?_
  exact (proj_closure_measure quotientCoordinate (quotientCoordinate_injective N)
    (fun ω => quotientClosure N L (quotientOpen ω)) (indexedField canonicalIndex) (quotientClosure_restriction N L) a
    fun C => m * C.card < (m - 1) * Fintype.card (Molecule N)).symm.trans_le
    (effective_quotient_bulk q hq hq1 m (by omega) a ha N hN)

theorem split_escape_finite (a : I) (K : ℕ) (hK : 2 ≤ K) :
    splitEscapeProbability a K =
      staticReactionMeasure (2 * ((K - 2) + 2)) a (staticEscapeEvent 2 (K - 2)) := by
  rw [splitEscapeProbability, finite_static_escape_measure_eq]
  congr 1; ext; simp [reversibleEscapeEvent_iff, show K - 2 + 2 = K by omega]

theorem split_survival_le_escape (a : I) (K : ℕ) : staticSurvival a ≤ splitEscapeProbability a K := by
  rw [staticSurvival, infiniteStaticMeasure,
    Measure.map_apply measurable_currySplitField (measurableSet_reversibleUnbounded 2)]
  exact measure_mono fun _ hω => hω K

theorem quotient_escape_finite (a : I) (K : ℕ) (hK : 2 ≤ K) :
    quotientEscapeProbability a K =
      quotientStaticMeasure (2 * ((K - 2) + 2)) a (quotientEscapeEvent 2 (K - 2)) := by
  rw [quotientEscapeProbability, quotient_escape_measure_eq]
  congr 1; ext; simp [reversibleEscapeEvent_iff, show K - 2 + 2 = K by omega]

theorem quotient_survival_le_escape (a : I) (K : ℕ) :
    quotientSurvival a ≤ quotientEscapeProbability a K :=
  measure_mono fun _ hω => hω K

def sparseWitnessCap (r : ℕ) : ℕ := 2*(2^(r+1)+2)

def splitSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (Reaction (sparseWitnessCap r))).choose r

def quotientSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (RepositoryChannel (sparseWitnessCap r))).choose r

theorem finite_many_open_probability (J : Type*) [Fintype J] (a : I) (r : ℕ) :
    Measure.pi (fun _ : J => ambientCoordLaw a)
      {ω | r ≤ (Finset.univ.filter fun j : J => ω j).card} ≤
      ((Fintype.card J).choose r : ENNReal) * (toNNReal a : ENNReal) ^ r := by
  let P := (Finset.univ : Finset J).powersetCard r
  have hs : {ω : J → Prop | r ≤ (Finset.univ.filter fun j : J => ω j).card} ⊆
      ⋃ T ∈ P, (T : Set J).pi fun _ => ({True} : Set Prop) := fun ω hω => by
    obtain ⟨T, hT, hc⟩ := Finset.exists_subset_card_eq hω
    exact Set.mem_iUnion₂.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hc⟩,
      fun j hj => by simpa using (Finset.mem_filter.mp (hT hj)).2⟩
  refine (measure_mono hs).trans ((measure_biUnion_finset_le _ _).trans_eq ?_)
  have ht : ∀ T ∈ P, Measure.pi (fun _ : J => ambientCoordLaw a) ((T : Set J).pi fun _ => {True}) =
      (toNNReal a : ENNReal) ^ r := fun T hT => by
    rw [Measure.pi_pi_finset]; simp [(Finset.mem_powersetCard.mp hT).2]
  rw [Finset.sum_congr rfl ht]; simp [P]

private theorem generic_sparse_probability {J : Type*} [Fintype J] {S : ENNReal} (a : I) (r : ℕ)
    (cl : (J → Prop) → Finset (Molecule (sparseWitnessCap r)))
    (hS : S ≤ Measure.pi (fun _ : J => ambientCoordLaw a) {ω | ∃ x ∈ cl ω, 2 ^ (r + 1) + 2 < (moleculeWord x).length})
    (hlen : ∀ ω x, x ∈ cl ω → molLength x ≤ 2 ^ ((Finset.univ.filter ω).card + 1)) :
    S ≤ ((Fintype.card J).choose r : ENNReal) * (toNNReal a : ENNReal) ^ r := by
  refine hS.trans ((measure_mono (t := {ω | r ≤ (Finset.univ.filter ω).card}) ?_).trans
    (finite_many_open_probability J a r))
  rintro ω ⟨x, hx, hl⟩
  by_contra hn; change ¬ r ≤ _ at hn
  have := hlen ω x hx
  have := Nat.pow_le_pow_right (by omega : 0 < 2) (show (Finset.univ.filter ω).card + 1 ≤ r + 1 by omega)
  rw [moleculeWord_length] at hl; omega

theorem split_sparse_probability (a : I) (r : ℕ) :
    staticSurvival a ≤ (splitSparseCoefficient r : ENNReal) * (toNNReal a : ENNReal) ^ r :=
  generic_sparse_probability a r (fun ω => temporaryReactionClosure 2 (staticOpenReactions ω))
    (by rw [← Measure.infinitePi_eq_pi]; exact staticSurvival_le_finite_escape a (2 ^ (r + 1)))
    fun ω => sparse_closure_length _ (staticOpenReactions ω)

theorem quotient_sparse_probability (a : I) (r : ℕ) :
    quotientSurvival a ≤ (quotientSparseCoefficient r : ENNReal) * (toNNReal a : ENNReal) ^ r :=
  generic_sparse_probability a r (fun ω => quotientClosure _ 2 (quotientOpen ω))
    (quotientSurvival_le_finite_escape a (2 ^ (r + 1)))
    fun ω => quotient_sparse_closure_length _ (quotientOpen ω)

theorem split_sparse_real (a : I) (r : ℕ) :
    (staticSurvival a).toReal ≤ (splitSparseCoefficient r : ℝ) * (a : ℝ) ^ r := by
  simpa using ENNReal.toReal_mono (by finiteness) (split_sparse_probability a r)

theorem quotient_sparse_real (a : I) (r : ℕ) :
    (quotientSurvival a).toReal ≤ (quotientSparseCoefficient r : ℝ) * (a : ℝ) ^ r := by
  simpa using ENNReal.toReal_mono (by finiteness) (quotient_sparse_probability a r)

private theorem power_bound_intensity_flatness (S : I → ℝ) (C : ℕ → ℕ)
    (hbound : ∀ a r, S a ≤ (C r : ℝ) * (a : ℝ) ^ r) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      S (criticalOpenness lam hlam) < ε * lam ^ d := by
  let c : ℝ := C (d + 1)
  have hc : 0 < c + 1 := by positivity
  refine ⟨ε / (c + 1), by positivity, fun lam hlam hlamδ => ?_⟩
  let a := criticalOpenness lam hlam
  have ha2 : (a : ℝ) ≤ lam := by change 1 - Real.exp (-lam) ≤ lam; linarith [Real.add_one_le_exp (-lam)]
  have hca : c * lam < ε := by linarith [(lt_div_iff₀ hc).mp hlamδ, (by positivity : 0 ≤ c)]
  have hb := (hbound a (d + 1)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ a.2.1 ha2 _) (by positivity))
  have hm := mul_lt_mul_of_pos_right hca (pow_pos hlam d)
  rw [pow_succ] at hb; dsimp [c] at hb hm; linarith

theorem split_low_intensity_flatness (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      (staticSurvival (criticalOpenness lam hlam)).toReal < ε * lam ^ d :=
  power_bound_intensity_flatness _ splitSparseCoefficient split_sparse_real d ε hε

theorem quotient_low_intensity_flatness (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      (quotientSurvival (criticalOpenness lam hlam)).toReal < ε * lam ^ d :=
  power_bound_intensity_flatness _ quotientSparseCoefficient quotient_sparse_real d ε hε

/-- A fully symbolic certificate, requiring no enumeration of channel fields. -/
theorem worked_low_openness_bound (a : I) (ha : (a : ℝ) ≤ 1 / 10 ^ 20) :
    (staticSurvival a).toReal < 8 / 10 ^ 26 := by
  have h := split_sparse_real a 2
  have hc : splitSparseCoefficient 2 = 712483666919430 := by
    unfold splitSparseCoefficient sparseWitnessCap
    rw [card_reactions_exact (by norm_num)]; norm_num [Nat.choose_two_right]
  rw [hc, Nat.cast_ofNat] at h
  exact h.trans_lt ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ a.2.1 ha 2) (by norm_num)).trans_lt (by norm_num))

end

def splitEscapeBool (N K : ℕ) (ω : Reaction N → Bool) : Bool :=
  decide (∃ x ∈ computedClosure N 2 (Finset.univ.filter (fun r => ω r)), K < molLength x)

def quotientEscapeBool (N K : ℕ) (ω : RepositoryChannel N → Bool) : Bool :=
  splitEscapeBool N K (fun r => ω (splitToQuotient r))

def splitEscapeEval (q : ℚ) (K : ℕ) : ℚ :=
  rationalEventProbability (Reaction (2*(K+2))) q (splitEscapeBool _ (K+2))

def quotientEscapeEval (q : ℚ) (K : ℕ) : ℚ :=
  rationalEventProbability (RepositoryChannel (2*(K+2))) q (quotientEscapeBool _ (K+2))

def splitSeedBool (N L : ℕ) (ω : Reaction N → Bool) : Bool :=
  decide (binaryFood N L ⊆ computedClosure N 2 (Finset.univ.filter (fun r => ω r)))

def quotientSeedBool (N L : ℕ) (ω : RepositoryChannel N → Bool) : Bool :=
  splitSeedBool N L (fun r => ω (splitToQuotient r))

def splitSeedEval (N L : ℕ) (q : ℚ) : ℚ :=
  rationalEventProbability (Reaction N) q (splitSeedBool N L)

def quotientSeedEval (N L : ℕ) (q : ℚ) : ℚ :=
  rationalEventProbability (RepositoryChannel N) q (quotientSeedBool N L)

theorem splitEscapeEval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) :
    (splitEscapeEval q K : ℝ) =
      (staticReactionMeasure (2 * (K + 2)) (rationalParameter q hq hq1) (staticEscapeEvent 2 K)).toReal := by
  classical
  rw [splitEscapeEval, ← rationalEventProbability_correct _ q hq hq1, staticReactionMeasure, Measure.infinitePi_eq_pi]
  congr 2; ext ω
  simp [splitEscapeBool, computedClosure_eq, staticEscapeEvent, staticOpenReactions, moleculeWord_length]

theorem quotientEscapeEval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) :
    (quotientEscapeEval q K : ℝ) =
      (quotientStaticMeasure (2 * (K + 2)) (rationalParameter q hq hq1) (quotientEscapeEvent 2 K)).toReal := by
  classical
  rw [quotientEscapeEval, ← rationalEventProbability_correct _ q hq hq1, quotientStaticMeasure]
  congr 2; ext ω
  simp only [Set.mem_ofPred_eq, quotientEscapeBool, splitEscapeBool, decide_eq_true_eq, computedClosure_eq]
  change (∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions fun r => ω (splitToQuotient r)), K + 2 < molLength x) ↔ _
  simp [← quotientClosure_pullback, quotientEscapeEvent, moleculeWord_length]

theorem splitSeedEval_correct (N L : ℕ) (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (splitSeedEval N L q : ℝ) =
      (staticReactionMeasure N (rationalParameter q hq hq1)
        {ω | binaryFood N L ⊆ temporaryReactionClosure 2 (staticOpenReactions ω)}).toReal := by
  classical
  rw [splitSeedEval, ← rationalEventProbability_correct _ q hq hq1, staticReactionMeasure, Measure.infinitePi_eq_pi]
  congr 2; ext ω; simp [splitSeedBool, computedClosure_eq, staticOpenReactions]

theorem quotientSeedEval_correct (N L : ℕ) (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (quotientSeedEval N L q : ℝ) =
      (quotientStaticMeasure N (rationalParameter q hq hq1)
        {ω | binaryFood N L ⊆ quotientClosure N 2 (quotientOpen ω)}).toReal := by
  classical
  rw [quotientSeedEval, ← rationalEventProbability_correct _ q hq hq1, quotientStaticMeasure]
  congr 2; ext ω
  simp only [Set.mem_ofPred_eq, quotientSeedBool, splitSeedBool, decide_eq_true_eq, computedClosure_eq]
  change (binaryFood N L ⊆ temporaryReactionClosure 2 (staticOpenReactions fun r => ω (splitToQuotient r))) ↔ _
  rw [← quotientClosure_pullback]

section
open Classical

private theorem seed_mass_split_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {N L m : ℕ} (cl2 clL : Ω → Finset (Molecule N))
    (htrans : ∀ ω, binaryFood N L ⊆ cl2 ω → clL ω ⊆ cl2 ω) :
    μ {ω | binaryFood N L ⊆ cl2 ω} ≤
      μ {ω | (m - 1) * Fintype.card (Molecule N) ≤ m * (cl2 ω).card} +
      μ {ω | m * (clL ω).card < (m - 1) * Fintype.card (Molecule N)} := by
  refine (measure_mono fun ω h => ?_).trans (measure_union_le _ _)
  by_cases hb : m * (clL ω).card < (m - 1) * Fintype.card (Molecule N)
  · exact .inr hb
  · exact .inl ((Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card (htrans ω h))))

theorem split_finite_source_lower (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (lambda : ℝ)
    (hk : 6 < nearFullPoolSize n m)
    (hpool : rationalParameter q hq.le hq1 ≤ fixedPoolParameter (catalysisP n lambda) (nearFullPoolSize n m)) :
    staticReactionMeasure n (rationalParameter q hq.le hq1)
      {ω | binaryFood n (10 * seedIndex q hq hq1 m) ⊆ temporaryReactionClosure 2 (staticOpenReactions ω)} ≤
      uniformCatalysisMeasure n lambda (HasRAFEvent n) + (m : ENNReal)⁻¹ :=
  (seed_mass_split_bound _ _ _ fun _ h => temporaryReactionClosure_seed_transfer Finset.Subset.rfl
    fun _ hx => h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)).trans
    (add_le_add (canonical_raf_ge_near_full_static n m lambda hm _ hk hpool)
      (effective_static_bulk q hq hq1 m hm n hn))

theorem quotient_finite_source_lower (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (p : I)
    (hk : 6 < nearFullPoolSize n m)
    (hpool : rationalParameter q hq.le hq1 ≤ fixedPoolParameter p (nearFullPoolSize n m)) :
    let hh : 0 < q / 2 := by positivity
    let hh1 : q / 2 ≤ 1 := by linarith
    quotientStaticMeasure n (rationalParameter q hq.le hq1)
      {ω | binaryFood n (10 * seedIndex (q / 2) hh hh1 m) ⊆ quotientClosure n 2 (quotientOpen ω)} ≤
      quotientRAFProbability n p + (m : ENNReal)⁻¹ :=
  (seed_mass_split_bound _ _ _ fun _ h => by
    simp only [quotientClosure_pullback] at h ⊢
    exact temporaryReactionClosure_seed_transfer Finset.Subset.rfl fun _ hx =>
      h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)).trans
    (add_le_add (quotient_near_full_lower n m p _ hm hk hpool)
      (effective_quotient_bulk q hq hq1 m hm _ le_rfl n hn))

theorem canonical_raf_le_finite_escape_36 (n K : ℕ) (lambda : ℝ) :
    uniformCatalysisMeasure n lambda (HasRAFEvent n) ≤
      staticReactionMeasure (2*(K+2))
        (fixedPoolParameter (catalysisP n lambda) (Fintype.card (Molecule n)))
        (staticEscapeEvent 2 K) +
      (Fintype.card (Molecule (K+2)) : ENNReal)*36*(toNNReal (catalysisP n lambda) : ENNReal) := by
  rw [uniform_raf_eq_law]
  have hcard : (Finset.univ.filter fun r : Reaction n => RevSeedReaction (binaryPolymerCRS n 2) r).card ≤ 36 := by
    rw [← Fintype.card_subtype]; exact card_concrete_gateway_binary_t2 n
  refine (crs_raf_upper (K := K) (binaryPolymerCRS n 2) hcard (catalysisP n lambda)).trans (add_le_add_left ?_ _)
  rw [← Measure.infinitePi_eq_pi, finite_static_escape_measure_eq]
  exact static_capped_escape_le n K _

end

def rationalPool (p : ℚ) (k : ℕ) : ℚ := 1-(1-p)^k

theorem rationalPool_nonneg (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) : 0 ≤ rationalPool p k :=
  sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp1) (by linarith))

theorem rationalPool_le_one (p : ℚ) (hp1 : p ≤ 1) (k : ℕ) : rationalPool p k ≤ 1 :=
  sub_le_self _ (pow_nonneg (sub_nonneg.mpr hp1) k)

theorem rationalPool_correct (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    rationalParameter (rationalPool p k) (rationalPool_nonneg p hp hp1 k) (rationalPool_le_one p hp1 k) =
      fixedPoolParameter (rationalParameter p hp hp1) k :=
  Subtype.ext (by simp [rationalParameter, rationalPool])

def splitEvaluationCap (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  let L := 10*seedIndex q hq hq1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)

def splitCertifiedInterval (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  let e := splitEscapeEval q (splitEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)

def quotientEvaluationCap (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  let hhalf : 0 < q/2 := rationalHalf_pos q hq
  let hhalf1 : q/2 ≤ 1 := rationalHalf_le_one q hq hq1
  let L := 10*seedIndex (q/2) hhalf hhalf1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)

def quotientCertifiedInterval (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  let e := quotientEscapeEval q (quotientEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)

theorem real_record_budget (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ)
    (ε : ℚ) (hε : 0 < ε) :
    ((actualBinaryWords L).card : ℝ) * (1 - (q : ℝ) ^ (L + 1)) ^ recordIndex q hq hq1 L ε hε ≤ (ε : ℝ) / 4 := by
  have hr := (Rat.cast_le (K := ℝ)).mpr (geometricIndex_spec (1 - q ^ (L + 1)) (2 ^ (L + 1)) (ε / 4)
    (repair_ratio q hq hq1 L).1 (repair_ratio q hq hq1 L).2 (by positivity : (0 : ℚ) < ε / 4)).2
  push_cast at hr
  have hc : ((actualBinaryWords L).card : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
    exact_mod_cast (actualBinaryWords_card L ▸ Nat.sub_le _ _ : (actualBinaryWords L).card ≤ 2 ^ (L + 1))
  exact (mul_le_mul_of_nonneg_right hc (pow_nonneg (by exact_mod_cast (repair_ratio q hq hq1 L).1) _)).trans hr

theorem real_error_of_bound (e S : ENNReal) (hS : S ≠ ∞) (m L r : ℕ) (hm : 0 < m)
    (a : I) (h : e ≤ S + (m : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) * (1 - (toNNReal a : ENNReal) ^ (L + 1)) ^ r) :
    e.toReal ≤ S.toReal + 1 / (m : ℝ) + ((actualBinaryWords L).card : ℝ) * (1 - (a : ℝ) ^ (L + 1)) ^ r := by
  have hi : (m : ENNReal)⁻¹ ≠ ∞ := by simp [hm.ne']
  have ht : ((actualBinaryWords L).card : ENNReal) * (1 - (toNNReal a : ENNReal) ^ (L + 1)) ^ r ≠ ∞ := by finiteness
  have hsum : S + (m : ENNReal)⁻¹ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hS, hi⟩
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hsum, ht⟩) h
  rw [ENNReal.toReal_add hsum ht, ENNReal.toReal_add hS hi, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le (pow_le_one₀ (by positivity) (by exact_mod_cast a.2.2)) (by simp)] at hr
  simpa [one_div] using hr

private theorem generic_uniform_approx {q : ℚ} (hq : 0 < q) (hq1 : q ≤ 1) {ε : ℚ} (hε : 0 < ε)
    {a : I} (ha : rationalParameter q hq.le hq1 ≤ a) {L : ℕ} {esc S : ENNReal} (hS : S ≠ ⊤)
    (htrunc : esc ≤ S + (precisionIndex ε : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) * (1 - (toNNReal a : ENNReal) ^ (L + 1)) ^ recordIndex q hq hq1 L ε hε) :
    esc.toReal ≤ S.toReal + (ε : ℝ) / 2 := by
  have ht := real_error_of_bound esc S hS _ L _
    ((Nat.succ_le_of_lt zero_lt_two).trans (precisionIndex_ge_two ε)) a htrunc
  have hp : 1 / (precisionIndex ε : ℝ) ≤ (ε : ℝ) / 4 := by
    have hc := (Rat.cast_le (K := ℝ)).mpr (precisionIndex_error ε hε); push_cast at hc; exact hc
  have hr : ((actualBinaryWords L).card : ℝ) * (1 - (a : ℝ) ^ (L + 1)) ^ recordIndex q hq hq1 L ε hε ≤ (ε : ℝ) / 4 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr (pow_le_one₀ a.2.1 a.2.2))
      (sub_le_sub_left (pow_le_pow_left₀ (by exact_mod_cast hq.le : (0 : ℝ) ≤ q) (ha : (q : ℝ) ≤ a) _) 1) _)
      (Nat.cast_nonneg _)).trans (real_record_budget q hq hq1 L ε hε)
  linarith

private theorem generic_certified_correct {q : ℚ} (hq : 0 < q) (hq1 : q ≤ 1) {ε : ℚ} (hε : 0 < ε)
    {L : ℕ} {e : ℚ} {esc S : ENNReal} (hS : S ≠ ⊤) (hesc : esc ≠ ⊤)
    (htrunc : esc ≤ S + (precisionIndex ε : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) *
        (1 - (toNNReal (rationalParameter q hq.le hq1) : ENNReal) ^ (L + 1)) ^ recordIndex q hq hq1 L ε hε)
    (heval : (e : ℝ) = esc.toReal) (hle : S ≤ esc) :
    ((e - ε / 2 : ℚ) : ℝ) ≤ S.toReal ∧ S.toReal ≤ (e : ℝ) ∧ e - (e - ε / 2) < ε :=
  ⟨by have := generic_uniform_approx hq hq1 hε le_rfl hS htrunc; push_cast; linarith,
    heval ▸ ENNReal.toReal_mono hesc hle, by linarith⟩

theorem splitCertifiedInterval_correct (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    let interval := splitCertifiedInterval q hq hq1 ε hε
    (interval.1 : ℝ) ≤ (staticSurvival (rationalParameter q hq.le hq1)).toReal ∧
      (staticSurvival (rationalParameter q hq.le hq1)).toReal ≤ (interval.2 : ℝ) ∧
      interval.2 - interval.1 < ε :=
  generic_certified_correct hq hq1 hε (by unfold staticSurvival; exact measure_ne_top _ _)
    (by unfold splitEscapeProbability; exact measure_ne_top _ _)
    (explicit_split_truncation q hq hq1 _ (precisionIndex_ge_two ε) _ le_rfl _)
    ((splitEscapeEval_correct q hq.le hq1 _).trans
      (congrArg ENNReal.toReal (split_escape_finite _ _ (recordCap_ge_two _ _)).symm))
    (split_survival_le_escape _ _)

theorem quotientCertifiedInterval_correct (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    let interval := quotientCertifiedInterval q hq hq1 ε hε
    (interval.1 : ℝ) ≤ (quotientSurvival (rationalParameter q hq.le hq1)).toReal ∧
      (quotientSurvival (rationalParameter q hq.le hq1)).toReal ≤ (interval.2 : ℝ) ∧
      interval.2 - interval.1 < ε :=
  generic_certified_correct hq hq1 hε (by unfold quotientSurvival; exact measure_ne_top _ _)
    (by unfold quotientEscapeProbability; exact measure_ne_top _ _)
    (explicit_quotient_truncation q hq hq1 _ (precisionIndex_ge_two ε) _ le_rfl _)
    ((quotientEscapeEval_correct q hq.le hq1 _).trans
      (congrArg ENNReal.toReal (quotient_escape_finite _ _ (recordCap_ge_two _ _)).symm))
    (quotient_survival_le_escape _ _)

theorem split_uniform_approximation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ε : ℚ) (hε : 0 < ε) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) :
    (splitEscapeProbability a (splitEvaluationCap q hq hq1 ε hε)).toReal ≤
      (staticSurvival a).toReal + (ε : ℝ) / 2 :=
  generic_uniform_approx hq hq1 hε ha (by unfold staticSurvival; exact measure_ne_top _ _)
    (explicit_split_truncation q hq hq1 _ (precisionIndex_ge_two ε) a ha _)

theorem quotient_uniform_approximation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ε : ℚ) (hε : 0 < ε) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) :
    (quotientEscapeProbability a (quotientEvaluationCap q hq hq1 ε hε)).toReal ≤
      (quotientSurvival a).toReal + (ε : ℝ) / 2 :=
  generic_uniform_approx hq hq1 hε ha (by unfold quotientSurvival; exact measure_ne_top _ _)
    (explicit_quotient_truncation q hq hq1 _ (precisionIndex_ge_two ε) a ha _)

def splitTotalInterval (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  if h : q = 0 then (0,0) else splitCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

def quotientTotalInterval (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  if h : q = 0 then (0,0) else quotientCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

noncomputable def splitCatalyticProbability (n : ℕ) (p : I) : ENNReal :=
  uniformCatalysisMeasure n ((p : ℝ)*Fintype.card (Reaction n)/n) (HasRAFEvent n)

def splitSourceInterval (n m K : ℕ) (p q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) : ℚ × ℚ :=
  (splitSeedEval n (10*seedIndex q hq hq1 m) q - 1/m,
    splitEscapeEval (rationalPool p (Fintype.card (Molecule n))) K +
      (Fintype.card (Molecule (K+2)) : ℚ)*36*p)

def quotientSourceInterval (n m K : ℕ) (p q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) : ℚ × ℚ :=
  let hh : 0 < q/2 := rationalHalf_pos q hq
  let hh1 : q/2 ≤ 1 := rationalHalf_le_one q hq hq1
  (quotientSeedEval n (10*seedIndex (q/2) hh hh1 m) q - 1/m,
    quotientEscapeEval (rationalPool p (Fintype.card (Molecule n))) K +
      (Fintype.card (Molecule (K+2)) : ℚ)*34*p)

def rationalIntervalError (source profile : ℚ × ℚ) : ℚ :=
  max (source.2-profile.1) (profile.2-source.1)

private theorem totalInterval_correct_aux (S : I → ENNReal) (h0 : S 0 = 0)
    (cert : (q : ℚ) → 0 < q → q ≤ 1 → (ε : ℚ) → 0 < ε → ℚ × ℚ)
    (hcert : ∀ q hq hq1 ε hε, let v := cert q hq hq1 ε hε
      (v.1 : ℝ) ≤ (S (rationalParameter q (le_of_lt hq) hq1)).toReal ∧
        (S (rationalParameter q (le_of_lt hq) hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2 - v.1 < ε)
    (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    let v := if h : q = 0 then (0, 0) else cert q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε
    (v.1 : ℝ) ≤ (S (rationalParameter q hq hq1)).toReal ∧
      (S (rationalParameter q hq hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2 - v.1 < ε := by
  by_cases h : q = 0
  · subst h; rw [show rationalParameter 0 hq hq1 = 0 from Subtype.ext (by simp [rationalParameter])]; simp [h0, hε]
  · simpa [dite_eq_right h] using hcert q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

theorem splitTotalInterval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    let v := splitTotalInterval q hq hq1 ε hε
    (v.1 : ℝ) ≤ (staticSurvival (rationalParameter q hq hq1)).toReal ∧
      (staticSurvival (rationalParameter q hq hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2 - v.1 < ε :=
  totalInterval_correct_aux staticSurvival
    (le_antisymm (by simpa only [toNNReal_zero, ENNReal.coe_zero, zero_pow Nat.one_ne_zero, mul_zero] using
      split_sparse_probability 0 1) zero_le)
    splitCertifiedInterval splitCertifiedInterval_correct q hq hq1 ε hε

theorem quotientTotalInterval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    let v := quotientTotalInterval q hq hq1 ε hε
    (v.1 : ℝ) ≤ (quotientSurvival (rationalParameter q hq hq1)).toReal ∧
      (quotientSurvival (rationalParameter q hq hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2 - v.1 < ε :=
  totalInterval_correct_aux quotientSurvival
    (le_antisymm (by simpa only [toNNReal_zero, ENNReal.coe_zero, zero_pow Nat.one_ne_zero, mul_zero] using
      quotient_sparse_probability 0 1) zero_le)
    quotientCertifiedInterval quotientCertifiedInterval_correct q hq hq1 ε hε

private theorem source_profile_error_aux {m K G : ℕ} (hm : 0 < m)
    {p : ℚ} (hp : 0 ≤ p) (hp1 : p ≤ 1) {sEv eEv : ℚ} {seedM escM P : ENNReal}
    (hP : P ≠ ⊤) (hesc : escM ≠ ⊤)
    (hsEv : (sEv : ℝ) = seedM.toReal) (heEv : (eEv : ℝ) = escM.toReal)
    (hlow : seedM ≤ P + (m : ENNReal)⁻¹)
    (hupp : P ≤ escM + (Fintype.card (Molecule (K + 2)) : ENNReal) * G * (toNNReal (rationalParameter p hp hp1) : ENNReal))
    {S : ℝ} {prof : ℚ × ℚ} (hprof : (prof.1 : ℝ) ≤ S ∧ S ≤ (prof.2 : ℝ)) :
    |P.toReal - S| ≤ (rationalIntervalError (sEv - 1 / m, eEv + (Fintype.card (Molecule (K + 2)) : ℚ) * G * p) prof : ℝ) := by
  have hi : (m : ENNReal)⁻¹ ≠ ⊤ := by simp [hm.ne']
  have ht : (Fintype.card (Molecule (K + 2)) : ENNReal) * G * (toNNReal (rationalParameter p hp hp1) : ENNReal) ≠ ⊤ := by finiteness
  have hl := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hP, hi⟩) hlow
  have hu := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hesc, ht⟩) hupp
  rw [ENNReal.toReal_add hP hi, ← hsEv, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← one_div] at hl
  rw [ENNReal.toReal_add hesc ht, ← heEv, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, ENNReal.coe_toReal, coe_toNNReal] at hu
  change _ ≤ _ + _ * _ * (p : ℝ) at hu
  dsimp only [rationalIntervalError]
  push_cast
  exact abs_le.mpr ⟨neg_le.mpr (le_max_of_le_right (by linarith [hprof.2])),
    le_max_of_le_left (by linarith [hprof.1])⟩

theorem split_source_profile_error (n m K : ℕ) (hn : 4 ≤ n) (hm : 0 < m)
    (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hk : 6 < nearFullPoolSize n m) (hpool : q ≤ rationalPool p (nearFullPoolSize n m))
    (s : ℚ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    |(splitCatalyticProbability n (rationalParameter p hp hp1)).toReal -
      (staticSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (splitSourceInterval n m K p q hq hq1)
        (splitTotalInterval s hs hs1 ε hε) : ℝ) := by
  let a := rationalParameter p hp hp1
  let lam : ℝ := (a : ℝ) * Fintype.card (Reaction n) / n
  have he : catalysisP n lam = a := RAFEmergenceApprox.catalysisP_covers_probability n (by omega) a
  have hqp : rationalParameter q hq.le hq1 ≤ fixedPoolParameter a (nearFullPoolSize n m) := by
    rw [← rationalPool_correct p hp hp1]; exact (Rat.cast_le (K := ℝ)).mpr hpool
  have hS := splitTotalInterval_correct s hs hs1 ε hε
  simpa only [splitSourceInterval, splitCatalyticProbability, Nat.cast_ofNat] using source_profile_error_aux (G := 36) hm hp hp1
    (measure_ne_top _ _) (measure_ne_top _ _)
    (splitSeedEval_correct n _ q hq.le hq1)
    ((splitEscapeEval_correct _ (rationalPool_nonneg p hp hp1 _) (rationalPool_le_one p hp1 _) K).trans
      (by rw [rationalPool_correct]))
    (split_finite_source_lower q hq hq1 m n hm (by omega) lam hk (he.symm ▸ hqp))
    (he ▸ canonical_raf_le_finite_escape_36 n K lam) ⟨hS.1, hS.2.1⟩

theorem quotient_source_profile_error (n m K : ℕ) (hn : 0 < n) (hm : 0 < m)
    (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hk : 6 < nearFullPoolSize n m) (hpool : q ≤ rationalPool p (nearFullPoolSize n m))
    (s : ℚ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    |(quotientRAFProbability n (rationalParameter p hp hp1)).toReal -
      (quotientSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (quotientSourceInterval n m K p q hq hq1)
        (quotientTotalInterval s hs hs1 ε hε) : ℝ) := by
  let a := rationalParameter p hp hp1
  have hqp : rationalParameter q hq.le hq1 ≤ fixedPoolParameter a (nearFullPoolSize n m) := by
    rw [← rationalPool_correct p hp hp1]; exact (Rat.cast_le (K := ℝ)).mpr hpool
  have hS := quotientTotalInterval_correct s hs hs1 ε hε
  simpa only [quotientSourceInterval, Nat.cast_ofNat] using source_profile_error_aux (G := 34) hm hp hp1
    (by unfold quotientRAFProbability quotientCatalyticLaw; exact measure_ne_top _ _)
    (by unfold quotientStaticMeasure; exact measure_ne_top _ _)
    (quotientSeedEval_correct n _ q hq.le hq1)
    ((quotientEscapeEval_correct _ (rationalPool_nonneg p hp hp1 _) (rationalPool_le_one p hp1 _) K).trans
      (by rw [rationalPool_correct]))
    (quotient_finite_source_lower q hq hq1 m n hm hn a hk hqp)
    (quotient_raf_upper n K a) ⟨hS.1, hS.2.1⟩

end RAFCriticalWindowQuantitative
