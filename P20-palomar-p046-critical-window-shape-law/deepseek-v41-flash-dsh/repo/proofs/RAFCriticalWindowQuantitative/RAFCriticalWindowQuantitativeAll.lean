module

public import Mathlib.Analysis.SpecificLimits.Basic
public import proofs.HordijkSteelThreshold.HordijkSteelThresholdAll
public import proofs.RAFEmergenceApprox.RAFEmergenceApproxAll
public import proofs.RAFReactionQuotient.RAFReactionQuotientAll

@[expose] public section


namespace RAFCriticalWindowQuantitative

section
open Filter HordijkSteelThreshold
open scoped Topology

/-- A decidable rational test, using the source's literal contour constant. -/
def seedTest (b : ℚ) (m k : ℕ) : Prop :=
  0 < k ∧ (molecularContourConstant : ℚ) * (1 - b^2)^k *
    ((m : ℚ) * (m+1) + 1) ≤ 1

instance (b : ℚ) (m k : ℕ) : Decidable (seedTest b m k) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem seedTest_exists (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) :
    ∃ k, seedTest b m k := by
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hbR1 : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
    have hq0 : (0 : ℝ) ≤ 1 - (b : ℝ)^2 := by nlinarith
    have hq1 : 1 - (b : ℝ)^2 < 1 := by nlinarith
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have hs := (ht.const_mul (molecularContourConstant : ℝ)).mul_const
      ((m : ℝ) * (m+1) + 1)
    simp [mul_zero, zero_mul] at hs
    obtain ⟨k, hk, hv⟩ := ((eventually_ge_atTop 1).and
      (hs.eventually_lt_const (show (0 : ℝ) < 1 by norm_num))).exists
    refine ⟨k, by omega, ?_⟩
    exact_mod_cast hv.le
/-- Executable unbounded search; termination is proved from geometric decay. -/
def seedIndex (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) : ℕ :=
  Nat.find (seedTest_exists b hb hb1 m)

theorem seedIndex_spec (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) :
    seedTest b m (seedIndex b hb hb1 m) := Nat.find_spec (seedTest_exists b hb hb1 m)

/-- The exact rational comparison gives the deficit needed by the mass proof. -/
theorem rational_deficit_bound (b : ℚ) (m k : ℕ) (hm : 0 < m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (ht : seedTest b m k) :
    let h := (molecularContourConstant : ℚ) * (1-b^2)^k
    h < 1 ∧ h / (1-h) ≤ 1 / ((m : ℚ)*(m+1)) := by
    dsimp
    have hd : (0 : ℚ) < (m : ℚ)*(m+1) := by positivity
    have hh0 : (0 : ℚ) ≤ (molecularContourConstant : ℚ) * (1-b^2)^k := by
      apply mul_nonneg (Nat.cast_nonneg _)
      apply pow_nonneg
      nlinarith
    have hh := ht.2
    have hh1 : (molecularContourConstant : ℚ) * (1-b^2)^k < 1 := by nlinarith
    refine ⟨hh1, ?_⟩
    apply (div_le_div_iff₀ (sub_pos.mpr hh1) hd).mpr
    nlinarith

end

section
open Filter
open scoped Topology

def geometricTest (t c ε : ℚ) (r : ℕ) : Prop := 0 < r ∧ c*t^r ≤ ε

instance (t c ε : ℚ) (r : ℕ) : Decidable (geometricTest t c ε r) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem geometricTest_exists (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) :
    ∃ r, geometricTest t c ε r := by
    have ht0R : (0 : ℝ) ≤ t := by exact_mod_cast ht0
    have ht1R : (t : ℝ) < 1 := by exact_mod_cast ht1
    have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
    have hs := (tendsto_pow_atTop_nhds_zero_of_lt_one ht0R ht1R).const_mul (c : ℝ)
    simp [mul_zero] at hs
    obtain ⟨r,hr,hv⟩ := ((eventually_ge_atTop 1).and (hs.eventually_lt_const hεR)).exists
    exact ⟨r,by omega,by exact_mod_cast hv.le⟩
def geometricIndex (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) : ℕ :=
  Nat.find (geometricTest_exists t c ε ht0 ht1 hε)

theorem geometricIndex_spec (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) :
    geometricTest t c ε (geometricIndex t c ε ht0 ht1 hε) :=
  Nat.find_spec (geometricTest_exists t c ε ht0 ht1 hε)

/-- The repair-failure ratio is a genuine geometric ratio at every positive openness. -/
theorem repair_ratio (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ) :
    0 ≤ 1-q^(L+1) ∧ 1-q^(L+1) < 1 := by
  have hp := pow_pos hq (L+1)
  have hu := pow_le_one₀ hq.le hq1 (n := L+1)
  constructor <;> linarith


end

section

theorem rationalHalf_pos (q : ℚ) (hq : 0 < q) : 0 < q/2 :=
  div_pos hq zero_lt_two

theorem rationalHalf_le_one (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) : q/2 ≤ 1 :=
  (div_le_self hq.le one_le_two).trans hq1

def precisionIndex (ε : ℚ) : ℕ := ⌈4/ε⌉₊+2

theorem precisionIndex_ge_two (ε : ℚ) : 2 ≤ precisionIndex ε := by
  unfold precisionIndex
  omega

theorem precisionIndex_error (ε : ℚ) (hε : 0 < ε) :
    1/(precisionIndex ε : ℚ) ≤ ε/4 := by
  have hc := Nat.le_ceil (4/ε : ℚ)
  have hm : (0 : ℚ) < precisionIndex ε := by
    exact_mod_cast (show 0 < precisionIndex ε from lt_of_lt_of_le (by omega) (precisionIndex_ge_two ε))
  have hbig : (4 : ℚ)/ε ≤ precisionIndex ε := by
    exact hc.trans (by simp [precisionIndex])
  have hx := (div_le_iff₀ hε).mp hbig
  apply (div_le_iff₀ hm).mpr
  nlinarith

def recordIndex (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ)
    (ε : ℚ) (hε : 0 < ε) : ℕ :=
  geometricIndex (1-q^(L+1)) (2^(L+1)) (ε/4)
    (repair_ratio q hq hq1 L).1 (repair_ratio q hq hq1 L).2 (by positivity)

theorem recordIndex_error (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ)
    (ε : ℚ) (hε : 0 < ε) :
    0 < recordIndex q hq hq1 L ε hε ∧
      (2 : ℚ)^(L+1)*(1-q^(L+1))^(recordIndex q hq hq1 L ε hε) ≤ ε/4 :=
  geometricIndex_spec _ _ _ _ _ _


end

section
open HordijkSteelThreshold

/-- The first record above a completed prefix occurs by twice that prefix. -/
theorem generated_or_bounded_record {L B : ℕ} (hLB : L ≤ B)
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : InfiniteReversibleGenerated L field w) :
    FiniteReversibleGenerated B L field w ∨
      ∃ v, B < v.length ∧ v.length ≤ 2*B ∧
        FiniteReversibleGenerated v.length L field v := by
    induction h with
    | food hn hL => exact Or.inl (.food hn hL (hL.trans hLB))
    | @ligate u v _ _ ho ihu ihv =>
      rcases ihu with hu | he
      · rcases ihv with hv | he
        · by_cases hlen : (u++v).length ≤ B
          · exact Or.inl (.ligate hu hv ho hlen)
          · have hb : B ≤ (u++v).length := by omega
            have huB := finiteReversibleGenerated_length_le hu
            have hvB := finiteReversibleGenerated_length_le hv
            refine Or.inr ⟨u++v, by omega, ?_, .ligate
              (finiteReversibleGenerated_mono_cap hb hu)
              (finiteReversibleGenerated_mono_cap hb hv) ho le_rfl⟩
            simp [List.length_append]
            omega
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
theorem escape_has_bounded_record {L B : ℕ} (hLB : L ≤ B)
    {field : InfiniteSplitEnvironment}
    (h : ∃ w, B < w.length ∧ InfiniteReversibleGenerated L field w) :
    ∃ v, B < v.length ∧ v.length ≤ 2*B ∧
      FiniteReversibleGenerated v.length L field v := by
  obtain ⟨w,hw,hg⟩ := h
  rcases generated_or_bounded_record hLB hg with hf | he
  · have hl := finiteReversibleGenerated_length_le hf
    omega
  · exact he


end

section
open HordijkSteelThreshold unitInterval
open scoped ENNReal

def rationalParameter (b : ℚ) (hb : 0 ≤ b) (hb1 : b ≤ 1) : I :=
  ⟨b, by constructor <;> exact_mod_cast ‹_›⟩

theorem contourBudget_finite (a : I) (k : ℕ) : contourBudget a k ≠ ∞ := by
  unfold contourBudget
  finiteness

theorem contourBudget_real (a : I) (k : ℕ) :
    (contourBudget a k).toReal = (molecularContourConstant : ℝ) * (1-(a : ℝ)^2)^k := by
  have ha : (toNNReal a : ENNReal)^2 ≤ 1 := by
    exact pow_le_one₀ (by positivity) (by exact_mod_cast a.property.2)
  rw [contourBudget, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le ha (by simp)]
  simp

theorem selected_contour_deficit (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    contourBudget a k / (1-contourBudget a k) ≤
      1 / ((m : ENNReal)*(m+1)) := by
    dsimp only
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    have hq := rational_deficit_bound b m k hm hb.le hb1 (seedIndex_spec b hb hb1 m)
    have hr : (contourBudget a k).toReal < 1 := by
      rw [contourBudget_real]
      change (molecularContourConstant : ℝ) * (1-(b : ℝ)^2)^k < 1
      exact_mod_cast hq.1
    have he : contourBudget a k < 1 := by
      exact (ENNReal.toReal_lt_toReal (contourBudget_finite a k) (by simp)).mp (by simpa using hr)
    have hn := ne_of_gt (tsub_pos_iff_lt.mpr he)
    apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (contourBudget_finite a k) hn)
      (by finiteness)).mp
    rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le he.le (by simp), contourBudget_real]
    simp only [ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_natCast]
    change (molecularContourConstant : ℝ) * (1-(b : ℝ)^2)^k /
      (1-(molecularContourConstant : ℝ) * (1-(b : ℝ)^2)^k) ≤ 1/((m : ℝ)*(m+1))
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq.2
    push_cast at hcast
    exact hcast

end

section
open Classical MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

/-- Uniform finite closure deficit at the executable seed cutoff. -/
theorem effective_closure_deficit (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1)
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N) (d : ℕ) (hd : 0 < d) :
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    let η := (m : ENNReal)⁻¹/(m+1)
    staticReactionMeasure N a {ω |
      (temporaryReactionClosure (10*k) (staticOpenReactions ω)).card+d ≤ Fintype.card (Molecule N)} ≤
      η + (Fintype.card (Molecule N) : ENNReal)*η/d := by
    dsimp only
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    have hk := (seedIndex_spec b hb hb1 m).1
    have hbound := selected_contour_deficit b hb hb1 m hm
    have hηeq : 1 / ((m : ENNReal)*(m+1)) = (m : ENNReal)⁻¹/(m+1) := by
      simp [div_eq_mul_inv, ENNReal.mul_inv]
    change contourBudget a k / (1-contourBudget a k) ≤ _ at hbound
    rw [hηeq] at hbound
    apply (measure_temporaryClosure_deficit (w := 5*k) (k := k)
      (by omega : 2*(5*k) ≤ 10*k) (by omega) (by omega) hN a d hd).trans
    gcongr
/-- The computed cutoff gives the literal uniform supplied-seed mass guarantee. -/
theorem effective_static_bulk (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    ∀ N : ℕ, 0 < N →
      staticReactionMeasure N a {ω |
        m*(temporaryReactionClosure (10*k) (staticOpenReactions ω)).card <
          (m-1)*Fintype.card (Molecule N)} ≤ (m : ENNReal)⁻¹ := by
    dsimp only
    let a := rationalParameter b hb.le hb1
    let η := (m : ENNReal)⁻¹/(m+1)
    let k := seedIndex b hb hb1 m
    let L := 10*k
    have hbulk := effective_closure_deficit b hb hb1 m hm
    intro N hN
    let U := Fintype.card (Molecule N)
    let d := U/m+1
    have hd : 0 < d := Nat.succ_pos _
    have hUd : U ≤ m*d := by
      have ht : U/m < U/m+1 := by omega
      have hh := (Nat.div_lt_iff_lt_mul hm).mp ht
      dsimp [d]
      nlinarith
    have hsub : {ω : Reaction N → Prop |
        m*(temporaryReactionClosure L (staticOpenReactions ω)).card < (m-1)*U} ⊆
        {ω | (temporaryReactionClosure L (staticOpenReactions ω)).card+d ≤ U} := by
      intro ω hω
      have hdiv := Nat.div_mul_le_self U m
      have hm1 : m-1+1 = m := by omega
      dsimp [d]
      change m*(temporaryReactionClosure L (staticOpenReactions ω)).card < (m-1)*U at hω
      nlinarith
    have hcast : (U : ENNReal) ≤ (m : ENNReal)*d := by exact_mod_cast hUd
    have hratio : (U : ENNReal)*η/d ≤ (m : ENNReal)*η := by
      calc
        _ ≤ ((m : ENNReal)*d)*η/d := by gcongr
        _ = (m : ENNReal)*η := by
          rw [mul_right_comm, ENNReal.mul_div_cancel_right (by exact_mod_cast Nat.ne_of_gt hd) (by simp)]
    have htotal : η+(m : ENNReal)*η = (m : ENNReal)⁻¹ := by
      calc
        η+(m : ENNReal)*η = (1+(m : ENNReal))*η := by rw [add_mul, one_mul]
        _ = _ := ?_
      have he : (1 : ENNReal)+m = m+1 := add_comm _ _
      rw [he]
      exact ENNReal.mul_div_cancel (by simp) (by simp)
    calc
      _ ≤ staticReactionMeasure N a {ω |
        (temporaryReactionClosure L (staticOpenReactions ω)).card+d ≤ U} := measure_mono hsub
      _ ≤ η+(U : ENNReal)*η/d := hbulk N hN d hd
      _ ≤ η+(m : ENNReal)*η := add_le_add le_rfl hratio
      _ = _ := htotal

end

section
open Classical Filter MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal Topology

/-- The computable cutoff controls seed acquisition for the actual split survival law. -/
theorem effective_seed_probability_le_survival (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) :
    let b0 := rationalParameter q hq.le hq1
    let L := 10 * seedIndex q hq hq1 m
    ∀ b : I, b0 ≤ b →
      infiniteStaticMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ≤ staticSurvival b + (m : ENNReal)⁻¹ := by
    dsimp only
    let b0 := rationalParameter q hq.le hq1
    let L := 10 * seedIndex q hq hq1 m
    have hbulk := effective_static_bulk q hq hq1 m (by omega)
    intro b hb
    have hbad (N : ℕ) (hN : 0 < N) :
        staticReactionMeasure N b {ω | m*(temporaryReactionClosure L
          (staticOpenReactions ω)).card < (m-1)*Fintype.card (Molecule N)} ≤ (m : ENNReal)⁻¹ := by
      apply (static_decreasing_event_mono N hb
        (fun S => m*(temporaryReactionClosure L S).card < (m-1)*Fintype.card (Molecule N)) ?_).trans
        (hbulk N hN)
      intro S T hST hT
      exact (Nat.mul_le_mul_left m (Finset.card_le_card (temporaryReactionClosure_mono hST))).trans_lt hT
    have hK (K : ℕ) :
        infiniteStaticMeasure b {field | ∀ w ∈ actualBinaryWords L,
          InfiniteReversibleGenerated 2 field w} ≤
        staticReactionMeasure (2*(K+2)) b (staticEscapeEvent 2 K) + (m : ENNReal)⁻¹ := by
      apply le_of_tendsto (finite_static_seed_probability_tendsto 2 b (actualBinaryWords L))
      filter_upwards [(tendsto_atTop.mp card_molecule_tendsto_atTop)
        (m*Fintype.card (Molecule (K+2))+1),eventually_ge_atTop 1] with N hlarge hN
      have hmass : staticReactionMeasure N b {ω | (m-1)*Fintype.card (Molecule N) ≤
          m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} ≤
          staticReactionMeasure (2*(K+2)) b (staticEscapeEvent 2 K) := by
        rw [finite_static_escape_measure_eq]
        apply (measure_mono (show {ω : Reaction N → Prop |
          (m-1)*Fintype.card (Molecule N) ≤ m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} ⊆
          {ω | ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), K+2 < molLength x}
          from ?_)).trans (static_capped_escape_le N K b)
        intro ω hω
        by_contra h
        have hs : temporaryReactionClosure 2 (staticOpenReactions ω) ⊆ binaryFood N (K+2) := by
          intro x hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.le_of_not_gt fun hl => h ⟨x,hx,hl⟩⟩
        have hc := (Finset.card_le_card hs).trans (binaryFood_card_le_cutoff N (K+2))
        change (m-1)*Fintype.card (Molecule N) ≤ m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card at hω
        have hmult : Fintype.card (Molecule N) ≤ (m-1)*Fintype.card (Molecule N) := by
          have hh := Nat.mul_le_mul_right (Fintype.card (Molecule N)) (show 1 ≤ m-1 by omega)
          simpa using hh
        nlinarith
      exact (same_field_seed_mass_bound N L m b).trans
        (add_le_add hmass (hbad N (by omega)))
    exact ge_of_tendsto' ((finite_static_escape_probability_tendsto b).add_const (m : ENNReal)⁻¹) hK
end

section
open Classical HordijkSteelThreshold RAF.Polymer RAF.Concrete MeasureTheory unitInterval
open scoped ENNReal

/-- The record repair finishes inside its explicitly bounded cap. -/
theorem finite_record_support (w v : List Bool) (hw : 0 < w.length) (hv : 0 < v.length) :
    ∃ T : Finset (List Bool × ℕ), T.card ≤ v.length+1 ∧
      Disjoint (splitPrefixCoordinates w.length) T ∧
      ∀ field : InfiniteSplitEnvironment,
        FiniteReversibleGenerated w.length 2 field w →
        (∀ z ∈ T, field z.1 z.2) →
          FiniteReversibleGenerated (w.length+v.length) 2 field v := by
    let N := w.length+v.length
    obtain ⟨S,hsize,hband,hgen⟩ := target_trial_support (N := N) w v hw hv le_rfl
    let T := S.image literalSplitCoordinate
    refine ⟨T,(Finset.card_image_le).trans hsize,?_,?_⟩
    · apply Finset.disjoint_left.mpr
      intro z hz ht
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ht
      have hl := (mem_splitPrefixCoordinates w.length (literalSplitCoordinate r)).mp hz
      have hb := (hband r hr).1
      change (moleculeWord (reactionProduct r)).length ≤ w.length ∧ _ at hl
      rw [moleculeWord_length] at hl
      omega
    · intro field hrecord hopen
      have hgN := finiteReversibleGenerated_mono_cap (show w.length ≤ N by dsimp [N]; omega) hrecord
      obtain ⟨x,hx,he⟩ := finiteReversible_to_literalClosure hgN
      have hs : S ⊆ restrictedSplitReactions N field := by
        intro r hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hopen (literalSplitCoordinate r)
          (Finset.mem_image.mpr ⟨r,hr,rfl⟩)⟩
      obtain ⟨y,hy,hev⟩ := hgen (restrictedSplitReactions N field) hs x hx he
      simpa [hev] using literalClosure_to_finiteReversible field y hy
theorem finite_record_failure_bound (a : I) (w v : List Bool)
    (hw : 0 < w.length) (hv : 0 < v.length) (N : ℕ) (hN : w.length+v.length ≤ N)
    (E : Set SplitField) (hE : SplitPrefixDetermined (splitPrefixCoordinates w.length) E)
    (hrecord : ∀ ω ∈ E, FiniteReversibleGenerated w.length 2 (currySplitField ω) w) :
    infiniteSplitPi a (E ∩ {ω | ¬ FiniteReversibleGenerated N 2 (currySplitField ω) v}) ≤
      infiniteSplitPi a E * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
  obtain ⟨T,hsize,hdis,hgen⟩ := finite_record_support w v hw hv
  have hs : E ∩ {ω | ¬ FiniteReversibleGenerated N 2 (currySplitField ω) v} ⊆
      E ∩ {ω | ¬ ∀ z ∈ T, ω z} := by
    intro ω hω
    refine ⟨hω.1,?_⟩
    intro hopen
    exact hω.2 (finiteReversibleGenerated_mono_cap hN
      (hgen (currySplitField ω) (hrecord ω hω.1) hopen))
  apply (measure_mono hs).trans
  rw [split_prefix_failure_measure a _ T hdis E hE]
  have hpow : (toNNReal a : ENNReal)^(v.length+1) ≤ (toNNReal a : ENNReal)^T.card := by
    apply pow_le_pow_of_le_one (zero_le : 0 ≤ (toNNReal a : ENNReal))
    · exact_mod_cast a.property.2
    · exact hsize
  exact mul_le_mul_right (tsub_le_tsub_left hpow 1) _


end

section
open Classical HordijkSteelThreshold MeasureTheory unitInterval
open scoped ENNReal

def escapedMissing (B : ℕ) (v : List Bool) : Set SplitField :=
  {ω | (∃ w, B < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w) ∧
    ¬ FiniteReversibleGenerated B 2 (currySplitField ω) v}

theorem finite_missing_determined (B : ℕ) (v : List Bool) :
    SplitPrefixDetermined (splitPrefixCoordinates B)
      {ω | ¬ FiniteReversibleGenerated B 2 (currySplitField ω) v} := by
  intro ω η he
  have ht (x y : SplitField) (hxy : ∀ z ∈ splitPrefixCoordinates B, x z = y z)
      (hg : FiniteReversibleGenerated B 2 (currySplitField x) v) :
      FiniteReversibleGenerated B 2 (currySplitField y) v :=
    finiteReversibleGenerated_transfer_prefix (M := B) le_rfl
      (fun w hw k hk => hxy (w,k) ((mem_splitPrefixCoordinates _ _).mpr ⟨hw,hk⟩)) hg
  exact not_congr ⟨ht ω η he, ht η ω fun z hz => (he z hz).symm⟩

theorem escape_mem_record_atoms {B : ℕ} (hB : 2 ≤ B) {ω : SplitField}
    (h : ∃ w, B < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w) :
    ω ∈ ⋃ i : RecordPrefixIndex, recordPrefixAtom B i := by
  have hex : ∃ M, B < M ∧ currySplitField ω ∈ reversibleRecordEvent 2 M := by
    obtain ⟨w,hw,_,hg⟩ := escape_has_bounded_record hB h
    exact ⟨w.length,hw,w,rfl,hg⟩
  let M := Nat.find hex
  have hrec : currySplitField ω ∈ firstRecordEvent 2 B M := by
    refine ⟨(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩
    intro k hBk hk hr
    exact Nat.find_min hex hk ⟨hBk,hr⟩
  exact Set.mem_iUnion.mpr ⟨⟨M,fun z => ω z.val⟩,hrec,fun _ => rfl⟩

theorem first_record_cap {B M : ℕ} (hB : 2 ≤ B) {ω : SplitField}
    (h : currySplitField ω ∈ firstRecordEvent 2 B M) : M ≤ 2*B := by
  obtain ⟨w,hw,hg⟩ := h.2.1
  have hBM := h.1
  have he : ∃ w, B < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w :=
    ⟨w,by omega,finiteReversibleGenerated_to_infinite hg⟩
  obtain ⟨v,hv,hvB,hvg⟩ := escape_has_bounded_record hB he
  by_contra hn
  exact h.2.2 v.length hv (by omega) ⟨v,rfl,hvg⟩

/-- The deterministic-cap contraction; no conditioning on future escape. -/
theorem escaped_missing_contraction (a : I) (v : List Bool) (hv : 0 < v.length)
    (B : ℕ) (hB : 2 ≤ B) :
    infiniteSplitPi a (escapedMissing (2*B+v.length) v) ≤
      infiniteSplitPi a (escapedMissing B v) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
        let C := {ω | ¬ FiniteReversibleGenerated B 2 (currySplitField ω) v}
        let D := fun i => C ∩ recordPrefixAtom B i
        have hC := finite_missing_determined B v
        have hmeas (i : RecordPrefixIndex) : MeasurableSet (D i) :=
          (measurableSet_of_splitPrefixDetermined _ C hC).inter
            (measurableSet_of_splitPrefixDetermined _ _ (recordPrefixAtom_determined B i))
        have hdis : Pairwise fun i j => Disjoint (D i) (D j) := fun i j hij =>
          (recordPrefixAtoms_disjoint B hij).mono Set.inter_subset_right Set.inter_subset_right
        have hpiece (i : RecordPrefixIndex) :
            infiniteSplitPi a (escapedMissing (2*B+v.length) v ∩ D i) ≤
              infiniteSplitPi a (D i) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
          rcases Set.eq_empty_or_nonempty (D i) with he | ⟨ω, hω⟩
          · simp [he]
          · obtain ⟨w, hw, _, hrecord⟩ := recordPrefixAtom_word B i ⟨ω, hω.2⟩
            have hBM := first_record_cap hB hω.2.1
            have hd : SplitPrefixDetermined (splitPrefixCoordinates w.length) (D i) := by
              rw [hw]
              intro η ξ he
              refine and_congr ?_ (recordPrefixAtom_determined B i η ξ he)
              apply hC
              intro z hz
              have hz' := (mem_splitPrefixCoordinates B z).mp hz
              exact he z ((mem_splitPrefixCoordinates i.1 z).mpr
                ⟨by omega, by omega⟩)
            refine (measure_mono (show escapedMissing (2*B+v.length) v ∩ D i ⊆
              D i ∩ {η | ¬ FiniteReversibleGenerated (2*B+v.length) 2 (currySplitField η) v}
              from fun η hη => ⟨hη.2, hη.1.2⟩)).trans ?_
            exact finite_record_failure_bound a w v (by omega) hv (2*B+v.length) (by omega) (D i) hd
              fun η hη => hrecord η hη.2
        have hcover : escapedMissing (2*B+v.length) v ⊆
            ⋃ i : RecordPrefixIndex, escapedMissing (2*B+v.length) v ∩ D i := by
          rintro ω hω
          obtain ⟨w, hw, hg⟩ := hω.1
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (escape_mem_record_atoms hB ⟨w, by omega, hg⟩)
          exact Set.mem_iUnion.mpr ⟨i, hω,
            fun hgen => hω.2 (finiteReversibleGenerated_mono_cap (by omega) hgen), hi⟩
        have hsub : (⋃ i : RecordPrefixIndex, D i) ⊆ escapedMissing B v := by
          rintro ω hω
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hω
          obtain ⟨w, hw, hg⟩ := hi.2.1.2.1
          exact ⟨⟨w, by have := hi.2.1.1; omega, finiteReversibleGenerated_to_infinite hg⟩, hi.1⟩
        calc
          _ ≤ infiniteSplitPi a (⋃ i : RecordPrefixIndex, escapedMissing (2*B+v.length) v ∩ D i) :=
            measure_mono hcover
          _ ≤ ∑' i : RecordPrefixIndex, infiniteSplitPi a (escapedMissing (2*B+v.length) v ∩ D i) :=
            measure_iUnion_le _
          _ ≤ ∑' i : RecordPrefixIndex, infiniteSplitPi a (D i) *
              (1-(toNNReal a : ENNReal)^(v.length+1)) := ENNReal.tsum_le_tsum hpiece
          _ = infiniteSplitPi a (⋃ i : RecordPrefixIndex, D i) *
              (1-(toNNReal a : ENNReal)^(v.length+1)) := by
            rw [ENNReal.tsum_mul_right, measure_iUnion hdis hmeas]
          _ ≤ _ := mul_le_mul_left (measure_mono hsub) _
def recordCap (ell : ℕ) : ℕ → ℕ :=
  Nat.rec 2 (fun _ cap => 2*cap+ell)

theorem recordCap_ge_two (ell j : ℕ) : 2 ≤ recordCap ell j := by
    induction j with
    | zero => rfl
    | succ j ih => simp [recordCap] at *; omega
theorem recordCap_mono_length {ell L : ℕ} (h : ell ≤ L) (j : ℕ) :
    recordCap ell j ≤ recordCap L j := by
    induction j with
    | zero => rfl
    | succ j ih => simp [recordCap] at *; omega
theorem escapedMissing_antitone (v : List Bool) : Antitone (fun B => escapedMissing B v) := by
  intro B N hBN ω hω
  obtain ⟨w,hw,hg⟩ := hω.1
  exact ⟨⟨w,by omega,hg⟩,
    fun hv => hω.2 (finiteReversibleGenerated_mono_cap hBN hv)⟩

theorem repeated_record_failure (a : I) (v : List Bool) (hv : 0 < v.length) (r : ℕ) :
    infiniteSplitPi a (escapedMissing (recordCap v.length r) v) ≤
      (1-(toNNReal a : ENNReal)^(v.length+1))^r := by
    induction r with
    | zero => simpa [pow_zero] using (prob_le_one : infiniteSplitPi a (escapedMissing (recordCap v.length 0) v) ≤ 1)
    | succ r ih =>
      calc
        _ ≤ infiniteSplitPi a (escapedMissing (recordCap v.length r) v) *
            (1-(toNNReal a : ENNReal)^(v.length+1)) :=
          escaped_missing_contraction a v hv _ (recordCap_ge_two _ _)
        _ ≤ (1-(toNNReal a : ENNReal)^(v.length+1))^r *
            (1-(toNNReal a : ENNReal)^(v.length+1)) := mul_le_mul' ih le_rfl
        _ = _ := (pow_succ _ _).symm
theorem common_cap_target_failure (a : I) (v : List Bool) (hv : 0 < v.length)
    (L : ℕ) (hvL : v.length ≤ L) (r : ℕ) :
    infiniteSplitPi a (escapedMissing (recordCap L r) v) ≤
      (1-(toNNReal a : ENNReal)^(L+1))^r := by
  have hp : (toNNReal a : ENNReal)^(L+1) ≤ (toNNReal a : ENNReal)^(v.length+1) := by
    apply pow_le_pow_of_le_one (zero_le : 0 ≤ (toNNReal a : ENNReal))
    · exact_mod_cast a.property.2
    · omega
  exact ((measure_mono (escapedMissing_antitone v (recordCap_mono_length hvL r))).trans
    (repeated_record_failure a v hv r)).trans
      (pow_le_pow_left' (tsub_le_tsub_left hp 1) r)

/-- A finite target family, with no independence asserted between targets. -/
theorem finite_seed_failure (a : I) (seed : Finset (List Bool)) (L : ℕ)
    (hseed : ∀ v ∈ seed, 0 < v.length ∧ v.length ≤ L) (r : ℕ) :
    infiniteSplitPi a {ω |
      (∃ w, recordCap L r < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w) ∧
      ¬ ∀ v ∈ seed, FiniteReversibleGenerated (recordCap L r) 2 (currySplitField ω) v} ≤
      (seed.card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r := by
  have hsub : {ω : SplitField |
      (∃ w, recordCap L r < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w) ∧
      ¬ ∀ v ∈ seed, FiniteReversibleGenerated (recordCap L r) 2 (currySplitField ω) v} ⊆
      ⋃ v ∈ seed, escapedMissing (recordCap L r) v := by
    intro ω hω
    push Not at hω
    obtain ⟨v,hv,hmissing⟩ := hω.2
    exact Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨hv,hω.1,hmissing⟩⟩
  calc
    _ ≤ infiniteSplitPi a (⋃ v ∈ seed, escapedMissing (recordCap L r) v) := measure_mono hsub
    _ ≤ ∑ v ∈ seed, infiniteSplitPi a (escapedMissing (recordCap L r) v) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ seed, (1-(toNNReal a : ENNReal)^(L+1))^r := by
      apply Finset.sum_le_sum
      intro v hv
      exact common_cap_target_failure a v (hseed v hv).1 L (hseed v hv).2 r
    _ = _ := by simp


end

section
open Classical HordijkSteelThreshold MeasureTheory unitInterval RAF.Polymer
open scoped ENNReal

/-- Literal infinite escape probability; first escape gives its finite cap 2K. -/
noncomputable def splitEscapeProbability (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w}

theorem explicit_split_truncation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) (r : ℕ) :
    let L := 10*seedIndex q hq hq1 m
    splitEscapeProbability a (recordCap L r) ≤ staticSurvival a + (m : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r := by
            let L := 10*seedIndex q hq hq1 m
            let K := recordCap L r
            let E := {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w}
            let H := {ω | ∀ v ∈ actualBinaryWords L, FiniteReversibleGenerated K 2 (currySplitField ω) v}
            let G := {ω | ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 (currySplitField ω) v}
            have hseed : ∀ v ∈ actualBinaryWords L, 0 < v.length ∧ v.length ≤ L := by
              intro v hv
              have hh := (mem_actualBinaryWords v L).mp hv
              exact ⟨List.length_pos_iff.mpr hh.1,hh.2⟩
            have hbad : infiniteSplitPi a (E ∩ Hᶜ) ≤
                ((actualBinaryWords L).card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r :=
              finite_seed_failure a (actualBinaryWords L) L hseed r
            have hgood : infiniteSplitPi a H ≤ staticSurvival a + (m : ENNReal)⁻¹ := by
              have hi := effective_seed_probability_le_survival q hq hq1 m hm a ha
              have hmeas : MeasurableSet {field : InfiniteSplitEnvironment |
                  ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 field v} := by
                have he : {field : InfiniteSplitEnvironment |
                    ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 field v} =
                    ⋂ v ∈ actualBinaryWords L, {field | InfiniteReversibleGenerated 2 field v} := by
                  ext field
                  simp
                rw [he]
                exact MeasurableSet.biInter (Finset.countable_toSet _) fun v _ =>
                  measurableSet_infiniteReversibleGenerated 2 v
              rw [infiniteStaticMeasure, Measure.map_apply measurable_currySplitField
                hmeas] at hi
              apply (measure_mono (show H ⊆ G from ?_)).trans hi
              intro ω hω v hv
              exact finiteReversibleGenerated_to_infinite (hω v hv)
            have hs : E ⊆ (E ∩ Hᶜ) ∪ H := by
              intro ω hω
              by_cases hh : ω ∈ H
              · exact Or.inr hh
              · exact Or.inl ⟨hω,hh⟩
            calc
              splitEscapeProbability a K ≤ infiniteSplitPi a ((E ∩ Hᶜ) ∪ H) := measure_mono hs
              _ ≤ infiniteSplitPi a (E ∩ Hᶜ) + infiniteSplitPi a H := measure_union_le _ _
              _ ≤ _ := by simpa [add_comm] using add_le_add hbad hgood
end

section
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold RAFReactionQuotient
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal

/-- Explicit seed cutoff transported through the source's bounded-fibre domination. -/
theorem effective_quotient_bulk (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    let hhalf : 0 < q/2 := by positivity
    let hhalf1 : q/2 ≤ 1 := by linarith
    let L := 10*seedIndex (q/2) hhalf hhalf1 m
    ∀ a : I, rationalParameter q hq.le hq1 ≤ a → ∀ n : ℕ, 0 < n →
      quotientStaticMeasure n a {ω |
        m*(quotientClosure n L (quotientOpen ω)).card <
          (m-1)*Fintype.card (Molecule n)} ≤ (m : ENNReal)⁻¹ := by
  dsimp only
  have hhalf : 0 < q/2 := by positivity
  have hhalf1 : q/2 ≤ 1 := by linarith
  let a0 := rationalParameter q hq.le hq1
  let L := 10*seedIndex (q/2) hhalf hhalf1 m
  have heq : rationalParameter (q/2) hhalf.le hhalf1 = halfParameter a0 := by
    apply Subtype.ext
    simp [rationalParameter,halfParameter,a0]
  have hbulk := effective_static_bulk (q/2) hhalf hhalf1 m hm
  dsimp only at hbulk
  rw [heq] at hbulk
  intro a ha n hn
  let E := fun ω : RepositoryChannel n → Prop =>
    m*(quotientClosure n L (quotientOpen ω)).card < (m-1)*Fintype.card (Molecule n)
  have hi := product_decreasing_mono
    (fibreParameter (@splitToQuotient n) (halfParameter a0)) (fun _ => a)
    (fun j => (fibreParameter_half_le splitToQuotient a0 j
      (by
        convert split_fibre_le_two j using 1
        congr 1
        ext r
        simp)).trans ha)
    E (quotient_mass_failure_antitone n L m)
  have he := fieldOR_map (@splitToQuotient n) (halfParameter a0)
  rw [← he, Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at hi
  have hevent : {ω : Reaction n → Prop | E (fieldOR splitToQuotient ω)} =
      {ω | m*(temporaryReactionClosure L (staticOpenReactions ω)).card <
        (m-1)*Fintype.card (Molecule n)} := by
    ext ω
    simp only [Set.mem_ofPred_eq,E,quotientClosure_OR]
  change quotientStaticMeasure n a {ω | E ω} ≤
    RAFEmergenceApprox.Generic.colLaw (Reaction n) (halfParameter a0)
      {ω | E (fieldOR splitToQuotient ω)} at hi
  rw [hevent] at hi
  apply hi.trans
  simpa only [staticReactionMeasure,Measure.infinitePi_eq_pi,
    RAFEmergenceApprox.Generic.colLaw] using hbulk n hn


end

section
open Classical Filter MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold RAFReactionQuotient
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

theorem effective_quotient_seed_survival (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) :
    let hhalf : 0 < q/2 := by positivity
    let hhalf1 : q/2 ≤ 1 := by linarith
    let L := 10*seedIndex (q/2) hhalf hhalf1 m
    ∀ b : I, rationalParameter q hq.le hq1 ≤ b →
      quotientInfiniteMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ≤ quotientSurvival b + (m : ENNReal)⁻¹ := by
  dsimp only
  have hhalf : 0 < q/2 := by positivity
  have hhalf1 : q/2 ≤ 1 := by linarith
  let L := 10*seedIndex (q/2) hhalf hhalf1 m
  have hbulk := effective_quotient_bulk q hq hq1 m (by omega)
  intro b hb
  have hK (K : ℕ) :
      quotientInfiniteMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ≤
      quotientStaticMeasure (2*(K+2)) b (quotientEscapeEvent 2 K) + (m : ENNReal)⁻¹ := by
    apply le_of_tendsto (quotient_finite_seed_tendsto 2 b (actualBinaryWords L))
    filter_upwards [(tendsto_atTop.mp card_molecule_tendsto_atTop)
      (m*Fintype.card (Molecule (K+2))+1),eventually_ge_atTop 1] with N hlarge hN
    have hmass : quotientStaticMeasure N b {q | (m-1)*Fintype.card (Molecule N) ≤
        m*(quotientClosure N 2 (quotientOpen q)).card} ≤
        quotientStaticMeasure (2*(K+2)) b (quotientEscapeEvent 2 K) := by
      rw [quotient_escape_measure_eq]
      apply (measure_mono (show {q : RepositoryChannel N → Prop |
        (m-1)*Fintype.card (Molecule N) ≤ m*(quotientClosure N 2 (quotientOpen q)).card} ⊆
        {q | ∃ x ∈ quotientClosure N 2 (quotientOpen q), K+2 < molLength x} from ?_)).trans
        (quotient_capped_escape_le N K b)
      intro q hq
      by_contra h
      have hs : quotientClosure N 2 (quotientOpen q) ⊆ binaryFood N (K+2) := by
        intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.le_of_not_gt (fun hl => h ⟨x,hx,hl⟩)⟩
      have hc := (Finset.card_le_card hs).trans (binaryFood_card_le_cutoff N (K+2))
      change (m-1)*Fintype.card (Molecule N) ≤ m*(quotientClosure N 2 (quotientOpen q)).card at hq
      have hmult : Fintype.card (Molecule N) ≤ (m-1)*Fintype.card (Molecule N) := by
        have hh := Nat.mul_le_mul_right (Fintype.card (Molecule N)) (show 1 ≤ m-1 by omega)
        simpa using hh
      nlinarith
    exact (quotient_same_field_seed_mass N L m b).trans
      (add_le_add hmass (hbulk b hb N (by omega)))
  exact ge_of_tendsto' ((quotient_escape_tendsto b).add_const (m : ENNReal)⁻¹) hK


end

section
open Classical HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete MeasureTheory unitInterval
open scoped ENNReal

theorem quotient_finite_record_support (w v : List Bool) (hw : 0 < w.length) (hv : 0 < v.length) :
    ∃ T : Finset (List Bool × ℕ), T.card ≤ v.length+1 ∧
      Disjoint (splitPrefixCoordinates w.length) T ∧
      ∀ ω : SplitField, FiniteReversibleGenerated w.length 2 (quotientField ω) w →
        (∀ z ∈ T, ω z) → FiniteReversibleGenerated (w.length+v.length) 2 (quotientField ω) v := by
      let N := w.length+v.length
      obtain ⟨S,hsize,hband,hgen⟩ := target_trial_support (N := N) w v hw hv le_rfl
      let T := S.image fun r => canonicalIndex (literalSplitCoordinate r)
      refine ⟨T,(Finset.card_image_le).trans hsize,?_,?_⟩
      · apply Finset.disjoint_left.mpr
        intro z hz ht
        obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ht
        have hl := (mem_splitPrefixCoordinates w.length _).mp hz
        rw [canonicalIndex_product] at hl
        have hb := (hband r hr).1
        change (moleculeWord (RAF.Concrete.reactionProduct r)).length ≤ w.length ∧ _ at hl
        rw [moleculeWord_length] at hl
        omega
      · intro ω hrecord hopen
        have hgN := finiteReversibleGenerated_mono_cap (show w.length ≤ N by dsimp [N]; omega) hrecord
        obtain ⟨x,hx,he⟩ := finiteReversible_to_literalClosure hgN
        have hs : S ⊆ restrictedSplitReactions N (quotientField ω) := by
          intro r hr
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hopen _ (Finset.mem_image.mpr ⟨r,hr,rfl⟩)⟩
        obtain ⟨y,hy,hev⟩ := hgen (restrictedSplitReactions N (quotientField ω)) hs x hx he
        simpa [hev] using literalClosure_to_finiteReversible (quotientField ω) y hy
theorem quotient_finite_record_failure_bound (a : I) (w v : List Bool)
    (hw : 0 < w.length) (hv : 0 < v.length) (N : ℕ) (hN : w.length+v.length ≤ N)
    (E : Set SplitField) (hE : SplitPrefixDetermined (splitPrefixCoordinates w.length) E)
    (hrecord : ∀ ω ∈ E, FiniteReversibleGenerated w.length 2 (quotientField ω) w) :
    infiniteSplitPi a (E ∩ {ω | ¬ FiniteReversibleGenerated N 2 (quotientField ω) v}) ≤
      infiniteSplitPi a E * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
  obtain ⟨T,hsize,hdis,hgen⟩ := quotient_finite_record_support w v hw hv
  have hs : E ∩ {ω | ¬ FiniteReversibleGenerated N 2 (quotientField ω) v} ⊆
      E ∩ {ω | ¬ ∀ z ∈ T, ω z} := by
    intro ω hω
    refine ⟨hω.1,?_⟩
    intro hopen
    exact hω.2 (finiteReversibleGenerated_mono_cap hN
      (hgen ω (hrecord ω hω.1) hopen))
  apply (measure_mono hs).trans
  rw [split_prefix_failure_measure a _ T hdis E hE]
  have hpow : (toNNReal a : ENNReal)^(v.length+1) ≤ (toNNReal a : ENNReal)^T.card := by
    apply pow_le_pow_of_le_one (zero_le : 0 ≤ (toNNReal a : ENNReal))
    · exact_mod_cast a.property.2
    · exact hsize
  exact mul_le_mul_right (tsub_le_tsub_left hpow 1) _


end

section
open Classical HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval
open scoped ENNReal

def quotientEscapedMissing (B : ℕ) (v : List Bool) : Set SplitField :=
  {ω | (∃ w, B < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w) ∧
    ¬ FiniteReversibleGenerated B 2 (quotientField ω) v}

theorem quotient_finite_missing_determined (B : ℕ) (v : List Bool) :
    SplitPrefixDetermined (splitPrefixCoordinates B)
      {ω | ¬ FiniteReversibleGenerated B 2 (quotientField ω) v} := by
    intro ω η he
    apply finite_missing_determined B v (fun z => ω (canonicalIndex z))
      fun z => η (canonicalIndex z)
    intro z hz
    exact he (canonicalIndex z) (canonicalIndex_prefix hz)
/-- The deterministic-cap contraction; no conditioning on future escape. -/
theorem quotient_escaped_missing_contraction (a : I) (v : List Bool) (hv : 0 < v.length)
    (B : ℕ) (hB : 2 ≤ B) :
    infiniteSplitPi a (quotientEscapedMissing (2*B+v.length) v) ≤
      infiniteSplitPi a (quotientEscapedMissing B v) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
                let C := {ω | ¬ FiniteReversibleGenerated B 2 (quotientField ω) v}
                let D := fun i => C ∩ quotientRecordAtom B i
                have hC := quotient_finite_missing_determined B v
                have hmeasC := measurableSet_of_splitPrefixDetermined _ C hC
                have hmeas (i : RecordPrefixIndex) : MeasurableSet (D i) :=
                  hmeasC.inter (measurableSet_of_splitPrefixDetermined _ _ (quotientRecordAtom_determined B i))
                have hdis : Pairwise fun i j => Disjoint (D i) (D j) := by
                  intro i j hij
                  exact (quotientRecordAtoms_disjoint B hij).mono Set.inter_subset_right Set.inter_subset_right
                have hpiece (i : RecordPrefixIndex) :
                    infiniteSplitPi a (quotientEscapedMissing (2*B+v.length) v ∩ D i) ≤
                      infiniteSplitPi a (D i) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
                  by_cases hn : (D i).Nonempty
                  · obtain ⟨ω,hω⟩ := hn
                    have hMB := first_record_cap (ω := fun z => ω (canonicalIndex z)) hB hω.2.1
                    obtain ⟨w,hw,hBw,hrecord⟩ := recordPrefixAtom_word B i ⟨fun z => ω (canonicalIndex z),hω.2⟩
                    have hd : SplitPrefixDetermined (splitPrefixCoordinates w.length) (D i) := by
                      rw [hw]
                      intro η ξ he
                      apply and_congr
                      · apply hC
                        intro z hz
                        have hz' := (mem_splitPrefixCoordinates B z).mp hz
                        exact he z ((mem_splitPrefixCoordinates i.1 z).mpr ⟨by omega,by omega⟩)
                      · exact quotientRecordAtom_determined B i η ξ he
                    apply (measure_mono (show quotientEscapedMissing (2*B+v.length) v ∩ D i ⊆
                      D i ∩ {η | ¬ FiniteReversibleGenerated (2*B+v.length) 2 (quotientField η) v}
                      from fun η hη => ⟨hη.2,hη.1.2⟩)).trans
                    exact quotient_finite_record_failure_bound a w v (by omega) hv (2*B+v.length)
                      (by omega) (D i) hd fun η hη => hrecord (fun z => η (canonicalIndex z)) hη.2
                  · have he : D i = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
                    simp [he]
                have hcover : quotientEscapedMissing (2*B+v.length) v ⊆
                    ⋃ i : RecordPrefixIndex, quotientEscapedMissing (2*B+v.length) v ∩ D i := by
                  intro ω hω
                  obtain ⟨w,hw,hg⟩ := hω.1
                  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (escape_mem_record_atoms (ω := fun z => ω (canonicalIndex z)) hB ⟨w,by omega,hg⟩)
                  exact Set.mem_iUnion.mpr ⟨i,hω,
                    fun hgen => hω.2 (finiteReversibleGenerated_mono_cap (by omega) hgen),hi⟩
                have hsub : (⋃ i : RecordPrefixIndex, D i) ⊆ quotientEscapedMissing B v := by
                  intro ω hω
                  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hω
                  obtain ⟨w,hw,hg⟩ := hi.2.1.2.1
                  exact ⟨⟨w,by have hb := hi.2.1.1; omega,finiteReversibleGenerated_to_infinite hg⟩,hi.1⟩
                calc
                  _ ≤ infiniteSplitPi a (⋃ i : RecordPrefixIndex, quotientEscapedMissing (2*B+v.length) v ∩ D i) := measure_mono hcover
                  _ ≤ ∑' i : RecordPrefixIndex, infiniteSplitPi a (quotientEscapedMissing (2*B+v.length) v ∩ D i) := measure_iUnion_le _
                  _ ≤ ∑' i : RecordPrefixIndex, infiniteSplitPi a (D i) *
                      (1-(toNNReal a : ENNReal)^(v.length+1)) := ENNReal.tsum_le_tsum hpiece
                  _ = infiniteSplitPi a (⋃ i : RecordPrefixIndex, D i) *
                      (1-(toNNReal a : ENNReal)^(v.length+1)) := by
                    rw [ENNReal.tsum_mul_right,measure_iUnion hdis hmeas]
                  _ ≤ _ := mul_le_mul_left (measure_mono hsub) _
theorem quotientEscapedMissing_antitone (v : List Bool) : Antitone (fun B => quotientEscapedMissing B v) := by
  intro B N hBN ω hω
  obtain ⟨w,hw,hg⟩ := hω.1
  exact ⟨⟨w,by omega,hg⟩,
    fun hv => hω.2 (finiteReversibleGenerated_mono_cap hBN hv)⟩

theorem quotient_repeated_record_failure (a : I) (v : List Bool) (hv : 0 < v.length) (r : ℕ) :
    infiniteSplitPi a (quotientEscapedMissing (recordCap v.length r) v) ≤
      (1-(toNNReal a : ENNReal)^(v.length+1))^r := by
    induction r with
    | zero => simpa [pow_zero] using (prob_le_one : infiniteSplitPi a (quotientEscapedMissing (recordCap v.length 0) v) ≤ 1)
    | succ r ih =>
      calc
        _ ≤ infiniteSplitPi a (quotientEscapedMissing (recordCap v.length r) v) *
            (1-(toNNReal a : ENNReal)^(v.length+1)) :=
          quotient_escaped_missing_contraction a v hv _ (recordCap_ge_two _ _)
        _ ≤ (1-(toNNReal a : ENNReal)^(v.length+1))^r *
            (1-(toNNReal a : ENNReal)^(v.length+1)) := mul_le_mul' ih le_rfl
        _ = _ := (pow_succ _ _).symm
theorem quotient_common_cap_target_failure (a : I) (v : List Bool) (hv : 0 < v.length)
    (L : ℕ) (hvL : v.length ≤ L) (r : ℕ) :
    infiniteSplitPi a (quotientEscapedMissing (recordCap L r) v) ≤
      (1-(toNNReal a : ENNReal)^(L+1))^r := by
  have hp : (toNNReal a : ENNReal)^(L+1) ≤ (toNNReal a : ENNReal)^(v.length+1) := by
    apply pow_le_pow_of_le_one (zero_le : 0 ≤ (toNNReal a : ENNReal))
    · exact_mod_cast a.property.2
    · omega
  exact ((measure_mono (quotientEscapedMissing_antitone v (recordCap_mono_length hvL r))).trans
    (quotient_repeated_record_failure a v hv r)).trans
      (pow_le_pow_left' (tsub_le_tsub_left hp 1) r)

/-- A finite target family, with no independence asserted between targets. -/
theorem quotient_finite_seed_failure (a : I) (seed : Finset (List Bool)) (L : ℕ)
    (hseed : ∀ v ∈ seed, 0 < v.length ∧ v.length ≤ L) (r : ℕ) :
    infiniteSplitPi a {ω |
      (∃ w, recordCap L r < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w) ∧
      ¬ ∀ v ∈ seed, FiniteReversibleGenerated (recordCap L r) 2 (quotientField ω) v} ≤
      (seed.card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r := by
  have hsub : {ω : SplitField |
      (∃ w, recordCap L r < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w) ∧
      ¬ ∀ v ∈ seed, FiniteReversibleGenerated (recordCap L r) 2 (quotientField ω) v} ⊆
      ⋃ v ∈ seed, quotientEscapedMissing (recordCap L r) v := by
    intro ω hω
    push Not at hω
    obtain ⟨v,hv,hmissing⟩ := hω.2
    exact Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨hv,hω.1,hmissing⟩⟩
  calc
    _ ≤ infiniteSplitPi a (⋃ v ∈ seed, quotientEscapedMissing (recordCap L r) v) := measure_mono hsub
    _ ≤ ∑ v ∈ seed, infiniteSplitPi a (quotientEscapedMissing (recordCap L r) v) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ seed, (1-(toNNReal a : ENNReal)^(L+1))^r := by
      apply Finset.sum_le_sum
      intro v hv
      exact quotient_common_cap_target_failure a v (hseed v hv).1 L (hseed v hv).2 r
    _ = _ := by simp


end

section
open Classical RAFReactionQuotient HordijkSteelThreshold MeasureTheory unitInterval RAF.Polymer
open scoped ENNReal

/-- Literal infinite escape probability; first escape gives its finite cap 2K. -/
noncomputable def quotientEscapeProbability (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w}

theorem explicit_quotient_truncation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) (r : ℕ) :
    let hhalf : 0 < q/2 := by positivity
    let hhalf1 : q/2 ≤ 1 := by linarith
    let L := 10*seedIndex (q/2) hhalf hhalf1 m
    quotientEscapeProbability a (recordCap L r) ≤ quotientSurvival a + (m : ENNReal)⁻¹ +
      ((actualBinaryWords L).card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r := by
  dsimp only
  have hhalf : 0 < q/2 := by positivity
  have hhalf1 : q/2 ≤ 1 := by linarith
  let L := 10*seedIndex (q/2) hhalf hhalf1 m
  let K := recordCap L r
  let E : Set SplitField := {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w}
  let H : Set SplitField := {ω | ∀ v ∈ actualBinaryWords L, FiniteReversibleGenerated K 2 (quotientField ω) v}
  let G : Set SplitField := {ω | ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 (quotientField ω) v}
  have hseed : ∀ v ∈ actualBinaryWords L, 0 < v.length ∧ v.length ≤ L := by
    intro v hv
    have hh := (mem_actualBinaryWords v L).mp hv
    exact ⟨List.length_pos_iff.mpr hh.1,hh.2⟩
  have hbad : infiniteSplitPi a (E ∩ Hᶜ) ≤
      ((actualBinaryWords L).card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r :=
    quotient_finite_seed_failure a (actualBinaryWords L) L hseed r
  have hgood : infiniteSplitPi a H ≤ quotientSurvival a + (m : ENNReal)⁻¹ := by
    have hi := effective_quotient_seed_survival q hq hq1 m hm a ha
    have hmeas : MeasurableSet {field : InfiniteSplitEnvironment |
        ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 field v} := by
      have he : {field : InfiniteSplitEnvironment |
          ∀ v ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 field v} =
          ⋂ v ∈ actualBinaryWords L, {field | InfiniteReversibleGenerated 2 field v} := by
        ext field
        simp
      rw [he]
      exact MeasurableSet.biInter (Finset.countable_toSet _) (fun v _ =>
        measurableSet_infiniteReversibleGenerated 2 v)
    rw [quotientInfiniteMeasure, Measure.map_apply quotientField_measurable
      hmeas] at hi
    apply (measure_mono (show H ⊆ G from ?_)).trans hi
    intro ω hω v hv
    exact finiteReversibleGenerated_to_infinite (hω v hv)
  have hs : E ⊆ (E ∩ Hᶜ) ∪ H := by
    intro ω hω
    by_cases hh : ω ∈ H
    · exact Or.inr hh
    · exact Or.inl ⟨hω,hh⟩
  calc
    quotientEscapeProbability a K ≤ infiniteSplitPi a ((E ∩ Hᶜ) ∪ H) := measure_mono hs
    _ ≤ infiniteSplitPi a (E ∩ Hᶜ) + infiniteSplitPi a H := measure_union_le _ _
    _ ≤ _ := by simpa only [add_comm] using add_le_add hbad hgood


end

section
open Classical HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF.Polymer
open scoped ENNReal

theorem split_escape_finite (a : I) (K : ℕ) (hK : 2 ≤ K) :
    splitEscapeProbability a K =
      staticReactionMeasure (2*((K-2)+2)) a (staticEscapeEvent 2 (K-2)) := by
  unfold splitEscapeProbability
  rw [finite_static_escape_measure_eq, infiniteStaticMeasure,
    Measure.map_apply measurable_currySplitField (measurableSet_reversibleEscapeEvent 2 (K-2))]
  congr 1
  ext ω
  change (∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w) ↔ _
  rw [Set.mem_preimage, reversibleEscapeEvent_iff]
  have he : K-2+2 = K := by omega
  rw [he]

theorem split_survival_le_escape (a : I) (K : ℕ) : staticSurvival a ≤ splitEscapeProbability a K := by
  rw [staticSurvival, infiniteStaticMeasure,
    Measure.map_apply measurable_currySplitField (measurableSet_reversibleUnbounded 2)]
  apply measure_mono
  intro ω hω
  exact hω K

theorem quotient_escape_finite (a : I) (K : ℕ) (hK : 2 ≤ K) :
    quotientEscapeProbability a K =
      quotientStaticMeasure (2*((K-2)+2)) a (quotientEscapeEvent 2 (K-2)) := by
  unfold quotientEscapeProbability
  rw [quotient_escape_measure_eq, quotientInfiniteMeasure,
    Measure.map_apply quotientField_measurable (measurableSet_reversibleEscapeEvent 2 (K-2))]
  congr 1
  ext ω
  change (∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w) ↔ _
  rw [Set.mem_preimage, reversibleEscapeEvent_iff]
  have he : K-2+2 = K := by omega
  rw [he]

theorem quotient_survival_le_escape (a : I) (K : ℕ) :
    quotientSurvival a ≤ quotientEscapeProbability a K := by
  apply measure_mono
  intro ω hω
  exact hω K


end

section
open HordijkSteelThreshold RAF.Polymer RAF.Concrete

/-- A finite executable evaluator, using the literal source's closure iteration. -/
def computedClosure (N L : ℕ) (S : Finset (Reaction N)) : Finset (Molecule N) :=
  revClosureAt (binaryPolymerCRS N L) S (Fintype.card (Molecule N))

theorem closure_growth_or_stable {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (k : ℕ) :
    k ≤ (revClosureAt Q S k).card ∨ revClosureAt Q S (k+1) = revClosureAt Q S k := by
  induction k with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ k ih =>
    rcases ih with hg | he
    · by_cases he : revClosureAt Q S (k+1) = revClosureAt Q S k
      · right
        change revClosureStep Q S (revClosureAt Q S (k+1)) = _
        rw [he]
        exact he
      · left
        have hs := revClosureAt_mono_stage Q S (Nat.le_succ k)
        have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs,Ne.symm he⟩)
        exact Nat.succ_le_of_lt (lt_of_le_of_lt hg hcard)
    · right
      change revClosureStep Q S (revClosureAt Q S (k+1)) = _
      rw [he]
      exact he

theorem closure_stable_at_card {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) :
    revClosureAt Q S (Fintype.card M+1) = revClosureAt Q S (Fintype.card M) := by
  rcases closure_growth_or_stable Q S (Fintype.card M) with hg | he
  · have hu := Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) hg)
    apply Finset.Subset.antisymm
    · rw [hu]
      exact Finset.subset_univ _
    · exact revClosureAt_mono_stage Q S (Nat.le_succ _)
  · exact he

theorem closure_stable_after_card {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (j : ℕ) :
    revClosureAt Q S (Fintype.card M+j) = revClosureAt Q S (Fintype.card M) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, revClosureAt, ih]
    exact closure_stable_at_card Q S

/-- Exact semantics: the executable finite iteration equals the existing closure. -/
theorem computedClosure_eq (N L : ℕ) (S : Finset (Reaction N)) :
    computedClosure N L S = temporaryReactionClosure L S := by
  ext x
  rw [mem_temporaryReactionClosure]
  constructor
  · intro hx
    exact ⟨Fintype.card (Molecule N),hx⟩
  · rintro ⟨k,hk⟩
    by_cases h : k ≤ Fintype.card (Molecule N)
    · exact revClosureAt_mono_stage _ _ h hk
    · have he : k = Fintype.card (Molecule N)+(k-Fintype.card (Molecule N)) := by omega
      rw [he,closure_stable_after_card] at hk
      exact hk


end

section
open Classical HordijkSteelThreshold MeasureTheory unitInterval
open scoped ENNReal

def rationalEventProbability (J : Type*) [Fintype J] [DecidableEq J] (q : ℚ)
    (event : (J → Bool) → Bool) : ℚ :=
  ∑ ω : J → Bool, if event ω then ∏ j, if ω j then q else 1-q else 0

/-- Exact probability semantics for an arbitrary executable Boolean event. -/
theorem rationalEventProbability_correct (J : Type*) [Fintype J] [DecidableEq J] (q : ℚ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (event : (J → Bool) → Bool) :
    ((Measure.pi (fun _ : J => ambientCoordLaw (rationalParameter q hq hq1)))
      {ω | event (fun j => decide (ω j))}).toReal =
      (rationalEventProbability J q event : ℝ) := by
                    let a := rationalParameter q hq hq1
                    let μ := Measure.pi fun _ : J => ambientCoordLaw a
                    let E : Set (J → Prop) := {ω | event fun j => decide (ω j)}
                    let F := Finset.univ.filter fun ω => ω ∈ E
                    have hF : (F : Set (J → Prop)) = E := by ext ω; simp [F]
                    have hatom (ω : J → Prop) : μ {ω} = (∏ j, staticAtomWeight a (ω j) : NNReal) := by
                      rw [Measure.pi_singleton]
                      simp [ambientCoordLaw_atom, ENNReal.ofNNReal_finsetProd]
                    have he : μ E = ((∑ ω ∈ F, ∏ j, staticAtomWeight a (ω j) : NNReal) : ENNReal) := by
                      rw [← hF, ← sum_measure_singleton]
                      simp [hatom, ENNReal.ofNNReal_finsetSum]
                    change (μ E).toReal = _
                    rw [he]
                    simp only [ENNReal.coe_toReal, NNReal.coe_sum, NNReal.coe_prod]
                    rw [Finset.sum_filter]
                    let e : (J → Bool) ≃ (J → Prop) := Equiv.piCongrRight fun _ => Equiv.propEquivBool.symm
                    rw [← e.sum_comp]
                    have hw (P : Prop) : (staticAtomWeight a P : ℝ) = if P then (q : ℝ) else 1-q := by
                      by_cases hP : P <;> simp [staticAtomWeight,hP,a,rationalParameter]
                    simp [hw]
                    simp [rationalEventProbability,e,Equiv.propEquivBool,E]
                    apply Finset.sum_congr rfl
                    intro ω _
                    by_cases hev : event ω = true
                    · simp only [hev,ite_true]
                      push_cast
                      apply Finset.prod_congr rfl
                      intro j _
                      by_cases hbit : ω j = true <;> simp [hbit]
                    · simp [hev]
end

section
open HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open MeasureTheory

def splitEscapeBool (N K : ℕ) (ω : Reaction N → Bool) : Bool :=
  decide (∃ x ∈ computedClosure N 2 (Finset.univ.filter (fun r => ω r)), K < molLength x)

def quotientEscapeBool (N K : ℕ) (ω : RepositoryChannel N → Bool) : Bool :=
  splitEscapeBool N K (fun r => ω (splitToQuotient r))

def splitEscapeEval (q : ℚ) (K : ℕ) : ℚ :=
  rationalEventProbability (Reaction (2*(K+2))) q (splitEscapeBool _ (K+2))

def quotientEscapeEval (q : ℚ) (K : ℕ) : ℚ :=
  rationalEventProbability (RepositoryChannel (2*(K+2))) q (quotientEscapeBool _ (K+2))

theorem splitEscapeEval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) :
    (splitEscapeEval q K : ℝ) =
      (staticReactionMeasure (2*(K+2)) (rationalParameter q hq hq1) (staticEscapeEvent 2 K)).toReal := by
      classical
      have h := rationalEventProbability_correct (Reaction (2*(K+2))) q hq hq1 (splitEscapeBool _ (K+2))
      have he : {ω : Reaction (2*(K+2)) → Prop | splitEscapeBool _ (K+2) fun r => decide (ω r)} =
          staticEscapeEvent 2 K := by
        ext ω
        simp [splitEscapeBool,computedClosure_eq,staticEscapeEvent,staticOpenReactions,moleculeWord_length]
      rw [he] at h
      simpa [splitEscapeEval,staticReactionMeasure,Measure.infinitePi_eq_pi] using h.symm
theorem quotientEscapeEval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) :
    (quotientEscapeEval q K : ℝ) =
      (quotientStaticMeasure (2*(K+2)) (rationalParameter q hq hq1) (quotientEscapeEvent 2 K)).toReal := by
        classical
        have h := rationalEventProbability_correct (RepositoryChannel (2*(K+2))) q hq hq1
          (quotientEscapeBool _ (K+2))
        have he : {ω : RepositoryChannel (2*(K+2)) → Prop |
            quotientEscapeBool _ (K+2) fun r => decide (ω r)} = quotientEscapeEvent 2 K := by
          ext ω
          simp only [Set.mem_ofPred_eq,quotientEscapeBool,splitEscapeBool,decide_eq_true_eq,
            computedClosure_eq]
          change (∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions fun r => ω (splitToQuotient r)),
            K+2 < molLength x) ↔ _
          rw [← quotientClosure_pullback]
          simp [quotientEscapeEvent,Set.mem_ofPred_eq,moleculeWord_length]
        rw [he] at h
        exact h.symm
end

section
open HordijkSteelThreshold MeasureTheory unitInterval
open scoped ENNReal

theorem real_record_budget (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ)
    (ε : ℚ) (hε : 0 < ε) :
    ((actualBinaryWords L).card : ℝ) * (1-(q : ℝ)^(L+1))^(recordIndex q hq hq1 L ε hε) ≤
      (ε : ℝ)/4 := by
    have h := (recordIndex_error q hq hq1 L ε hε).2
    have hr := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at hr
    have hc : (actualBinaryWords L).card ≤ 2^(L+1) := by
      rw [actualBinaryWords_card]
      exact Nat.sub_le _ _
    have ht : (0 : ℝ) ≤ 1-(q : ℝ)^(L+1) := by
      exact_mod_cast (repair_ratio q hq hq1 L).1
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (pow_nonneg ht _)).trans hr
theorem real_error_of_bound (e S : ENNReal) (hS : S ≠ ∞) (m L r : ℕ) (hm : 0 < m)
    (a : I) (h : e ≤ S+(m : ENNReal)⁻¹+
      ((actualBinaryWords L).card : ENNReal)*(1-(toNNReal a : ENNReal)^(L+1))^r) :
    e.toReal ≤ S.toReal+1/(m : ℝ)+
      ((actualBinaryWords L).card : ℝ)*(1-(a : ℝ)^(L+1))^r := by
    have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    have hp : (toNNReal a : ENNReal)^(L+1) ≤ 1 :=
      pow_le_one₀ (by positivity) (by exact_mod_cast a.property.2)
    have ht : ((actualBinaryWords L).card : ENNReal)*(1-(toNNReal a : ENNReal)^(L+1))^r ≠ ∞ := by
      finiteness
    have hi : (m : ENNReal)⁻¹ ≠ ∞ := by simp [hm0]
    have hsum := ENNReal.add_ne_top.mpr ⟨hS,hi⟩
    have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hsum,ht⟩) h
    rw [ENNReal.toReal_add hsum ht, ENNReal.toReal_add hS hi,
      ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hp (by simp)] at hr
    simpa [one_div] using hr

end

section
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory

def splitEvaluationCap (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  let L := 10*seedIndex q hq hq1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)

def splitCertifiedInterval (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  let e := splitEscapeEval q (splitEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)

/-- An executable terminating rational enclosure for the actual split survival profile. -/
theorem splitCertifiedInterval_correct (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ε : ℚ) (hε : 0 < ε) :
    let interval := splitCertifiedInterval q hq hq1 ε hε
    (interval.1 : ℝ) ≤ (staticSurvival (rationalParameter q hq.le hq1)).toReal ∧
      (staticSurvival (rationalParameter q hq.le hq1)).toReal ≤ (interval.2 : ℝ) ∧
      interval.2-interval.1 < ε := by
        let m := precisionIndex ε
        let L := 10*seedIndex q hq hq1 m
        let r := recordIndex q hq hq1 L ε hε
        let K := recordCap L r
        let a := rationalParameter q hq.le hq1
        let e := splitEscapeEval q (K-2)
        have hm := precisionIndex_ge_two ε
        have hK := recordCap_ge_two L r
        have hS : staticSurvival a ≠ ⊤ := by
          unfold staticSurvival
          exact measure_ne_top _ _
        have ht := real_error_of_bound (splitEscapeProbability a K) (staticSurvival a) hS m L r
          (by omega) a (explicit_split_truncation q hq hq1 m hm a le_rfl r)
        have he : (e : ℝ) = (splitEscapeProbability a K).toReal :=
          (splitEscapeEval_correct q hq.le hq1 (K-2)).trans
            (congrArg ENNReal.toReal (split_escape_finite a K hK).symm)
        have hp : 1/(m : ℝ) ≤ (ε : ℝ)/4 := by
          have hcast := (Rat.cast_le (K := ℝ)).mpr (precisionIndex_error ε hε)
          push_cast at hcast
          exact hcast
        have hr := real_record_budget q hq hq1 L ε hε
        change (splitEscapeProbability a K).toReal ≤ (staticSurvival a).toReal+1/(m : ℝ)+
          ((actualBinaryWords L).card : ℝ)*(1-(q : ℝ)^(L+1))^r at ht
        have hl : (staticSurvival a).toReal ≤ (e : ℝ) := by
          rw [he]
          apply ENNReal.toReal_mono _ (split_survival_le_escape a K)
          unfold splitEscapeProbability
          exact measure_ne_top _ _
        change ((e-ε/2 : ℚ) : ℝ) ≤ (staticSurvival a).toReal ∧
          (staticSurvival a).toReal ≤ (e : ℝ) ∧ e-(e-ε/2) < ε
        refine ⟨?_,hl,?_⟩
        · push_cast
          linarith
        · linarith

def quotientEvaluationCap (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  let hhalf : 0 < q/2 := rationalHalf_pos q hq
  let hhalf1 : q/2 ≤ 1 := rationalHalf_le_one q hq hq1
  let L := 10*seedIndex (q/2) hhalf hhalf1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)

def quotientCertifiedInterval (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  let e := quotientEscapeEval q (quotientEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)

/-- An executable terminating rational enclosure for the actual quotient survival profile. -/
theorem quotientCertifiedInterval_correct (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ε : ℚ) (hε : 0 < ε) :
    let interval := quotientCertifiedInterval q hq hq1 ε hε
    (interval.1 : ℝ) ≤ (quotientSurvival (rationalParameter q hq.le hq1)).toReal ∧
      (quotientSurvival (rationalParameter q hq.le hq1)).toReal ≤ (interval.2 : ℝ) ∧
      interval.2-interval.1 < ε := by
        let m := precisionIndex ε
        have hhalf : 0 < q/2 := by positivity
        have hhalf1 : q/2 ≤ 1 := by linarith
        let L := 10*seedIndex (q/2) hhalf hhalf1 m
        let r := recordIndex q hq hq1 L ε hε
        let K := recordCap L r
        let a := rationalParameter q hq.le hq1
        let e := quotientEscapeEval q (K-2)
        have hm := precisionIndex_ge_two ε
        have hK := recordCap_ge_two L r
        have hS : quotientSurvival a ≠ ⊤ := by
          unfold quotientSurvival
          exact measure_ne_top _ _
        have ht := real_error_of_bound (quotientEscapeProbability a K) (quotientSurvival a) hS m L r
          (by omega) a (explicit_quotient_truncation q hq hq1 m hm a le_rfl r)
        have he : (e : ℝ) = (quotientEscapeProbability a K).toReal :=
          (quotientEscapeEval_correct q hq.le hq1 (K-2)).trans
            (congrArg ENNReal.toReal (quotient_escape_finite a K hK).symm)
        have hp : 1/(m : ℝ) ≤ (ε : ℝ)/4 := by
          have hcast := (Rat.cast_le (K := ℝ)).mpr (precisionIndex_error ε hε)
          push_cast at hcast
          exact hcast
        have hr := real_record_budget q hq hq1 L ε hε
        change (quotientEscapeProbability a K).toReal ≤ (quotientSurvival a).toReal+1/(m : ℝ)+
          ((actualBinaryWords L).card : ℝ)*(1-(q : ℝ)^(L+1))^r at ht
        have hl : (quotientSurvival a).toReal ≤ (e : ℝ) := by
          rw [he]
          apply ENNReal.toReal_mono _ (quotient_survival_le_escape a K)
          unfold quotientEscapeProbability
          exact measure_ne_top _ _
        change ((e-ε/2 : ℚ) : ℝ) ≤ (quotientSurvival a).toReal ∧
          (quotientSurvival a).toReal ≤ (e : ℝ) ∧ e-(e-ε/2) < ε
        refine ⟨?_,hl,?_⟩
        · push_cast
          linarith
        · linarith

end

section
open HordijkSteelThreshold RAF.Concrete RAF.Polymer

def settledChannels {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R)
    (S : Finset R) (C : Finset M) : Finset R :=
  S.filter (fun r => Q.lhs r ⊆ C ∧ Q.rhs r ⊆ C)

theorem settledChannels_mono {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R)
    (S : Finset R) {C D : Finset M} (h : C ⊆ D) :
    settledChannels Q S C ⊆ settledChannels Q S D := by
  intro r hr
  obtain ⟨hr,hleft,hright⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨hr,hleft.trans h,hright.trans h⟩

theorem enabled_settled_next {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R)
    (S : Finset R) (C : Finset M) (r : R) (hr : r ∈ S)
    (hen : RevEnabledLhs Q C r ∨ RevEnabledRhs Q C r) :
    r ∈ settledChannels Q S (revClosureStep Q S C) := by
      have hold : C ⊆ revClosureStep Q S C := Finset.subset_union_left
      have hadd : (if RevEnabledLhs Q C r then Q.rhs r else ∅) ∪
          (if RevEnabledRhs Q C r then Q.lhs r else ∅) ⊆ revClosureStep Q S C := by
        intro x hx
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,hr,hx⟩)
      apply Finset.mem_filter.mpr
      refine ⟨hr,?_⟩
      rcases hen with hL | hR
      · refine ⟨hL.trans hold,?_⟩
        intro x hx
        apply hadd
        apply Finset.mem_union_left
        simpa [ite_eq_left hL] using hx
      · refine ⟨?_,hR.trans hold⟩
        intro x hx
        apply hadd
        apply Finset.mem_union_right
        simpa [ite_eq_left hR] using hx
theorem growing_closure_grows_settled {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) (C : Finset M)
    (hg : revClosureStep Q S C ≠ C) :
    (settledChannels Q S C).card < (settledChannels Q S (revClosureStep Q S C)).card := by
            have hold : C ⊆ revClosureStep Q S C := Finset.subset_union_left
            have hn : ¬ revClosureStep Q S C ⊆ C := fun hh => hg (Finset.Subset.antisymm hh hold)
            obtain ⟨x,hx,hnot⟩ := Finset.not_subset.mp hn
            have hxnew : x ∈ S.biUnion fun r =>
                (if RevEnabledLhs Q C r then Q.rhs r else ∅) ∪
                (if RevEnabledRhs Q C r then Q.lhs r else ∅) :=
              (Finset.mem_union.mp hx).resolve_left hnot
            obtain ⟨r,hr,hxr⟩ := Finset.mem_biUnion.mp hxnew
            have hactive : RevEnabledLhs Q C r ∨ RevEnabledRhs Q C r := by
              by_contra hh
              push Not at hh
              simp [hh.1,hh.2] at hxr
            have hnotsettled : r ∉ settledChannels Q S C := by
              intro hs
              obtain ⟨_,hleft,hright⟩ := Finset.mem_filter.mp hs
              rcases Finset.mem_union.mp hxr with hxL | hxR
              · by_cases hL : RevEnabledLhs Q C r
                · exact hnot (hright (by simpa [ite_eq_left hL] using hxL))
                · simp [hL] at hxL
              · by_cases hR : RevEnabledRhs Q C r
                · exact hnot (hleft (by simpa [ite_eq_left hR] using hxR))
                · simp [hR] at hxR
            apply Finset.card_lt_card
            refine Finset.ssubset_iff_subset_ne.mpr ⟨settledChannels_mono Q S hold,?_⟩
            intro he
            exact hnotsettled (he.symm ▸ (enabled_settled_next Q S C r hr hactive))
theorem settled_growth_or_stable {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) (k : ℕ) :
    k ≤ (settledChannels Q S (revClosureAt Q S k)).card ∨
      revClosureAt Q S (k+1) = revClosureAt Q S k := by
  induction k with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ k ih =>
    by_cases he : revClosureAt Q S (k+1) = revClosureAt Q S k
    · right
      change revClosureStep Q S (revClosureAt Q S (k+1)) = _
      rw [he]
      exact he
    · have hk := ih.resolve_right he
      exact Or.inl (Nat.succ_le_of_lt (lt_of_le_of_lt hk (growing_closure_grows_settled Q S _ he)))

/-- Each nonstationary round finishes at least one new channel. -/
theorem closure_stable_at_channel_count {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) :
    revClosureAt Q S (S.card+1) = revClosureAt Q S S.card := by
  rcases settled_growth_or_stable Q S S.card with hg | he
  · by_contra hn
    have hh := growing_closure_grows_settled Q S (revClosureAt Q S S.card) hn
    have hbound : (settledChannels Q S (revClosureStep Q S (revClosureAt Q S S.card))).card ≤ S.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  · exact he

theorem closure_stable_after_channel_count {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) (j : ℕ) :
    revClosureAt Q S (S.card+j) = revClosureAt Q S S.card := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ,revClosureAt,ih]
    exact closure_stable_at_channel_count Q S

theorem temporaryClosure_eq_channel_iteration (N L : ℕ) (S : Finset (Reaction N)) :
    temporaryReactionClosure L S = revClosureAt (binaryPolymerCRS N L) S S.card := by
    ext x
    rw [mem_temporaryReactionClosure]
    constructor
    · rintro ⟨k,hk⟩
      by_cases h : k ≤ S.card
      · exact revClosureAt_mono_stage _ _ h hk
      · have he : k = S.card+(k-S.card) := by omega
        rw [he,closure_stable_after_channel_count] at hk
        exact hk
    · intro hx
      exact ⟨S.card,hx⟩
theorem finite_iteration_length (N : ℕ) (S : Finset (Reaction N)) (k : ℕ)
    (x : Molecule N) (hx : x ∈ revClosureAt (binaryPolymerCRS N 2) S k) :
    molLength x ≤ 2^(k+1) := by
          induction k generalizing x with
          | zero =>
            exact (Finset.mem_filter.mp hx).2
          | succ k ih =>
            have hinc : 2^(k+1) ≤ 2^(k+1+1) := by
              rw [pow_succ]
              omega
            change x ∈ revClosureStep (binaryPolymerCRS N 2) S
              (revClosureAt (binaryPolymerCRS N 2) S k) at hx
            rcases Finset.mem_union.mp hx with hx | hx
            · exact (ih x hx).trans hinc
            · obtain ⟨r,_,hx⟩ := Finset.mem_biUnion.mp hx
              have hlen : molLength (reactionLeft r)+molLength (reactionRight r) =
                  molLength (reactionProduct r) := by
                simp [molLength_reactionLeft,molLength_reactionRight,molLength_reactionProduct,reaction_length_add]
              rcases Finset.mem_union.mp hx with hx | hx
              · by_cases hen : RevEnabledLhs (binaryPolymerCRS N 2)
                    (revClosureAt (binaryPolymerCRS N 2) S k) r
                · rw [ite_eq_left hen] at hx
                  have he := Finset.mem_singleton.mp hx
                  have hl := ih (reactionLeft r) (hen (by simp [binaryPolymerCRS]))
                  have hr := ih (reactionRight r) (hen (by simp [binaryPolymerCRS]))
                  rw [he,pow_succ]
                  omega
                · simp [hen] at hx
              · by_cases hen : RevEnabledRhs (binaryPolymerCRS N 2)
                    (revClosureAt (binaryPolymerCRS N 2) S k) r
                · rw [ite_eq_left hen] at hx
                  have hp := ih (reactionProduct r) (hen (by simp [binaryPolymerCRS]))
                  have hx' : x = reactionLeft r ∨ x = reactionRight r := by
                    simpa [binaryPolymerCRS,Finset.mem_insert,Finset.mem_singleton] using hx
                  rcases hx' with rfl | rfl <;> omega
                · simp [hen] at hx
/-- A sparse set of open channels cannot generate an arbitrarily long molecule. -/
theorem sparse_closure_length (N : ℕ) (S : Finset (Reaction N))
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure 2 S) :
    molLength x ≤ 2^(S.card+1) := by
  rw [temporaryClosure_eq_channel_iteration] at hx
  exact finite_iteration_length N S S.card x hx


end

section
open Classical HordijkSteelThreshold MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

set_option Elab.async false
set_option maxHeartbeats 100000

theorem finite_support_open_probability (J : Type*) [Fintype J] (a : I) (T : Finset J) :
    (Measure.pi (fun _ : J => ambientCoordLaw a)) {ω | ∀ j ∈ T, ω j} = (toNNReal a : ENNReal)^T.card := by
    have he : {ω : J → Prop | ∀ j ∈ T, ω j} =
        (T : Set J).pi fun _ => ({True} : Set Prop) := by
      ext ω
      simp
    rw [he, Measure.pi_pi_finset]
    simp [ambientCoordLaw]
theorem finite_many_open_probability (J : Type*) [Fintype J] (a : I) (r : ℕ) :
    (Measure.pi (fun _ : J => ambientCoordLaw a))
      {ω | r ≤ (Finset.univ.filter (fun j : J => ω j)).card} ≤
      ((Fintype.card J).choose r : ENNReal)*(toNNReal a : ENNReal)^r := by
      let μ := Measure.pi fun _ : J => ambientCoordLaw a
      let P := (Finset.univ : Finset J).powersetCard r
      have hs : {ω : J → Prop | r ≤ (Finset.univ.filter fun j : J => ω j).card} ⊆
          ⋃ T ∈ P, {ω | ∀ j ∈ T, ω j} := by
        intro ω hω
        obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq hω
        refine Set.mem_iUnion.mpr ⟨T,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
        · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hcard⟩
        · intro j hj
          exact (Finset.mem_filter.mp (hT hj)).2
      calc
        _ ≤ μ (⋃ T ∈ P, {ω | ∀ j ∈ T, ω j}) := measure_mono hs
        _ ≤ ∑ T ∈ P, μ {ω | ∀ j ∈ T, ω j} := measure_biUnion_finset_le _ _
        _ = ∑ _T ∈ P, (toNNReal a : ENNReal)^r := by
          apply Finset.sum_congr rfl
          intro T hT
          rw [finite_support_open_probability, (Finset.mem_powersetCard.mp hT).2]
        _ = _ := by simp [P]
end

section
open HordijkSteelThreshold RAFReactionQuotient RAF.Concrete RAF.Polymer OverlapCorrectedRAF.Source

set_option Elab.async false
set_option maxHeartbeats 100000

theorem quotientClosure_eq_channel_iteration (N L : ℕ) (S : Finset (RepositoryChannel N)) :
    quotientClosure N L S = revClosureAt (repositoryCRS N L) S S.card := by
    ext x
    rw [mem_quotientClosure]
    constructor
    · rintro ⟨k,hk⟩
      by_cases h : k ≤ S.card
      · exact revClosureAt_mono_stage _ _ h hk
      · have he : k = S.card+(k-S.card) := by omega
        rw [he,closure_stable_after_channel_count] at hk
        exact hk
    · intro hx
      exact ⟨S.card,hx⟩
theorem quotient_iteration_length (N : ℕ) (S : Finset (RepositoryChannel N)) (k : ℕ)
    (x : Molecule N) (hx : x ∈ revClosureAt (repositoryCRS N 2) S k) :
    molLength x ≤ 2^(k+1) := by
        induction k generalizing x with
        | zero =>
          exact (Finset.mem_filter.mp hx).2
        | succ k ih =>
          have hinc : 2^(k+1) ≤ 2^(k+1+1) := by
            rw [pow_succ]
            omega
          change x ∈ revClosureStep (repositoryCRS N 2) S
            (revClosureAt (repositoryCRS N 2) S k) at hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact (ih x hx).trans hinc
          · obtain ⟨r,_,hx⟩ := Finset.mem_biUnion.mp hx
            have hlen : molLength (r.val.1)+molLength (r.val.2) =
                molLength (concatMolecule r.val.1 r.val.2 r.property.1) := by
              simp [concatMolecule]
            rcases Finset.mem_union.mp hx with hx | hx
            · by_cases hen : RevEnabledLhs (repositoryCRS N 2)
                  (revClosureAt (repositoryCRS N 2) S k) r
              · rw [ite_eq_left hen] at hx
                have he := Finset.mem_singleton.mp hx
                have hl := ih (r.val.1) (hen (by simp [repositoryCRS]))
                have hr := ih (r.val.2) (hen (by simp [repositoryCRS]))
                rw [he,pow_succ]
                omega
              · simp [hen] at hx
            · by_cases hen : RevEnabledRhs (repositoryCRS N 2)
                  (revClosureAt (repositoryCRS N 2) S k) r
              · rw [ite_eq_left hen] at hx
                have hp := ih (concatMolecule r.val.1 r.val.2 r.property.1) (hen (by simp [repositoryCRS]))
                have hx' : x = r.val.1 ∨ x = r.val.2 := by
                  simpa [repositoryCRS,Finset.mem_insert,Finset.mem_singleton] using hx
                rcases hx' with rfl | rfl <;> omega
              · simp [hen] at hx
/-- A sparse set of open channels cannot generate an arbitrarily long molecule. -/
theorem quotient_sparse_closure_length (N : ℕ) (S : Finset (RepositoryChannel N))
    (x : Molecule N) (hx : x ∈ quotientClosure N 2 S) :
    molLength x ≤ 2^(S.card+1) := by
  rw [quotientClosure_eq_channel_iteration] at hx
  exact quotient_iteration_length N S S.card x hx


end

section
open Classical HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Source MeasureTheory unitInterval
open scoped ENNReal

def sparseWitnessCap (r : ℕ) : ℕ := 2*(2^(r+1)+2)

def splitSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (Reaction (sparseWitnessCap r))).choose r

def quotientSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (RepositoryChannel (sparseWitnessCap r))).choose r

theorem split_sparse_probability (a : I) (r : ℕ) :
    staticSurvival a ≤ (splitSparseCoefficient r : ENNReal)*(toNNReal a : ENNReal)^r := by
    let K := 2^(r+1)
    let N := 2*(K+2)
    have hs : staticEscapeEvent 2 K ⊆
        {ω | r ≤ (Finset.univ.filter fun j : Reaction N => ω j).card} := by
      intro ω hω
      obtain ⟨x,hx,hlen⟩ := hω
      by_contra hn
      have hcard : (staticOpenReactions ω).card < r := by
        exact lt_of_not_ge hn
      have hb := sparse_closure_length N (staticOpenReactions ω) x hx
      have hp : 2^((staticOpenReactions ω).card+1) ≤ 2^(r+1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      rw [moleculeWord_length] at hlen
      dsimp [K] at hlen
      omega
    apply (staticSurvival_le_finite_escape a K).trans
    apply (measure_mono hs).trans
    simpa +instances only [staticReactionMeasure,Measure.infinitePi_eq_pi,
      splitSparseCoefficient,sparseWitnessCap,N,K,ENNReal.instLE,ENNReal.instPartialOrder] using
      finite_many_open_probability (Reaction N) a r
theorem quotient_sparse_probability (a : I) (r : ℕ) :
    quotientSurvival a ≤ (quotientSparseCoefficient r : ENNReal)*(toNNReal a : ENNReal)^r := by
    let K := 2^(r+1)
    let N := 2*(K+2)
    have hs : quotientEscapeEvent 2 K ⊆
        {ω | r ≤ (Finset.univ.filter fun j : RepositoryChannel N => ω j).card} := by
      intro ω hω
      obtain ⟨x,hx,hlen⟩ := hω
      by_contra hn
      have hcard : (quotientOpen ω).card < r := by
        exact lt_of_not_ge hn
      have hb := quotient_sparse_closure_length N (quotientOpen ω) x hx
      have hp : 2^((quotientOpen ω).card+1) ≤ 2^(r+1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      rw [moleculeWord_length] at hlen
      dsimp [K] at hlen
      omega
    apply (quotientSurvival_le_finite_escape a K).trans
    exact (measure_mono hs).trans (finite_many_open_probability (RepositoryChannel N) a r)
theorem split_sparse_real (a : I) (r : ℕ) :
    (staticSurvival a).toReal ≤ (splitSparseCoefficient r : ℝ)*(a : ℝ)^r := by
  have h := ENNReal.toReal_mono (by finiteness) (split_sparse_probability a r)
  simpa using h

theorem quotient_sparse_real (a : I) (r : ℕ) :
    (quotientSurvival a).toReal ≤ (quotientSparseCoefficient r : ℝ)*(a : ℝ)^r := by
  have h := ENNReal.toReal_mono (by finiteness) (quotient_sparse_probability a r)
  simpa using h

/-- Epsilon-delta flatness: smaller than every fixed power at zero. -/
theorem power_bound_implies_flatness (S : I → ℝ) (C : ℕ → ℕ)
    (hbound : ∀ a r, S a ≤ (C r : ℝ)*(a : ℝ)^r) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : I, 0 < (a : ℝ) → (a : ℝ) < δ → S a < ε*(a : ℝ)^d := by
    let c : ℝ := C (d+1)
    refine ⟨ε/(c+1),by positivity,?_⟩
    intro a ha haδ
    have hx := (lt_div_iff₀ (show 0 < c+1 by positivity)).mp haδ
    have hca : c*(a : ℝ) < ε := by nlinarith
    have hp := mul_lt_mul_of_pos_right hca (pow_pos ha d)
    have hb := hbound a (d+1)
    rw [pow_succ] at hb
    dsimp [c] at hp
    nlinarith

end

section
open HordijkSteelThreshold RAFReactionQuotient unitInterval

theorem split_survival_zero : staticSurvival 0 = 0 := by
  apply le_antisymm _ (by positivity)
  simpa only [toNNReal_zero,ENNReal.coe_zero,zero_pow Nat.one_ne_zero,mul_zero] using split_sparse_probability 0 1

theorem quotient_survival_zero : quotientSurvival 0 = 0 := by
  apply le_antisymm _ (by positivity)
  simpa only [toNNReal_zero,ENNReal.coe_zero,zero_pow Nat.one_ne_zero,mul_zero] using quotient_sparse_probability 0 1

def splitTotalInterval (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  if h : q = 0 then (0,0) else splitCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

def quotientTotalInterval (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  if h : q = 0 then (0,0) else quotientCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

theorem splitTotalInterval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    let v := splitTotalInterval q hq hq1 ε hε
    (v.1 : ℝ) ≤ (staticSurvival (rationalParameter q hq hq1)).toReal ∧
      (staticSurvival (rationalParameter q hq hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2-v.1 < ε := by
    by_cases h : q = 0
    · subst q
      have he : rationalParameter 0 hq hq1 = 0 := by apply Subtype.ext; simp [rationalParameter]
      simp [splitTotalInterval,he,split_survival_zero,hε]
    · simpa [splitTotalInterval,dite_eq_right h] using
        splitCertifiedInterval_correct q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε
theorem quotientTotalInterval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    let v := quotientTotalInterval q hq hq1 ε hε
    (v.1 : ℝ) ≤ (quotientSurvival (rationalParameter q hq hq1)).toReal ∧
      (quotientSurvival (rationalParameter q hq hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2-v.1 < ε := by
    by_cases h : q = 0
    · subst q
      have he : rationalParameter 0 hq hq1 = 0 := by apply Subtype.ext; simp [rationalParameter]
      simp [quotientTotalInterval,he,quotient_survival_zero,hε]
    · simpa [quotientTotalInterval,dite_eq_right h] using
        quotientCertifiedInterval_correct q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε
end

section
open HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Source MeasureTheory

def splitSeedBool (N L : ℕ) (ω : Reaction N → Bool) : Bool :=
  decide (binaryFood N L ⊆ computedClosure N 2 (Finset.univ.filter (fun r => ω r)))

def quotientSeedBool (N L : ℕ) (ω : RepositoryChannel N → Bool) : Bool :=
  splitSeedBool N L (fun r => ω (splitToQuotient r))

def splitSeedEval (N L : ℕ) (q : ℚ) : ℚ :=
  rationalEventProbability (Reaction N) q (splitSeedBool N L)

def quotientSeedEval (N L : ℕ) (q : ℚ) : ℚ :=
  rationalEventProbability (RepositoryChannel N) q (quotientSeedBool N L)

theorem splitSeedEval_correct (N L : ℕ) (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (splitSeedEval N L q : ℝ) =
      (staticReactionMeasure N (rationalParameter q hq hq1)
        {ω | binaryFood N L ⊆ temporaryReactionClosure 2 (staticOpenReactions ω)}).toReal := by
      classical
      have h := rationalEventProbability_correct (Reaction N) q hq hq1 (splitSeedBool N L)
      have he : {ω : Reaction N → Prop | splitSeedBool N L fun r => decide (ω r)} =
          {ω | binaryFood N L ⊆ temporaryReactionClosure 2 (staticOpenReactions ω)} := by
        ext ω
        simp [splitSeedBool,computedClosure_eq,staticOpenReactions]
      rw [he] at h
      simpa [splitSeedEval,staticReactionMeasure,Measure.infinitePi_eq_pi] using h.symm
theorem quotientSeedEval_correct (N L : ℕ) (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (quotientSeedEval N L q : ℝ) =
      (quotientStaticMeasure N (rationalParameter q hq hq1)
        {ω | binaryFood N L ⊆ quotientClosure N 2 (quotientOpen ω)}).toReal := by
        classical
        have h := rationalEventProbability_correct (RepositoryChannel N) q hq hq1 (quotientSeedBool N L)
        have he : {ω : RepositoryChannel N → Prop | quotientSeedBool N L fun r => decide (ω r)} =
            {ω | binaryFood N L ⊆ quotientClosure N 2 (quotientOpen ω)} := by
          ext ω
          simp [Set.mem_ofPred_eq,quotientSeedBool,splitSeedBool,decide_eq_true_eq,computedClosure_eq]
          change (binaryFood N L ⊆ temporaryReactionClosure 2
            (staticOpenReactions fun r => ω (splitToQuotient r))) ↔ _
          rw [← quotientClosure_pullback]
        rw [he] at h
        exact h.symm
end

section
open Classical HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal

theorem finite_food_seed_mass (N L m : ℕ) (a : I) :
    staticReactionMeasure N a {ω | binaryFood N L ⊆ temporaryReactionClosure 2 (staticOpenReactions ω)} ≤
      staticReactionMeasure N a {ω | (m-1)*Fintype.card (Molecule N) ≤
        m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} +
      staticReactionMeasure N a {ω | m*(temporaryReactionClosure L (staticOpenReactions ω)).card <
        (m-1)*Fintype.card (Molecule N)} := by
  apply (measure_mono (show {ω : Reaction N → Prop | binaryFood N L ⊆
      temporaryReactionClosure 2 (staticOpenReactions ω)} ⊆
      {ω | (m-1)*Fintype.card (Molecule N) ≤ m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} ∪
      {ω | m*(temporaryReactionClosure L (staticOpenReactions ω)).card < (m-1)*Fintype.card (Molecule N)} from ?_)).trans
    (measure_union_le _ _)
  intro ω hseed
  by_cases hb : m*(temporaryReactionClosure L (staticOpenReactions ω)).card < (m-1)*Fintype.card (Molecule N)
  · exact Or.inr hb
  · left
    have hs : temporaryReactionClosure L (staticOpenReactions ω) ⊆
        temporaryReactionClosure 2 (staticOpenReactions ω) := by
      apply temporaryReactionClosure_seed_transfer Finset.Subset.rfl
      intro x hx
      exact hseed (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
    exact (Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card hs))

theorem quotient_finite_food_seed_mass (N L m : ℕ) (a : I) :
    quotientStaticMeasure N a {ω | binaryFood N L ⊆ quotientClosure N 2 (quotientOpen ω)} ≤
      quotientStaticMeasure N a {ω | (m-1)*Fintype.card (Molecule N) ≤
        m*(quotientClosure N 2 (quotientOpen ω)).card} +
      quotientStaticMeasure N a {ω | m*(quotientClosure N L (quotientOpen ω)).card <
        (m-1)*Fintype.card (Molecule N)} := by
    apply (measure_mono (show {ω : RepositoryChannel N → Prop | binaryFood N L ⊆ quotientClosure N 2 (quotientOpen ω)} ⊆
        {ω | (m-1)*Fintype.card (Molecule N) ≤ m*(quotientClosure N 2 (quotientOpen ω)).card} ∪
        {ω | m*(quotientClosure N L (quotientOpen ω)).card < (m-1)*Fintype.card (Molecule N)} from ?_)).trans
      (measure_union_le _ _)
    intro ω hseed
    by_cases hb : m*(quotientClosure N L (quotientOpen ω)).card < (m-1)*Fintype.card (Molecule N)
    · exact Or.inr hb
    · left
      have hs : quotientClosure N L (quotientOpen ω) ⊆ quotientClosure N 2 (quotientOpen ω) := by
        simp [quotientClosure_pullback] at hseed ⊢
        apply temporaryReactionClosure_seed_transfer Finset.Subset.rfl
        intro x hx
        exact hseed (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
      exact (Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card hs))
theorem split_finite_source_lower (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (lambda : ℝ)
    (hk : 6 < nearFullPoolSize n m)
    (hpool : rationalParameter q hq.le hq1 ≤ fixedPoolParameter (catalysisP n lambda) (nearFullPoolSize n m)) :
    staticReactionMeasure n (rationalParameter q hq.le hq1)
      {ω | binaryFood n (10*seedIndex q hq hq1 m) ⊆ temporaryReactionClosure 2 (staticOpenReactions ω)} ≤
      uniformCatalysisMeasure n lambda (HasRAFEvent n) + (m : ENNReal)⁻¹ := by
  have he : (finiteInitialSegment (Molecule n) (nearFullPoolSize n m)).card = nearFullPoolSize n m :=
    card_finiteInitialSegment _ _ (nearFullPoolSize_le n m)
  have hl := canonical_raf_ge_near_full_static n m lambda hm (rationalParameter q hq.le hq1) hk
    (by change _ ≤ fixedPoolParameter _ (finiteInitialSegment (Molecule n) (nearFullPoolSize n m)).card; rwa [he])
  exact (finite_food_seed_mass n _ m _).trans
    (add_le_add hl (effective_static_bulk q hq hq1 m hm n hn))

theorem quotient_finite_source_lower (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (p : I)
    (hk : 6 < nearFullPoolSize n m)
    (hpool : rationalParameter q hq.le hq1 ≤ fixedPoolParameter p (nearFullPoolSize n m)) :
    let hh : 0 < q/2 := by positivity
    let hh1 : q/2 ≤ 1 := by linarith
    quotientStaticMeasure n (rationalParameter q hq.le hq1)
      {ω | binaryFood n (10*seedIndex (q/2) hh hh1 m) ⊆ quotientClosure n 2 (quotientOpen ω)} ≤
      quotientRAFProbability n p + (m : ENNReal)⁻¹ := by
  dsimp only
  exact (quotient_finite_food_seed_mass n _ m _).trans
    (add_le_add (quotient_near_full_lower n m p _ hm hk hpool)
      (effective_quotient_bulk q hq hq1 m hm _ le_rfl n hn))


end

section
open Classical HordijkSteelThreshold MeasureTheory RAF RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

theorem bounded_seed_probability_le_36 (n K : ℕ) (hn : 4 ≤ n) (lambda : ℝ) :
    ambientPiMeasure n lambda (boundedSeedCatalystEvent n K) ≤
      (Fintype.card (Molecule K) : ENNReal) * 36 *
        (toNNReal (catalysisP n lambda) : ENNReal) := by
    let J := ↥(binaryFood n K) × PolymerSeedReaction n 2
    let E : J → Set (AmbientCoord n → Prop) := fun j => {ω | ω (j.1.val,j.2.val)}
    have he : boundedSeedCatalystEvent n K = ⋃ j : J, E j := by
      ext ω
      simp only [boundedSeedCatalystEvent, Set.mem_ofPred_eq, Set.mem_iUnion, E]
      constructor
      · rintro ⟨x,r,hx,hr,hω⟩
        exact ⟨(⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩,⟨r,hr⟩),hω⟩
      · rintro ⟨⟨x,r⟩,hω⟩
        exact ⟨x.val,r.val,(Finset.mem_filter.mp x.property).2,r.property,hω⟩
    rw [he]
    calc
      _ ≤ ∑ j : J, ambientPiMeasure n lambda (E j) := measure_iUnion_fintype_le _ _
      _ = (Fintype.card J : ENNReal) * (toNNReal (catalysisP n lambda) : ENNReal) := by
        simp [E, ambient_coordinate_probability, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul_left
        have hc : Fintype.card J ≤ Fintype.card (Molecule K) * 36 := by
          dsimp [J]
          rw [Fintype.card_prod, Fintype.card_coe]
          exact Nat.mul_le_mul (binaryFood_card_le_cutoff n K) (le_of_eq (card_concrete_gateway_binary_t2 hn))
        exact_mod_cast hc
theorem ambient_raf_le_escape_add_seed_36 (n K : ℕ) (hn : 4 ≤ n) (lambda : ℝ) :
    ambientPiMeasure n lambda {ω | ∃ S : Finset (Reaction n),
      IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S} ≤
    ambientPiMeasure n lambda {ω | ∃ x ∈
      temporaryReactionClosure 2 (catalystActive ω Finset.univ), K < molLength x} +
      (Fintype.card (Molecule K) : ENNReal) * 36 *
        (toNNReal (catalysisP n lambda) : ENNReal) := by
    let E : Set (AmbientCoord n → Prop) := {ω | ∃ x ∈
      temporaryReactionClosure 2 (catalystActive ω Finset.univ), K < molLength x}
    have hs : {ω | ∃ S : Finset (Reaction n),
        IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S} ⊆
        E ∪ boundedSeedCatalystEvent n K := by
      intro ω hraf
      by_cases he : ω ∈ E
      · exact Or.inl he
      · right
        apply bounded_raf_has_seed_catalyst ω ?_ hraf
        intro x hx
        exact Nat.le_of_not_gt fun h => he ⟨x,hx,h⟩
    exact (measure_mono hs).trans ((measure_union_le _ _).trans
      (add_le_add_right (bounded_seed_probability_le_36 n K hn lambda) _))
theorem canonical_raf_le_finite_escape_36 (n K : ℕ) (hn : 4 ≤ n) (lambda : ℝ) :
    uniformCatalysisMeasure n lambda (HasRAFEvent n) ≤
      staticReactionMeasure (2*(K+2))
        (fixedPoolParameter (catalysisP n lambda) (Fintype.card (Molecule n)))
        (staticEscapeEvent 2 K) +
      (Fintype.card (Molecule (K+2)) : ENNReal)*36*(toNNReal (catalysisP n lambda) : ENNReal) := by
  rw [canonical_raf_measure_eq_ambient]
  exact (ambient_raf_le_escape_add_seed_36 n (K+2) hn lambda).trans
    (add_le_add_left (ambient_escape_le_finite_static n K lambda) _)


end

section
open HordijkSteelThreshold RAFReactionQuotient unitInterval

theorem criticalOpenness_pos_le (lam : ℝ) (hlam : 0 < lam) :
    0 < (criticalOpenness lam hlam : ℝ) ∧ (criticalOpenness lam hlam : ℝ) ≤ lam := by
  change 0 < 1-Real.exp (-lam) ∧ 1-Real.exp (-lam) ≤ lam
  constructor
  · have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hlam)
    linarith
  · linarith [Real.add_one_le_exp (-lam)]

theorem power_bound_intensity_flatness (S : I → ℝ) (C : ℕ → ℕ)
    (hbound : ∀ a r, S a ≤ (C r : ℝ)*(a : ℝ)^r) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      S (criticalOpenness lam hlam) < ε*lam^d := by
  obtain ⟨δ,hδ,h⟩ := power_bound_implies_flatness S C hbound d ε hε
  refine ⟨δ,hδ,?_⟩
  intro lam hlam hlamδ
  have ha := criticalOpenness_pos_le lam hlam
  exact (h _ ha.1 (ha.2.trans_lt hlamδ)).trans_le
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.1.le ha.2 d) hε.le)

theorem split_low_intensity_flatness (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      (staticSurvival (criticalOpenness lam hlam)).toReal < ε*lam^d :=
  power_bound_intensity_flatness _ splitSparseCoefficient split_sparse_real d ε hε

theorem quotient_low_intensity_flatness (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      quotientTransitionLimit lam hlam < ε*lam^d :=
  power_bound_intensity_flatness _ quotientSparseCoefficient quotient_sparse_real d ε hε


end

section
open Classical HordijkSteelThreshold RAF.Concrete RAF.Polymer RAFReactionQuotient OverlapCorrectedRAF.Source

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
    have hfixed := closure_stable_at_card Q T
    have hg : revClosureStep Q S C ≠ C := by
      intro he
      have hall : ∀ k, revClosureAt Q S k ⊆ C := by
        intro k
        induction k with
        | zero => exact revClosureAt_mono_stage Q T (Nat.zero_le _)
        | succ k ih =>
          exact (revClosureStep_mono Q Finset.Subset.rfl ih).trans (Finset.subset_of_eq he)
      exact hnot (hall _ hx)
    have hex : ∃ r ∈ S, revClosureStep Q {r} C ≠ C := by
      by_contra h
      push Not at h
      apply hg
      apply Finset.Subset.antisymm _ Finset.subset_union_left
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact hy
      · obtain ⟨r,hr,hy⟩ := Finset.mem_biUnion.mp hy
        have hh : y ∈ revClosureStep Q {r} C :=
          Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r,Finset.mem_singleton_self _,hy⟩)
        rw [h r hr] at hh
        exact hh
    obtain ⟨r,hr,hgrow⟩ := hex
    refine ⟨r,hr,?_,hgrow⟩
    intro hrT
    apply hgrow
    apply Finset.Subset.antisymm _ Finset.subset_union_left
    exact (revClosureStep_mono Q (Finset.singleton_subset_iff.mpr hrT) Finset.Subset.rfl).trans
      (Finset.subset_of_eq hfixed)
theorem long_target_productive_history {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (length : M → ℕ)
    (hbound : ∀ T x, x ∈ fullClosure Q T → length x ≤ 2^(T.card+1))
    (S : Finset R) (k : ℕ) (x : M) (hx : x ∈ fullClosure Q S)
    (hlen : 2^(k+1) < length x) :
    ∃ T, ProductiveHistory Q S k T ∧ T.card = k ∧ T ⊆ S := by
  induction k with
  | zero => exact ⟨∅,ProductiveHistory.nil,Finset.card_empty,Finset.empty_subset _⟩
  | succ k ih =>
    have hp : 2^(k+1) ≤ 2^(k+1+1) := Nat.pow_le_pow_right (by omega) (by omega)
    obtain ⟨T,hT,hcard,hTS⟩ := ih (hp.trans_lt hlen)
    have hnot : x ∉ fullClosure Q T := by
      intro hh
      have hb := hbound T x hh
      rw [hcard] at hb
      omega
    obtain ⟨r,hr,hrT,hgrow⟩ := productive_extension Q S T x hx hnot
    exact ⟨insert r T,ProductiveHistory.step hT hr hrT hgrow,
      by rw [Finset.card_insert_of_notMem hrT,hcard],Finset.insert_subset hr hTS⟩

theorem split_long_target_history (N k : ℕ) (S : Finset (Reaction N)) (x : Molecule N)
    (hx : x ∈ temporaryReactionClosure 2 S) (hlen : 2^(k+1) < molLength x) :
    ∃ T, ProductiveHistory (binaryPolymerCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S := by
  apply long_target_productive_history _ molLength _ S k x _ hlen
  · intro T y hy
    apply sparse_closure_length N T y
    rwa [← computedClosure_eq]
  · rwa [← computedClosure_eq] at hx

theorem quotient_long_target_history (N k : ℕ) (S : Finset (RepositoryChannel N)) (x : Molecule N)
    (hx : x ∈ quotientClosure N 2 S) (hlen : 2^(k+1) < molLength x) :
    ∃ T, ProductiveHistory (repositoryCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S := by
  have he (T : Finset (RepositoryChannel N)) : fullClosure (repositoryCRS N 2) T = quotientClosure N 2 T := by
    ext y
    rw [mem_quotientClosure]
    constructor
    · intro hy; exact ⟨Fintype.card (Molecule N),hy⟩
    · rintro ⟨j,hj⟩
      by_cases h : j ≤ Fintype.card (Molecule N)
      · exact revClosureAt_mono_stage _ _ h hj
      · have hjj : j = Fintype.card (Molecule N)+(j-Fintype.card (Molecule N)) := by omega
        rw [hjj,closure_stable_after_card] at hj
        exact hj
  apply long_target_productive_history _ molLength _ S k x _ hlen
  · intro T y hy
    exact quotient_sparse_closure_length N T y (by rwa [he] at hy)
  · rwa [he]


end

section
open HordijkSteelThreshold RAFReactionQuotient unitInterval

def rationalPool (p : ℚ) (k : ℕ) : ℚ := 1-(1-p)^k

theorem rationalPool_nonneg (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ rationalPool p k := by
  exact sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp1) (by linarith))

theorem rationalPool_le_one (p : ℚ) (hp1 : p ≤ 1) (k : ℕ) : rationalPool p k ≤ 1 := by
  dsimp [rationalPool]
  linarith [pow_nonneg (sub_nonneg.mpr hp1) k]

theorem rationalPool_correct (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    rationalParameter (rationalPool p k) (rationalPool_nonneg p hp hp1 k) (rationalPool_le_one p hp1 k) =
      fixedPoolParameter (rationalParameter p hp hp1) k := by
  apply Subtype.ext
  simp [rationalParameter,rationalPool]


end

section
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF.Polymer RAF.Concrete
open scoped ENNReal

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

theorem splitSourceInterval_correct (n m K : ℕ) (hn : 4 ≤ n) (hm : 0 < m)
    (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hk : 6 < nearFullPoolSize n m) (hpool : q ≤ rationalPool p (nearFullPoolSize n m)) :
    let v := splitSourceInterval n m K p q hq hq1
    (v.1 : ℝ) ≤ (splitCatalyticProbability n (rationalParameter p hp hp1)).toReal ∧
      (splitCatalyticProbability n (rationalParameter p hp hp1)).toReal ≤ (v.2 : ℝ) := by
        let a := rationalParameter p hp hp1
        let lam := (a : ℝ)*Fintype.card (Reaction n)/n
        have he := RAFEmergenceApprox.catalysisP_covers_probability n (by omega) a
        have hqpool : rationalParameter q hq.le hq1 ≤ fixedPoolParameter a (nearFullPoolSize n m) := by
          rw [← rationalPool_correct p hp hp1]
          exact (Rat.cast_le (K := ℝ)).mpr hpool
        have hl := split_finite_source_lower q hq hq1 m n hm (by omega) lam hk (by rwa [he])
        have hu := canonical_raf_le_finite_escape_36 n K hn lam
        rw [he] at hu
        have hP : uniformCatalysisMeasure n lam (HasRAFEvent n) ≠ ⊤ := measure_ne_top _ _
        have hi : (m : ENNReal)⁻¹ ≠ ⊤ := by simp [Nat.ne_of_gt hm]
        have hlow := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hP,hi⟩) hl
        rw [ENNReal.toReal_add hP hi, ← splitSeedEval_correct n _ q hq.le hq1] at hlow
        have hE : staticReactionMeasure (2*(K+2)) (fixedPoolParameter a (Fintype.card (Molecule n)))
            (staticEscapeEvent 2 K) ≠ ⊤ := measure_ne_top _ _
        have ht : (Fintype.card (Molecule (K+2)) : ENNReal)*36*(toNNReal a : ENNReal) ≠ ⊤ := by finiteness
        have hupp := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hE,ht⟩) hu
        rw [ENNReal.toReal_add hE ht, ← rationalPool_correct p hp hp1,
          ← splitEscapeEval_correct _ (rationalPool_nonneg p hp hp1 _) (rationalPool_le_one p hp1 _) K] at hupp
        rw [ENNReal.toReal_inv,ENNReal.toReal_natCast] at hlow
        simp [← one_div] at hlow
        dsimp only [a] at hlow hupp
        simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.coe_toReal,coe_toNNReal] at hupp
        dsimp only [splitSourceInterval,splitCatalyticProbability,Prod.fst,Prod.snd]
        push_cast
        constructor
        · change _ ≤ (uniformCatalysisMeasure n lam (HasRAFEvent n)).toReal
          linarith
        · exact hupp
theorem quotientSourceInterval_correct (n m K : ℕ) (hn : 0 < n) (hm : 0 < m)
    (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hk : 6 < nearFullPoolSize n m) (hpool : q ≤ rationalPool p (nearFullPoolSize n m)) :
    let v := quotientSourceInterval n m K p q hq hq1
    (v.1 : ℝ) ≤ (quotientRAFProbability n (rationalParameter p hp hp1)).toReal ∧
      (quotientRAFProbability n (rationalParameter p hp hp1)).toReal ≤ (v.2 : ℝ) := by
    let a := rationalParameter p hp hp1
    have hqpool : rationalParameter q hq.le hq1 ≤ fixedPoolParameter a (nearFullPoolSize n m) := by
      rw [← rationalPool_correct p hp hp1]
      exact (Rat.cast_le (K := ℝ)).mpr hpool
    have hl := quotient_finite_source_lower q hq hq1 m n hm hn a hk hqpool
    have hu := quotient_raf_upper n K a
    have hP : quotientRAFProbability n a ≠ ⊤ := by unfold quotientRAFProbability quotientCatalyticLaw; exact measure_ne_top _ _
    have hi : (m : ENNReal)⁻¹ ≠ ⊤ := by simp [Nat.ne_of_gt hm]
    have hlow := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hP,hi⟩) hl
    rw [ENNReal.toReal_add hP hi, ← quotientSeedEval_correct n _ q hq.le hq1] at hlow
    have hE : quotientStaticMeasure (2*(K+2)) (fixedPoolParameter a (Fintype.card (Molecule n)))
        (quotientEscapeEvent 2 K) ≠ ⊤ := by unfold quotientStaticMeasure; exact measure_ne_top _ _
    have ht : (Fintype.card (Molecule (K+2)) : ENNReal)*34*(toNNReal a : ENNReal) ≠ ⊤ := by finiteness
    have hupp := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hE,ht⟩) hu
    rw [ENNReal.toReal_add hE ht, ← rationalPool_correct p hp hp1,
      ← quotientEscapeEval_correct _ (rationalPool_nonneg p hp hp1 _) (rationalPool_le_one p hp1 _) K] at hupp
    rw [ENNReal.toReal_inv,ENNReal.toReal_natCast] at hlow
    simp [← one_div] at hlow
    dsimp only [a] at hlow hupp
    simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.coe_toReal,coe_toNNReal] at hupp
    dsimp only [quotientSourceInterval,Prod.fst,Prod.snd]
    push_cast
    constructor
    · linarith
    · exact hupp
theorem interval_comparison_error (P S lP uP lS uS : ℝ)
    (hP : lP ≤ P ∧ P ≤ uP) (hS : lS ≤ S ∧ S ≤ uS) :
    |P-S| ≤ max (uP-lS) (uS-lP) := by
  apply abs_le.mpr
  constructor
  · have h := le_max_right (uP-lS) (uS-lP)
    linarith [hP.1,hS.2]
  · have h := le_max_left (uP-lS) (uS-lP)
    linarith [hP.2,hS.1]


end

section
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF.Polymer RAF.Concrete
open Filter
open scoped Topology

def rationalIntervalError (source profile : ℚ × ℚ) : ℚ :=
  max (source.2-profile.1) (profile.2-source.1)

theorem split_source_profile_error (n m K : ℕ) (hn : 4 ≤ n) (hm : 0 < m)
    (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hk : 6 < nearFullPoolSize n m) (hpool : q ≤ rationalPool p (nearFullPoolSize n m))
    (s : ℚ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    |(splitCatalyticProbability n (rationalParameter p hp hp1)).toReal -
      (staticSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (splitSourceInterval n m K p q hq hq1)
        (splitTotalInterval s hs hs1 ε hε) : ℝ) := by
  have hP := splitSourceInterval_correct n m K hn hm p hp hp1 q hq hq1 hk hpool
  have hS := splitTotalInterval_correct s hs hs1 ε hε
  have h := interval_comparison_error _ _ _ _ _ _ hP ⟨hS.1,hS.2.1⟩
  simpa [rationalIntervalError] using h

theorem quotient_source_profile_error (n m K : ℕ) (hn : 0 < n) (hm : 0 < m)
    (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hk : 6 < nearFullPoolSize n m) (hpool : q ≤ rationalPool p (nearFullPoolSize n m))
    (s : ℚ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    |(quotientRAFProbability n (rationalParameter p hp hp1)).toReal -
      (quotientSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (quotientSourceInterval n m K p q hq hq1)
        (quotientTotalInterval s hs hs1 ε hε) : ℝ) := by
  have hP := quotientSourceInterval_correct n m K hn hm p hp hp1 q hq hq1 hk hpool
  have hS := quotientTotalInterval_correct s hs hs1 ε hε
  have h := interval_comparison_error _ _ _ _ _ _ hP ⟨hS.1,hS.2.1⟩
  simpa [rationalIntervalError] using h


end

section
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval

theorem uniform_record_budget (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ)
    (ε : ℚ) (hε : 0 < ε) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) :
    ((actualBinaryWords L).card : ℝ) * (1-(a : ℝ)^(L+1))^(recordIndex q hq hq1 L ε hε) ≤
      (ε : ℝ)/4 := by
    have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast hq.le
    have hqa := ha
    have hpow := pow_le_pow_left₀ hq0 hqa (L+1)
    have hnonneg : (0 : ℝ) ≤ 1-(a : ℝ)^(L+1) :=
      sub_nonneg.mpr (pow_le_one₀ a.property.1 a.property.2)
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hnonneg (sub_le_sub_left hpow 1) _) (Nat.cast_nonneg _)).trans
      (real_record_budget q hq hq1 L ε hε)
theorem split_uniform_approximation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ε : ℚ) (hε : 0 < ε) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) :
    (splitEscapeProbability a (splitEvaluationCap q hq hq1 ε hε)).toReal ≤
      (staticSurvival a).toReal + (ε : ℝ)/2 := by
  let m := precisionIndex ε
  let L := 10*seedIndex q hq hq1 m
  let r := recordIndex q hq hq1 L ε hε
  have hm : 2 ≤ m := precisionIndex_ge_two ε
  have hS : staticSurvival a ≠ ⊤ := by unfold staticSurvival; exact measure_ne_top _ _
  have ht := real_error_of_bound _ _ hS m L r (by omega) a
    (explicit_split_truncation q hq hq1 m hm a ha r)
  have hp : 1/(m : ℝ) ≤ (ε : ℝ)/4 := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr (precisionIndex_error ε hε)
    push_cast at hcast
    exact hcast
  have hr := uniform_record_budget q hq hq1 L ε hε a ha
  change (splitEscapeProbability a (recordCap L r)).toReal ≤ _
  linarith

theorem quotient_uniform_approximation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ε : ℚ) (hε : 0 < ε) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) :
    (quotientEscapeProbability a (quotientEvaluationCap q hq hq1 ε hε)).toReal ≤
      (quotientSurvival a).toReal + (ε : ℝ)/2 := by
  let m := precisionIndex ε
  have hh : 0 < q/2 := by positivity
  have hh1 : q/2 ≤ 1 := by linarith
  let L := 10*seedIndex (q/2) hh hh1 m
  let r := recordIndex q hq hq1 L ε hε
  have hm : 2 ≤ m := precisionIndex_ge_two ε
  have hS : quotientSurvival a ≠ ⊤ := by unfold quotientSurvival; exact measure_ne_top _ _
  have ht := real_error_of_bound _ _ hS m L r (by omega) a
    (explicit_quotient_truncation q hq hq1 m hm a ha r)
  have hp : 1/(m : ℝ) ≤ (ε : ℝ)/4 := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr (precisionIndex_error ε hε)
    push_cast at hcast
    exact hcast
  have hr := uniform_record_budget q hq hq1 L ε hε a ha
  change (quotientEscapeProbability a (recordCap L r)).toReal ≤ _
  linarith


end

section
open HordijkSteelThreshold unitInterval

theorem split_second_coefficient : splitSparseCoefficient 2 = 712483666919430 := by
  unfold splitSparseCoefficient sparseWitnessCap
  rw [card_reactions_exact (by norm_num)]
  norm_num [Nat.choose_two_right]

theorem split_quadratic_bound (a : I) :
    (staticSurvival a).toReal ≤ 712483666919430*(a : ℝ)^2 := by
    simpa [split_second_coefficient,Nat.cast_ofNat] using split_sparse_real a 2
/-- A fully symbolic certificate, requiring no enumeration of channel fields. -/
theorem worked_low_openness_bound (a : I) (ha : (a : ℝ) ≤ 1/10^20) :
    (staticSurvival a).toReal < 8/10^26 := by
      exact (split_quadratic_bound a).trans_lt ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ a.property.1 ha 2) (by norm_num)).trans_lt (by norm_num))
end

end RAFCriticalWindowQuantitative
