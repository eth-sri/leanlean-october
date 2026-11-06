module

public import Registry.P046.SupportingObligations
public import proofs.RAFCriticalWindowQuantitative.SourceCalibration
public import proofs.RAFCriticalWindowQuantitative.LowIntensity
public import proofs.RAFCriticalWindowQuantitative.ProductiveHistory
public import proofs.RAFCriticalWindowQuantitative.WorkedBound

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient unitInterval RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

/-- Quantitative properties of the specified actual profile and executable programs. -/
structure ProfileGuarantees (S : I → ENNReal) (escape : I → ℕ → ENNReal)
    (evaluate : (q : ℚ) → 0 ≤ q → q ≤ 1 → (ε : ℚ) → 0 < ε → ℚ × ℚ)
    (cap : (q : ℚ) → 0 < q → q ≤ 1 → (ε : ℚ) → 0 < ε → ℕ)
    (coefficient : ℕ → ℕ) : Prop where
  enclosure : ∀ q hq hq1 ε hε,
    let v := evaluate q hq hq1 ε hε
    (v.1 : ℝ) ≤ (S $ rationalParameter q hq hq1).toReal ∧
      (S $ rationalParameter q hq hq1).toReal ≤ (v.2 : ℝ) ∧ v.2-v.1 < ε
  uniform_error : ∀ q hq hq1 ε hε a, rationalParameter q (le_of_lt hq) hq1 ≤ a →
    (escape a $ cap q hq hq1 ε hε).toReal ≤ (S a).toReal+(ε : ℝ)/2
  power_bound : ∀ a r, (S a).toReal ≤ (coefficient r : ℝ)*(a : ℝ)^r
  intensity_flatness : ∀ d ε, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ → (S $ criticalOpenness lam hlam).toReal < ε*lam^d

section
variable (M : SplitModel) [∀ N, DecidableEq $ M.C N] (Ls : (q : ℚ) → 0 < q → q ≤ 1 → ℕ → ℕ) (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε)

def capOf : ℕ :=
  recordCap (Ls q hq hq1 $ precisionIndex ε) $ recordIndex q hq hq1 (Ls q hq hq1 $ precisionIndex ε) ε hε

def certifiedOf : ℚ × ℚ :=
  let K := capOf Ls q hq hq1 ε hε - 2
  let e := rationalEventProbability (M.C $ 2*(K+2)) q fun ω => splitEscapeBool _ (K+2) fun r => ω $ M.π r
  (e-ε/2,e)

open MeasureTheory in
theorem profile_of (hg : PrefixIndex M.g) {S : I → ENNReal}
    (hS : ∀ a, M.ν a {field | ReversibleUnbounded 2 field} = S a) {c : ℕ → ℕ}
    (hsp : ∀ a r, S a ≤ (c r : ENNReal)*(toNNReal a : ENNReal)^r)
    (hbulk : ∀ q hq hq1 m, 2 ≤ m → ∀ a : I, rationalParameter q hq.le hq1 ≤ a → ∀ N, 0 < N →
      M.μ N a {x | m*(M.cl N (Ls q hq hq1 m) x).card < (m-1)*Fintype.card (Molecule N)} ≤ (m : ENNReal)⁻¹) :
    ProfileGuarantees S
      (fun a K => infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (fieldOf M.g ω) w})
      (fun q hq hq1 ε hε => if h : q = 0 then (0,0) else certifiedOf M Ls q (lt_of_le_of_ne hq $ Ne.symm h) hq1 ε hε)
      (capOf Ls) c := by
  have hu : ∀ q hq hq1 ε hε a, rationalParameter q hq.le hq1 ≤ a →
      (infiniteSplitPi a {ω | ∃ w, capOf Ls q hq hq1 ε hε < w.length ∧
          InfiniteReversibleGenerated 2 (fieldOf M.g ω) w}).toReal ≤ (S a).toReal + ε/2 :=
    fun q hq hq1 ε hε a ha => by
    have hgood := hS a ▸ M.seed_survival a _ _ (precisionIndex_ge_two ε) $ hbulk q hq hq1 _ (precisionIndex_ge_two ε) a ha
    have hS := hS a ▸ measure_ne_top (M.ν a) _
    unfold capOf
    generalize Ls q hq hq1 (precisionIndex ε) = L at hgood ⊢
    generalize S a = T at hgood hS ⊢
    rw [Measure.map_apply (measurable_fieldOf M.g) $ by
      simp_rw [Set.ofPred_forall]; exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
        measurableSet_infiniteReversibleGenerated 2 v] at hgood
    have hm := precisionIndex_ge_two ε
    have hp : (toNNReal a : ENNReal)^(L+1) ≤ 1 :=
      pow_le_one₀ (by positivity) $ by exact_mod_cast a.property.2
    have ht : ((actualBinaryWords L).card) *
        (1-(toNNReal a : ENNReal)^(L+1))^(recordIndex q hq hq1 L ε hε) ≠ ⊤ := by
      finiteness
    have hsum : T+(precisionIndex ε : ENNReal)⁻¹ ≠ ⊤ := by simp_all; omega
    refine (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hsum,ht⟩) $ (measure_mono (t := {ω | ∀ v ∈ actualBinaryWords L,
      FiniteReversibleGenerated (recordCap L $ recordIndex q hq hq1 L ε hε) 2 (fieldOf M.g ω) v} ∪ ⋃ v ∈ actualBinaryWords L,
        escapedMissing M.g (recordCap L _) v) fun ω hω => ?_).trans
      ((measure_union_le _ _).trans $ add_le_add (le_trans (measure_mono fun ω hω v hv =>
        finiteReversibleGenerated_to_infinite $ hω v hv) hgood) $ (measure_biUnion_finset_le _ _).trans
          ((Finset.sum_le_card_nsmul _ _ _ fun v hv => common_cap_target_failure hg a v (List.length_pos_iff.mpr
            ((mem_actualBinaryWords v L).mp hv).1) L ((mem_actualBinaryWords v L).mp hv).2 _).trans_eq $ nsmul_eq_mul _ _))).trans ?_
    · refine or_iff_not_imp_left.2 fun h => ?_
      obtain ⟨v, hv, hm⟩ := not_forall₂.1 h
      exact Set.mem_biUnion hv ⟨hω, hm⟩
    rw [ENNReal.toReal_add hsum ht, ENNReal.toReal_add hS $ by simp; omega,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hp $ by simp]
    have hc := (Rat.cast_le (K := ℝ)).mpr $ precisionIndex_error ε hε
    have hr := (Rat.cast_le (K := ℝ)).mpr (geometricIndex_spec _ (2^(L+1)) (ε/4) (repair_ratio q hq hq1 L).1 (repair_ratio q hq hq1 L).2 $ by positivity).2
    have hcR : ((actualBinaryWords L).card) ≤ (2 : ℝ)^(L+1) := by
      rw [actualBinaryWords_card]
      exact_mod_cast Nat.sub_le _ _
    have hpow := pow_le_pow_left₀ (by positivity) (show (q : ℝ) ≤ a from ha) $ L+1
    have h1 : 0 ≤ 1-(q : ℝ)^(L+1) := by exact_mod_cast (repair_ratio q hq hq1 L).1
    have hnonneg : 0 ≤ 1-(a : ℝ)^(L+1) :=
      sub_nonneg.mpr $ pow_le_one₀ a.property.1 a.property.2
    have hr := (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hnonneg (sub_le_sub_left hpow 1) $ recordIndex q hq hq1 L ε hε)
        (Nat.cast_nonneg (actualBinaryWords L).card)).trans
      ((mul_le_mul_of_nonneg_right hcR $ pow_nonneg h1 _).trans $ by push_cast at hr; exact hr)
    simp_all
    linarith
  have hsr := sparse_real hsp
  refine ⟨fun q hq hq1 ε hε => ?_, hu, hsr, fun d ε hε => ⟨ε/(c (d+1)+1), by positivity, fun lam hlam hδ => ?_⟩⟩
  · by_cases h0 : q = 0
    · subst q
      have he : rationalParameter 0 hq hq1 = 0 := by apply Subtype.ext; simp [rationalParameter]
      have := hsp 0 1
      simp_all
    have hq' := lt_of_le_of_ne hq $ Ne.symm h0
    have h := (M.eval_correct q hq hq1 $ capOf Ls q hq' hq1 ε hε - 2).trans
      (congrArg ENNReal.toReal (M.escape_eq' (recordCap_ge_two _ _) _).symm)
    have := h.trans_le $ hu q hq' hq1 ε hε _ le_rfl
    have := (ENNReal.toReal_mono (measure_ne_top _ _) $ hS _ ▸ (M.ν_RU _).trans_le $ measure_mono fun _ h => h _).trans_eq h.symm
    push_cast [certifiedOf, h0]
    refine ⟨?_,?_,?_⟩ <;> linarith
  have h0 : 0 < 1-Real.exp (-lam) := by simp_all
  have h1 : 1-Real.exp (-lam) ≤ lam := by linarith [Real.add_one_le_exp $ -lam]
  have hb := hsr (criticalOpenness lam hlam) $ d+1
  change _ ≤ _ * (1-Real.exp (-lam))^(d+1) at hb
  rw [lt_div_iff₀ $ by positivity] at hδ
  rw [pow_succ] at hb
  have h2 := pow_le_pow_left₀ h0.le h1 d
  have h3 := pow_pos h0 d
  nlinarith [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (c $ d+1)),
    mul_le_mul_of_nonneg_left h2 hε.le, mul_pos h3 hε]

end

open Classical in
theorem split_profile_guarantees : ProfileGuarantees staticSurvival splitEscapeProbability
    splitTotalInterval splitEvaluationCap splitSparseCoefficient :=
  profile_of splitModel (fun q hq hq1 m => 10*seedIndex q hq hq1 m) (fun _ _ => Iff.rfl) (fun _ => rfl) split_sparse_probability fun q hq hq1 m hm a ha N hN =>
      (product_decreasing_mono (fun _ => _) _ (fun _ => ha) (fun ω => m*(splitModel.cl N _ ω).card < _)
        fun _ _ h hT => (Nat.mul_le_mul_left m $ Finset.card_le_card
          (temporaryReactionClosure_mono fun r hr => Finset.mem_filter.2 ⟨Finset.mem_univ _, h _ (Finset.mem_filter.1 hr).2⟩)).trans_lt hT).trans
        (effective_static_bulk q hq hq1 m (by omega) N hN)

theorem quotient_profile_guarantees : ProfileGuarantees quotientSurvival quotientEscapeProbability
    quotientTotalInterval quotientEvaluationCap quotientSparseCoefficient :=
  profile_of quotientModel (fun q hq hq1 m => 10*seedIndex (q/2) (rationalHalf_pos q hq) (rationalHalf_le_one q hq hq1) m)
    canonicalIndex_prefixIndex quotientModel.ν_RU quotient_sparse_probability
    fun q hq hq1 m hm a ha N hN => (MeasureTheory.measure_mono fun x h => by rwa [Set.mem_ofPred_eq,
      quotientClosure_pullback]).trans $ effective_quotient_bulk q hq hq1 m (by omega) a ha N hN

/-- The source contract uses actual catalytic inputs, not an assumed convergence rate. -/
def SourceGuarantees : Prop :=
  (∀ n m K, ∀ _hn : 4 ≤ n, ∀ _hm : 0 < m,
    ∀ p hp hp1 q hq hq1, ∀ _hk : 6 < nearFullPoolSize n m,
    ∀ _hpool : q ≤ rationalPool p (nearFullPoolSize n m),
    ∀ s hs hs1 ε hε,
    |(splitCatalyticProbability n $ rationalParameter p hp hp1).toReal -
      (staticSurvival $ rationalParameter s hs hs1).toReal| ≤
      (rationalIntervalError (splitSourceInterval n m K p q hq hq1)
        (splitTotalInterval s hs hs1 ε hε) : ℝ)) ∧
  (∀ n m K, ∀ _hn : 0 < n, ∀ _hm : 0 < m,
    ∀ p hp hp1 q hq hq1, ∀ _hk : 6 < nearFullPoolSize n m,
    ∀ _hpool : q ≤ rationalPool p (nearFullPoolSize n m),
    ∀ s hs hs1 ε hε,
    |(quotientRAFProbability n $ rationalParameter p hp hp1).toReal -
      (quotientSurvival $ rationalParameter s hs hs1).toReal| ≤
      (rationalIntervalError (quotientSourceInterval n m K p q hq hq1)
        (quotientTotalInterval s hs hs1 ε hε) : ℝ))

open Classical MeasureTheory in
theorem finite_source_guarantees : SourceGuarantees := by
  constructor <;> intro n m K hn hm p hp hp1 q hq hq1 hk hpool s hs hs1 ε hε
  on_goal 1 =>
    have he := RAFEmergenceApprox.catalysisP_covers_probability n (by omega) $ rationalParameter p hp hp1
    obtain ⟨h1,h2⟩ := toReal_interval hm ((splitModel.food_seed_mass n _ m _).trans $ add_le_add ((measure_mono fun ω (hω : _ ≤ m*_) => by
        show _ ≤ (splitModel.cl n 2 ω).card
        have := Nat.div_mul_le_self (Fintype.card $ Molecule n) m; unfold nearFullPoolSize; nlinarith).trans
      (le_trans (product_increasing_mono _ (fun _ => fixedPoolParameter (catalysisP n _) $ nearFullPoolSize n m) (fun _ => by rw [he, ← rationalPool_correct p hp hp1]; exact (Rat.cast_le (K := ℝ)).mpr hpool)
        (fun ω => nearFullPoolSize n m ≤ (splitModel.cl n 2 ω).card)
        fun _ _ h hS => hS.trans $ Finset.card_le_card $ temporaryReactionClosure_mono fun r hr => Finset.mem_filter.2 ⟨Finset.mem_univ _, h _ (Finset.mem_filter.1 hr).2⟩)
      (by
        show _ ≤ splitCatalyticProbability n (rationalParameter p hp hp1)
        rw [splitCatalyticProbability, canonical_raf_measure_eq_ambient, ambient_eq_law, Measure.map_apply (by fun_prop) (Set.toFinite _).measurableSet]
        exact (card_finiteInitialSegment _ _ (nearFullPoolSize_le n m) ▸ mass_ge_static _ _ (fun _ _ h => temporaryReactionClosure_mono h) _ $ Fintype.card $ Reaction n).trans
          (measure_mono fun ω hω => ⟨_, usableClosureReactions_isRAF _ (fun x r => ω r x)
            (fun r hr => (RAFEmergenceApprox.Generic.mem_catalystActive ω _ r).mp $ (peelingActiveAt_stable_card _ _ (RAFEmergenceApprox.Generic.catalystActive_mono ω)
              fun _ _ h => temporaryReactionClosure_mono h).ge hr) $ exists_long_of_card $ hk.trans_le hω⟩))))
      (effective_static_bulk q hq hq1 m hm n $ by omega)) (by
      rw [splitCatalyticProbability, canonical_raf_measure_eq_ambient]
      refine (measure_mono fun ω hraf => ?_).trans $ (measure_union_le _ _).trans $ add_le_add (by
          show ambientPiMeasure n _ {ω | ∃ x ∈ temporaryReactionClosure 2 $ RAFEmergenceApprox.Generic.catalystActive (fun r x => ω (x, r)) Finset.univ, K+2 < molLength x} ≤ _
          rw [ambient_eq_law, Measure.map_apply (by fun_prop) (Set.toFinite _).measurableSet]
          erw [pool_statistic _ _ fun S => ∃ x ∈ temporaryReactionClosure 2 S, K+2 < molLength x, Finset.card_univ, ← splitModel.escape_eq]
          exact splitModel.capped_le n K _)
        (union_card_le _ (binaryFood n $ K+2) (Finset.univ.filter $ RevSeedReaction $ binaryPolymerCRS n 2)
          (fun x r => {ω | ω (x,r)}) (fun _ _ => by
            rw [ambient_eq_law, Measure.map_apply (by fun_prop) $ by measurability]
            exact law_coord _ _ _)
          (binaryFood_card_le_cutoff n $ K+2)
          ((Fintype.card_subtype _).symm.trans_le card_concrete_gateway_binary_t2))
      refine or_iff_not_imp_left.2 fun he => ?_
      obtain ⟨S, hne, hfg, hcat⟩ := hraf
      obtain ⟨r, hr, hseed⟩ := exists_rev_seed_of_foodGenerated _ S hne hfg
      obtain ⟨x, k, hx, hxr⟩ := hcat r hr
      refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_gt fun hl => he ⟨x,
        temporaryReactionClosure_mono (fun r hr => ?_) $ (mem_temporaryReactionClosure S x).mpr ⟨k, hx⟩, hl⟩⟩,
        r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hseed⟩, hxr⟩
      obtain ⟨x, _, _, hx⟩ := hcat r hr
      exact (RAFEmergenceApprox.Generic.mem_catalystActive _ _ r).mpr ⟨x, Finset.mem_univ _, hx⟩)
      (measure_ne_top (splitModel.μ _ _) _) $ by finiteness
    rw [he] at h2
    refine interval_error ?_ $ split_profile_guarantees.1 s hs hs1 ε hε
  on_goal 2 =>
    obtain ⟨h1,h2⟩ := toReal_interval hm ((quotientModel.food_seed_mass n _ m $ rationalParameter q hq.le hq1).trans $ add_le_add
      (by
          simp only [SplitModel.cl, ← quotientClosure_pullback]
          refine (measure_mono fun ω hω => ?_).trans $ (product_increasing_mono _
            (fun _ => fixedPoolParameter _ $ nearFullPoolSize n m) (fun _ => by rw [← rationalPool_correct p hp hp1]; exact (Rat.cast_le (K := ℝ)).mpr hpool)
            (fun ω => nearFullPoolSize n m ≤ (quotientClosure n 2 $ quotientOpen ω).card) fun x y hxy hx =>
              hx.trans $ Finset.card_le_card $ quotientClosure_mono n 2 fun j => by
                simpa [quotientOpen] using hxy j).trans
            (card_finiteInitialSegment _ _ (nearFullPoolSize_le n m) ▸ (mass_ge_static _ _ (quotientClosure_mono n 2) _
              (Fintype.card $ RepositoryChannel n)).trans (measure_mono fun ω hω => by
            show ∃ S, IsRevRAF (repositoryCRS n 2) (fun x j => ω j x) S
            have hs := usableClosureReactions_isRAF _ (fun x r => ω (splitToQuotient r) x)
              (fun r hr => quotientClosure_preimage _ ▸ (RAFEmergenceApprox.Generic.mem_catalystActive _ _ _).mp
                ((peelingActiveAt_stable_card _ _ (RAFEmergenceApprox.Generic.catalystActive_mono ω) $ quotientClosure_mono n 2).ge (Finset.mem_filter.mp hr).2))
              (quotientClosure_preimage (L := 2) _ ▸ exists_long_of_card (hk.trans_le hω))
            refine ⟨_, hs.1.image splitToQuotient, fun j hj => ?_, fun j hj => ?_⟩ <;> obtain ⟨r, hmem, rfl⟩ := Finset.mem_image.mp hj
            · obtain ⟨k, hk⟩ := hs.2.1 r hmem
              exact ⟨k, by simpa only [splitToQuotient_lhs, splitToQuotient_rhs, split_closure_eq_quotient] using hk⟩
            · obtain ⟨x, k, hx, hc⟩ := hs.2.2 r hmem
              exact ⟨x, k, by rwa [split_closure_eq_quotient], hc⟩))
          have := Nat.div_mul_le_self (Fintype.card $ Molecule n) m
          simp only [Set.mem_ofPred_eq, nearFullPoolSize] at *
          nlinarith)
      (by simp only [SplitModel.cl, ← quotientClosure_pullback]; exact effective_quotient_bulk q hq hq1 m hm _ le_rfl n hn))
      (by
      let E : Set (RepositoryChannel n → Molecule n → Prop) := {ω | ∃ x ∈
        quotientClosure n 2 $ RAFEmergenceApprox.Generic.catalystActive ω Finset.univ, K+2 < molLength x}
      refine ((measure_mono (s := quotientRAFEvent n) fun ω hraf => ?_).trans $ (measure_union_le E _).trans $ add_le_add_right
        (union_card_le _ (binaryFood n $ K+2) (repositorySeedChannels n 2) (fun x j => {ω | ω j x})
          (fun x j => law_coord _ j x) (binaryFood_card_le_cutoff n $ K+2)
          (repositorySeedChannels_card_le_34 n)) _).trans $ add_le_add_left ?_ _
      · refine or_iff_not_imp_left.2 fun he => ?_
        obtain ⟨S,hS⟩ := hraf
        obtain ⟨r,hr,hseed⟩ := exists_rev_seed_of_foodGenerated _ S hS.1 hS.2.1
        obtain ⟨x,k,hx,hcat⟩ := hS.2.2 r hr
        have hx' := quotientClosure_mono n 2 (fun r hr => let ⟨x, _, _, h⟩ := hS.2.2 r hr
          (RAFEmergenceApprox.Generic.mem_catalystActive _ _ _).mpr ⟨x, Finset.mem_univ _, h⟩) $ (mem_quotientClosure S x).mpr ⟨k,hx⟩
        exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.le_of_not_gt $ fun hl => he ⟨x,hx',hl⟩⟩,
          r, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hseed⟩, hcat⟩
      rw [pool_statistic _ Finset.univ
        (∃ x ∈ quotientClosure n 2 ·, K+2 < molLength x),Finset.card_univ,
        ← quotientModel.escape_eq]
      exact (measure_mono fun ω h => by rwa [Set.mem_ofPred_eq, SplitModel.cl, ← quotientClosure_pullback]).trans
        (quotientModel.capped_le n K _)) (measure_ne_top (Measure.pi _) _) $ by finiteness
    refine interval_error ?_ $ quotient_profile_guarantees.1 s hs hs1 ε hε
  all_goals simp only [← splitModel.seedEval_correct n _ q hq.le hq1, ← quotientModel.seedEval_correct n _ q hq.le hq1] at h1
  all_goals simp only [← rationalPool_correct p hp hp1, ← splitModel.eval_correct _ (rationalPool_nonneg p hp hp1 _) (rationalPool_le_one p hp1 _) K,
    ← quotientModel.eval_correct _ (rationalPool_nonneg p hp hp1 _) (rationalPool_le_one p hp1 _) K,
    ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.coe_toReal,coe_toNNReal] at h2
  all_goals dsimp only [splitSourceInterval,quotientSourceInterval]; push_cast; exact ⟨h1, h2⟩

/-- Compiled minimum quantitative/computability successor for both literal RAF models.
The programs are explicit definitions; no desired bound or validity oracle is assumed. -/
theorem quantitative_critical_window_resolution :
    ProfileGuarantees staticSurvival splitEscapeProbability
      splitTotalInterval splitEvaluationCap splitSparseCoefficient ∧
    ProfileGuarantees quotientSurvival quotientEscapeProbability
      quotientTotalInterval quotientEvaluationCap quotientSparseCoefficient ∧
    SourceGuarantees ∧
    (∀ N k S x, x ∈ temporaryReactionClosure (N := N) 2 S → 2^(k+1) < molLength x →
      ∃ T, ProductiveHistory (binaryPolymerCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S) ∧
    (∀ N k S x, x ∈ quotientClosure N 2 S → 2^(k+1) < molLength x →
      ∃ T, ProductiveHistory (repositoryCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S) ∧
    (∀ a : I, (a : ℝ) ≤ 1/10^20 → (staticSurvival a).toReal < 8/10^26) :=
  ⟨split_profile_guarantees,quotient_profile_guarantees,finite_source_guarantees,
    fun _ _ _ _ hx => long_target_productive_history _ molLength (fun T y hy => split_closure_length T y
      ((mem_temporaryReactionClosure _ _).2 ⟨_, hy⟩)) _ _ _ (card_closure_sub _ _ _
        ((mem_temporaryReactionClosure _ _).1 hx).choose_spec),
    fun _ _ _ _ hx => long_target_productive_history _ molLength (fun T y hy => quotient_closure_length T y
      ((mem_quotientClosure _ _).2 ⟨_, hy⟩)) _ _ _ (card_closure_sub _ _ _
        ((mem_quotientClosure _ _).1 hx).choose_spec),worked_low_openness_bound⟩

end RAFCriticalWindowQuantitative
