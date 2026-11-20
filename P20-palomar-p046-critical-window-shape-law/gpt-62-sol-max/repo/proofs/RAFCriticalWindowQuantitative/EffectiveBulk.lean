module

public import proofs.HordijkSteelThreshold.InfiniteStaticLaw
public import proofs.RAFCriticalWindowQuantitative.ApproximationParameters
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import proofs.RAFReactionQuotient.QuotientMap

@[expose] public section

namespace HordijkSteelThreshold
open MeasureTheory unitInterval

noncomputable def detourRisk (a : I) (k : ℕ) : ENNReal := (blockFailure a 2)^k

private def detourProduct (w : List Bool) : List.Vector Bool (w.length/2) ↪ List Bool :=
  ⟨fun j => w ++ j.val, (List.append_right_injective w).comp Subtype.val_injective⟩

variable (g : CutMap)

private def detourFailure (w : List Bool) : Set SplitField :=
  (MeasurableEquiv.curry (List Bool) ℕ Prop) ⁻¹'
    (↑(Finset.univ.map (detourProduct w)) : Set (List Bool)).pi
      (fun t => trialFailure {g (t,w.length-1), g (t,w.length)})

private def shortFailure (k : ℕ) : Set SplitField :=
  ⋃ w, {ω | 10*k < List.length w ∧ ω ∈ detourFailure g w}

private theorem measure_shortFailure (a : I) (k : ℕ) (hk : 0 < k) (hθ : detourRisk a k ≤ (2⁻¹ : ENNReal)^2) :
    infiniteSplitPi a (shortFailure g k) ≤ 2*detourRisk a k := by
  let θ := detourRisk a k
  refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum (g := fun w : List Bool => θ*((2⁻¹ : ENNReal)^2)^w.length) ?_).trans_eq ?_)
  · intro w
    by_cases hw : 10*k < w.length
    · simp only [hw, true_and, Set.ofPred_mem_eq]
      let B (t : List Bool) : Finset ℕ := {g (t,w.length-1), g (t,w.length)}
      rw [detourFailure, ← MeasurableEquiv.map_apply, infiniteSplitPi,
        Measure.infinitePi_map_curry (fun (_ : List Bool) (_ : ℕ) => ambientCoordLaw a),
        Measure.infinitePi_pi _ (fun t _ => (iid_block_failure a (B t)).1)]
      refine (Finset.prod_le_prod (g := fun _ => blockFailure a 2) fun t _ =>
        (iid_block_failure a (B t)).2.trans_le
          (failure_ratio_mono a ((Finset.card_insert_le ..).trans (by simp)))).trans ?_
      rw [Finset.prod_const, Finset.card_map, Finset.card_univ, card_vector, Fintype.card_bool]
      have hcount : (w.length+1)*k ≤ 2^(w.length/2) := by
        let j := w.length/4
        calc
          _ ≤ (2*j)^2 := by
            nlinarith [Nat.mul_le_mul (show w.length+1 ≤ 8*j by omega) (show 2*k ≤ j by omega)]
          _ ≤ (2^j)^2 := Nat.pow_le_pow_left (Nat.mul_le_pow (by decide) j) _
          _ ≤ _ := by rw [← pow_mul']; gcongr; omega
      apply (pow_le_pow_of_le_one zero_le (show blockFailure a 2 ≤ 1 from tsub_le_self)
        hcount).trans
      rw [Nat.mul_comm, pow_mul, ← detourRisk, pow_succ, mul_comm]
      gcongr
    · simp [hw]
  have hu : (2 : ENNReal)*2⁻¹ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  rw [← ENNReal.tsum_fiberwise _ List.length]
  change (∑' n, ∑' w : List.Vector Bool n, θ*((2⁻¹ : ENNReal)^2)^w.val.length) = 2*θ
  simp [mul_left_comm, ← mul_pow, pow_two, ← mul_assoc, hu, one_mul,
    ENNReal.tsum_mul_left, ENNReal.tsum_geometric, mul_comm]

/-- The first stage has a global union bound, since every word below the
chosen threshold has exponentially many possible suffixes for its detour. -/

private theorem generate_short {g : CutMap} {ω : SplitField} {N k : ℕ}
    (hk : 0 < k) (hω : ω ∉ shortFailure g k) (w : List Bool) (hne : w ≠ [])
    (hT : w.length ≤ min N (max (10*k) (2*N/3))) : FiniteReversibleGenerated N (10*k) (pullbackField g ω) w := by
  by_cases h : w.length ≤ 10*k
  · exact .food hne (by omega)
  obtain ⟨j, hj, hj'⟩ : ∃ j : List.Vector Bool (w.length/2),
      pullbackField g ω (w ++ j.val) (w.length-1) ∧ pullbackField g ω (w ++ j.val) w.length := by
    have hn : ω ∉ detourFailure g w := fun hn => hω (Set.mem_iUnion.mpr ⟨w, by omega, hn⟩)
    simpa [detourFailure, detourProduct, trialFailure, blockEvent, pullbackField, CutMap.relabel] using! hn
  obtain ⟨u,b,rfl⟩ := (List.eq_nil_or_concat' w).resolve_left hne
  refine .left hne (List.length_pos_iff.mp (by grind)) ?_ ⟨by grind,hj'⟩
  rw [List.append_assoc]
  refine .ligate (generate_short hk hω u ?_ ?_) (generate_short hk hω (b::j.val) (by simp) ?_)
    ⟨by grind, by simpa [List.append_assoc] using hj⟩
  all_goals grind
termination_by w.length
decreasing_by all_goals grind

end HordijkSteelThreshold

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Polymer RAF.Concrete MeasureTheory unitInterval RAFReactionQuotient

section

variable (g : CutMap)

abbrev SeedGenerated (N : ℕ) (ω : SplitField) :=
  FiniteReversibleGenerated N 2 (pullbackField g ω)

def escapedMissing (B : ℕ) (v : List Bool) : Set SplitField :=
  latentEscapeEvent g B ∩ {ω | ¬ SeedGenerated g B ω v}

/-- Partition escape by the first record, in length and then word-code order.
Each piece reads only products up to that record's length. -/
theorem escaped_missing_contraction
    (a : I) (v : List Bool) (hv : v ≠ []) {L : ℕ} (hL : v.length ≤ L) (B : ℕ) (hB : 2 ≤ B) :
    infiniteSplitPi a (escapedMissing g (2*B+L) v) ≤
      infiniteSplitPi a (escapedMissing g B v) * blockFailure a (L+1) := by
  let Record := {w : List Bool // B < w.length ∧ w.length ≤ 2*B}
  let R := List.Shortlex (· < · : Bool → Bool → Prop)
  let G (ω : SplitField) (w : Record) := SeedGenerated g w.val.length ω w.val
  let D (w : Record) : Set SplitField := {ω | G ω w ∧
    (∀ u, R u.val w.val → ¬ G ω u) ∧
    ¬ SeedGenerated g B ω v}
  -- A capped derivation depends only on the coordinates of its reaction catalogue.
  let P (N : ℕ) := Finset.univ.image fun r : Reaction N => g.relabel (literalSplitCoordinate r)
  have hD (w : Record) := split_prefix_law a (P w.val.length) (D w) <| by
    intro ω η h
    have gen {N : ℕ} (hN : N ≤ w.val.length) (v : List Bool) :
        SeedGenerated g N ω v ↔ SeedGenerated g N η v := by
      suffices restrictedSplitReactions N (pullbackField g ω) = restrictedSplitReactions N (pullbackField g η) by
        simp [SeedGenerated, finiteReversible_iff_literalClosure, literalClosure, this]
      ext r
      simp only [restrictedSplitReactions, mem_openChannels]
      exact Iff.of_eq (h _ (Finset.mem_image_of_mem _ (Finset.mem_univ (⟨r.1.castLE hN,r.2⟩ : Reaction w.val.length))))
    apply propext
    refine and_congr (gen le_rfl _) (and_congr ?_ (not_congr (gen w.property.1.le v)))
    exact forall_congr' fun u => forall_congr' fun hr => not_congr (gen (by grind [List.shortlex_def]) u.val)
  let key (w t : List Bool) := g.relabel (if t = [] then (v++w, v.length) else (t++w,1))
  let U (u : Record) := (v.tails.map (key u.val)).toFinset
  calc
    _ ≤ infiniteSplitPi a (⋃ w, D w ∩ trialFailure (U w)) := measure_mono (by
      rintro ω ⟨⟨t,ht,htgen⟩,hn⟩
      obtain ⟨w,hw,hN,hg⟩ := escape_has_bounded_record hB ⟨t,by omega,htgen⟩
      obtain ⟨u,hu,hm⟩ := ((List.Shortlex.wf (wellFounded_lt (α := Bool))).onFun (f := Subtype.val)).has_min
        {u | G ω u} ⟨⟨w,hw,hN⟩,hg⟩
      refine Set.mem_iUnion.mpr ⟨u, ⟨⟨hu,fun v hv hg' => hm v hg' hv,
        fun hv => hn (finiteReversibleGenerated_mono_cap (by omega) hv)⟩, ?_⟩⟩
      intro ho
      let w := u.val
      have hopen (t : List Bool) (ht : t <:+ v) := of_eq_true (ho (key w t) (by simp [U]; exact ⟨t,ht,rfl⟩))
      have gen (t : List Bool) : t <:+ v → SeedGenerated g (2*B+L) ω (t++w) := by
        induction t with
        | nil => exact fun _ => finiteReversibleGenerated_mono_cap (by grind) hu
        | cons b t ih =>
          intro ht
          exact .ligate (u := [b]) (v := t++w) (.food (by simp) (by grind))
            (ih ((List.suffix_cons ..).trans ht))
            ⟨by grind, by simpa [key, pullbackField] using hopen (b::t) ht⟩
      exact hn (.left hv (List.length_pos_iff.mp (by grind)) (gen v List.suffix_rfl)
        ⟨by grind, by simpa [key, pullbackField] using hopen [] List.nil_suffix⟩))
    _ ≤ (∑' w, infiniteSplitPi a (D w)) * blockFailure a (L+1) := by
      rw [← ENNReal.tsum_mul_right]
      refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun u => ?_)
      rw [(hD u).2 (U u) (by
        simp [-Sigma.exists, -Prod.forall, Finset.disjoint_left, P, U]
        intro r t _ h
        have := moleculeWord_cap (reactionProduct r)
        grind [literalSplitCoordinate, CutMap.relabel, List.length_eq_zero_iff])]
      exact mul_le_mul' le_rfl (failure_ratio_mono a ((List.toFinset_card_le _).trans (by simpa using hL)))
    _ ≤ _ := by
      rw [← measure_iUnion]
      · refine mul_le_mul' (measure_mono ?_) le_rfl
        intro ω hω
        obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hω
        exact ⟨⟨w.val,w.property.1,finiteReversibleGenerated_to_infinite hw.1⟩,hw.2.2⟩
      · exact fun x y h => Set.disjoint_left.mpr fun _ hx hy => h (Subtype.ext
          (Std.Trichotomous.trichotomous (r := R) _ _ (hy.2.1 x · hx.1) (hx.2.1 y · hy.1)))
      · exact fun w => (hD w).1

def recordCap (ell : ℕ) : ℕ → ℕ :=
  Nat.rec 2 (fun _ cap => 2*cap+ell)

theorem recordCap_ge_two (ell j : ℕ) : 2 ≤ recordCap ell j := by
  induction j <;> first | rfl | grind [recordCap]

/-- Escape without survival requires a failed detour or a missing seed word. -/
theorem truncation (a : I) (k r : ℕ) (hk : 0 < k) (hθ : detourRisk a k ≤ (2⁻¹ : ENNReal)^2) :
    let L := 10*k
    latentEscapeProbability g a (recordCap L r) ≤
      latentSurvival g a + 2*detourRisk a k + (2 : ENNReal)^(L+1)*(blockFailure a (L+1))^r := by
  intro L
  refine (measure_le_inter_add_sdiff _ _ {ω | ∀ v : Molecule L,
    SeedGenerated g (recordCap L r) ω (moleculeWord v)}).trans (add_le_add ?_ ?_)
  · refine measure_le_add_of_cover ?_ le_rfl (measure_shortFailure g a k hk hθ)
    intro ω hω
    refine or_iff_not_imp_right.mpr fun hn K => ?_
    let w := List.replicate (K+1) false
    have h := generate_short (N := 2*(K+1)) hk hn w (by simp [w]) (by simp [w]; omega)
    refine ⟨w, by simp [w], h.rebase ?_ (fun _ _ ho => ho.2)⟩
    intro u hu hl
    simpa using finiteReversibleGenerated_to_infinite
      (hω.2 (sourceWordMolecule u (List.length_pos_iff.mpr hu) (hl.trans (min_le_left ..))))
  · refine (measure_le_card_mul (δ := (blockFailure a (L+1))^r) Finset.univ
      (fun v : Molecule L => escapedMissing g (recordCap L r) (moleculeWord v)) ?_ ?_).trans ?_
    · simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Finset.mem_univ, true_and, not_forall]
      tauto
    · intro v _
      induction r with
      | zero => simpa using (prob_le_one : infiniteSplitPi a _ ≤ 1)
      | succ r ih =>
        rw [pow_succ]
        exact (escaped_missing_contraction g a _ (moleculeWord_nonempty v) (moleculeWord_cap v)
          _ (recordCap_ge_two ..)).trans (mul_le_mul' ih le_rfl)
    · rw [Finset.card_univ]
      gcongr
      norm_cast
      simp only [Fintype.card_sigma, Fintype.card_fin, pow_succ', ← Finset.mul_sum]
      rw [Fin.sum_univ_eq_sum_range]
      exact Nat.mul_le_mul_left _ ((Nat.geomSum_lt (s := Finset.range L) (by decide) (by simp)).le)

end

section
variable (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) (a : I)
  (ha : rationalParameter b hb.le hb1 ≤ a)
include ha

theorem selected_detourRisk :
    let k := seedIndex b hb hb1 m
    let θ := detourRisk a k
    0 < k ∧ θ ≤ (2⁻¹ : ENNReal)^2 ∧ 2*θ + (m : ENNReal)*(2*θ) ≤ (m : ENNReal)⁻¹ := by
  intro k θ
  refine ⟨(seedIndex_spec ..).1, ?_⟩
  have ht : θ ≤ detourRisk (rationalParameter b hb.le hb1) k :=
    pow_le_pow_left' (blockFailure_anti ha 2) k
  let d : ENNReal := m*(m+1)
  have hc : (4 : ENNReal) ≤ molecularContourConstant := by norm_num [molecularContourConstant]
  have h : 4*θ*(d+1) ≤ 1 := by
    grw [ht, hc]
    apply (ENNReal.toReal_le_toReal (by unfold d detourRisk; finiteness) (by simp)).mp
    simp [ENNReal.toReal_mul, detourRisk, d, rationalParameter]
    exact_mod_cast (seedIndex_spec b hb hb1 m).2
  rw [← ENNReal.inv_pow, ENNReal.le_inv_iff_mul_le, ENNReal.le_inv_iff_mul_le]
  constructor
  · rw [mul_comm, show (2 : ENNReal)^2 = 4 by norm_num, ← mul_one (4*θ)]
    grw [show (1 : ENNReal) ≤ d+1 by simp, h]
  · rw [show (2*θ+(m : ENNReal)*(2*θ))*m = 2*θ*d by unfold d; ring]
    grw [show (2 : ENNReal) ≤ 4 by norm_num, show d ≤ d+1 by simp, h]

/-- The supplied-seed mass estimate, transported to either finite catalogue. -/
theorem effective_bulk {J : Type*} [Fintype J] {N : ℕ} {g : CutMap}
    (C : FiniteCatalogue J N g) :
    let k := seedIndex b hb hb1 m
    finiteFieldLaw a {q | (C.closure (10*k) q).card < nearFullPoolSize N m} ≤ (m : ENNReal)⁻¹ := by
  intro k
  rw [C.measure_closure a (10*k) (fun U => U.card < nearFullPoolSize N m)]
  obtain ⟨hk,hθ,hδ⟩ := selected_detourRisk b hb hb1 m a ha
  refine le_trans ?_ hδ
  let T := max (10*k) (2*N/3)
  let cut (x : Molecule N) (i : Fin k) := (moleculeWord x).length - T + i.val
  let U (x : Molecule N) := Finset.univ.map ⟨fun i : Fin k => (moleculeWord x, cut x i),
    fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Prod.snd h))⟩
  let bad (x : Molecule N) : Set SplitField := if T < (moleculeWord x).length then blockEvent (U x) False else ∅
  let δ := 2*detourRisk a k
  let pool ω := literalClosure N (10*k) (pullbackField g ω)
  have hbad (x) : MeasurableSet (bad x) ∧ infiniteSplitPi a (bad x) ≤ δ := by
    dsimp only [bad]
    split
    · let h := iid_block a (U x) False
      refine ⟨h.1, ?_⟩
      change infiniteSplitPi a (blockEvent (U x) False) ≤ 2*detourRisk a k
      rw [infiniteSplitPi, h.2, ambientCoordLaw_false, show (U x).card = k by simp [U], detourRisk, two_mul]
      refine (pow_le_pow_left' ?_ k).trans le_self_add
      exact (ENNReal.toReal_le_toReal (by simp) (by simp)).mp (by simp; nlinarith [a.property.1, a.property.2])
    · simp
  -- On the complement of the detour failure, every missing molecule is
  -- charged to a failed block. Apply Markov's inequality to the scaled count.
  obtain hU | hU := isEmpty_or_nonempty (Molecule N)
  · simp [nearFullPoolSize]
  let F (x) := (bad x).indicator (fun _ => (m : ENNReal))
  have hF (x) : Measurable (F x) := measurable_const.indicator (hbad x).1
  refine measure_le_add_of_cover (B := {ω | (Fintype.card (Molecule N) : ENNReal) ≤ ∑ x, F x ω})
    ?_ (measure_shortFailure g a k hk hθ) ?_
  · intro ω hsmall
    refine or_iff_not_imp_left.mpr fun hω => ?_
    let B := Finset.univ.filter fun x => ω ∈ bad x
    have hsub : (pool ω)ᶜ ⊆ B := by
      intro x hx_bad
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hx
      let w := moleculeWord x
      have hN : w.length ≤ N := moleculeWord_cap x
      have hgen : FiniteReversibleGenerated N (10*k) (pullbackField g ω) w := by
        by_cases hxT : w.length ≤ T
        · exact generate_short hk hω w (moleculeWord_nonempty x) (le_min hN hxT)
        simp [-moleculeWord_length, bad, U, blockEvent, w, lt_of_not_ge hxT] at hx
        obtain ⟨i,hi⟩ := hx
        let j := cut x i
        rw [← List.take_append_drop j w]
        refine .ligate (generate_short hk hω _ ?_ ?_) (generate_short hk hω _ ?_ ?_) ?_
        all_goals try (rw [← List.length_pos_iff]; grind)
        all_goals try grind
        rw [List.take_append_drop, List.length_take_of_le (by grind), pullbackField, CutMap.relabel,
          C.fix_short (w,j) (by grind)]
        exact ⟨hN,hi⟩
      obtain ⟨y,hy,he⟩ := (finiteReversible_iff_literalClosure _ _).mp hgen
      exact (Finset.mem_compl.mp hx_bad) (moleculeWord_injective he ▸ hy)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_compl] at hc
    have := Nat.mul_div_le (Fintype.card (Molecule N)) m
    change (pool ω).card < _ at hsmall
    rw [nearFullPoolSize, Nat.sub_mul, one_mul] at hsmall
    simp only [F, Set.mem_ofPred_eq, Set.indicator_apply, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, ← Nat.cast_mul]
    exact_mod_cast ((Nat.div_lt_iff_lt_mul (by grind : 0 < m)).mp (show Fintype.card (Molecule N) / m < B.card by omega)).le
  refine (ENNReal.mul_le_mul_iff_right (by exact_mod_cast Fintype.card_ne_zero) (by finiteness)).mp
    ((mul_meas_ge_le_lintegral (Finset.measurable_sum _ fun x _ => hF x) _).trans ?_)
  rw [lintegral_finsetSum _ (fun x _ => hF x)]
  simpa [nsmul_eq_mul, F, lintegral_indicator, fun x => (hbad x).1] using
    Finset.sum_le_card_nsmul Finset.univ _ ((m : ENNReal)*δ) (fun x _ => mul_le_mul' le_rfl (hbad x).2)

end

variable (a : I) (K : ℕ)

noncomputable def splitEscapeProbability : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w}

noncomputable def quotientEscapeProbability : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w}

end RAFCriticalWindowQuantitative
