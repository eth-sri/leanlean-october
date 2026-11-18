module

public import proofs.HordijkSteelThreshold.StaticClosureMass

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped ENNReal Topology

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

def ReversibleUnbounded (L : ℕ) (field : InfiniteSplitEnvironment) : Prop :=
  ∀ K : ℕ, ∃ w, K < w.length ∧ InfiniteReversibleGenerated L field w

def currySplitField (ω : (List Bool × ℕ) → Prop) : InfiniteSplitEnvironment :=
  fun w k => ω (w,k)

theorem measurable_currySplitField : Measurable currySplitField :=
  Measurable.of_eval fun w => Measurable.of_eval fun k => measurable_pi_apply (w, k)

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

noncomputable def staticSurvival (a : I) : ENNReal :=
  infiniteStaticMeasure a {field | ReversibleUnbounded 2 field}

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
    (h : FiniteReversibleGenerated N L field w) : FiniteReversibleGenerated M L field w := by
  induction h with
  | food hn hL hN => exact .food hn hL (hN.trans hNM)
  | ligate _ _ ho hN ihu ihv => exact .ligate ihu ihv ho (hN.trans hNM)
  | left hu hv _ ho ih => exact .left hu hv ih ho
  | right hu hv _ ho ih => exact .right hu hv ih ho

theorem finiteReversibleGenerated_length_le {N L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : FiniteReversibleGenerated N L field w) : w.length ≤ N := by
  induction h with
  | food _ _ hN => exact hN
  | ligate _ _ _ hN _ _ => exact hN
  | left _ _ _ _ ih => simp at ih; omega
  | right _ _ _ _ ih => simp at ih; omega

theorem finiteReversibleGenerated_to_infinite {N L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : FiniteReversibleGenerated N L field w) : InfiniteReversibleGenerated L field w := by
  induction h with
  | food hn hL _ => exact .food hn hL
  | ligate _ _ ho _ ihu ihv => exact .ligate ihu ihv ho
  | left hu hv _ ho ih => exact .left hu hv ih ho
  | right hu hv _ ho ih => exact .right hu hv ih ho

theorem generated_or_bounded_record {L B : ℕ} (hLB : L ≤ B)
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : InfiniteReversibleGenerated L field w) :
    FiniteReversibleGenerated B L field w ∨
      ∃ v, B < v.length ∧ v.length ≤ 2 * B ∧ FiniteReversibleGenerated v.length L field v := by
  induction h with
  | food hn hL => exact .inl (.food hn hL (hL.trans hLB))
  | @ligate u v _ _ ho ihu ihv =>
    rcases ihu with hu | he
    · rcases ihv with hv | he
      · by_cases hlen : (u ++ v).length ≤ B
        · exact .inl (.ligate hu hv ho hlen)
        · have hb : B ≤ (u ++ v).length := by omega
          have := finiteReversibleGenerated_length_le hu
          have := finiteReversibleGenerated_length_le hv
          exact .inr ⟨u ++ v, by omega, by simp; omega, .ligate
            (finiteReversibleGenerated_mono_cap hb hu) (finiteReversibleGenerated_mono_cap hb hv) ho le_rfl⟩
      · exact .inr he
    · exact .inr he
  | left hu hv _ ho ih => exact ih.imp (fun hp => .left hu hv hp ho) id
  | right hu hv _ ho ih => exact ih.imp (fun hp => .right hu hv hp ho) id

theorem infiniteReversibleGenerated_finite_certificate {L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : InfiniteReversibleGenerated L field w) : ∃ N, FiniteReversibleGenerated N L field w := by
  induction h with
  | @food w hn hL => exact ⟨w.length, .food hn hL le_rfl⟩
  | @ligate u v _ _ ho ihu ihv =>
    obtain ⟨N, hN⟩ := ihu; obtain ⟨M, hM⟩ := ihv
    exact ⟨max (max N M) (u ++ v).length, .ligate
      (finiteReversibleGenerated_mono_cap (by omega) hN)
      (finiteReversibleGenerated_mono_cap (by omega) hM) ho (by omega)⟩
  | left hu hv _ ho ih => obtain ⟨N, hN⟩ := ih; exact ⟨N, .left hu hv hN ho⟩
  | right hu hv _ ho ih => obtain ⟨N, hN⟩ := ih; exact ⟨N, .right hu hv hN ho⟩

noncomputable def restrictedSplitReactions (N : ℕ) (field : InfiniteSplitEnvironment) :
    Finset (Reaction N) :=
  Finset.univ.filter fun r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r)

theorem moleculeWord_nonempty {N : ℕ} (x : Molecule N) : moleculeWord x ≠ [] :=
  List.length_pos_iff.mp (moleculeWord_length x ▸ Nat.succ_pos _)

theorem moleculeWord_cap {N : ℕ} (x : Molecule N) : (moleculeWord x).length ≤ N :=
  moleculeWord_length x ▸ x.1.isLt

theorem reaction_words_append {N : ℕ} (r : Reaction N) :
    moleculeWord (reactionLeft r) ++ moleculeWord (reactionRight r) = moleculeWord (reactionProduct r) := by
  rw [moleculeWord_reactionLeft, moleculeWord_reactionRight, List.take_append_drop]

theorem literalClosure_to_finiteReversible {N L : ℕ} (field : InfiniteSplitEnvironment)
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure L (restrictedSplitReactions N field)) :
    FiniteReversibleGenerated N L field (moleculeWord x) := by
  refine temporaryReactionClosure_induction (restrictedSplitReactions N field)
    (fun y => FiniteReversibleGenerated N L field (moleculeWord y))
    (fun y hy => .food (moleculeWord_nonempty y) (by rwa [moleculeWord_length]) (moleculeWord_cap y))
    (fun r hr hl hh => ?_) (fun r hr hp => ?_) x hx
  · have ho := (Finset.mem_filter.mp hr).2
    rw [← reaction_words_append r] at ho ⊢
    exact .ligate hl hh (by simpa [moleculeWord_length] using ho) (reaction_words_append r ▸ moleculeWord_cap _)
  · have ho := (Finset.mem_filter.mp hr).2
    rw [← reaction_words_append r] at ho hp
    have hf : field (moleculeWord (reactionLeft r) ++ moleculeWord (reactionRight r))
        (moleculeWord (reactionLeft r)).length := by simpa [moleculeWord_length] using ho
    exact ⟨.left (moleculeWord_nonempty _) (moleculeWord_nonempty _) hp hf,
      .right (moleculeWord_nonempty _) (moleculeWord_nonempty _) hp hf⟩

theorem finiteReversible_to_literalClosure {N L : ℕ} {field : InfiniteSplitEnvironment}
    {w : List Bool} (hw : FiniteReversibleGenerated N L field w) :
    ∃ x ∈ temporaryReactionClosure L (restrictedSplitReactions N field), moleculeWord x = w := by
  let S := restrictedSplitReactions N field
  have smem (u v : List Bool) (r : Reaction N) (hl : moleculeWord (reactionLeft r) = u)
      (hp : moleculeWord (reactionProduct r) = u ++ v) (ho : field (u ++ v) u.length) : r ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [hp, ← molLength_reactionLeft, ← moleculeWord_length, hl] using ho⟩
  have clv {u v : List Bool} (hu : u ≠ []) (hv : v ≠ []) (ho : field (u ++ v) u.length)
      (ih : ∃ x ∈ temporaryReactionClosure L S, moleculeWord x = u ++ v) :
      (∃ x ∈ temporaryReactionClosure L S, moleculeWord x = u) ∧
      (∃ y ∈ temporaryReactionClosure L S, moleculeWord y = v) := by
    obtain ⟨x, hx, hxp⟩ := ih
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) u v (List.length_pos_iff.mpr hu)
      (List.length_pos_iff.mpr hv) (by rw [← List.length_append, ← hxp]; exact moleculeWord_cap x)
    have hc := temporaryReactionClosure_cleavage S r (smem u v r hl hp ho)
      (moleculeWord_injective (hp.trans hxp.symm) ▸ hx)
    exact ⟨⟨_, hc.1, hl⟩, ⟨_, hc.2, hr⟩⟩
  induction hw with
  | @food w hn hL hN =>
    exact ⟨sourceWordMolecule w (List.length_pos_iff.mpr hn) hN,
      temporaryReactionClosure_food S _ (by simpa using hL), sourceWordMolecule_word _ _ _⟩
  | @ligate u v _ _ ho hN ihu ihv =>
    obtain ⟨x, hx, hxu⟩ := ihu; obtain ⟨y, hy, hyv⟩ := ihv
    obtain ⟨r, hl, hr, hp⟩ := source_append_split (N := N) u v
      (List.length_pos_iff.mpr (hxu ▸ moleculeWord_nonempty x))
      (List.length_pos_iff.mpr (hyv ▸ moleculeWord_nonempty y)) (by simpa using hN)
    exact ⟨reactionProduct r, temporaryReactionClosure_ligation S r (smem u v r hl hp ho)
      (moleculeWord_injective (hl.trans hxu.symm) ▸ hx) (moleculeWord_injective (hr.trans hyv.symm) ▸ hy), hp⟩
  | left hu hv _ ho ih => exact (clv hu hv ho ih).1
  | right hu hv _ ho ih => exact (clv hu hv ho ih).2

theorem finiteReversible_iff_literalClosure {N L : ℕ} (field : InfiniteSplitEnvironment)
    (w : List Bool) : FiniteReversibleGenerated N L field w ↔
      ∃ x ∈ temporaryReactionClosure L (restrictedSplitReactions N field), moleculeWord x = w :=
  ⟨finiteReversible_to_literalClosure, fun ⟨x, hx, he⟩ => he ▸ literalClosure_to_finiteReversible field x hx⟩

theorem measurableSet_finiteReversibleGenerated (N L : ℕ) (w : List Bool) :
    MeasurableSet {field : InfiniteSplitEnvironment | FiniteReversibleGenerated N L field w} := by
  have hm : Measurable fun field : InfiniteSplitEnvironment =>
      ∃ x ∈ temporaryReactionClosure L (Finset.univ.filter fun r : Reaction N =>
        field (moleculeWord (reactionProduct r)) (reactionLeftLength r)), moleculeWord x = w :=
    (measurable_of_finite (fun ω : Reaction N → Prop =>
      ∃ x ∈ temporaryReactionClosure L (Finset.univ.filter ω), moleculeWord x = w)).comp
      (Measurable.of_eval fun r => (measurable_pi_apply _).comp (measurable_pi_apply _))
  rw [show {field : InfiniteSplitEnvironment | FiniteReversibleGenerated N L field w} =
      {field | ∃ x ∈ temporaryReactionClosure L (restrictedSplitReactions N field), moleculeWord x = w} by
      ext f; exact finiteReversible_iff_literalClosure f w]
  simpa [restrictedSplitReactions] using (MeasurableSet.singleton True).preimage hm

theorem measurableSet_infiniteReversibleGenerated (L : ℕ) (w : List Bool) :
    MeasurableSet {field : InfiniteSplitEnvironment | InfiniteReversibleGenerated L field w} := by
  rw [show {field : InfiniteSplitEnvironment | InfiniteReversibleGenerated L field w} =
      ⋃ N : ℕ, {field | FiniteReversibleGenerated N L field w} by
      ext; simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      exact ⟨infiniteReversibleGenerated_finite_certificate, fun ⟨_, h⟩ => finiteReversibleGenerated_to_infinite h⟩]
  exact MeasurableSet.iUnion fun N => measurableSet_finiteReversibleGenerated N L w

theorem finite_seed_probability_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → InfiniteSplitEnvironment) (L : ℕ) (seed : Finset (List Bool)) :
    Tendsto (fun N => μ {ω | ∀ w ∈ seed, FiniteReversibleGenerated N L (F ω) w})
      atTop (nhds (μ {ω | ∀ w ∈ seed, InfiniteReversibleGenerated L (F ω) w})) := by
  have hcap (field : InfiniteSplitEnvironment) :
      (∀ w ∈ seed, InfiniteReversibleGenerated L field w) ↔
        ∃ N, ∀ w ∈ seed, FiniteReversibleGenerated N L field w := by
    refine ⟨?_, fun ⟨N, hN⟩ w hw => finiteReversibleGenerated_to_infinite (hN w hw)⟩
    induction seed using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp⟩
    | insert w s _ ih =>
      intro h
      obtain ⟨N, hN⟩ := infiniteReversibleGenerated_finite_certificate (h w (Finset.mem_insert_self _ _))
      obtain ⟨M, hM⟩ := ih fun v hv => h v (Finset.mem_insert_of_mem hv)
      exact ⟨max N M, fun v hv => (Finset.mem_insert.mp hv).elim
        (fun he => he ▸ finiteReversibleGenerated_mono_cap (Nat.le_max_left _ _) hN)
        (fun hv => finiteReversibleGenerated_mono_cap (Nat.le_max_right _ _) (hM v hv))⟩
  have ht := tendsto_measure_iUnion_atTop (μ := μ)
    (s := fun N => {ω | ∀ w ∈ seed, FiniteReversibleGenerated N L (F ω) w})
    fun _ _ hNM _ hf w hw => finiteReversibleGenerated_mono_cap hNM (hf w hw)
  rwa [show (⋃ N, {ω : Ω | ∀ w ∈ seed, FiniteReversibleGenerated N L (F ω) w}) =
    {ω | ∀ w ∈ seed, InfiniteReversibleGenerated L (F ω) w} by ext ω; simp [hcap (F ω)]] at ht

theorem measurableSet_reversibleUnbounded (L : ℕ) :
    MeasurableSet {field : InfiniteSplitEnvironment | ReversibleUnbounded L field} := by
  rw [show {field : InfiniteSplitEnvironment | ReversibleUnbounded L field} =
      ⋂ K : ℕ, ⋃ w : List Bool, ⋃ (_ : K < w.length), {field | InfiniteReversibleGenerated L field w} by
      ext; simp [ReversibleUnbounded]]
  exact MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun w =>
    MeasurableSet.iUnion fun _ => measurableSet_infiniteReversibleGenerated L w

def reversibleEscapeEvent (L K : ℕ) : Set InfiniteSplitEnvironment :=
  {field | ∃ w, K + L < w.length ∧ FiniteReversibleGenerated (2 * (K + L)) L field w}

theorem reversibleEscapeEvent_iff (L K : ℕ) (field : InfiniteSplitEnvironment) :
    field ∈ reversibleEscapeEvent L K ↔
      ∃ w, K + L < w.length ∧ InfiniteReversibleGenerated L field w := by
  refine ⟨fun ⟨w, hw, hg⟩ => ⟨w, hw, finiteReversibleGenerated_to_infinite hg⟩, fun ⟨w, hw, hg⟩ => ?_⟩
  rcases generated_or_bounded_record (Nat.le_add_left L K) hg with hf | ⟨v, hv1, hv2, hvf⟩
  · exact ⟨w, hw, finiteReversibleGenerated_mono_cap (by omega) hf⟩
  · exact ⟨v, hv1, finiteReversibleGenerated_mono_cap hv2 hvf⟩

theorem measurableSet_reversibleEscapeEvent (L K : ℕ) :
    MeasurableSet (reversibleEscapeEvent L K) := by
  rw [show reversibleEscapeEvent L K = ⋃ w : List Bool, ⋃ (_ : K + L < w.length),
      {field | FiniteReversibleGenerated (2 * (K + L)) L field w} by ext; simp [reversibleEscapeEvent]]
  exact MeasurableSet.iUnion fun w => MeasurableSet.iUnion fun _ => measurableSet_finiteReversibleGenerated _ _ w

theorem reversible_escape_probability_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Ω → InfiniteSplitEnvironment) (hF : Measurable F) (L : ℕ) :
    Tendsto (fun K => μ {ω | F ω ∈ reversibleEscapeEvent L K}) atTop
      (nhds (μ {ω | ReversibleUnbounded L (F ω)})) := by
  have hint : (⋂ K, {ω | F ω ∈ reversibleEscapeEvent L K}) = {ω | ReversibleUnbounded L (F ω)} := by
    ext ω; simp only [Set.mem_iInter, Set.mem_ofPred_eq, reversibleEscapeEvent_iff, ReversibleUnbounded]
    exact ⟨fun h K => let ⟨w, hw, hg⟩ := h K; ⟨w, by omega, hg⟩, fun h K => h (K + L)⟩
  rw [← hint]
  exact tendsto_measure_iInter_atTop
    (fun K => ((measurableSet_reversibleEscapeEvent L K).preimage hF).nullMeasurableSet)
    (fun K M hKM ω h => let ⟨w, hw, hg⟩ := (reversibleEscapeEvent_iff L M (F ω)).mp h
      (reversibleEscapeEvent_iff L K (F ω)).mpr ⟨w, by omega, hg⟩)
    ⟨0, measure_ne_top _ _⟩

theorem infinite_seed_le_survival {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Ω → InfiniteSplitEnvironment) (hF : Measurable F) {m L : ℕ} (hm : 2 ≤ m)
    (hbad : ∀ N, 0 < N → μ {ω | m * (temporaryReactionClosure L (restrictedSplitReactions N (F ω))).card <
      (m - 1) * Fintype.card (Molecule N)} ≤ (m : ENNReal)⁻¹) :
    μ {ω | ∀ w ∈ actualBinaryWords L, InfiniteReversibleGenerated 2 (F ω) w} ≤
      μ {ω | ReversibleUnbounded 2 (F ω)} + (m : ENNReal)⁻¹ := by
  refine ge_of_tendsto' ((reversible_escape_probability_tendsto μ F hF 2).add_const _)
    fun K => le_of_tendsto (finite_seed_probability_tendsto μ F 2 _) ?_
  filter_upwards [(tendsto_atTop.mp card_molecule_tendsto_atTop) (m * Fintype.card (Molecule (K + 2)) + 1),
    eventually_ge_atTop 1] with N hlarge hN
  refine (measure_mono fun ω hω => ?_).trans ((measure_union_le _ _).trans (add_le_add le_rfl (hbad N hN)))
  by_cases hb : m * (temporaryReactionClosure L (restrictedSplitReactions N (F ω))).card < (m - 1) * Fintype.card (Molecule N)
  · exact .inr hb
  · refine .inl ?_
    have hsub : temporaryReactionClosure L (restrictedSplitReactions N (F ω)) ⊆
        temporaryReactionClosure 2 (restrictedSplitReactions N (F ω)) :=
      temporaryReactionClosure_seed_transfer Finset.Subset.rfl fun x hx =>
        let ⟨y, hy, he⟩ := finiteReversible_to_literalClosure
          (hω _ ((mem_actualBinaryWords _ _).mpr ⟨moleculeWord_nonempty x, moleculeWord_length x ▸ hx⟩))
        moleculeWord_injective he ▸ hy
    have hc2 := (Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card hsub))
    by_contra h
    have hc := (Finset.card_le_card (t := binaryFood N (K + 2)) fun x hx =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_gt fun hl => h ((reversibleEscapeEvent_iff 2 K (F ω)).mpr
        ⟨moleculeWord x, by simpa [moleculeWord_length] using hl,
          finiteReversibleGenerated_to_infinite (literalClosure_to_finiteReversible _ x hx)⟩)⟩).trans
      (binaryFood_card_le_cutoff N (K + 2))
    have hm1 : Fintype.card (Molecule N) ≤ (m - 1) * Fintype.card (Molecule N) := by
      simpa using Nat.mul_le_mul_right (Fintype.card (Molecule N)) (show 1 ≤ m - 1 by omega)
    nlinarith

noncomputable def literalSplitCoordinate {N : ℕ} (r : Reaction N) : List Bool × ℕ :=
  (moleculeWord (reactionProduct r), reactionLeftLength r)

theorem literalSplitCoordinate_injective (N : ℕ) : Function.Injective (@literalSplitCoordinate N) := by
  rintro ⟨kr, cr, sr⟩ ⟨ks, cs, ss⟩ he
  have hp := moleculeWord_injective (congrArg Prod.fst he)
  obtain rfl : kr = ks := congrArg Sigma.fst hp
  obtain rfl : cr = cs := Fin.ext (congrArg (fun x : Molecule N => x.2.1) hp)
  have hk := congrArg Prod.snd he; dsimp [literalSplitCoordinate, reactionLeftLength] at hk
  exact congrArg (fun s => (⟨kr, cr, s⟩ : Reaction N)) (Fin.ext (by omega))

theorem infiniteSplitPi_proj {α : Type*} [Fintype α] (c : α → List Bool × ℕ)
    (hc : Function.Injective c) (a : I) :
    (infiniteSplitPi a).map (fun ω x => ω (c x)) = Measure.pi (fun _ : α => ambientCoordLaw a) := by
  have hi : iIndepFun (fun z (ω : (List Bool × ℕ) → Prop) => ω z) (infiniteSplitPi a) :=
    iIndepFun_infinitePi fun _ => measurable_id
  rw [(hi.precomp hc).map_fun_eq_pi_map fun x => (measurable_pi_apply (c x)).aemeasurable]
  simp_rw [infiniteSplitPi, Measure.infinitePi_map_eval]

theorem proj_closure_measure {α : Type*} [Fintype α] (c : α → List Bool × ℕ) (hc : Function.Injective c)
    {N L : ℕ} (cl : (α → Prop) → Finset (Molecule N)) (F : ((List Bool × ℕ) → Prop) → InfiniteSplitEnvironment)
    (hcl : ∀ ω, cl (fun x => ω (c x)) = temporaryReactionClosure L (restrictedSplitReactions N (F ω)))
    (a : I) (P : Finset (Molecule N) → Prop) :
    Measure.pi (fun _ : α => ambientCoordLaw a) {q | P (cl q)} =
      infiniteSplitPi a {ω | P (temporaryReactionClosure L (restrictedSplitReactions N (F ω)))} := by
  rw [← infiniteSplitPi_proj c hc a,
    Measure.map_apply (Measurable.of_eval fun _ => measurable_pi_apply _) (Set.toFinite _).measurableSet]
  congr 1; ext ω; exact Iff.of_eq (congrArg P (hcl ω))

theorem proj_escape_measure {α : Type*} [Fintype α] {L K : ℕ} (c : α → List Bool × ℕ) (hc : Function.Injective c)
    (cl : (α → Prop) → Finset (Molecule (2 * (K + L)))) (F : ((List Bool × ℕ) → Prop) → InfiniteSplitEnvironment)
    (hcl : ∀ ω, cl (fun x => ω (c x)) = temporaryReactionClosure L (restrictedSplitReactions (2 * (K + L)) (F ω)))
    (a : I) :
    Measure.pi (fun _ : α => ambientCoordLaw a) {q | ∃ x ∈ cl q, K + L < (moleculeWord x).length} =
      infiniteSplitPi a {ω | F ω ∈ reversibleEscapeEvent L K} := by
  rw [proj_closure_measure c hc cl F hcl a fun C => ∃ x ∈ C, K + L < (moleculeWord x).length]
  congr 1; ext ω
  exact ⟨fun ⟨x, hx, hl⟩ => ⟨moleculeWord x, hl, literalClosure_to_finiteReversible _ x hx⟩,
    fun ⟨w, hw, hg⟩ => let ⟨x, hx, he⟩ := finiteReversible_to_literalClosure hg; ⟨x, hx, he ▸ hw⟩⟩

theorem proj_capped_escape_le {α : Type*} [Fintype α] {N K : ℕ} (c : α → List Bool × ℕ) (hc : Function.Injective c)
    (cl : (α → Prop) → Finset (Molecule N)) (F : ((List Bool × ℕ) → Prop) → InfiniteSplitEnvironment)
    (hcl : ∀ ω, cl (fun x => ω (c x)) = temporaryReactionClosure 2 (restrictedSplitReactions N (F ω)))
    (a : I) :
    Measure.pi (fun _ : α => ambientCoordLaw a) {q | ∃ x ∈ cl q, K + 2 < molLength x} ≤
      infiniteSplitPi a {ω | F ω ∈ reversibleEscapeEvent 2 K} := by
  rw [proj_closure_measure c hc cl F hcl a fun C => ∃ x ∈ C, K + 2 < molLength x]
  exact measure_mono fun ω ⟨x, hx, hl⟩ => (reversibleEscapeEvent_iff 2 K (F ω)).mpr
    ⟨moleculeWord x, by simpa [moleculeWord_length] using hl,
      finiteReversibleGenerated_to_infinite (literalClosure_to_finiteReversible _ x hx)⟩

def staticEscapeEvent (L K : ℕ) : Set (Reaction (2 * (K + L)) → Prop) :=
  {ω | ∃ x ∈ temporaryReactionClosure L (staticOpenReactions ω), K + L < (moleculeWord x).length}

theorem finite_static_escape_measure_eq (L K : ℕ) (a : I) :
    staticReactionMeasure (2 * (K + L)) a (staticEscapeEvent L K) =
      infiniteSplitPi a {ω | currySplitField ω ∈ reversibleEscapeEvent L K} := by
  rw [staticReactionMeasure, Measure.infinitePi_eq_pi]
  exact proj_escape_measure literalSplitCoordinate (literalSplitCoordinate_injective _) _ currySplitField (fun _ => rfl) a

theorem static_capped_escape_le (N K : ℕ) (a : I) :
    staticReactionMeasure N a {ω | ∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions ω), K + 2 < molLength x} ≤
      infiniteSplitPi a {ω | currySplitField ω ∈ reversibleEscapeEvent 2 K} := by
  rw [staticReactionMeasure, Measure.infinitePi_eq_pi]
  exact proj_capped_escape_le literalSplitCoordinate (literalSplitCoordinate_injective _) _ currySplitField (fun _ => rfl) a

theorem staticSurvival_le_finite_escape (a : I) (K : ℕ) :
    staticSurvival a ≤ staticReactionMeasure (2 * (K + 2)) a (staticEscapeEvent 2 K) := by
  rw [staticSurvival, infiniteStaticMeasure,
    Measure.map_apply measurable_currySplitField (measurableSet_reversibleUnbounded 2), finite_static_escape_measure_eq]
  exact measure_mono fun _ h => (reversibleEscapeEvent_iff 2 K _).mpr (h (K + 2))

abbrev SplitField := (List Bool × ℕ) → Prop

def SplitPrefixDetermined (P : Finset (List Bool × ℕ)) (E : Set SplitField) : Prop :=
  ∀ ω η, (∀ z ∈ P, ω z = η z) → (ω ∈ E ↔ η ∈ E)

def splitPrefixCoordinates (M : ℕ) : Finset (List Bool × ℕ) :=
  (shortBinaryWords M).product (Finset.range (M + 1))

@[simp] theorem mem_splitPrefixCoordinates (M : ℕ) (z : List Bool × ℕ) :
    z ∈ splitPrefixCoordinates M ↔ z.1.length ≤ M ∧ z.2 ≤ M := by
  simp [splitPrefixCoordinates, mem_shortBinaryWords]

theorem measurableSet_of_splitPrefixDetermined (P : Finset (List Bool × ℕ))
    (E : Set SplitField) (hE : SplitPrefixDetermined P E) : MeasurableSet E := by
  obtain ⟨e, rfl⟩ := iid_prefix_determined_measurable P E hE
  simpa using (MeasurableSet.singleton True).preimage
    ((measurable_of_finite e).comp (Measurable.of_eval fun z => measurable_pi_apply z.1))

theorem split_prefix_failure_measure (a : I) (P T : Finset (List Bool × ℕ))
    (hPT : Disjoint P T) (E : Set SplitField) (hE : SplitPrefixDetermined P E) :
    infiniteSplitPi a (E ∩ {ω | ¬ ∀ z ∈ T, ω z}) =
      infiniteSplitPi a E * (1 - (toNNReal a : ENNReal) ^ T.card) :=
  iid_prefix_failure_measure a P T hPT E hE

theorem finiteReversibleGenerated_transfer_prefix {N M L : ℕ} (hNM : N ≤ M)
    {field other : InfiniteSplitEnvironment}
    (he : ∀ w : List Bool, w.length ≤ M → ∀ k : ℕ, k ≤ M → field w k = other w k)
    {w : List Bool} (h : FiniteReversibleGenerated N L field w) :
    FiniteReversibleGenerated N L other w := by
  induction h with
  | food hn hL hN => exact .food hn hL hN
  | @ligate u v _ _ ho hN ihu ihv =>
    exact .ligate ihu ihv (he (u ++ v) (hN.trans hNM) u.length (by simp at hN; omega) ▸ ho) hN
  | @left u v hu hv hp ho ih =>
    have hlen := finiteReversibleGenerated_length_le hp
    exact .left hu hv ih (he (u ++ v) (hlen.trans hNM) u.length (by simp at hlen; omega) ▸ ho)
  | @right u v hu hv hp ho ih =>
    have hlen := finiteReversibleGenerated_length_le hp
    exact .right hu hv ih (he (u ++ v) (hlen.trans hNM) u.length (by simp at hlen; omega) ▸ ho)

end HordijkSteelThreshold

namespace RAFReactionQuotient
open Classical Filter MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

theorem closureAt_image {M R J : Type*} [DecidableEq M] [DecidableEq J]
    (Q : ReversibleCRS M R) (P : ReversibleCRS M J)
    (π : R → J) (hl : ∀ r, P.lhs (π r) = Q.lhs r)
    (hr : ∀ r, P.rhs (π r) = Q.rhs r) (hf : P.food = Q.food)
    (S : Finset R) : ∀ k : ℕ, revClosureAt P (S.image π) k = revClosureAt Q S k
  | 0 => hf
  | k + 1 => by
    simp only [revClosureAt, closureAt_image Q P π hl hr hf S k, revClosureStep]
    congr 1; ext; simp [Finset.mem_biUnion, RevEnabledLhs, RevEnabledRhs, hl, hr]

abbrev OrderedChannel (n : ℕ) :=
  {uv : Molecule n × Molecule n // molLength uv.1 + molLength uv.2 ≤ n}

theorem precedes_total {n : ℕ} (u v : Molecule n) :
    moleculePrecedes u v ∨ moleculePrecedes v u := by
  unfold moleculePrecedes; omega

def canonical {n : ℕ} (r : OrderedChannel n) : RepositoryChannel n :=
  if h : displayedConcat r.val.1 r.val.2 ≠ displayedConcat r.val.2 r.val.1 ∨
      moleculePrecedes r.val.1 r.val.2 then
    ⟨r.val, r.property, h⟩
  else
    ⟨(r.val.2, r.val.1), (Nat.add_comm (molLength r.val.2) (molLength r.val.1)).le.trans r.property,
      Or.inr ((precedes_total r.val.1 r.val.2).resolve_left (fun hp => h (Or.inr hp)))⟩

def splitToOrdered {n : ℕ} (r : Reaction n) : OrderedChannel n :=
  ⟨(reactionLeft r, reactionRight r), by
    simp only [molLength_reactionLeft, molLength_reactionRight, reaction_length_add]
    exact Nat.succ_le_of_lt r.1.isLt⟩

def splitToQuotient {n : ℕ} (r : Reaction n) : RepositoryChannel n :=
  canonical (splitToOrdered r)

theorem molecule_ext {n : ℕ} {x y : Molecule n}
    (hl : molLength x = molLength y) (hc : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨i, x⟩; rcases y with ⟨j, y⟩
  obtain rfl : i = j := Fin.ext (by dsimp [molLength] at hl; omega)
  exact congrArg (Sigma.mk i) (Fin.ext hc)

theorem concat_code {n : ℕ} (u v : Molecule n) (h : molLength u + molLength v ≤ n) :
    (concatMolecule u v h).2.val = displayedConcat u v := by
  simp [concatMolecule, moleculeOfCode, concatCode, displayedConcat, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

theorem split_concat {n : ℕ} (r : Reaction n) :
    concatMolecule (reactionLeft r) (reactionRight r) (splitToOrdered r).property =
      reactionProduct r := by
  refine molecule_ext ((molLength_moleculeOfCode _ _ _).trans ?_) ?_
  · rw [molLength_reactionLeft, molLength_reactionRight, reaction_length_add, molLength_reactionProduct]
  · rw [concat_code (reactionLeft r) (reactionRight r) (splitToOrdered r).property,
      displayedConcat, molLength_reactionRight]
    change r.2.1.val / 2 ^ reactionRightLength r * 2 ^ reactionRightLength r +
      r.2.1.val % 2 ^ reactionRightLength r = r.2.1.val
    simpa only [Nat.mul_comm] using Nat.div_add_mod r.2.1.val (2 ^ reactionRightLength r)

theorem split_closure_eq_quotient {n : ℕ} (t : ℕ) (S : Finset (Reaction n)) (k : ℕ) :
    revClosureAt (repositoryCRS n t) (S.image splitToQuotient) k =
      revClosureAt (binaryPolymerCRS n t) S k := by
  refine closureAt_image _ _ splitToQuotient (fun r => ?_) (fun r => ?_) rfl S k
  · unfold splitToQuotient canonical; split <;> simp [repositoryCRS, binaryPolymerCRS, splitToOrdered, Finset.pair_comm]
  · unfold splitToQuotient canonical
    split
    · change {concatMolecule (reactionLeft r) (reactionRight r) _} = {reactionProduct r}; rw [split_concat]
    · rename_i h
      have hc : displayedConcat (reactionLeft r) (reactionRight r) = displayedConcat (reactionRight r) (reactionLeft r) :=
        Classical.byContradiction fun hn => h (.inl hn)
      change {concatMolecule (reactionRight r) (reactionLeft r) _} = {reactionProduct r}
      rw [← split_concat r]; congr 1
      exact molecule_ext ((molLength_moleculeOfCode _ _ _).trans ((Nat.add_comm _ _).trans (molLength_moleculeOfCode _ _ _).symm))
        ((concat_code _ _ _).trans (hc.symm.trans (concat_code _ _ _).symm))

theorem split_fibre_le_two {n : ℕ} (j : RepositoryChannel n) :
    (Finset.univ.filter fun r : Reaction n => splitToQuotient r = j).card ≤ 2 := by
  have hinj : Function.Injective (@splitToOrdered n) := fun ⟨ri, rw, rk⟩ ⟨si, sw, sk⟩ he => by
    have hp : reactionProduct ⟨ri, rw, rk⟩ = reactionProduct ⟨si, sw, sk⟩ := by
      rw [← split_concat, ← split_concat]
      exact congrArg (fun q : OrderedChannel n => concatMolecule q.1.1 q.1.2 q.2) he
    have hl : rk.val + 1 = sk.val + 1 := by
      simpa [splitToOrdered, molLength_reactionLeft, reactionLeftLength] using
        congrArg (fun q : OrderedChannel n => molLength q.1.1) he
    obtain rfl : ri = si := congrArg Sigma.fst hp
    obtain rfl : rw = sw := Fin.ext (congrArg (fun x : Molecule n => x.2.val) hp)
    exact congrArg (fun k => (⟨ri, rw, k⟩ : Reaction n)) (Fin.ext (by omega))
  let a : OrderedChannel n := ⟨j.1, j.2.1⟩
  let b : OrderedChannel n := ⟨j.1.swap, by have := j.2.1; dsimp; omega⟩
  have hsub : (Finset.univ.filter fun r : Reaction n => splitToQuotient r = j).image splitToOrdered ⊆ {a, b} := by
    rintro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    have he := (Finset.mem_filter.mp hr).2
    have hv : (canonical (splitToOrdered r)).1 = (splitToOrdered r).1 ∨
        (canonical (splitToOrdered r)).1 = (splitToOrdered r).1.swap := by
      unfold canonical; split <;> [exact .inl rfl; exact .inr rfl]
    rw [show canonical (splitToOrdered r) = j from he] at hv
    rcases hv with hv | hv
    · simp [show splitToOrdered r = a from Subtype.ext hv.symm]
    · simp [show splitToOrdered r = b from Subtype.ext (congrArg Prod.swap hv).symm]
  exact (Finset.card_image_of_injective _ hinj).symm.le.trans
    ((Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp)))

theorem splitToOrdered_surjective (n : ℕ) : Function.Surjective (@splitToOrdered n) := fun q => by
  obtain ⟨r, hl, hr, _⟩ := source_append_split (moleculeWord q.1.1) (moleculeWord q.1.2)
    (by rw [moleculeWord_length]; exact Nat.succ_pos _)
    (by rw [moleculeWord_length]; exact Nat.succ_pos _)
    (by simpa [moleculeWord_length] using q.2)
  exact ⟨r, Subtype.ext (Prod.ext (moleculeWord_injective hl) (moleculeWord_injective hr))⟩

theorem quotient_mark_pullback_OR {n : ℕ} (ω : RepositoryChannel n → Prop) (j : RepositoryChannel n) :
    (∃ r : Reaction n, splitToQuotient r = j ∧ ω (splitToQuotient r)) ↔ ω j := by
  refine ⟨fun ⟨_, hr, hw⟩ => hr ▸ hw, fun hj => ?_⟩
  obtain ⟨r, hr⟩ := splitToOrdered_surjective n ⟨j.1, j.2.1⟩
  have hc : splitToQuotient r = j := by simp [splitToQuotient, hr, canonical, dite_eq_left j.2.2]
  exact ⟨r, hc, hc.symm ▸ hj⟩

theorem noncanonical_strict_lengths {n : ℕ} (r : OrderedChannel n)
    (h : ¬ (displayedConcat r.val.1 r.val.2 ≠ displayedConcat r.val.2 r.val.1 ∨
      moleculePrecedes r.val.1 r.val.2)) : molLength r.val.2 < molLength r.val.1 := by
  have hc : displayedConcat r.1.1 r.1.2 = displayedConcat r.1.2 r.1.1 :=
    Classical.byContradiction fun hn => h (.inl hn)
  have hn : ¬ moleculePrecedes r.1.1 r.1.2 := fun hp => h (.inr hp)
  have hne : molLength r.1.1 ≠ molLength r.1.2 := fun he => hn <| by
    have : 1 < 2 ^ molLength r.1.1 := by
      unfold molLength; rw [pow_succ]; have : 0 < 2 ^ r.1.1.1.val := (by positivity); omega
    have hv : r.1.1 = r.1.2 := molecule_ext he (by unfold displayedConcat at hc; rw [← he] at hc; nlinarith)
    exact hv ▸ .inr ⟨rfl, le_rfl⟩
  unfold moleculePrecedes at hn; omega

noncomputable def quotientClosure (n L : ℕ) (S : Finset (RepositoryChannel n)) :
    Finset (Molecule n) := Finset.univ.filter fun x => ∃ k, x ∈ revClosureAt (repositoryCRS n L) S k

@[simp] theorem mem_quotientClosure {n L : ℕ} (S : Finset (RepositoryChannel n))
    (x : Molecule n) : x ∈ quotientClosure n L S ↔ ∃ k, x ∈ revClosureAt (repositoryCRS n L) S k := by
  simp [quotientClosure]

theorem quotientClosure_mono (n L : ℕ) : Monotone (quotientClosure n L) :=
  fun S T hST x hx => let ⟨k, hk⟩ := (mem_quotientClosure S x).mp hx
    (mem_quotientClosure T x).mpr ⟨k, revClosureAt_mono_reactions _ hST k hk⟩

noncomputable def quotientCatalyticLaw (n : ℕ) (p : I) :=
  RAFEmergenceApprox.Generic.law (X := Molecule n) (fun _ : RepositoryChannel n => p)

section
variable {R J : Type*} [Fintype R]

def fieldOR (π : R → J) (ω : R → Prop) (j : J) : Prop := ∃ r, π r = j ∧ ω r

noncomputable def fibreParameter (π : R → J) (p : I) (j : J) : I :=
  σ ((σ p) ^ (Finset.univ.filter fun r => π r = j).card)

theorem fibreParameter_value (π : R → J) (p : I) (j : J) :
    (fibreParameter π p j : ℝ) =
      1 - (1 - (p : ℝ)) ^ (Finset.univ.filter fun r => π r = j).card := by
  simp [fibreParameter]

/-- The complete quotient ensemble is a product law with its actual fibre probabilities. -/
theorem fieldOR_map [Fintype J] (π : R → J) (p : I) :
    (RAFEmergenceApprox.Generic.colLaw R p).map (fieldOR π) =
      Measure.pi fun j => ambientCoordLaw (fibreParameter π p j) := by
  have hfib : (RAFEmergenceApprox.Generic.colLaw R p).map
      (fun ω j (r : {r : R // π r = j}) => ω r.1) =
      Measure.pi fun j => RAFEmergenceApprox.Generic.colLaw {r : R // π r = j} p := by
    refine Measure.ext_of_singleton fun g => ?_
    rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton g),
      show (fun ω : R → Prop => fun j (r : {r : R // π r = j}) => ω r.1) ⁻¹' {g} =
        {fun r => g (π r) ⟨r, rfl⟩} by
          ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
          exact ⟨fun h r => h (π r) ⟨r, rfl⟩, fun h j ⟨r, hr⟩ => by subst hr; exact h r⟩,
      RAFEmergenceApprox.Generic.colLaw, pi_singleton, pi_singleton]
    simp_rw [RAFEmergenceApprox.Generic.colLaw, pi_singleton]
    exact (Fintype.prod_fiberwise π fun r => ambientCoordLaw p {g (π r) ⟨r, rfl⟩}).symm.trans
      (Finset.prod_congr rfl fun _ _ => Finset.prod_congr rfl fun ⟨_, hr⟩ _ => by subst hr; rfl)
  rw [show fieldOR π = (fun (g : ∀ j, {r : R // π r = j} → Prop) j => ∃ r ∈ Finset.univ, g j r) ∘
      (fun ω j (r : {r : R // π r = j}) => ω r.1) by ext ω j; simp [fieldOR, Subtype.exists],
    ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hfib,
    Measure.pi_map_pi (f := fun j (v : {r : R // π r = j} → Prop) => ∃ r ∈ Finset.univ, v r)
      fun _ => (measurable_of_finite _).aemeasurable]
  congr 1; funext j
  rw [RAFEmergenceApprox.Generic.pool_col_map, Finset.card_univ, Fintype.card_subtype]; rfl
end

noncomputable def halfParameter (a : I) : I :=
  ⟨(a : ℝ) / 2, div_nonneg a.2.1 zero_le_two, by linarith [a.2.2]⟩

theorem fibreParameter_half_le {R J : Type*} [Fintype R]
    (π : R → J) (a : I) (j : J)
    (hm : (Finset.univ.filter fun r => π r = j).card ≤ 2) :
    fibreParameter π (halfParameter a) j ≤ a := by
  change (fibreParameter π (halfParameter a) j : ℝ) ≤ (a : ℝ)
  rw [fibreParameter_value]
  have := a.2.1; have := a.2.2
  let m := (Finset.univ.filter fun r => π r = j).card
  change 1 - (1 - (a : ℝ) / 2) ^ m ≤ (a : ℝ)
  have : m ≤ 2 := hm
  interval_cases m <;> norm_num <;> nlinarith

noncomputable def quotientStaticMeasure (n : ℕ) (a : I) :=
  Measure.pi (fun _ : RepositoryChannel n => ambientCoordLaw a)

noncomputable def quotientOpen {n : ℕ} (ω : RepositoryChannel n → Prop) :
    Finset (RepositoryChannel n) := Finset.univ.filter ω

theorem quotientClosure_OR {n L : ℕ} (ω : Reaction n → Prop) :
    quotientClosure n L (quotientOpen (fieldOR splitToQuotient ω)) =
      temporaryReactionClosure L (staticOpenReactions ω) := by
  rw [show quotientOpen (fieldOR splitToQuotient ω) = (staticOpenReactions ω).image splitToQuotient by
    ext; simp [quotientOpen, fieldOR, staticOpenReactions, and_comm]]
  ext; simp [mem_quotientClosure, mem_temporaryReactionClosure, split_closure_eq_quotient]

theorem quotient_mass_failure_antitone (n L m : ℕ) :
    Antitone (fun ω : RepositoryChannel n → Prop =>
      m * (quotientClosure n L (quotientOpen ω)).card < (m - 1) * Fintype.card (Molecule n)) :=
  fun _ _ hxy hy => (Nat.mul_le_mul_left m (Finset.card_le_card (quotientClosure_mono n L
    fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy j (Finset.mem_filter.mp hj).2⟩))).trans_lt hy

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

noncomputable def criticalOpenness (lambda : ℝ) (hlambda : 0 < lambda) : I :=
  ⟨1-Real.exp (-lambda), by
    constructor
    · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    · linarith [Real.exp_pos (-lambda)]⟩

noncomputable def orderedCoordinate {n : ℕ} (r : OrderedChannel n) : List Bool × ℕ :=
  (moleculeWord r.1.1 ++ moleculeWord r.1.2, molLength r.1.1)

noncomputable def quotientCoordinate {n : ℕ} (j : RepositoryChannel n) : List Bool × ℕ :=
  orderedCoordinate ⟨j.1, j.2.1⟩

theorem canonicalIndex_split {n : ℕ} (r : Reaction n) :
    canonicalIndex (literalSplitCoordinate r) = quotientCoordinate (splitToQuotient r) := by
  have hosp : orderedCoordinate (splitToOrdered r) = literalSplitCoordinate r :=
    Prod.ext (reaction_words_append r) (molLength_reactionLeft r)
  rw [← hosp, splitToQuotient]
  let q := splitToOrdered r
  change canonicalIndex (orderedCoordinate q) = quotientCoordinate (canonical q)
  have hcomm {u v : Molecule n} : moleculeWord u ++ moleculeWord v = moleculeWord v ++ moleculeWord u ↔
      displayedConcat u v = displayedConcat v u :=
    ⟨fun he => by simpa [binaryWordCode_append, binaryWordCode_moleculeWord, moleculeWord_length, displayedConcat] using congrArg binaryWordCode he,
     fun hc => binaryWordCode_injective_length (by simp [Nat.add_comm])
       (by simpa [binaryWordCode_append, binaryWordCode_moleculeWord, moleculeWord_length, displayedConcat] using hc)⟩
  have ht : (moleculeWord q.1.1 ++ moleculeWord q.1.2).take (molLength q.1.1) = moleculeWord q.1.1 := by
    rw [← moleculeWord_length q.1.1]; simp
  have hd : (moleculeWord q.1.1 ++ moleculeWord q.1.2).drop (molLength q.1.1) = moleculeWord q.1.2 := by
    rw [← moleculeWord_length q.1.1]; simp
  unfold canonical
  split
  · rename_i h
    simp only [canonicalIndex, orderedCoordinate, ht, hd, List.length_append, moleculeWord_length, Nat.add_sub_cancel_left]
    rw [ite_eq_right fun ⟨_, _, hl, hc⟩ => h.elim (fun h1 => h1 (hcomm.mp hc)) (fun h2 => by unfold moleculePrecedes at h2; omega)]; rfl
  · rename_i h
    have hl := noncanonical_strict_lengths q h
    have hw := hcomm.mpr (Classical.byContradiction fun hn => h (.inl hn))
    have hpos : 0 < molLength q.1.2 := Nat.succ_pos _
    simp only [canonicalIndex, orderedCoordinate, ht, hd, List.length_append, moleculeWord_length, Nat.add_sub_cancel_left]
    rw [ite_eq_left ⟨Nat.succ_pos _, by omega, hl, hw⟩]
    exact Prod.ext hw rfl

theorem quotientCoordinate_injective (n : ℕ) : Function.Injective (@quotientCoordinate n) := fun j k he => by
  obtain ⟨r, hr⟩ := splitToOrdered_surjective n ⟨j.1, j.2.1⟩
  obtain ⟨s, hs⟩ := splitToOrdered_surjective n ⟨k.1, k.2.1⟩
  have hosp (t : Reaction n) : orderedCoordinate (splitToOrdered t) = literalSplitCoordinate t :=
    Prod.ext (reaction_words_append t) (molLength_reactionLeft t)
  have hls : literalSplitCoordinate r = literalSplitCoordinate s := by
    simpa [quotientCoordinate, ← hr, ← hs, hosp] using he
  exact Subtype.ext (congrArg (fun q : OrderedChannel n => q.1)
    (hr ▸ hs ▸ congrArg splitToOrdered (literalSplitCoordinate_injective n hls)))

theorem quotientClosure_pullback {n L : ℕ} (q : RepositoryChannel n → Prop) :
    quotientClosure n L (quotientOpen q) =
      temporaryReactionClosure L (staticOpenReactions fun r => q (splitToQuotient r)) := by
  rw [← quotientClosure_OR, show fieldOR splitToQuotient (fun r => q (splitToQuotient r)) = q from
    funext fun j => propext (quotient_mark_pullback_OR q j)]

theorem quotientClosure_restriction (n L : ℕ) (ω : SplitField) :
    quotientClosure n L (quotientOpen fun j => ω (quotientCoordinate j)) =
      temporaryReactionClosure L (restrictedSplitReactions n (quotientField ω)) := by
  rw [quotientClosure_pullback]; congr 1; ext r
  simp only [staticOpenReactions, restrictedSplitReactions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.of_eq (congrArg ω (canonicalIndex_split r).symm)

def quotientEscapeEvent (L K : ℕ) : Set (RepositoryChannel (2 * (K + L)) → Prop) :=
  {q | ∃ x ∈ quotientClosure (2 * (K + L)) L (quotientOpen q), K + L < (moleculeWord x).length}

theorem quotient_escape_measure_eq (L K : ℕ) (a : I) :
    quotientStaticMeasure (2 * (K + L)) a (quotientEscapeEvent L K) =
      infiniteSplitPi a {ω | quotientField ω ∈ reversibleEscapeEvent L K} :=
  proj_escape_measure quotientCoordinate (quotientCoordinate_injective _) _ quotientField
    (quotientClosure_restriction _ L) a

theorem quotient_capped_escape_le (N K : ℕ) (a : I) :
    quotientStaticMeasure N a {q | ∃ x ∈ quotientClosure N 2 (quotientOpen q), K + 2 < molLength x} ≤
      infiniteSplitPi a {ω | quotientField ω ∈ reversibleEscapeEvent 2 K} :=
  proj_capped_escape_le quotientCoordinate (quotientCoordinate_injective _) _ quotientField
    (quotientClosure_restriction N 2) a

theorem quotientSurvival_le_finite_escape (a : I) (K : ℕ) :
    quotientSurvival a ≤ quotientStaticMeasure (2 * (K + 2)) a (quotientEscapeEvent 2 K) := by
  rw [quotient_escape_measure_eq]
  exact measure_mono fun _ h => (reversibleEscapeEvent_iff 2 K _).mpr (h (K + 2))

def quotientRAFEvent (n : ℕ) : Set (RepositoryChannel n → Molecule n → Prop) :=
  {ω | ∃ S, IsRevRAF (repositoryCRS n 2) (fun x j => ω j x) S}

noncomputable def quotientRAFProbability (n : ℕ) (p : I) : ENNReal :=
  quotientCatalyticLaw n p (quotientRAFEvent n)

theorem quotient_near_full_lower (n m : ℕ) (p q : I) (hm : 0 < m)
    (hk : 6 < nearFullPoolSize n m)
    (hq : q ≤ fixedPoolParameter p (nearFullPoolSize n m)) :
    quotientStaticMeasure n q {ω | (m - 1) * Fintype.card (Molecule n) ≤
      m * (quotientClosure n 2 (quotientOpen ω)).card} ≤ quotientRAFProbability n p :=
  crs_near_full_lower (repositoryCRS n 2) rfl p q hm hk hq

theorem quotient_raf_upper (n K : ℕ) (p : I) :
    quotientRAFProbability n p ≤
      quotientStaticMeasure (2 * (K + 2)) (fixedPoolParameter p (Fintype.card (Molecule n)))
        (quotientEscapeEvent 2 K) + (Fintype.card (Molecule (K + 2)) : ENNReal) * 34 * (toNNReal p : ENNReal) := by
  refine (crs_raf_upper (K := K) (repositoryCRS n 2) (repositorySeedChannels_card_le_34 n) p).trans
    (add_le_add_left ?_ _)
  rw [quotient_escape_measure_eq]
  exact quotient_capped_escape_le n K _

end RAFReactionQuotient
