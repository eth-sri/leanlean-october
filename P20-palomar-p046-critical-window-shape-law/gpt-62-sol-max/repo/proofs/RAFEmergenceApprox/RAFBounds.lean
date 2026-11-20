module

public import proofs.HordijkSteelThreshold.AmbientIndependence
public import Mathlib.Probability.ProductMeasure
public import proofs.HordijkSteelThreshold.BinaryReactionSplit
public import proofs.HordijkSteelThreshold.ReversibleClosure

@[expose] public section

namespace RAFEmergenceApprox.Generic
open MeasureTheory unitInterval HordijkSteelThreshold MeasureTheory.Measure
open RAF.Concrete RAF.Polymer RAFCriticalWindowQuantitative

/-- Deterministic nested sets realizing every possible finite pool size. -/
noncomputable def finiteInitialSegment (X : Type*) [Fintype X] (k : ℕ) : Finset X :=
  (Finset.univ.filter (fun i : Fin (Fintype.card X) => i.val < k)).map
    (Fintype.equivFin X).symm.toEmbedding

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

noncomputable abbrev catalystActive (ω : R → X → Prop) (C : Finset X) : Finset R :=
  openChannels (fun r => ∃ x ∈ C, ω r x)

noncomputable abbrev iidCatalysis (p : I) : Measure (R → X → Prop) :=
  law (fun _ => p)

omit [Fintype X] in
theorem catalystActive_mono (ω : R → X → Prop) : Monotone (catalystActive ω) := by
  intro C D h r hr
  aesop

theorem pool_statistic (p : I) (C : Finset X) (stat : Finset R → Prop) :
    iidCatalysis p {ω | stat (catalystActive ω C)} =
      finiteFieldLaw (fixedPoolParameter p C.card) {q | stat (openChannels q)} := by
  have h : (colLaw X p).map (fun v => ∃ x ∈ C, v x) = ambientCoordLaw (fixedPoolParameter p C.card) := by
    apply probability_prop_eq_of_false
    rw [Measure.map_apply .of_discrete .of_discrete]
    rw [ambientCoordLaw_false, fixedPoolParameter, symm_symm]
    change _ = (↑(toNNReal (σ p)^C.card) : ENNReal)
    simpa [colLaw, ← infinitePi_eq_pi, not_exists, ← ENNReal.coe_pow, blockEvent, Set.pi] using (iid_block p C False).2
  simp_rw [finiteFieldLaw, ← h]
  rw [← pi_map_pi (fun _ => Measurable.of_discrete.aemeasurable), Measure.map_apply .of_discrete .of_discrete]
  rfl

variable [DecidableEq X]

/-- Probability of a RAF in the independent catalyst-mark model. -/
noncomputable abbrev rafProbability (Q : ReversibleCRS X R) (p : I) : ENNReal :=
  iidCatalysis p {ω | ∃ S, IsRevRAF Q (fun x r => ω r x) S}

private theorem isRAF_iff (Q : ReversibleCRS X R) (ω : R → X → Prop) (S : Finset R) :
    IsRevRAF Q (fun x r => ω r x) S ↔ S.Nonempty ∧
      (∀ r ∈ S, Q.lhs r ∪ Q.rhs r ⊆ fullClosure Q S) ∧
      S ⊆ catalystActive ω (fullClosure Q S) := by
  unfold IsRevRAF RevFoodGenerated RevReflexivelyAutocatalytic
  simp only [Finset.subset_iff (s₁ := S), mem_openChannels]
  constructor <;> grind [mem_fullClosure, fullClosure]

theorem raf_mass_lower (Q : ReversibleCRS X R) (k : ℕ) (p q : I)
    (hk : Q.food.card < k) (hkU : k ≤ Fintype.card X)
    (hq : q ≤ fixedPoolParameter p k) :
    finiteFieldLaw q {ω | k ≤ (fullClosure Q (openChannels ω)).card} ≤ rafProbability Q p := by
  refine (product_increasing_mono hq ?_).trans ?_
  · intro u v huv hu
    exact hu.trans (Finset.card_mono (fullClosure_mono Q (by simpa [Finset.subset_iff, Pi.le_def] using huv)))
  let C := fullClosure Q
  let P := finiteInitialSegment X
  have hP : Monotone P := fun _ _ h => Finset.map_subset_map.mpr (by grind)
  let step (ω : R → X → Prop) := C ∘ catalystActive ω
  have hstep (ω : R → X → Prop) : Monotone (step ω) :=
    (fullClosure_mono Q).comp (catalystActive_mono ω)
  let scalar (ω : R → X → Prop) : Finset X → Finset X := step ω ∘ P ∘ Finset.card
  have hs (ω) : Monotone (scalar ω) := (hstep ω).comp (hP.comp Finset.card_mono)
  let T := Fintype.card X
  let trace (f : Finset X → Finset X) (hf : Monotone f) : {H : Fin (T+1) → Finset X // Antitone H} :=
    ⟨fun t => f^[t.val] Finset.univ, fun _ _ h => hf.antitone_iterate_of_map_le (Finset.subset_univ _) h⟩
  let A (ω : R → X → Prop) := trace (step ω) (hstep ω)
  let B (ω : R → X → Prop) := trace (scalar ω) (hs ω)
  -- An entire descending pool trace is tested after a single reindexing.
  have htrace : (iidCatalysis p).map A = (iidCatalysis p).map B := by
    apply Measure.ext_of_singleton
    rintro ⟨H,hh⟩
    simp only [Measure.map_apply .of_discrete .of_discrete]
    -- Sort by the time of disappearance so that each pool becomes a prefix.
    let f := Fintype.equivFin X
    let key (x : X) := (Finset.univ.filter fun t => x ∈ H t).card
    let o := Tuple.sort (OrderDual.toDual ∘ key ∘ f.symm)
    let e := (f.trans o).trans f.symm
    have hk (x : X) (t : Fin (T+1)) : t.val < key x ↔ x ∈ H t :=
      Fin.lt_card_filter_univ_iff_apply_of_imp _ (fun _ _ h hx => hh h hx)
    have hsort : Antitone (key ∘ f.symm ∘ o) := Tuple.monotone_sort (OrderDual.toDual ∘ key ∘ f.symm)
    have he t x : e x ∈ H t ↔ x ∈ P (H t).card := by
      have hcard : (Finset.univ.filter (fun i => f.symm (o i) ∈ H t)).card = (H t).card := by
        rw [← Finset.card_map (o.trans f.symm).toEmbedding, Finset.map_filter, Finset.map_univ_equiv]
        simp [Function.comp_def]
      simpa [e, P, finiteInitialSegment, f, hk, hcard, Function.comp_def] using
        (Tuple.lt_card_gt_iff_apply_gt_of_antitone (j := f x) (a := t.val) hsort).symm
    have hm : (iidCatalysis p).map (fun (ω : R → X → Prop) r x => ω r (e x)) = iidCatalysis p := by
      rw [iidCatalysis, law, pi_map_pi (f := fun (_ : R) (v : X → Prop) x => v (e x))
        (fun _ => Measurable.of_discrete.aemeasurable)]
      simp_rw [colLaw, ← infinitePi_eq_pi, map_infinitePi_infinitePi_of_inj e.injective]
    nth_rw 2 [← hm]
    rw [Measure.map_apply .of_discrete .of_discrete]
    congr 1
    ext ω
    have hact (D : Fin (T+1)) : catalystActive ω (H D) =
        catalystActive (fun r x => ω r (e x)) (P (H D).card) := by
      ext r
      simp only [mem_openChannels, ← he]
      exact e.exists_congr_right.symm
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff, A, B, trace, funext_iff]
    constructor <;> intro h t <;> induction t using Fin.induction with
    | zero => exact h 0
    | succ t ih =>
      have h₀ := h t.castSucc
      have h₁ := h t.succ
      simp_all only [Fin.val_castSucc, Fin.val_succ, Function.iterate_succ_apply', step, scalar,
        Function.comp_apply]

  have he := congrArg (· {H | k ≤ (H.val (Fin.last T)).card}) htrace
  simp only [Measure.map_apply .of_discrete .of_discrete, A, B, trace] at he
  have hpool := pool_statistic p (P k) (fun A => k ≤ (C A).card)
  rw [show (P k).card = k by simp [P, finiteInitialSegment, Fin.card_filter_val_lt, hkU]] at hpool
  rw [← hpool]
  refine (measure_mono ?_).trans (he.symm.le.trans (measure_mono ?_))
  · intro ω hω
    exact hω.trans <| Finset.card_mono <|
      ((hs ω).monotone_iterate_of_le_map (hstep ω (hP hω)) (Nat.zero_le T)).trans
        ((hs ω).iterate T (Finset.subset_univ _))
  · intro ω hw
    let D := (step ω)^[T] Finset.univ
    let S := catalystActive ω D
    let U := S.filter (fun r => Q.lhs r ∪ Q.rhs r ⊆ D)
    have hfix : C S = D := stationary_of_rank
      (fun t => (step ω)^[t] Finset.univ) _ (Function.iterate_succ_apply' _ · _) (fun D => Dᶜ.card)
      T (fun _ => Finset.card_le_univ _) (fun t ht => Finset.card_lt_card
        (Finset.compl_ssubset_compl.mpr (((hstep ω).antitone_iterate_of_map_le (Finset.subset_univ _) t.le_succ).lt_of_ne ht)))
    have hsub : C U ⊆ D := hfix ▸ fullClosure_mono Q (Finset.filter_subset ..)
    have he : fullClosure Q U = D := hsub.antisymm (by
      rw [← hfix]
      exact fullClosure_least (fullClosure_food Q U) (by grind [fullClosure_completes]))
    refine ⟨U, (isRAF_iff Q ω U).2 ?_⟩
    rw [he]
    refine ⟨?_, by simp [U], Finset.filter_subset ..⟩
    have := fullClosure_eq_food_of_no_seed Q ∅ (by simp)
    grind [Finset.not_nonempty_iff_eq_empty]

/-- Either the ambient pool reaches outside the cutoff or some seed reaction
has a catalyst in the cutoff; bound the latter by a union over marks. -/
theorem raf_escape_upper {n : ℕ} (Q : ReversibleCRS (Molecule n) R) (p : I) (K c : ℕ)
    (hc : Fintype.card {r // RevSeedReaction Q r} ≤ c) :
    rafProbability Q p ≤
    finiteFieldLaw (fixedPoolParameter p (Fintype.card (Molecule n)))
      {ω | ∃ x ∈ fullClosure Q (openChannels ω), K < molLength x} +
      (Fintype.card (Molecule K) : ENNReal)*(c : ENNReal)*(toNNReal p : ENNReal) := by
  let B := binaryFood n K
  let J := ↥B × {r // RevSeedReaction Q r}
  let E : J → Set (R → Molecule n → Prop) := fun j => {ω | ω j.2.val j.1.val}
  unfold rafProbability
  rw [← Finset.card_univ (α := Molecule n), ← pool_statistic _ Finset.univ
    (fun A => ∃ x ∈ fullClosure Q A, K < molLength x)]
  refine measure_le_add_of_cover (B := ⋃ j, E j) ?_ le_rfl ?_
  · rintro ω ⟨S,hS⟩
    obtain ⟨hne,hends,hcat⟩ := (isRAF_iff Q ω S).mp hS
    obtain ⟨r,hr,hseed⟩ : ∃ r ∈ S, RevSeedReaction Q r := by
      by_contra! hn
      rw [fullClosure_eq_food_of_no_seed Q S hn] at hends
      grind [RevSeedReaction]
    obtain ⟨x,hx,hxcat⟩ := (mem_openChannels _ _).mp (hcat hr)
    by_cases hb : x ∈ B
    · aesop
    · refine Or.inl ⟨x, fullClosure_mono Q (hcat.trans (catalystActive_mono ω (Finset.subset_univ _))) hx, ?_⟩
      simp_all [B,binaryFood]
  · refine (measure_le_card_mul (δ := toNNReal p) Finset.univ E (by simp) ?_).trans ?_
    · intro j _
      simpa [iidCatalysis, law, colLaw, E, Function.comp_def] using
        (((measurePreserving_eval (fun _ : Molecule n => ambientCoordLaw p) j.1.val).comp
          (measurePreserving_eval (fun _ : R => colLaw (Molecule n) p) j.2.val)).measure_preimage
          (MeasurableSet.singleton True).nullMeasurableSet).le
    · simp only [Finset.card_univ, J, Fintype.card_prod, Fintype.card_coe, Nat.cast_mul]
      gcongr
      exact_mod_cast binaryFood_card_le_cutoff n K
end RAFEmergenceApprox.Generic
