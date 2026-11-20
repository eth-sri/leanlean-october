module
public import proofs.RAF.Concrete.Closure
public import proofs.HordijkSteelThreshold.AmbientIndependence
public import proofs.RAFCriticalWindowQuantitative.ApproximationParameters

/-! Catalytic peeling: straighten the nested pools and compare with a fixed-size pool. -/

@[expose] public section

namespace RAFEmergenceApprox.Generic
open Classical HordijkSteelThreshold MeasureTheory ProbabilityTheory unitInterval RAF.Concrete RAFCriticalWindowQuantitative
section
variable (X : Type*) [Fintype X]

/-- Deterministic nested sets realizing every possible finite pool size. -/
noncomputable def finiteInitialSegment (k : ℕ) : Finset X :=
  (Finset.univ.filter (fun i : Fin (Fintype.card X) => i.val < k)).map
    (Fintype.equivFin X).symm.toEmbedding

theorem finiteInitialSegment_mono :
    Monotone (finiteInitialSegment X) := by
  intro a b hab
  apply Finset.map_subset_map.mpr
  gcongr

theorem card_finiteInitialSegment
    (k : ℕ) (hk : k ≤ Fintype.card X) :
    (finiteInitialSegment X k).card = k := by
  rw [finiteInitialSegment, Finset.card_map, Fin.card_filter_val_lt, min_eq_right hk]

open Finset
variable {X}
/-- A single permutation straightens every pool in a decreasing trajectory.
Sort each molecule by the smallest size of a pool containing it. -/
lemma chain_perm {A : ℕ → Finset X} (hA : Antitone A) (h₀ : A 0 = univ) :
    ∃ e : Equiv.Perm X, ∀ t, (A t).map e.toEmbedding = finiteInitialSegment X (A t).card := by
  let rank (x : X) := Nat.find (show ∃ k, ∃ t, x ∈ A t ∧ (A t).card = k from ⟨_,0,by simp [h₀],rfl⟩)
  have sub {s t} (h : (A s).card ≤ (A t).card) : A s ⊆ A t :=
    (le_total t s).elim (fun h => hA h) fun h' => (eq_of_subset_of_card_le (hA h') h).ge
  have mem t x : rank x ≤ (A t).card ↔ x ∈ A t := by
    simp only [rank,Nat.find_le_iff]; grind
  let e := (Fintype.equivFin X).symm
  obtain ⟨g,sorted⟩ := enumerate_by rank
  refine ⟨g.symm.trans e,fun t => ?_⟩
  have eq : univ.filter (fun i => rank (g i) ≤ (A t).card) = (A t).map g.symm.toEmbedding := by
    ext; simp [mem,mem_map_equiv]
  have c := congrArg card eq
  ext x
  have h := Tuple.lt_card_le_iff_apply_le_of_monotone (j := e.symm x) (a := (A t).card) sorted
  dsimp only [Function.comp_apply] at h
  rw [c,mem] at h
  rw [mem_map_equiv,finiteInitialSegment,mem_map_equiv]
  simpa [Equiv.symm_trans_apply,e] using h.symm
end

variable {X R : Type*} [Fintype X] [Fintype R]

variable (ω : R → X → Prop)
noncomputable abbrev catalystActive (C : Finset X) :=
  @Finset.filter _ (fun r => ∃ x ∈ C, ω r x) (fun _ => Classical.propDecidable _) Finset.univ

omit [Fintype X] in
@[simp] theorem mem_catalystActive (C : Finset X) (r : R) :
    r ∈ catalystActive ω C ↔ ∃ x ∈ C, ω r x := by simp [catalystActive]

omit [Fintype X] in
theorem catalystActive_mono : Monotone (catalystActive ω) := by
  intro A B h r; simp; grind

/-- An injective sample-dependent relabeling of molecules preserves the iid law:
each atom retains exactly the same product weight. -/
private lemma shuffle_law (p : R → I) (e : (R → X → Prop) → Equiv.Perm X)
    (hinj : Function.Injective (fun (ω : R → X → Prop) r x => ω r (e ω x))) :
    MeasurePreserving (fun (ω : R → X → Prop) r x => ω r (e ω x)) (law p) (law p) := by
  refine ⟨measurable_of_finite _,?_⟩
  let f := fun (ω : R → X → Prop) r x => ω r (e ω x)
  apply Measure.ext_of_singleton; intro v
  obtain ⟨w,rfl⟩ := (Finite.injective_iff_surjective.mp hinj) v
  have eq : f ⁻¹' {f w} = {w} := by ext; exact hinj.eq_iff
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton _),eq]
  simp [law,colLaw]
  exact Finset.prod_congr rfl fun r _ => (Equiv.prod_comp (e w) fun x => ambientCoordLaw (p r) {w r x}).symm

/-- Peel by iterating the pool update from the entire universe. -/
abbrev pools (F : Finset X → Finset X) (t : ℕ) := F^[t] Finset.univ
@[simp] lemma pools_succ (F : Finset X → Finset X) (t : ℕ) : pools F (t+1) = F (pools F t) := Function.iterate_succ_apply' ..
lemma pools_anti {F : Finset X → Finset X} (h : Monotone F) : Antitone (pools F) :=
  h.antitone_iterate_of_map_le (Finset.subset_univ _)

noncomputable abbrev segment (A : Finset X) := finiteInitialSegment X A.card
lemma segment_mono : Monotone (segment (X := X)) := (finiteInitialSegment_mono X).comp Finset.card_mono

/-- The failure probability characterizes a Bernoulli bit. -/
lemma bit_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → Prop) (hg : Measurable g) (p : I) (hf : μ {ω | ¬g ω} = toNNReal (σ p)) :
    MeasurePreserving g μ (ambientCoordLaw p) := by
  refine ⟨hg,?_⟩
  have h : μ.map g {False} = ambientCoordLaw p {False} := by
    simpa [Measure.map_apply hg,Set.preimage] using hf
  apply Measure.ext_of_singleton; intro P
  rcases Classical.propComplete P with rfl | rfl
  · rw [show ({True} : Set Prop) = {False}ᶜ by simp]; simp only [measure_compl (MeasurableSet.singleton _) (measure_ne_top _ _),measure_univ,h]
  · assumption

/-- Couple both product laws using the same independent uniform thresholds. -/
theorem product_increasing_mono {J : Type*} [Fintype J] {a c : I} (hac : a ≤ c)
    (E : (J → Prop) → Prop) (hE : Monotone E) :
    colLaw J a {ω | E ω} ≤ colLaw J c {ω | E ω} := by
  have law (p : I) : MeasurePreserving (fun x : I => x ≤ p) volume (ambientCoordLaw p) := by
    apply bit_law _ _ (measurable_mem.mpr measurableSet_Iic)
    change volume {x : I | ¬x ≤ p} = _
    rw [show {x : I | ¬x ≤ p} = Set.Ioi p by ext; simp, volume_Ioi,ENNReal.ofReal]; congr 1; exact NNReal.eq (by simp [sub_nonneg.mpr p.2.2])
  have eq (p : I) := (measurePreserving_pi _ _ (fun _ : J => law p)).finite_event {ω | E ω}
  unfold colLaw; rw [←eq,←eq]; exact measure_mono fun _ h => hE (fun _ hj => hac.trans' hj) h

lemma pool_stat (p : I) (C : Finset X) (P : Finset R → Prop) :
    iid X R p {ω | P (catalystActive ω C)} = colLaw R (fixedPoolParameter p C.card) {ω | P (Finset.univ.filter ω)} := by
  let hit (v : X → Prop) := ∃ x ∈ C, v x
  have h : MeasurePreserving hit (colLaw X p) (ambientCoordLaw (fixedPoolParameter p C.card)) := by
    apply bit_law _ _ (measurable_of_finite _)
    rw [show {v | ¬hit v} = (C : Set X).pi (fun _ => {False}) by ext; simp [hit,Set.mem_pi],colLaw,Measure.pi_pi_finset]
    simp [fixedPoolParameter]; rfl
  exact (measurePreserving_pi _ _ (fun _ : R => h)).finite_event {ω | P (Finset.univ.filter ω)}

lemma coordinate_probability (p : I) (r : R) (x : X) : iid X R p {ω | ω r x} = (toNNReal p : ENNReal) := by
  have hp := (measurePreserving_eval (fun _ : X => ambientCoordLaw p) x).comp
    (measurePreserving_eval (fun _ : R => colLaw X p) r)
  simpa [iid,law,Set.preimage,Function.comp_def,ambientCoordLaw] using hp.finite_event {True}

lemma hit_bound (p : I) (C : Finset X) (A : Finset R) :
    iid X R p {ω | ∃ r ∈ A, ∃ x ∈ C, ω r x} ≤ (C.card : ENNReal)*A.card*(toNNReal p : ENNReal) := by
  refine (finite_cover _ (fun j : C × A => {ω | ω j.2 j.1}) ?_ (fun j => (coordinate_probability p j.2.val j.1.val).le)).trans_eq (by simp)
  rintro ω ⟨r,hr,x,hx,h⟩; exact ⟨(⟨x,hx⟩,⟨r,hr⟩),h⟩

variable [DecidableEq X] (Q : ReversibleCRS X R)
omit [Fintype X] [Fintype R] in
abbrev rafEvent := {ω : R → X → Prop | ∃ S, IsRevRAF Q (fun x r => ω r x) S}

lemma active_iff (ω : R → X → Prop) (S : Finset R) : S ⊆ catalystActive ω (fullClosure Q S) ↔
    RevReflexivelyAutocatalytic Q (fun x r => ω r x) S := by
  simp only [RevReflexivelyAutocatalytic,Finset.subset_iff,mem_catalystActive,full_mem,exists_and_right]

lemma terminal_raf (ω : R → X → Prop) (D : Finset X) (hk : Q.food.card < D.card)
    (hd : D = fullClosure Q (catalystActive ω D)) : ω ∈ rafEvent Q := by
  let A := catalystActive ω D
  let S := A.filter (fun r => Q.lhs r ∪ Q.rhs r ⊆ D)
  have incl : fullClosure Q S ⊆ D := hd ▸ full_mono Q (Finset.filter_subset _ _)
  have he : fullClosure Q S = D := by
    apply Finset.Subset.antisymm incl; rw [hd]; apply full_le Q A (full_food Q S)
    grind [full_closed,Finset.union_subset_iff,Finset.Subset.trans]
  refine ⟨S,?_,?_,?_⟩
  · by_contra! h0
    rw [←he,h0] at hk
    have hc : fullClosure Q ∅ ⊆ Q.food := by grind [full_le]
    exact hk.not_ge (Finset.card_le_card hc)
  · intro r hr
    refine ⟨Fintype.card X,?_⟩
    change _ ⊆ fullClosure Q S; rw [he]; exact (Finset.mem_filter.mp hr).2
  · apply (active_iff Q ω S).mp; rw [he]; exact Finset.filter_subset ..

lemma pool_barrier {p q : I} (k : ℕ) (hk : Q.food.card < k) (hpool : q ≤ fixedPoolParameter p k) :
    colLaw R q {ω | k ≤ (fullClosure Q (Finset.univ.filter ω)).card} ≤ iid X R p (rafEvent Q) := by
  by_cases hk' : k ≤ Fintype.card X
  swap
  · simp [show ∀ S, ¬ k ≤ (fullClosure Q S).card from fun S h => hk' (h.trans (Finset.card_le_univ _))]
  refine (product_increasing_mono hpool _ ?_).trans ?_
  · intro u v h hu; exact hu.trans (Finset.card_le_card (full_mono Q (Finset.monotone_filter_right _ (fun j _ => h j))))
  let C := fullClosure Q
  let Iₖ := finiteInitialSegment X k
  rw [show fixedPoolParameter p k = fixedPoolParameter p Iₖ.card by rw [card_finiteInitialSegment X k hk'],
    ←pool_stat p Iₖ (fun S => k ≤ (C S).card)]
  -- Sort the canonical pools in this sample. Ordinary peeling in the
  -- relabeled field recovers these pools, and hence the relabeling itself.
  let H (ω : R → X → Prop) := pools (C ∘ catalystActive ω ∘ segment)
  have mc (ω : R → X → Prop) := (full_mono Q).comp (catalystActive_mono ω)
  have hb ω : Antitone (H ω) := pools_anti ((mc ω).comp segment_mono)
  let e ω := (chain_perm (hb ω) rfl).choose
  let f (ω : R → X → Prop) r x := ω r (e ω x)
  have traj ω : pools (C ∘ catalystActive (f ω)) = H ω := by
    funext t; induction t with
    | zero => rfl
    | succ t ih =>
      simp only [H,pools_succ,Function.comp_apply,ih]
      rw [show segment (H ω t) = _ from ((chain_perm (hb ω) rfl).choose_spec t).symm]
      congr 1; ext; simp; dsimp only [f,e]; grind
  have inj : Function.Injective f := by
    intro u v eq
    have he := (traj u).symm.trans (eq ▸ traj v)
    have he' : e u = e v := by unfold e; congr 2; rw [he]
    funext r y; obtain ⟨x,rfl⟩ := (e u).surjective y
    simpa only [f,he'] using congrFun (congrFun eq r) x
  rw [←(shuffle_law (fun _ => p) e inj).finite_event (rafEvent Q)]
  apply measure_mono; intro ω h
  obtain ⟨t,ht⟩ := WellFoundedLT.antitone_chain_condition (hb ω)
  apply terminal_raf Q (f ω) (H ω t)
  · apply hk.trans_le; clear ht; induction t with
    | zero => assumption
    | succ t ih => rw [show H ω (t+1) = _ from pools_succ _ t]; exact h.trans (Finset.card_mono (mc ω (finiteInitialSegment_mono X ih)))
  · calc
      _ = H ω (t+1) := ht _ (Nat.le_succ t)
      _ = _ := by rw [←traj,pools_succ]; rfl

end RAFEmergenceApprox.Generic
