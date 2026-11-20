module

public import ADR11.Coalescent.Evolution
public import ADR11.Trees.Hierarchy
public import ADR11.MSC.Law

/-! A clade's law is a probability distribution supported on forests of
its sampled lineages. Independent assembly and then a population step
preserve this invariant, so one induction suffices. -/
@[expose] public section

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {L : Type*} [Fintype L] [DecidableEq L]

namespace Law
variable {α β ι : Type*} [Fintype α] [Fintype β]

structure Valid (p : Law α) (P : α → Prop) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  mass : dotProduct p 1 = 1
  support : ∀ {a}, p a ≠ 0 → P a

theorem Valid.bind {p : Law α} {q : α → Law β} {P Q} (hp : Valid p P) (hq : ∀ a, P a → Valid (q a) Q) : Valid (Law.bind p q) Q where
  nonneg b := sum_nonneg fun a _ => by
    by_cases hz : p a = 0; · simp [hz]
    exact mul_nonneg (hp.nonneg a) ((hq a (hp.support hz)).nonneg b)
  mass := by classical rw [expect_bind]; exact (expect_congr fun a hz => (hq a (hp.support hz)).mass).trans hp.mass
  support hb := by
    obtain ⟨a,_,h⟩ := exists_ne_zero_of_sum_ne_zero hb
    exact (hq a (hp.support (left_ne_zero_of_mul h))).support (right_ne_zero_of_mul h)

end Law

namespace SpeciesTree
variable (σ : SpeciesTree X) (s : L → X)
noncomputable abbrev leave := forestDist σ.clusters σ.length s
noncomputable def enter (A : Finset X) := Law.combine (σ.kids A) (σ.leave s) (sampledForest s A)

theorem leave_eq (A : Finset X) : σ.leave s A = Law.bind (σ.enter s A) (populationKernel σ.length A) := by
  funext G; rw [leave,forestDist]; unfold enter Law.combine Law.bind; rw [Law.expect_push]; rfl
end SpeciesTree

omit [Fintype X] in
theorem mem_sampledForest {s : L → X} {A : Finset X} {C : Finset L} :
    C ∈ sampledForest s A ↔ ∃ l, s l ∈ A ∧ {l} = C := by
  simp [sampledForest]

omit [Fintype X] in
theorem singleton_mem_sampledForest {s : L → X} {A : Finset X} {l : L} :
    {l} ∈ sampledForest s A ↔ s l ∈ A := by
  simp [sampledForest]

abbrev Supported (s : L → X) (A : Finset X) (F : Clusters L) :=
  IsForest F ∧ sampledForest s A ⊆ F ∧ lineages F ⊆ pre s A

private theorem enter_supported (σ : SpeciesTree X) {s : L → X} {A : Finset X}
    (f : σ.kids A → Clusters L) (hf : ∀ B : σ.kids A, Supported s B (f B)) : Supported s A (univ.sup f ∪ sampledForest s A) := by
  have sub (B : σ.kids A) {C} (hc : C ∈ f B) : C ⊆ pre s B := (subset_lineages hc).trans (hf B).2.2
  have dis (b d : σ.kids A) (ne : b ≠ d) : Disjoint (pre s b) (pre s d) :=
    pre_disjoint s (σ.siblings b.prop d.prop (fun h => ne (Subtype.ext h)))
  have good : IsForest (univ.sup f) := by
    simp only [IsForest,Laminar,mem_sup,mem_univ,true_and]
    constructor
    · rintro C ⟨b,hb⟩; exact (hf b).1.1 C hb
    · rintro C ⟨b,hb⟩ D ⟨d,hd⟩
      by_cases h : b=d; · subst d; exact (hf b).1.2 C hb D hd
      exact .inr (.inr ((dis b d h).mono (sub b hb) (sub d hd)))
  refine ⟨good.with_atoms _,subset_union_right,?_⟩
  apply Finset.sup_le
  simp only [id_eq,mem_union,mem_sup,mem_univ,true_and,mem_sampledForest]
  rintro C (⟨b,hb⟩|⟨l,hl,rfl⟩); exacts [(sub b hb).trans (pre_mono s (child_lt b.prop).subset),by simpa using hl]

namespace SpeciesTree
variable (σ : SpeciesTree X) (s : L → X) {A : Finset X}

private theorem assemble (ih : ∀ B ∈ σ.kids A, Law.Valid (σ.leave s B) (Supported s B)) : Law.Valid (σ.enter s A) (Supported s A) where
  nonneg F := by
    apply sum_nonneg; intro f _; split; · exact prod_nonneg fun B _ => (ih B B.prop).nonneg _
    rfl
  mass := by
    rw [← Law.cdf_univ,enter,Law.cdf_combine]; simp [prod_eq_one fun B hb => (ih B hb).mass]
  support hz := by
    obtain ⟨f,_,hf⟩ := exists_ne_zero_of_sum_ne_zero hz
    split_ifs at hf with e; · exact e ▸ enter_supported σ f fun B => (ih B B.prop).support (prod_ne_zero_iff.mp hf B (mem_univ _))
    contradiction

theorem valid_leave (ha : A ∈ σ.clusters) : Law.Valid (σ.leave s A) (Supported s A) := by
  induction A using σ.cladeInduction with | step A ih =>
  rw [leave_eq]; apply (assemble σ s fun B hb => ih B hb (child_mem hb)).bind
  intro F hF
  refine ⟨populationKernel_nonneg (fun hu => (σ.length_pos _ ha hu).le) hF.1,by simpa [dotProduct] using populationKernel_sum σ.length A hF.1,fun hz => ?_⟩
  obtain ⟨hg,sub,lin⟩ := populationKernel_support hF.1 hz
  exact ⟨hg,hF.2.1.trans sub,lin ▸ hF.2.2⟩

theorem valid_enter (A : Finset X) : Law.Valid (σ.enter s A) (Supported s A) := assemble σ s fun _ hb => σ.valid_leave s (child_mem hb)
end SpeciesTree

theorem Challenge.unrootedDist_nonneg (σ : SpeciesTree X) (s : L → X) (T : Finset (Finset L)) : 0 ≤ σ.unrootedDist s T := by
  apply sum_nonneg; intro G _; split_ifs; · exact (σ.valid_leave s σ.univ_mem).nonneg G
  rfl

theorem Challenge.unrootedDist_sum (σ : SpeciesTree X) (s : L → X) : ∑ T, σ.unrootedDist s T = 1 := by
  unfold SpeciesTree.unrootedDist; rw [sum_comm]; simpa [SpeciesTree.rootedDist,SpeciesTree.leave,sum_ite_eq,dotProduct] using (σ.valid_leave s σ.univ_mem).mass

end ADR11
