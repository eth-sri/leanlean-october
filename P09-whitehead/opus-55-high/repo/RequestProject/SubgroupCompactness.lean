import Mathlib


/-!
# The two Zorn-type steps of Section 2

Section 2 of the paper uses two set-theoretic arguments about normal subgroups
of `G = π₁(K)`.

1. *Compactness.*  Each requirement (2.2) "depends on finitely many decisions
   `g ∈ M`".  If every finite list of requirements is met by some normal
   subgroup, then a single normal subgroup meets all of them.  The paper phrases
   this through Zorn's lemma applied to collections of membership decisions; the
   formalization below is the equivalent compactness statement for the product
   topology on `G → Bool`.

2. *Minimality.*  Among the normal subgroups satisfying all requirements there
   is a minimal one, because the intersection of a decreasing chain again
   satisfies every requirement.
-/

namespace FiniteChains

open Set

variable {G : Type*} [Group G]

/-- A requirement is *finitely determined* when its truth value at a subgroup depends only
on the membership of the elements of some fixed finite set. -/
def FinitelyDetermined {ι : Type*} (Sat : Subgroup G → ι → Prop) :=
  ∀ v, ∃ F : Finset G, ∀ N N',
    (∀ g ∈ F, (g ∈ N ↔ g ∈ N')) → (Sat N v ↔ Sat N' v)

section Compactness

/-- The indicator functions of normal subgroups, inside the compact space `G → Bool`. -/
def NSSet G [Group G] : Set (G → Bool) :=
  {f | f 1 = true ∧ (∀ a b, f a = true → f b = true → f (a * b) = true) ∧
    (∀ a, f a = true → f a⁻¹ = true) ∧ (∀ g a, f a = true → f (g * a * g⁻¹) = true)}

/-- The normal subgroup with a given indicator function. -/
def toSubgroup f (hf : f ∈ NSSet G) : Subgroup G where
  carrier := {g | f g = true}
  one_mem' := hf.1
  mul_mem' ha hb := hf.2.1 _ _ ha hb
  inv_mem' ha := hf.2.2.1 _ ha

theorem mem_toSubgroup hf (g : G) :
    g ∈ toSubgroup f hf ↔ f g = true := Iff.rfl

theorem toSubgroup_normal (hf : f ∈ NSSet G) :
    (toSubgroup f hf).Normal :=
  ⟨fun n hn g => hf.2.2.2 g n hn⟩

omit [Group G] in
/-- A condition on `G → Bool` that only depends on finitely many coordinates is closed. -/
theorem isClosed_of_finite_determination (P : (G → Bool) → Prop) (F : Finset G)
    (hF : ∀ f f' : G → Bool, (∀ g ∈ F, f g = f' g) → P f → P f') :
    IsClosed {f | P f} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro f hf
  refine ⟨{f' | ∀ g ∈ F, f' g = f g}, ?_, ?_, fun g _ => rfl⟩
  · tauto
  · have hset : {f' : G → Bool | ∀ g ∈ F, f' g = f g}
        = ⋂ g ∈ F, (· g) ⁻¹' {f g} := by
      aesop
    rw [hset]
    exact isOpen_biInter_finset fun g _ => (isOpen_discrete _).preimage (continuous_apply g)

theorem isClosed_NSSet : IsClosed (NSSet G) := by
  classical
  have h1 : IsClosed {f : G → Bool | f 1 = true} :=
    isClosed_of_finite_determination _ {1} (by
      simp_all)
  have h2 : ∀ a b, IsClosed {f : G → Bool | f a = true → f b = true → f (a * b) = true} := by
    intro a b
    refine isClosed_of_finite_determination _ {a, b, a * b} ?_
    simp_all
  have h3 : ∀ a, IsClosed {f : G → Bool | f a = true → f a⁻¹ = true} := by
    intro a
    refine isClosed_of_finite_determination _ {a, a⁻¹} ?_
    simp_all
  have h4 : ∀ g a, IsClosed {f : G → Bool | f a = true → f (g * a * g⁻¹) = true} := by
    intro g a
    refine isClosed_of_finite_determination _ {a, g * a * g⁻¹} ?_
    simp_all
  have hset : NSSet G = {f : G → Bool | f 1 = true}
      ∩ ((⋂ p : G × G, {f : G → Bool | f p.1 = true → f p.2 = true → f (p.1 * p.2) = true})
      ∩ ((⋂ a : G, {f : G → Bool | f a = true → f a⁻¹ = true})
      ∩ (⋂ p : G × G, {f : G → Bool | f p.2 = true → f (p.1 * p.2 * p.1⁻¹) = true}))) := by
    aesop
  rw [hset]
  exact h1.inter ((isClosed_iInter (by simp_all)).inter
    ((isClosed_iInter h3).inter (isClosed_iInter (by simp_all))))

/-- **The compactness step of Section 2.**  If every finite family of finitely determined
requirements is satisfied by some normal subgroup, then all requirements are satisfied
simultaneously by a single normal subgroup. -/
theorem exists_normal_subgroup_forall Sat
    (hdet : FinitelyDetermined Sat)
    (hfin : ∀ S : Finset ι, ∃ N, N.Normal ∧ ∀ v ∈ S, Sat N v) :
    ∃ N : Subgroup G, N.Normal ∧ ∀ v, Sat N v := by
  classical
  choose F hF using hdet
  -- the closed set of indicator functions satisfying the requirement `v`
  set B : ι → Set (G → Bool) := fun v =>
    NSSet G ∩ {f | ∀ N, (∀ g, g ∈ N ↔ f g = true) → Sat N v} with hB
  have hBclosed : ∀ v, IsClosed (B v) := by
    intro v
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro f hf
    by_cases hfZ : f ∈ NSSet G
    · have hnot : ¬ ∀ N, (∀ g, g ∈ N ↔ f g = true) → Sat N v := by simp_all
      push Not at hnot
      obtain ⟨N, hNmem, hNsat⟩ := hnot
      refine ⟨{f' | ∀ g ∈ F v, f' g = f g}, ?_, ?_, fun g _ => rfl⟩
      · intro f' hf' hf'B
        cases' hf'B with hf'Z hf'sat
        have hNN' : Sat N v ↔ Sat (toSubgroup f' hf'Z) v := by
          refine hF v N (toSubgroup f' hf'Z) ?_
          intro g hg
          rw [hNmem g, mem_toSubgroup hf'Z g, hf' g hg]
        exact hNsat (hNN'.mpr (hf'sat _ (mem_toSubgroup hf'Z)))
      · have hset : {f' : G → Bool | ∀ g ∈ F v, f' g = f g}
            = ⋂ g ∈ F v, (· g) ⁻¹' {f g} := by
          aesop
        rw [hset]
        exact isOpen_biInter_finset fun g _ => (isOpen_discrete _).preimage (continuous_apply g)
    · exact ⟨(NSSet G)ᶜ, fun f' hf' hf'B => hf' hf'B.1, isClosed_NSSet.isOpen_compl, hfZ⟩
  -- the indicator function of a normal subgroup lies in the corresponding closed sets
  have hmemZ : ∀ N : Subgroup G, N.Normal → (fun g => decide (g ∈ N)) ∈ NSSet G := by
    intro N hN
    refine ⟨by simp, ?_, ?_, ?_⟩
    · aesop
    · simp
    · intro g a ha
      simp [decide_eq_true_eq] at ha ⊢
      exact hN.conj_mem a ha g
  have hmemB : ∀ N, N.Normal → ∀ v, Sat N v →
      (fun g => decide (g ∈ N)) ∈ B v := by
    grind
  -- compactness
  have hne : (NSSet G ∩ ⋂ v, B v).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hempty
    cases' isClosed_NSSet.isCompact.elim_finite_subfamily_closed B hBclosed hempty with u hu
    obtain ⟨N, hN, hNu⟩ := hfin u
    have hmem : (fun g => decide (g ∈ N)) ∈ NSSet G ∩ ⋂ v ∈ u, B v :=
      ⟨hmemZ N hN, Set.mem_iInter₂.mpr (by grind)⟩
    grind
  obtain ⟨f, hfZ, hfB⟩ := hne
  refine ⟨toSubgroup f hfZ, toSubgroup_normal hfZ, fun v => ?_⟩
  exact (Set.mem_iInter.mp hfB v).2 _ (mem_toSubgroup hfZ)

end Compactness

/-- **The minimality step of Section 2.**  If the requirements pass to intersections of
decreasing chains, then a normal subgroup satisfying them all contains a minimal such
normal subgroup. -/
theorem exists_minimal_normal_sat (Sat : Subgroup G → Prop)
    (hchain : ∀ C : Set (Subgroup G), IsChain (· ≤ ·) C → C.Nonempty →
      (∀ N ∈ C, N.Normal ∧ Sat N) → Sat (sInf C))
    M (hM : M.Normal) (hMs : Sat M) :
    ∃ N, N ≤ M ∧ N.Normal ∧ Sat N ∧
      ∀ N', N' ≤ N → N'.Normal → Sat N' → N' = N := by
  classical
  set s : Set (Subgroup G) := {N | N ≤ M ∧ N.Normal ∧ Sat N} with hs
  have hMem : M ∈ s := by simp_all
  have hub : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, ub ≤ z := by
    intro c hcs hchain' y hy
    have hne : c.Nonempty := by tauto
    refine ⟨sInf c, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact (sInf_le hy).trans (hcs hy).1
    · constructor
      intro n hn g
      rw [Subgroup.mem_sInf] at hn ⊢
      intro N hN
      exact ((hcs hN).2.1).conj_mem n (hn N hN) g
    · grind
    · intro z hz
      exact sInf_le hz
  obtain ⟨m, -, hmax⟩ := zorn_le_nonempty₀ (α := (Subgroup G)ᵒᵈ) s
    (hub · · ·.symm · ·) M hMem
  obtain ⟨hmM, hmN, hmS⟩ := hmax.1
  refine ⟨m, hmM, hmN, hmS, ?_⟩
  intro N' hN' hN'norm hN'sat
  have hN's : N' ∈ s := by grind
  exact le_antisymm hN' (hmax.2 hN's hN')
