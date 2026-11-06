import Mathlib.Tactic

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



variable {G : Type*} [Group G]

/-- A requirement is *finitely determined* when its truth value at a subgroup depends only
on the membership of the elements of some fixed finite set. -/
def FinitelyDetermined {ι : Type*} (Sat : Subgroup G → ι → Prop)  :=
  ∀ v : ι, ∃ F : Finset G, ∀ N N' : Subgroup G,
    (∀ g ∈ F, (g ∈ N ↔ g ∈ N')) → (Sat N v ↔ Sat N' v)

section

/-- The indicator functions of normal subgroups, inside the compact space `G → Bool`. -/
def NSSet (G : Type*) [Group G] : Set (G → Bool) :=
  {f | f 1 = true ∧ (∀ a b, f a = true → f b = true → f (a * b) = true) ∧
    (∀ a, f a = true → f a⁻¹ = true) ∧ (∀ g a, f a = true → f (g * a * g⁻¹) = true)}

/-- The normal subgroup with a given indicator function. -/
def toSubgroup (f : G → Bool) (hf : f ∈ NSSet G) : Subgroup G where
  carrier := {g | f g = true}
  one_mem' := hf.1
  mul_mem' ha hb := hf.2.1 _ _ ha hb
  inv_mem' ha := hf.2.2.1 _ ha

theorem mem_toSubgroup {f : G → Bool} (hf : f ∈ NSSet G) (g : G) :
    g ∈ toSubgroup f hf ↔ f g = true := Iff.rfl

theorem toSubgroup_normal {f : G → Bool} (hf : f ∈ NSSet G) :
    (toSubgroup f hf).Normal :=
  ⟨fun n hn g => hf.2.2.2 g n hn⟩

omit [Group G] in
/-- Finite-coordinate predicates are closed on any continuously parametrized family. -/
theorem isClosed_finitely_determined {X : Type*} [TopologicalSpace X]
    (r : X → G → Bool) (hr : Continuous r) (P : X → Prop) (F : Finset G)
    (hF : ∀ x x', (∀ g ∈ F, r x g = r x' g) → P x → P x') :
    IsClosed {x | P x} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨{x' | ∀ g ∈ F, r x' g = r x g}, ?_, ?_, fun g _ => rfl⟩
  · exact fun x' hx' hp => hx (hF x' x hx' hp)
  · have he : {x' | ∀ g ∈ F, r x' g = r x g} =
        ⋂ g ∈ F, (fun x' => r x' g) ⁻¹' {r x g} := by ext; simp
    rw [he]
    exact isOpen_biInter_finset fun g _ =>
      (isOpen_discrete _).preimage ((continuous_apply g).comp hr)

theorem isClosed_NSSet : IsClosed (NSSet G) := by
  have h (g : G) : IsClopen {f : G → Bool | f g = true} :=
    (isClopen_discrete {true}).preimage (continuous_apply g)
  simp only [NSSet, Set.setOf_and, Set.setOf_forall]
  exact (h 1).isClosed.inter ((isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_imp (h a).isOpen (isClosed_imp (h b).isOpen (h (a * b)).isClosed)).inter
    ((isClosed_iInter fun a => isClosed_imp (h a).isOpen (h a⁻¹).isClosed).inter
    (isClosed_iInter fun g => isClosed_iInter fun a => isClosed_imp (h a).isOpen (h (g * a * g⁻¹)).isClosed)))

/-- **The compactness step of Section 2.**  If every finite family of finitely determined
requirements is satisfied by some normal subgroup, then all requirements are satisfied
simultaneously by a single normal subgroup. -/
theorem exists_normal_subgroup_forall {ι : Type*} (Sat : Subgroup G → ι → Prop)
    (hdet : FinitelyDetermined Sat)
    (hfin : ∀ S : Finset ι, ∃ N : Subgroup G, N.Normal ∧ ∀ v ∈ S, Sat N v) :
    ∃ N : Subgroup G, N.Normal ∧ ∀ v, Sat N v := by
  classical
  choose F hF using hdet
  -- the closed set of indicator functions satisfying the requirement `v`
  set B : ι → Set (G → Bool) := fun v =>
    NSSet G ∩ {f | ∀ N : Subgroup G, (∀ g, g ∈ N ↔ f g = true) → Sat N v} with hB
  have hBclosed (v : ι) : IsClosed (B v) := by
    refine (isClosed_NSSet.isClosedEmbedding_subtypeVal.isClosed_iff_preimage_isClosed
      (fun f hf => ⟨⟨f, hf.1⟩, rfl⟩)).mpr ?_
    refine isClosed_finitely_determined (fun f : NSSet G => f.val) continuous_subtype_val
      (fun f => f.val ∈ B v) (F v) ?_
    intro f f' hff hf
    refine ⟨f'.property, ?_⟩
    intro N hN
    apply (hF v (toSubgroup f.val f.property) N ?_).mp
      (hf.2 _ (mem_toSubgroup f.property))
    intro g hg
    change f.val g = true ↔ g ∈ N
    rw [hff g hg, hN g]
  -- the indicator function of a normal subgroup lies in the corresponding closed sets
  have hmemZ : ∀ N : Subgroup G, N.Normal → (fun g => decide (g ∈ N)) ∈ NSSet G := by
    intro N hN
    refine ⟨by simp, ?_, ?_, ?_⟩
    · aesop
    · simp_all
    · intro g a ha
      simp only [decide_eq_true_eq] at ha ⊢
      exact hN.conj_mem a ha g
  have hmemB : ∀ (N : Subgroup G), N.Normal → ∀ v, Sat N v →
      (fun g => decide (g ∈ N)) ∈ B v := by
    grind
  -- compactness
  have hne : (NSSet G ∩ ⋂ v, B v).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty] at hempty
    obtain ⟨u, hu⟩ := isClosed_NSSet.isCompact.elim_finite_subfamily_closed B hBclosed hempty
    obtain ⟨N, hN, hNu⟩ := hfin u
    have hmem : (fun g => decide (g ∈ N)) ∈ NSSet G ∩ ⋂ v ∈ u, B v :=
      ⟨hmemZ N hN, Set.mem_iInter₂.mpr fun v hv => hmemB N hN v (hNu v hv)⟩
    exact absurd hmem.2 (Set.disjoint_left.mp hu hmem.1)
  obtain ⟨f, hfZ, hfB⟩ := hne
  refine ⟨toSubgroup f hfZ, toSubgroup_normal hfZ, fun v => ?_⟩
  exact (Set.mem_iInter.mp hfB v).2 _ (mem_toSubgroup hfZ)

end

/-- **The minimality step of Section 2.**  If the requirements pass to intersections of
decreasing chains, then a normal subgroup satisfying them all contains a minimal such
normal subgroup. -/
theorem exists_minimal_normal_sat (Sat : Subgroup G → Prop)
    (hchain : ∀ C : Set (Subgroup G), IsChain (· ≤ ·) C → C.Nonempty →
      (∀ N ∈ C, N.Normal ∧ Sat N) → Sat (sInf C))
    (M : Subgroup G) (hM : M.Normal) (hMs : Sat M) :
    ∃ N : Subgroup G, N ≤ M ∧ N.Normal ∧ Sat N ∧
      ∀ N' : Subgroup G, N' ≤ N → N'.Normal → Sat N' → N' = N := by
  classical
  set s : Set (Subgroup G) := {N | N ≤ M ∧ N.Normal ∧ Sat N} with hs
  have hMem : M ∈ s := ⟨le_rfl, hM, hMs⟩
  have hub : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, ub ≤ z := by
    intro c hcs hchain' y hy
    have hne : c.Nonempty := ⟨y, hy⟩
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
    (fun c hcs hc y hy => hub c hcs hc.symm y hy) M hMem
  obtain ⟨hmM, hmN, hmS⟩ := hmax.1
  refine ⟨m, hmM, hmN, hmS, ?_⟩
  intro N' hN' hN'norm hN'sat
  have hN's : N' ∈ s := ⟨hN'.trans hmM, hN'norm, hN'sat⟩
  exact le_antisymm hN' (hmax.2 hN's hN')

end FiniteChains
