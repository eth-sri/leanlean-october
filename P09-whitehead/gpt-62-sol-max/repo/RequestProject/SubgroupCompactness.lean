module

public import Mathlib

@[expose] public section

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
def FinitelyDetermined {ι : Type*} (Sat : Subgroup G → ι → Prop) : Prop :=
  ∀ v : ι, ∃ F : Finset G, ∀ N N' : Subgroup G,
    (∀ g ∈ F, (g ∈ N ↔ g ∈ N')) → (Sat N v ↔ Sat N' v)

section Compactness

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

theorem toSubgroup_normal {f : G → Bool} (hf : f ∈ NSSet G) :
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
        = ⋂ g ∈ F, (fun h  => h g) ⁻¹' {f g} := by
      ext f'; simp
    rw [hset]
    exact isOpen_biInter_finset fun g _ => (isOpen_discrete _).preimage (continuous_apply g)

theorem isClosed_NSSet : IsClosed (NSSet G) := by
  classical
  have hImp (a b : G) : IsClosed {f : G → Bool | f a = true → f b = true} := by
    apply isClosed_of_finite_determination _ {a, b}
    intro f f' he h
    simpa only [he a (by simp), he b (by simp)] using h
  have hMul (a b : G) : IsClosed {f : G → Bool | f a = true → f b = true → f (a * b) = true} := by
    apply isClosed_of_finite_determination _ {a, b, a * b}
    intro f f' he h
    simpa only [he a (by simp), he b (by simp), he (a * b) (by simp)] using h
  simp only [NSSet, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_eq (continuous_apply 1) continuous_const).inter
    ((isClosed_iInter fun a => isClosed_iInter (hMul a)).inter
      ((isClosed_iInter fun a => hImp a a⁻¹).inter
        (isClosed_iInter fun g => isClosed_iInter fun a => hImp a (g * a * g⁻¹))))

/-- **The compactness step of Section 2.**  If every finite family of finitely determined
requirements is satisfied by some normal subgroup, then all requirements are satisfied
simultaneously by a single normal subgroup. -/
theorem exists_normal_subgroup_forall {ι : Type*} (Sat : Subgroup G → ι → Prop)
    (hdet : FinitelyDetermined Sat)
    (hfin : ∀ S : Finset ι, ∃ N : Subgroup G, N.Normal ∧ ∀ v ∈ S, Sat N v) :
    ∃ N : Subgroup G, N.Normal ∧ ∀ v, Sat N v := by
  classical
  choose F hF using hdet
  -- Extend each requirement to all indicator functions by testing only its finite coordinates.
  let B (v : ι) : Set (G → Bool) := {f | ∃ N : Subgroup G,
    (∀ g ∈ F v, g ∈ N ↔ f g = true) ∧ Sat N v}
  have hB (v : ι) : IsClosed (B v) := by
    apply isClosed_of_finite_determination _ (F v)
    rintro f f' he ⟨N, hN, hs⟩
    exact ⟨N, fun g hg => he g hg ▸ hN g hg, hs⟩
  obtain ⟨f, hf, hBf⟩ := isClosed_NSSet.isCompact.inter_iInter_nonempty B hB (fun U => by
    obtain ⟨N, hN, hU⟩ := hfin U
    refine ⟨fun g => decide (g ∈ N), ?_, Set.mem_iInter₂.mpr (fun v hv => ?_)⟩
    · simp only [NSSet, Set.mem_setOf_eq, decide_eq_true_eq]
      exact ⟨N.one_mem, fun _ _ => N.mul_mem, fun _ => N.inv_mem, fun g a ha => hN.conj_mem a ha g⟩
    · exact ⟨N, by simp, hU v hv⟩)
  refine ⟨toSubgroup f hf, toSubgroup_normal hf, fun v => ?_⟩
  obtain ⟨N, hN, hs⟩ := Set.mem_iInter.mp hBf v
  exact (hF v N (toSubgroup f hf) hN).1 hs

end Compactness

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
    · exact hchain c hchain' hne fun N hN => ⟨(hcs hN).2.1, (hcs hN).2.2⟩
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
