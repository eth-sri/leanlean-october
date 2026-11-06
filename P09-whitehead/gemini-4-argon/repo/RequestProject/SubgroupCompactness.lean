module

public import Mathlib

@[expose] public section

namespace FiniteChains

open Set

variable {G : Type*} [Group G]

def FinitelyDetermined {ι : Type*} (Sat : Subgroup G → ι → Prop) : Prop :=
  ∀ v : ι, ∃ F : Finset G, ∀ N N' : Subgroup G,
    (∀ g ∈ F, (g ∈ N ↔ g ∈ N')) → (Sat N v ↔ Sat N' v)

def NSSet (G : Type*) [Group G] : Set (G → Bool) :=
  {f | f 1 = true ∧ (∀ a b, f a = true → f b = true → f (a * b) = true) ∧
    (∀ a, f a = true → f a⁻¹ = true) ∧ (∀ g a, f a = true → f (g * a * g⁻¹) = true)}

def toSubgroup (f : G → Bool) (hf : f ∈ NSSet G) : Subgroup G where
  carrier := {g | f g = true}
  one_mem' := hf.1
  mul_mem' ha hb := hf.2.1 _ _ ha hb
  inv_mem' ha := hf.2.2.1 _ ha

omit [Group G] in
theorem isClosed_of_finite_determination (P : (G → Bool) → Prop) (F : Finset G)
    (hF : ∀ f f' : G → Bool, (∀ g ∈ F, f g = f' g) → P f → P f') :
    IsClosed {f | P f} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  refine fun f hf => ⟨⋂ g ∈ F, (· g) ⁻¹' {f g},
    fun f' hf' => hf ∘ hF f' f fun g hg => by simpa using Set.mem_iInter₂.mp hf' g hg,
    isOpen_biInter_finset fun g _ => (isOpen_discrete _).preimage (continuous_apply g), by simp⟩

theorem isClosed_NSSet : IsClosed (NSSet G) := by
  classical
  have hset : NSSet G = ⋂ p : G × G × G, {f : G → Bool | f 1 = true ∧
      (f p.1 = true → f p.2.1 = true → f (p.1 * p.2.1) = true) ∧
      (f p.1 = true → f p.1⁻¹ = true) ∧
      (f p.1 = true → f (p.2.2 * p.1 * p.2.2⁻¹) = true)} := by
    ext f; simp only [NSSet, mem_setOf_eq, mem_iInter, Prod.forall]
    exact ⟨fun ⟨h1, h2, h3, h4⟩ a b g => ⟨h1, h2 a b, h3 a, h4 g a⟩,
      fun h => ⟨(h 1 1 1).1, fun a b => (h a b 1).2.1, fun a => (h a 1 1).2.2.1,
        fun g a => (h a 1 g).2.2.2⟩⟩
  rw [hset]
  refine isClosed_iInter fun ⟨a, b, g⟩ =>
    isClosed_of_finite_determination _ {1, a, b, a * b, a⁻¹, g * a * g⁻¹} fun f f' h => ?_
  rw [← h 1 (by simp), ← h a (by simp), ← h b (by simp), ← h (a * b) (by simp),
    ← h a⁻¹ (by simp), ← h (g * a * g⁻¹) (by simp)]
  exact id

theorem exists_normal_subgroup_forall {ι : Type*} (Sat : Subgroup G → ι → Prop)
    (hdet : FinitelyDetermined Sat)
    (hfin : ∀ S : Finset ι, ∃ N : Subgroup G, N.Normal ∧ ∀ v ∈ S, Sat N v) :
    ∃ N : Subgroup G, N.Normal ∧ ∀ v, Sat N v := by
  classical
  choose F hF using hdet
  let B : ι → Set (G → Bool) := fun v =>
    {f | ∃ N : Subgroup G, (∀ g ∈ F v, (g ∈ N ↔ f g = true)) ∧ Sat N v}
  have hBclosed (v : ι) : IsClosed (B v) :=
    isClosed_of_finite_determination _ (F v) fun f f' h ⟨N, hN, hS⟩ =>
      ⟨N, fun g hg => by rw [← h g hg]; exact hN g hg, hS⟩
  have hmemZ (N : Subgroup G) (hN : N.Normal) : (fun g => decide (g ∈ N)) ∈ NSSet G :=
    ⟨by simp, fun a b => by simpa using N.mul_mem, fun a => by simpa using N.inv_mem,
      fun g a => by simpa using (hN.conj_mem a · g)⟩
  have hne : (NSSet G ∩ ⋂ v, B v).Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hempty
    obtain ⟨u, hu⟩ := isClosed_NSSet.isCompact.elim_finite_subfamily_closed B hBclosed hempty
    obtain ⟨N, hN, hNu⟩ := hfin u
    exact disjoint_left.mp hu (hmemZ N hN)
      (mem_iInter₂.mpr fun v hv => ⟨N, fun _ _ => by simp, hNu v hv⟩)
  obtain ⟨f, hfZ, hfB⟩ := hne
  refine ⟨toSubgroup f hfZ, ⟨fun n hn g => hfZ.2.2.2 g n hn⟩, fun v => ?_⟩
  obtain ⟨N, hN, hS⟩ := mem_iInter.mp hfB v
  exact (hF v N (toSubgroup f hfZ) hN).mp hS

theorem exists_minimal_normal_sat (Sat : Subgroup G → Prop)
    (hchain : ∀ C : Set (Subgroup G), IsChain (· ≤ ·) C → C.Nonempty →
      (∀ N ∈ C, N.Normal ∧ Sat N) → Sat (sInf C))
    (M : Subgroup G) (hM : M.Normal) (hMs : Sat M) :
    ∃ N : Subgroup G, N ≤ M ∧ N.Normal ∧ Sat N ∧
      ∀ N' : Subgroup G, N' ≤ N → N'.Normal → Sat N' → N' = N := by
  classical
  let s : Set (Subgroup G) := {N | N ≤ M ∧ N.Normal ∧ Sat N}
  have hub : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, ub ≤ z :=
    fun c hcs hc y hy => ⟨sInf c, ⟨(sInf_le hy).trans (hcs hy).1,
      ⟨fun n hn g => Subgroup.mem_sInf.mpr fun N hN =>
        (hcs hN).2.1.conj_mem n (Subgroup.mem_sInf.mp hn N hN) g⟩,
      hchain c hc ⟨y, hy⟩ fun N hN => (hcs hN).2⟩, fun _ => sInf_le⟩
  obtain ⟨m, -, ⟨hmM, hmN, hmS⟩, hmax⟩ := zorn_le_nonempty₀ (α := (Subgroup G)ᵒᵈ) s
    (fun c hcs hc y hy => hub c hcs hc.symm y hy) M ⟨le_rfl, hM, hMs⟩
  exact ⟨m, hmM, hmN, hmS, fun N' hN' hN'n hN's =>
    le_antisymm hN' (hmax ⟨hN'.trans hmM, hN'n, hN's⟩ hN')⟩
