module

public import RequestProject.NerveBoundaryReflection

@[expose] public section

/-! Simultaneous deletion of an arbitrary family of maximal cells uses only finite supports. -/
namespace FiniteChains.Nerve
universe u
variable {P : Type u} [PartialOrder P]
  {C T : P → Prop} (hTC : ∀ p, T p → C p)
  (hmax : ∀ p, T p → ∀ x, C x → p ≤ x → x = p)
  {n : ℕ}
  (hlink₁ : ∀ v, T v → FillsDegreeIn (fun p => C p ∧ p < v) n)
  (hlink₂ : ∀ v, T v → FillsDegreeIn (fun p => C p ∧ p < v) (n + 1))

include hTC hmax hlink₁ hlink₂ in
theorem maximalFamily_finite (S : Finset P) (hS : ∀ v ∈ S, T v) :
    GeneratesDegreeIn (fun p => (C p ∧ ¬ T p) ∨ p ∈ S)
      (fun p => C p ∧ ¬ T p) (n + 1) ∧
    ReflectsBoundsIn (fun p => (C p ∧ ¬ T p) ∨ p ∈ S)
      (fun p => C p ∧ ¬ T p) (n + 1) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      constructor
      · intro c hc _ hd
        grind
      · intro c _ _ hb
        simpa using hb
  | @insert v S hvS ih =>
      have hvT  := hS v (Finset.mem_insert_self _ _)
      have hvC  := hTC v hvT
      have hprev := ih (fun p hp => hS p (Finset.mem_insert_of_mem hp))
      let Prev := fun p => (C p ∧ ¬ T p) ∨ p ∈ S
      let U := fun p => (C p ∧ ¬ T p) ∨ p ∈ insert v S
      let D := fun p => C p ∧ p ≤ v
      have hUC (p : P) (hp : U p) : C p := by grind
      have hinter (p : P) : (Prev p ∧ D p) ↔ C p ∧ p < v := by
        grind [lt_iff_le_and_ne]
      have hunion (p : P) : U p ↔ Prev p ∨ D p := by
        grind [Finset.mem_insert, lt_iff_le_and_ne]
      have hmix (p r : P) (hpr : p ≤ r) (hp : U p) (hr : U r) :
          (Prev p ∧ Prev r) ∨ (D p ∧ D r) := by
        have hpC := hUC p hp
        have hrC := hUC r hr
        grind [Finset.mem_insert]
      have hcone : AcyclicIn D := acyclicIn_of_subtype D (fun _ =>
        exists_bdry_eq_of_cycle id ⟨v, hvC, le_rfl⟩ monotone_id (fun _ => le_rfl) (·.2.2))
      constructor
      · exact generatesDegreeIn_union_of_unmixed hunion hmix hprev.1
          (generatesDegreeIn_of_acyclicRelIn (acyclicRelIn_of_acyclicIn hcone))
          (fillsDegreeIn_congr (fun p => (hinter p).symm) (hlink₁ v hvT))
      · exact reflectsBoundsIn_trans (fun _ hp => Or.inl hp)
          (reflectsBoundsIn_union_of_unmixed hmix
            (fillsDegreeIn_congr (fun p => (hinter p).symm) (hlink₂ v hvT))) hprev.2

theorem exists_finite_maximal_support (c : Ch P) (hc : c ∈ IncOn C) :
    ∃ S : Finset P, (∀ v ∈ S, T v) ∧ c ∈ IncOn (fun p => (C p ∧ ¬ T p) ∨ p ∈ S) := by
  classical
  let S := (c.support.biUnion (·.toFinset)).filter T
  refine ⟨S, fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
  rw [mem_incOn_iff]
  intro l hl
  obtain ⟨hchain, hsupp⟩ := (mem_incOn_iff c).mp hc l hl
  refine ⟨hchain, ?_⟩
  intro p hp
  by_cases hpT : T p
  · exact Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨l, hl, List.mem_toFinset.mpr hp⟩, hpT⟩)
  · exact Or.inl ⟨hsupp p hp, hpT⟩

include hTC hmax hlink₁ hlink₂ in
/-- Both homology comparisons hold for the whole maximal family. The family,
ambient complex, and cover are not required to be finite. -/
theorem maximalFamily_homology :
    GeneratesDegreeIn C (fun p => C p ∧ ¬ T p) (n + 1) ∧
      ReflectsBoundsIn C (fun p => C p ∧ ¬ T p) (n + 1) := by
  constructor
  · intro c hc hd hcyc
    obtain ⟨S, hS, hcS⟩ := exists_finite_maximal_support (T := T) c hc
    obtain ⟨d, hdB, y, hy, hdd, he⟩ :=
      (maximalFamily_finite hTC hmax hlink₁ hlink₂ S hS).1 c hcS hd hcyc
    refine ⟨d, hdB, y, incOn_mono ?_ hy, hdd, he⟩
    intro p hp
    exact hp.elim (·.1) (fun h => hTC p (hS p h))
  · intro c hc hd hbound
    obtain ⟨y, hy, hdy⟩ := hbound
    obtain ⟨S, hS, hyS⟩ := exists_finite_maximal_support (T := T) y hy
    exact (maximalFamily_finite hTC hmax hlink₁ hlink₂ S hS).2 c hc hd ⟨y, hyS, hdy⟩

end FiniteChains.Nerve
