import RequestProject.NerveMaximalDeletion


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
      have hvT : T v := by simp_all
      have hvC : C v := hTC v hvT
      have hS' : ∀ p ∈ S, T p := by simp_all
      have hprev := ih hS'
      let Prev := fun p => (C p ∧ ¬ T p) ∨ p ∈ S
      let U := fun p => (C p ∧ ¬ T p) ∨ p ∈ insert v S
      let D := fun p => C p ∧ p ≤ v
      have hinter (p : P) : (Prev p ∧ D p) ↔ C p ∧ p < v := by
        constructor
        · rintro ⟨hp, hpC, hpv⟩
          refine ⟨hpC, lt_of_le_of_ne hpv ?_⟩
          grind
        grind
      have hunion (p : P) : U p ↔ Prev p ∨ D p := by
        grind
      have hmix : ∀ p r, p ≤ r → U p → U r →
          (Prev p ∧ Prev r) ∨ (D p ∧ D r) := by
        grind
      have hcone : AcyclicIn D := by
        let b : {p : P // D p} := ⟨v, hvC, le_refl _⟩
        apply acyclicIn_of_subtype D (by grind)
        intro c hc hd
        exact exists_bdry_eq_of_cycle id b monotone_id (by simp)
          (by aesop) hc hd
      constructor
      · exact generatesDegreeIn_union_of_unmixed hunion hmix hprev.1
          (generatesDegreeIn_of_acyclicRelIn (acyclicRelIn_of_acyclicIn hcone))
          (by simp_all)
      · exact reflectsBoundsIn_trans (fun _ hp => Or.inl hp)
          (reflectsBoundsIn_union_of_unmixed hmix
            (by grind)) hprev.2

theorem exists_finite_maximal_support c (hc : c ∈ IncOn C) :
    ∃ S : Finset P, (∀ v ∈ S, T v) ∧ c ∈ IncOn (fun p => (C p ∧ ¬ T p) ∨ p ∈ S) := by
  classical
  let S := (c.support.biUnion (·.toFinset)).filter T
  refine ⟨S, by grind, ?_⟩
  rw [mem_incOn_iff]
  intro l hl
  cases' (mem_incOn_iff c).mp hc l hl with hchain hsupp
  refine ⟨hchain, ?_⟩
  intro p hp
  by_cases hpT : T p
  · aesop
  simp_all

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
    tauto
  · intro c hc hd hbound
    obtain ⟨y, hy, hdy⟩ := hbound
    obtain ⟨S, hS, hyS⟩ := exists_finite_maximal_support (T := T) y hy
    exact (maximalFamily_finite hTC hmax hlink₁ hlink₂ S hS).2 c hc hd (by grind)
