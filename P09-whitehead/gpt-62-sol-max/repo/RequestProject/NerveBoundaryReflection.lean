module

public import RequestProject.NerveDegreeTransfer

@[expose] public section

/-! Reflection of actual fillings under deletion of an acyclic attaching piece. -/
namespace FiniteChains.Nerve
universe u
variable {P : Type u} [Preorder P]

/-- A homogeneous chain in `B` that bounds in `U` already bounds in `B`. -/
def ReflectsBoundsIn (U B : P → Prop) (n : ℕ) : Prop :=
  ∀ c ∈ IncOn B, lengthProjection n c = c →
    (∃ y ∈ IncOn U, bdry y = c) → ∃ y ∈ IncOn B, bdry y = c

/-- The injectivity half of the chain gluing argument. Only intersection cycles
in the degree of the chain being filled need to bound. -/
theorem reflectsBoundsIn_union_of_unmixed {A B U : P → Prop} {n : ℕ}
    (hmix : ∀ a b : P, a ≤ b → U a → U b → (A a ∧ A b) ∨ (B a ∧ B b))
    (hJ : FillsDegreeIn (fun p => A p ∧ B p) n) : ReflectsBoundsIn U A n := by
  intro c hc hd hbound
  obtain ⟨y, hy, hyd, hdy⟩ := homogeneous_filling hd hbound
  obtain ⟨a, ha, _, b, hb, hbd, rfl⟩ := exists_split_homogeneous_of_unmixed hmix hy hyd
  rw [map_add] at hdy
  have hdbA : bdry b ∈ IncOn A := by
    have he : bdry b = c - bdry a := by rw [← hdy]; abel
    rw [he]
    exact AddSubgroup.sub_mem _ hc (bdry_mem_incOn ha)
  have hdbJ : bdry b ∈ IncOn (fun p => A p ∧ B p) := by
    rw [← incOn_inf]
    exact ⟨hdbA, bdry_mem_incOn hb⟩
  have hdbd : lengthProjection n (bdry b) = bdry b := by rw [lengthProjection_bdry, hbd]
  obtain ⟨z, hz, hdz⟩ := hJ (bdry b) hdbJ hdbd (by simp [bdry_bdry])
  refine ⟨a + z, AddSubgroup.add_mem _ ha (incOn_mono (fun _ h => h.1) hz), ?_⟩
  rw [map_add, hdz, hdy]

theorem reflectsBoundsIn_trans {U B C : P → Prop} {n : ℕ}
    (hCB : ∀ p, C p → B p) (hUB : ReflectsBoundsIn U B n)
    (hBC : ReflectsBoundsIn B C n) : ReflectsBoundsIn U C n := by
  intro c hc hd hbound
  exact hBC c hc hd (hUB c (incOn_mono hCB hc) hd hbound)

end FiniteChains.Nerve
