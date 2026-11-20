module

public import PottsDiscontinuity.FK.IncreasingEvents

/-!
# Comparing two wirings that differ by one identification

If a boundary condition `η` is obtained from `ξ` by wiring one more pair `(b₀, t₀)` of classes
together, then the number of clusters changes by at most one, and not at all on the event that
`b₀` and `t₀` are already connected.  Consequently the two FK measures are comparable on
increasing events whose configurations already connect `b₀` to `t₀`.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

section Count

variable {V : Type*} [Finite V] {G : SimpleGraph V}

/-- The coarsening of a setoid obtained by wiring the classes of `b₀` and `t₀`. -/
def wireSetoid (s : Setoid V) (b₀ t₀ : V) : Setoid V where
  r x y := s.r x y ∨ ((s.r x b₀ ∨ s.r x t₀) ∧ (s.r y b₀ ∨ s.r y t₀))
  iseqv :=
    { refl := fun x => Or.inl (s.refl x)
      symm := by
        tauto
      trans := by
        rintro x y z (h | h) (h' | h')
        · exact Or.inl (s.trans h h')
        · refine Or.inr ⟨?_, h'.2⟩
          rcases h'.1 with h1 | h1
          · exact Or.inl (s.trans h h1)
          · exact Or.inr (s.trans h h1)
        · refine Or.inr ⟨h.1, ?_⟩
          rcases h.2 with h1 | h1
          · exact Or.inl (s.trans (s.symm h') h1)
          · exact Or.inr (s.trans (s.symm h') h1)
        simp_all }

/-- Adding one identification changes the number of classes by at most one. -/
theorem card_quotient_le_wire (s t : Setoid V) (b₀ t₀ : V) (hst : s ≤ t)
    (hbt : t ≤ wireSetoid s b₀ t₀) :
    Nat.card (Quotient s) ≤ Nat.card (Quotient t) + 1 := by
  let F := Quotient.map' id (fun x y h => hst h)
  let S' := ({Quotient.mk s t₀} : Set (Quotient s))ᶜ
  have hinj : Function.Injective (fun q : S' => F q.1) := by
    rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ h
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective q₁
    obtain ⟨y, rfl⟩ := Quotient.mk_surjective q₂
    apply Subtype.ext
    simp only
    have hxy : t.r x y := Quotient.exact h
    rcases hbt hxy with h3 | ⟨hx, hy⟩
    · exact Quotient.sound h3
    · have hmem (z : V) (hz : Quotient.mk s z ≠ Quotient.mk s t₀) : s.r z b₀ ∨ s.r z t₀ → s.r z b₀ :=
        fun h => h.elim id (fun h' => (hz (Quotient.sound h')).elim)
      exact Quotient.sound (s.trans (hmem x h₁ hx) (s.symm (hmem y h₂ hy)))
  have : Finite (Quotient s) := Quotient.finite s
  have hc : Nat.card (Quotient s) = 1 + Nat.card S' := by
    simpa only [S', Nat.card_coe_set_eq, Set.ncard_singleton] using
      (Set.ncard_add_ncard_compl ({Quotient.mk s t₀} : Set (Quotient s))).symm
  rw [hc, add_comm]
  exact Nat.add_le_add_right (Nat.card_le_card_of_injective _ hinj) _

end Count

section Weights

variable {V : Type*} [Finite V] {G : SimpleGraph V}

noncomputable local instance wcEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _

/-- Hypothesis: `η` is obtained from `ξ` by additionally wiring the classes of `b₀` and `t₀`. -/
def IsWireStep (ξ η : FK.BoundaryCondition V) (b₀ t₀ : V) : Prop :=
  ξ.partition ≤ η.partition ∧
    ∀ x y, η.partition.r x y → ξ.partition.r x y ∨
      ((ξ.partition.r x b₀ ∨ ξ.partition.r x t₀) ∧ (ξ.partition.r y b₀ ∨ ξ.partition.r y t₀))

omit [Finite V] in
theorem setoid_le_wire {ξ η : FK.BoundaryCondition V} {b₀ t₀ : V} (h : IsWireStep ξ η b₀ t₀)
    (A : FK.Configuration G) :
    FK.componentSetoid G η A ≤ wireSetoid (FK.componentSetoid G ξ A) b₀ t₀ := by
  apply FK.componentSetoid_le
  · intro u v huv
    exact Or.inl (FK.actualConnected_component G ξ A huv)
  · intro x y hxy
    exact (h.2 x y hxy).imp (FK.boundary_component G ξ A) fun ⟨hx, hy⟩ =>
      ⟨hx.imp (FK.boundary_component G ξ A) (FK.boundary_component G ξ A),
        hy.imp (FK.boundary_component G ξ A) (FK.boundary_component G ξ A)⟩

theorem count_le_wire {ξ η : FK.BoundaryCondition V} {b₀ t₀ : V} (h : IsWireStep ξ η b₀ t₀)
    (A : FK.Configuration G) :
    FK.componentCount G ξ A ≤ FK.componentCount G η A + 1 := by
  unfold FK.componentCount
  exact card_quotient_le_wire _ _ b₀ t₀
    (FK.componentSetoid_mono_edges_boundary ξ η h.1 A A (Finset.Subset.refl _))
    (setoid_le_wire h A)

theorem count_eq_of_connected {ξ η : FK.BoundaryCondition V} {b₀ t₀ : V}
    (h : IsWireStep ξ η b₀ t₀) (A : FK.Configuration G)
    (hc : (FK.componentSetoid G ξ A).r b₀ t₀) :
    FK.componentCount G η A = FK.componentCount G ξ A := by
  have hle := FK.componentSetoid_mono_edges_boundary ξ η h.1 A A (Finset.Subset.refl _)
  have hge : FK.componentSetoid G η A ≤ FK.componentSetoid G ξ A := by
    intro x y hxy
    rcases setoid_le_wire h A hxy with h3 | ⟨hx, hy⟩
    · exact h3
    · let s := FK.componentSetoid G ξ A
      have hmem (z : V) : s.r z b₀ ∨ s.r z t₀ → s.r z b₀ :=
        fun h => h.elim id (fun h' => s.trans h' (s.symm hc))
      exact s.trans (hmem x hx) (s.symm (hmem y hy))
  have : FK.componentSetoid G η A = FK.componentSetoid G ξ A := le_antisymm hge hle
  unfold FK.componentCount
  rw [this]

/-- On an event on which `b₀` and `t₀` are connected, the measure with the extra wiring is at most
`q` times the measure without it. -/
theorem measure_wire_le (q : FK.Parameters) {ξ η : FK.BoundaryCondition V} {b₀ t₀ : V}
    (h : IsWireStep ξ η b₀ t₀) (S : Set (FK.Configuration G))
    (hS : ∀ A ∈ S, (FK.componentSetoid G ξ A).r b₀ t₀) :
    (FK.measure G q η S).toReal ≤ q.val * (FK.measure G q ξ S).toReal := by
  have hZ : FK.partitionFunction G q ξ ≤ q.val * FK.partitionFunction G q η := by
    unfold FK.partitionFunction FK.FiniteProbability.partition
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro A _
    have hp := FK.edgeParameter_pos q
    have hp' := FK.one_sub_edgeParameter_pos q
    have hw := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ q.property (count_le_wire h A))
      (show 0 ≤ FK.edgeParameter q ^ A.card * (1 - FK.edgeParameter q) ^ (Nat.card G.edgeSet - A.card) by positivity)
    simpa only [FK.weight, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hw
  rw [FK.measure_toReal_eq_indicator_sum, FK.measure_toReal_eq_indicator_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  by_cases hA : A ∈ S
  · simp only [Set.indicator_of_mem hA, mul_one, FK.configurationProbability]
    rw [← mul_div_assoc, div_le_div_iff₀ (FK.partitionFunction_pos G q η) (FK.partitionFunction_pos G q ξ),
      FK.weight, count_eq_of_connected h A (hS A hA), ← FK.weight]
    simpa only [mul_left_comm, mul_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hZ (FK.weight_pos G q ξ A).le
  · simp [hA]

end Weights

end PottsDiscontinuity.TorusCrossing
