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

def wireSetoid (s : Setoid V) (b₀ t₀ : V) : Setoid V where
  r x y := s.r x y ∨ ((s.r x b₀ ∨ s.r x t₀) ∧ (s.r y b₀ ∨ s.r y t₀))
  iseqv :=
    { refl := fun x => Or.inl (s.refl x)
      symm := by
        rintro x y (h | h)
        · exact Or.inl (s.symm h)
        · exact Or.inr ⟨h.2, h.1⟩
      trans := by
        rintro x y z (h | h) (h' | h')
        · exact Or.inl (s.trans h h')
        · exact Or.inr ⟨h'.1.imp (s.trans h) (s.trans h), h'.2⟩
        · exact Or.inr ⟨h.1, h.2.imp (s.trans (s.symm h')) (s.trans (s.symm h'))⟩
        · exact Or.inr ⟨h.1, h'.2⟩ }

theorem card_quotient_le_wire (s t : Setoid V) (b₀ t₀ : V) (hst : s ≤ t)
    (hbt : t ≤ wireSetoid s b₀ t₀) :
    Nat.card (Quotient s) ≤ Nat.card (Quotient t) + 1 := by
  let S' : Set (Quotient s) := {q | q ≠ Quotient.mk s t₀}
  have hinj : Function.Injective (fun q : S' => Quotient.map' id (fun x y h => hst h) q.1) := by
    rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ h
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective q₁
    obtain ⟨y, rfl⟩ := Quotient.mk_surjective q₂
    apply Subtype.ext; dsimp only
    rcases hbt (Quotient.exact h) with h3 | ⟨hx, hy⟩
    · exact Quotient.sound h3
    · exact Quotient.sound (s.trans
        (hx.resolve_right fun h4 => h₁ (Quotient.sound h4))
        (s.symm (hy.resolve_right fun h4 => h₂ (Quotient.sound h4))))
  have h1 : Nat.card S' ≤ Nat.card (Quotient t) := Nat.card_le_card_of_injective _ hinj
  have : Finite (Quotient s) := Quotient.finite s
  have hc := Nat.card_congr (Equiv.Set.sumCompl ({q : Quotient s | q = Quotient.mk s t₀} : Set _))
  rw [Nat.card_sum, show ({q : Quotient s | q = Quotient.mk s t₀} : Set _)ᶜ = S' by ext; simp [S'],
    show Nat.card ({q : Quotient s | q = Quotient.mk s t₀} : Set _) = 1 by simp] at hc
  omega

end Count

section Weights

variable {V : Type*} [Finite V] {G : SimpleGraph V}

noncomputable local instance wcEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
noncomputable local instance wcEdgeDecEq : DecidableEq G.edgeSet := Classical.decEq _

def IsWireStep (ξ η : FK.BoundaryCondition V) (b₀ t₀ : V) : Prop :=
  ξ.partition ≤ η.partition ∧
    ∀ x y, η.partition.r x y → ξ.partition.r x y ∨
      ((ξ.partition.r x b₀ ∨ ξ.partition.r x t₀) ∧ (ξ.partition.r y b₀ ∨ ξ.partition.r y t₀))

omit [Finite V] in
theorem setoid_le_wire {ξ η : FK.BoundaryCondition V} {b₀ t₀ : V} (h : IsWireStep ξ η b₀ t₀)
    (A : FK.Configuration G) :
    FK.componentSetoid G η A ≤ wireSetoid (FK.componentSetoid G ξ A) b₀ t₀ := by
  apply FK.componentSetoid_le
  · intro _ _ huv; exact Or.inl (FK.actualConnected_component G ξ A huv)
  · intro x y hxy
    exact (h.2 x y hxy).imp (FK.boundary_component G ξ A) fun ⟨hx, hy⟩ =>
      ⟨hx.imp (FK.boundary_component G ξ A) (FK.boundary_component G ξ A),
       hy.imp (FK.boundary_component G ξ A) (FK.boundary_component G ξ A)⟩

theorem count_le_wire {ξ η : FK.BoundaryCondition V} {b₀ t₀ : V} (h : IsWireStep ξ η b₀ t₀)
    (A : FK.Configuration G) :
    FK.componentCount G ξ A ≤ FK.componentCount G η A + 1 :=
  card_quotient_le_wire _ _ b₀ t₀
    (FK.componentSetoid_mono_edges_boundary ξ η h.1 A A (Finset.Subset.refl _))
    (setoid_le_wire h A)

theorem count_eq_of_connected {ξ η : FK.BoundaryCondition V} {b₀ t₀ : V}
    (h : IsWireStep ξ η b₀ t₀) (A : FK.Configuration G)
    (hc : (FK.componentSetoid G ξ A).r b₀ t₀) :
    FK.componentCount G η A = FK.componentCount G ξ A := by
  have hge : FK.componentSetoid G η A ≤ FK.componentSetoid G ξ A := fun x y hxy => by
    rcases setoid_le_wire h A hxy with h3 | ⟨hx, hy⟩
    · exact h3
    · exact (FK.componentSetoid G ξ A).trans
        (hx.elim id fun h4 => (FK.componentSetoid G ξ A).trans h4 ((FK.componentSetoid G ξ A).symm hc))
        ((FK.componentSetoid G ξ A).symm
          (hy.elim id fun h4 => (FK.componentSetoid G ξ A).trans h4 ((FK.componentSetoid G ξ A).symm hc)))
  unfold FK.componentCount
  rw [le_antisymm hge (FK.componentSetoid_mono_edges_boundary ξ η h.1 A A (Finset.Subset.refl _))]

theorem measure_wire_le (q : FK.Parameters) {ξ η : FK.BoundaryCondition V} {b₀ t₀ : V}
    (h : IsWireStep ξ η b₀ t₀) (S : Set (FK.Configuration G))
    (hS : ∀ A ∈ S, (FK.componentSetoid G ξ A).r b₀ t₀) :
    (FK.measure G q η S).toReal ≤ q.val * (FK.measure G q ξ S).toReal := by
  have hw (A : FK.Configuration G) : FK.weight G q ξ A ≤ q.val * FK.weight G q η A := by
    unfold FK.weight
    have h1 := pow_le_pow_right₀ q.property (count_le_wire (G := G) h A)
    rw [pow_succ] at h1
    have hp1 : 0 ≤ FK.edgeParameter q ^ A.card * (1 - FK.edgeParameter q) ^ (Nat.card G.edgeSet - A.card) :=
      mul_nonneg (pow_nonneg (FK.edgeParameter_pos q).le _) (pow_nonneg (FK.one_sub_edgeParameter_pos q).le _)
    nlinarith [mul_le_mul_of_nonneg_left h1 hp1]
  have hZ : FK.partitionFunction G q ξ ≤ q.val * FK.partitionFunction G q η := by
    unfold FK.partitionFunction FK.FiniteProbability.partition
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun A _ => hw A
  have hZp := FK.partitionFunction_pos G q ξ
  have hZq := FK.partitionFunction_pos G q η
  rw [FK.measure_toReal_eq_indicator_sum, FK.measure_toReal_eq_indicator_sum]
  have key (A : FK.Configuration G) :
      FK.configurationProbability G q η A * S.indicator (fun _ => (1 : ℝ)) A =
      (FK.partitionFunction G q ξ / FK.partitionFunction G q η) *
        (FK.configurationProbability G q ξ A * S.indicator (fun _ => (1 : ℝ)) A) := by
    by_cases hA : A ∈ S
    · simp only [Set.indicator, hA, ite_true, mul_one, FK.configurationProbability, FK.weight,
        count_eq_of_connected h A (hS A hA)]
      field_simp
    · simp [Set.indicator, hA]
  simp_rw [key, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hZq).2 hZ)
    (Finset.sum_nonneg fun A _ => mul_nonneg (FK.configurationProbability_pos G q ξ A).le
      (Set.indicator_nonneg (fun _ _ => zero_le_one) A))

end Weights

end PottsDiscontinuity.TorusCrossing
