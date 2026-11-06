import RequestProject.OrderNerveAffineEdgePath
import RequestProject.FiniteSimpleArcConcatenation


/-! Realizing an explicitly enumerated finite rank-one poset cycle gives
an actual topological circle. All topological assertions follow from exact
affine edge coordinates. Pending Lean verification. -/

noncomputable section
open scoped Classical unitInterval
open Set Topology

namespace FiniteChains.Comb
open RelativeAttachment

structure FinitePosetCycle (P : Type) [PartialOrder P] (n : ℕ) where
  positive : 0 < n
  vertex : Fin (n + 2) ≃ P
  consecutive : ∀ i : Fin (n + 1),
    vertex i.castSucc ≤ vertex i.succ ∨ vertex i.succ ≤ vertex i.castSucc
  closing : vertex (Fin.last (n + 1)) ≤ vertex 0 ∨ vertex 0 ≤ vertex (Fin.last (n + 1))
  edges : ∀ a b : P, a ≠ b → (a ≤ b ∨ b ≤ a) →
    (∃ i : Fin (n + 1), (a = vertex i.castSucc ∧ b = vertex i.succ) ∨
      (b = vertex i.castSucc ∧ a = vertex i.succ)) ∨
    (a = vertex (Fin.last (n + 1)) ∧ b = vertex 0) ∨
      (b = vertex (Fin.last (n + 1)) ∧ a = vertex 0)
  height : P → ℕ
  height_strict : StrictMono height
  height_le : ∀ p, height p ≤ 1

namespace FinitePosetCycle

variable {P : Type} [PartialOrder P] {n : ℕ} (C : FinitePosetCycle P n)

def edge (i : Fin (n + 1)) := orderNerveComparablePath (C.consecutive i)
def lastEdge := orderNerveComparablePath C.closing

theorem edge_coordinates i t p :
    orderNerveRealizationCoordinates P (C.edge i t) p =
      (1 - t) * (if C.vertex i.castSucc = p then 1 else 0) +
        t * (if C.vertex i.succ = p then 1 else 0) :=
  orderNerveComparablePath_coordinates _ _ _

theorem lastEdge_coordinates t p :
    orderNerveRealizationCoordinates P (C.lastEdge t) p =
      (1 - t) * (if C.vertex (Fin.last (n + 1)) = p then 1 else 0) +
        t * (if C.vertex 0 = p then 1 else 0) :=
  orderNerveComparablePath_coordinates _ _ _

theorem vne (h : i.val ≠ j.val) : C.vertex i ≠ C.vertex j :=
  by aesop

theorem edge_injective i : Function.Injective (C.edge i) :=
  orderNerveComparablePath_injective _ (C.vne (by simp))

theorem lastEdge_injective : Function.Injective C.lastEdge :=
  orderNerveComparablePath_injective _ (by simp)

theorem edge_meet i j (hij : i < j) s t
    (h : C.edge i s = C.edge j t) : s = 1 ∧ t = 0 := by
  have hi0 := congrArg (orderNerveRealizationCoordinates P · (C.vertex i.castSucc)) h
  have hj1 := congrArg (orderNerveRealizationCoordinates P · (C.vertex j.succ)) h
  have hji : C.vertex j.castSucc ≠ C.vertex i.castSucc := by aesop
  have hji' : C.vertex j.succ ≠ C.vertex i.castSucc := C.vne (by dsimp; omega)
  have hij₂ : C.vertex i.succ ≠ C.vertex j.succ := by aesop
  simp [edge_coordinates, ite_true, mul_one, mul_zero, add_zero] at hi0
  simp [edge_coordinates, ite_true, mul_one, mul_zero, zero_add, add_zero] at hj1
  grind

def «prefix» : Path (orderNerveRealizationVertex (C.vertex 0))
    (orderNerveRealizationVertex (C.vertex (Fin.last (n + 1)))) :=
  arcConcat n (orderNerveRealizationVertex ∘ C.vertex) C.edge

theorem prefix_injective : Function.Injective C.prefix :=
  arcConcat_injective n _ _ C.edge_injective C.edge_meet

theorem prefix_meet_last s t (h : C.prefix s = C.lastEdge t) :
    C.prefix s = orderNerveRealizationVertex (C.vertex 0) ∨
      C.prefix s = orderNerveRealizationVertex (C.vertex (Fin.last (n + 1))) := by
  obtain ⟨i, u, hu⟩ := (arcConcat_range n (orderNerveRealizationVertex ∘ C.vertex)
    C.edge _).mp ⟨s, rfl⟩
  have he := hu.trans h
  by_cases hi : i.val = 0
  · have hc := (C.edge_coordinates i u (C.vertex (Fin.last (n + 1)))).symm.trans
      ((congrArg _ he).trans
          (C.lastEdge_coordinates t _))
    have h₀ : C.vertex i.castSucc ≠ C.vertex (Fin.last _) := by simp
    have h₁ : C.vertex i.succ ≠ C.vertex (Fin.last _) := C.vne (by
      have hn := C.positive
      dsimp
      omega)
    grind
  · have hc := (C.edge_coordinates i u _).symm.trans
      ((congrArg _ he).trans
        (C.lastEdge_coordinates t (C.vertex 0)))
    aesop

def traversal := C.prefix.trans C.lastEdge

theorem traversal_fiber s t (h : C.traversal s = C.traversal t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) :=
  path_trans_loop_fiber C.prefix C.lastEdge C.prefix_injective C.lastEdge_injective
    C.prefix_meet_last h

include C in
theorem height_ne {a b : P} (hne : a ≠ b) (h : a ≤ b ∨ b ≤ a) :
    C.height a ≠ C.height b := by
  rcases h with h | h
  · exact ne_of_lt (C.height_strict (lt_of_le_of_ne h hne))
  · exact (ne_of_lt (C.height_strict (lt_of_le_of_ne h hne.symm))).symm

include C in
theorem support_pair [Fintype P] (x : orderNerveRealization P) :
    ∃ a b : P, a ≠ b ∧ (a ≤ b ∨ b ≤ a) ∧
      ∀ p, p ≠ a → p ≠ b → orderNerveRealizationCoordinates P x p = 0 := by
  let c := orderNerveRealizationCoordinates P x
  have hpositive : ∃ a, 0 < c a := by
    by_contra hn
    push_neg at hn
    have hs : ∑ a, c a ≤ 0 := Finset.sum_nonpos (by simp_all)
    have he := orderNerveRealizationCoordinates_sum x
    linarith
  cases' hpositive with a ha
  have hc := orderNerveRealizationCoordinates_support_chain x
  by_cases hb : ∃ b, b ≠ a ∧ 0 < c b
  · obtain ⟨b, hba, hb⟩ := hb
    have hab := hc ha hb hba.symm
    refine ⟨a, b, hba.symm, hab, ?_⟩
    intro p hpa hpb
    apply le_antisymm _ (orderNerveRealizationCoordinates_nonneg x p)
    by_contra hp
    have hp' := lt_of_not_ge hp
    have h₁ := C.height_ne hba.symm hab
    have h₂ := C.height_ne hpa (hc hp' ha hpa)
    have h₃ := C.height_ne hpb (hc hp' hb hpb)
    have ha₁ := C.height_le a
    have hb₁ := C.height_le b
    have hp₁ := C.height_le p
    omega
  · have hz : ∀ p, p ≠ a → c p = 0 := by
      intro p hpa
      apply le_antisymm _ (orderNerveRealizationCoordinates_nonneg x p)
      grind
    let k := C.vertex.symm a
    by_cases hk : k = Fin.last _
    · have he : C.vertex (Fin.last _) = a :=
        by grind
      refine ⟨a, C.vertex 0, ?_, ?_, by grind⟩
      · grind
      · rw [← he]
        exact C.closing
    · cases' Fin.exists_castSucc_eq.mpr hk with i hi
      have he : C.vertex i.castSucc = a :=
        by grind
      refine ⟨a, C.vertex i.succ, ?_, ?_, by grind⟩
      · grind
      · rw [← he]
        exact C.consecutive i

theorem traversal_surjective : Function.Surjective C.traversal := by
  letI : Fintype P := Fintype.ofEquiv _ C.vertex
  intro x
  obtain ⟨a, b, hne, hab, hs⟩ := C.support_pair x
  rcases C.edges a b hne hab with ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support _
      (by simp_all) x hs
    change x ∈ Set.range (C.prefix.trans C.lastEdge)
    rw [Path.trans_range]
    exact Or.inl ((arcConcat_range n (orderNerveRealizationVertex ∘ C.vertex) C.edge x).mpr
      (by aesop))
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support (C.consecutive i)
      (by grind) x (by simp_all)
    change x ∈ Set.range (C.prefix.trans C.lastEdge)
    rw [Path.trans_range]
    exact Or.inl ((arcConcat_range n (orderNerveRealizationVertex ∘ C.vertex) C.edge x).mpr
      (by aesop))
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support C.closing
      (by simp) x hs
    change x ∈ Set.range (C.prefix.trans C.lastEdge)
    rw [Path.trans_range]
    tauto
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support C.closing
      (by simp) x (by simp_all)
    change x ∈ Set.range (C.prefix.trans C.lastEdge)
    rw [Path.trans_range]
    tauto

def boundaryHomeomorph :=
  (simpleLoopBoundaryHomeomorph C.traversal C.traversal_surjective C.traversal_fiber).symm
