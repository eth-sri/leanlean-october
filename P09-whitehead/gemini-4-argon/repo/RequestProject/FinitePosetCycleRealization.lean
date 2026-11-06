module

public import RequestProject.OrderNerveAffineEdgePath
public import RequestProject.FiniteSimpleArcConcatenation

@[expose] public section

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

theorem edge_coordinates (i : Fin (n + 1)) (t : I) (p : P) :
    orderNerveRealizationCoordinates P (C.edge i t) p =
      (1 - (t : ℝ)) * (if C.vertex i.castSucc = p then 1 else 0) +
        (t : ℝ) * (if C.vertex i.succ = p then 1 else 0) :=
  orderNerveComparablePath_coordinates _ _ _

theorem lastEdge_coordinates (t : I) (p : P) :
    orderNerveRealizationCoordinates P (C.lastEdge t) p =
      (1 - (t : ℝ)) * (if C.vertex (Fin.last (n + 1)) = p then 1 else 0) +
        (t : ℝ) * (if C.vertex 0 = p then 1 else 0) :=
  orderNerveComparablePath_coordinates _ _ _

theorem vne {i j : Fin (n + 2)} (h : i.val ≠ j.val) : C.vertex i ≠ C.vertex j :=
  fun he => h (congrArg Fin.val (C.vertex.injective he))

def «prefix» : Path (orderNerveRealizationVertex (C.vertex 0))
    (orderNerveRealizationVertex (C.vertex (Fin.last (n + 1)))) :=
  arcConcat n (orderNerveRealizationVertex ∘ C.vertex) C.edge

def traversal : Path (orderNerveRealizationVertex (C.vertex 0))
    (orderNerveRealizationVertex (C.vertex 0)) := C.prefix.trans C.lastEdge

theorem traversal_fiber (s t : I) (h : C.traversal s = C.traversal t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  refine path_trans_loop_fiber C.prefix C.lastEdge
    (arcConcat_injective n _ _ (fun i => orderNerveComparablePath_injective _ (C.vne (by simp))) fun i j hij s t h => ?_)
    (orderNerveComparablePath_injective _ (C.vne (by simp))) (fun s t h => ?_) h
  · have hij' : i.val < j.val := hij
    have hi0 := congrArg (fun z => orderNerveRealizationCoordinates P z (C.vertex i.castSucc)) h
    have hj1 := congrArg (fun z => orderNerveRealizationCoordinates P z (C.vertex j.succ)) h
    dsimp at hi0 hj1
    simp only [edge_coordinates, ite_true,
      if_neg (C.vne (by simp) : C.vertex i.succ ≠ C.vertex i.castSucc),
      if_neg (C.vne (by simpa using ne_of_gt hij') : C.vertex j.castSucc ≠ C.vertex i.castSucc),
      if_neg (C.vne (by dsimp; omega) : C.vertex j.succ ≠ C.vertex i.castSucc),
      mul_one, mul_zero, add_zero] at hi0
    simp only [edge_coordinates, ite_true,
      if_neg (C.vne (by dsimp; omega) : C.vertex i.castSucc ≠ C.vertex j.succ),
      if_neg (C.vne (by dsimp; omega) : C.vertex i.succ ≠ C.vertex j.succ),
      if_neg (C.vne (by simp) : C.vertex j.castSucc ≠ C.vertex j.succ),
      mul_one, mul_zero, zero_add, add_zero] at hj1
    exact ⟨Subtype.ext (by change (s : ℝ) = 1; linarith), Subtype.ext (by change (t : ℝ) = 0; linarith)⟩
  · obtain ⟨i, u, hu⟩ := (arcConcat_range n (orderNerveRealizationVertex ∘ C.vertex) C.edge _).mp ⟨s, rfl⟩
    have he := hu.trans h
    by_cases hi : i.val = 0
    · have hc := (C.edge_coordinates i u (C.vertex (Fin.last (n + 1)))).symm.trans
        ((congrArg (fun z => orderNerveRealizationCoordinates P z (C.vertex (Fin.last (n + 1)))) he).trans
          (C.lastEdge_coordinates t (C.vertex (Fin.last (n + 1)))))
      have hn := C.positive
      simp only [if_neg (C.vne (by dsimp; omega) : C.vertex i.castSucc ≠ C.vertex (Fin.last (n + 1))),
        if_neg (C.vne (by dsimp; omega) : C.vertex i.succ ≠ C.vertex (Fin.last (n + 1))),
        if_neg (C.vne (by simp) : C.vertex 0 ≠ C.vertex (Fin.last (n + 1))),
        ite_true, mul_zero, mul_one, add_zero] at hc
      exact .inl (h.trans (by rw [show t = 1 from Subtype.ext (by change (t : ℝ) = 1; linarith)]; exact C.lastEdge.target))
    · have hc := (C.edge_coordinates i u (C.vertex 0)).symm.trans
        ((congrArg (fun z => orderNerveRealizationCoordinates P z (C.vertex 0)) he).trans
          (C.lastEdge_coordinates t (C.vertex 0)))
      simp only [if_neg (C.vne (by simpa using hi) : C.vertex i.castSucc ≠ C.vertex 0),
        if_neg (C.vne (by simp) : C.vertex i.succ ≠ C.vertex 0),
        if_neg (C.vne (by simp) : C.vertex (Fin.last (n + 1)) ≠ C.vertex 0),
        ite_true, mul_zero, mul_one, zero_add, add_zero] at hc
      exact .inr (h.trans (by rw [show t = 0 from Subtype.ext (by change (t : ℝ) = 0; linarith)]; exact C.lastEdge.source))

theorem traversal_surjective : Function.Surjective C.traversal := by
  letI : Fintype P := Fintype.ofEquiv (Fin (n + 2)) C.vertex
  intro x
  have hne_ht {a b : P} (hne : a ≠ b) (h : a ≤ b ∨ b ≤ a) : C.height a ≠ C.height b :=
    h.elim (fun h => ne_of_lt (C.height_strict (lt_of_le_of_ne h hne)))
      fun h => (ne_of_lt (C.height_strict (lt_of_le_of_ne h hne.symm))).symm
  have hsupp : ∃ a b : P, a ≠ b ∧ (a ≤ b ∨ b ≤ a) ∧
      ∀ p, p ≠ a → p ≠ b → orderNerveRealizationCoordinates P x p = 0 := by
    let c := orderNerveRealizationCoordinates P x
    have hpos : ∃ a, 0 < c a := by
      by_contra hn; push_neg at hn
      linarith [Finset.sum_nonpos fun a (_ : a ∈ Finset.univ) => hn a,
        orderNerveRealizationCoordinates_sum x]
    obtain ⟨a, ha⟩ := hpos
    have hc := orderNerveRealizationCoordinates_support_chain x
    by_cases hb : ∃ b, b ≠ a ∧ 0 < c b
    · obtain ⟨b, hba, hb⟩ := hb
      have hab := hc ha hb hba.symm
      refine ⟨a, b, hba.symm, hab, fun p hpa hpb =>
        le_antisymm ?_ (orderNerveRealizationCoordinates_nonneg x p)⟩
      by_contra hp
      have hp' := lt_of_not_ge hp
      have := hne_ht hba.symm hab
      have := hne_ht hpa (hc hp' ha hpa)
      have := hne_ht hpb (hc hp' hb hpb)
      have := C.height_le a; have := C.height_le b; have := C.height_le p; omega
    · have hz (p) (hpa : p ≠ a) : c p = 0 :=
        le_antisymm (le_of_not_gt fun hp => hb ⟨p, hpa, hp⟩) (orderNerveRealizationCoordinates_nonneg x p)
      let k := C.vertex.symm a
      by_cases hk : k = Fin.last (n + 1)
      · have he : C.vertex (Fin.last (n + 1)) = a := (congrArg C.vertex hk).symm.trans (C.vertex.apply_symm_apply a)
        exact ⟨a, C.vertex 0, he ▸ C.vne (by simp), he ▸ C.closing, fun p hpa _ => hz p hpa⟩
      · obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hk
        have he : C.vertex i.castSucc = a := (congrArg C.vertex hi).trans (C.vertex.apply_symm_apply a)
        exact ⟨a, C.vertex i.succ, he ▸ C.vne (by simp), he ▸ C.consecutive i, fun p hpa _ => hz p hpa⟩
  obtain ⟨a, b, hne, hab, hs⟩ := hsupp
  change x ∈ Set.range (C.prefix.trans C.lastEdge)
  rw [Path.trans_range]
  rcases C.edges a b hne hab with ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support (C.consecutive i) (C.vne (by simp)) x hs
    exact .inl ((arcConcat_range n (orderNerveRealizationVertex ∘ C.vertex) C.edge x).mpr ⟨i, t, ht⟩)
  · obtain ⟨t, ht⟩ := orderNerveComparablePath_of_support (C.consecutive i) (C.vne (by simp)) x fun p h₀ h₁ => hs p h₁ h₀
    exact .inl ((arcConcat_range n (orderNerveRealizationVertex ∘ C.vertex) C.edge x).mpr ⟨i, t, ht⟩)
  · exact .inr (orderNerveComparablePath_of_support C.closing (C.vne (by simp)) x hs)
  · exact .inr (orderNerveComparablePath_of_support C.closing (C.vne (by simp)) x fun p h₀ h₁ => hs p h₁ h₀)

def boundaryHomeomorph : orderNerveRealization P ≃ₜ UnitBoundary (Fin 2 → ℝ) :=
  (simpleLoopBoundaryHomeomorph C.traversal C.traversal_surjective C.traversal_fiber).symm
