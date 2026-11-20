module

public import Mathlib

/-!
# Conserved flows on a bipartite indexed graph

Edges are indexed independently of their endpoint pairs, so parallel edges are
retained. A circulation space of dimension at most one forces every nonzero
circulation to have degree at most two on its support.
-/

@[expose] public section

open scoped BigOperators

namespace PottsDiscontinuity.TorusLoops.Bipartite

variable {E P D : Type*} [Fintype E] [Fintype P] [Fintype D]

noncomputable section

section

variable (p : E → P) (d : E → D)

def incidence : Matrix (P ⊕ D) E ℚ := by
  classical
  exact fun v e => (if v = Sum.inl (p e) then 1 else 0) -
    (if v = Sum.inr (d e) then 1 else 0)

def boundary : (E → ℚ) →ₗ[ℚ] (P ⊕ D → ℚ) := by
  classical
  exact Matrix.toLin' (incidence p d)

def coboundary : (P ⊕ D → ℚ) →ₗ[ℚ] (E → ℚ) where
  toFun a e := a (.inl (p e)) - a (.inr (d e))
  map_add' _ _ := by ext; simp only [Pi.add_apply]; ring
  map_smul' _ _ := by ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

end

omit [Fintype P] [Fintype D] in
open scoped Classical in
theorem boundary_inl (p : E → P) (d : E → D) (f : E → ℚ) (v : P) :
    boundary p d f (.inl v) = ∑ e with p e = v, f e := by
  simp [boundary, incidence, Matrix.toLin'_apply, Matrix.mulVec, eq_comm,
    Finset.sum_filter, dotProduct]

omit [Fintype P] [Fintype D] in
open scoped Classical in
theorem boundary_inr (p : E → P) (d : E → D) (f : E → ℚ) (v : D) :
    boundary p d f (.inr v) = -(∑ e with d e = v, f e) := by
  simp [boundary, incidence, Matrix.toLin'_apply, Matrix.mulVec, eq_comm,
    Finset.sum_filter, ← Finset.sum_neg_distrib, dotProduct]

omit [Fintype E] in
open scoped Classical in
theorem coboundary_eq_transpose (p : E → P) (d : E → D) :
    coboundary p d = Matrix.toLin' (incidence p d).transpose := by
  apply LinearMap.ext
  intro a
  funext e
  change a (.inl (p e)) - a (.inr (d e)) = ∑ v, incidence p d v e * a v
  simp only [incidence, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

section

variable (p : E → P) (d : E → D)

theorem rank_boundary_eq_coboundary :
    Module.finrank ℚ (LinearMap.range (boundary p d)) =
      Module.finrank ℚ (LinearMap.range (coboundary p d)) := by
  classical
  rw [coboundary_eq_transpose]
  change (incidence p d).rank = (incidence p d).transpose.rank
  simp

def constantKernel : ℚ →ₗ[ℚ] LinearMap.ker (coboundary p d) where
  toFun a := ⟨fun _ => a, by ext; exact sub_self a⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem card_edges_le_vertices (v₀ : P)
    (hker : Module.finrank ℚ (LinearMap.ker (boundary p d)) ≤ 1) :
    Fintype.card E ≤ Fintype.card P + Fintype.card D := by
  have hinj : Function.Injective (constantKernel p d) := by
    intro a b hab
    exact congrFun (congrArg Subtype.val hab) (.inl v₀)
  have hk := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_self] at hk
  have hb := LinearMap.finrank_range_add_finrank_ker (boundary p d)
  have hc := LinearMap.finrank_range_add_finrank_ker (coboundary p d)
  rw [Module.finrank_pi, rank_boundary_eq_coboundary] at hb
  rw [Module.finrank_pi, Fintype.card_sum] at hc
  omega

end

abbrev SupportEdge (f : E → ℚ) := {e : E // f e ≠ 0}
abbrev SupportVertex {X : Type*} (p : E → X) (f : E → ℚ) := {v : X // ∃ e, f e ≠ 0 ∧ p e = v}

local instance supportEdgeFintype (f : E → ℚ) : Fintype (SupportEdge f) := Fintype.ofFinite _
local instance supportVertexFintype {X : Type*} [Fintype X] (p : E → X) (f : E → ℚ) :
    Fintype (SupportVertex p f) := Fintype.ofFinite _

def supportEndpoint {X : Type*} (p : E → X) (f : E → ℚ) (e : SupportEdge f) : SupportVertex p f :=
  ⟨p e.val, e.val, e.property, rfl⟩

def supportExtension (f : E → ℚ) : (SupportEdge f → ℚ) →ₗ[ℚ] (E → ℚ) := by
  classical
  exact
    { toFun := fun a e => if he : f e ≠ 0 then a ⟨e, he⟩ else 0
      map_add' := by intro a b; ext e; by_cases he : f e = 0 <;> simp_all
      map_smul' := by intro c a; ext e; simp }

omit [Fintype E] in
@[simp] theorem supportExtension_apply (f : E → ℚ) (a : SupportEdge f → ℚ)
    (e : SupportEdge f) : supportExtension f a e.val = a e := by
  simp [supportExtension, e.property]

omit [Fintype E] in
theorem supportExtension_injective (f : E → ℚ) : Function.Injective (supportExtension f) := by
  intro a b hab
  funext e
  have he := congrFun hab e.val
  simpa using he

theorem sum_supportExtension (f : E → ℚ) (a : SupportEdge f → ℚ) (k : E → ℚ) :
    (∑ e : E, k e * supportExtension f a e) =
      ∑ e : SupportEdge f, k e.val * a e := by
  classical
  have he : (∑ e : SupportEdge f, k e.val * a e) =
      ∑ e : SupportEdge f, k e.val * supportExtension f a e.val := by simp
  rw [he, ← Finset.sum_subtype (Finset.univ.filter fun e => f e ≠ 0)
    (by simp) (fun e => k e * supportExtension f a e), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hf : f e = 0 <;> simp [supportExtension, hf]

omit [Fintype P] [Fintype D] in
theorem boundary_supportExtension_active (p : E → P) (d : E → D) (f : E → ℚ)
    (a : SupportEdge f → ℚ) (v : SupportVertex p f ⊕ SupportVertex d f) :
    boundary p d (supportExtension f a) (Sum.map Subtype.val Subtype.val v) =
      boundary (supportEndpoint p f) (supportEndpoint d f) a v := by
  classical
  change (∑ e, incidence p d (Sum.map Subtype.val Subtype.val v) e * supportExtension f a e) = _
  rw [sum_supportExtension]
  apply Finset.sum_congr rfl
  intro e _
  cases v <;> simp [incidence, supportEndpoint, Subtype.ext_iff]

omit [Fintype P] [Fintype D] in
theorem supportExtension_mem_kernel (p : E → P) (d : E → D) (f : E → ℚ)
    (a : LinearMap.ker (boundary (supportEndpoint p f) (supportEndpoint d f))) :
    supportExtension f a.val ∈ LinearMap.ker (boundary p d) := by
  classical
  ext v
  by_cases hv : v ∈ Set.range (Sum.map (fun u : SupportVertex p f => u.val)
    (fun u : SupportVertex d f => u.val))
  · obtain ⟨u, rfl⟩ := hv
    exact (boundary_supportExtension_active p d f a.val u).trans (congrFun a.property u)
  · change (∑ e, incidence p d v e * supportExtension f a.val e) = 0
    rw [sum_supportExtension]
    apply Finset.sum_eq_zero
    intro e _
    have hp : v ≠ Sum.inl (p e.val) := fun h => hv ⟨.inl (supportEndpoint p f e), h.symm⟩
    have hd : v ≠ Sum.inr (d e.val) := fun h => hv ⟨.inr (supportEndpoint d f e), h.symm⟩
    simp [incidence, hp, hd]

section

variable (p : E → P) (d : E → D) (f : E → ℚ)

def supportKernelExtension :
    LinearMap.ker (boundary (supportEndpoint p f) (supportEndpoint d f)) →ₗ[ℚ]
      LinearMap.ker (boundary p d) where
  toFun a := ⟨supportExtension f a.val, supportExtension_mem_kernel p d f a⟩
  map_add' a b := Subtype.ext ((supportExtension f).map_add a.val b.val)
  map_smul' c a := Subtype.ext ((supportExtension f).map_smul c a.val)

theorem support_card_le_active_vertices
    (hker : Module.finrank ℚ (LinearMap.ker (boundary p d)) ≤ 1)
    (e₀ : E) (he₀ : f e₀ ≠ 0) :
    Fintype.card (SupportEdge f) ≤
      Fintype.card (SupportVertex p f) + Fintype.card (SupportVertex d f) := by
  have hi : Function.Injective (supportKernelExtension p d f) := by
    intro a b hab
    apply Subtype.ext
    exact supportExtension_injective f (congrArg Subtype.val hab)
  have hk := LinearMap.finrank_le_finrank_of_injective hi
  exact card_edges_le_vertices (supportEndpoint p f) (supportEndpoint d f)
    ⟨p e₀, e₀, he₀, rfl⟩ (hk.trans hker)

end

omit [Fintype P] [Fintype D] in
theorem supportRestriction_mem_kernel (p : E → P) (d : E → D) (f : E → ℚ)
    (hf : f ∈ LinearMap.ker (boundary p d)) :
    (fun e : SupportEdge f => f e.val) ∈
      LinearMap.ker (boundary (supportEndpoint p f) (supportEndpoint d f)) := by
  have he : supportExtension f (fun e : SupportEdge f => f e.val) = f := by
    ext e
    by_cases hh : f e = 0 <;> simp [supportExtension, hh]
  ext v
  rw [← boundary_supportExtension_active, he]
  exact congrFun hf _

private theorem two_le_card_zero_sum {X : Type*} (s : Finset X) (a : X → ℚ)
    (hs : s.Nonempty) (ha : ∀ x ∈ s, a x ≠ 0) (hz : ∑ x ∈ s, a x = 0) : 2 ≤ s.card := by
  grind [Finset.card_eq_one.mp]

open scoped Classical in
private theorem support_degree_pos {X : Type*} (p : E → X) (f : E → ℚ) (v : SupportVertex p f)
    (hz : ∑ e with supportEndpoint p f e = v, f e.val = 0) :
    2 ≤ (Finset.univ.filter fun e => supportEndpoint p f e = v).card := by
  refine two_le_card_zero_sum _ (fun e => f e.val) ?_ (fun e _ => e.property) hz
  obtain ⟨e, he, hp⟩ := v.property
  exact ⟨⟨e, he⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext hp⟩⟩

omit [Fintype P] [Fintype D] in
open scoped Classical in
private theorem support_primal_degree_pos (p : E → P) (d : E → D) (f : E → ℚ)
    (hf : f ∈ LinearMap.ker (boundary p d)) (v : SupportVertex p f) :
    2 ≤ (Finset.univ.filter fun e => supportEndpoint p f e = v).card := by
  apply support_degree_pos
  have hz := congrFun (supportRestriction_mem_kernel p d f hf) (.inl v)
  rw [boundary_inl, Pi.zero_apply] at hz
  convert hz using 1; congr 1; ext x; simp

omit [Fintype P] [Fintype D] in
open scoped Classical in
private theorem support_dual_degree_pos (p : E → P) (d : E → D) (f : E → ℚ)
    (hf : f ∈ LinearMap.ker (boundary p d)) (v : SupportVertex d f) :
    2 ≤ (Finset.univ.filter fun e => supportEndpoint d f e = v).card := by
  apply support_degree_pos
  have hz := congrFun (supportRestriction_mem_kernel p d f hf) (.inr v)
  rw [boundary_inr, Pi.zero_apply, neg_eq_zero] at hz
  convert hz using 1; congr 1; ext x; simp

open scoped Classical in
theorem support_primal_degree_le_two (p : E → P) (d : E → D) (f : E → ℚ)
    (hf : f ∈ LinearMap.ker (boundary p d))
    (hker : Module.finrank ℚ (LinearMap.ker (boundary p d)) ≤ 1)
    (v : SupportVertex p f) :
    (Finset.univ.filter fun e : SupportEdge f => supportEndpoint p f e = v).card ≤ 2 := by
  classical
  obtain ⟨e₀, he₀, _⟩ := v.property
  have hc := support_card_le_active_vertices p d f hker e₀ he₀
  have hp :=
    (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
      (f := supportEndpoint p f) (by simp)).symm
  have hd :=
    (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
      (f := supportEndpoint d f) (by simp)).symm
  by_contra hn
  have hsp := Finset.sum_lt_sum (s := Finset.univ)
    (fun u _ => support_primal_degree_pos p d f hf u) ⟨v, Finset.mem_univ _, by omega⟩
  have hsd := Finset.sum_le_sum (s := Finset.univ)
    (fun u _ => support_dual_degree_pos p d f hf u)
  rw [hp] at hsp
  rw [hd] at hsd
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsp hsd
  omega

open scoped Classical in
/-- At most two edges of a nonzero circulation can be incident to any primal
vertex if the entire circulation space has dimension at most one. -/
theorem primal_support_degree_le_two (p : E → P) (d : E → D) (f : E → ℚ)
    (hf : f ∈ LinearMap.ker (boundary p d))
    (hker : Module.finrank ℚ (LinearMap.ker (boundary p d)) ≤ 1) (v : P) :
    (Finset.univ.filter fun e => f e ≠ 0 ∧ p e = v).card ≤ 2 := by
  classical
  by_cases hv : ∃ e, f e ≠ 0 ∧ p e = v
  · have hh := support_primal_degree_le_two p d f hf hker ⟨v, hv⟩
    have he : (Finset.univ.filter fun e => f e ≠ 0 ∧ p e = v).card =
        (Finset.univ.filter fun e : SupportEdge f =>
          supportEndpoint p f e = ⟨v, hv⟩).card := by
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      exact (Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun e => f e ≠ 0) (fun e => p e = v))).symm.trans (Fintype.card_congr
          (Equiv.subtypeEquivRight fun e => by simp [supportEndpoint]))
    omega
  · have he : (Finset.univ.filter fun e => f e ≠ 0 ∧ p e = v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      grind
    grind

end
end PottsDiscontinuity.TorusLoops.Bipartite
