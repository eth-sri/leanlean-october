module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Order.Filter.AtTopBot.Finset

@[expose] public section

noncomputable section
open Filter Topology
namespace DedekindZetaZeroFree.WildRestrictedTruncation
variable {I : Type*} (G : I → Type*) [∀ i, Group (G i)]
  [∀ i, TopologicalSpace (G i)] (K : ∀ i, Subgroup (G i))
local instance : DecidableEq I := Classical.decEq _

abbrev Product := RestrictedProduct G (fun i ↦ (K i : Set (G i))) Filter.cofinite

section

variable (x : Product G K)

def truncate (s : Finset I) : Product G K :=
  ⟨fun i ↦ if i ∈ s then x i else 1, by
    apply Filter.eventually_cofinite.mpr
    apply s.finite_toSet.subset
    intro i hi
    by_contra hn
    apply hi
    change (if i ∈ s then x i else 1) ∈ K i
    rw [ite_eq_right (show i ∉ s from hn)]
    exact (K i).one_mem⟩

theorem tendsto_truncate :
    Tendsto (truncate G K x) atTop (𝓝 x) := by
  let S := {i | x i ∈ K i}
  let f (s : Finset I) :
      RestrictedProduct G (fun i ↦ (K i : Set (G i))) (Filter.principal S) :=
    ⟨truncate G K x s, by
      apply Filter.eventually_principal.mpr
      intro i hi
      change (if i ∈ s then x i else 1) ∈ K i
      split_ifs
      · exact hi
      apply one_mem⟩
  have hf : Tendsto f atTop (𝓝 (⟨x, Filter.eventually_principal.mpr (fun i hi ↦ hi)⟩)) := by
    apply (RestrictedProduct.isEmbedding_coe_of_principal
       ).tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({i} : Finset I)] with s hs
    change x i = (if i ∈ s then x i else 1)
    rw [ite_eq_left (hs (Finset.mem_singleton_self i))]
  exact (RestrictedProduct.continuous_inclusion
     (Filter.le_principal_iff.mpr x.property)).continuousAt.tendsto.comp hf

theorem truncate_insert (s : Finset I) (i : I) (hi : i ∉ s) :
    truncate G K x (insert i s) = RestrictedProduct.mulSingle K i (x i) * truncate G K x s := by
  apply RestrictedProduct.ext
  intro j
  by_cases hj : j = i
  · subst j
    change (if i ∈ insert i s then x i else 1) =
      RestrictedProduct.mulSingle K i (x i) i * (if i ∈ s then x i else 1)
    simp_all
  · change (if j ∈ insert i s then x j else 1) =
      RestrictedProduct.mulSingle K i (x i) j * (if j ∈ s then x j else 1)
    simp_all

end

def word (x : Product G K) : List I → Product G K
  | [] => 1
  | i :: l => RestrictedProduct.mulSingle K i (x i) * word x l

theorem truncate_list (x : Product G K) (l : List I) (hl : l.Nodup) :
    truncate G K x l.toFinset = word G K x l := by
  induction l with
  | nil =>
    rfl
  | cons i l ih =>
    simp at hl
    rw [List.toFinset_cons, truncate_insert G K x l.toFinset i (by simpa using hl.1),
      ih hl.2]
    rfl

end DedekindZetaZeroFree.WildRestrictedTruncation

end
