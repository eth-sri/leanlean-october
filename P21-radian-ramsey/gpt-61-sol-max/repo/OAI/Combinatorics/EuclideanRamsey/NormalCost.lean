/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/NormalCost.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.ColoringCompactness

@[expose] public section

namespace OAI.EuclideanRamsey


noncomputable section




variable {G : Type*} {H : Type*} {X : Type*} [Group G] [Group H] [MulAction H X]

structure NormalCost (L : Subgroup G) where
  cost : G → ℝ
  nonneg : ∀ g,0≤cost g
  one : cost 1=0
  inv : ∀ g∈L,cost g⁻¹=cost g
  conj : ∀ g∈L,∀ k,cost (k*g*k⁻¹)=cost g
  mul : ∀ g∈L,∀ h∈L,cost (g*h)≤cost g+cost h
namespace NormalCost
variable {L : Subgroup G} [L.Normal] (c : NormalCost L)

lemma product_difference {α : Type*} (l : List α) (a b : α → G)
    (B : ℝ) (h : ∀ j∈l,a j*(b j)⁻¹∈L ∧ c.cost (a j*(b j)⁻¹) ≤ B) :
    (l.map a).prod*((l.map b).prod)⁻¹∈L ∧
    c.cost ((l.map a).prod*((l.map b).prod)⁻¹) ≤
      l.length * B := by
  induction l with
  | nil => simp [c.one,L.one_mem]
  | cons j l ih =>
    obtain ⟨hm,hc⟩ := ih (fun k hk => h k (by simp [hk]))
    obtain ⟨hj,hB⟩ := h j (by simp)
    let z := (l.map a).prod*((l.map b).prod)⁻¹
    have he : (a j*(l.map a).prod)*(b j*(l.map b).prod)⁻¹ =
        (a j*z*(a j)⁻¹)*(a j*(b j)⁻¹) := by dsimp [z]; group
    have hz : a j*z*(a j)⁻¹∈L := (inferInstance : L.Normal).conj_mem _ hm _
    simp only [List.map_cons,List.prod_cons,List.length_cons]
    rw [he]
    refine ⟨L.mul_mem hz hj,?_⟩
    exact (c.mul _ hz _ hj).trans (by rw [c.conj z hm]; push_cast; nlinarith)
end NormalCost

def groupList (H : Type*) [Fintype H] : List H := (Finset.univ : Finset H).toList
lemma groupList_mul_perm [Fintype H] (h : H) :
    ((groupList H).map (·*h)).Perm (groupList H) := by
  classical
  apply (List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).map (mul_left_injective h))
    (Finset.nodup_toList _)).mpr
  intro g
  simp
  exact ⟨g*h⁻¹,by group⟩

def orbitAverage [Fintype H] (w : X → G) (x : X) : G :=
  ((groupList H).map (fun h => w (h•x))).prod

end

end OAI.EuclideanRamsey
