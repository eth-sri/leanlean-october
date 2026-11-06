module
public import Mathlib

public import PottsDiscontinuity.Bethe.AsymptoticBoundary
public import PottsDiscontinuity.Bethe.AsymptoticEndpoint

/-! # Limit of the finite missing-root contribution -/

@[expose] public section

open Set Filter
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

theorem tendsto_offsetBoundarySum {ι : Type*} {l : Filter ι} {Δ : ℝ}
    (hΔ : Δ < -1) (r : ℕ) (N : ι → ℕ) (hr : ∀ i, r ≤ N i / 2)
    (hn : ∀ i, 0 < N i / 2) (p : ∀ i, Fin (N i / 2) → ℝ)
    (hp : ∀ i, p i ∈ S_n (N i / 2)) (d : ι → ℝ) (hd : Tendsto d l (𝓝 0))
    (hdnonneg : ∀ i, 0 ≤ d i)
    (hmesh : ∀ i, ∀ j : Fin (N i / 2 + 1),
      rootPartitionPoint (N i / 2) (p i) (hn i) j.succ -
        rootPartitionPoint (N i / 2) (p i) (hn i) j.castSucc ≤ d i)
    {x : ι → ℝ} {a : ℝ} (hx : Tendsto x l (𝓝 a)) :
    Tendsto (fun i => offsetBoundarySum Δ (N i) r (hr i) (p i) (x i)) l
      (𝓝 ((r : ℝ) / 2 * (theta Δ a (-Real.pi) + theta Δ a Real.pi))) := by
  have hleft (s : ℕ) (hs : s ≤ r) (k : Fin s) :
      Tendsto (fun i => p i ⟨k.val, by have := hr i; omega⟩) l (𝓝 (-Real.pi)) :=
    tendsto_root_at_left_of_mesh (fun i => N i / 2) hn p hp d hd hdnonneg hmesh _ r
       fun i => by change k.val ≤ r; omega 
  have hright (s t : ℕ) (hst : s + t = r) (k : Fin t) :
      Tendsto (fun i => p i ⟨s + (N i / 2 - r) + k.val, by have := hr i; omega⟩) l
        (𝓝 Real.pi) :=
    tendsto_root_at_right_of_mesh (fun i => N i / 2) hn p hp d hd hdnonneg hmesh _ r
       fun i => by grind 
  have hθleft (s : ℕ) (hs : s ≤ r) (k : Fin s) :
      Tendsto (fun i => theta Δ (x i) (p i ⟨k.val, by have := hr i; omega⟩)) l
        (𝓝 (theta Δ a (-Real.pi))) := by
    simpa only [Function.comp_def] using
      (continuous_theta hΔ).continuousAt.tendsto.comp (hx.prodMk_nhds (hleft s hs k))
  have hθright (s t : ℕ) (hst : s + t = r) (k : Fin t) :
      Tendsto (fun i => theta Δ (x i) (p i ⟨s + (N i / 2 - r) + k.val, by have := hr i; omega⟩)) l
        (𝓝 (theta Δ a Real.pi)) := by
    simpa only [Function.comp_def] using
      (continuous_theta hΔ).continuousAt.tendsto.comp (hx.prodMk_nhds (hright s t hst k))
  
  
  
  have hR₁ := tendsto_finsetSum Finset.univ
     fun k _ => hθright (r - r / 2) (r / 2) (by omega) k 
  have ht := ((((tendsto_finsetSum Finset.univ  fun k _ => hθleft (r / 2) (by omega) k ).add (tendsto_finsetSum Finset.univ
                            fun k _ => hθright (r / 2) (r - r / 2) (by omega) k )).add (tendsto_finsetSum Finset.univ  fun k _ => hθleft (r - r / 2) (by omega) k )).add hR₁).div_const 2
  have hr' :  (r / 2 : ℕ)  +  (r - r / 2 : ℕ)  = (r : ℝ) := by
    exact_mod_cast  by omega 
  convert ht using 1
  · rfl
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    grind

end PottsDiscontinuity.Bethe
