module
public import ADR11.Computation.Skeleton
public import ADR11.Trees.Metric
public import ADR11.Identifiability.Unrooted

/-! The two possible cherries of the unrooted skeleton are `ab` and `de`.
The five crossing trees (neither cherry present) measure the position of the
root: moving past a triple or a quadruple raises all the probes outside it
relative to the probes inside it.  The gap across each such cut is recovered
from differences of probes; absent cuts have gap zero. -/
@[expose] public section
noncomputable section
namespace ADR11.Skeleton
open Finset Real _root_.ADR11.Computation
open Sparse (mon branch eval branch_pos branch_le)
abbrev Tree := SpeciesTree (Fin 5)

variable {τ ρ : Tree} (S : τ.clusters ∈ shapes) (R : ρ.clusters ∈ shapes)
private def gain (x : ℕ → ℝ) (c : ℕ) := factor c * mon x (stageKey c)
private def gap (x : ℕ → ℝ) (c : ℕ) := gain x c * (1 - x c ^ width c)
private def dot (x : ℕ → ℝ) (a : ℕ → ℤ) := ∑ d ∈ cuts.toFinset, (a d : ℝ) * gap x d
noncomputable def probe (τ : Tree) (i : Fin 5) := τ.unrootedDist id (crossing i)

include S in
private theorem model (i : Fin 5) :
    let x := branch τ
    90 * probe τ i = 6 * mon x baseKey + dot x (tilt i) := by
  have eqn := Sparse.likelihood τ (checked _ S i)
  have term (c) : 90 * eval (branch τ) (terms i c) = tilt i c * gap (branch τ) c := by simp [terms,gap,gain,mon]; ring
  rw [probe,eqn,polynomial,Sparse.eval_cons,map_sum,mul_add,mul_sum]
  simp [dot,term]; ring

private def diff (i j : Fin 5) (c : ℕ) := tilt j c - tilt i c
include S in
private theorem contrast (i j : Fin 5) :
    90 * (probe τ j - probe τ i) = dot (branch τ) (diff i j) := by
  rw [mul_sub,model S,model S,add_sub_add_left_eq_sub]; simp [dot,diff,sub_mul,sum_sub_distrib]

private def axis (c d : ℕ) : ℤ := if d = c then 5 else 0
private abbrev Below (H : Family 5) (a b : ℕ → ℤ) := ∀ d ∈ cuts, decC 5 d ∈ H → a d ≤ b d

/- A single probe difference bounds a given cut gap from above in the
first shape and below in the second. Only active cuts contribute. -/
attribute [-instance] Fintype.decidableForallFintype in
set_option synthInstance.maxSize 4096 in
private theorem bracket : ∀ s ∈ shapes, ∀ r ∈ shapes, ∀ c ∈ cuts, ∃ i j : Fin 5,
    Below s (axis c) (diff i j) ∧ Below r (diff i j) (axis c) := by decide +kernel

private theorem gain_pos (c : ℕ) : 0 < gain (branch τ) c := by
  apply mul_pos (by unfold factor; split <;> norm_num)
  exact Multiset.prod_pos (by simp)

private theorem dot_mono {a b} (ab : Below τ.clusters a b) :
    dot (branch τ) a ≤ dot (branch τ) b := by
  apply sum_le_sum; intro c hc; replace hc := List.mem_toFinset.mp hc
  by_cases hm : decC 5 c ∈ τ.clusters
  · exact mul_le_mul_of_nonneg_right (Int.cast_le.mpr (ab c hc hm)) (mul_nonneg (gain_pos c).le
      (sub_nonneg.mpr (pow_le_one₀ (branch_pos τ c).le (branch_le τ c))))
  · simp [gap,branch,SpeciesTree.edge,hm]

include S R in
private theorem gap_le (hd : probe τ = probe ρ) {c} (hc : c ∈ cuts) : gap (branch τ) c ≤ gap (branch ρ) c := by
  obtain ⟨i,j,lo,hi⟩ := bracket _ S _ R c hc
  have le := dot_mono lo
  rw [← contrast S,hd,contrast R] at le
  simpa [dot,axis,ite_mul,hc] using le.trans (dot_mono hi)

attribute [-instance] Fintype.decidableForallFintype in
set_option synthInstance.maxSize 4096 in
private theorem support : ∀ s ∈ shapes, ∀ A ∈ s, 3 ≤ #A → A ≠ univ →
    ∃ c ∈ cuts, decC 5 c = A := by decide +kernel

include S R in
private theorem same (hd : probe τ = probe ρ) (hu : ∀ A, #A = 2 → τ.unrootedLength A = ρ.unrootedLength A) :
    τ.SameRootedMetricTree ρ := by
  let x := branch τ
  let y := branch ρ
  have splitEq (a b : ℕ) (e : (decC 5 a)ᶜ = decC 5 b) (ha2 : #(decC 5 a) = 2) : x a * x b = y a * y b := by
    simp [x,y,branch,← e,← exp_add,← neg_add,SpeciesTree.edge_add_compl,hu _ ha2]
  have base : mon x baseKey = mon y baseKey := by
    calc _ = (x 3 * x 28) * (x 24 * x 7) := by simp [mon,baseKey]; ring
         _ = (y 3 * y 28) * (y 24 * y 7) := by rw [splitEq 3 28,splitEq 24 7] <;> decide
         _ = _ := by simp [mon,baseKey]; ring
  have matchCut (c : ℕ) (hc : c ∈ cuts) (e : mon x (stageKey c) = mon y (stageKey c)) : x c = y c := by
    have hg := le_antisymm (gap_le S R hd hc) (gap_le R S hd.symm hc)
    have ge : gain x c = gain y c := by simp [gain,e]
    change gain x c * _ = gain y c * _ at hg; rw [ge] at hg
    exact (pow_left_inj₀ (branch_pos τ _).le (branch_pos ρ _).le (by unfold width; split <;> decide)).mp
      (sub_right_injective (mul_left_cancel₀ (gain_pos (τ := ρ) c).ne' hg))
  have t (c) (hc : c ∈ cuts) (ht : triple c) := matchCut c hc (by simpa [stageKey,ht] using base)
  have allCuts (c) (hc : c ∈ cuts) : x c = y c := by
    by_cases ht : triple c; · exact t c hc ht
    apply matchCut c hc
    simp [stageKey,ht,mon,Multiset.map_nsmul,Multiset.prod_nsmul,t 7 (by decide) (by decide),t 28 (by decide) (by decide),show (baseKey.map x).prod = (baseKey.map y).prod from base]
  have big (A : Finset (Fin 5)) (h3 : 3 ≤ #A) (ha : A ≠ univ) : τ.edge A = ρ.edge A := by
    by_cases hex : ∃ c ∈ cuts, decC 5 c = A
    · obtain ⟨c,hc,rfl⟩ := hex
      simpa [x,y,branch] using allCuts c hc
    · have hn H (hs : H ∈ shapes) : A ∉ H := fun hm => hex (support _ hs A hm h3 ha)
      simp [SpeciesTree.edge,hn _ S,hn _ R]
  apply SpeciesTree.same_of_edge
  intro A h2 ha
  by_cases h3 : 3 ≤ #A
  · exact big A h3 ha
  have hb : #Aᶜ = 3 := by rw [card_compl]; simp; omega
  have hb' : Aᶜ ≠ univ := by intro he; simp [he] at hb
  have e := hu A (by omega); rw [← SpeciesTree.edge_add_compl,← SpeciesTree.edge_add_compl] at e
  linarith [big Aᶜ hb.ge hb']

private def cherries (H : Family 5) := (unroot H).filter (#· = 2)
private def label (k l : Fin 5) := (Equiv.swap 2 k).trans (Equiv.swap 3 l)

/- A single relabelling works for every resolution of a given unrooted skeleton. -/
attribute [-instance] Fintype.decidableForallFintype in
set_option synthInstance.maxSize 4096 in
private theorem align : ∀ Q ∈ ((full 5).map cherries).dedup, ∃ k l : Fin 5,
    ∀ H ∈ full 5, cherries H = Q → relabelFamily (label k l) H ∈ shapes := by decide +kernel

private theorem five_fin (σ σ' : Tree) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := by
  obtain ⟨k,l,hk⟩ := align _ (List.mem_dedup.mpr (List.mem_map.mpr ⟨_,full_mem σ,rfl⟩))
  let e := label k l
  have form (μ : Tree) (eqn : cherries μ.clusters = cherries σ.clusters) : (μ.relabel e).clusters ∈ shapes := by
    rw [SpeciesTree.relabel_clusters]; exact hk _ (full_mem μ) eqn
  have eqn : cherries σ'.clusters = cherries σ.clusters := by
    ext A; simp only [cherries,mem_filter,and_congr_left_iff,SpeciesTree.split_pos]; intro h2; rw [splits h A h2]
  have hd := (SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e).2 h
  exact (SpeciesTree.sameRootedMetricTree_relabel_iff _ _ e).mp (same (form σ rfl) (form σ' eqn)
    (by funext; simp [probe,hd]) (splits hd))

end ADR11.Skeleton

namespace ADR11

theorem appC_sameRootedMetricTree {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 5)
    (σ σ' : SpeciesTree X) (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  let e := Fintype.equivFinOfCardEq hX
  exact (SpeciesTree.sameRootedMetricTree_relabel_iff σ σ' e).1
    (Skeleton.five_fin _ _ ((SpeciesTree.unrootedDist_relabel_eq_iff _ _ e).2 h))

end ADR11
