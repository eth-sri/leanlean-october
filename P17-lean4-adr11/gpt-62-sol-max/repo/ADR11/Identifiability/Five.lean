module

public import ADR11.Identifiability.FiveWeights

@[expose] public section

namespace ADR11
open Finset Real _root_.ADR11.Computation

private abbrev inactiveAt (H : For 5) (i : Fin 5) :=
  decC 5 (groupCode i) ∉ H ∧ decC 5 (pendantCode i) ∉ H

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem common_inactive : ∀ cs ∈ fiveRootings, ∀ ds ∈ fiveRootings, ∃ i : Fin 5,
    inactiveAt (codedHierarchy 5 cs) i ∧ inactiveAt (codedHierarchy 5 ds) i := by rw [rootings_literal.2]; decide +kernel

private theorem pendant_proper (i : Fin 5) : decC 5 (pendantCode i) ≠ univ :=
  (by decide : ∀ i : Fin 5, decC 5 (pendantCode i) ≠ univ) i

private theorem inactive (τ : TreeOn 5) (i : Fin 5) (hi : inactiveAt τ.clusters i) :
    rootWeight τ i = 0 := by
  simp [rootWeight, groupFactor, e5, edgeFactor, hi.1, hi.2]

private theorem min_weight (τ : TreeOn 5) {i j : Fin 5} (hn : i ≠ j)
    (hg : groupFactor τ i = groupFactor τ j) :
    min (rootWeight τ i) (rootWeight τ j) = 3 * (1 - groupFactor τ i ^ 2) := by
  have bound (k : Fin 5) : 0 ≤ groupFactor τ i ^ 2 * (1 - e5 τ (pendantCode k) ^ 6) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.2 (pow_le_one₀ (exp_pos _).le
      (edgeFactor_le_one τ (pendant_proper k))))
  have hp : e5 τ (pendantCode i) = 1 ∨ e5 τ (pendantCode j) = 1 := by
    simp only [e5, edgeFactor_eq_one_iff τ (pendant_proper _)]
    by_contra! h
    exact (by decide : ∀ i j : Fin 5, i ≠ j → ¬ compatibleCodes 5 (pendantCode i) (pendantCode j))
      i j hn (τ.laminar _ h.1 _ h.2)
  unfold rootWeight
  rw [← hg, min_add_add_left]
  rcases hp with h | h <;> simp [h, min_eq_left (bound j), min_eq_right (bound i)]

/-- Rooted identifiability among the rootings of a fixed labelled five-leaf unrooted tree. -/
theorem identify_normal_five (τ τ' : TreeOn 5) {k : Fin 3}
    (hu : unroot τ.clusters = U5 k) (hu' : unroot τ'.clusters = U5 k)
    (hx : x5 τ = x5 τ') (hy : y5 τ = y5 τ') (h : τ.unrootedDist id = τ'.unrootedDist id) :
    τ.SameRootedMetricTree τ' := by
  obtain ⟨cs, hm, hτ⟩ := exists_rootCode5 τ hu
  obtain ⟨cs', hm', hτ'⟩ := exists_rootCode5 τ' hu'
  have hw : rootWeight τ = rootWeight τ' := by
    have he : x5 τ' * y5 τ' / 90 ≠ 0 := by unfold x5 y5; positivity
    have hd (i : Fin 5) : 5 * rootWeight τ i - weightSum (rootWeight τ) =
        5 * rootWeight τ' i - weightSum (rootWeight τ') := by
      have H := congrFun h (readingTree i)
      rw [five_reading τ hm hτ, five_reading τ' hm' hτ', hx, hy] at H
      exact mul_left_cancel₀ he (add_left_cancel H)
    obtain ⟨i, h₁, h₂⟩ := common_inactive cs hm cs' hm'
    have H := hd i
    rw [inactive τ i (hτ ▸ h₁), inactive τ' i (hτ' ▸ h₂)] at H
    funext j
    linarith [hd j]
  have hf : ∀ A ∈ informativeCodes.toFinset.image (decC 5), edgeFactor τ A = edgeFactor τ' A := by
    have pos (τ : TreeOn 5) (c) : 0 < e5 τ c := exp_pos _
    have hp (σ : TreeOn 5) (i : Fin 5) : 0 < groupFactor σ i := pos _ _
    have group (i j : Fin 5) (hn : i ≠ j) (hg : ∀ σ, groupFactor σ i = groupFactor σ j) :
        groupFactor τ i = groupFactor τ' i := by
      have a := min_weight τ hn (hg τ)
      rw [hw, min_weight τ' hn (hg τ')] at a
      exact (pow_left_inj₀ (hp τ i).le (hp τ' i).le (by decide : 2 ≠ 0)).1 (by linarith)
    have hA : e5 τ 28 = e5 τ' 28 := group 0 1 (by decide) (fun _ => rfl)
    have hD : e5 τ 7 = e5 τ' 7 := group 3 4 (by decide) (fun _ => rfl)
    simp only [x5_edges, hA] at hx
    simp only [y5_edges, hD] at hy
    have h3 := mul_right_cancel₀ (pos τ' 28).ne' hx
    have h24 := mul_right_cancel₀ (pos τ' 7).ne' hy
    have P (i : Fin 5) : e5 τ (pendantCode i) = e5 τ' (pendantCode i) := by
      have he : groupFactor τ i = groupFactor τ' i := by
        unfold groupFactor groupCode
        have h0 (σ : TreeOn 5) : e5 σ 0 = 1 := by
          have := σ.nonempty_of_mem ∅
          simp [e5, edgeFactor, show decC 5 0 = ∅ by decide, show ∅ ∉ σ.clusters by grind]
        split_ifs <;> simp only [hA, hD, h0]
      have H := congrFun hw i
      unfold rootWeight at H
      rw [he] at H
      have e := mul_left_cancel₀ (pow_ne_zero 2 (hp τ' i).ne') (add_left_cancel H)
      exact (pow_left_inj₀ (pos τ _).le (pos τ' _).le (by decide : 6 ≠ 0)).1 (by linarith)
    intro A hA
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hA
    simp [informativeCodes] at hc
    rcases hc with rfl | rfl | rfl | rfl | ⟨i, rfl⟩ <;> first | assumption | exact P i
  have hI := internal_mem_codes τ hu
  have hI' := internal_mem_codes τ' hu'
  have hc : internalClusters τ = internalClusters τ' := by
    ext A
    have h (ρ : TreeOn 5) (hu : A ≠ univ) := edgeFactor_lt_one_iff ρ hu
    grind [internalClusters]
  have he : τ.clusters = τ'.clusters := by simpa using congrArg hierarchyOf hc
  refine ⟨he, fun A hA h2 hu => ?_⟩
  simpa [edgeFactor, hA, he ▸ hA, exp_eq_exp] using hf _ (hI (mem_filter.2 ⟨hA, h2, hu⟩))

end ADR11
