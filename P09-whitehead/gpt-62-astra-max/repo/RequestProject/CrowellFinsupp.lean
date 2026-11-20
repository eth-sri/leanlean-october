module

public import RequestProject.FoxFinsupp
public import RequestProject.CoverHomologyOne
public import RequestProject.MagnusKernel

@[expose] public section

/-! The Crowell sequence with finite chains and arbitrary cell-index types. -/

namespace FiniteChains

variable {α : Type*} [DecidableEq α] (N : Subgroup (FreeGroup α)) [N.Normal]

@[simp] theorem coe_coverFoxGradient (w : FreeGroup α) :
    (coverFoxGradient N w) = foxVec N w := rfl

section

variable {v : FreeGroup α} (hv : v ∈ N)
include hv

theorem coverFoxGradient_mul (w : FreeGroup α) :
    coverFoxGradient N (v * w) = coverFoxGradient N v + coverFoxGradient N w := by
  apply Finsupp.ext
  solve_by_elim [foxVec_mul]

theorem coverFoxGradient_inv :
    coverFoxGradient N v⁻¹ = -coverFoxGradient N v := by
  apply Finsupp.ext
  solve_by_elim [foxVec_inv]

theorem coverFoxGradient_zpow (n : ℤ) :
    coverFoxGradient N (v ^ n) = n • coverFoxGradient N v := by
  apply Finsupp.ext
  solve_by_elim [foxVec_zpow]

end

theorem coverFoxGradient_conj {r : FreeGroup α} (hr : r ∈ N) (f : FreeGroup α) :
    coverFoxGradient N (f * r * f⁻¹) = qgrp N f • coverFoxGradient N r := by
  apply Finsupp.ext
  simp_all [proj_grp, foxVec_conj]

@[simp] theorem coverFoxGradient_one : coverFoxGradient N 1 = 0 := by
  simp [coverFoxGradient]

theorem coverFoxGradient_eq_zero_iff {w : FreeGroup α} (hw : w ∈ N) :
    coverFoxGradient N w = 0 ↔ w ∈ ⁅N, N⁆ := by
  rw [← foxVec_eq_zero_iff N hw]
  exact ⟨fun h => congrArg (fun c : α →₀ CoverRing N => (c : α → CoverRing N)) h,
    fun h => Finsupp.ext (congrFun h)⟩

/-- Every finite one-cycle of a cover is the Fox vector of a word in its defining subgroup.
There is no assumption that the set of generators is finite. -/
theorem exists_mem_of_coverFirstBoundary_eq_zero (c : α →₀ CoverRing N)
    (hc : coverFirstBoundary N c = 0) :
    ∃ r ∈ N, c = coverFoxGradient N r := by
  classical
  let a := fun i => liftQ N (c i)
  let b := ∑ i ∈ c.support, a i * (grp (FreeGroup.of i) - 1)
  have hproja : ∀ i, proj N (a i) = c i := fun i => proj_liftQ N _
  have hprojb : proj N b = 0 := by
    rw [map_sum]
    have he : ∑ i ∈ c.support, proj N (a i * (grp (FreeGroup.of i) - 1)) =
        coverFirstBoundary N c := by
      change _ = ∑ i ∈ c.support, c i * (qgrp N _ - 1)
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_mul, map_sub, proj_grp, map_one, hproja]
    rw [he, hc]
  have hfoxb : foxProj N b = c := by
    funext j
    have hterm : ∀ i, foxLin j (a i * (grp (FreeGroup.of i) - 1)) =
        a i * (if j = i then 1 else 0) := by
      intro i
      rw [foxLin_mul, map_sub, aug_grp, map_one, sub_self,
        zero_smul, zero_add, map_sub]
      have h1 : foxLin j 1 = 0 := by
        solve_by_elim [grp_one, foxLin_grp, fox_one]
      simp_all
    change proj N _ = c j
    dsimp only [b]
    rw [map_sum]
    change proj N _ = c j
    simp_rw [hterm]
    by_cases hj : j ∈ c.support
    · simp_all
    · simp_all
  obtain ⟨r, hr, he⟩ := foxProj_mem_foxMod N b hprojb
  refine ⟨r, hr, ?_⟩
  ext <;> simp_all

variable {J : Type*} (ρ : J → FreeGroup α)

@[simp] theorem coverSecondBoundary_single (j : J) (x : CoverRing N) :
    coverSecondBoundary N ρ (Finsupp.single j x) = x • coverFoxGradient N (ρ j) :=
  Finsupp.linearCombination_single _ x j

variable (hρ : ∀ j, ρ j ∈ N)
include hρ

/-- The Fox vector of every consequence of the relators is a finite two-boundary. -/
theorem exists_coverSecondBoundary_of_mem_normalClosure
    {w : FreeGroup α} (hw : w ∈ Subgroup.normalClosure (Set.range ρ)) :
    ∃ c : J →₀ CoverRing N, coverSecondBoundary N ρ c = coverFoxGradient N w := by
  classical
  let T : Subgroup (FreeGroup α) :=
    { carrier := {v | v ∈ N ∧ ∃ c : J →₀ CoverRing N,
        coverSecondBoundary N ρ c = coverFoxGradient N v}
      one_mem' := ⟨N.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro v w ⟨hv, c, hc⟩ ⟨hw, d, hd⟩
        exact ⟨N.mul_mem hv hw, c + d, by
          simp_all [map_add, hc, hd, coverFoxGradient_mul]⟩
      inv_mem' := by
        rintro w ⟨hw, c, hc⟩
        exact ⟨N.inv_mem hw, -c, by simp_all [map_neg, hc, coverFoxGradient_inv]⟩ }
  haveI : T.Normal := by
    constructor
    rintro w ⟨hw, c, hc⟩ f
    refine ⟨Subgroup.Normal.conj_mem ‹N.Normal› w hw f, qgrp N f • c, ?_⟩
    simp_all [map_smul, hc, coverFoxGradient_conj]
  have hrange : Set.range ρ ⊆ T := by
    rintro _ ⟨j, rfl⟩
    exact ⟨hρ j, Finsupp.single j 1, by simp⟩
  exact ((Subgroup.normalClosure_le_normal hrange) hw).2

/-- Every finite two-boundary is the Fox vector of a consequence of the relators. -/
theorem exists_mem_normalClosure_of_coverSecondBoundary
    (c : J →₀ CoverRing N) :
    ∃ w ∈ Subgroup.normalClosure (Set.range ρ),
      coverSecondBoundary N ρ c = coverFoxGradient N w := by
  classical
  have hRle : Subgroup.normalClosure (Set.range ρ) ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    exact hρ j
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | add c d hc hd =>
      obtain ⟨v, hv, he⟩ := hc
      obtain ⟨w, hw, hf⟩ := hd
      exact ⟨v * w, Subgroup.mul_mem _ hv hw, by
        rw [map_add, he, hf, coverFoxGradient_mul N (hRle hv)]⟩
  | single j x =>
      obtain ⟨w, hw, he⟩ := exists_mem_smul_foxVec hRle
        (Subgroup.subset_normalClosure (Set.mem_range_self j)) x
      refine ⟨w, hw, ?_⟩
      rw [coverSecondBoundary_single]
      apply Finsupp.ext
      solve_by_elim

/-- The integral Hurewicz membership calculation for arbitrary presentations. -/
theorem coverFoxGradient_mem_range_iff
    {w : FreeGroup α} (hw : w ∈ N) :
    (∃ c : J →₀ CoverRing N, coverSecondBoundary N ρ c = coverFoxGradient N w) ↔
      w ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆ := by
  have hRle : Subgroup.normalClosure (Set.range ρ) ≤ N := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    exact hρ j
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨r, hr, he⟩ := exists_mem_normalClosure_of_coverSecondBoundary N ρ hρ c
    have hh : coverFoxGradient N (w * r⁻¹) = 0 := by
      rw [coverFoxGradient_mul N hw, coverFoxGradient_inv N (hRle hr), ← hc, ← he]
      exact add_neg_cancel _
    have hw' : w = (w * r⁻¹) * r := by group
    rw [hw']
    exact Subgroup.mul_mem _
      ((le_sup_right : ⁅N, N⁆ ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆) ((coverFoxGradient_eq_zero_iff N (N.mul_mem hw (N.inv_mem (hRle hr)))).mp hh))
      ((le_sup_left : Subgroup.normalClosure (Set.range ρ) ≤
        Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆) hr)
  · intro hw'
    obtain ⟨r, hr, t, ht, he⟩ := Subgroup.mem_sup_of_normal_right.mp hw'
    obtain ⟨c, hc⟩ := exists_coverSecondBoundary_of_mem_normalClosure N ρ hρ hr
    refine ⟨c, ?_⟩
    rw [← he, coverFoxGradient_mul N (hRle hr),
      (coverFoxGradient_eq_zero_iff N (Subgroup.commutator_le_left N N ht)).mpr ht, add_zero] <;> assumption

/-- Perfectness of the quotient covering subgroup gives exactness in degree one,
without any finite-presentation restriction. -/
theorem exists_coverSecondBoundary_preimage
    (hperfect : N ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆)
    (c : α →₀ CoverRing N) (hc : coverFirstBoundary N c = 0) :
    ∃ d : J →₀ CoverRing N, coverSecondBoundary N ρ d = c := by
  obtain ⟨w, hw, rfl⟩ := exists_mem_of_coverFirstBoundary_eq_zero N c hc
  exact (coverFoxGradient_mem_range_iff N ρ hρ hw).mpr (hperfect hw)

end FiniteChains
