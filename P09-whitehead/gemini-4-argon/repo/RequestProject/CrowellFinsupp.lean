module

public import RequestProject.FoxFinsupp
public import RequestProject.CoverHomologyOne
public import RequestProject.MagnusKernel

@[expose] public section

namespace FiniteChains

variable {α : Type*} [DecidableEq α] (N : Subgroup (FreeGroup α)) [N.Normal]

@[simp] theorem coe_coverFoxGradient (w : FreeGroup α) :
    (coverFoxGradient N w : α → CoverRing N) = foxVec N w := rfl

theorem coverFoxGradient_mul {v : FreeGroup α} (hv : v ∈ N) (w : FreeGroup α) :
    coverFoxGradient N (v * w) = coverFoxGradient N v + coverFoxGradient N w :=
  Finsupp.ext (congrFun (foxVec_mul hv w))

theorem coverFoxGradient_inv {v : FreeGroup α} (hv : v ∈ N) :
    coverFoxGradient N v⁻¹ = -coverFoxGradient N v :=
  Finsupp.ext (congrFun (foxVec_inv hv))

theorem coverFoxGradient_zpow {v : FreeGroup α} (hv : v ∈ N) (n : ℤ) :
    coverFoxGradient N (v ^ n) = n • coverFoxGradient N v :=
  Finsupp.ext (congrFun (foxVec_zpow hv n))

theorem coverFoxGradient_conj {r : FreeGroup α} (hr : r ∈ N) (f : FreeGroup α) :
    coverFoxGradient N (f * r * f⁻¹) = qgrp N f • coverFoxGradient N r :=
  Finsupp.ext fun i => by
    change foxVec N (f * r * f⁻¹) i = qgrp N f * foxVec N r i
    simpa only [proj_grp, Pi.smul_apply, smul_eq_mul] using congrFun (foxVec_conj hr f) i

@[simp] theorem coverFoxGradient_one : coverFoxGradient N (1 : FreeGroup α) = 0 := by
  ext i; simp [coverFoxGradient]

theorem coverFoxGradient_eq_zero_iff {w : FreeGroup α} (hw : w ∈ N) :
    coverFoxGradient N w = 0 ↔ w ∈ ⁅N, N⁆ := by
  rw [← foxVec_eq_zero_iff N hw]
  exact ⟨congrArg (fun c : α →₀ CoverRing N => (c : α → CoverRing N)), fun h => Finsupp.ext (congrFun h)⟩

theorem exists_mem_of_coverFirstBoundary_eq_zero (c : α →₀ CoverRing N)
    (hc : coverFirstBoundary N c = 0) :
    ∃ r ∈ N, c = coverFoxGradient N r := by
  classical
  let a (i : α) : FreeGroupRing α := liftQ N (c i)
  let b : FreeGroupRing α := ∑ i ∈ c.support, a i * (grp (FreeGroup.of i) - 1)
  have hproja (i : α) : proj N (a i) = c i := proj_liftQ N (c i)
  have hprojb : proj N b = 0 := by
    change proj N (∑ i ∈ c.support, a i * (grp (FreeGroup.of i) - 1)) = 0
    rw [map_sum]
    have he : ∑ i ∈ c.support, proj N (a i * (grp (FreeGroup.of i) - 1)) =
        coverFirstBoundary N c := by
      change _ = ∑ i ∈ c.support, c i * (qgrp N (FreeGroup.of i) - 1)
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_sub, proj_grp, map_one, hproja]
    rw [he, hc]
  have hfoxb : foxProj N b = (c : α → CoverRing N) := funext fun j => by
    have hterm (i : α) : foxLin j (a i * (grp (FreeGroup.of i) - 1)) =
        a i * (if j = i then 1 else 0) := by
      rw [foxLin_mul, map_sub, aug_grp, map_one, sub_self, zero_smul, zero_add, map_sub,
        show foxLin j (1 : FreeGroupRing α) = 0 by rw [← grp_one, foxLin_grp, fox_one],
        foxLin_grp, fox_of, sub_zero]
    change proj N (foxLin j b) = c j
    dsimp only [b]; rw [map_sum]
    change proj N (∑ i ∈ c.support, foxLin j (a i * (grp (FreeGroup.of i) - 1))) = c j
    simp_rw [hterm]
    by_cases hj : j ∈ c.support
    · simpa [mul_ite, Finset.sum_ite_eq', hj] using hproja j
    · simp [mul_ite, hj, show c j = 0 by simpa using hj]
  obtain ⟨r, hr, he⟩ := foxProj_mem_foxMod N b hprojb
  exact ⟨r, hr, Finsupp.ext (congrFun (hfoxb.symm.trans he))⟩

variable {J : Type*} (ρ : J → FreeGroup α)

@[simp] theorem coverSecondBoundary_single (j : J) (x : CoverRing N) :
    coverSecondBoundary N ρ (Finsupp.single j x) = x • coverFoxGradient N (ρ j) :=
  Finsupp.linearCombination_single _ x j

theorem exists_coverSecondBoundary_of_mem_normalClosure (hρ : ∀ j, ρ j ∈ N)
    {w : FreeGroup α} (hw : w ∈ Subgroup.normalClosure (Set.range ρ)) :
    ∃ c : J →₀ CoverRing N, coverSecondBoundary N ρ c = coverFoxGradient N w := by
  classical
  let T : Subgroup (FreeGroup α) :=
    { carrier := {v | v ∈ N ∧ ∃ c : J →₀ CoverRing N,
        coverSecondBoundary N ρ c = coverFoxGradient N v}
      one_mem' := ⟨N.one_mem, 0, by simp⟩
      mul_mem' := fun ⟨hv, c, hc⟩ ⟨hw, d, hd⟩ =>
        ⟨N.mul_mem hv hw, c + d, by rw [map_add, hc, hd, coverFoxGradient_mul N hv]⟩
      inv_mem' := fun ⟨hw, c, hc⟩ =>
        ⟨N.inv_mem hw, -c, by rw [map_neg, hc, coverFoxGradient_inv N hw]⟩ }
  have : T.Normal := ⟨fun w ⟨hw, c, hc⟩ f =>
    ⟨Subgroup.Normal.conj_mem ‹N.Normal› w hw f, qgrp N f • c, by
      rw [map_smul, hc, coverFoxGradient_conj N hw]⟩⟩
  exact ((Subgroup.normalClosure_le_normal (N := T) (by
    rintro _ ⟨j, rfl⟩
    exact ⟨hρ j, Finsupp.single j 1, by rw [coverSecondBoundary_single, one_smul]⟩)) hw).2

theorem coverFoxGradient_mem_range_iff (hρ : ∀ j, ρ j ∈ N)
    {w : FreeGroup α} (hw : w ∈ N) :
    (∃ c : J →₀ CoverRing N, coverSecondBoundary N ρ c = coverFoxGradient N w) ↔
      w ∈ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆ := by
  have hRle : Subgroup.normalClosure (Set.range ρ) ≤ N :=
    Subgroup.normalClosure_le_normal (by rintro _ ⟨j, rfl⟩; exact hρ j)
  constructor
  · rintro ⟨c, hc⟩
    have hex : ∀ c : J →₀ CoverRing N, ∃ r ∈ Subgroup.normalClosure (Set.range ρ),
        coverSecondBoundary N ρ c = coverFoxGradient N r := by
      classical
      intro c; induction c using Finsupp.induction_linear with
      | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
      | add _ _ hc hd =>
          obtain ⟨v, hv, he⟩ := hc; obtain ⟨w, hw, hf⟩ := hd
          exact ⟨v * w, Subgroup.mul_mem _ hv hw, by
            rw [map_add, he, hf, coverFoxGradient_mul N (hRle hv)]⟩
      | single j x =>
          obtain ⟨w, hw, he⟩ := exists_mem_smul_foxVec hRle
            (Subgroup.subset_normalClosure (Set.mem_range_self j)) x
          exact ⟨w, hw, by rw [coverSecondBoundary_single]; exact Finsupp.ext (congrFun he)⟩
    obtain ⟨r, hr, he⟩ := hex c
    have hm := (coverFoxGradient_eq_zero_iff N (N.mul_mem hw (N.inv_mem (hRle hr)))).mp (by
      rw [coverFoxGradient_mul N hw, coverFoxGradient_inv N (hRle hr), ← hc, ← he]
      exact add_neg_cancel _)
    rw [show w = (w * r⁻¹) * r by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hm) (Subgroup.mem_sup_left hr)
  · intro hw'
    obtain ⟨r, hr, t, ht, he⟩ := Subgroup.mem_sup_of_normal_right.mp hw'
    obtain ⟨c, hc⟩ := exists_coverSecondBoundary_of_mem_normalClosure N ρ hρ hr
    exact ⟨c, by rw [← he, coverFoxGradient_mul N (hRle hr),
      (coverFoxGradient_eq_zero_iff N (Subgroup.commutator_le_left N N ht)).mpr ht, add_zero, hc]⟩

theorem exists_coverSecondBoundary_preimage (hρ : ∀ j, ρ j ∈ N)
    (hperfect : N ≤ Subgroup.normalClosure (Set.range ρ) ⊔ ⁅N, N⁆)
    (c : α →₀ CoverRing N) (hc : coverFirstBoundary N c = 0) :
    ∃ d : J →₀ CoverRing N, coverSecondBoundary N ρ d = c := by
  obtain ⟨w, hw, rfl⟩ := exists_mem_of_coverFirstBoundary_eq_zero N c hc
  exact (coverFoxGradient_mem_range_iff N ρ hρ hw).mpr (hperfect hw)

end FiniteChains
