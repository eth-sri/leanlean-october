module

public import GS.NonmanifoldClosure.TopologicalClosure
public import GS.UnitaryLocalModel.RankCone

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix GS GS.UnitaryLocalModel GS.NonmanifoldObstruction GS.NonmanifoldFinal GS.NonmanifoldClosure
open scoped BigOperators Topology
namespace GS.UnitaryTopology

abbrev RankThreeCone (κ : Type*) [Fintype κ] := GenRankCone 2 κ
def rankThreeZero {κ : Type*} [Fintype κ] : RankThreeCone κ := ⟨0, by simp⟩

def quaternionContraction {r : ℕ} (W : Matrix (Fin 3) (Fin r × Fin 4) ℝ) :
    Fin r × Fin 4 → ℝ := fun j =>
  ![W 0 (j.1, 0) - W 1 (j.1, 1) - W 2 (j.1, 2),
    W 0 (j.1, 1) + W 1 (j.1, 0) + W 2 (j.1, 3),
    W 0 (j.1, 2) - W 1 (j.1, 3) + W 2 (j.1, 0),
    W 0 (j.1, 3) + W 1 (j.1, 2) - W 2 (j.1, 1)] j.2

def firstRowSection {κ : Type*} [Fintype κ] [DecidableEq κ] (z : κ → ℝ) : RankThreeCone κ :=
  ⟨sphereOuter ![1, 0, 0] z, rank_sphereOuter_le_one _ _⟩

private theorem quaternionContraction_zero_iff {r : ℕ} (W : RankThreeCone (Fin r × Fin 4)) :
    quaternionContraction W.val = 0 ↔ W = rankThreeZero := by
  refine ⟨fun he => ?_, fun h => by subst h; funext ⟨_, a⟩; fin_cases a <;> norm_num [quaternionContraction, rankThreeZero]⟩
  obtain ⟨u, hu, z, hz⟩ := exists_sphereOuter_of_rank_le_one W.val W.property
  have hs : vectorSq (quaternionContraction W.val) = frobSq W.val := by
    rw [← hz, frobSq_sphereOuter hu]
    simp only [vectorSq, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hq : (∑ a : Fin 4, quaternionContraction (sphereOuter u z) (j, a) ^ 2) =
        (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * ∑ a : Fin 4, z (j, a) ^ 2 := by
      norm_num [quaternionContraction, sphereOuter, Fin.sum_univ_succ,
        show (2 : Fin 3).succ = (3 : Fin 4) from rfl]
      ring
    rw [hq, hu, one_mul]
  rw [he] at hs
  exact Subtype.ext ((frobSq_eq_zero_iff W.val).mp (by simpa [vectorSq] using hs.symm))

def quaternionProductRetract (e r : ℕ) :
    IsolatedEuclideanRetract ((Fin e → ℝ) × RankThreeCone (Fin r × Fin 4)) (0, rankThreeZero) (e + r * 4) := by
  have hc : Fintype.card (Fin e ⊕ (Fin r × Fin 4)) = e + r * 4 := by simp
  let eqv : ((Fin e → ℝ) × (Fin r × Fin 4 → ℝ)) ≃ₜ Eucl (e + r * 4) :=
    (sumCoordinates.trans (reindexReal ((Fintype.equivFin _).trans (Equiv.cast (congrArg Fin hc))))).trans
      (EuclideanSpace.equiv (Fin (e + r * 4)) ℝ).symm.toHomeomorph
  have hz0 : eqv (0, 0) = 0 := by ext i; simp [eqv, sumCoordinates, reindexReal]
  have hqc : Continuous (@quaternionContraction r) :=
    continuous_pi fun ⟨_, a⟩ => by fin_cases a <;> simp [quaternionContraction] <;> fun_prop
  have hfs : Continuous (@firstRowSection (Fin r × Fin 4) _ _) := by
    apply Continuous.subtype_mk; unfold sphereOuter; fun_prop
  have hqs (z : Fin r × Fin 4 → ℝ) : quaternionContraction (firstRowSection z).val = z := by
    funext ⟨_, a⟩; fin_cases a <;> norm_num [quaternionContraction, firstRowSection, sphereOuter] <;> rfl
  have hf0 : firstRowSection (0 : Fin r × Fin 4 → ℝ) = rankThreeZero := by
    apply Subtype.ext; ext i j; simp [firstRowSection, sphereOuter, rankThreeZero]
  exact
    { sectionMap := (fun p => (p.1, firstRowSection p.2)) ∘ eqv.symm
      projectionMap := eqv ∘ fun p => (p.1, quaternionContraction p.2.val)
      section_continuous := (continuous_fst.prodMk (hfs.comp continuous_snd)).comp eqv.symm.continuous
      projection_continuous := eqv.continuous.comp
        (continuous_fst.prodMk (hqc.comp (continuous_subtype_val.comp continuous_snd)))
      projection_section := fun x => by simp [Function.comp_apply, hqs]
      section_zero := by
        rw [Function.comp_apply, eqv.symm_apply_eq.mpr hz0.symm]; exact Prod.ext rfl hf0
      projection_zero_iff := fun p => by
        rw [Function.comp_apply, ← hz0, eqv.injective.eq_iff, Prod.ext_iff, quaternionContraction_zero_iff, Prod.ext_iff] }

theorem rankThreeProduct_not_euclidean_of_four_dvd (e d : ℕ) (hd : 0 < d) (hdiv : 4 ∣ d) :
    ¬ EuclideanAt ((0, rankThreeZero) : (Fin e → ℝ) × RankThreeCone (Fin d)) := by
  obtain ⟨r, hr⟩ := hdiv
  have hd' : d = r * 4 := by omega
  have hrpos : 0 < r := by omega
  subst hd'
  have hblk : ¬ EuclideanAt ((0, rankThreeZero) : (Fin e → ℝ) × RankThreeCone (Fin r × Fin 4)) := by
    refine not_euclidean_of_retract_regular_charts (quaternionProductRetract e r)
      (Fintype.card (Fin e) + Fintype.card (Fin r × Fin 4) + 2) (by simp) fun U hU h0 => ?_
    let j : Fin r × Fin 4 := (⟨0, hrpos⟩, 0)
    obtain ⟨p, hp, hpc⟩ := exists_gen_regular_in_open (ι := Fin e) 2 j U hU h0
    exact ⟨genPivotChart (ι := Fin e) 2 j, p, hp, hpc⟩
  let eqv : Fin r × Fin 4 ≃ Fin (r * 4) := finProdFinEquiv
  let h : ((Fin e → ℝ) × RankThreeCone (Fin r × Fin 4)) ≃ₜ ((Fin e → ℝ) × RankThreeCone (Fin (r * 4))) :=
    (Homeomorph.refl _).prodCongr
      { toFun := fun W => ⟨W.val.reindex (Equiv.refl _) eqv, by simpa only [Matrix.rank_reindex] using W.property⟩
        invFun := fun W => ⟨W.val.reindex (Equiv.refl _) eqv.symm, by simpa only [Matrix.rank_reindex] using W.property⟩
        left_inv := fun W => by apply Subtype.ext; ext i j; simp
        right_inv := fun W => by apply Subtype.ext; ext i j; simp
        continuous_toFun := by
          apply Continuous.subtype_mk; apply continuous_pi; intro i; apply continuous_pi; intro j
          exact (continuous_apply (eqv.symm j)).comp ((continuous_apply i).comp continuous_subtype_val)
        continuous_invFun := by
          apply Continuous.subtype_mk; apply continuous_pi; intro i; apply continuous_pi; intro j
          exact (continuous_apply (eqv j)).comp ((continuous_apply i).comp continuous_subtype_val) }
  have hh0 : h (0, rankThreeZero) = (0, rankThreeZero) := Prod.ext rfl (Subtype.ext rfl)
  intro he
  exact hblk ((euclideanAt_homeomorph h (0, rankThreeZero)).mpr (hh0.symm ▸ he))

end GS.UnitaryTopology
