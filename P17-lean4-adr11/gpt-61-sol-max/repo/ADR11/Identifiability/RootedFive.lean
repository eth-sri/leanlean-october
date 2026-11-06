module
public import ADR11.Trees.Classify
public import ADR11.Computation.FiveLinear
public import ADR11.Identifiability.FourTaxaAnalysis
public import ADR11.MSC.Marginal
public import ADR11.Identifiability.FiveQuartets
public import ADR11.Rootings.Proofs
@[expose] public section
namespace ADR11.Five
open Finset Real _root_.ADR11.Computation
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable def baseParam (len : Finset (Fin 5) → ℝ) (k j : ℕ) (i : Fin 5) : ℝ :=
  param len k j (i + 1)

theorem dist (k : Fin 3) (j : Fin (6 + 2 * k.val)) (τ : SpeciesTree (Fin 5))
    (hc : τ.clusters = hierarchy k j) (i : Fin 4) :
    90 * τ.unrootedDist id (geneTree i) =
      rowVal k j i (baseParam τ.length k j) (param τ.length k j 6) := by
  rw [root_unrootedDist_eq_evalPoly τ (t := (geneTree i, poly k j i)) (hc.symm ▸ checks k j)
    (List.mem_map.2 ⟨i.val, List.mem_range.2 i.isLt, rfl⟩)]
  unfold evalPoly poly rowVal
  simp only [Multiset.map_coe, Multiset.sum_coe]
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 2
  funext cl
  simp only [← monoVal_nil τ.length]
  change _ = (cl.1 : ℝ) * ((keys k j).map (monoVal τ.length)).getD cl.2 (monoVal τ.length [])
  rw [List.getD_map]
  simp only [Function.comp_apply]
  push_cast
  ring

theorem bounds (k : Fin 3) (j : Fin (6 + 2 * k.val)) (τ : SpeciesTree (Fin 5))
    (hc : τ.clusters = hierarchy k j) :
    rootBounds k j (baseParam τ.length k j) (param τ.length k j 6) := by
  have hp := τ.length_pos
  rw [hc] at hp
  fin_cases k <;> fin_cases j
  all_goals
    norm_num [rootBounds, baseParam, param, keys, aKey, bKey, mixKey, rKey, codes, monoVal, weight,
      exp_lt_exp, exp_lt_one_iff, hierarchy, hierarchyOf, decF, decC, Fin.univ_succ, Nat.testBit] at hp ⊢ <;> grind

theorem unrooted_weights (k : Fin 3) (j : Fin (6 + 2 * k.val)) (τ : SpeciesTree (Fin 5))
    (hc : τ.clusters = hierarchy k j) :
    τ.unrootedLength (decC 5 3) = weight τ.length (aKey k j) ∧
    τ.unrootedLength (decC 5 24) = weight τ.length (bKey k j) := by
  simp only [SpeciesTree.unrootedLength, hc]
  fin_cases k <;> fin_cases j <;> constructor
  all_goals
    conv_lhs => enter [1]; cbv
    simp [aKey, bKey, codes, weight] <;> rfl

theorem same (k : Fin 3) (τ τ' : SpeciesTree (Fin 5))
    (hc : unroot τ.clusters = U5 k) (hc' : unroot τ'.clusters = U5 k)
    (hU : τ.SameUnrootedMetricTree τ') (h : τ.unrootedDist id = τ'.unrootedDist id) :
    τ.SameRootedMetricTree τ' := by
  obtain ⟨j, -, hj⟩ := mem_image.1 ((hierarchies k) ▸ mem_rootings τ hc)
  obtain ⟨j', -, hj'⟩ := mem_image.1 ((hierarchies k) ▸ mem_rootings τ' hc')
  have hw := unrooted_weights k j τ hj.symm
  have hw' := unrooted_weights k j' τ' hj'.symm
  have ha := hw.1.symm.trans ((hU.length_eq (decC 5 3) (by decide) (by decide)).trans hw'.1)
  have hb := hw.2.symm.trans ((hU.length_eq (decC 5 24) (by decide) (by decide)).trans hw'.2)
  have he : baseParam τ.length k j = baseParam τ'.length k j' := by
    ext l
    fin_cases k <;> fin_cases j <;> fin_cases j' <;> fin_cases l <;>
      simp [baseParam, param, keys, monoVal, mixKey, aKey, bKey, codes, weight,
        exp_eq_exp] at ha hb ⊢ <;> linarith
  have hbounds := bounds k j τ hj.symm
  have hbounds' := bounds k j' τ' hj'.symm
  rw [← he] at hbounds'
  have hd (i : Fin 4) :
      rowVal k j i (baseParam τ.length k j) (param τ.length k j 6) =
      rowVal k j' i (baseParam τ.length k j) (param τ'.length k j' 6) := by
    conv_rhs => rw [he]
    rw [← dist k j τ hj.symm i, ← dist k j' τ' hj'.symm i, h]
  obtain ⟨rfl, hr⟩ : j = j' ∧ param τ.length k j 6 = param τ'.length k j' 6 := by
    simp only [Fin.forall_fin_succ] at hd
    clear * - hbounds hbounds' hd
    fin_cases k <;> fin_cases j <;> fin_cases j'
    all_goals
      norm_num [rootBounds, rowVal, coeffs, table] at *
      linarith
  change monoVal τ.length (rKey k j) = monoVal τ'.length (rKey k j) at hr
  rw [monoVal, monoVal, exp_eq_exp, neg_inj] at hr
  refine ⟨hj.symm.trans hj', fun C hC h2 hu => ?_⟩
  have hm : C ∈ decF 5 (codes k j) := by grind [hierarchy, hierarchyOf]
  fin_cases k <;> fin_cases j <;>
    simp [aKey, bKey, rKey, codes, decF, weight] at ha hb hr hm <;> grind

end ADR11.Five
