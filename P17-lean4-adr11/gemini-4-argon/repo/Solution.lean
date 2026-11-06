module

public import ADR11.Nonbinary.FiveTaxa
public import ADR11.Nonbinary.Theorem9

@[expose] public section

namespace ADR11.Challenge

open ADR11 Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem unrootedDist_nonneg {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) (T : Finset (Finset L)) : 0 ≤ σ.unrootedDist s T := ADR11.unrootedDist_nonneg σ s T

theorem unrootedDist_sum {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) : ∑ T, σ.unrootedDist s T = 1 := ADR11.unrootedDist_sum σ s

private theorem t4_eq (σ : SpeciesTree (Fin 4)) {H : Finset (Finset (Fin 4))} (hσ : σ.clusters = H)
    {S : Finset (Finset (Fin 4))} {L : ℝ} (hL : ∑ C ∈ S, σ.length C = L)
    {U₁ U₂ U₃ : Finset (Finset (Fin 4))}
    (hS : H.filter (fun C => C ≠ univ ∧ (C = {0, 1} ∨ C = ({0, 1} : Finset (Fin 4))ᶜ)) = S := by decide)
    (hU : unroot H = U4 1 ∧ U₁ = treeOfClusters {{0, 1}} ∧ U₂ = treeOfClusters {{0, 2}} ∧
      U₃ = treeOfClusters {{0, 3}} := by decide) :
    σ.unrootedDist id U₁ = 1 - 2 / 3 * exp (-L) ∧
    σ.unrootedDist id U₂ = 1 / 3 * exp (-L) ∧
    σ.unrootedDist id U₃ = 1 / 3 * exp (-L) := by
  have hl : σ.unrootedLength {0, 1} = L := by unfold SpeciesTree.unrootedLength; rw [hσ, hS, hL]
  rw [hU.2.1, hU.2.2.1, hU.2.2.2, ← hl]
  exact n4_U4_one σ (hσ ▸ hU.1)

theorem fourTaxa_balanced (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {2, 3}, {0}, {1}, {2}, {3}}) :
    σ.unrootedDist id {{0, 1}, {2, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 - 2 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id {{0, 2}, {1, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id {{0, 3}, {1, 2}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) :=
  t4_eq σ hσ (sum_pair (by decide))

theorem fourTaxa_caterpillar (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {0, 1, 2}, {0}, {1}, {2}, {3}}) :
    σ.unrootedDist id {{0, 1}, {2, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 - 2 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id {{0, 2}, {1, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id {{0, 3}, {1, 2}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-σ.length {0, 1}) :=
  t4_eq σ hσ (sum_singleton _ _)

theorem proposition11_theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  have hU := sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h
  have h5 : ∀ S : Finset X, ∀ hS : S.Nonempty, #S = 5 →
      (σ.restrict S hS).SameRootedMetricTree (σ'.restrict S hS) := fun S hS hS5 => by
    have hd := unrootedDist_restrict_eq h S hS
    exact appC_sameRootedMetricTree (by simpa using hS5) _ _ hd
      (sameUnrootedMetricTree_of_unrootedDist_eq _ _ hd)
  have hR := rl_nb_childClusters_univ_eq hX hU.1 fun S hS hS5 => (h5 S hS hS5).1
  exact rl_sameRootedMetricTree_of_clusters_eq hX
    (rl_eq_of_unroot_eq σ.isHierarchy σ'.isHierarchy hU.1 hR) hU h5

theorem proposition11_theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' :=
  unrootedDist_eq_iff_four hX σ σ'

theorem proposition11_corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := by
  set s' : (Σ x, Fin (min (ℓ x) 2)) → X := Sigma.fst
  let e : (Σ x, Fin (min (ℓ x) 2)) ↪ (Σ x, Fin (ℓ x)) :=
    ⟨fun p => ⟨p.1, Fin.castLE (min_le_left _ _) p.2⟩, fun ⟨x, i⟩ ⟨y, j⟩ h => by
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 h
      simp only [heq_eq_eq, Fin.castLE_inj] at h; rw [h]⟩
  have hcomp : (Sigma.fst : (Σ x, Fin (ℓ x)) → X) ∘ e = s' := rfl
  have h' : σ.unrootedDist s' = σ'.unrootedDist s' :=
    funext fun T' => by rw [← hcomp, σ.unrootedDist_comp_embedding, σ'.unrootedDist_comp_embedding, h]
  have hsurj : Function.Surjective s' := fun x =>
    ⟨⟨x, ⟨0, lt_min (hℓ x) (by norm_num)⟩⟩, rfl⟩
  have hfib : ∀ x, #(univ.filter fun l => s' l = x) = min (ℓ x) 2 := fun x => by
    have : (univ.filter fun l => s' l = x) =
        (univ : Finset (Fin (min (ℓ x) 2))).map ⟨Sigma.mk x, sigma_mk_injective⟩ := by
      ext ⟨y, i⟩
      simp only [s', mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
      exact ⟨fun h => h ▸ ⟨i, rfl⟩, fun ⟨j, hj⟩ => (Sigma.mk.inj_iff.1 hj).1.symm⟩
    rw [this, card_map, card_univ, Fintype.card_fin]
  have h2 : ∀ x, #(univ.filter fun l => s' l = x) ≤ 2 := fun x => by
    rw [hfib]; exact min_le_right _ _
  have hext : (σ.extend s' hsurj).unrootedDist id = (σ'.extend s' hsurj).unrootedDist id := by
    have e1 : ∀ τ : SpeciesTree X, (τ.extend s' hsurj).unrootedDist id = τ.unrootedDist s' := by
      intro τ; funext T; unfold SpeciesTree.unrootedDist; simp_rw [← τ.rootedDist_extend hsurj h2]
    rw [e1, e1, h']
  have h5 : 5 ≤ Fintype.card (Σ x, Fin (min (ℓ x) 2)) := by
    rw [Fintype.card_sigma]; simp only [Fintype.card_fin]
    have hone : ∀ x, 1 ≤ min (ℓ x) 2 := fun x => le_min (hℓ x) (by norm_num)
    rcases hcond with ⟨h4, x, hx⟩ | ⟨h3, x, y, hxy, hx, hy⟩
    · rw [← sum_erase_add _ _ (mem_univ x), min_eq_right hx]
      have := sum_le_sum fun z (_ : z ∈ univ.erase x) => hone z
      rw [sum_const, card_erase_of_mem (mem_univ x), card_univ, smul_eq_mul, mul_one] at this
      omega
    · have hyx : y ∈ univ.erase x := mem_erase.2 ⟨hxy.symm, mem_univ y⟩
      rw [← sum_erase_add _ _ (mem_univ x), ← sum_erase_add _ _ hyx, min_eq_right hx,
        min_eq_right hy]
      have := sum_le_sum fun z (_ : z ∈ (univ.erase x).erase y) => hone z
      rw [sum_const, card_erase_of_mem hyx, card_erase_of_mem (mem_univ x), card_univ,
        smul_eq_mul, mul_one] at this
      omega
  have hcardX : 2 ≤ Fintype.card X := by rcases hcond with ⟨h4, -⟩ | ⟨h3, -⟩ <;> omega
  obtain ⟨hc, hlen⟩ := SpeciesTree.sameRootedMetricTree_of_extend hcardX σ σ' hsurj
    (proposition11_theorem9 h5 _ _ hext)
  exact ⟨hc, fun x hx => hlen x (by rw [hfib, min_eq_right hx])⟩

theorem theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (_ : σ.IsBinary)
    (_ : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := proposition11_theorem9 hX σ σ' h

theorem theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) (_ : σ.IsBinary)
    (_ : σ'.IsBinary) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' :=
  proposition11_theorem9_four hX σ σ'

theorem proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
        σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
        σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  refine ⟨fun σ σ' _ _ h => (unrootedDist_eq_iff_four hX σ σ').1 h, ?_⟩
  let σ₁ : SpeciesTree (Fin 4) :=
    ⟨hierarchyOf {{0, 1}, {0, 1, 2}}, by decide, by decide, by decide, by decide,
      fun _ => 1, fun _ _ _ => one_pos⟩
  let σ₂ : SpeciesTree (Fin 4) :=
    ⟨hierarchyOf {{0, 1}, {0, 1, 3}}, by decide, by decide, by decide, by decide,
      fun _ => 1, fun _ _ _ => one_pos⟩
  have hsame : σ₁.SameUnrootedMetricTree σ₂ := by
    refine ⟨by decide, fun A _ _ _ => ?_⟩
    unfold SpeciesTree.unrootedLength
    have h1 : σ₁.clusters.filter (fun C => C ≠ univ ∧ (C = A ∨ C = Aᶜ)) =
        σ₂.clusters.filter (fun C => C ≠ univ ∧ (C = A ∨ C = Aᶜ)) := by
      revert A; decide
    rw [h1]
  let e : Fin 4 ≃ X := (Fintype.equivFinOfCardEq hX).symm
  exact ⟨σ₁.relabel e, σ₂.relabel e,
    σ₁.isBinary_relabel e (by unfold SpeciesTree.IsBinary; decide),
    σ₂.isBinary_relabel e (by unfold SpeciesTree.IsBinary; decide),
    (SpeciesTree.unrootedDist_relabel_eq_iff σ₁ σ₂ e).2
      ((unrootedDist_eq_iff_four (Fintype.card_fin 4) σ₁ σ₂).2 hsame),
    fun hs => absurd ((SpeciesTree.sameRootedMetricTree_relabel_iff σ₁ σ₂ e).1 hs).1 (by decide)⟩

theorem corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X) (_ : σ.IsBinary) (_ : σ'.IsBinary)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} :=
  proposition11_corollary10 ℓ hℓ hcond σ σ' h

end ADR11.Challenge
