module

public import ADR11.Nonbinary.FiveTaxa
public import ADR11.FourTaxa

@[expose] public section

namespace ADR11.Challenge

open ADR11 Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

set_option quotPrecheck false
local notation "T4" σ:max a:max b:max =>
  SpeciesTree.unrootedDist σ id {a, b, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}}
local notation "Q4" σ:max L:max =>
  T4 σ {0, 1} {2, 3} = 1 - 2 / 3 * exp (-L) ∧
  T4 σ {0, 2} {1, 3} = 1 / 3 * exp (-L) ∧
  T4 σ {0, 3} {1, 2} = 1 / 3 * exp (-L)
local notation "Goal9" σ:max σ':max =>
  SpeciesTree.unrootedDist σ id = SpeciesTree.unrootedDist σ' id →
    SpeciesTree.SameRootedMetricTree σ σ'
local notation "Goal9_4" σ:max σ':max =>
  SpeciesTree.unrootedDist σ id = SpeciesTree.unrootedDist σ' id ↔
    SpeciesTree.SameUnrootedMetricTree σ σ'
local notation "Cond10" X:max ℓ:max =>
  (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
    (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y)
local notation "Goal10" ℓ:max σ:max σ':max =>
  SpeciesTree.unrootedDist σ (Sigma.fst : (Σ x, Fin (ℓ x)) → _) =
    SpeciesTree.unrootedDist σ' (Sigma.fst : (Σ x, Fin (ℓ x)) → _) →
  SpeciesTree.SameRootedMetricTree σ σ' ∧
    ∀ x, 2 ≤ ℓ x → SpeciesTree.length σ {x} = SpeciesTree.length σ' {x}

theorem unrootedDist_nonneg {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) (T : Finset (Finset L)) : 0 ≤ σ.unrootedDist s T :=
  ADR11.unrootedDist_nonneg σ s T

theorem unrootedDist_sum {L : Type*} [Fintype L] [DecidableEq L] (σ : SpeciesTree X)
    (s : L → X) : ∑ T, σ.unrootedDist s T = 1 :=
  ADR11.unrootedDist_sum σ s

theorem fourTaxa_balanced (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {2, 3}, {0}, {1}, {2}, {3}}) :
    Q4 σ (σ.length {0, 1} + σ.length {2, 3}) := by
  convert ADR11.fourTaxa_balanced σ (hσ.trans (by decide)) using 4 <;> decide

theorem fourTaxa_caterpillar (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {0, 1, 2}, {0}, {1}, {2}, {3}}) :
    Q4 σ (σ.length {0, 1}) := by
  convert ADR11.fourTaxa_caterpillar σ (hσ.trans (by decide)) using 4 <;> decide

theorem appC_sameRootedMetricTree (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  have hU := sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U5 hX σ
  have he' : unroot (σ'.relabel e.symm).clusters = U5 k := by
    rw [SpeciesTree.relabel_clusters, unroot_relabelFamily, ← hU.1, ← unroot_relabelFamily]
    exact he
  have hd := (SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e.symm).2 h
  rw [← SpeciesTree.sameRootedMetricTree_relabel_iff σ σ' e.symm]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · obtain ⟨h1, hs⟩ := rootings_zero_main he
    exact hs _ (by rw [← h1, ← (rootings_zero_main he').1]; unfold tag0 u; rw [hd]) hd
  · obtain ⟨h1, hs⟩ := rootings_one_main he
    exact hs _ (by rw [← h1, ← (rootings_one_main he').1]; unfold tag1 linVal u; rw [hd]) hd
  · obtain ⟨h1, hs⟩ := rootings_two_main he
    exact hs _ (by rw [← h1, ← (rootings_two_main he').1]; unfold tag2 linVal u; rw [hd]) hd

theorem proposition11_theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X) :
    Goal9 σ σ' := fun h => by
  have hU := sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h
  have h5 (S : Finset X) (hS : S.Nonempty) (hS5 : #S = 5) :=
    appC_sameRootedMetricTree (by simpa using hS5) _ _ (unrootedDist_restrict_eq h S hS)
  exact rl_sameRootedMetricTree_of_clusters_eq hX
    (rl_eq_of_unroot_eq σ.isHierarchy σ'.isHierarchy hU.1
      (rl_nb_childClusters_univ_eq hX hU.1 fun S hS hS5 => (h5 S hS hS5).1)) hU h5

theorem proposition11_theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) :
    Goal9_4 σ σ' :=
  unrootedDist_eq_iff_four hX σ σ'

theorem proposition11_corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x) (hcond : Cond10 X ℓ)
    (σ σ' : SpeciesTree X) : Goal10 ℓ σ σ' := fun h => by
  let f (z : X) := min (ℓ z) 2
  let keep : (Σ x, Fin (f x)) ↪ (Σ x, Fin (ℓ x)) :=
    ⟨fun p => ⟨p.1, p.2.castLE (min_le_left _ _)⟩, fun ⟨_, _⟩ ⟨_, _⟩ h => by aesop⟩
  set s' : (Σ x, Fin (f x)) → X := Sigma.fst
  have hsurj : Function.Surjective s' := fun x => ⟨⟨x, 0, lt_min (hℓ x) (by omega)⟩, rfl⟩
  have hfib (x) : #(univ.filter fun l => s' l = x) = f x := by
    rw [show (univ.filter fun l => s' l = x) = image (Sigma.mk x) univ by ext ⟨y, i⟩; aesop,
      card_image_of_injective _ sigma_mk_injective, card_univ, Fintype.card_fin]
  have h2 (x) : #(univ.filter fun l => s' l = x) ≤ 2 := hfib x ▸ min_le_right _ _
  have hext : (σ.extend s' hsurj).unrootedDist id = (σ'.extend s' hsurj).unrootedDist id := by
    have e1 (τ : SpeciesTree X) (T) : (τ.extend s' hsurj).unrootedDist id T =
        τ.unrootedDist ((Sigma.fst : (Σ x, Fin (ℓ x)) → X) ∘ keep) T := by
      simp [SpeciesTree.unrootedDist, ← τ.rootedDist_extend hsurj h2]; rfl
    ext T; rw [e1, e1, σ.unrootedDist_comp_embedding, σ'.unrootedDist_comp_embedding, h]
  have h5 : 5 ≤ Fintype.card (Σ x, Fin (f x)) := by
    rw [Fintype.card_sigma]; simp only [Fintype.card_fin]
    have hle (S : Finset X) (hS : ∀ z ∈ S, 2 ≤ ℓ z) : Fintype.card X + #S ≤ ∑ z, f z := by
      simpa [sum_add_distrib, sum_boole] using sum_le_sum fun z (_ : z ∈ univ) =>
        show 1 + (if z ∈ S then 1 else 0) ≤ f z by
          dsimp only [f]; split_ifs with hz <;> [have := hS z hz; skip] <;> have := hℓ z <;> omega
    rcases hcond with ⟨h4, x, hx⟩ | ⟨h3, x, y, hxy, hx, hy⟩
    · have := hle {x} (by simp [hx]); simp at this; omega
    · have := hle {x, y} (by simp [hx, hy]); rw [card_pair hxy] at this; omega
  obtain ⟨hc, hlen⟩ := SpeciesTree.sameRootedMetricTree_of_extend
    (by rcases hcond with ⟨_, -⟩ | ⟨_, -⟩ <;> omega) σ σ' hsurj
    (proposition11_theorem9 h5 _ _ hext)
  exact ⟨hc, fun x hx => hlen x (by rw [hfib]; exact le_min hx le_rfl)⟩

theorem theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (_ : σ.IsBinary)
    (_ : σ'.IsBinary) : Goal9 σ σ' :=
  proposition11_theorem9 hX σ σ'

theorem theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) (_ : σ.IsBinary)
    (_ : σ'.IsBinary) : Goal9_4 σ σ' :=
  proposition11_theorem9_four hX σ σ'

theorem proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
        σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
        σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  let e : Fin 4 ≃ X := (Fintype.equivFinOfCardEq hX).symm
  let σ₁ : SpeciesTree (Fin 4) := ⟨h4 [3, 7], by decide, by decide,
    by decide, by decide, fun _ => 1, fun _ _ _ => one_pos⟩
  let σ₂ : SpeciesTree (Fin 4) := ⟨h4 [3, 11], by decide, by decide,
    by decide, by decide, fun _ => 1, fun _ _ _ => one_pos⟩
  have hflt : ∀ A : Finset (Fin 4), 2 ≤ #A → 2 ≤ #Aᶜ →
      (σ₁.clusters.filter fun C => C ≠ univ ∧ (C = A ∨ C = Aᶜ)) =
        σ₂.clusters.filter fun C => C ≠ univ ∧ (C = A ∨ C = Aᶜ) := by decide
  refine ⟨fun σ σ' _ _ => (unrootedDist_eq_iff_four hX σ σ').1, σ₁.relabel e, σ₂.relabel e,
    σ₁.isBinary_relabel e (show ∀ A ∈ h4 [3, 7], _ by decide),
    σ₂.isBinary_relabel e (show ∀ A ∈ h4 [3, 11], _ by decide),
    (SpeciesTree.unrootedDist_relabel_eq_iff σ₁ σ₂ e).2 ((unrootedDist_eq_iff_four rfl σ₁ σ₂).2
      ⟨by decide, fun A _ h1 h2 => by
        change ∑ C ∈ _, (1 : ℝ) = ∑ C ∈ _, (1 : ℝ); rw [hflt A h1 h2]⟩),
    fun hs => absurd ((SpeciesTree.sameRootedMetricTree_relabel_iff σ₁ σ₂ e).1 hs).1 (by decide)⟩

theorem corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x) (hcond : Cond10 X ℓ)
    (σ σ' : SpeciesTree X) (_ : σ.IsBinary) (_ : σ'.IsBinary) : Goal10 ℓ σ σ' :=
  proposition11_corollary10 ℓ hℓ hcond σ σ'

end ADR11.Challenge

