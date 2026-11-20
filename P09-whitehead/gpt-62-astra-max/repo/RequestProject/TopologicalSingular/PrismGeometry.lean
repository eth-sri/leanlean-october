module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.PrismIndices

@[expose] public section

/-! # Continuous prism simplices and all their face identities -/

namespace FiniteChains.SingularPrism

open Set Topology TopologicalSingular

theorem stdMap_const {m n : ℕ} (b : Fin n) (z : stdSimplex ℝ (Fin m)) :
    stdSimplex.map (fun _ : Fin m => b) z = stdSimplex.vertex b := by
  classical
  apply Subtype.ext
  funext j
  simp only [stdSimplex.map, FunOnFinite.linearMap_apply_apply]
  by_cases h : b = j
  · simp_all
  · simp [h]

variable {n : ℕ}

variable (i : Fin (n + 1))

noncomputable def prismMap : C(Domain (n + 1), unitInterval × Domain n) :=
  ⟨fun z => (stdSimplexHomeomorphUnitInterval (stdSimplex.map (cut i.val) z),
      stdSimplex.map i.predAbove z),
    (stdSimplexHomeomorphUnitInterval.continuous.comp (stdSimplex.continuous_map _)).prodMk
      (stdSimplex.continuous_map _)⟩

variable (j : Fin (n + 2))

theorem prismMap_left (h : j ≤ i.castSucc)
    (z : Domain _) :
    prismMap i.succ (stdSimplex.map j.castSucc.succAbove z) =
      ((prismMap i z).1, stdSimplex.map j.succAbove (prismMap i z).2) := by
  simp only [prismMap, ContinuousMap.coe_mk, stdSimplex.map_comp_apply]
  grind [cut_left, base_left]

theorem prismMap_right (h : i.castSucc < j)
    (z : Domain _) :
    prismMap i.castSucc (stdSimplex.map j.succ.succAbove z) =
      ((prismMap i z).1, stdSimplex.map j.succAbove (prismMap i z).2) := by
  simp only [prismMap, ContinuousMap.coe_mk, stdSimplex.map_comp_apply]
  grind [cut_right, base_right]

theorem prismMap_middle (i : Fin n) (z : Domain n) :
    prismMap i.castSucc (stdSimplex.map i.succ.castSucc.succAbove z) =
      prismMap i.succ (stdSimplex.map i.succ.castSucc.succAbove z) := by
  apply Prod.ext
  · simp only [prismMap, ContinuousMap.coe_mk, stdSimplex.map_comp_apply]
    rw [cut_middle]
  · change stdSimplex.map i.castSucc.predAbove (stdSimplex.map i.succ.castSucc.succAbove z) =
      stdSimplex.map i.succ.predAbove (stdSimplex.map i.succ.castSucc.succAbove z)
    grind [stdSimplex.map_comp_apply, base_next, base_same]

variable (n : ℕ) (z : Domain n)

theorem prismMap_first :
    prismMap 0 (stdSimplex.map (0 : Fin (n + 2)).succAbove z) = (1, z) := by
  apply Prod.ext
  · change stdSimplexHomeomorphUnitInterval
      (stdSimplex.map (cut 0) (stdSimplex.map (0 : Fin (n + 2)).succAbove z)) = 1
    rw [stdSimplex.map_comp_apply, cut_first, stdMap_const]
    exact stdSimplexHomeomorphUnitInterval_one
  · change stdSimplex.map (0 : Fin _).predAbove
      (stdSimplex.map _ z) = z
    rw [stdSimplex.map_comp_apply]
    change stdSimplex.map ((0 : Fin _).predAbove ∘ (0 : Fin _).castSucc.succAbove) z = z
    rw [base_same, stdSimplex.map_id_apply]

theorem prismMap_last :
    prismMap (Fin.last n) (stdSimplex.map (Fin.last (n + 1)).succAbove z) = (0, z) := by
  apply Prod.ext
  · change stdSimplexHomeomorphUnitInterval
      (stdSimplex.map (cut n) (stdSimplex.map (Fin.last (n + 1)).succAbove z)) = 0
    rw [stdSimplex.map_comp_apply, cut_last, stdMap_const]
    exact stdSimplexHomeomorphUnitInterval_zero
  · change stdSimplex.map (Fin.last n).predAbove
      (stdSimplex.map _ z) = z
    grind [stdSimplex.map_comp_apply, base_next, stdSimplex.map_id_apply]

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)

variable {n : ℕ}

noncomputable def simplex (σ : Simplex X n) (i : Fin _) :=
  H.toContinuousMap.comp ⟨fun z => ((prismMap i z).1, σ (prismMap i z).2),
    (prismMap i).continuous.fst.prodMk (σ.continuous.comp (prismMap i).continuous.snd)⟩

variable (σ : Simplex X (n + 1)) (i : Fin (n + 1)) (j : Fin (n + 2))

theorem simplex_left
    (h : j ≤ i.castSucc) :
    face j.castSucc (simplex H σ i.succ) = simplex H (face j σ) i := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap i.succ (stdSimplex.map j.castSucc.succAbove z)).1,
      σ (prismMap i.succ (stdSimplex.map j.castSucc.succAbove z)).2) = _
  rw [prismMap_left i j h]
  rfl

theorem simplex_right
    (h : i.castSucc < j) :
    face j.succ (simplex H σ i.castSucc) = simplex H (face j σ) i := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap i.castSucc (stdSimplex.map j.succ.succAbove z)).1,
      σ (prismMap i.castSucc (stdSimplex.map j.succ.succAbove z)).2) = _
  rw [prismMap_right i j h]
  rfl

theorem simplex_middle (σ : Simplex X n) (i : Fin n) :
    face i.succ.castSucc (simplex H σ i.castSucc) = face i.succ.castSucc (simplex H σ i.succ) := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap i.castSucc (stdSimplex.map i.succ.castSucc.succAbove z)).1,
      σ (prismMap i.castSucc (stdSimplex.map i.succ.castSucc.succAbove z)).2) = _
  rw [prismMap_middle]
  rfl

variable (n : ℕ) (σ : Simplex X n)

theorem simplex_first :
    face 0 (simplex H σ 0) = simplexMap g n σ := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap 0 (stdSimplex.map (0 : Fin (n + 2)).succAbove z)).1,
      σ (prismMap 0 (stdSimplex.map (0 : Fin (n + 2)).succAbove z)).2) = _
  rw [prismMap_first]
  exact H.apply_one _

theorem simplex_last :
    face (Fin.last (n + 1)) (simplex H σ (Fin.last n)) = simplexMap f n σ := by
  apply ContinuousMap.ext
  intro z
  change H ((prismMap (Fin.last n) (stdSimplex.map (Fin.last (n + 1)).succAbove z)).1,
      σ (prismMap (Fin.last n) (stdSimplex.map (Fin.last (n + 1)).succAbove z)).2) = _
  rw [prismMap_last]
  exact H.apply_zero _

end FiniteChains.SingularPrism
