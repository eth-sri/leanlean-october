module

public import ADR11.SmallTrees
public import ADR11.MSC.Relabel

/-!
# Classes of five-taxon gene trees

The paper's arguments on five taxa (the proof of Proposition 7, and Appendix C for nonbinary
species trees) read the shape and the labelling of the species tree off the classes of unrooted
gene trees with equal probabilities: the least probable class and the class with the second
smallest probability. This module defines them as functions of the distribution `u τ`
(`u τ i = ℙ_τ(T_i)`), and transports them along relabellings of the taxa ("permuting labels",
l. 319 of the paper).

* `cls_leastClass τ`, `cls_secondClass τ`: the indices `i ∈ [1, 15]` of the gene trees `T_i` of
  least probability and of the second smallest probability.
* `cls_leastClass_congr`, `cls_secondClass_congr`: they depend only on the distribution.
* `cls_u_relabel`: relabelling the taxa by `π` permutes the gene tree probabilities:
  `u (τ.relabel π) j = u τ i` when `π` maps `T_i` to `T_j`.
* `cls_leastClass_relabel`, `cls_secondClass_relabel`: if `π` maps each `T_i` to `T_{p i}` (and
  every `T_j` is such an image), the classes of `τ` are the images under `p` of those of `τ`
  relabelled by `π⁻¹`.
* `cls_idx π`: the permutation of the gene trees induced by `π`; `cls_classes_of`,
  `cls_least_of`: the classes of a relabelled tree, checked by computation.
* `ac1_argmin`, `ac1_least_second`, `ac1_least`, `ac1_cases`: the classes of a distribution
  that takes one value on a set of gene trees and larger values elsewhere.
-/

@[expose] public section

namespace ADR11

open Finset

open scoped Classical in
/-- The least probable class: the indices `i ∈ [1, 15]` of the gene trees `T_i` of least
probability. -/
noncomputable def cls_leastClass (τ : SpeciesTree (Fin 5)) : Finset ℕ :=
  {i ∈ Icc 1 15 | ∀ j ∈ Icc 1 15, u τ i ≤ u τ j}

open scoped Classical in
/-- The class with the second smallest probability: the indices outside the least probable class
whose probability is least among them. -/
noncomputable def cls_secondClass (τ : SpeciesTree (Fin 5)) : Finset ℕ :=
  {i ∈ Icc 1 15 | i ∉ cls_leastClass τ ∧ ∀ j ∈ Icc 1 15, j ∉ cls_leastClass τ → u τ i ≤ u τ j}

theorem cls_u_congr {τ τ' : SpeciesTree (Fin 5)}
    (h : τ.unrootedDist id = τ'.unrootedDist id) (i : ℕ) : u τ i = u τ' i := by
  unfold u
  rw [h]

theorem cls_leastClass_congr {τ τ' : SpeciesTree (Fin 5)}
    (h : τ.unrootedDist id = τ'.unrootedDist id) : cls_leastClass τ = cls_leastClass τ' := by
  ext i
  simp only [cls_leastClass, mem_filter, cls_u_congr h]

theorem cls_secondClass_congr {τ τ' : SpeciesTree (Fin 5)}
    (h : τ.unrootedDist id = τ'.unrootedDist id) : cls_secondClass τ = cls_secondClass τ' := by
  ext i
  simp only [cls_secondClass, mem_filter, cls_leastClass_congr h, cls_u_congr h]

/-- Relabelling the taxa permutes the gene tree probabilities: if `π` maps `T_i` to `T_j`, then
`T_j` has the same probability under the relabelled species tree as `T_i` under `τ`. -/
theorem cls_u_relabel (τ : SpeciesTree (Fin 5)) (π : Fin 5 ≃ Fin 5) {i j : ℕ}
    (h : relabelFamily π (T5 i) = T5 j) : u (τ.relabel π) j = u τ i := by
  unfold u
  rw [← h, SpeciesTree.unrootedDist_relabel]

/-! ### Membership in the classes -/

theorem cls_mem_leastClass {τ : SpeciesTree (Fin 5)} {i : ℕ} :
    i ∈ cls_leastClass τ ↔ i ∈ Icc 1 15 ∧ ∀ j ∈ Icc 1 15, u τ i ≤ u τ j := by simp_all [cls_leastClass]

theorem cls_mem_secondClass {τ : SpeciesTree (Fin 5)} {i : ℕ} :
    i ∈ cls_secondClass τ ↔ i ∈ Icc 1 15 ∧ i ∉ cls_leastClass τ ∧
      ∀ j ∈ Icc 1 15, j ∉ cls_leastClass τ → u τ i ≤ u τ j := by norm_num [cls_leastClass, cls_secondClass]

/-! ### Relabelling the taxa permutes the classes -/

section IndexMap

/-! In this section `π` maps each gene tree `T_i` (`i ∈ [1, 15]`) to `T_{p i}`, and every `T_j` is
such an image. -/

variable (τ : SpeciesTree (Fin 5)) (π : Fin 5 ≃ Fin 5) {p : ℕ → ℕ}
  (hp : ∀ i ∈ Icc 1 15, p i ∈ Icc 1 15 ∧ relabelFamily π (T5 i) = T5 (p i))
  (hs : ∀ j ∈ Icc 1 15, ∃ i ∈ Icc 1 15, p i = j)

include hp in
/-- Relabelling back: `T_{p k}` has the same probability under `τ` as `T_k` under `τ` relabelled
by `π⁻¹`. -/
theorem cls_u_index {k : ℕ} (hk : k ∈ Icc 1 15) : u τ (p k) = u (τ.relabel π.symm) k := by
  conv_lhs => rw [← τ.relabel_relabel_symm π.symm, π.symm_symm]
  exact cls_u_relabel _ π (hp k hk).2

include hp hs in
theorem cls_forall_index {R : ℕ → Prop} : (∀ k ∈ Icc 1 15, R k) ↔ ∀ l ∈ Icc 1 15, R (p l) := by grind

include hs in
/-- A class of `τ` is the image under `p` of a class of `τ` relabelled by `π⁻¹` if `T_{p i}` is in
the first iff `T_i` is in the second. -/
theorem cls_image_index {S T : Finset ℕ} (hS : S ⊆ Icc 1 15) (hT : T ⊆ Icc 1 15)
    (h : ∀ i ∈ Icc 1 15, p i ∈ S ↔ i ∈ T) : S = T.image p := by grind

include hp hs in
/-- `T_{p i}` is in the least probable class of `τ` iff `T_i` is in that of `τ` relabelled by
`π⁻¹`. -/
theorem cls_mem_leastClass_relabel_iff {i : ℕ} (hi : i ∈ Icc 1 15) :
    p i ∈ cls_leastClass τ ↔ i ∈ cls_leastClass (τ.relabel π.symm) := by
  rw [cls_mem_leastClass, cls_mem_leastClass, cls_forall_index π hp hs]
  exact and_congr (iff_of_true (hp i hi).1 hi) (forall₂_congr fun l hl => by
    rw [cls_u_index τ π hp hi, cls_u_index τ π hp hl])

include hp hs in
/-- The least probable class of `τ` is the image under `p` of that of `τ` relabelled by `π⁻¹`. -/
theorem cls_leastClass_relabel :
    cls_leastClass τ = (cls_leastClass (τ.relabel π.symm)).image p :=
  cls_image_index hs (fun _ h => (cls_mem_leastClass.1 h).1) (fun _ h => (cls_mem_leastClass.1 h).1) fun _ =>
    cls_mem_leastClass_relabel_iff τ π hp hs

include hp hs in
/-- The class of the second smallest probability of `τ` is the image under `p` of that of `τ`
relabelled by `π⁻¹`. -/
theorem cls_secondClass_relabel :
    cls_secondClass τ = (cls_secondClass (τ.relabel π.symm)).image p :=
  cls_image_index hs (fun _ h => (cls_mem_secondClass.1 h).1) (fun _ h => (cls_mem_secondClass.1 h).1) fun i hi => by
    rw [cls_mem_secondClass, cls_mem_secondClass, cls_forall_index π hp hs,
      cls_mem_leastClass_relabel_iff τ π hp hs hi]
    exact and_congr (iff_of_true (hp i hi).1 hi) (and_congr_right' (forall₂_congr fun l hl => by
      rw [cls_mem_leastClass_relabel_iff τ π hp hs hl, cls_u_index τ π hp hi,
        cls_u_index τ π hp hl]))

end IndexMap

/-- The permutation of the gene trees induced by `π`: the index of the image of `T_i`. -/
def cls_idx (π : Fin 5 ≃ Fin 5) (i : ℕ) : ℕ :=
  ((List.range 16).find? fun j => relabelFamily π (T5 i) = T5 j).getD 0

variable {τ : SpeciesTree (Fin 5)} {H H' : Finset (Finset (Fin 5))} {L S L' S' : Finset ℕ}

/-- Permuting labels: if `τ` is the relabelling by `π` of a tree with clusters `H` whose least
probable class is `L`, then the least probable class of `τ` is the image of `L`. -/
theorem cls_least_of (π : Fin 5 ≃ Fin 5) (h : ∀ {ρ : SpeciesTree (Fin 5)}, ρ.clusters = H → cls_leastClass ρ = L)
    (hτ : τ.clusters = H') (hH : relabelFamily π H = H' := by decide +kernel)
    (hp : ∀ i ∈ Icc 1 15, cls_idx π i ∈ Icc 1 15 ∧ relabelFamily π (T5 i) = T5 (cls_idx π i) := by
      decide +kernel)
    (hs : ∀ j ∈ Icc 1 15, ∃ i ∈ Icc 1 15, cls_idx π i = j := by decide +kernel)
    (hL : L.image (cls_idx π) = L' := by decide +kernel) : cls_leastClass τ = L' := by
  rw [cls_leastClass_relabel τ π hp hs, h (by rw [SpeciesTree.relabel_clusters, hτ, ← hH, relabelFamily_symm]), hL]

/-- Permuting labels: if `τ` is the relabelling by `π` of a tree with clusters `H` whose classes
are `L` and `S`, then the classes of `τ` are the images of `L` and `S`. -/
theorem cls_classes_of (π : Fin 5 ≃ Fin 5)
    (h : ∀ {ρ : SpeciesTree (Fin 5)}, ρ.clusters = H → cls_leastClass ρ = L ∧ cls_secondClass ρ = S)
    (hτ : τ.clusters = H') (hH : relabelFamily π H = H' := by decide +kernel)
    (hp : ∀ i ∈ Icc 1 15, cls_idx π i ∈ Icc 1 15 ∧ relabelFamily π (T5 i) = T5 (cls_idx π i) := by
      decide +kernel)
    (hs : ∀ j ∈ Icc 1 15, ∃ i ∈ Icc 1 15, cls_idx π i = j := by decide +kernel)
    (hL : L.image (cls_idx π) = L' := by decide +kernel)
    (hS : S.image (cls_idx π) = S' := by decide +kernel) :
    cls_leastClass τ = L' ∧ cls_secondClass τ = S' := by
  have hρ := h (ρ := τ.relabel π.symm) (by rw [SpeciesTree.relabel_clusters, hτ, ← hH, relabelFamily_symm])
  rw [cls_leastClass_relabel τ π hp hs, cls_secondClass_relabel τ π hp hs, hρ.1, hρ.2]
  grind

/-! ### The least probable class and the next one -/

/-- If `f` takes the value `v` on a nonempty `S ⊆ I` and larger values on `I \ S`, then `S` is
the set of minimizers of `f` on `I`. -/
theorem ac1_argmin {I S : Finset ℕ} {f : ℕ → ℝ} {d : DecidablePred fun i => ∀ j ∈ I, f i ≤ f j} (v : ℝ)
    (hS : S ⊆ I) (hne : S.Nonempty) (hf : ∀ i ∈ I, if i ∈ S then f i = v else v < f i) :
    {i ∈ I | ∀ j ∈ I, f i ≤ f j} = S := by
  grind

/-- The least probable class `S₁` (value `v`) and the class `S₂` (value `w`) with the second
smallest probability. -/
theorem ac1_least_second {τ : SpeciesTree (Fin 5)} {S₁ S₂ : Finset ℕ} (v w : ℝ)
    (hS : S₁ ⊆ Icc 1 15 ∧ S₁.Nonempty ∧ S₂ ⊆ Icc 1 15 \ S₁ ∧ S₂.Nonempty)
    (hu : ∀ i ∈ Icc 1 15,
      if i ∈ S₁ then u τ i = v else if i ∈ S₂ then v < u τ i ∧ u τ i = w else w < u τ i) :
    cls_leastClass τ = S₁ ∧ cls_secondClass τ = S₂ := by simp [cls_leastClass, cls_secondClass]; grind

/-- The least probable class `S` (value `v`). -/
theorem ac1_least {τ : SpeciesTree (Fin 5)} {S : Finset ℕ} (v : ℝ) (hS : S ⊆ Icc 1 15 ∧ S.Nonempty)
    (hu : ∀ i ∈ Icc 1 15, if i ∈ S then u τ i = v else v < u τ i) : cls_leastClass τ = S :=
  ac1_argmin v hS.1 hS.2 hu

/-- Applies `ac1_least_second` or `ac1_least` and checks each gene tree. -/
macro "ac1_cases " t:term " using " fs:term,* : tactic => `(tactic| (
  refine $t ?_ ?_
  · decide
  intro i hi
  obtain ⟨h1, h2⟩ := mem_Icc.1 hi
  interval_cases i <;> simp [*] <;> (try apply And.intro) <;> linarith only [$fs,*]))

end ADR11
