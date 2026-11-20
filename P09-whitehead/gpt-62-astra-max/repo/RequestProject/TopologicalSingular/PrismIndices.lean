module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularChainMaps

@[expose] public section

/-! # Vertex maps for the standard triangulation of a prism -/

namespace FiniteChains.SingularPrism

open CategoryTheory

def cut (i : ℕ) {m : ℕ} (j : Fin m) : Fin 2 := if j.val ≤ i then 0 else 1

variable {n : ℕ}

variable (i : Fin (n + 1)) (j : Fin (n + 2))

theorem cut_left (h : j ≤ i.castSucc) :
    cut i.succ.val ∘ j.castSucc.succAbove = (cut i.val) := by
  funext k
  simp only [Function.comp_apply, cut, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ] <;> grind

theorem cut_right (h : i.castSucc < j) :
    cut i.castSucc.val ∘ j.succ.succAbove = (cut i.val) := by
  funext k
  have hh : i.val < j.val := h
  have hv : (j.succ.succAbove k).val = if k.val < j.val + 1 then k.val else k.val + 1 := by
    by_cases hk : k.val < j.val + 1
    · simp_all [Fin.succAbove_of_castSucc_lt, if_pos]
    · simp_all [Fin.succAbove_of_le_castSucc, if_neg]
  have he : (j.succ.succAbove k).val ≤ i.val ↔ k.val ≤ i.val := by
    rw [hv]
    split_ifs <;> omega
  simp [Function.comp_apply, cut, Fin.val_castSucc, he]

theorem cut_middle (i : Fin n) :
    cut i.succ.val ∘ i.succ.castSucc.succAbove =
      (cut i.castSucc.val ∘ i.succ.castSucc.succAbove) := by
  funext k
  simp only [Function.comp_apply, cut, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ] <;> grind

variable (n : ℕ)

theorem cut_first :
    cut 0 ∘ (0 : Fin _).succAbove = (fun _ : Fin (n + 1) => 1) := rfl

theorem cut_last :
    cut n ∘ (Fin.last _).succAbove = (fun _ : Fin (n + 1) => 0) := by
  funext k
  simp only [Function.comp_apply, Fin.succAbove_last, cut, Fin.val_castSucc] <;> grind

theorem base_left {n : ℕ} (i : Fin _) (j : Fin (n + 2)) (h : j ≤ i.castSucc) :
    i.succ.predAbove ∘ j.castSucc.succAbove = j.succAbove ∘ i.predAbove := by
  funext k
  exact congrArg (fun f : SimplexCategory.mk _ ⟶ SimplexCategory.mk _ => f k)
    (SimplexCategory.δ_comp_σ_of_le h)

theorem base_right {n : ℕ} (i : Fin _) (j : Fin (n + 2)) (h : i.castSucc < j) :
    i.castSucc.predAbove ∘ j.succ.succAbove = j.succAbove ∘ i.predAbove := by
  funext k
  exact congrArg (fun f : SimplexCategory.mk _ ⟶ SimplexCategory.mk _ => f k)
    (SimplexCategory.δ_comp_σ_of_gt h)

theorem base_same {n : ℕ} (i : Fin (n + 1)) :
    i.predAbove ∘ i.castSucc.succAbove = id := by
  aesop

theorem base_next {n : ℕ} (i : Fin (n + 1)) :
    i.predAbove ∘ i.succ.succAbove = id := by
  funext k
  exact congrArg (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk n => f k)
    (SimplexCategory.δ_comp_σ_succ (i := i))

end FiniteChains.SingularPrism
