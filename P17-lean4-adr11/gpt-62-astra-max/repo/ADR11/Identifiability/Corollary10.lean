module

public import ADR11.MSC.MultiSample
public import ADR11.Nonbinary.Theorem9

@[expose] public section

namespace ADR11.Challenge

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The fibre of `Sigma.fst` over `x` in `Σ x, Fin (n x)` has `n x` elements. -/
theorem c10_card_filter_sigma_fst (n : X → ℕ) (x : X) :
    #(univ.filter fun p : (Σ y, Fin (n y)) => p.1 = x) = n x := by
  rw [← univ_sigma_univ,filter_sigma,card_sigma]; simp [filter_const,apply_ite]

variable (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X)
include hℓ hcond
local notation "equalSamples" => σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
  σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)

theorem proposition11_corollary10 (h : equalSamples) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := by
  let s : (Σ x, Fin (ℓ x)) → X := Sigma.fst
  have hs : Function.Surjective s := fun x => ⟨⟨x,⟨0,hℓ x⟩⟩,rfl⟩
  have lower (T : Finset X) (ht : ∀ x ∈ T, 2 ≤ ℓ x) : Fintype.card X + #T ≤ Fintype.card (Σ x, Fin (ℓ x)) := by
    rw [Fintype.card_sigma]; simp only [Fintype.card_fin]
    calc _ = ∑ x : X, (1 + if x ∈ T then 1 else 0) := by simp [sum_add_distrib]
         _ ≤ _ := sum_le_sum fun x _ => by split_ifs with hx <;> simp_all [Nat.succ_le_iff]
  have n5 : 5 ≤ Fintype.card (Σ x, Fin (ℓ x)) := by
    rcases hcond with ⟨h4,x,hx⟩ | ⟨h3,x,y,hn,hx,hy⟩
    · have := lower {x} (by simpa); simp_all; omega
    · have := lower {x,y} (by simpa using And.intro hx hy); simp_all
  have he := proposition11_theorem9 n5 (σ.extend hs) (σ'.extend hs) (by simpa [SpeciesTree.extend,SpeciesTree.unrootedDist_pull,s] using h)
  have edge (A) (h2 : 2 ≤ #(pre s A)) (hu : A ≠ univ) : σ.edge A = σ'.edge A := by
    simpa only [SpeciesTree.extend_edge _ hs h2 hu] using SpeciesTree.edge_eq he h2
  refine ⟨SpeciesTree.same_of_edge fun A h2 hu => edge A (h2.trans ?_) hu,?_⟩
  · simpa [image_pre hs] using card_image_le (f := s) (s := pre s A)
  · intro x hx
    have hu : {x} ≠ (univ : Finset X) := by intro e; have := congrArg card e; simp at this; rcases hcond with ⟨h,-⟩ | ⟨h,-⟩ <;> omega
    simpa [SpeciesTree.edge,hu,σ.singleton_mem,σ'.singleton_mem] using edge {x} (by simpa [pre,s,c10_card_filter_sigma_fst] using hx) hu

theorem corollary10 (_ : σ.IsBinary) (_ : σ'.IsBinary) (h : equalSamples) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} :=
  proposition11_corollary10 ℓ hℓ hcond σ σ' h

end ADR11.Challenge
