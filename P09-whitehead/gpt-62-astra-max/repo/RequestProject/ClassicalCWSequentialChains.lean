module

public import RequestProject.ClassicalCWCellEmbedding

@[expose] public section

/-! Compose the actual successive cellular embeddings into the last
stage. Thus the common ambient complex in HasChain is constructed from
the extensions themselves. -/

noncomputable section
namespace Whitehead

namespace CWCellEmbedding

variable {K : ℕ → TwoComplex} (f : ∀ i, CWCellEmbedding (K i) (K (i + 1)))

def chain (i j : ℕ) (hij : i ≤ j) :=
  Nat.leRecOn (C := fun k => CWCellEmbedding (K i) (K k)) hij
    (fun {k} e => (f k).comp e) (refl (K i))

theorem chain_map_self (i : ℕ) : (chain f i i le_rfl).map = ContinuousMap.id (K i) := by
  have he : chain f i i le_rfl = refl _ :=
    Nat.leRecOn_self _
  aesop

variable (i j : ℕ)

theorem chain_map_succ_right (hij : i ≤ j) :
    (chain f i _ (Nat.le_trans hij (Nat.le_succ j))).map =
      (f j).map.comp (chain f i j hij).map := by
  have he : chain f i _ (Nat.le_trans hij (Nat.le_succ j)) =
      (f j).comp _ :=
    Nat.leRecOn_succ hij _
  aesop

theorem chain_map_step (hij : i + 1 ≤ j) :
    (chain f i j (Nat.le_trans (Nat.le_succ i) hij)).map =
      (chain f _ j hij).map.comp (f i).map := by
  induction hij with
  | refl =>
      simp [chain_map_self, chain_map_succ_right]
  | @step j hij ih =>
      rw [chain_map_succ_right f i j (Nat.le_trans (Nat.le_succ i) hij),
        chain_map_succ_right f _ j hij, ih] <;> rfl

end CWCellEmbedding

theorem hasChain_of_successive_cellEmbeddings {K : ℕ → TwoComplex}
    (f : ∀ i, CWCellEmbedding (K i) _) (n : ℕ)
    (hp : ∀ i, i < n → ∃ x : K (i + 1), x ∉ Set.range (f i).map)
    (hk : ∀ i, i < n → KillsPi2 (f i).map)
    (finite : Bool) (hfin : finite = true → FiniteCells (K n)) :
    HasChain (K 0) n finite := by
  let e (i : Fin _) :=
    CWCellEmbedding.chain f i.val n (Nat.le_of_lt_succ i.isLt)
  apply hasChain_of_cellEmbeddings _ _
    e _ ?_ ?_ (fun i => hk i.val i.isLt) finite hfin
  · grind [CWCellEmbedding.chain_map_step]
  · intro i
    obtain ⟨x, hx⟩ := hp i.val i.isLt
    refine ⟨x, ?_⟩
    rintro ⟨y, hy⟩
    apply hx
    refine ⟨y, (e i.succ).closedEmbedding.injective ?_⟩
    have hs := congrArg (fun g : C(K i.val, K n) => g y)
      (CWCellEmbedding.chain_map_step f i.val n i.isLt)
    exact hs.symm.trans hy

end Whitehead
