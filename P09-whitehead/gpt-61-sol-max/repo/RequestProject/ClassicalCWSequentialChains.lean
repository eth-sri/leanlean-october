import Mathlib.Tactic

import RequestProject.ClassicalCWCellEmbedding

/-! Compose the actual successive cellular embeddings into the last
stage. Thus the common ambient complex in HasChain is constructed from
the extensions themselves. -/

noncomputable section
namespace Whitehead.CWCellEmbedding



variable {K : ℕ → TwoComplex} (f : ∀ i, CWCellEmbedding (K i) (K (i + 1)))

variable (i j : ℕ)
def chain  (hij : i ≤ j)  :=
  Nat.leRecOn (C := fun k => CWCellEmbedding (K i) (K k)) hij
    (fun {k} e => (f k).comp e) (refl (K i))

theorem chain_map_self (i : ℕ) : (chain f i i le_rfl).map = ContinuousMap.id (K i) := by
  have he  :=
    Nat.leRecOn_self (next := fun {k} e => (f k).comp e) (refl (K i))
  exact congrArg (fun q : CWCellEmbedding (K i) (K i) => q.map) he

theorem chain_map_succ_right  (hij : i ≤ j) :
    (chain f i (j + 1) (Nat.le_trans hij (Nat.le_succ j))).map =
      (f j).map.comp (chain f i j hij).map := by
  have he : chain f i (j + 1) (Nat.le_trans hij (Nat.le_succ j)) =
      (f j).comp (chain f i j hij) :=
    Nat.leRecOn_succ (next := fun {k} e => (f k).comp e) hij (refl (K i))
  exact congrArg (fun q : CWCellEmbedding (K i) (K (j + 1)) => q.map) he

theorem chain_map_step  (hij : i + 1 ≤ j) :
    (chain f i j (Nat.le_trans (Nat.le_succ i) hij)).map =
      (chain f (i + 1) j hij).map.comp (f i).map := by
  induction hij with
  | refl =>
      simp_all [chain_map_self, chain_map_succ_right]
  | @step j hij ih =>
      rw [chain_map_succ_right f i j (Nat.le_trans (Nat.le_succ i) hij),
        chain_map_succ_right f (i + 1) j hij, ih]
      rfl

end CWCellEmbedding

theorem hasChain_of_successive_cellEmbeddings {K : ℕ → TwoComplex}
    (f : ∀ i, CWCellEmbedding (K i) (K (i + 1))) (n : ℕ)
    (hp : ∀ i, i < n → ∃ x : K (i + 1), x ∉ Set.range (f i).map)
    (hk : ∀ i, i < n → KillsPi2 (f i).map)
    (finite : Bool) (hfin : finite = true → FiniteCells (K n)) :
    HasChain (K 0) n finite := by
  let e (i : Fin (n + 1))  :=
    CWCellEmbedding.chain f i.val n (Nat.le_of_lt_succ i.isLt)
  apply hasChain_of_cellEmbeddings (fun i : Fin (n + 1) => K i.val) (K n)
    e (fun i => (f i.val).map) ?_ ?_ (fun i => hk i.val i.isLt) finite hfin
  · aesop (add simp [CWCellEmbedding.chain_map_step])
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
