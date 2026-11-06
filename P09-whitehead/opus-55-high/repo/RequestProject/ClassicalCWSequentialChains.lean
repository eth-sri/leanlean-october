import RequestProject.ClassicalCWCellEmbedding


/-! Compose the actual successive cellular embeddings into the last
stage. Thus the common ambient complex in HasChain is constructed from
the extensions themselves. -/

namespace Whitehead

namespace CWCellEmbedding

variable {K : ℕ → TwoComplex} (f : ∀ i, CWCellEmbedding (K i) (K (i + 1)))

def chain (i j : ℕ) (hij : i ≤ j) :=
  Nat.leRecOn (C := fun k => CWCellEmbedding (K i) (K k)) hij
    (fun {k} e => (f k).comp e) (refl _)

theorem chain_map_self i : (chain f i i le_rfl).map = ContinuousMap.id (K i) := by
  have he : chain f i i le_rfl = refl _ :=
    Nat.leRecOn_self (next := fun {k} e => (f k).comp e) _
  aesop

theorem chain_map_succ_right i j hij :
    (chain f i (j + 1) (Nat.le_trans hij (Nat.le_succ j))).map =
      (f j).map.comp (chain f i j hij).map := by
  have he : chain f i _ (by grind) =
      (f j).comp (chain f i j hij) :=
    Nat.leRecOn_succ (next := fun {k} e => (f k).comp e) hij _
  aesop

theorem chain_map_step i j (hij : i + 1 ≤ j) :
    (chain f i j (Nat.le_trans (Nat.le_succ i) hij)).map =
      (chain f (i + 1) j hij).map.comp (f i).map := by
  induction hij with
  | refl =>
      simp [chain_map_self, chain_map_succ_right f i i le_rfl]
  | @step j hij ih =>
      rw [chain_map_succ_right f i j (by grind),
        chain_map_succ_right f _ j hij, ih]
      rfl

end CWCellEmbedding

theorem hasChain_of_successive_cellEmbeddings {K : ℕ → TwoComplex}
    (f : ∀ i, CWCellEmbedding (K i) (K (i + 1))) n
    (hp : ∀ i, i < n → ∃ x, x ∉ Set.range (f i).map)
    (hk : ∀ i, i < n → KillsPi2 (f i).map)
    finite (hfin : finite = true → FiniteCells (K n)) :
    HasChain (K 0) n finite := by
  let e (i : Fin (n + 1)) :=
    CWCellEmbedding.chain f i.val n (Nat.le_of_lt_succ i.isLt)
  apply hasChain_of_cellEmbeddings (K ·.val) (K n)
    e (fun i => (f i.val).map) ?_ ?_ (by simp_all) finite hfin
  · intro i
    exact (CWCellEmbedding.chain_map_step f i.val n i.isLt).symm
  · intro i
    cases' hp i.val i.isLt with x hx
    refine ⟨x, ?_⟩
    rintro ⟨y, hy⟩
    apply hx
    refine ⟨y, (e i.succ).closedEmbedding.injective ?_⟩
    have hs := congrArg (· y)
      (CWCellEmbedding.chain_map_step f i.val n i.isLt)
    exact hs.symm.trans hy
