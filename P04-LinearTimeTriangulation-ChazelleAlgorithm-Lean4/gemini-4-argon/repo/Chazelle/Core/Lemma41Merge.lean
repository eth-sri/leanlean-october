module

public import Chazelle.Core.Lemma41Ram4

/-!
# WP-J, part 11: the merge contract, named

`MergeMeets s κ F G H X Ok` is the `Meets` statement of `MergeSpec` for one merge program `s`;
`mergeMeets_of` extracts it from `MergeSpec`.
-/

namespace Chazelle.Core.L41

open Machine

@[expose] public section

/-- The precondition of a merge. -/
def MergePre (X : MemCtx) (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c : Config) :
    Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    X.holds P c.nmem (rd c bMerge 9) (c.nreg ALLOC) ∧
    rd c bMerge 5 + fuseLoss ≤ X.cap P c.nmem (rd c bMerge 9) ∧ 4 ≤ rd c bMerge 7 ∧
    rd c bMerge 5 + fuseLoss ≤ rd c bMerge 6 ∧
    JunctionWF P (c.nreg ALLOC) c.nmem (rd c bMerge 0) (rd c bMerge 1) (rd c bMerge 2) ∧
    ∃ Hs J N₁ N₂, JunctionAt c.nmem (rd c bMerge 0) (rd c bMerge 1) (rd c bMerge 2) (Qof P) Hs J ∧
      J.P.Simple ∧ SharedGeneric J ∧
      Ok P (chainModel J.left) ∧ Ok P (chainModel J.right) ∧
      Ok P (chainModel J.whole) ∧ (chainModel J.whole).FullDegLe (Qof P) (rd c bMerge 7) ∧
      NFWithin c.nmem (rd c bMerge 3) (c.nreg ALLOC) N₁ ∧
      NFWithin c.nmem (rd c bMerge 4) (c.nreg ALLOC) N₂ ∧
      (∃ γ₁, γ₁ ≤ rd c bMerge 5 ∧
        IsCanonicalNF (chainModel J.left) (Qof P) N₁ γ₁ (rd c bMerge 7)) ∧
      (∃ γ₂, γ₂ ≤ rd c bMerge 5 ∧
        IsCanonicalNF (chainModel J.right) (Qof P) N₂ γ₂ (rd c bMerge 7))

/-- The postcondition of a merge. -/
def MergePost (P : Polygon) (c c' : Config) : Prop :=
  ∀ Hs J N₁ N₂,
    JunctionAt c.nmem (rd c bMerge 0) (rd c bMerge 1) (rd c bMerge 2) (Qof P) Hs J →
    NFAt c.nmem (rd c bMerge 3) N₁ → NFAt c.nmem (rd c bMerge 4) N₂ →
    ∃ N, c.nreg ALLOC ≤ rd c' bMerge 8 ∧ NFWithin c'.nmem (rd c' bMerge 8) (c'.nreg ALLOC) N ∧
      IsCanonicalNF (chainModel J.whole) (Qof P) N (rd c bMerge 6) (rd c bMerge 7)

/-- The cost of a merge. -/
def mergeCost (κ F G H : ℕ → ℕ) (c : Config) : ℕ :=
  κ (rd c bMerge 7) * (c.nmem (rd c bMerge 3) + c.nmem (rd c bMerge 4) + 1) *
    F (rd c bMerge 5 + fuseLoss) * G (rd c bMerge 5 + fuseLoss) *
    (H (rd c bMerge 5 + fuseLoss) + Nat.clog 2 (c.nmem (rd c bMerge 2 + 2) + 1) + 1)

/-- **One merge program** meets the contract of `MergeSpec`. -/
def MergeMeets (s : Stmt) (κ F G H : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop) : Prop :=
  Meets s (mergeBands ∪ oracleBands) (fun P W c => MergePre X Ok P W c)
    (fun P c c' => MergePost P c c') (fun _ c => mergeCost κ F G H c)

/-- **The merge contract of `MergeSpec`.** -/
theorem mergeMeets_of (hM : MergeSpec) : ∃ (mk : Stmt → Stmt → Stmt) (κ : ℕ → ℕ),
    ∀ (sh cu : Stmt) (Bs Bc : Finset ℕ) (F G H : ℕ → ℕ) (X : MemCtx)
      (Ok : Polygon → Model → Prop), X.CapLocal → X.Halves → (∀ P M, Ok P M → OkModel P M) →
      Monotone F → Monotone G → Monotone H →
      Bs ⊆ oracleBands → Bc ⊆ oracleBands →
      ShooterOK sh Bs F X Ok → CutterOK cu Bc G H X Ok → MergeMeets (mk sh cu) κ F G H X Ok := by
  obtain ⟨mk, κ, h⟩ := hM
  exact ⟨mk, κ, fun sh cu Bs Bc F G H X Ok h1 hh h0 m1 m2 m3 h2 h3 h4 h5 =>
    h sh cu Bs Bc F G H X Ok h1 hh h0 m1 m2 m3 h2 h3 h4 h5⟩

end

end Chazelle.Core.L41
