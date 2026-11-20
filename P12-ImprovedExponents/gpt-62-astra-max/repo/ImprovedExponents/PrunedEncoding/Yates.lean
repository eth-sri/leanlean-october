module

public import ImprovedExponents.PrunedEncoding.Card

@[expose] public section

/-!
# Pruned encodings: Yates' algorithm, stage by stage

The encodings `Φ_τ(a) = ∑_u a[u] ∏_ℓ φ_{τ_ℓ}(u_ℓ)` of an array `a` on the left strings of length `L`
are computed one level at a time. Stage `k` holds the array

  `A_k[τ_1 ⋯ τ_k ; u_{k+1} ⋯ u_L] = ∑_{u_1, …, u_k} a[u] ∏_{ℓ ≤ k} φ_{τ_ℓ}(u_ℓ)`,

so that `A_0 = a` and `A_L[τ] = Φ_τ(a)`. Its index is a *mixed string*: terms at the first `k`
levels and left variables at the others. We let all the arrays live on the mixed strings
`Fin L → Term ⊕ LeftVar` (`MixStr L`), an array of stage `k` vanishing outside the strings of that
shape (`IsStage k`).

* `yatesStep ℓ` is the step at level `ℓ`, and `yatesStage a k` is the array after the steps at the
  levels `0, …, k - 1`, starting from `yatesInit a`.
* `yatesStage_eq`: the entries are the partial encodings `mixPhi a s`.
* `yatesStage_final`: the last array holds the encodings `Phi τ a`.
* `yatesStage_eq_zero_of_innerCount`: if `a` vanishes off the strings with exactly `m` inner
  variables, an entry with more than `m` inner variables among its left variables is `0`.
* `yatesStage_succ`, `p0Count_update_le`, `card_phi_ne_zero_le`: an entry of stage `k + 1` is a sum
  of at most three entries of stage `k`, with signs, whose strings have no more symbols `P₀`.
-/

namespace ImprovedExponents

open Finset ThreeSumApsp

/-- A mixed string of length `L`: at each level, a term or a left variable. -/
abbrev MixStr (L : ℕ) : Type := Fin L → Term ⊕ LeftVar

/-- The shape of the indices of stage `k`: terms at the levels below `k`, left variables at the
levels from `k` on. -/
def IsStage {L : ℕ} (k : ℕ) (s : MixStr L) : Prop :=
  ∀ ℓ : Fin L, (ℓ.val < k → (s ℓ).isLeft) ∧ (k ≤ ℓ.val → (s ℓ).isRight)

/-- The shape of stage `k` is decidable. -/
instance {L : ℕ} (k : ℕ) : DecidablePred (IsStage (L := L) k) := fun s =>
  inferInstanceAs
    (Decidable (∀ ℓ : Fin L, (ℓ.val < k → (s ℓ).isLeft) ∧ (k ≤ ℓ.val → (s ℓ).isRight)))

end ImprovedExponents
