/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.BlockStages
public import VaughtConjecture.Knight.Rank
public import VaughtConjecture.Knight.Directedness
public import VaughtConjecture.Knight.ChartLanguage

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w

namespace KnightRealization

/-- Exact parent consistency, `typeMap`-spelled (the tower's `pull` is `typeMap`,
definitionally).  Re-proved from the mainline definition; the original one-liner is
`PartialDensity.lean` on `origin/e7/high-candidate` (PR #194). -/
theorem exactParent_typeMap {γ : LimitStage} {M : Type w} {B : KnightRealization γ M}
    (hB : B.IsExactParentConsistent) {n k : ℕ} (t : Fin n ↪ M) (q : S γ.1 n)
    (f : Fin k ↪ Fin n) (hq : B.eval t = some q) : B.eval (f.trans t) = typeMap f q :=
  hB t q f hq

end KnightRealization

end VaughtConjecture.Knight
