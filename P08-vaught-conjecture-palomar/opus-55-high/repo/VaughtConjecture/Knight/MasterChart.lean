/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FinitePartialState
public import VaughtConjecture.TypeTower.FiniteMaster

/-! # Literal master-chart normal form

An exactly consistent partial realization supported on an evaluated master is
literally its face diagram, including undefined invisible faces. No saturation,
modelhood or nonempty-master assumption is involved.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FixedHeight
open TypeTower KnightRealization
universe w
variable {β : LimitStage} {M : Type w} {N : ℕ}

noncomputable def masterChart (w : Fin N ↪ M) (P : S β.1 N) : KnightRealization β M :=
  (FiniteMaster.mk N w P : FiniteMaster knightTower β M).chart

theorem eq_masterChart {A : KnightRealization β M}
    (hcons : A.IsExactParentConsistent) w (P : S β.1 N)
    (hw : A.eval w = some P) (hmaster : MasteredBy A w) : A = masterChart w P :=
  FiniteMaster.eq_chart (T := knightTower) ⟨N, w, P⟩ hcons hw (fun t ht => hmaster t ht)

end VaughtConjecture.Knight.FixedHeight
