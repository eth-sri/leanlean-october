/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Terminal

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

open CellScheme.restrictFace (toCell belowMap toCell_strictMono toCell_injective
  exists_toCell_eq scope_toCell_subset image_scope_restrictFace gradedLe_restrictFace_iff
  toCell_cast_eq_of_emb)

universe w

namespace Transform

end Transform

namespace StageType

variable {α : Ordinal.{0}} {k m n : ℕ}

/-- **Composition law**: the cell map of a composite restriction is the composite of the cell
maps (the two strictly monotone enumerations of the `f.trans g`-visible cells agree). -/
theorem mapCell_trans {z : S α n} {y : S α m} {x : S α k} {g : Fin m ↪ Fin n}
    {f : Fin k ↪ Fin m} (hzy : typeMap g z = some y) (hyx : typeMap f y = some x)
    (hzx : typeMap (f.trans g) z = some x) (d : Cell x.scheme.scheme) :
    mapCell hzx d = mapCell hzy (mapCell hyx d) := by
  obtain ⟨hg, rfl⟩ : ∃ hr, z.restrictFace g hr = y :=
    ⟨visible_of_typeMap_eq_some hzy, restrictFace_eq_of_typeMap_eq_some hzy⟩
  obtain ⟨hf, rfl⟩ : ∃ hr, (z.restrictFace g hg).restrictFace f hr = x :=
    ⟨visible_of_typeMap_eq_some hyx, restrictFace_eq_of_typeMap_eq_some hyx⟩
  set D := z.scheme.scheme with hD
  have hvis : Finset.univ.image (f.trans g) ∈ D.plan := visible_of_typeMap_eq_some hzx
  set e : Fin ((D.restrictFace g hg).restrictFace f hf).card → Cell D :=
    fun c => toCell D g hg (toCell (D.restrictFace g hg) f hf c) with he_def
  have he : StrictMono e :=
    (toCell_strictMono D g hg).comp (toCell_strictMono (D.restrictFace g hg) f hf)
  have hvis_e : ∀ c, D.scope (e c) ⊆ Finset.univ.image (f.trans g) := by
    intro c
    have h1 : ((D.restrictFace g hg).scope (toCell (D.restrictFace g hg) f hf c)).image g
        = D.scope (e c) :=
      image_scope_restrictFace D g hg _
    rw [← h1]
    have h2 : (D.restrictFace g hg).scope (toCell (D.restrictFace g hg) f hf c) ⊆
        Finset.univ.image f :=
      scope_toCell_subset (D.restrictFace g hg) f hf _
    calc ((D.restrictFace g hg).scope (toCell (D.restrictFace g hg) f hf c)).image g
        ⊆ (Finset.univ.image f).image g := Finset.image_subset_image h2
      _ = Finset.univ.image (f.trans g) := by
          rw [Finset.image_image]; rfl
  have hcard : (D.restrictFace (f.trans g) hvis).card
      = ((D.restrictFace g hg).restrictFace f hf).card :=
    congrArg (fun w : S α k => w.scheme.scheme.card) (restrictFace_eq_of_typeMap_eq_some hzx)
  have key := toCell_cast_eq_of_emb D (f.trans g) hvis he hvis_e hcard d
  assumption

end StageType

open StageType

end VaughtConjecture.Knight
