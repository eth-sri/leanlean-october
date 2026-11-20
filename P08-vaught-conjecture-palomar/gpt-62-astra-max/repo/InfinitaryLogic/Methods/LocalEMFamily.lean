/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Methods.LocalColimit
public import InfinitaryLogic.Methods.LocalEMSupport
public import Mathlib.ModelTheory.Encoding

/-!
# The countable local atom/deForm family `ΓEMlocal`

The size bottleneck of the EM re-base, resolved. The EM term model's `EMContext` needs a
tail-indiscernible family `Γ` containing every de-substituted atom (`atom_mem`/`rel_mem`) and the
deForms of the truth-lemma family (`DeFormClosedForGammaStar`); the tail extraction
(`MorleyHanfExtractionTail`) delivers indiscernibility only over a **countable** `Γ`. Over
`skolemColim L` the atom diagram is uncountable and the context cannot be instantiated; this file
builds the countable replacement over `localColim s₀`.

**The factoring insight**: a de-substituted atom/deForm over a support `S : Finset J` depends on
its `Λ[[J]]`-terms only *through* their de-substitutions to `Fin S.card`-variable `Λ`-terms. So
the family of ALL such formulas — over EVERY linear order `J`, every support, every closed term —
factors through the **canonical (J-free) seeds** indexed by `Σ m, Λ.Term (Fin m)`-data, which are
countable whenever `Λ` is. Concretely, the local `locDeEqAtom`/`locDeRelAtom`/`locDeForm` are
*defined* as canonical seeds applied to `locDeTermFin`-images, so factoring is definitional and
membership in the canonical seeds is by construction.

Contents:
* Canonical seeds over any `Λ : Language.{0,0}`: `canonEqAtom(s)`, `canonRelAtom(s)`,
  `canonDeForm(s)` + countability (`canonEqAtoms_countable` etc.) from countable symbol types.
* The `J`-side de-substitution pipeline over any `Λ` (mirroring the `skolemColim`-specific chain
  in `EMTermModel.lean`; the generic pieces `deepRank`/`Term.varFinset_relabel` live in the
  shared `LocalEMSupport.lean`): `locJConstOf`, `locJSupport`, `locDeTermPos`, `locDeTermFin`,
  and the local atoms/deForm `locDeEqAtom`/`locDeRelAtom`/`locDeForm` with membership in the
  canonical seeds.
* The assembled family `ΓEMlocal s₀ = ΓlocalColim ∪ eq-atoms ∪ rel-atoms ∪ deForms(ΓlocalColim)`
  over `localColim s₀`, with `ΓEMlocal_countable`, the membership interface the future local
  `EMContext` instantiation will discharge (`locDeEqAtom_mem_ΓEMlocal` = `atom_mem`,
  `locDeRelAtom_mem_ΓEMlocal` = `rel_mem`, `locDeForm_mem_ΓEMlocal` = the deForm closure), and
  the enumeration `exists_ΓEMlocalEnum` in the exact shape the tail extraction consumes.

The GENERIC semantic (realize) bridges live in `LocalEMContext.lean`; the old
`skolemColim`-specific ones remain in `EMTermModel.lean`. This file is deliberately purely
syntactic.
-/

@[expose] public section

namespace FirstOrder.Language

/-! ### Canonical (J-free) seeds over a countable language -/

variable (Λ : Language.{0, 0})

/-- The **canonical equality atom** of two `Fin m`-variable terms: the arity-`m` formula
`t = u` with the variables rebound. Every de-substituted equality atom (over any `J`, any
support) is definitionally of this shape. -/
def canonEqAtom {m : ℕ} (t u : Λ.Term (Fin m)) : Λ.BoundedFormulaω Empty m :=
  BoundedFormulaω.equal (t.relabel Sum.inr) (u.relabel Sum.inr)

/-- The **canonical relation atom**: a relation symbol applied to rebound `Fin m`-variable
terms. -/
def canonRelAtom {m l : ℕ} (R : Λ.Relations l) (ts : Fin l → Λ.Term (Fin m)) :
    Λ.BoundedFormulaω Empty m :=
  BoundedFormulaω.rel R fun i => (ts i).relabel Sum.inr

/-! ### The `J`-side de-substitution pipeline

Mirrors the `skolemColim`-specific chain of `EMTermModel.lean` over an arbitrary `Λ` (the generic
pieces `deepRank`, `deepRank_lt_card`, `Term.varFinset_relabel` live in the shared
`LocalEMSupport.lean`). The `loc` prefix disambiguates from the `skolemColim` versions. -/

variable (J : Type) [LinearOrder J]

/-- The `J`-constant carried by a function symbol of `Λ[[J]]`: only an arity-`0` symbol from the
`constantsOn J` summand is a skeleton constant. -/
def locJConstOf : {n : ℕ} → Λ[[J]].Functions n → Finset J
  | 0, Sum.inr j => {j}
  | _, _ => ∅

/-- The finite set of `J`-constants (skeleton constants) mentioned in a `Λ[[J]]`-term. -/
def locJSupport {α : Type} : Λ[[J]].Term α → Finset J
  | .var _ => ∅
  | .func f ts => (Finset.univ.biUnion fun i => locJSupport (ts i)) ∪ locJConstOf Λ J f

/-- The de-substituted term `constantsToVars t` uses only the variables `Sum.inl j` for `j` a
skeleton constant of `t`. -/
theorem locConstantsToVars_varFinset_subset (t : Λ[[J]].Term Empty) :
    t.constantsToVars.varFinset ⊆ (locJSupport Λ J t).image Sum.inl := by
  induction t with
  | var e => exact e.elim
  | @func l f ts ih =>
    rcases l with _ | l
    · rcases f with f' | c
      · simp [Term.constantsToVars, Term.varFinset]
      · simp only [Term.constantsToVars, locJSupport, locJConstOf, Term.varFinset]; rfl
    · rcases f with f' | c
      · simp only [Term.constantsToVars, Term.varFinset, locJSupport,
          show locJConstOf Λ J (Sum.inl f' : Λ[[J]].Functions (l + 1)) = ∅ from rfl,
          Finset.union_empty]
        intro x hx
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hx
        obtain ⟨i, hxi⟩ := hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (ih i hxi)
        exact Finset.mem_image.mpr ⟨y, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hy⟩, rfl⟩
      · exact c.elim

/-- The **de-substituted term at ordered support positions**: each skeleton constant `c_j`
becomes the `ℕ`-variable `deepRank S j`. -/
def locDeTermPos (S : Finset J) (t : Λ[[J]].Term Empty) : Λ.Term ℕ :=
  t.constantsToVars.relabel (Sum.elim (fun j => deepRank J S j) Empty.elim)

/-- The ordered-position term uses only variables `< S.card` once `S` covers the term's skeleton
constants. -/
theorem locDeTermPos_varFinset_subset {S : Finset J} {t : Λ[[J]].Term Empty}
    (hsub : locJSupport Λ J t ⊆ S) :
    (locDeTermPos Λ J S t).varFinset ⊆ Finset.range S.card := by
  rw [locDeTermPos, Term.varFinset_relabel]
  intro n hn
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (locConstantsToVars_varFinset_subset Λ J t hx)
  simp only [Sum.elim_inl]
  exact Finset.mem_range.mpr (deepRank_lt_card (J := J) (hsub hj))

/-- The **de-substituted term at `Fin S.card` positions**: `locDeTermPos` with its variables
packaged as genuine `Fin S.card` indices. The finite-variable term through which every
`J`-dependent atom/deForm factors. -/
def locDeTermFin (S : Finset J) (t : Λ[[J]].Term Empty) (hsub : locJSupport Λ J t ⊆ S) :
    Λ.Term (Fin S.card) :=
  (locDeTermPos Λ J S t).restrictVar
    (fun x => ⟨x.1, Finset.mem_range.mp (locDeTermPos_varFinset_subset (Λ := Λ) (J := J) hsub x.2)⟩)

/-! ### Local atoms and deForm — canonical seeds applied to de-substituted terms -/

/-- The **local de-substituted equality atom**: definitionally a canonical equality atom, so its
membership in `canonEqAtoms` is by construction. -/
def locDeEqAtom (S : Finset J) (t u : Λ[[J]].Term Empty)
    (ht : locJSupport Λ J t ⊆ S) (hu : locJSupport Λ J u ⊆ S) :
    Λ.BoundedFormulaω Empty S.card :=
  canonEqAtom Λ (locDeTermFin Λ J S t ht) (locDeTermFin Λ J S u hu)

/-- The **local de-substituted relation atom**: definitionally a canonical relation atom. -/
def locDeRelAtom (S : Finset J) {l : ℕ} (R : Λ.Relations l)
    (ts : Fin l → Λ[[J]].Term Empty) (ht : ∀ i, locJSupport Λ J (ts i) ⊆ S) :
    Λ.BoundedFormulaω Empty S.card :=
  canonRelAtom Λ R fun i => locDeTermFin Λ J S (ts i) (ht i)

/-! ### The assembled family `ΓEMlocal` over the local colimit -/

variable (s₀ : LocalStage)

end FirstOrder.Language
