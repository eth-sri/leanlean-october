import Mathlib.Tactic

import RequestProject.RelativeAmbientChain
import RequestProject.PresChainRealization

/-! The concrete relative induction as `PresChainFS` and hence as actual
topological presentation chains. The zeroth presentation is the original
core itself, not a larger presentation merely containing it. Unverified. -/

noncomputable section


namespace FiniteChains.PresInclusionFS
variable {A B J K : Type} [DecidableEq A] [DecidableEq B]
  (ρ : J → FreeGroup A) (τ : K → FreeGroup B)
  (g : A → B) (f : J → K) (hg : Function.Injective g) (hf : Function.Injective f)
  (hrel : ∀ j, τ (f j) = FreeGroup.map g (ρ j))

theorem zero_universal_chains
    (hz : ∀ x, FSIsFoxCycle ρ x → (mor ρ τ g f hg hf hrel).cells x = 0)
    (u : PresGroup ρ × J →₀ ℤ) (hu : Comb.bdry2 (Comb.univCover ρ) u = 0) :
    Finsupp.mapDomain (Prod.map (groupHom ρ τ g f hrel) f) u = 0 := by
  apply (Comb.fs_univCover_zero_pi2_iff ρ (groupHom ρ τ g f hrel) f hf).2 ?_ u hu
  intro v hv
  apply hz v
  
  ext i : 1
  simpa [fs_coverSecondBoundary_apply, Finsupp.zero_apply] using hv i
end FiniteChains.PresInclusionFS

namespace FiniteChains.RelativeNormalForm.AmbientChain
variable {A C : Type} {core : C → FreeGroup A} {n : ℕ} (c : AmbientChain core n)

def chainGen : ℕ → Type
  | 0 => A
  | _ + 1 => A ⊕ c.extraGen

instance chainGenDecidableEq : (i : ℕ) → DecidableEq (c.chainGen i)
  | 0 => Classical.decEq _
  | _ + 1 => @instDecidableEqSum A c.extraGen (Classical.decEq _) (Classical.decEq _)

def chainCell : ℕ → Type
  | 0 => C
  | i + 1 => C ⊕ {s // c.stage i s}

def chainRel : ∀ i, c.chainCell i → FreeGroup (c.chainGen i)
  | 0 => core
  | i + 1 => rawPresentation core (restrictedExtra c.rel (c.stage i))

def chainGenIncl : ∀ i, c.chainGen i → c.chainGen (i + 1)
  | 0 => Sum.inl
  | _ + 1 => id

def chainCellIncl : ∀ i, c.chainCell i → c.chainCell (i + 1)
  | 0 => Sum.inl
  | i + 1 => oldCellIncl (c.mono i)

variable (i : ℕ)
include i in
theorem chainGenIncl_injective  : Function.Injective (c.chainGenIncl i) := by
  cases i
  · exact Sum.inl_injective
  · exact Function.injective_id

include i in
theorem chainCellIncl_injective  : Function.Injective (c.chainCellIncl i) := by
  cases i with
  | zero => exact Sum.inl_injective
  | succ i => exact oldCellIncl_injective (c.mono i)

include i in
theorem chainRel_incl  (j : c.chainCell i) :
    c.chainRel (i + 1) (c.chainCellIncl i j) = FreeGroup.map (c.chainGenIncl i) (c.chainRel i j) := by
  cases i with
  | zero => rfl
  | succ i =>
      cases j with
      | inl j => solve_by_elim [FreeGroup.map.id, symm]
      | inr j => exact (FreeGroup.map.id (c.rel j.val)).symm

variable (hinj : Function.Injective (expMatrix core))
include hinj in
theorem chainMor_zero  (i : ℕ) (hi : i < n + 1)
    (x : c.chainCell i →₀ MonoidAlgebra ℤ (PresGroup (c.chainRel i)))
    (hx : FSIsFoxCycle (c.chainRel i) x) :
    (PresInclusionFS.mor (c.chainRel i) (c.chainRel (i + 1))
      (c.chainGenIncl i) (c.chainCellIncl i) (c.chainGenIncl_injective i)
      (c.chainCellIncl_injective i) (c.chainRel_incl i)).cells x = 0 := by
  cases i with
  | zero =>
      exact coreIntoRaw_zero core (restrictedExtra c.rel (c.stage 0)) hinj
        (c.core_trivial 0) x hx
  | succ i => exact c.zero i (by omega) x hx

include hinj in
/-- Every hypothesis in the presentation-chain zero field is supplied by
the actual finite-support construction. -/
def toPresChainFS  : PresChainFS core (n + 1) where
  gen := c.chainGen
  cell := c.chainCell
  decGen := c.chainGenDecidableEq
  rel := c.chainRel
  genIncl := c.chainGenIncl
  genIncl_injective := c.chainGenIncl_injective
  cellIncl := c.chainCellIncl
  cellIncl_injective := c.chainCellIncl_injective
  rel_incl := c.chainRel_incl
  baseGen := id
  baseGen_injective := Function.injective_id
  baseCell := id
  baseCell_injective := Function.injective_id
  rel_base := by intro j; exact (FreeGroup.map.id (core j)).symm
  zero_pi2 := by
    classical solve_by_elim (transparency := .default) (maxDepth := 10) [FiniteChains.PresInclusionFS.zero_universal_chains, FiniteChains.RelativeNormalForm.AmbientChain.chainGenIncl_injective, FiniteChains.RelativeNormalForm.AmbientChain.chainCellIncl_injective, FiniteChains.RelativeNormalForm.AmbientChain.chainRel_incl, FiniteChains.RelativeNormalForm.AmbientChain.chainMor_zero]

include i in
theorem chain_proper  (hi : i < n + 1) :
    (∃ a : c.chainGen (i + 1), a ∉ Set.range (c.chainGenIncl i)) ∨
      ∃ j : c.chainCell (i + 1), j ∉ Set.range (c.chainCellIncl i) := by
  cases i with
  | zero =>
      left
      exact ⟨Sum.inr c.fresh, by rintro ⟨a, h⟩; exact Sum.inl_ne_inr h⟩
  | succ i =>
      obtain ⟨s, hs, hsp⟩ := c.strict i (by omega)
      right
      refine ⟨Sum.inr ⟨s, hs⟩, ?_⟩
      rintro ⟨j, hj⟩
      cases j with
      | inl j => exact Sum.inl_ne_inr hj
      | inr j =>
          have he : j.val = s := congrArg Subtype.val (Sum.inr.inj hj)
          exact hsp (he ▸ j.property)

end FiniteChains.RelativeNormalForm.AmbientChain
