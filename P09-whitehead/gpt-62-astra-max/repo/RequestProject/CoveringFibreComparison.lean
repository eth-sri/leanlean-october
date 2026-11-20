module

public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

/-! A continuous map over a covering projection is a homeomorphism if
its fibre map is bijective at points meeting every path component.
All transport is actual covering monodromy. Unverified source. -/

noncomputable section
namespace FiniteChains.CoveringComparison
open Topology
open scoped unitInterval Classical
variable {Y E X : Type} [TopologicalSpace Y] [TopologicalSpace E] [TopologicalSpace X]
  (r : C(Y, X)) (p : C(E, X)) (hr : IsCoveringMap r) (hp : IsCoveringMap p)
  (f : C(Y, E)) (hover : ∀ y, p (f y) = r y)

def fibreMap (x : X) : r ⁻¹' {x} → p ⁻¹' {x} :=
  fun y => ⟨f y.val, (hover y.val).trans y.property⟩

variable {x x' : X}

theorem fibreMap_monodromy (γ : Path x x') (y : r ⁻¹' {x}) :
    fibreMap r p f hover x' (hr.monodromy (Path.Homotopic.Quotient.mk γ) y) =
      hp.monodromy (Path.Homotopic.Quotient.mk γ) (fibreMap r p f hover x y) := by
  let Γ := hr.liftPath γ y.val (γ.source.trans y.property.symm)
  have hΓ : f.comp Γ = hp.liftPath γ _
      (γ.source.trans ((hover y.val).trans y.property).symm) := by
    apply (hp.eq_liftPath_iff' _).mpr
    constructor
    · funext t
      exact (hover _).trans
        (congrFun (hr.liftPath_lifts γ y.val (γ.source.trans y.property.symm)) t)
    · change f _ = f y.val
      rw [hr.liftPath_zero]
  apply Subtype.ext
  exact congrArg (fun k : C(unitInterval, E) => k 1) hΓ

include hr hp in
theorem fibreMap_bijective_of_joined (hxx' : Joined x x')
    (hb : Function.Bijective (fibreMap r p f hover x')) :
    Function.Bijective (fibreMap r p f hover x) := by
  let γ := hxx'.somePath
  let b := hp.monodromy (Path.Homotopic.Quotient.mk γ)
  have ha : Function.Bijective (hr.monodromy (Path.Homotopic.Quotient.mk γ)) := hr.monodromy_bijective _
  have hb' : Function.Bijective b := hp.monodromy_bijective _
  have hs :=
    fibreMap_monodromy r p hr hp f hover γ
  constructor
  · intro y z hyz
    apply ha.1
    apply hb.1
    grind
  · intro e
    obtain ⟨y', hy'⟩ := hb.2 (b e)
    obtain ⟨y, rfl⟩ := ha.2 y'
    refine ⟨y, hb'.1 ?_⟩ <;> grind

theorem bijective_of_fibrewise
    (hfib : ∀ x, Function.Bijective (fibreMap r p f hover x)) : Function.Bijective f := by
  constructor
  · intro y z hyz
    have hz := (hover z).symm.trans
      ((congrArg p hyz).symm.trans (hover y))
    exact congrArg Subtype.val ((hfib (r y)).1
      (show fibreMap r p f hover (r y) ⟨y, rfl⟩ =
        fibreMap r p f hover (r y) ⟨z, hz⟩ from Subtype.ext hyz))
  · intro e
    obtain ⟨y, hy⟩ := (hfib _).2 ⟨e, rfl⟩
    exact ⟨y.val, congrArg Subtype.val hy⟩

include hr hp hover in
theorem isLocalHomeomorph : IsLocalHomeomorph f := by
  have h : (p ∘ f) = r := funext hover
  have hc : IsLocalHomeomorph (p ∘ f) := by simpa only [h] using hr.isLocalHomeomorph
  exact hc.of_comp hp.isLocalHomeomorph f.continuous

def homeomorphOfFibrewise
    (hfib : ∀ x, Function.Bijective _) :=
  (isLocalHomeomorph r p hr hp f hover).toHomeomorphOfBijective
    (bijective_of_fibrewise r p f hover hfib)

end FiniteChains.CoveringComparison
