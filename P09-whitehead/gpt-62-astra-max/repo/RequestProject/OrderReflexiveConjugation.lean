module

public import RequestProject.OrderCxNatHtpy
public import RequestProject.StrictOrderComplex

@[expose] public section

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- The reversed actual reflexive order edge is null-homotopic. -/
theorem htpy_ordNegSelf_nil (a : P) :
    Htpy _ a a [ordNeg (le_refl a)] [] := by
  have h := htpy_revPath (isPath_ordPos (le_refl a)) (htpy_ordSelf_nil a)
  assumption

/-- Reflexive edge conjugation does not alter the actual based loop class. -/
theorem htpy_reflexive_conjugation {a : P} (p : List _)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) :
    Htpy _ a a ([ordNeg (le_refl a)] ++ p ++ [ordPos (le_refl a)]) p := by
  have h1 := (htpy_ordNegSelf_nil a).congr_append (isPath_nil' a)
    (hp.append (isPath_ordPos (le_refl a)))
  have h1' : Htpy _ a a
      ([ordNeg (le_refl a)] ++ p ++ [ordPos (le_refl a)]) (p ++ [ordPos (le_refl a)]) := by
    simpa only [List.nil_append, List.append_assoc] using h1
  have h2' : Htpy _ a a (p ++ [ordPos (le_refl a)]) p := by
    simpa only [List.append_nil] using ((htpy_ordSelf_nil a).congr_append hp (isPath_nil' a))
  exact h1'.trans h2'

/-- Order-homotopic actual maps agreeing at the basepoint induce homotopic based loops. -/
theorem htpy_loop_mapPath_le_fixed {Q : Type u} [PartialOrder Q]
    {f g : P → Q} (hf : Monotone f) (hg : Monotone g) (hfg : ∀ x, f x ≤ g x)
    {a : P} (hfix : f a = g a) (p : List _)
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) :
    Htpy _ (f a) (f a) (mapPath (orderCxMap f hf) p)
      (mapPath (orderCxMap g hg) p) := by
  have hn := htpy_loop_mapPath_le hf hg hfg hp
  have he : (⟨(f a, g a), hfg a⟩ : OrdEdge Q) = ⟨(f a, f a), le_refl _⟩ :=
    Subtype.ext (Prod.ext rfl hfix.symm)
  change Htpy _ _ _ _
    ([(⟨(f a, g a), hfg a⟩, false)] ++ mapPath (orderCxMap f hf) p ++
      [(⟨(f a, g a), hfg a⟩, true)]) at hn
  rw [he, ← hfix] at hn
  exact (hn.trans (htpy_reflexive_conjugation _ (isPath_mapPath (orderCxMap f hf) hp))).symm

end FiniteChains.Comb
