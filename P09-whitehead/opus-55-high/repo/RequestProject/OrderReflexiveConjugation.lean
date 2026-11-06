import RequestProject.OrderCxNatHtpy
import RequestProject.StrictOrderComplex
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

/-- The reversed actual reflexive order edge is null-homotopic. -/
theorem htpy_ordNegSelf_nil (a : P) :
    Htpy (orderCx P) a a [ordNeg (le_refl a)] [] := by
  have h := htpy_revPath (by aesop) (htpy_ordSelf_nil a)
  simp_all

/-- Reflexive edge conjugation does not alter the actual based loop class. -/
theorem htpy_reflexive_conjugation {a : P} p
    (hp : IsPathX (orderCx P) p a a) :
    Htpy (orderCx P) a a ([ordNeg (le_refl a)] ++ p ++ [ordPos (le_refl a)]) p := by
  have h1 := (htpy_ordNegSelf_nil a).congr_append (isPath_nil' a)
    (hp.append (isPath_ordPos (le_refl a)))
  have h2 := (htpy_ordSelf_nil a).congr_append hp (isPath_nil' a)
  have h1' : Htpy _ a a
      ([ordNeg (le_refl a)] ++ p ++ [ordPos (le_refl a)]) (p ++ [ordPos (le_refl a)]) := by
    simp_all
  have h2' : Htpy _ a a (p ++ [ordPos (le_refl a)]) p := by
    simp_all
  exact h1'.trans h2'

/-- Order-homotopic actual maps agreeing at the basepoint induce homotopic based loops. -/
theorem htpy_loop_mapPath_le_fixed {Q} [PartialOrder Q]
    {f g : P → Q} hf hg (hfg : ∀ x, f x ≤ g x)
    {a} (hfix : f a = g a) p
    (hp : IsPathX (orderCx P) p a a) :
    Htpy (orderCx Q) (f a) (f a) (mapPath (orderCxMap f hf) p)
      (mapPath (orderCxMap g hg) p) := by
  have hn := htpy_loop_mapPath_le hf hg hfg hp
  have he : (⟨(f a, g a), hfg a⟩ : OrdEdge Q) = ⟨(f a, f a), le_refl _⟩ :=
    by simp_all
  change Htpy _ (g a) (g a) (mapPath (orderCxMap g hg) p)
    ([(⟨(f a, g a), hfg a⟩, false)] ++ mapPath (orderCxMap f hf) p ++
      [(⟨(f a, g a), hfg a⟩, true)]) at hn
  rw [he, ← hfix] at hn
  exact (hn.trans (htpy_reflexive_conjugation _ (isPath_mapPath _ hp))).symm
