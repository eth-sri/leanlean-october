module
import Mathlib
public import GafniTao.WooleyMixedMean
public import GafniTao.WooleyResidueRefinement

@[expose] public section

/-!
# Wooley Lemma 6.3: refinement of the initial mixed mean

This file formalizes the two applications of Lemma 6.2 in the proof of
Wooley's Lemma 6.3.  The key statement is kept pointwise on the complete
finite frequency grid.  Both refined residue classes are explicit and the
separation condition modulo `p^nu` is preserved.
-/

open Finset
open scoped BigOperators

namespace GafniTao



section
variable {p nu theta : ℕ} [NeZero p] (hnu : nu ≤ theta)
include p nu theta hnu

/-- A refinement of a residue class modulo `p^theta` has the original least
residue modulo `p^nu`. -/
theorem wooley_refinement_val_mod
    
    (xi : ZMod (p ^ nu))
    {z : ZMod (p ^ theta)}
    (hz : z ∈ wooleyResidueRefinementFiber p nu theta hnu xi) :
    z.val % (p ^ nu) = xi.val := by
  have hcast :
      ZMod.castHom (pow_dvd_pow p hnu) (ZMod (p ^ nu)) z = xi := by
    exact (Finset.mem_filter.mp hz).2
  have hzval :
      (z.val : ZMod (p ^ nu)) = xi := by
    simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using hcast
  have hval := congrArg ZMod.val hzval
  simpa only [ZMod.val_natCast] using hval

/-- Separation modulo `p^nu` survives simultaneous refinement to depth
`theta`. -/
theorem wooley_refinements_separated
    
    {xi eta : ZMod (p ^ nu)}
    (hsep : wooleyResiduesSeparated nu xi eta)
    {xi' eta' : ZMod (p ^ theta)}
    (hxi : xi' ∈ wooleyResidueRefinementFiber p nu theta hnu xi)
    (heta : eta' ∈ wooleyResidueRefinementFiber p nu theta hnu eta) :
    wooleyResiduesSeparated nu xi' eta' := by
  unfold wooleyResiduesSeparated at hsep ⊢
  rw [wooley_refinement_val_mod hnu xi hxi,
    wooley_refinement_val_mod hnu eta heta]
  simpa [Nat.mod_eq_of_lt (ZMod.val_lt xi),
    Nat.mod_eq_of_lt (ZMod.val_lt eta)] using hsep

/-- Summing over a separated coarse pair and then over both refinement
fibres is exactly summation over separated refined pairs. -/
theorem wooley_sum_refinement_pairs
    
    (F : ZMod (p ^ theta) → ZMod (p ^ theta) → ℝ) :
    ∑ xi : ZMod (p ^ nu),
        ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
          ∑ xi' ∈ wooleyResidueRefinementFiber p nu theta hnu xi,
            ∑ eta' ∈ wooleyResidueRefinementFiber p nu theta hnu eta,
              F xi' eta' =
      ∑ xi' : ZMod (p ^ theta),
        ∑ eta' : ZMod (p ^ theta) with
          wooleyResiduesSeparated nu xi' eta', F xi' eta' := by
  classical
  let red : ZMod (p ^ theta) → ZMod (p ^ nu) :=
    ZMod.castHom (pow_dvd_pow p hnu) (ZMod (p ^ nu))
  let coarsePairs : Finset (ZMod (p ^ nu) × ZMod (p ^ nu)) :=
    (Finset.univ.product Finset.univ).filter fun xy =>
      wooleyResiduesSeparated nu xy.1 xy.2
  let finePairs : Finset (ZMod (p ^ theta) × ZMod (p ^ theta)) :=
    (Finset.univ.product Finset.univ).filter fun zw =>
      wooleyResiduesSeparated nu zw.1 zw.2
  let redPair : ZMod (p ^ theta) × ZMod (p ^ theta) →
      ZMod (p ^ nu) × ZMod (p ^ nu) := fun zw => (red zw.1, red zw.2)
  let pairFiber (xy : ZMod (p ^ nu) × ZMod (p ^ nu)) :=
    (wooleyResidueRefinementFiber p nu theta hnu xy.1).product
      (wooleyResidueRefinementFiber p nu theta hnu xy.2)
  have href (z : ZMod (p ^ theta)) (xi : ZMod (p ^ nu)) :
      z ∈ wooleyResidueRefinementFiber p nu theta hnu xi ↔ red z = xi := by
    simp only [wooleyResidueRefinementFiber, Finset.mem_filter, Finset.mem_univ, true_and, red]
  have hsep (z w : ZMod (p ^ theta)) :
      wooleyResiduesSeparated nu (red z) (red w) ↔
        wooleyResiduesSeparated nu z w := by
    constructor
    · intro h
      exact wooley_refinements_separated hnu h
        ((href z (red z)).2 rfl) ((href w (red w)).2 rfl)
    · intro h
      unfold wooleyResiduesSeparated at h ⊢
      have hz := wooley_refinement_val_mod hnu (red z)
        ((href z (red z)).2 rfl)
      have hw := wooley_refinement_val_mod hnu (red w)
        ((href w (red w)).2 rfl)
      rw [hz, hw] at h
      simpa [Nat.mod_eq_of_lt (ZMod.val_lt (red z)),
        Nat.mod_eq_of_lt (ZMod.val_lt (red w))] using h
  have hfiber (xy : ZMod (p ^ nu) × ZMod (p ^ nu))
      (hxy : wooleyResiduesSeparated nu xy.1 xy.2) :
      finePairs.filter (fun zw => redPair zw = xy) = pairFiber xy := by aesop
  have hfiber_empty (xy : ZMod (p ^ nu) × ZMod (p ^ nu))
      (hxy : ¬ wooleyResiduesSeparated nu xy.1 xy.2) :
      finePairs.filter (fun zw => redPair zw = xy) = ∅ := by aesop
  have hinter (xy : ZMod (p ^ nu) × ZMod (p ^ nu)) :
      ∑ zw ∈ finePairs with redPair zw = xy, F zw.1 zw.2 =
        if wooleyResiduesSeparated nu xy.1 xy.2 then
          ∑ zw ∈ pairFiber xy, F zw.1 zw.2
        else 0 := by grind
  have hgroup := Finset.sum_fiberwise finePairs redPair
    (fun zw => F zw.1 zw.2)
  have hflat :
      ∑ xy ∈ coarsePairs,
          ∑ zw ∈ pairFiber xy, F zw.1 zw.2 =
        ∑ zw ∈ finePairs, F zw.1 zw.2 := by
    rw [← hgroup]
    simp_rw [hinter]
    simp [coarsePairs, Finset.sum_filter]
  calc
    (∑ xi : ZMod (p ^ nu),
        ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
          ∑ xi' ∈ wooleyResidueRefinementFiber p nu theta hnu xi,
            ∑ eta' ∈ wooleyResidueRefinementFiber p nu theta hnu eta,
              F xi' eta') =
        ∑ xy ∈ coarsePairs,
          ∑ zw ∈ pairFiber xy, F zw.1 zw.2 := by
      simp only [coarsePairs, pairFiber, Finset.sum_filter]
      simp
      simpa [Finset.sum_product] using (Finset.sum_product
        (Finset.univ : Finset (ZMod (p ^ nu)))
        (Finset.univ : Finset (ZMod (p ^ nu)))
        (fun xy => if wooleyResiduesSeparated nu xy.1 xy.2 then
          ∑ zw ∈
            (wooleyResidueRefinementFiber p nu theta hnu xy.1).product
              (wooleyResidueRefinementFiber p nu theta hnu xy.2),
            F zw.1 zw.2 else 0)).symm
    _ = ∑ zw ∈ finePairs, F zw.1 zw.2 := hflat
    _ = ∑ xi' : ZMod (p ^ theta),
        ∑ eta' : ZMod (p ^ theta) with
          wooleyResiduesSeparated nu xi' eta', F xi' eta' := by
      simp only [finePairs, Finset.sum_filter]
      simpa using Finset.sum_product
        (Finset.univ : Finset (ZMod (p ^ theta)))
        (Finset.univ : Finset (ZMod (p ^ theta)))
        (fun zw => if wooleyResiduesSeparated nu zw.1 zw.2 then
          F zw.1 zw.2 else 0)
end





