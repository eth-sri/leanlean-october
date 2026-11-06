module
public import GafniTao.WooleyMixedMean
public import GafniTao.WooleyResidueRefinement
import WeylPort.Analytic.RealLaplace

public section

/-!
# Wooley Lemma 6.3: refinement of the initial mixed mean

This file formalizes the two applications of Lemma 6.2 in the proof of
Wooley's Lemma 6.3.  The key statement is kept pointwise on the complete
finite frequency grid.  Both refined residue classes are explicit and the
separation condition modulo `p^nu` is preserved.
-/

open Finset

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
  have hpnu : 0 < p ^ nu := pow_pos (NeZero.pos p) nu
  have hxiVal : xi.val < p ^ nu := ZMod.val_lt xi
  have hzval :
      (z.val : ZMod (p ^ nu)) = xi := by
    simp_all
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
  grind

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
  pm_5919 theta nu hnu
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
    pm_93 wooleyResidueRefinementFiber Finset.mem_filter Finset.mem_univ true_and red
  have hsep (z w : ZMod (p ^ theta)) :
      wooleyResiduesSeparated nu (red z) (red w) ↔
        wooleyResiduesSeparated nu z w := by
    constructor
    · intro h
      exact wooley_refinements_separated hnu h
        ((href z (red z)).2 rfl) ((href w (red w)).2 rfl)
    · intro h
      unfold wooleyResiduesSeparated at h ⊢
      pm_7912 hz z
      pm_7912 hw w
      rw [hz, hw] at h
      simpa [Nat.mod_eq_of_lt (ZMod.val_lt (red z)),
        Nat.mod_eq_of_lt (ZMod.val_lt (red w))] using h
  have hfiber (xy : ZMod (p ^ nu) × ZMod (p ^ nu))
      (hxy : wooleyResiduesSeparated nu xy.1 xy.2) :
      finePairs.filter (fun zw => redPair zw = xy) = pairFiber xy := by
    ext zw
    simp only [Finset.mem_filter]
    dsimp [finePairs, redPair, pairFiber]
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hfine, hred⟩
      pm_1544
      exact ⟨(href zw.1 xy.1).2 hz, (href zw.2 xy.2).2 hw⟩
    · rintro ⟨hz, hw⟩
      have hzred := (href zw.1 xy.1).1 hz
      have hwred := (href zw.2 xy.2).1 hw
      exact ⟨wooley_refinements_separated hnu hxy hz hw,
        Prod.ext hzred hwred⟩
  have hfiber_empty (xy : ZMod (p ^ nu) × ZMod (p ^ nu))
      (hxy : ¬ wooleyResiduesSeparated nu xy.1 xy.2) :
      finePairs.filter (fun zw => redPair zw = xy) = ∅ := by
    ext zw
    simp only [Finset.mem_filter]
    dsimp [finePairs, redPair]
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and]
    have hempty : zw ∈ (∅ : Finset
        (ZMod (p ^ theta) × ZMod (p ^ theta))) ↔ False := by simp
    rw [hempty]
    constructor
    · rintro ⟨hfine, hred⟩
      pm_1544
      apply hxy
      have : wooleyResiduesSeparated nu (red zw.1) (red zw.2) :=
        (hsep zw.1 zw.2).2 hfine
      simpa [hz, hw] using this
    · exact False.elim
  have hinter (xy : ZMod (p ^ nu) × ZMod (p ^ nu)) :
      ∑ zw ∈ finePairs with redPair zw = xy, F zw.1 zw.2 =
        if wooleyResiduesSeparated nu xy.1 xy.2 then
          ∑ zw ∈ pairFiber xy, F zw.1 zw.2
        else 0 := by
    by_cases hxy : wooleyResiduesSeparated nu xy.1 xy.2
    · rw [ite_eq_left hxy, hfiber xy hxy]
    · rw [ite_eq_right hxy, hfiber_empty xy hxy]
      simp
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
      simp
      simpa using Finset.sum_product
        (Finset.univ : Finset (ZMod (p ^ theta)))
        (Finset.univ : Finset (ZMod (p ^ theta)))
        (fun zw => if wooleyResiduesSeparated nu zw.1 zw.2 then
          F zw.1 zw.2 else 0)
end


end GafniTao
