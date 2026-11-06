import RequestProject.GenusLoops
import RequestProject.BlockSurfaceApplyW
import RequestProject.Tac
noncomputable section


/-!
# The theorem applied to the block of the article, over the closed surface of genus `q`

This file feeds the genuine closed surface of genus `q` into the general theorem
`FiniteChains.Davis.injective_substHomF_of_surfaceW`.

The nerve of the block is the flag triangulation of the closed orientable surface of genus `q`
carried by the face poset `SCell (gvc q) (gec q)` of the `4q`-gon with its sides glued in pairs
according to the surface word `∏_{h<q} a_h b_h a_h⁻¹ b_h⁻¹`.  The marking
`FiniteChains.Davis.surfAtt` sends the boundary of the polygon onto the attaching circle of the
relator of the block, so that the side `4h` of the polygon reads the generator `a_h` and the
side `4h+1` reads `b_h`; the polygon itself is filled by the triangles of the surface, whence
`FiniteChains.Davis.Genus.genus_hfilling`, the hypothesis (B1) of the substitution.

* `FiniteChains.Davis.Genus.genusW` — the words of the presentation: the chosen words of the
  retained relators, and the surface word for the relator of the block;
* `FiniteChains.Davis.Genus.genusAtt` — the attaching map of the block, i.e. the marking of the
  surface;
* `FiniteChains.Davis.Genus.genus_hread` — the loop of the distinguished generator `(h, i)`
  reads exactly the letter `a_h`, resp. `b_h`;
* `FiniteChains.Davis.Genus.injective_substHomF_genus` — **the theorem applied to the block**:
  the structural homomorphism of the simultaneous substitution by the block of genus `q` is
  injective.
-/

bwd

namespace FiniteChains.Davis

open RACG Mirror Comb PresModel BlockFamily

namespace Genus

variable {α Jr : Type} (ρ : Jr ⊕ PUnit → FreeGroup α) (a b : ℕ → α) (q : ℕ) [NeZero q]

/-- The words of the presentation: the chosen words of the retained relators, and the surface
word of genus `q` for the relator of the block. -/
def genusW : Jr ⊕ PUnit → List (α × Bool) :=
  Sum.elim (fun jr => presWords ρ (Sum.inl jr)) (fun _ => surfWord a b q)

omit [NeZero q] in
theorem genusW_inr (s : PUnit) : genusW ρ a b q (Sum.inr s) = surfWord a b q := rfl

omit [NeZero q] in
theorem mk_genusW (hrho : ρ (Sum.inr PUnit.unit) = FreeGroup.mk (surfWord a b q)) :
    ∀ j, FreeGroup.mk (genusW ρ a b q j) = ρ j := by
  rintro (jr | s)
  · exact mk_presWords ρ _
  tauto

/-- **The attaching map of the block**: the marking of the surface of genus `q`, which sends the
boundary of the polygon onto the attaching circle of the relator of the block. -/
abbrev genusAtt :=
  surfAtt (w := genusW ρ a b q) (j₀ := Sum.inr PUnit.unit) (genus_hM a b q)
    (genus_hvlab a b q) (genus_helb a b q) (gc q)

/-- The word read by the loop of the distinguished generator `x = (h, i)`: the letter `a_h` for
`i = false`, the letter `b_h` for `i = true`. -/
def genusLw (_ : PUnit) (x : ℕ × Bool) :=
  [sLet a b (4 * (x.1 % q) + (if x.2 then 1 else 0))]

/-! ### The base point -/

theorem genusAtt_base :
    genusAtt ρ a b q (gBase q) = ptBase (genusW ρ a b q) := by
  rwd [gBase, att_V]
  rfl

theorem genus_hcb :
    IsPath (orderCx (PresPos (genusW ρ a b q))).src (orderCx (PresPos (genusW ρ a b q))).tgt []
      (ptBase (genusW ρ a b q)) (genusAtt ρ a b q (gBase q)) :=
  (genusAtt_base ρ a b q).symm

/-! ### The reading -/

omit [NeZero q] in
theorem genus_index (x : ℕ × Bool) :
    8 * (x.1 % q) + (if x.2 then 2 else 0)
      = 2 * (4 * (x.1 % q) + (if x.2 then 1 else 0)) := by
  grind

theorem genus_index_lt (x : ℕ × Bool) :
    4 * (x.1 % q) + (if x.2 then 1 else 0) < (surfWord a b q).length := by
  have hq : x.1 % q < q := Nat.mod_lt _ q.pos_of_neZero
  rw [surfWord_length]
  grind

/-- **The loop of the distinguished generator reads its letter.** -/
theorem genus_hread s x :
    Htpy (orderCx (PresPos (genusW ρ a b q))) (ptBase (genusW ρ a b q))
      (ptBase (genusW ρ a b q))
      ([] ++ mapPath (orderCxMap (genusAtt ρ a b q) (genusAtt ρ a b q).monotone) (gSig q x)
        ++ revPath [])
      (wordLoop (genusW ρ a b q) (genusLw a b q s x)) := by
  set k : ℕ := 4 * (x.1 % q) + (if x.2 then 1 else 0) with hkdef
  have hk : k < (genusW ρ a b q (Sum.inr PUnit.unit)).length := genus_index_lt a b q x
  -- the loop of the generator is the side of the polygon carrying the letter `k`
  have hsig : gSig q x
      = bdEdge _ (cyc _ (2 * k)) ++ bdEdge _ (cyc _ (2 * k + 1)) := by
    have h1 : gSig q x = gPath q (2 * k) := by
      rw [gSig_eq, genus_index]
    tauto
  -- the letter read is the letter `k` of the surface word
  have hlet : (genusW ρ a b q (Sum.inr PUnit.unit))[k]'hk = sLet a b k := by
    have h := surfWord_getElem? a b q k (by
      have := genus_index_lt a b q x
      simp_all)
    have h' : (genusW ρ a b q (Sum.inr PUnit.unit))[k]? = some (sLet a b k) := h
    rw [List.getElem?_eq_getElem hk] at h'
    exact Option.some.inj h'
  have hmain := htpy_mapPath_letter (w := genusW ρ a b q) (j₀ := Sum.inr PUnit.unit)
    (genus_hM a b q) (genus_hvlab a b q) (genus_helb a b q) (gc q) k hk
  have hword : wordLoop _ (genusLw a b q s x)
      = letterLoop (genusW ρ a b q) (sLet a b k) := by
    simp [genusLw, wordLoop, hkdef]
  simp_all

/-! ### The relator of the block -/

/-! ### The theorem applied to the block -/

/-! ### Simultaneous substitutions for an arbitrary family of relators -/
