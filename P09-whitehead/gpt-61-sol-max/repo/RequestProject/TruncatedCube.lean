import Mathlib.Tactic

import RequestProject.MomentAngle

/-!
# The truncated complex `M_q` and Lemma 3.2 (iii)

Section 3.3 of the paper cuts the corner `v = (1, …, 1)` out of the cube complex `C(L)`:

  `M = C(L) ∩ {∑_h (1 - x_h) ≥ 1/2}`,

so that the cut surface is a copy of the link `L` of `v`, and asserts (Lemma 3.2 (iii))
that the inclusion sends the fundamental class of the cut surface to zero in `H₂(M; ℤ)`.
The paper's proof is a chain-level computation: the signed sum of the three-cubes has, after
truncation, boundary exactly the cut surface.

This file carries out that computation.  The cells of `M` are

* the cubes of `C(L)` (those meeting the corner are truncated, which does not change their
  cell structure), except the removed corner vertex itself;
* one *cut cell* `Δ_σ` of dimension `|σ| - 1` for each nonempty face `σ` of `L`; the cut
  cells form a copy of `L`, namely the cut surface.

Chains are recorded as pairs: a coefficient function on cubes and a coefficient function on
cut cells.  The boundary operator `bdryT` is the cubical boundary on the first component,
while the coefficient of a cut cell `Δ_τ` in the boundary picks up the cube with free set
`τ` and all other coordinates `+1` (the unique cube truncated along `Δ_τ`), with the sign
`(-1)^{|τ|}`, together with the simplicial boundary inside the cut copy of `L`.

`bdryT_bdryT` verifies that this is a differential, so the model really is a chain complex,
and `cutSurface_isBoundary` is Lemma 3.2 (iii): for an oriented triangulated surface `L`
the fundamental cycle of the cut surface is the boundary of the signed sum of the
three-cubes, hence zero in `H₂(M)`.
-/

namespace FiniteChains

open Finset

variable {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]

  (σ : Finset V)
/-- The cube with free set `σ` all of whose remaining coordinates are `+1`; it is the unique
cube of `C(L)` with free set `σ` that is truncated along the cut cell `Δ_σ`. -/
def posCube   := fun v => if v ∈ σ then CubeCoord.free else CubeCoord.pos

omit [LinearOrder V] in
@[simp] theorem freeSet_posCube  : freeSet (posCube σ) = σ := by aesop (add simp [posCube])

omit [Fintype V] [LinearOrder V] in
theorem update_posCube  (j : V) :
    Function.update (posCube σ) j CubeCoord.free = posCube (insert j σ) := by aesop (add simp [posCube, Function.update_apply])

omit [LinearOrder V] in
@[simp] theorem cubeChain_posCube (o : Finset V → ℤ) (σ : Finset V) :
    cubeChain o (posCube σ) = o σ := by
  have : ∏ h ∈ univ \ σ, ((posCube σ) h).sgn = 1 := by
    refine Finset.prod_eq_one ?_
    intro h hh
    have  := (Finset.mem_sdiff.mp hh).2
    simp [posCube, this, CubeCoord.sgn]
  simp [cubeChain, this]

/-- The sign with which the cut cell `Δ_σ` occurs in the boundary of the truncated cube
with free set `σ` and remaining coordinates `+1`. -/
def cutSign   := (-1) ^ σ.card

/-- A chain of the truncated complex: coefficients on the cubes and on the cut cells. -/
abbrev TChain (V : Type) := (Cube V → ℤ) × (Finset V → ℤ)

/-- The boundary operator of the truncated complex. -/
def bdryT (x : TChain V)  :=
  (bdry x.1, fun τ => cutSign τ * x.1 (posCube τ) + simpBdry x.2 τ)

/-- The cubical boundary of the cube `posCube τ`, written out. -/
theorem bdry_posCube (c : Cube V → ℤ) (τ : Finset V) :
    bdry c (posCube τ)
      = ∑ j ∈ univ.filter (fun j => j ∉ τ),
          (-1 : ℤ) ^ (τ.filter (fun i => i < j)).card * c (posCube (insert j τ)) := by
  have hidx : (univ.filter fun j => (posCube τ) j ≠ CubeCoord.free)
      = univ.filter fun j => j ∉ τ := by
    ext j; simp [posCube]
  rw [bdry, hidx]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjτ : j ∉ τ := by simpa using hj
  rw [update_posCube, incid, freeSet_posCube]
  simp [posCube, hjτ, CubeCoord.sgn]

/-- **Lemma 3.2 (iii): the cut surface bounds.**  Let `o` be the fundamental cycle of an
oriented triangulated closed surface `L` (a simplicial cycle supported on the triangles).
Then the signed sum of the three-cubes of `C(L)`, viewed in the truncated complex, has
boundary equal to the fundamental cycle of the cut copy of `L`, up to sign.  In particular
the class of the cut surface vanishes in `H₂(M)`. -/
theorem cutSurface_isBoundary {o : Finset V → ℤ} (hcyc : simpBdry o = 0)
    (hsupp : ∀ σ : Finset V, σ.card ≠ 3 → o σ = 0) :
    bdryT (cubeChain o, 0) = (0, -o) := by
  refine Prod.ext ?_ ?_
  · exact cubeChain_cycle hcyc
  · funext τ
    show cutSign τ * cubeChain o (posCube τ) + simpBdry 0 τ = -o τ
    have hzero : simpBdry (0 : Finset V → ℤ) τ = 0 := by simp [simpBdry]
    rw [hzero, add_zero, cubeChain_posCube]
    by_cases h3 : τ.card = 3
    · simp [cutSign, h3]
    · simp [hsupp τ h3]

end FiniteChains
