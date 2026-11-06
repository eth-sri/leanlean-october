import RequestProject.MagnusKernel
import RequestProject.CoverHomologyOne
import RequestProject.UniversalCoefficients


/-!
# The Hurewicz dictionary `H₁(K_N) = N/[N, N]`, proved

For a finite presentation `⟨x_1, …, x_n | r_1, …, r_m⟩` with free group `F`, relator
subgroup `R = ⟪r_1, …, r_m⟫` and a normal subgroup `Ñ ◁ F` containing the relators, the
chain complex of the cover `K_N` was built in `RequestProject/CoverChainComplex.lean`:

* its cycles are the Fox vectors of the elements of `Ñ` (Crowell);
* its boundaries are the Fox vectors of the elements of `R`
  (`RequestProject/CoverHomologyOne.lean`).

With the Magnus/Blanchfield theorem of `RequestProject/MagnusKernel.lean` (the Fox vector
map has kernel exactly `[Ñ, Ñ]`) this identifies the first homology of the cover:

`H₁(K_N) = Ñ / (R·[Ñ, Ñ]) = N/[N, N]`,  where `N = Ñ/R`.

The two statements proved here are

* `FiniteChains.foxVec_mem_range_bdry2_iff` — for `w ∈ Ñ` the Fox vector of `w` is a
  boundary exactly when `w ∈ R·[Ñ, Ñ]`; this is the injectivity half of the dictionary, the
  surjectivity half being the Crowell sequence;
* `FiniteChains.mem_relComm_of_pow_mem` — the resulting torsion freeness of `N/[N, N]`:
  if the Fox boundary of the cover is injective modulo every prime, then `wⁿ ∈ R·[Ñ, Ñ]`
  with `n ≠ 0` forces `w ∈ R·[Ñ, Ñ]`.

Up to the passage from `Ñ ◁ F` to `N = Ñ/R ◁ G = F/R`, this is exactly the input that
Section 2 of the paper takes from the Hurewicz theorem and the universal coefficient
theorem.
-/
