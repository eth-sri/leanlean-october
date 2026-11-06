module

public import RequestProject.Oriented

public import RequestProject.BlockSpineSubst

@[expose] public section

backwardOptions



/-!
# From a surface filling to the hypothesis `hfill` of the substitution

`RequestProject/BlockSpinePres.lean` reads the marked presentation `B = ⟨s_h, t_h, Z ∣ β_m⟩` of
the block off the two-dimensional spine of the block, and
`RequestProject/BlockSpineSubst.lean` deduces the injectivity of the structural homomorphism
`FiniteChains.BlockFamily.substHomF` of the simultaneous substitution — but only under the
hypothesis `hfill`, the hypothesis (B1) which says that the replaced relator dies in the
substituted presentation.

This file **derives** `hfill` from geometry: from a *filling of the surface relator inside the
cut surface of the block*.  The replaced relator is the surface word

    `∏_h [u_h, v_h]`

(the product of the commutators of the prescribed old words, over a list of pairs of
distinguished generators), and the geometric input is that the corresponding product of
commutators of the chosen loops of the cut surface is trivial in the fundamental group of the
cut surface — which is exactly what the polygon of the closed surface of genus `q` provides,
its boundary being that product of commutators.

* `FiniteChains.Davis.commWord` — the product of commutators over a list of pairs;
* `FiniteChains.Davis.mem_relSub_spineBeta_commWord` — the surface word in the distinguished
  generators is a consequence of the relators of the block, once its loops bound in the cut
  surface;
* `FiniteChains.Davis.filledF_of_surface_filling` — hence the replaced relator is a consequence
  of the substituted presentation: the hypothesis (B1);
* `FiniteChains.Davis.injective_substHomF_of_surface` — the application with `hfill`
  discharged: the only remaining inputs are the reading of the prescribed words by the
  attaching map and the filling of the surface relator.
-/


namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

universe u v

/-! ### Products of commutators -/

/-- The product of the commutators `[f x, f y]` over a list of pairs `(x, y)`. -/
def commWord {ι : Type*} {G : Type*} [Group G] (f : ι → G) (ps : List (ι × ι)) : G :=
  (ps.map fun p => f p.1 * f p.2 * (f p.1)⁻¹ * (f p.2)⁻¹).prod

@[simp] theorem commWord_nil {ι : Type*} {G : Type*} [Group G] (f : ι → G) :
    commWord f [] = 1 := rfl

theorem commWord_cons {ι : Type*} {G : Type*} [Group G] (f : ι → G) (p : ι × ι)
    (ps : List (ι × ι)) :
    commWord f (p :: ps) = (f p.1 * f p.2 * (f p.1)⁻¹ * (f p.2)⁻¹) * commWord f ps := by
  simp [commWord]

/-- A homomorphism carries the product of commutators to the product of commutators of the
images. -/
theorem map_commWord {ι : Type*} {G H : Type*} [Group G] [Group H] (φ : G →* H) (f : ι → G)
    (ps : List (ι × ι)) : φ (commWord f ps) = commWord (fun i => φ (f i)) ps := by
  induction ps with
  | nil => simp
  | cons p ps ih => rw [commWord_cons, map_mul, ih, commWord_cons]; simp

theorem commWord_congr {ι : Type*} {G : Type*} [Group G] {f g : ι → G} (h : ∀ i, f i = g i)
    (ps : List (ι × ι)) : commWord f ps = commWord g ps := by
  simp only [commWord, h]

/-! ### Two general facts about normal closures -/

/-- A homomorphism carries a normal closure into any normal closure containing the images of the
generators. -/
theorem map_mem_normalClosure {G H : Type*} [Group G] [Group H] (φ : G →* H) {S : Set G}
    {N : Set H} (hS : ∀ g ∈ S, φ g ∈ Subgroup.normalClosure N) {x : G}
    (hx : x ∈ Subgroup.normalClosure S) : φ x ∈ Subgroup.normalClosure N := by
  have hle : Subgroup.normalClosure S ≤ (Subgroup.normalClosure N).comap φ :=
    Subgroup.normalClosure_le_normal (fun g hg => hS g hg)
  exact hle hx

/-! ### The surface word is a consequence of the block relators -/

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

/-! ### The hypothesis (B1), derived -/

/-! ### The application -/

end Davis
end FiniteChains
