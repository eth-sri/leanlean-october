module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.MonoidAlgebra.Defs

@[expose] public section

namespace Finsupp

/-- Additive functions on the free abelian group agree if they agree on its basis. -/
theorem eq_on_basis {ι M : Type*} [AddCommGroup M] {f g : (ι →₀ ℤ) → M}
    (hf : ∀ x y, f (x + y) = f x + f y) (hg : ∀ x y, g (x + y) = g x + g y)
    (h : ∀ i, f (single i 1) = g (single i 1)) (c : ι →₀ ℤ) : f c = g c := by
  let F  := AddMonoidHom.mk' f hf
  let G  := AddMonoidHom.mk' g hg
  exact LinearMap.congr_fun (lhom_ext' (φ := F.toIntLinearMap) (ψ := G.toIntLinearMap)
    fun i => LinearMap.ext_ring (h i)) c

/-- Additive functions out of a finitely supported direct sum are determined by the summands. -/
theorem eq_on_singles {ι R M : Type*} [AddZeroClass R] [AddGroup M] {f g : (ι →₀ R) → M}
    (hf : ∀ x y, f (x + y) = f x + f y) (hg : ∀ x y, g (x + y) = g x + g y)
    (h : ∀ i r, f (single i r) = g (single i r)) (c : ι →₀ R) : f c = g c :=
  DFunLike.congr_fun (addHom_ext (f := AddMonoidHom.mk' f hf) (g := AddMonoidHom.mk' g hg) h) c

/-- Pushforward of chains preserves a pointwise commutative square of coordinate maps. -/
theorem mapDomain_square {A B C D M : Type*} [AddCommMonoid M]
    {f : A → B} {g : B → D} {i : A → C} {j : C → D} (h : ∀ x, g (f x) = j (i x))
    (c : A →₀ M) : mapDomain g (mapDomain f c) = mapDomain j (mapDomain i c) := by
  rw [← mapDomain_comp, ← mapDomain_comp]
  exact mapDomain_congr fun x _ => h x

/-- For a supported chain, it suffices to check the images of the relevant basis vectors. -/
theorem map_mem_of_supported {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (S : Set ι) (T : Submodule R M) (L : (ι →₀ R) →ₗ[R] M)
    (hL : ∀ v ∈ S, L (single v 1) ∈ T)
    {c : ι →₀ R} (hc : c ∈ supported R R S) : L c ∈ T := by
  have h : supported R R S ≤ T.comap L := by
    rw [supported_eq_span_single]
    exact Submodule.span_le.mpr (by rintro _ ⟨v, hv, rfl⟩; exact hL v hv)
  exact h hc

theorem map_mem_of_basis {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (T : Submodule R M) (L : (ι →₀ R) →ₗ[R] M)
    (hL : ∀ v, L (single v 1) ∈ T) (c : ι →₀ R) : L c ∈ T :=
  map_mem_of_supported Set.univ T L (fun v _ => hL v) (by simp)

theorem linearCombination_mem {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {T : Submodule R M} {v : ι → M} (hv : ∀ i, v i ∈ T) (c : ι →₀ R) :
    linearCombination R v c ∈ T :=
  map_mem_of_basis T _ (fun i => by simpa using hv i) c

end Finsupp

namespace MonoidAlgebra

/-- Additive functions from a monoid algebra agree if they agree on each summand. -/
theorem eq_on_singles {ι R M : Type*} [Semiring R] [AddGroup M] {f g : MonoidAlgebra R ι → M}
    (hf : ∀ x y, f (x + y) = f x + f y) (hg : ∀ x y, g (x + y) = g x + g y)
    (h : ∀ i r, f (single i r) = g (single i r)) (c : MonoidAlgebra R ι) : f c = g c :=
  DFunLike.congr_fun (addMonoidHom_ext (f := AddMonoidHom.mk' f hf) (g := AddMonoidHom.mk' g hg) h) c

end MonoidAlgebra

open Lean Parser Tactic

/-- Solve the additivity goals produced when reducing an equality to generators. -/
syntax "finsupp_additivity" (simpArgs)? : tactic
macro_rules
  | `(tactic| finsupp_additivity $[$args]?) => do
    let rules := Syntax.TSepArray.ofElems (args.map (·.raw[1].getSepArgs.map fun s => ⟨s⟩) |>.getD #[])
    `(tactic| (intro x y; (try simp [Finsupp.mapDomain_add, Finsupp.add_apply,
      add_mul, mul_add, Finset.sum_add_distrib, $rules,*]) <;> abel))

/-- Reduce equality of additive expressions in an integer chain to the unit generators. -/
macro "finsupp_basis " c:ident args:(simpArgs)? : tactic =>
  `(tactic| (apply Finsupp.eq_on_basis (c := $c)
             case hf => finsupp_additivity $[$args]?
             case hg => finsupp_additivity $[$args]?))

/-- Reduce equality of additive expressions in a chain to the individual summands. -/
macro "finsupp_singles " c:ident args:(simpArgs)? : tactic =>
  `(tactic| (apply Finsupp.eq_on_singles (c := $c)
             case hf => finsupp_additivity $[$args]?
             case hg => finsupp_additivity $[$args]?))

/-- Reduce equality of additive group-ring expressions to the individual monomials. -/
macro "group_ring_singles " c:ident args:(simpArgs)? : tactic =>
  `(tactic| (apply MonoidAlgebra.eq_on_singles (c := $c)
             case hf => finsupp_additivity $[$args]?
             case hg => finsupp_additivity $[$args]?))
