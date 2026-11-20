module

public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section

namespace FiniteChains

variable {I U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]

/-- A linear lift whose basis images satisfy prescribed carrier conditions. -/
structure CarriedLift (b : Module.Basis I ℤ U) (P : I → V → Prop)
    (d : V →ₗ[ℤ] W) (f : U →ₗ[ℤ] W) where
  map : U →ₗ[ℤ] V
  carried : ∀ i, P i (map (b i))
  commutes : d.comp map = f

namespace CarriedLift

variable {b : Module.Basis I ℤ U} {P : I → V → Prop} {d : V →ₗ[ℤ] W} {f : U →ₗ[ℤ] W}

noncomputable def ofExists (h : ∀ i, ∃ v, P i v ∧ d v = f (b i)) : CarriedLift b P d f where
  map := b.constr ℤ fun i => (h i).choose
  carried i := by simpa only [Module.Basis.constr_basis] using (h i).choose_spec.1
  commutes := b.ext fun i => by
    simpa only [LinearMap.comp_apply, Module.Basis.constr_basis] using (h i).choose_spec.2

theorem boundary (s : CarriedLift b P d f) (u : U) : d (s.map u) = f u :=
  DFunLike.congr_fun s.commutes u

theorem fixed (s : CarriedLift b P d f) (p : V →ₗ[ℤ] V)
    (h : ∀ i v, P i v → p v = v) (u : U) : p (s.map u) = s.map u :=
  DFunLike.congr_fun (b.ext (f₁ := p.comp s.map) (fun i => h i _ (s.carried i))) u

end CarriedLift
end FiniteChains
