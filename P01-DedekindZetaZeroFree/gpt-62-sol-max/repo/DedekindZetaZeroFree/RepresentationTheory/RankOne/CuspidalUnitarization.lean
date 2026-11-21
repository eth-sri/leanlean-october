module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RepresentationsAndFixedLevels

@[expose] public section

namespace DedekindZetaZeroFree.CuspidalFiniteCosetForm

variable {G V : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V]

def coefficient (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V) (v : V) : G → ℂ :=
  fun g => ℓ (ρ g v)

abbrev LeftCosets (U : CompactOpenLevel G) :=
  Quotient (MulAction.orbitRel (U.toOpenSubgroup : Subgroup G) G)

def cosetMk (U : CompactOpenLevel G) (g : G) : LeftCosets U :=
  Quotient.mk _ g

def FixesFunctional (ρ : Representation ℂ G V) (U : CompactOpenLevel G)
    (ℓ : Module.Dual ℂ V) : Prop :=
  ∀ u ∈ U.toOpenSubgroup, ∀ v : V, ℓ (ρ u v) = ℓ v

noncomputable def descendedCoefficient (ρ : Representation ℂ G V)
    (ℓ : Module.Dual ℂ V) (U : CompactOpenLevel G) (v : V) : LeftCosets U → ℂ :=
  fun q => coefficient ρ ℓ v q.out

noncomputable def form (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    (U : CompactOpenLevel G) (v w : V) : ℂ :=
  ∑ᶠ q : LeftCosets U,
    descendedCoefficient ρ ℓ U v q * star (descendedCoefficient ρ ℓ U w q)

theorem exists_fixing_level [IsTopologicalGroup G]
    (hBasis : ∀ J : OpenSubgroup G, ∃ U : CompactOpenLevel G,
      U.toOpenSubgroup ≤ J)
    (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    (hℓ : SmoothVector ρ.dual ℓ) :
    ∃ U : CompactOpenLevel G, FixesFunctional ρ U ℓ := by
  rcases hℓ with ⟨J, hJ⟩
  rcases hBasis J with ⟨U, hUJ⟩
  refine ⟨U, fun u hu v => ?_⟩
  have h := congrArg (fun f : Module.Dual ℂ V => f v)
    (hJ u⁻¹ (J.inv_mem (hUJ hu)))
  simpa [Representation.dual, Module.Dual.transpose_apply] using h

theorem descendedCoefficient_eq (ρ : Representation ℂ G V)
    (ℓ : Module.Dual ℂ V) (U : CompactOpenLevel G)
    (hU : FixesFunctional ρ U ℓ) (v : V) (q : LeftCosets U)
    (g : G) (hg : cosetMk U g = q) :
    descendedCoefficient ρ ℓ U v q = coefficient ρ ℓ v g := by
  have he : cosetMk U q.out = cosetMk U g := (Quotient.out_eq q).trans hg.symm
  rcases Quotient.exact he with ⟨u, hu⟩
  change (u : G) * g = q.out at hu
  simp only [descendedCoefficient, coefficient, ← hu, map_mul, Module.End.mul_apply]
  exact hU u u.property (ρ g v)

end DedekindZetaZeroFree.CuspidalFiniteCosetForm
