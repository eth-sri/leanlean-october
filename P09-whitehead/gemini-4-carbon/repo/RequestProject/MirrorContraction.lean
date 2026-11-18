module

public import RequestProject.NervePrism
public import RequestProject.ChamberDescent

@[expose] public section

/-!
# The union of the descending mirrors is contractible

The chamber proof needs the following fact about the chamber `F = |𝒫|`, the order complex of
the poset `𝒫` of simplices of `L`: for a nonempty simplex `D` of `L`, the union of mirrors

  `⋃_{s ∈ D} F_s`,  `F_s = |{σ ∈ L : s ∈ σ}|`,

is nonempty and contractible.  Two statements are proved here.

* `FiniteChains.Mirror.exists_mem_forall_mem_iff` — the union of mirrors **is** the order complex
  of the poset `𝒫_D = {σ ∈ L : σ ∩ D ≠ ∅}`: a nonempty chain of simplices lies in a single
  mirror `F_s` with `s ∈ D` if and only if each of its members meets `D`.
* `FiniteChains.Mirror.exists_bdry_eq_of_cycle` — the augmented simplicial chain complex of the
  order complex of `𝒫_D` is contractible: every cycle is a boundary, by the explicit prism
  homotopy of `RequestProject/NervePrism.lean` applied to `ρ σ = σ ∩ D`, which satisfies
  `ρ ≤ id` and `ρ ≤ c_D`.

The final section instantiates this for the right-angled Coxeter group of
`RequestProject/ChamberDescent.lean`, with `D` the descent set `D(w)`: by
`FiniteChains.RACG.rdesc_rel` the descent set is a simplex of `L`, and by
`FiniteChains.RACG.exists_rdesc` it is nonempty for `w ≠ 1`, so the attaching subcomplex of the
chamber `F_w` is contractible.
-/

namespace FiniteChains
namespace Mirror

universe u

variable {V : Type u} [DecidableEq V]

/-- The simplices of `L` that meet `D`: the poset `𝒫_D` whose order complex is the union of the
mirrors `F_s`, `s ∈ D`. -/
def MeetPoset (L : Finset V → Prop) (D : Finset V) : Type u :=
  {σ : Finset V // L σ ∧ (σ ∩ D).Nonempty}

instance (L : Finset V → Prop) (D : Finset V) : PartialOrder (MeetPoset L D) :=
  Subtype.partialOrder _

@[simp] theorem MeetPoset.le_def {L : Finset V → Prop} {D : Finset V} (σ τ : MeetPoset L D) :
    σ ≤ τ ↔ σ.1 ⊆ τ.1 := Iff.rfl

/-! ### The union of mirrors is the order complex of `𝒫_D` -/

/-! ### Contractibility -/

variable {L : Finset V → Prop} {D : Finset V}

/-- The vertex `D` of the poset `𝒫_D`. -/
def top (hLD : L D) (hD : D.Nonempty) : MeetPoset L D :=
  ⟨D, hLD, by simpa using hD⟩

/-! ### The descent set of an element of a right-angled Coxeter group -/

section RACG

open RACG

variable [Fintype V] (A : CommRel V)

/-- The descent set `D(x) = {s : ℓ(xs) < ℓ(x)}` as a finite set of generators. -/
noncomputable def rdescFinset (x : CayGroup A) : Finset V := by
  classical
  exact Finset.univ.filter fun s => IsRDesc A x s

theorem mem_rdescFinset {x : CayGroup A} {s : V} :
    s ∈ rdescFinset A x ↔ IsRDesc A x s := by
  classical
  simp [rdescFinset]

/-- The simplices of `L`: the cliques of the commutation graph. -/
def IsSimplex (σ : Finset V) : Prop := ∀ s ∈ σ, ∀ r ∈ σ, s ≠ r → A.rel s r

omit [DecidableEq V] [Fintype V] in
theorem isSimplex_subset {σ τ : Finset V} (hστ : σ ⊆ τ) (hτ : IsSimplex A τ) :
    IsSimplex A σ := fun s hs r hr hsr => hτ s (hστ hs) r (hστ hr) hsr

/-- **The descent set is a simplex of `L`**, in the form needed by the chamber argument. -/
theorem isSimplex_rdescFinset (x : CayGroup A) : IsSimplex A (rdescFinset A x) := by
  intro s hs r hr hsr
  exact rdesc_rel A hsr ((mem_rdescFinset A).1 hs) ((mem_rdescFinset A).1 hr)

/-- **The descent set is nonempty** for `x ≠ 1`. -/
theorem rdescFinset_nonempty {x : CayGroup A} (hx : x ≠ 1) : (rdescFinset A x).Nonempty := by
  obtain ⟨s, hs⟩ := exists_rdesc A hx
  exact ⟨s, (mem_rdescFinset A).2 hs⟩

end RACG

end Mirror
end FiniteChains
