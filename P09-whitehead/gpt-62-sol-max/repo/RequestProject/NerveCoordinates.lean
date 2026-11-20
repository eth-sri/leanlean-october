module

public import RequestProject.NerveDegree
public import RequestProject.FinsuppBasis
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section

namespace FiniteChains.Nerve
open FreeAbelianGroup
universe u v
variable {P : Type u} {X : Type v}

/-- Regard a chain indexed by flags as a chain of vertex lists. -/
noncomputable def encode (e : X → List P) : (X →₀ ℤ) →ₗ[ℤ] Ch P :=
  Finsupp.linearCombination ℤ (fun x => of (e x))

/-- Extract the coefficients of the flags represented by a list embedding. -/
noncomputable def decode (e : X ↪ List P) : Ch P →ₗ[ℤ] (X →₀ ℤ) :=
  (Finsupp.lcomapDomain e e.injective).comp toFinsupp.toIntLinearMap

@[simp] theorem decode_of (e : X ↪ List P) (x : X) :
    decode e (of (e x)) = Finsupp.single x 1 := by
  simp [decode, Finsupp.comapDomain_single]

theorem decode_of_notMem (e : X ↪ List P) {l : List P} (h : l ∉ Set.range e) :
    decode e (of l) = 0 := by
  change Finsupp.lcomapDomain (R := ℤ) e e.injective (toFinsupp (of l)) = _
  rw [toFinsupp_of]
  exact Finsupp.comapDomain_single_of_not_mem_range h _ _

theorem decode_encode (e : X ↪ List P) (c : X →₀ ℤ) : decode e (encode e c) = c := by
  finsupp_basis c
  intro x
  simp [encode]

theorem encode_injective (e : X ↪ List P) : Function.Injective (encode e) :=
  (show Function.LeftInverse (decode e) (encode e) from decode_encode e).injective

theorem encode_decode [Preorder P] (e : X ↪ List P) (n : ℕ)
    (hlen : ∀ x, (e x).length = n)
    (hfull : ∀ l, List.IsChain (· ≤ ·) l → l.length = n → l ∈ Set.range e)
    {c : Ch P} (hc : c ∈ Inc P) : encode e (decode e c) = lengthProjection n c := by
  refine AddMonoidHom.eqOn_closure (f := ((encode e).comp (decode e)).toAddMonoidHom)
    (g := lengthProjection n) ?_ hc
  rintro _ ⟨l, hl, rfl⟩
  change encode e (decode e (of l)) = lengthProjection n (of l)
  by_cases h : l ∈ Set.range e
  · obtain ⟨x, rfl⟩ := h
    simp [encode, hlen]
  · have hn : l.length ≠ n := fun hn => h (hfull l hl hn)
    simp [decode_of_notMem e h, hn]

theorem map_decode_mem [Preorder P] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : X ↪ List P) (F : (X →₀ ℤ) →ₗ[ℤ] M) (S : Submodule ℤ M) {A : P → Prop}
    (hF : ∀ x, (∀ p ∈ e x, A p) → F (Finsupp.single x 1) ∈ S)
    {c : Ch P} (hc : c ∈ IncOn A) : F (decode e c) ∈ S := by
  refine map_mem_of_mem_closure (F.comp (decode e)).toAddMonoidHom (T := S.toAddSubgroup) ?_ hc
  rintro _ ⟨l, hl, rfl⟩
  change F (decode e (of l)) ∈ S
  by_cases h : l ∈ Set.range e
  · obtain ⟨x, rfl⟩ := h
    simpa only [decode_of] using hF x hl.2
  · simp [decode_of_notMem e h]

end FiniteChains.Nerve
