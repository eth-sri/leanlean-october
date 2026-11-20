module

public import RequestProject.OrderNerveDictionary
public import RequestProject.FinsuppBasis
public import RequestProject.NerveCoordinates

@[expose] public section

/-! Recover actual cellular two- and three-chains from homogeneous increasing nerve chains. -/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open FreeAbelianGroup
universe u
variable {P : Type u} [PartialOrder P]

def ordEdgeVertices : OrdEdge P ↪ List P :=
  ⟨fun t => [t.1.1, t.1.2], by
    rintro ⟨⟨a, b⟩, h⟩ ⟨⟨a', b'⟩, h'⟩ he
    simpa [OrdEdge, Subtype.mk.injEq, Prod.mk.injEq, List.cons.injEq] using he⟩

noncomputable def decodeOrdNerve1 : Nerve.Ch P →+ (OrdEdge P →₀ ℤ) :=
  (Nerve.decode ordEdgeVertices).toAddMonoidHom

theorem ordNerveChain1_injective : Function.Injective (ordNerveChain1 (P := P)) :=
  Nerve.encode_injective ordEdgeVertices

theorem ordNerveChain1_decode {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    ordNerveChain1 (decodeOrdNerve1 c) = Nerve.lengthProjection 2 c := by
  refine Nerve.encode_decode ordEdgeVertices 2 (fun _ => rfl) ?_ hc
  intro l hl hn
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hn
  exact ⟨⟨(a, b), by simpa [List.isChain_cons] using hl⟩, rfl⟩

def ordTriVertices : OrdTri P ↪ List P :=
  ⟨fun t => [t.1.1, t.1.2.1, t.1.2.2], by
    rintro ⟨⟨a, b, c⟩, h⟩ ⟨⟨a', b', c'⟩, h'⟩ he
    simpa [OrdTri, Subtype.mk.injEq, Prod.mk.injEq, List.cons.injEq] using he⟩

noncomputable def decodeOrdNerve2 : Nerve.Ch P →+ (OrdTri P →₀ ℤ) :=
  (Nerve.decode ordTriVertices).toAddMonoidHom

theorem decodeOrdNerve2_encode (c : OrdTri P →₀ ℤ) :
    decodeOrdNerve2 (ordNerveChain2 c) = c := Nerve.decode_encode ordTriVertices c

theorem ordNerveChain2_injective : Function.Injective (ordNerveChain2 (P := P)) :=
  Nerve.encode_injective ordTriVertices

theorem ordNerveChain2_decode {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    ordNerveChain2 (decodeOrdNerve2 c) = Nerve.lengthProjection 3 c := by
  refine Nerve.encode_decode ordTriVertices 3 (fun _ => rfl) ?_ hc
  intro l hl hn
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hn
  exact ⟨⟨(a, b, c), by simpa [List.isChain_cons] using hl⟩, rfl⟩

def ordTetVertices : OrdTet P ↪ List P :=
  ⟨fun t => [t.1.1, t.1.2.1, t.1.2.2.1, t.1.2.2.2], by
    rintro ⟨⟨a, b, c, d⟩, h⟩ ⟨⟨a', b', c', d'⟩, h'⟩ he
    simpa [OrdTet, Subtype.mk.injEq, Prod.mk.injEq, List.cons.injEq] using he⟩

noncomputable def decodeOrdNerve3 : Nerve.Ch P →+ (OrdTet P →₀ ℤ) :=
  (Nerve.decode ordTetVertices).toAddMonoidHom

theorem ordNerveChain3_decode {c : Nerve.Ch P} (hc : c ∈ Nerve.Inc P) :
    ordNerveChain3 (decodeOrdNerve3 c) = Nerve.lengthProjection 4 c := by
  refine Nerve.encode_decode ordTetVertices 4 (fun _ => rfl) ?_ hc
  intro l hl hn
  obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp hn
  exact ⟨⟨(a, b, c, d), by simpa [List.isChain_cons] using hl⟩, rfl⟩

/-- Zero nerve boundary is equivalent to the actual zero cellular boundary. -/
theorem ordNerveChain2_cycle_iff (c : OrdTri P →₀ ℤ) :
    Nerve.bdry (ordNerveChain2 c) = 0 ↔ bdry2 (orderCx P) c = 0 := by
  rw [← ordNerveChain1_bdry2]
  exact ⟨fun h => ordNerveChain1_injective (h.trans (map_zero _).symm),
    fun h => by rw [h, map_zero]⟩

theorem ordNerveChain2_lengthProjection (c : OrdTri P →₀ ℤ) :
    Nerve.lengthProjection 3 (ordNerveChain2 c) = ordNerveChain2 c := by
  classical
  finsupp_basis c
  intro t
  simp [ordNerveChain2]

theorem ordNerveChain2_mem_inc (c : OrdTri P →₀ ℤ) :
    ordNerveChain2 c ∈ Nerve.Inc P := by
  apply Finsupp.linearCombination_mem (T := (Nerve.Inc P).toIntSubmodule) _ c
  intro t
  apply Nerve.of_mem_inc
  simpa [List.isChain_cons] using t.2

/-- Triangles lying in a subposet, with all three vertices required to lie in it. -/
def ordTriOn (A : P → Prop) : Set (OrdTri P) :=
  {t | A t.1.1 ∧ A t.1.2.1 ∧ A t.1.2.2}

theorem decodeOrdNerve2_supported {A : P → Prop} {c : Nerve.Ch P}
    (hc : c ∈ Nerve.IncOn A) :
    decodeOrdNerve2 c ∈ Finsupp.supported ℤ ℤ (ordTriOn A) := by
  refine Nerve.map_decode_mem ordTriVertices LinearMap.id _ (fun t ht => ?_) hc
  exact Finsupp.single_mem_supported ℤ 1 (by simpa [ordTriVertices, ordTriOn] using ht)

end FiniteChains.Comb
