module

public import RequestProject.QCubeFacetIndex
public import RequestProject.QCubeEdgeChainEmbedding
public import RequestProject.QCubeThreeSubdivision

@[expose] public section

/-! Actual codimension-two faces and their coordinate signs. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

variable (c : QCube A)

variable (a b : V)

def qCubeDoubleFacet (s t : ZMod 2) :=
  qCubeFacet (qCubeFacet c a s) b t

@[simp] theorem qCubeDoubleFacet_sgn_first (hne : a ≠ b)
    (s t : ZMod 2) : (qCubeDoubleFacet c a b s t).sgn a = s := by
  simp [qCubeDoubleFacet, qCubeFacet, hne]

@[simp] theorem qCubeDoubleFacet_sgn_second
    (s t : ZMod 2) : (qCubeDoubleFacet c a b s t).sgn b = t := by
  simp [qCubeDoubleFacet]

theorem qCubeDoubleFacet_signs_injective (hne : a ≠ b) :
    Function.Injective (fun i : ZMod 2 × ZMod 2 => qCubeDoubleFacet c a b i.1 i.2) := by
  intro ⟨s, t⟩ ⟨u, v⟩ h
  grind [qCubeDoubleFacet_sgn_first, qCubeDoubleFacet_sgn_second]

variable [LinearOrder V] (c : QThreeCube A)

abbrev QThreeCube.hi : V := c.dirs 0
abbrev QThreeCube.mid : V := c.dirs 1
abbrev QThreeCube.lo : V := c.dirs 2

theorem QThreeCube.mid_lt : c.mid < c.hi := c.antitone (by decide : (0 : Fin 3) < 1)
theorem QThreeCube.lo_lt : c.lo < c.mid := c.antitone (by decide : (1 : Fin 3) < 2)
theorem QThreeCube.directions : c.1.spx = {c.hi, c.mid, c.lo} := by
  ext v; constructor
  · intro hv
    obtain ⟨i, hi⟩ := c.dirs.surjective ⟨v, hv⟩
    have := congrArg Subtype.val hi
    fin_cases i <;> simp_all [hi, QThreeCube.hi, mid, lo]
  · simp only [Finset.mem_insert, Finset.mem_singleton]; rintro (rfl | rfl | rfl) <;> exact (c.dirs _).2

def qThreeEdgeCell (i : Fin 3 × ZMod 2 × ZMod 2) :=
  if i.1 = 0 then qCubeDoubleFacet c.1 c.hi c.mid i.2.1 i.2.2
  else if i.1 = 1 then qCubeDoubleFacet c.1 c.hi c.lo i.2.1 i.2.2
  else qCubeDoubleFacet c.1 c.mid c.lo i.2.1 i.2.2

theorem qThreeEdgeCell_spx (i : Fin 3 × ZMod 2 × ZMod 2) :
    (qThreeEdgeCell c i).spx = if i.1 = 0 then {c.lo} else if i.1 = 1 then {c.mid} else {c.hi} := by
  have := c.lo_lt
  have := c.mid_lt
  obtain ⟨e, s, t⟩ := i
  fin_cases e <;> ext x <;> simp [qThreeEdgeCell, qCubeDoubleFacet, qCubeFacet, c.directions] <;> grind

theorem qThreeEdgeCell_injective : Function.Injective (qThreeEdgeCell c) := by
  intro ⟨e, s, t⟩ ⟨f, a, b⟩ h
  have he := congrArg QCube.spx h
  rw [qThreeEdgeCell_spx, qThreeEdgeCell_spx] at he
  have h0 := c.mid_lt.ne'
  have h1 := c.lo_lt.ne'
  have h2 := (c.lo_lt.trans c.mid_lt).ne'
  fin_cases e <;> fin_cases f <;> first
    | exact congrArg (Prod.mk _) (qCubeDoubleFacet_signs_injective c.1 _ _ h0 h)
    | exact congrArg (Prod.mk _) (qCubeDoubleFacet_signs_injective c.1 _ _ h1 h)
    | exact congrArg (Prod.mk _) (qCubeDoubleFacet_signs_injective c.1 _ _ h2 h)
    | exfalso; simp_all

def qThreeEdge (i : Fin 3 × ZMod 2 × ZMod 2) : QEdge A :=
  ⟨qThreeEdgeCell c i, by obtain ⟨i, s, t⟩ := i; fin_cases i <;> simp [qThreeEdgeCell_spx]⟩

theorem qThreeEdge_injective : Function.Injective (qThreeEdge c) :=
  fun _ _ h => qThreeEdgeCell_injective c (congrArg Subtype.val h)

end FiniteChains.Davis
