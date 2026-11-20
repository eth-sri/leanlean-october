module

public import RequestProject.CmpNerve
public import RequestProject.OrderCocycleFlatSections

@[expose] public section

/-! Recover a nonabelian cocycle on a face poset from its actual subdivision. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
universe u v w
variable {P : Type u} [PartialOrder P] [DecidableEq P]
  {G : Type v} [Group G] (c : OrdCocycle (NeSpx (cmpRel P)) G)

theorem edgeHop_comp_htpy {a b d : P} (hab : a ≤ b) (hbd : b ≤ d) :
    Htpy (orderCx (NeSpx (cmpRel P))) (spx1 a) (spx1 d)
      (edgeHop hab ++ edgeHop hbd) (edgeHop (hab.trans hbd)) := by
  apply htpy_of_loop_nil ((isPath_edgeHop hab).append (isPath_edgeHop hbd))
    (isPath_edgeHop (hab.trans hbd))
  apply htpy_nil_of_star d (starCh_spx1 (hab.trans hbd))
  · exact ((isPath_edgeHop hab).append (isPath_edgeHop hbd)).append
      (isPath_revPath (isPath_edgeHop (hab.trans hbd)))
  · grind [pathIn_append, pathIn_edgeHop, pathIn_revPath]

noncomputable def barycentricCocycle : OrdCocycle P G where
  val a b := if h : a ≤ b then c.readPath (edgeHop h) else 1
  comp hab hbd := by
    simp only [dif_pos hab, dif_pos hbd, dif_pos (hab.trans hbd)]
    exact (c.readPath_append _ _).symm.trans (c.readPath_htpy (edgeHop_comp_htpy hab hbd))

variable {a b : P}

theorem barycentricCocycle_val (h : a ≤ b) :
    (barycentricCocycle c).val a b = c.readPath (edgeHop h) := by
  simp_all [barycentricCocycle, dif_pos]

theorem edgeHop_read_via (hab : a ≤ b) (σ : NeSpx (cmpRel P))
    (ha : a ∈ σ.1) (hb : b ∈ σ.1) :
    c.readPath (edgeHop hab) = c.val (spx1 a) σ * (c.val (spx1 b) σ)⁻¹ := by
  have hσ : spx2 hab ≤ σ := by
    intro x hx
    aesop
  rw [← c.comp (spx1_le_spx2_left hab) hσ,
    ← c.comp (spx1_le_spx2_right hab) hσ]
  simp [edgeHop, hop, OrdCocycle.readPath_cons, OrdCocycle.readPath_nil, OrdCocycle.readGerm_ordPos, OrdCocycle.readGerm_ordNeg, mul_one]

variable {Ω : Type w} [MulAction G Ω]

variable (s : P → Ω)

noncomputable def barycentricSection (σ : NeSpx (cmpRel P)) :=
  (c.val (spx1 (chainMax σ)) σ)⁻¹ • s (chainMax σ)

/-- A flat section on the original face poset gives a flat section on the
actual subdivision, not merely an agreement on selected generators. -/
theorem barycentricSection_flat
    (hs : (barycentricCocycle c).IsFlatSection s) :
    c.IsFlatSection (barycentricSection c s) := by
  intro σ τ hστ
  have hm : spx1 (chainMax σ) ≤ σ := by
    intro x hx
    simp_all [spx1_val, chainMax_mem]
  have hread := hs (chainMax_monotone hστ)
  rw [barycentricCocycle_val c (chainMax_monotone hστ),
    edgeHop_read_via c (chainMax_monotone hστ) τ
      (hστ (chainMax_mem σ)) (chainMax_mem τ)] at hread
  unfold barycentricSection
  grind [c.comp, mul_smul, inv_smul_smul]

theorem barycentricSection_spx1 (a : P) :
    barycentricSection c s (spx1 a) = s a := by
  simp [barycentricSection]

end FiniteChains.Davis
