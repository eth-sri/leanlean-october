module

public import RequestProject.OrderComplexFreeFace
public import RequestProject.NerveUpperRetraction
public import RequestProject.PosetCoverUpTransform
public import RequestProject.PosetCoverRestriction

@[expose] public section

/-! Deleting the whole inverse image of a free face preserves finite chain homology. -/

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- The retraction is lifted in each sheet, so the full free-face fiber can be
deleted simultaneously even for an infinite or disconnected covering. -/
theorem cover_freeFace_homology {f : P → Q} (hf : IsPosetCover f)
    {C : Q → Prop} {s t : Q} (ht : C t) (hst : s ≤ t) (hne : t ≠ s)
    (hunique : ∀ x, C x → s ≤ x → x ≠ s → x = t) :
    Nerve.AcyclicRelIn (fun p => C (f p)) (fun p => C (f p) ∧ f p ≠ s) ∧
      ∀ n, Nerve.ReflectsBoundsIn (fun p => C (f p)) (fun p => C (f p) ∧ f p ≠ s) n := by
  obtain ⟨r, hr, hir, hav, hfix⟩ := exists_freeFace_upper_retraction ht hst hne hunique
  let hfc := IsPosetCover.restriction f {x | C x} hf
  let ρ := hfc.upTransform r hir
  have hρ := hfc.upTransform_monotone r hr hir
  have hbase : ∀ p, C (f (ρ p).1) ∧ f (ρ p).1 ≠ s := by
    intro p
    have hp := congrArg Subtype.val (hfc.upTransform_spec r hir p).2
    change f _ = (r _).1 at hp
    grind
  have hρfix : ∀ p, (C (f p.1) ∧ f p.1 ≠ s) → ρ p = p := by
    intro p hp
    apply hfc.upTransform_fixed r hir p
    exact hfix _ hp.2
  have hnonempty : ∃ p, C (f p) := by
    obtain ⟨p, hp⟩ := hf.surj t
    grind
  exact ⟨Nerve.acyclicRelIn_of_upper_retraction hnonempty ρ hρ (hfc.le_upTransform r hir) hbase,
    fun n => Nerve.reflectsBoundsIn_of_retraction (fun _ h => h.1) ρ hρ hbase hρfix n⟩

end FiniteChains.Comb
