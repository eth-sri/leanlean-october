import RequestProject.NerveUpperRetraction
import RequestProject.PosetCoverUpTransform
import RequestProject.PosetCoverRestriction
import RequestProject.Tac


/-! Deleting the whole inverse image of a free face preserves finite chain homology. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

theorem exists_freeFace_upper_retraction {C : Q → Prop} {s t}
    (ht : C t) (hst : s ≤ t) (hne : t ≠ s)
    (hunique : ∀ x, C x → s ≤ x → x ≠ s → x = t) :
    ∃ r : {x : Q // C x} → {x : Q // C x}, Monotone r ∧
      (∀ x, x ≤ r x) ∧ (∀ x, (r x).1 ≠ s) ∧ (∀ x, x.1 ≠ s → r x = x) := by
  classical
  let r : {x : Q // C x} → {x : Q // C x} :=
    fun x => if x.1 = s then ⟨t, ht⟩ else x
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x.1 = s
    · aesop
    · by_cases hy : y.1 = s
      · have hxs : x.1 ≤ s := hy ▸ hxy
        change (r x).1 ≤ (r y).1
        grind
      grind
  · aesop
  · grind
  grind

/-- The retraction is lifted in each sheet, so the full free-face fiber can be
deleted simultaneously even for an infinite or disconnected covering. -/
theorem cover_freeFace_homology {f : P → Q} (hf : IsPosetCover f)
    {C : Q → Prop} {s t} (ht : C t) (hst : s ≤ t) (hne : t ≠ s)
    (hunique : ∀ x, C x → s ≤ x → x ≠ s → x = t) :
    Nerve.AcyclicRelIn (fun p => C (f p)) (fun p => C (f p) ∧ f p ≠ s) ∧
      ∀ n, Nerve.ReflectsBoundsIn (fun p => C (f p)) (fun p => C (f p) ∧ f p ≠ s) n := by
  obtain ⟨r, hr, hir, hav, hfix⟩ := exists_freeFace_upper_retraction ht hst hne hunique
  let hfc := IsPosetCover.restriction f {x | C x} hf
  let ρ := hfc.upTransform r hir
  have hρ : Monotone ρ := hfc.upTransform_monotone r hr hir
  have hρge := hfc.le_upTransform r hir
  have hbase : ∀ p, C (f (ρ p).1) ∧ f (ρ p).1 ≠ s := by
    intro p
    refine ⟨(ρ p).2, ?_⟩
    have hp := congrArg Subtype.val (hfc.upTransform_spec r hir p).2
    change f (ρ p).1 = (r ⟨f p.1, p.2⟩).1 at hp
    simp_all
  have hρfix : ∀ p, (C (f p.1) ∧ f p.1 ≠ s) → ρ p = p := by
    intro p hp
    apply hfc.upTransform_fixed r hir p
    tauto
  have hnonempty : ∃ p, C (f p) := by
    cases' hf.surj t with p hp
    grind
  exact ⟨Nerve.acyclicRelIn_of_upper_retraction hnonempty ρ hρ hρge hbase,
    (Nerve.reflectsBoundsIn_of_retraction (by simp_all) ρ hρ hbase hρfix)⟩
