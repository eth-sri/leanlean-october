import RequestProject.GenusCappedSpineHurewicz
import RequestProject.PresCockcroftDictionary
import RequestProject.Tac
noncomputable section


/-! The actual capped spine and the Fox complex of its genuine presentation agree. -/
bwd

namespace FiniteChains.Comb
open scoped Classical

 theorem coverCycles_cockcroft_iff {α J : Type} [Fintype α] [DecidableEq α] [Fintype J]
    (ρ : J → FreeGroup α) :
    (∀ c, bdry2 (univCover ρ) c = 0 →
      Finsupp.mapDomain Prod.snd c = 0) ↔ _root_.FiniteChains.IsCockcroft ρ := by
  constructor
  · intro h v hv j
    let c := (coords _ J).symm v
    have hcoords : coords _ J c = v := LinearEquiv.apply_symm_apply _ v
    have hcycle : bdry2 (univCover ρ) c = 0 := by
      apply (univCover_bdry2_eq_zero_iff ρ c).mpr
      aesop
    have ha := augQ_coords ρ c j
    simp_all
  · intro h c hc
    have hv := (univCover_bdry2_eq_zero_iff ρ c).mp hc
    apply Finsupp.ext
    intro j
    rw [← augQ_coords ρ c j]
    tauto
end FiniteChains.Comb

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
open scoped Classical
variable (q : ℕ) [NeZero q]

instance : Fintype (SpinePresentationGen q) := Fintype.ofFinite _
instance : Fintype (SpinePresentationRel q) := Fintype.ofFinite _
instance : Fintype (SpinePresentationRel q ⊕ (Fin q × Bool)) := Fintype.ofFinite _
