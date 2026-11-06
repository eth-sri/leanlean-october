import RequestProject.GenusSpinePresentation
import RequestProject.Tac
noncomputable section


/-! The genuine finite complex obtained by capping the marked surviving spine. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def cappedSpineCx : Complex2 where
  V := (markedSpineCx q).V
  E := (markedSpineCx q).E
  F := (markedSpineCx q).F ⊕ (Fin q × Bool)
  src := (markedSpineCx q).src
  tgt := (markedSpineCx q).tgt
  base := Sum.elim (markedSpineCx q).base (fun _ => markedSpineBase q)
  att := Sum.elim (markedSpineCx q).att (fun x => (markedSpineLoop q x).1)
  att_isLoop := by
    rintro (f | x)
    · exact (markedSpineCx q).att_isLoop f
    grind


def cappedSpineTree : SpanningTree (cappedSpineCx q) where
  root := (markedSpineTree q).root
  ht := (markedSpineTree q).ht
  isTree := (markedSpineTree q).isTree
  up := (markedSpineTree q).up
  ht_root := (markedSpineTree q).ht_root
  ht_eq_zero := (markedSpineTree q).ht_eq_zero
  up_src := (markedSpineTree q).up_src
  up_ht := (markedSpineTree q).up_ht
  isTree_iff := (markedSpineTree q).isTree_iff

/-- The capped presentation is precisely the cell presentation of the capped complex. -/
theorem cappedSpineTree_rel :
    SpanningTree.treeRel (cappedSpineTree q) = cappedSpinePresentation q := by
  funext f
  cases f <;> rfl

def cappedSpineIncl : Hom (markedSpineCx q) (cappedSpineCx q) where
  onV := id
  onE := id
  onF := Sum.inl
  src_onE _ := rfl
  tgt_onE _ := rfl
  base_onF _ := rfl
  att_onF f := by
    aesop
