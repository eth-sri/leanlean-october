import RequestProject.GenusCapSurfaceExtraction
import RequestProject.GenusApply
import RequestProject.PresPosetReading
import RequestProject.OrderCocycleChains
import RequestProject.Tac
noncomputable section


/-! Explicit integral characters separating the actual genus marking loops. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel
variable (q : ℕ) [NeZero q]

def characterRel : Empty ⊕ PUnit → FreeGroup (ℕ × Bool) := fun _ => 1
def characterA (h : ℕ) := (h, false)
def characterB (h : ℕ) := (h, true)
def characterGen (x : ℕ × Bool) : Multiplicative ((ℕ × Bool) →₀ ℤ) :=
  Multiplicative.ofAdd (Finsupp.single x 1)

omit [NeZero q] in
theorem characterRel_read (j : Empty ⊕ PUnit) :
    wordVal characterGen (genusW characterRel characterA characterB q j) = 1 := by
  obtain j | j := j
  · exact j.elim
  · rwd [genusW_inr, wordVal, mk_surfWord, map_commWord]
    simp [commWord, mul_comm]

def surfaceCharacterCocycle :
    OrdCocycle (NeSpx (cmpRel (GenusVertex q))) (Multiplicative ((ℕ × Bool) →₀ ℤ)) :=
  (presCoc _ characterGen
    (characterRel_read q)).pullback
      _
      (genusAtt characterRel characterA characterB q).monotone

/-- This explicit surface cocycle evaluates each actual marking to its distinct basis vector. -/
theorem surfaceCharacterCocycle_gSig (x : Fin q × Bool) :
    (surfaceCharacterCocycle q).readPath (gSig q (x.1.val, x.2)) =
      Multiplicative.ofAdd (Finsupp.single (x.1.val, x.2) 1) := by
  have h := (presCoc _ characterGen
    (characterRel_read q)).readPath_htpy
      (genus_hread characterRel characterA characterB q PUnit.unit.{1} (x.1.val, x.2))
  rwd [h]
  have hl : genusLw characterA characterB q PUnit.unit.{1} (x.1.val, x.2) =
      [((x.1.val, x.2), true)] := by
    cases' x with i b
    grind [genusLw, sLet, Nat.mod_eq_of_lt i.isLt, characterA, characterB, show (4 * i.val + 1) / 4 = i.val from by omega]
  rwd [hl]
  exact reading_genClass _ _ _ _

/-- Evaluating this character extracts precisely the coefficient of each actual cap face. -/
theorem surfaceCharacter_capSurfaceChain2 c
    x :
    (surfaceCharacterCocycle q).chain1 (capSurfaceChain2 q c) (x.1.val, x.2) =
      c (.inr x) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      simp_all
  | single f n =>
      rwd [capSurfaceChain2, Finsupp.linearCombination_single, LinearMap.map_smul]
      obtain f | z := f
      · aesop
      · rwd [OrdCocycle.chain1_pathChain, surfaceCharacterCocycle_gSig]
        change (n • Finsupp.single (z.1.val, z.2) (1)) (x.1.val, x.2) =
          (Finsupp.single (Sum.inr z) n) (Sum.inr x)
        simp [Finsupp.single_apply, Prod.ext_iff, Fin.ext_iff]

/-- Every actual capped-cover cycle has zero augmented coefficient on every cap face. -/
theorem cappedCoverCycle_cap_augmentation_zero c
    (hc : Comb.bdry2 (cappedTreeCover q) c = 0) x :
    Finsupp.mapDomain Prod.snd c (.inr x) = 0 := by
  cases' capSurfaceCycle_boundary q c hc with d hd
  have h := (surfaceCharacterCocycle q).chain1_bdry2 d
  rwd [hd] at h
  have he := congrArg (· (x.1.val, x.2)) h
  simpa [surfaceCharacter_capSurfaceChain2, Finsupp.zero_apply] using he
