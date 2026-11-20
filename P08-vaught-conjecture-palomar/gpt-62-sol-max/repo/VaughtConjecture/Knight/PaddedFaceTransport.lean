/- Copyright (c) 2026 Cameron Freer. Released under the Apache 2.0 license. -/
module

public import VaughtConjecture.Knight.PaddedSourceTable
public import VaughtConjecture.Knight.PaddedInstallation
public import VaughtConjecture.Knight.FullFaceLifting
public import VaughtConjecture.Knight.CappedLiftComposition
public import VaughtConjecture.Knight.SeparatedLayerFace
public import VaughtConjecture.Knight.GradeCutLifting
public import VaughtConjecture.Knight.RelativeLadderGradeOneLift

@[expose] public section

namespace VaughtConjecture.Knight.Padded

open Transform Value ExtOrd CoatomBoundaryExtension

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {K : Spec A} {k : ℕ}

namespace Layer

variable (P : Layer K k)

def baseEquiv : K.base.below (A, 1) ≃ P.carrier.below (A, 1) :=
  CellScheme.belowEquivOfIndex P.baseMap P.base_mono.injective P.base_index (fun d hd => by
    rcases P.cases d with hb | ⟨_, hg, _⟩
    · tauto
    · exact (Nat.not_succ_le_self 1 (hg.trans hd.2)).elim)

theorem base_respects_iff (p : K.base.below (A, 1) → ExtOrd) :
    RespectsSemanticsBelow K.baseRows (A, 1) p ↔
      RespectsSemanticsBelow P.rows (A, 1) (p ∘ P.baseEquiv.symm) :=
  respects_iff_of_index_equiv P.baseEquiv (fun d => P.base_index d.1)
    (fun c d _ => (P.base_row c.1 d).symm) p

theorem base_pullback {q : Cell P.carrier → ExtOrd} (hq : RespectsSemantics P.rows q) :
    RespectsSemanticsBelow K.baseRows (A, 1) (fun d => q (P.baseMap d.1)) :=
  (iff_comp_symm P.baseEquiv.symm P.base_respects_iff _).mp (hq.toBelow _)

variable {n i : ℕ} {S : SemScheme n} {B : Finset ι} {e : Fin n ↪ ι} {he : Finset.univ.image e = B}
  (G : ExactSemanticFace (PointImageSemantics.rows S.scheme e he S.rows) K.boundaryRows) (hB : B ⊂ A)

/-- Pass from a native occurrence lift to the installed full-face clause. -/
theorem capped_face (hi : i ≤ k) (cut : ∀ d : Cell S.scheme, S.scheme.grade d ≤ i ↔ S.scheme.grade d ≤ k)
    (hl : PaddedFaceLift.Lift S.rows P.rows (P.faceAt S G hi)) :
    CappedLift P.rows (show GradedLe (B, k) (A, k) from ⟨hB.subset, le_rfl⟩) :=
  let L := P.face G hB.not_ge
  PaddedFaceLift.to_capped (L.fullEquiv cut) (fun p => (L.full_respects_iff cut p).mp) (fun _ => rfl) hl

/-- The grade-one clause uses the retained base on the very same carrier. -/
theorem capped_base (cut : ∀ d : Cell S.scheme, S.scheme.grade d ≤ i ↔ S.scheme.grade d ≤ 1)
    (hl : PaddedFaceLift.Lift S.rows K.baseRows
      (fun d : S.scheme.below (Finset.univ, i) => RelativeLadderLayer.prescribedAt K.boundary K.one
        (G.belowAmbient d.1 ((cut d.1).mp d.2.2)))) :
    CappedLift P.rows (show GradedLe (B, 1) (A, 1) from ⟨hB.subset, le_rfl⟩) :=
  let L := P.face G hB.not_ge
  PaddedFaceLift.to_capped_transport (L.fullEquiv cut) (fun p => (L.full_respects_iff cut p).mp)
    P.baseEquiv P.base_respects_iff (fun _ => rfl) hl

end Layer

namespace StepRows

variable (P : Layer K k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

def lowerEquiv (J : Finset ι × ℕ) (hJ : J.2 ≤ k) : P.carrier.below J ≃ (carrier P hnext).below J :=
  SourceLayerCarrier.inheritedEquiv P.carrier (K.Anchor (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext J (fun h => (Nat.not_succ_le_self k) (h.2.trans hJ))

theorem lower_pullback {J : Finset ι × ℕ} (hJ : J.2 ≤ k) {q : (carrier P hnext).below J → ExtOrd}
    (hq : RespectsSemanticsBelow (rows P hk hnext) J q) :
    RespectsSemanticsBelow P.rows J (q ∘ lowerEquiv P hnext J hJ) :=
  SeparatedSourceLayerCarrier.pullback_respects P.carrier (K.Anchor (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated (by omega)) (inherited_row P hk hnext)
    (fun h => (Nat.not_succ_le_self k) (h.2.trans hJ)) hq

theorem lower_lift {U V : Finset ι × ℕ} (h : GradedLe U V) (hv : V.2 ≤ k)
    (hl : CappedLift P.rows h) : CappedLift (rows P hk hnext) h :=
  SeparatedSourceLayerCarrier.lift P.carrier (K.Anchor (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated (by omega)) (inherited_row P hk hnext) h
    (fun he => (Nat.not_succ_le_self k) (he.2.trans hv)) hl

end StepRows

variable (L : Layer K 2) (t : ℕ) (ht : t + 2 ≤ A.card) (J : Finset ι × ℕ) (hJ : J.2 ≤ t + 2)

def buildEquiv : (r : ℕ) → (hr : t + r + 2 ≤ A.card) →
    (build L t ht).carrier.below J ≃ (build L (t + r) hr).carrier.below J
  | 0, _ => Equiv.refl _
  | r + 1, hr => (buildEquiv r (by omega)).trans
    (StepRows.lowerEquiv (build L (t + r) (by omega)) (by omega) J (by omega))

theorem build_pullback (r : ℕ) (hr : t + r + 2 ≤ A.card)
    {q : Cell (build L (t + r) hr).carrier → ExtOrd} (hq : RespectsSemantics (build L (t + r) hr).rows q) :
    RespectsSemanticsBelow (build L t ht).rows J (fun d => q (buildEquiv L t ht J hJ r hr d).1) := by
  suffices ∀ (p : (build L (t + r) hr).carrier.below J → ExtOrd),
      RespectsSemanticsBelow (build L (t + r) hr).rows J p →
        RespectsSemanticsBelow (build L t ht).rows J (p ∘ buildEquiv L t ht J hJ r hr) from this _ (hq.toBelow _)
  clear hq q
  induction r with
  | zero => exact fun _ h => h
  | succ r ih =>
    intro p hp
    exact ih (by omega) _ (StepRows.lower_pullback (build L (t + r) (by omega))
      (by omega) (by omega) (by omega) hp)

theorem buildEquiv_original (r : ℕ) (hr : t + r + 2 ≤ A.card) (d : K.boundary.below J) :
    (buildEquiv L t ht J hJ r hr
      ⟨(build L t ht).original d.1, by grind [Layer.original_index]⟩).1 =
      (build L (t + r) hr).original d.1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change StepRows.old (build L (t + r) (by omega)) (by omega)
      (buildEquiv L t ht J hJ r (by omega)
        ⟨(build L t ht).original d.1, by grind⟩).1 = _
    rw [ih]
    rfl

end

end VaughtConjecture.Knight.Padded
