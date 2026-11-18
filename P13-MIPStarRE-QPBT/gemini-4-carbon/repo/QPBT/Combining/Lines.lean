module

public import QPBT.Combining.Points
public import QPBT.Combining.ErrorBounds
public import QPBT.Combining.Witnesses
public import QPBT.Combining.DirectLowDegreeCore
public import QPBT.Games.RestrictedAverage
public import QPBT.Games.DistributionAux
public import QPBT.Games.DistributionMarginals
public import QPBT.Games.Sandwich.Defs
public import QPBT.Games.Sandwich.Pasting.Heterogeneous
public import QPBT.Games.Sandwich.Pasting.Assembly
public import QPBT.Games.Sandwich.Pasting.SchmidtMirror
public import QPBT.Games.Sandwich.Support
public import QPBT.Games.ErrorFunctions
public import QPBT.Observables.LineDefs
public import QPBT.Observables.WinImplications.Setup
public import QPBT.Observables.WinImplications.LowDegree
public import QPBT.Algebra.Coefficients
public import QPBT.ExplicitConstants
public import MIPStarRE.LDT.Basic.DistributionAvg
public import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkCore

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-! ## Section 1: Pair-state consistency transport and opposite-placement positivity -/

namespace ProjectiveSetting

theorem consistencyDefect_pairState_eq_AA'_BA''
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    {Sample Outcome : Type*} [Fintype Sample] [DecidableEq Sample]
    [Fintype Outcome] [DecidableEq Outcome]
    (law : Distribution Sample)
    (first : Sample → Measurement Outcome (S.ExpandedLocalSpace .alice))
    (second : Sample → Measurement Outcome (S.ExpandedLocalSpace .bob)) :
    consistencyDefect law
        (fun s a => heteroKron ((first s).effect a) 1)
        (fun s a => heteroKron 1 ((second s).effect a))
        (ExtendedLineGame.pairState S) =
      consistencyDefect law
        (fun s a => S.place .AA' ((first s).effect a))
        (fun s a => S.place .BA'' ((second s).effect a))
        S.psiHat := by
  unfold consistencyDefect
  refine avgOver_congr _ _ _ fun s => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a = b
  · simp [h]
  · simp only [if_neg h]
    change stateQForm (ExtendedLineGame.pairState S)
        (heteroKron ((first s).effect a) 1 * heteroKron 1 ((second s).effect b)) =
      stateQForm S.psiHat (S.place .AA' ((first s).effect a) * S.place .BA'' ((second s).effect b))
    rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
    exact ExtendedLineGame.stateQForm_pairState_eq_AA'_BA'' S _ _
      (Matrix.nonneg_iff_posSemidef.mp ((first s).pos a)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp ((second s).pos b)).isHermitian

theorem consistencyDefect_pairState_eq_AB''_BB'
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    {Sample Outcome : Type*} [Fintype Sample] [DecidableEq Sample]
    [Fintype Outcome] [DecidableEq Outcome]
    (law : Distribution Sample)
    (first : Sample → Measurement Outcome (S.ExpandedLocalSpace .alice))
    (second : Sample → Measurement Outcome (S.ExpandedLocalSpace .bob)) :
    consistencyDefect law
        (fun s a => heteroKron ((first s).effect a) 1)
        (fun s a => heteroKron 1 ((second s).effect a))
        (ExtendedLineGame.pairState S) =
      consistencyDefect law
        (fun s a => S.place .AB'' ((first s).effect a))
        (fun s a => S.place .BB' ((second s).effect a))
        S.psiHat := by
  unfold consistencyDefect
  refine avgOver_congr _ _ _ fun s => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a = b
  · simp [h]
  · simp only [if_neg h]
    change stateQForm (ExtendedLineGame.pairState S)
        (heteroKron ((first s).effect a) 1 * heteroKron 1 ((second s).effect b)) =
      stateQForm S.psiHat (S.place .AB'' ((first s).effect a) * S.place .BB' ((second s).effect b))
    rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
    exact ExtendedLineGame.stateQForm_pairState_eq_AB''_BB' S _ _
      (Matrix.nonneg_iff_posSemidef.mp ((first s).pos a)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp ((second s).pos b)).isHermitian

theorem place_mul_place_nonneg {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
    (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂)
    {X : Op (S.ExpandedLocalSpace p₁.side)} {Y : Op (S.ExpandedLocalSpace p₂.side)}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ S.place p₁ X * S.place p₂ Y :=
  Commute.mul_nonneg (S.place_nonneg p₁ hX) (S.place_nonneg p₂ hY) (S.place_comm p₁ p₂ hopp X Y)

end ProjectiveSetting

theorem consistencyDefect_integrand_nonneg {P : AdmissibleParams} {ε : ℝ}
    {α : Type*} [Fintype α] [DecidableEq α] (S : ProjectiveSetting P ε)
    (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂)
    (M₁ : Measurement α (S.ExpandedLocalSpace p₁.side))
    (M₂ : Measurement α (S.ExpandedLocalSpace p₂.side)) :
    0 ≤ ∑ a : α, ∑ b : α,
      if a = b then 0
      else (inner ℂ S.psiHat
        ((EuclideanSpace.equiv (SixReg P S.toStrategy.ιA S.toStrategy.ιB) ℂ).symm
          ((S.place p₁ (M₁.effect a) * S.place p₂ (M₂.effect b)).mulVec S.psiHat))).re := by
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  by_cases h : a = b
  · rw [if_pos h]
  · rw [if_neg h]
    exact stateQForm_nonneg S.psiHat (S.place_mul_place_nonneg p₁ p₂ hopp (M₁.pos a) (M₂.pos b))

theorem consistencyDefect_integrand_le_one {P : AdmissibleParams} {ε : ℝ}
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (S : ProjectiveSetting P ε) (p1 p2 : Placement) (hopp : p1.IsOpposite p2)
    (first : Measurement Outcome (S.ExpandedLocalSpace p1.side))
    (second : Measurement Outcome (S.ExpandedLocalSpace p2.side)) :
    (∑ answer : Outcome, ∑ other : Outcome,
      if answer = other then 0 else stateQForm S.psiHat
        (S.place p1 (first.effect answer) * S.place p2 (second.effect other))) ≤ 1 := by
  have h := point_defect_eq (S.placedMeasurement p1 first) (S.placedMeasurement p2 second) S.psiHat
  simp only [ProjectiveSetting.placedMeasurement_effect, S.psiHat_norm, one_pow] at h
  rw [h]
  have hdiag : 0 ≤ ∑ a : Outcome, stateQForm S.psiHat
      (S.place p1 (first.effect a) * S.place p2 (second.effect a)) :=
    Finset.sum_nonneg fun a _ => stateQForm_nonneg _
      (S.place_mul_place_nonneg p1 p2 hopp (first.pos a) (second.pos a))
  linarith

/-! ## Section 2: Restricted line-point mixtures, error inflation, and lineRepMap uniformity -/

theorem clDistribution_seedEvent_mass (L : LdParams) (i : Fin L.m)
    (CL : LdSpace L → LdSpace L) (hseed : ∀ z : LdSpace L, (CL z).seed = z.seed) :
    ∑ sample ∈ (clDistribution CL (ldPointCL L)).support.filter (restrictedLineSeedEvent L i),
      (clDistribution CL (ldPointCL L)).weight sample = 1 / (L.m : ℝ) := by
  classical
  haveI : Nonempty (ScalarQ L) := ⟨0⟩
  haveI : Nonempty (Fin L.m) := Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  rw [Distribution.sum_filter_weight_eq_avgOver]
  unfold clDistribution
  rw [Distribution.avgOver_map]
  have hpt (z : LdSpace L) :
      (if restrictedLineSeedEvent L i (CL z, ldPointCL L z) then (1 : ℝ) else 0) =
        if chiIndex L z.seed = i then 1 else 0 := by
    by_cases h : chiIndex L z.seed = i
    · rw [if_pos h, if_pos (by change chiIndex L (CL z).seed = i; rw [hseed z]; exact h)]
    · rw [if_neg h, if_neg (by change ¬ chiIndex L (CL z).seed = i; rw [hseed z]; exact h)]
  have hchi : (uniformDistribution (LdSpace L)).map (fun z : LdSpace L => chiIndex L z.seed) =
      uniformDistribution (Fin L.m) := by
    rw [← Distribution.map_map (uniformDistribution (LdSpace L)) (fun z => LdSpace.seed z) (chiIndex L),
      uniformDistribution_map_ldSeed, uniformDistribution_map_chiIndex]
  rw [avgOver_congr _ _ _ hpt,
    ← Distribution.avgOver_map (uniformDistribution (LdSpace L)) (fun z => chiIndex L z.seed)
      (fun j : Fin L.m => if j = i then (1 : ℝ) else 0), hchi]
  unfold avgOver
  simp [uniformDistribution_weight_apply, mul_ite]

theorem aLinePointDist_eq_bind_restricted (L : LdParams) :
    aLinePointDist L = Distribution.bind (uniformDistribution (Fin L.m)) (restrictedALineDist L) := by
  classical
  haveI : Nonempty (Fin L.m) := Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  have hmix := Distribution.bind_uniform_restrict_eq
    (clDistribution (ldALineCL L) (ldPointCL L)) (restrictedLineSeedEvent L)
    (restrictedALineSeedEvent_positive L)
    (fun i => by rw [clDistribution_seedEvent_mass L i (ldALineCL L) fun _ => rfl, Fintype.card_fin])
    (fun s => ⟨chiIndex L (LdSpace.seed s.1), rfl, fun _ hi => hi.symm⟩)
  rw [aLinePointDist, ← hmix, Distribution.bind_map]; rfl

theorem dLinePointDist_eq_bind_restricted (L : LdParams) :
    dLinePointDist L = Distribution.bind (uniformDistribution (Fin L.m)) (restrictedDLineDist L) := by
  classical
  haveI : Nonempty (Fin L.m) := Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one L.hm)
  have hmix := Distribution.bind_uniform_restrict_eq
    (clDistribution (ldDLineCL L) (ldPointCL L)) (restrictedLineSeedEvent L)
    (restrictedDLineSeedEvent_positive L)
    (fun i => by rw [clDistribution_seedEvent_mass L i (ldDLineCL L) fun _ => rfl, Fintype.card_fin])
    (fun s => ⟨chiIndex L (LdSpace.seed s.1), rfl, fun _ hi => hi.symm⟩)
  rw [dLinePointDist, ← hmix, Distribution.bind_map]; rfl

theorem avgOver_restrictedLinePointDist_le {P : AdmissibleParams}
    (f : (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) → ℝ)
    (hf : ∀ sample, 0 ≤ f sample) (kind : LineKind) (i : Fin P.m) :
    avgOver (restrictedLinePointDist P kind i) f ≤
      2 * (P.m : ℝ) * avgOver (linePointDist P.toLdParams) f := by
  classical
  haveI : Nonempty (Fin P.m) := Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one P.one_le_m)
  have hm : (0 : ℝ) < (P.m : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one P.one_le_m
  have hA0 := avgOver_nonneg (aLinePointDist P.toLdParams) f hf
  have hD0 := avgOver_nonneg (dLinePointDist P.toLdParams) f hf
  have hsum : 2 * avgOver (linePointDist P.toLdParams) f =
      avgOver (aLinePointDist P.toLdParams) f + avgOver (dLinePointDist P.toLdParams) f := by
    rw [linePointDist, WinImplications.avgOver_mix]; ring
  have hcomp (ν : Fin P.m → Distribution (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)))
      (μ : Distribution (LineDesc P.toLdParams × (Fin P.m → PauliScalar P)))
      (hbind : μ = Distribution.bind (uniformDistribution (Fin P.m)) ν)
      (hle : avgOver μ f ≤ 2 * avgOver (linePointDist P.toLdParams) f) :
      avgOver (ν i) f ≤ 2 * (P.m : ℝ) * avgOver (linePointDist P.toLdParams) f := by
    have hc := avgOver_bind_uniform_component_le ν f hf i
    rw [Fintype.card_fin, ← hbind, div_mul_eq_mul_div, one_mul, div_le_iff₀ hm, mul_comm] at hc
    exact hc.trans ((mul_le_mul_of_nonneg_left hle hm.le).trans_eq (by ring))
  cases kind
  · exact hcomp _ _ (aLinePointDist_eq_bind_restricted P.toLdParams) (by linarith)
  · exact hcomp _ _ (dLinePointDist_eq_bind_restricted P.toLdParams) (by linarith)

theorem avgOver_prod_restrictedLinePointDist_le {P : AdmissibleParams}
    (f : ((LineDesc P.toLdParams × (Fin P.m → PauliScalar P)) ×
      (LineDesc P.toLdParams × (Fin P.m → PauliScalar P))) → ℝ)
    (hf : ∀ sample, 0 ≤ f sample) (kindX kindZ : LineKind) (i j : Fin P.m) :
    avgOver (Distribution.prod (restrictedLinePointDist P kindX i)
        (restrictedLinePointDist P kindZ j)) f ≤
      4 * (P.m : ℝ) ^ 2 * avgOver (Distribution.prod
        (linePointDist P.toLdParams) (linePointDist P.toLdParams)) f := by
  rw [SandwichProduct.avgOver_distribution_prod, SandwichProduct.avgOver_distribution_prod]
  refine (avgOver_mono _ _ _ fun s1 =>
    avgOver_restrictedLinePointDist_le (fun s2 => f (s1, s2)) (fun s2 => hf (s1, s2)) kindZ j).trans ?_
  rw [avgOver_const_mul]
  exact (mul_le_mul_of_nonneg_left
    (avgOver_restrictedLinePointDist_le _ (fun s1 => avgOver_nonneg _ _ fun s2 => hf (s1, s2)) kindX i)
    (by positivity)).trans_eq (by ring)

theorem uniformDistribution_map_lineRepMap_add_smul {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] {m : ℕ} (v : Fin m → K) :
    (uniformDistribution ((Fin m → K) × K)).map (fun w => lineRepMap v w.1 + w.2 • v) =
      uniformDistribution (Fin m → K) := by
  refine uniformDistribution_map_of_card_fiber _ (Fintype.card K) fun x => ?_
  by_cases hv : v = 0
  · subst hv
    have hzero (u : Fin m → K) : lineRepMap (0 : Fin m → K) u = u := by
      have h := sub_lineRepMap_mem_span (0 : Fin m → K) u
      rw [show Submodule.span K ({0} : Set (Fin m → K)) = ⊥ by simp, Submodule.mem_bot, sub_eq_zero] at h
      exact h.symm
    have hfilt : ((Finset.univ : Finset ((Fin m → K) × K)).filter
        fun w => lineRepMap (0 : Fin m → K) w.1 + w.2 • (0 : Fin m → K) = x) =
        ({x} : Finset (Fin m → K)) ×ˢ (Finset.univ : Finset K) := by
      ext ⟨u, c⟩; simp [hzero, eq_comm]
    rw [hfilt, Finset.card_product]; simp
  · have hinj : Function.Injective (fun c : K => (lineRepMap v x + c • v, directLineRepParameter v x)) := by
      intro c₁ c₂ hc
      have hsub : (c₁ - c₂) • v = 0 := by rw [sub_smul, show c₁ • v = c₂ • v by simpa using congrArg Prod.fst hc, sub_self]
      exact (smul_eq_zero.mp hsub).elim sub_eq_zero.mp fun h => absurd h hv
    have himg : ((Finset.univ : Finset ((Fin m → K) × K)).filter fun w => lineRepMap v w.1 + w.2 • v = x) =
        (Finset.univ : Finset K).image (fun c => (lineRepMap v x + c • v, directLineRepParameter v x)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hw
        have hrep : lineRepMap v w.1 = lineRepMap v x := by rw [← hw, lineRepMap_add_smul, lineRepMap_apply_self]
        have ht : directLineRepParameter v x = w.2 :=
          directLineRepParameter_eq_of_nonzero hv (by rw [← hrep]; exact hw.symm)
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span v w.1)
        exact ⟨c, Prod.ext (by rw [← hrep, hc]; abel) ht⟩
      · rintro ⟨c, rfl⟩
        change lineRepMap v (lineRepMap v x + c • v) + directLineRepParameter v x • v = x
        rw [lineRepMap_add_smul, lineRepMap_apply_self]
        exact (directLineRepParameter_spec v x).symm
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]

theorem avgOver_uniform_lineRepMap_resample_parameter {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] {m : ℕ} (v : Fin m → K)
    (value : (Fin m → K) → (Fin m → K) → ℝ) :
    avgOver (uniformDistribution (Fin m → K)) (fun point => value (lineRepMap v point) point) =
      avgOver (uniformDistribution (Fin m → K)) (fun point =>
        avgOver (uniformDistribution K) (fun param =>
          value (lineRepMap v point) (lineRepMap v point + param • v))) := by
  have havg := congrArg (fun dist => avgOver dist (fun point => value (lineRepMap v point) point))
    (uniformDistribution_map_lineRepMap_add_smul v)
  rw [Distribution.avgOver_map, uniformDistribution_prod, SandwichProduct.avgOver_distribution_prod] at havg
  simpa only [lineRepMap_add_smul, lineRepMap_apply_self] using havg.symm

/-! ## Section 3: Coordinate blocks and the sub-line witness -/

theorem projX_add {K : Type*} [AddCommMonoid K] {m : ℕ} (u v : Fin (2 * m + 2) → K) :
    projX (u + v) = projX u + projX v := rfl
theorem projZ_add {K : Type*} [AddCommMonoid K] {m : ℕ} (u v : Fin (2 * m + 2) → K) :
    projZ (u + v) = projZ u + projZ v := rfl
theorem projX_smul {K : Type*} [Monoid K] {m : ℕ} (t : K) (u : Fin (2 * m + 2) → K) :
    projX (t • u) = t • projX u := rfl
theorem projZ_smul {K : Type*} [Monoid K] {m : ℕ} (t : K) (u : Fin (2 * m + 2) → K) :
    projZ (t • u) = t • projZ u := rfl

theorem embX_val (m : ℕ) (i : Fin m) : (embX m i).val = i.val := rfl
theorem embZ_val (m : ℕ) (i : Fin m) : (embZ m i).val = m + i.val := rfl
theorem alphaVar_val (m : ℕ) : (alphaVar m).val = 2 * m := by simp [alphaVar, finCombineEquiv]
theorem betaVar_val (m : ℕ) : (betaVar m).val = 2 * m + 1 := by simp [betaVar, finCombineEquiv]

theorem projX_coordinateDirection_embX {K : Type*} [Field K] {m : ℕ} (i : Fin m) :
    projX (coordinateDirection (embX m i) : Fin (2 * m + 2) → K) = coordinateDirection i := by
  funext j
  have hinj : Function.Injective (embX m) := fun a b h => by simpa using (finCombineEquiv m).symm.injective h
  simp [projX, coordinateDirection, Pi.single_apply, hinj.eq_iff]

theorem projX_coordinateDirection_embZ {K : Type*} [Field K] {m : ℕ} (i : Fin m) :
    projX (coordinateDirection (embZ m i) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embX m j ≠ embZ m i := fun h => by simpa using (finCombineEquiv m).symm.injective h
  simp [projX, coordinateDirection, hne]

theorem projX_coordinateDirection_alphaVar {K : Type*} [Field K] {m : ℕ} :
    projX (coordinateDirection (alphaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embX m j ≠ alphaVar m := fun h => by simpa using (finCombineEquiv m).symm.injective h
  simp [projX, coordinateDirection, hne]

theorem projX_coordinateDirection_betaVar {K : Type*} [Field K] {m : ℕ} :
    projX (coordinateDirection (betaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embX m j ≠ betaVar m := fun h => by simpa using (finCombineEquiv m).symm.injective h
  simp [projX, coordinateDirection, hne]

theorem projZ_coordinateDirection_embZ {K : Type*} [Field K] {m : ℕ} (i : Fin m) :
    projZ (coordinateDirection (embZ m i) : Fin (2 * m + 2) → K) = coordinateDirection i := by
  funext j
  have hinj : Function.Injective (embZ m) := fun a b h => by simpa using (finCombineEquiv m).symm.injective h
  simp [projZ, coordinateDirection, Pi.single_apply, hinj.eq_iff]

theorem projZ_coordinateDirection_embX {K : Type*} [Field K] {m : ℕ} (i : Fin m) :
    projZ (coordinateDirection (embX m i) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embZ m j ≠ embX m i := fun h => by simpa using (finCombineEquiv m).symm.injective h
  simp [projZ, coordinateDirection, hne]

theorem projZ_coordinateDirection_alphaVar {K : Type*} [Field K] {m : ℕ} :
    projZ (coordinateDirection (alphaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embZ m j ≠ alphaVar m := fun h => by simpa using (finCombineEquiv m).symm.injective h
  simp [projZ, coordinateDirection, hne]

theorem projZ_coordinateDirection_betaVar {K : Type*} [Field K] {m : ℕ} :
    projZ (coordinateDirection (betaVar m) : Fin (2 * m + 2) → K) = 0 := by
  funext j
  have hne : embZ m j ≠ betaVar m := fun h => by simpa using (finCombineEquiv m).symm.injective h
  simp [projZ, coordinateDirection, hne]

theorem directPointToPauli_coordinateDirection (P : AdmissibleParams) (k : Fin P.extendedDirectLd.m) :
    directPointToPauli P (coordinateDirection k) = coordinateDirection k := by
  change Fin (2 * P.m + 2) at k
  funext j
  by_cases h : k = j
  · subst j
    change extendedDirectScalarEquiv P ((Pi.single k 1 : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) k) =
      (Pi.single k 1 : Fin (2 * P.m + 2) → PauliScalar P) k
    rw [Pi.single_eq_same, map_one]
  · change extendedDirectScalarEquiv P ((Pi.single k 1 : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) j) =
      (Pi.single k 1 : Fin (2 * P.m + 2) → PauliScalar P) j
    rw [Pi.single_eq_of_ne (Ne.symm h), map_zero]

theorem directPointToPauli_add (P : AdmissibleParams)
    (u v : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    directPointToPauli P (u + v) = directPointToPauli P u + directPointToPauli P v :=
  funext fun i => map_add (extendedDirectScalarEquiv P) (u i) (v i)

theorem directPointToPauli_smul (P : AdmissibleParams)
    (t : DirectScalarQ P.extendedDirectLd)
    (u : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
    directPointToPauli P (t • u) = extendedDirectScalarEquiv P t • directPointToPauli P u :=
  funext fun i => map_mul (extendedDirectScalarEquiv P) t (u i)

theorem uniformDistribution_map_projX_projZ_pauli (P : AdmissibleParams) :
    (uniformDistribution (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)).map
        (fun u => (projX (directPointToPauli P u), projZ (directPointToPauli P u))) =
      Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
        (uniformDistribution (Fin P.m → PauliScalar P)) := by
  classical
  let eExt : (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) ≃
      ((Fin P.m → DirectScalarQ P.extendedDirectLd) × (Fin P.m → DirectScalarQ P.extendedDirectLd)) ×
        (Fin 2 → DirectScalarQ P.extendedDirectLd) :=
    (Equiv.arrowCongr (finCombineEquiv P.m) (Equiv.refl _)).trans
      ((Equiv.sumArrowEquivProdArrow _ _ _).trans
        (Equiv.prodCongr (Equiv.sumArrowEquivProdArrow _ _ _) (Equiv.refl _)))
  let eBlk : (Fin P.m → DirectScalarQ P.extendedDirectLd) ≃ (Fin P.m → PauliScalar P) :=
    Equiv.piCongrRight fun _ => (extendedDirectScalarEquiv P).toEquiv
  have h1 : (uniformDistribution (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)).map
      (fun u => (projX u, projZ u)) =
      Distribution.prod (uniformDistribution (Fin P.m → DirectScalarQ P.extendedDirectLd))
        (uniformDistribution (Fin P.m → DirectScalarQ P.extendedDirectLd)) := by
    have hf : (fun u => (projX u, projZ u)) = fun u => (eExt u).1 := funext fun u => Prod.ext rfl rfl
    rw [hf, ← Distribution.map_map _ eExt Prod.fst, uniformDistribution_map_equiv,
      uniformDistribution_map_fst, uniformDistribution_prod]
  have hfun : (fun u : Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd =>
      (projX (directPointToPauli P u), projZ (directPointToPauli P u))) =
      fun u => (Equiv.prodCongr eBlk eBlk) (projX u, projZ u) := rfl
  rw [hfun, ← Distribution.map_map _ (fun u => (projX u, projZ u)), h1,
    ← uniformDistribution_prod, uniformDistribution_map_equiv, uniformDistribution_prod]

theorem aLineDescOf_ldALineCL (L : LdParams) (z : LdSpace L) :
    aLineDescOf L (ldALineCL L z) = aLineDescOf L z := by
  have hcongr {b b' : Fin L.m → ScalarQ L} {s : ScalarQ L} (hb : b = b')
      (h1 : lineRepMap (coordinateDirection (chiIndex L s)) b = b)
      (h1' : lineRepMap (coordinateDirection (chiIndex L s)) b' = b') :
      LineDesc.axis b s h1 = LineDesc.axis b' s h1' := by subst hb; rfl
  exact hcongr (lineRepMap_apply_self _ _) _ _

theorem dLineDescOf_ldDLineCL (L : LdParams) (z : LdSpace L) :
    dLineDescOf L (ldDLineCL L z) = dLineDescOf L z := by
  have hcongr {b b' d d' : Fin L.m → ScalarQ L} {s : ScalarQ L} (hb : b = b') (hd : d = d')
      (h1 : lineRepMap d b = b) (h2 : ∀ j : Fin L.m, j.val < (chiIndex L s).val → d j = 0)
      (h1' : lineRepMap d' b' = b') (h2' : ∀ j : Fin L.m, j.val < (chiIndex L s).val → d' j = 0) :
      LineDesc.diagonal b s d h1 h2 = LineDesc.diagonal b' s d' h1' h2' := by subst hb; subst hd; rfl
  have hd : prefixProjection (chiIndex L (LdSpace.seed (ldDLineCL L z))) (LdSpace.direction (ldDLineCL L z)) =
      prefixProjection (chiIndex L (LdSpace.seed z)) (LdSpace.direction z) :=
    prefixProjection_idempotent _ _
  have hp : lineRepMap (prefixProjection (chiIndex L (LdSpace.seed (ldDLineCL L z))) (LdSpace.direction (ldDLineCL L z)))
      (LdSpace.point (ldDLineCL L z)) =
      lineRepMap (prefixProjection (chiIndex L (LdSpace.seed z)) (LdSpace.direction z)) (LdSpace.point z) := by
    rw [hd]; exact lineRepMap_apply_self _ _
  exact hcongr hp hd _ _ _ _

def ldSpaceBlockEquiv (L : LdParams) :
    LdSpace L ≃ (Fin L.m → ScalarQ L) × (ScalarQ L × (Fin L.m → ScalarQ L)) where
  toFun z := (LdSpace.point z, LdSpace.seed z, LdSpace.direction z)
  invFun w := fun i => match i with
    | .inl (.inl j) => w.1 j
    | .inl (.inr _) => w.2.1
    | .inr j => w.2.2 j
  left_inv z := by funext i; rcases i with (j | u) | j <;> rfl
  right_inv _ := rfl

def ldSeedIndexEvent (L : LdParams) (i : Fin L.m) (s : ScalarQ L) : Prop :=
  chiIndex L s = i

instance ldSeedIndexEvent_decidablePred (L : LdParams) (i : Fin L.m) :
    DecidablePred (ldSeedIndexEvent L i) := fun _ => by unfold ldSeedIndexEvent; infer_instance

theorem ldSeedIndexEvent_positive (L : LdParams) (i : Fin L.m) :
    0 < ∑ s ∈ (uniformDistribution (ScalarQ L)).support.filter (ldSeedIndexEvent L i),
      (uniformDistribution (ScalarQ L)).weight s := by
  refine Finset.sum_pos' (fun a _ => (uniformDistribution (ScalarQ L)).nonnegative a)
    ⟨seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩,
      Finset.mem_filter.mpr ⟨by simp, chiIndex_seedOfIndexResidue L i _⟩, ?_⟩
  simp only [uniformDistribution, Distribution.uniformOnFinset_weight, Finset.mem_univ, if_true]
  positivity

noncomputable def subLineSeedDist (P : AdmissibleParams) (i : Fin P.m) :
    Distribution (ScalarQ P.toLdParams) :=
  Distribution.restrict (uniformDistribution (ScalarQ P.toLdParams))
    (ldSeedIndexEvent P.toLdParams i) (ldSeedIndexEvent_positive P.toLdParams i)

theorem subLineSeedDist_isProbability (P : AdmissibleParams) (i : Fin P.m) :
    (subLineSeedDist P i).IsProbability :=
  Distribution.restrict_isProbability _ _ (ldSeedIndexEvent_positive P.toLdParams i)

noncomputable def subLineSourceLine (P : AdmissibleParams) (kind : LineKind)
    (b : Fin P.m → PauliScalar P) (s : ScalarQ P.toLdParams)
    (d : Fin P.m → PauliScalar P) : LineDesc P.toLdParams :=
  match kind with
  | .axis => aLineDescOf P.toLdParams ((ldSpaceBlockEquiv P.toLdParams).symm (b, (s, d)))
  | .diagonal => dLineDescOf P.toLdParams ((ldSpaceBlockEquiv P.toLdParams).symm (b, (s, d)))

theorem restrictedLinePointDist_eq_map_prod (P : AdmissibleParams)
    (kind : LineKind) (i : Fin P.m) :
    restrictedLinePointDist P kind i =
      (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
          (Distribution.prod (subLineSeedDist P i)
            (uniformDistribution (Fin P.m → PauliScalar P)))).map
        (fun w => (subLineSourceLine P kind w.1 w.2.1 w.2.2, w.1)) := by
  let L := P.toLdParams
  haveI : Nonempty (Fin L.m) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one L.hm⟩⟩
  letI : DecidablePred (fun z : LdSpace L => ldSeedIndexEvent L i (LdSpace.seed z)) :=
    fun z => inferInstanceAs (Decidable (ldSeedIndexEvent L i (LdSpace.seed z)))
  letI : DecidablePred (fun sw : ScalarQ L × (Fin L.m → ScalarQ L) => ldSeedIndexEvent L i sw.1) :=
    fun sw => inferInstanceAs (Decidable (ldSeedIndexEvent L i sw.1))
  have hposZ : 0 < ∑ z ∈ (uniformDistribution (LdSpace L)).support.filter
      (fun z => ldSeedIndexEvent L i (LdSpace.seed z)),
      (uniformDistribution (LdSpace L)).weight z := by
    refine Finset.sum_pos' (fun a _ => (uniformDistribution (LdSpace L)).nonnegative a)
      ⟨(fun _ => seedOfIndexResidue L i ⟨0, L.seedFiberCard_pos⟩),
        Finset.mem_filter.mpr ⟨by simp, chiIndex_seedOfIndexResidue L i _⟩, ?_⟩
    simp only [uniformDistribution, Distribution.uniformOnFinset_weight, Finset.mem_univ, if_true]; positivity
  have hposSW : 0 < ∑ sw ∈ (uniformDistribution (ScalarQ L × (Fin L.m → ScalarQ L))).support.filter
      (fun sw => ldSeedIndexEvent L i sw.1),
      (uniformDistribution (ScalarQ L × (Fin L.m → ScalarQ L))).weight sw := by
    have hmap : (uniformDistribution (ScalarQ L × (Fin L.m → ScalarQ L))).map (fun sw => chiIndex L sw.1) =
        uniformDistribution (Fin L.m) := by
      rw [← Distribution.map_map _ Prod.fst (chiIndex L), uniformDistribution_map_fst, uniformDistribution_map_chiIndex]
    rw [Distribution.sum_filter_weight_eq_avgOver]
    dsimp only [ldSeedIndexEvent]
    rw [← Distribution.avgOver_map (uniformDistribution (ScalarQ L × (Fin L.m → ScalarQ L)))
        (fun sw => chiIndex L sw.1) (fun j : Fin L.m => if j = i then (1 : ℝ) else 0), hmap]
    unfold avgOver
    simp only [uniformDistribution_support, uniformDistribution_weight_apply, mul_ite, mul_one, mul_zero,
      ← Finset.sum_filter, Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton, Fintype.card_fin]
    have hLm : (0 : ℝ) < L.m := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one L.hm
    exact one_div_pos.mpr hLm
  have hblk : (Distribution.restrict (uniformDistribution (LdSpace L))
      (fun z => ldSeedIndexEvent L i (LdSpace.seed z)) hposZ).map (ldSpaceBlockEquiv L) =
      Distribution.prod (uniformDistribution (Fin L.m → ScalarQ L))
        (Distribution.prod (subLineSeedDist P i) (uniformDistribution (Fin L.m → ScalarQ L))) := by
    have heq := uniformDistribution_map_equiv (ldSpaceBlockEquiv L)
    have hprod : 0 < ∑ w ∈ (uniformDistribution ((Fin L.m → ScalarQ L) × (ScalarQ L × (Fin L.m → ScalarQ L)))).support.filter
        (fun w => ldSeedIndexEvent L i w.2.1),
        (uniformDistribution ((Fin L.m → ScalarQ L) × (ScalarQ L × (Fin L.m → ScalarQ L)))).weight w := by
      rw [uniformDistribution_snd_event_mass (p := fun sw : ScalarQ L × (Fin L.m → ScalarQ L) => ldSeedIndexEvent L i sw.1)]
      exact hposSW
    have hposA : 0 < ∑ w ∈ ((uniformDistribution (LdSpace L)).map (ldSpaceBlockEquiv L)).support.filter
        (fun w => ldSeedIndexEvent L i w.2.1), ((uniformDistribution (LdSpace L)).map (ldSpaceBlockEquiv L)).weight w := by
      rw [heq]; exact hprod
    rw [← Distribution.restrict_map (uniformDistribution (LdSpace L)) (ldSpaceBlockEquiv L)
        (fun w => ldSeedIndexEvent L i w.2.1) (fun z => ldSeedIndexEvent L i (LdSpace.seed z)) (fun _ => Iff.rfl) hposA hposZ,
      Distribution.restrict_congr heq (fun w => ldSeedIndexEvent L i w.2.1) hposA hprod,
      restrict_uniform_prod_snd (fun sw : ScalarQ L × (Fin L.m → ScalarQ L) => ldSeedIndexEvent L i sw.1) hposSW hprod,
      restrict_uniform_prod_fst (ldSeedIndexEvent L i) (ldSeedIndexEvent_positive L i) hposSW]
    rfl
  cases kind
  · dsimp only [restrictedLinePointDist]
    have hpos : 0 < ∑ s ∈ ((uniformDistribution (LdSpace L)).map (fun z => (ldALineCL L z, ldPointCL L z))).support.filter
        (restrictedLineSeedEvent L i),
        ((uniformDistribution (LdSpace L)).map (fun z => (ldALineCL L z, ldPointCL L z))).weight s := by
      simpa only [clDistribution] using restrictedALineSeedEvent_positive L i
    have h1 : restrictedALineDist L i = (Distribution.restrict (uniformDistribution (LdSpace L))
        (fun z => ldSeedIndexEvent L i (LdSpace.seed z)) hposZ).map
        (fun z => (aLineDescOf L z, LdSpace.point z)) := by
      unfold restrictedALineDist restrictedALinePreDist clDistribution
      rw [Distribution.restrict_map _ _ (restrictedLineSeedEvent L i)
        (fun z => ldSeedIndexEvent L i (LdSpace.seed z)) (fun _ => Iff.rfl) hpos hposZ,
        Distribution.map_map]
      exact congrArg _ (funext fun z => by rw [aLineDescOf_ldALineCL]; rfl)
    rw [h1, ← hblk, Distribution.map_map]
    exact congrArg _ (funext fun z => by
      dsimp only [subLineSourceLine]
      rw [(ldSpaceBlockEquiv L).symm_apply_apply]; rfl)
  · dsimp only [restrictedLinePointDist]
    have hpos : 0 < ∑ s ∈ ((uniformDistribution (LdSpace L)).map (fun z => (ldDLineCL L z, ldPointCL L z))).support.filter
        (restrictedLineSeedEvent L i),
        ((uniformDistribution (LdSpace L)).map (fun z => (ldDLineCL L z, ldPointCL L z))).weight s := by
      simpa only [clDistribution] using restrictedDLineSeedEvent_positive L i
    have h1 : restrictedDLineDist L i = (Distribution.restrict (uniformDistribution (LdSpace L))
        (fun z => ldSeedIndexEvent L i (LdSpace.seed z)) hposZ).map
        (fun z => (dLineDescOf L z, LdSpace.point z)) := by
      unfold restrictedDLineDist restrictedDLinePreDist clDistribution
      rw [Distribution.restrict_map _ _ (restrictedLineSeedEvent L i)
        (fun z => ldSeedIndexEvent L i (LdSpace.seed z)) (fun _ => Iff.rfl) hpos hposZ,
        Distribution.map_map]
      exact congrArg _ (funext fun z => by rw [dLineDescOf_ldDLineCL]; rfl)
    rw [h1, ← hblk, Distribution.map_map]
    exact congrArg _ (funext fun z => by
      dsimp only [subLineSourceLine]
      rw [(ldSpaceBlockEquiv L).symm_apply_apply]; rfl)

theorem exists_subLineWitness (P : AdmissibleParams) :
    Nonempty (SubLineWitness P) := by
  let fstIdx : Fin P.m := ⟨0, lt_of_lt_of_le Nat.zero_lt_one P.one_le_m⟩
  let xIdx (k : Fin (2 * P.m + 2)) : Fin P.m := if h : k.val < P.m then ⟨k.val, h⟩ else fstIdx
  let zIdx (k : Fin (2 * P.m + 2)) : Fin P.m :=
    if h : P.m ≤ k.val ∧ k.val < 2 * P.m then ⟨k.val - P.m, by omega⟩ else fstIdx
  let extDir (kind : LineKind) (k : Fin (2 * P.m + 2))
      (w : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
      Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd :=
    match kind with
    | .axis => coordinateDirection k
    | .diagonal => directPrefixProjection (D := P.extendedDirectLd) k w
  let srcDir (kind : LineKind) (i : Fin P.m) (v : Fin P.m → PauliScalar P) : Fin P.m → PauliScalar P :=
    match kind with
    | .axis => coordinateDirection i
    | .diagonal => prefixProjection (P := P.toLdParams) i v
  let extLineOf (kind : LineKind) (s : DirectLdSpace P.extendedDirectLd) : DirectLineDesc P.extendedDirectLd :=
    match kind with
    | .axis => directALineDescOf P.extendedDirectLd s
    | .diagonal => directDLineDescOf P.extendedDirectLd s
  let PtDir := (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) ×
    (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
  let SData := PtDir × (ScalarQ P.toLdParams × ScalarQ P.toLdParams)
  let tripleOf (kind : LineKind) (k : Fin (2 * P.m + 2)) (w : SData) : SubLineTriple P :=
    (extLineOf kind ⟨w.1.1, k, w.1.2⟩,
      (subLineSourceLine P kind (projX (directPointToPauli P w.1.1)) w.2.1 (projX (directPointToPauli P w.1.2)),
       subLineSourceLine P kind (projZ (directPointToPauli P w.1.1)) w.2.2 (projZ (directPointToPauli P w.1.2))))
  let sampDist : Distribution (Fin (2 * P.m + 2) × SData) :=
    Distribution.bind (uniformDistribution (Fin (2 * P.m + 2))) fun k =>
      (Distribution.prod (uniformDistribution PtDir)
        (Distribution.prod (subLineSeedDist P (xIdx k)) (subLineSeedDist P (zIdx k)))).map fun w => (k, w)
  let branchDist (kind : LineKind) : Distribution (SubLineTriple P) :=
    sampDist.map fun w => tripleOf kind w.1 w.2
  let sDist : Distribution (SubLineTriple P) :=
    Distribution.bind (uniformDistribution (Fin 2)) ![branchDist .axis, branchDist .diagonal]
  -- Coordinate cases & span inclusions
  have hcases (k : Fin (2 * P.m + 2)) :
      (∃ i : Fin P.m, k = embX P.m i) ∨ (∃ j : Fin P.m, k = embZ P.m j) ∨ k = alphaVar P.m ∨ k = betaVar P.m := by
    rcases lt_or_ge k.val P.m with hk | hk
    · exact Or.inl ⟨⟨k.val, hk⟩, Fin.ext (embX_val P.m ⟨k.val, hk⟩).symm⟩
    · rcases lt_or_ge k.val (2 * P.m) with hk2 | hk2
      · exact Or.inr (Or.inl ⟨⟨k.val - P.m, by omega⟩, Fin.ext (by rw [embZ_val]; change k.val = P.m + (k.val - P.m); omega)⟩)
      · have := k.isLt
        rcases Nat.lt_or_ge k.val (2 * P.m + 1) with hk4 | hk4
        · exact Or.inr (Or.inr (Or.inl (Fin.ext (by rw [alphaVar_val]; omega))))
        · exact Or.inr (Or.inr (Or.inr (Fin.ext (by rw [betaVar_val]; omega))))
  have hxSpan (kind : LineKind) (k : Fin (2 * P.m + 2))
      (w : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
      projX (directPointToPauli P (extDir kind k w)) ∈
        Submodule.span (PauliScalar P) ({srcDir kind (xIdx k) (projX (directPointToPauli P w))} : Set _) := by
    rcases hcases k with ⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl <;> cases kind
    · have hx : xIdx (embX P.m i) = i := by
        dsimp [xIdx]; rw [dif_pos (by rw [embX_val]; exact i.isLt)]; exact Fin.ext (embX_val P.m i)
      rw [hx]; dsimp [extDir, srcDir]
      rw [congrArg projX (directPointToPauli_coordinateDirection P (embX P.m i)), projX_coordinateDirection_embX]
      exact Submodule.mem_span_singleton_self _
    · have hx : xIdx (embX P.m i) = i := by
        dsimp [xIdx]; rw [dif_pos (by rw [embX_val]; exact i.isLt)]; exact Fin.ext (embX_val P.m i)
      rw [hx]; dsimp [extDir, srcDir]
      have hp : projX (directPointToPauli P (directPrefixProjection (D := P.extendedDirectLd) (embX P.m i) w)) =
          prefixProjection (P := P.toLdParams) i (projX (directPointToPauli P w)) := by
        funext a
        change extendedDirectScalarEquiv P (if (embX P.m a).val < (embX P.m i).val then 0 else w (embX P.m a)) =
          if a.val < i.val then 0 else extendedDirectScalarEquiv P (w (embX P.m a))
        rw [embX_val, embX_val]; split_ifs <;> simp
      rw [hp]; exact Submodule.mem_span_singleton_self _
    · dsimp [extDir]; rw [congrArg projX (directPointToPauli_coordinateDirection P (embZ P.m j)), projX_coordinateDirection_embZ]
      exact Submodule.zero_mem _
    · dsimp [extDir]
      have hp : projX (directPointToPauli P (directPrefixProjection (D := P.extendedDirectLd) (embZ P.m j) w)) = 0 := by
        funext a; have := a.isLt
        change extendedDirectScalarEquiv P (if (embX P.m a).val < (embZ P.m j).val then 0 else _) = (0 : PauliScalar P)
        rw [embX_val, embZ_val, if_pos (by omega), map_zero]
      rw [hp]; exact Submodule.zero_mem _
    · dsimp [extDir]; rw [congrArg projX (directPointToPauli_coordinateDirection P (alphaVar P.m)), projX_coordinateDirection_alphaVar]
      exact Submodule.zero_mem _
    · dsimp [extDir]
      have hp : projX (directPointToPauli P (directPrefixProjection (D := P.extendedDirectLd) (alphaVar P.m) w)) = 0 := by
        funext a; have := a.isLt
        change extendedDirectScalarEquiv P (if (embX P.m a).val < (alphaVar P.m).val then 0 else _) = (0 : PauliScalar P)
        rw [embX_val, alphaVar_val, if_pos (by omega), map_zero]
      rw [hp]; exact Submodule.zero_mem _
    · dsimp [extDir]; rw [congrArg projX (directPointToPauli_coordinateDirection P (betaVar P.m)), projX_coordinateDirection_betaVar]
      exact Submodule.zero_mem _
    · dsimp [extDir]
      have hp : projX (directPointToPauli P (directPrefixProjection (D := P.extendedDirectLd) (betaVar P.m) w)) = 0 := by
        funext a; have := a.isLt
        change extendedDirectScalarEquiv P (if (embX P.m a).val < (betaVar P.m).val then 0 else _) = (0 : PauliScalar P)
        rw [embX_val, betaVar_val, if_pos (by omega), map_zero]
      rw [hp]; exact Submodule.zero_mem _
  have hzSpan (kind : LineKind) (k : Fin (2 * P.m + 2))
      (w : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) :
      projZ (directPointToPauli P (extDir kind k w)) ∈
        Submodule.span (PauliScalar P) ({srcDir kind (zIdx k) (projZ (directPointToPauli P w))} : Set _) := by
    rcases hcases k with ⟨i, rfl⟩ | ⟨j, rfl⟩ | rfl | rfl <;> cases kind
    · dsimp [extDir]; rw [congrArg projZ (directPointToPauli_coordinateDirection P (embX P.m i)), projZ_coordinateDirection_embX]
      exact Submodule.zero_mem _
    · have hz : zIdx (embX P.m i) = fstIdx := by
        dsimp [zIdx]; rw [dif_neg (by rw [embX_val]; have := i.isLt; omega)]
      rw [hz]; dsimp [extDir, srcDir]
      have hp : projZ (directPointToPauli P (directPrefixProjection (D := P.extendedDirectLd) (embX P.m i) w)) =
          prefixProjection (P := P.toLdParams) fstIdx (projZ (directPointToPauli P w)) := by
        funext a; have := i.isLt
        change extendedDirectScalarEquiv P (if (embZ P.m a).val < (embX P.m i).val then 0 else w (embZ P.m a)) =
          if a.val < 0 then 0 else extendedDirectScalarEquiv P (w (embZ P.m a))
        rw [embZ_val, embX_val, if_neg (by omega), if_neg (by omega)]
      rw [hp]; exact Submodule.mem_span_singleton_self _
    · have hz : zIdx (embZ P.m j) = j := by
        have := j.isLt; dsimp [zIdx]; rw [dif_pos (by rw [embZ_val]; omega)]
        exact Fin.ext (by change (embZ P.m j).val - P.m = j.val; rw [embZ_val]; omega)
      rw [hz]; dsimp [extDir, srcDir]
      rw [congrArg projZ (directPointToPauli_coordinateDirection P (embZ P.m j)), projZ_coordinateDirection_embZ]
      exact Submodule.mem_span_singleton_self _
    · have hz : zIdx (embZ P.m j) = j := by
        have := j.isLt; dsimp [zIdx]; rw [dif_pos (by rw [embZ_val]; omega)]
        exact Fin.ext (by change (embZ P.m j).val - P.m = j.val; rw [embZ_val]; omega)
      rw [hz]; dsimp [extDir, srcDir]
      have hp : projZ (directPointToPauli P (directPrefixProjection (D := P.extendedDirectLd) (embZ P.m j) w)) =
          prefixProjection (P := P.toLdParams) j (projZ (directPointToPauli P w)) := by
        funext a
        change extendedDirectScalarEquiv P (if (embZ P.m a).val < (embZ P.m j).val then 0 else w (embZ P.m a)) =
          if a.val < j.val then 0 else extendedDirectScalarEquiv P (w (embZ P.m a))
        rw [embZ_val, embZ_val]
        by_cases h : a.val < j.val
        · rw [if_pos (by omega), if_pos h, map_zero]
        · rw [if_neg (by omega), if_neg h]
      rw [hp]; exact Submodule.mem_span_singleton_self _
    · dsimp [extDir]; rw [congrArg projZ (directPointToPauli_coordinateDirection P (alphaVar P.m)), projZ_coordinateDirection_alphaVar]
      exact Submodule.zero_mem _
    · dsimp [extDir]
      have hp : projZ (directPointToPauli P (directPrefixProjection (D := P.extendedDirectLd) (alphaVar P.m) w)) = 0 := by
        funext a; have := a.isLt
        change extendedDirectScalarEquiv P (if (embZ P.m a).val < (alphaVar P.m).val then 0 else _) = (0 : PauliScalar P)
        rw [embZ_val, alphaVar_val, if_pos (by omega), map_zero]
      rw [hp]; exact Submodule.zero_mem _
    · dsimp [extDir]; rw [congrArg projZ (directPointToPauli_coordinateDirection P (betaVar P.m)), projZ_coordinateDirection_betaVar]
      exact Submodule.zero_mem _
    · dsimp [extDir]
      have hp : projZ (directPointToPauli P (directPrefixProjection (D := P.extendedDirectLd) (betaVar P.m) w)) = 0 := by
        funext a; have := a.isLt
        change extendedDirectScalarEquiv P (if (embZ P.m a).val < (betaVar P.m).val then 0 else _) = (0 : PauliScalar P)
        rw [embZ_val, betaVar_val, if_pos (by omega), map_zero]
      rw [hp]; exact Submodule.zero_mem _
  -- LineRep invariance on blocks
  have hrepX (v x : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
      (dX : Fin P.m → PauliScalar P)
      (hd : projX (directPointToPauli P v) ∈ Submodule.span (PauliScalar P) ({dX} : Set _)) :
      lineRepMap dX (projX (directPointToPauli P (lineRepMap v x))) =
        lineRepMap dX (projX (directPointToPauli P x)) := by
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span v x)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd
    have hx : x = lineRepMap v x + t • v := by rw [ht]; abel
    have hst : projX (directPointToPauli P x) =
        projX (directPointToPauli P (lineRepMap v x)) + (extendedDirectScalarEquiv P t * c) • dX := by
      conv_lhs => rw [hx]
      rw [directPointToPauli_add, directPointToPauli_smul, projX_add, projX_smul, ← hc]; module
    rw [hst, lineRepMap_add_smul]
  have hrepZ (v x : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
      (dZ : Fin P.m → PauliScalar P)
      (hd : projZ (directPointToPauli P v) ∈ Submodule.span (PauliScalar P) ({dZ} : Set _)) :
      lineRepMap dZ (projZ (directPointToPauli P (lineRepMap v x))) =
        lineRepMap dZ (projZ (directPointToPauli P x)) := by
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (sub_lineRepMap_mem_span v x)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hd
    have hx : x = lineRepMap v x + t • v := by rw [ht]; abel
    have hst : projZ (directPointToPauli P x) =
        projZ (directPointToPauli P (lineRepMap v x)) + (extendedDirectScalarEquiv P t * c) • dZ := by
      conv_lhs => rw [hx]
      rw [directPointToPauli_add, directPointToPauli_smul, projZ_add, projZ_smul, ← hc]; module
    rw [hst, lineRepMap_add_smul]
  have hsrcDir (kind : LineKind) (b : Fin P.m → PauliScalar P) (s : ScalarQ P.toLdParams) (d : Fin P.m → PauliScalar P) :
      (subLineSourceLine P kind b s d).direction = srcDir kind (chiIndex P.toLdParams s) d := by cases kind <;> rfl
  have hsrcBase (kind : LineKind) (b : Fin P.m → PauliScalar P) (s : ScalarQ P.toLdParams) (d : Fin P.m → PauliScalar P) :
      (subLineSourceLine P kind b s d).base = lineRepMap (srcDir kind (chiIndex P.toLdParams s) d) b := by cases kind <;> rfl
  have hextDir (kind : LineKind) (k : Fin (2 * P.m + 2)) (w : SData) :
      (tripleOf kind k w).1.direction = extDir kind k w.1.2 := by cases kind <;> rfl
  have hextBase (kind : LineKind) (k : Fin (2 * P.m + 2)) (w : SData) :
      (tripleOf kind k w).1.base = lineRepMap (extDir kind k w.1.2) w.1.1 := by cases kind <;> rfl
  have hsupp {sample : SubLineTriple P} (hs : sample ∈ sDist.support) :
      ∃ (kind : LineKind) (k : Fin (2 * P.m + 2)) (w : SData),
        chiIndex P.toLdParams w.2.1 = xIdx k ∧ chiIndex P.toLdParams w.2.2 = zIdx k ∧ sample = tripleOf kind k w := by
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (show sample ∈ (uniformDistribution (Fin 2)).support.biUnion _ from hs)
    obtain ⟨kind, hkind⟩ : ∃ kind : LineKind, sample ∈ (branchDist kind).support := by
      fin_cases c
      · exact ⟨.axis, by simpa using hc⟩
      · exact ⟨.diagonal, by simpa using hc⟩
    obtain ⟨kw, hkw, hkw'⟩ := Finset.mem_image.mp hkind
    obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp (show kw ∈ (uniformDistribution _).support.biUnion _ from hkw)
    obtain ⟨w, hw, hw'⟩ := Finset.mem_image.mp hk
    obtain ⟨-, hseeds⟩ := Finset.mem_product.mp hw
    obtain ⟨hsx, hsz⟩ := Finset.mem_product.mp hseeds
    exact ⟨kind, k, w, (Finset.mem_filter.mp hsx).2, (Finset.mem_filter.mp hsz).2, by rw [← hkw', ← hw']⟩
  have hsampProb : sampDist.IsProbability :=
    Distribution.bind_isProbability _ _ (uniformDistribution_isProbability _) fun k _ =>
      Distribution.IsProbability.map (Distribution.prod_isProbability _ _ (uniformDistribution_isProbability _)
        (Distribution.prod_isProbability _ _ (subLineSeedDist_isProbability P _) (subLineSeedDist_isProbability P _))) _
  -- Joint projected marginal for one branch & coordinate
  have hjoint (kind : LineKind) (k : Fin (2 * P.m + 2)) :
      (Distribution.prod (Distribution.prod (uniformDistribution PtDir)
          (Distribution.prod (subLineSeedDist P (xIdx k)) (subLineSeedDist P (zIdx k))))
        (uniformDistribution (DirectScalarQ P.extendedDirectLd))).map
        (fun p => ((tripleOf kind k p.1).2,
          (projX (directPointToPauli P ((tripleOf kind k p.1).1.base + p.2 • (tripleOf kind k p.1).1.direction)),
           projZ (directPointToPauli P ((tripleOf kind k p.1).1.base + p.2 • (tripleOf kind k p.1).1.direction))))) =
      (Distribution.prod
        (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
          (Distribution.prod (subLineSeedDist P (xIdx k)) (uniformDistribution (Fin P.m → PauliScalar P))))
        (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
          (Distribution.prod (subLineSeedDist P (zIdx k)) (uniformDistribution (Fin P.m → PauliScalar P))))).map
        (fun w => ((subLineSourceLine P kind w.1.1 w.1.2.1 w.1.2.2,
          subLineSourceLine P kind w.2.1 w.2.2.1 w.2.2.2), (w.1.1, w.2.1))) := by
    have hsrcCongr (b b' : Fin P.m → PauliScalar P) (s : ScalarQ P.toLdParams) (d : Fin P.m → PauliScalar P)
        (h : lineRepMap (srcDir kind (chiIndex P.toLdParams s) d) b =
          lineRepMap (srcDir kind (chiIndex P.toLdParams s) d) b') :
        subLineSourceLine P kind b s d = subLineSourceLine P kind b' s d := by
      cases kind
      · dsimp only [subLineSourceLine, aLineDescOf]
        exact (show ∀ (p p' : Fin P.m → PauliScalar P) (eqp : p = p') h1 h2,
          LineDesc.axis p s h1 = LineDesc.axis p' s h2 by intro p p' eqp h1 h2; subst eqp; rfl) _ _ h _ _
      · dsimp only [subLineSourceLine, dLineDescOf]
        exact (show ∀ (p p' : Fin P.m → PauliScalar P) (eqp : p = p') h1 h2 h3 h4,
          LineDesc.diagonal p s _ h1 h2 = LineDesc.diagonal p' s _ h3 h4 by
            intro p p' eqp h1 h2 h3 h4; subst eqp; rfl) _ _ h _ _ _ _
    have hshuf : Distribution.prod (Distribution.prod (uniformDistribution PtDir)
          (Distribution.prod (subLineSeedDist P (xIdx k)) (subLineSeedDist P (zIdx k))))
          (uniformDistribution (DirectScalarQ P.extendedDirectLd)) =
        (Distribution.prod
          (Distribution.prod (uniformDistribution (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd))
            (Distribution.prod (subLineSeedDist P (xIdx k)) (subLineSeedDist P (zIdx k))))
          (Distribution.prod (uniformDistribution (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd))
            (uniformDistribution (DirectScalarQ P.extendedDirectLd)))).map
          (fun w => (((w.2.1, w.1.1), w.1.2), w.2.2)) := by
      dsimp only [PtDir]
      rw [uniformDistribution_prod (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
        (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)]
      refine (Distribution.map_bijective_eq _ _
        (fun w : (((Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) × (ScalarQ P.toLdParams × ScalarQ P.toLdParams)) ×
          ((Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) × DirectScalarQ P.extendedDirectLd)) =>
          (((w.2.1, w.1.1), w.1.2), w.2.2))
        (fun u : ((((Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) ×
          (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)) ×
          (ScalarQ P.toLdParams × ScalarQ P.toLdParams)) × DirectScalarQ P.extendedDirectLd) =>
          ((u.1.1.2, u.1.2), (u.1.1.1, u.2)))
        (fun _ => rfl) (fun _ => rfl) ?_ ?_).symm
      · intro a; simp only [Distribution.prod_support, Finset.mem_product]; tauto
      · intro a; simp only [Distribution.prod_weight]; ring
    have hpp2 :
        (Distribution.prod
          (Distribution.prod (uniformDistribution (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd))
            (Distribution.prod (subLineSeedDist P (xIdx k)) (subLineSeedDist P (zIdx k))))
          (uniformDistribution (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd))).map
          (fun w => ((subLineSourceLine P kind (projX (directPointToPauli P w.2)) w.1.2.1 (projX (directPointToPauli P w.1.1)),
              subLineSourceLine P kind (projZ (directPointToPauli P w.2)) w.1.2.2 (projZ (directPointToPauli P w.1.1))),
            (projX (directPointToPauli P w.2), projZ (directPointToPauli P w.2)))) =
        (Distribution.prod
          (Distribution.prod
            (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P)) (uniformDistribution (Fin P.m → PauliScalar P)))
            (Distribution.prod (subLineSeedDist P (xIdx k)) (subLineSeedDist P (zIdx k))))
          (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P)) (uniformDistribution (Fin P.m → PauliScalar P)))).map
          (fun w => ((subLineSourceLine P kind w.2.1 w.1.2.1 w.1.1.1,
              subLineSourceLine P kind w.2.2 w.1.2.2 w.1.1.2), (w.2.1, w.2.2))) := by
      rw [← uniformDistribution_map_projX_projZ_pauli,
        Distribution.prod_map_left (uniformDistribution (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd))
          (Distribution.prod (subLineSeedDist P (xIdx k)) (subLineSeedDist P (zIdx k)))
          (fun u => (projX (directPointToPauli P u), projZ (directPointToPauli P u))),
        Distribution.prod_map_right _ (uniformDistribution (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd))
          (fun u => (projX (directPointToPauli P u), projZ (directPointToPauli P u))),
        Distribution.prod_map_left _ (uniformDistribution (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)) _,
        Distribution.map_map, Distribution.map_map]
    have hfin :
        (Distribution.prod
          (Distribution.prod
            (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P)) (uniformDistribution (Fin P.m → PauliScalar P)))
            (Distribution.prod (subLineSeedDist P (xIdx k)) (subLineSeedDist P (zIdx k))))
          (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P)) (uniformDistribution (Fin P.m → PauliScalar P)))).map
          (fun w => ((w.2.1, (w.1.2.1, w.1.1.1)), (w.2.2, (w.1.2.2, w.1.1.2)))) =
        Distribution.prod
          (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
            (Distribution.prod (subLineSeedDist P (xIdx k)) (uniformDistribution (Fin P.m → PauliScalar P))))
          (Distribution.prod (uniformDistribution (Fin P.m → PauliScalar P))
            (Distribution.prod (subLineSeedDist P (zIdx k)) (uniformDistribution (Fin P.m → PauliScalar P)))) := by
      refine Distribution.map_bijective_eq _ _
        (fun w : (((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) ×
          (ScalarQ P.toLdParams × ScalarQ P.toLdParams)) ×
          ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) =>
          ((w.2.1, (w.1.2.1, w.1.1.1)), (w.2.2, (w.1.2.2, w.1.1.2))))
        (fun u : ((Fin P.m → PauliScalar P) × (ScalarQ P.toLdParams × (Fin P.m → PauliScalar P))) ×
          ((Fin P.m → PauliScalar P) × (ScalarQ P.toLdParams × (Fin P.m → PauliScalar P))) =>
          (((u.1.2.2, u.2.2.2), (u.1.2.1, u.2.2.1)), (u.1.1, u.2.1)))
        (fun _ => rfl) (fun _ => rfl) ?_ ?_
      · intro a; simp only [Distribution.prod_support, Finset.mem_product]; tauto
      · intro a; simp only [Distribution.prod_weight]; ring
    rw [hshuf]
    refine (Distribution.map_map _ _ _).trans ((Distribution.prod_map_eq_bind _ _ _).trans ?_)
    refine (Distribution.bind_congr_support _ _
      (fun r => (uniformDistribution (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd)).map
        (fun y => ((subLineSourceLine P kind (projX (directPointToPauli P y)) r.2.1 (projX (directPointToPauli P r.1)),
            subLineSourceLine P kind (projZ (directPointToPauli P y)) r.2.2 (projZ (directPointToPauli P r.1))),
          (projX (directPointToPauli P y), projZ (directPointToPauli P y))))) ?_).trans ?_
    · intro r hr
      obtain ⟨-, hseeds⟩ := Finset.mem_product.mp hr
      obtain ⟨hsx, hsz⟩ := Finset.mem_product.mp hseeds
      have hx : chiIndex P.toLdParams r.2.1 = xIdx k := (Finset.mem_filter.mp hsx).2
      have hz : chiIndex P.toLdParams r.2.2 = zIdx k := (Finset.mem_filter.mp hsz).2
      have hfun : (fun p : (Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) × DirectScalarQ P.extendedDirectLd =>
          ((tripleOf kind k ((p.1, r.1), r.2)).2,
            (projX (directPointToPauli P ((tripleOf kind k ((p.1, r.1), r.2)).1.base + p.2 • (tripleOf kind k ((p.1, r.1), r.2)).1.direction)),
             projZ (directPointToPauli P ((tripleOf kind k ((p.1, r.1), r.2)).1.base + p.2 • (tripleOf kind k ((p.1, r.1), r.2)).1.direction))))) =
        fun p =>
          (fun y =>
            ((subLineSourceLine P kind (projX (directPointToPauli P y)) r.2.1 (projX (directPointToPauli P r.1)),
              subLineSourceLine P kind (projZ (directPointToPauli P y)) r.2.2 (projZ (directPointToPauli P r.1))),
             (projX (directPointToPauli P y), projZ (directPointToPauli P y))))
          (lineRepMap (extDir kind k r.1) p.1 + p.2 • extDir kind k r.1) := by
        funext p
        have hb := hextBase kind k ((p.1, r.1), r.2)
        have hd := hextDir kind k ((p.1, r.1), r.2)
        have hrep : lineRepMap (extDir kind k r.1) (lineRepMap (extDir kind k r.1) p.1 + p.2 • extDir kind k r.1) =
            lineRepMap (extDir kind k r.1) p.1 := by rw [lineRepMap_add_smul]; apply lineRepMap_apply_self
        have hcx : subLineSourceLine P kind (projX (directPointToPauli P p.1)) r.2.1 (projX (directPointToPauli P r.1)) =
            subLineSourceLine P kind (projX (directPointToPauli P (lineRepMap (extDir kind k r.1) p.1 + p.2 • extDir kind k r.1)))
              r.2.1 (projX (directPointToPauli P r.1)) := by
          refine hsrcCongr _ _ _ _ ?_
          rw [hx, ← hrepX _ _ _ (hxSpan kind k r.1),
            ← hrepX (extDir kind k r.1) (lineRepMap (extDir kind k r.1) p.1 + p.2 • extDir kind k r.1) _ (hxSpan kind k r.1), hrep]
        have hcz : subLineSourceLine P kind (projZ (directPointToPauli P p.1)) r.2.2 (projZ (directPointToPauli P r.1)) =
            subLineSourceLine P kind (projZ (directPointToPauli P (lineRepMap (extDir kind k r.1) p.1 + p.2 • extDir kind k r.1)))
              r.2.2 (projZ (directPointToPauli P r.1)) := by
          refine hsrcCongr _ _ _ _ ?_
          rw [hz, ← hrepZ _ _ _ (hzSpan kind k r.1),
            ← hrepZ (extDir kind k r.1) (lineRepMap (extDir kind k r.1) p.1 + p.2 • extDir kind k r.1) _ (hzSpan kind k r.1), hrep]
        dsimp only; rw [hb, hd]
        exact Prod.ext (Prod.ext hcx hcz) rfl
      change (Distribution.prod _ _).map _ = _
      have hm := Distribution.map_map
        (uniformDistribution ((Fin (2 * P.m + 2) → DirectScalarQ P.extendedDirectLd) × DirectScalarQ P.extendedDirectLd))
        (fun p => lineRepMap (extDir kind k r.1) p.1 + p.2 • extDir kind k r.1)
        (fun y => ((subLineSourceLine P kind (projX (directPointToPauli P y)) r.2.1 (projX (directPointToPauli P r.1)),
          subLineSourceLine P kind (projZ (directPointToPauli P y)) r.2.2 (projZ (directPointToPauli P r.1))),
          (projX (directPointToPauli P y), projZ (directPointToPauli P y))))
      rw [hfun, ← uniformDistribution_prod, ← hm, uniformDistribution_map_lineRepMap_add_smul]
    · refine (Distribution.prod_map_eq_bind _ _ _).symm.trans (hpp2.trans ?_)
      rw [← hfin, Distribution.map_map]
  let compBranch (kind : LineKind) : Distribution (SubLineComponent P) :=
    (uniformDistribution (Fin (2 * P.m + 2))).map fun k => (kind, (xIdx k, zIdx k))
  let compDist : Distribution (SubLineComponent P) :=
    Distribution.bind (uniformDistribution (Fin 2)) ![compBranch .axis, compBranch .diagonal]
  refine ⟨{
    D := sDist
    isProbability := Distribution.bind_isProbability _ _ (uniformDistribution_isProbability _) fun c _ => by
      fin_cases c <;> exact Distribution.IsProbability.map hsampProb _
    extended_marginal := by
      have hbfst (kind : LineKind) : (branchDist kind).map Prod.fst =
          (uniformDistribution (DirectLdSpace P.extendedDirectLd)).map (extLineOf kind) := by
        have hs1 : (branchDist kind).map Prod.fst =
            Distribution.bind (uniformDistribution (Fin (2 * P.m + 2))) fun k =>
              (Distribution.prod (uniformDistribution PtDir)
                (Distribution.prod (subLineSeedDist P (xIdx k)) (subLineSeedDist P (zIdx k)))).map
                fun w => extLineOf kind ⟨w.1.1, k, w.1.2⟩ := by
          dsimp only [branchDist, sampDist]
          rw [Distribution.map_map, Distribution.bind_map]
          exact Distribution.bind_congr_support _ _ _ fun k _ => by rw [Distribution.map_map]
        have hs2 (k : Fin (2 * P.m + 2)) :
            (Distribution.prod (uniformDistribution PtDir)
              (Distribution.prod (subLineSeedDist P (xIdx k)) (subLineSeedDist P (zIdx k)))).map
              (fun w => extLineOf kind ⟨w.1.1, k, w.1.2⟩) =
            (uniformDistribution PtDir).map (fun pd => extLineOf kind ⟨pd.1, k, pd.2⟩) :=
          Distribution.prod_map_of_fst (uniformDistribution PtDir) _
            (Distribution.prod_isProbability _ _ (subLineSeedDist_isProbability P _) (subLineSeedDist_isProbability P _))
            (fun pd : PtDir => extLineOf kind ⟨pd.1, k, pd.2⟩)
        let eSamp : DirectLdSpace P.extendedDirectLd ≃ Fin (2 * P.m + 2) × PtDir :=
          { toFun := fun s => (s.index, s.point, s.direction)
            invFun := fun w => ⟨w.2.1, w.1, w.2.2⟩
            left_inv := fun s => by cases s; rfl
            right_inv := fun w => by cases w; rfl }
        rw [hs1, Distribution.bind_congr_support _ _ _ fun k _ => hs2 k,
          ← Distribution.prod_map_eq_bind (uniformDistribution (Fin (2 * P.m + 2))) (uniformDistribution PtDir)
            (fun w => extLineOf kind ⟨w.2.1, w.1, w.2.2⟩),
          ← uniformDistribution_prod, ← uniformDistribution_map_equiv eSamp, Distribution.map_map]
        rfl
      dsimp only [sDist]
      rw [Distribution.bind_map, directLinePointDist, ← Distribution.bind_uniform_fin_two, Distribution.bind_map]
      refine Distribution.bind_congr_support _ _ _ fun c _ => ?_
      fin_cases c
      · dsimp; rw [hbfst .axis, directALinePointDist, Distribution.map_map]
      · dsimp; rw [hbfst .diagonal, directDLinePointDist, Distribution.map_map]
    incidence := fun sample hs u hu => by
      obtain ⟨kind, k, w, hx, hz, rfl⟩ := hsupp hs
      obtain ⟨tu, rfl⟩ := hu
      have hxsp : projX (directPointToPauli P (tripleOf kind k w).1.direction) ∈
          Submodule.span (PauliScalar P) ({(tripleOf kind k w).2.1.direction} : Set _) := by
        rw [hextDir, show (tripleOf kind k w).2.1.direction = srcDir kind (xIdx k) _ by
          rw [← hx]; exact hsrcDir kind _ w.2.1 _]
        exact hxSpan kind k w.1.2
      have hzsp : projZ (directPointToPauli P (tripleOf kind k w).1.direction) ∈
          Submodule.span (PauliScalar P) ({(tripleOf kind k w).2.2.direction} : Set _) := by
        rw [hextDir, show (tripleOf kind k w).2.2.direction = srcDir kind (zIdx k) _ by
          rw [← hz]; exact hsrcDir kind _ w.2.2 _]
        exact hzSpan kind k w.1.2
      have hxb : (tripleOf kind k w).2.1.base =
          lineRepMap (tripleOf kind k w).2.1.direction (projX (directPointToPauli P (tripleOf kind k w).1.base)) := by
        have h1 : (tripleOf kind k w).2.1.base = lineRepMap (srcDir kind (xIdx k) (projX (directPointToPauli P w.1.2)))
            (projX (directPointToPauli P w.1.1)) := by rw [← hx]; exact hsrcBase kind _ w.2.1 _
        have h2 : (tripleOf kind k w).2.1.direction = srcDir kind (xIdx k) (projX (directPointToPauli P w.1.2)) := by
          rw [← hx]; exact hsrcDir kind _ w.2.1 _
        rw [h1, h2, hextBase, hrepX _ _ _ (hxSpan kind k w.1.2)]
      have hzb : (tripleOf kind k w).2.2.base =
          lineRepMap (tripleOf kind k w).2.2.direction (projZ (directPointToPauli P (tripleOf kind k w).1.base)) := by
        have h1 : (tripleOf kind k w).2.2.base = lineRepMap (srcDir kind (zIdx k) (projZ (directPointToPauli P w.1.2)))
            (projZ (directPointToPauli P w.1.1)) := by rw [← hz]; exact hsrcBase kind _ w.2.2 _
        have h2 : (tripleOf kind k w).2.2.direction = srcDir kind (zIdx k) (projZ (directPointToPauli P w.1.2)) := by
          rw [← hz]; exact hsrcDir kind _ w.2.2 _
        rw [h1, h2, hextBase, hrepZ _ _ _ (hzSpan kind k w.1.2)]
      obtain ⟨cX, hcX⟩ := Submodule.mem_span_singleton.mp hxsp
      obtain ⟨cZ, hcZ⟩ := Submodule.mem_span_singleton.mp hzsp
      refine ⟨?_, ?_⟩
      · rw [LineDesc.pointSet, hxb, linePoints_eq_of_mem _ _ _ (mem_linePoints_lineRepMap _ _)]
        refine ⟨extendedDirectScalarEquiv P tu * cX, ?_⟩
        rw [directPointToPauli_add, directPointToPauli_smul, projX_add, projX_smul, ← hcX]; module
      · rw [LineDesc.pointSet, hzb, linePoints_eq_of_mem _ _ _ (mem_linePoints_lineRepMap _ _)]
        refine ⟨extendedDirectScalarEquiv P tu * cZ, ?_⟩
        rw [directPointToPauli_add, directPointToPauli_smul, projZ_add, projZ_smul, ← hcZ]; module
    compatibility := fun sample hs => by
      obtain ⟨kind, k, w, hx, hz, rfl⟩ := hsupp hs
      have hxsp : projX (directPointToPauli P (tripleOf kind k w).1.direction) ∈
          Submodule.span (PauliScalar P) ({(tripleOf kind k w).2.1.direction} : Set _) := by
        rw [hextDir, show (tripleOf kind k w).2.1.direction = srcDir kind (xIdx k) _ by
          rw [← hx]; exact hsrcDir kind _ w.2.1 _]
        exact hxSpan kind k w.1.2
      have hzsp : projZ (directPointToPauli P (tripleOf kind k w).1.direction) ∈
          Submodule.span (PauliScalar P) ({(tripleOf kind k w).2.2.direction} : Set _) := by
        rw [hextDir, show (tripleOf kind k w).2.2.direction = srcDir kind (zIdx k) _ by
          rw [← hz]; exact hsrcDir kind _ w.2.2 _]
        exact hzSpan kind k w.1.2
      have hxb : (tripleOf kind k w).2.1.base =
          lineRepMap (tripleOf kind k w).2.1.direction (projX (directPointToPauli P (tripleOf kind k w).1.base)) := by
        have h1 : (tripleOf kind k w).2.1.base = lineRepMap (srcDir kind (xIdx k) (projX (directPointToPauli P w.1.2)))
            (projX (directPointToPauli P w.1.1)) := by rw [← hx]; exact hsrcBase kind _ w.2.1 _
        have h2 : (tripleOf kind k w).2.1.direction = srcDir kind (xIdx k) (projX (directPointToPauli P w.1.2)) := by
          rw [← hx]; exact hsrcDir kind _ w.2.1 _
        rw [h1, h2, hextBase, hrepX _ _ _ (hxSpan kind k w.1.2)]
      have hzb : (tripleOf kind k w).2.2.base =
          lineRepMap (tripleOf kind k w).2.2.direction (projZ (directPointToPauli P (tripleOf kind k w).1.base)) := by
        have h1 : (tripleOf kind k w).2.2.base = lineRepMap (srcDir kind (zIdx k) (projZ (directPointToPauli P w.1.2)))
            (projZ (directPointToPauli P w.1.1)) := by rw [← hz]; exact hsrcBase kind _ w.2.2 _
        have h2 : (tripleOf kind k w).2.2.direction = srcDir kind (zIdx k) (projZ (directPointToPauli P w.1.2)) := by
          rw [← hz]; exact hsrcDir kind _ w.2.2 _
        rw [h1, h2, hextBase, hrepZ _ _ _ (hzSpan kind k w.1.2)]
      obtain ⟨aX, haX⟩ := Submodule.mem_span_singleton.mp
        (sub_lineRepMap_mem_span (tripleOf kind k w).2.1.direction (projX (directPointToPauli P (tripleOf kind k w).1.base)))
      obtain ⟨aZ, haZ⟩ := Submodule.mem_span_singleton.mp
        (sub_lineRepMap_mem_span (tripleOf kind k w).2.2.direction (projZ (directPointToPauli P (tripleOf kind k w).1.base)))
      obtain ⟨bX, hbX⟩ := Submodule.mem_span_singleton.mp hxsp
      obtain ⟨bZ, hbZ⟩ := Submodule.mem_span_singleton.mp hzsp
      refine ⟨aX, bX, aZ, bZ, _, _, _, _, rfl, rfl, rfl, rfl, fun t => ⟨?_, ?_⟩⟩
      · rw [projX_add, projX_smul, show projX (directPointToPauli P (tripleOf kind k w).1.base) =
            (tripleOf kind k w).2.1.base + aX • (tripleOf kind k w).2.1.direction by rw [hxb, haX]; abel,
          hbX.symm]
        module
      · rw [projZ_add, projZ_smul, show projZ (directPointToPauli P (tripleOf kind k w).1.base) =
            (tripleOf kind k w).2.2.base + aZ • (tripleOf kind k w).2.2.direction by rw [hzb, haZ]; abel,
          hbZ.symm]
        module
    source_mixture := by
      have hpbind {α : Type} (μ : Distribution α) (ν : α → Distribution (SubLineTriple P)) :
          subLinePointDist P (Distribution.bind μ ν) = Distribution.bind μ (fun a => subLinePointDist P (ν a)) := by
        unfold subLinePointDist; rw [Distribution.prod_bind_left, Distribution.bind_map]
      have hbr_bind (kind : LineKind) :
          branchDist kind = Distribution.bind (uniformDistribution (Fin (2 * P.m + 2))) fun k =>
            (Distribution.prod (uniformDistribution PtDir)
              (Distribution.prod (subLineSeedDist P (xIdx k)) (subLineSeedDist P (zIdx k)))).map
              fun w => tripleOf kind k w := by
        dsimp only [branchDist, sampDist]
        rw [Distribution.bind_map]
        exact Distribution.bind_congr_support _ _ _ fun k _ => by rw [Distribution.map_map]
      refine ⟨compDist,
        Distribution.bind_isProbability _ _ (uniformDistribution_isProbability _) fun c _ => by
          fin_cases c <;> exact Distribution.IsProbability.map (uniformDistribution_isProbability _) _,
        ?_, ?_⟩
      · dsimp only [sDist, compDist]
        rw [hpbind, Distribution.bind_map, Distribution.bind_bind]
        refine Distribution.bind_congr_support _ _ _ fun c _ => ?_
        have hXbr (kind : LineKind) :
            (subLinePointDist P (branchDist kind)).map subLineXProjection =
              Distribution.bind (compBranch kind) (subLineXComponentDist P) := by
          rw [hbr_bind, hpbind, Distribution.bind_map, Distribution.bind_map_left]
          refine Distribution.bind_congr_support _ _ _ fun k _ => ?_
          unfold subLinePointDist
          rw [Distribution.prod_map_left, Distribution.map_map, Distribution.map_map]
          have hj := congrArg (fun D => Distribution.map D (fun z => (z.1, z.2.1))) (hjoint kind k)
          simp only [Distribution.map_map] at hj
          refine hj.trans ?_
          simp only [subLineXComponentDist, restrictedLinePointDist_eq_map_prod, Distribution.map_map]
          rw [Distribution.prod_map_left, Distribution.prod_map_right, Distribution.map_map, Distribution.map_map]
        fin_cases c
        · exact hXbr .axis
        · exact hXbr .diagonal
      · dsimp only [sDist, compDist]
        rw [hpbind, Distribution.bind_map, Distribution.bind_bind]
        refine Distribution.bind_congr_support _ _ _ fun c _ => ?_
        have hZbr (kind : LineKind) :
            (subLinePointDist P (branchDist kind)).map subLineZProjection =
              Distribution.bind (compBranch kind) (subLineZComponentDist P) := by
          rw [hbr_bind, hpbind, Distribution.bind_map, Distribution.bind_map_left]
          refine Distribution.bind_congr_support _ _ _ fun k _ => ?_
          unfold subLinePointDist
          rw [Distribution.prod_map_left, Distribution.map_map, Distribution.map_map]
          have hj := congrArg (fun D => Distribution.map D (fun z => (z.1, z.2.2))) (hjoint kind k)
          simp only [Distribution.map_map] at hj
          refine hj.trans ?_
          simp only [subLineZComponentDist, restrictedLinePointDist_eq_map_prod, Distribution.map_map]
          rw [Distribution.prod_map_left, Distribution.prod_map_right, Distribution.map_map, Distribution.map_map]
        fin_cases c
        · exact hZbr .axis
        · exact hZbr .diagonal
    axis_closure := fun sample hs hax => by
      obtain ⟨kind, k, w, -, -, rfl⟩ := hsupp hs
      cases kind
      · exact ⟨rfl, rfl⟩
      · cases hax }⟩

theorem SubLineWitness.avgOver_projX_projZ (P : AdmissibleParams)
    (sublines : SubLineWitness P)
    (f : ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)) → ℝ) :
    avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd))
          (fun t =>
            f (projX (directPointToPauli P (sample.1.base + t • sample.1.direction)),
               projZ (directPointToPauli P (sample.1.base + t • sample.1.direction))))) =
      avgOver (uniformDistribution ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P))) f := by
  classical
  have hunif_add (D : DirectLdParams)
      (V : Fin D.m × (Fin D.m → DirectScalarQ D) → (Fin D.m → DirectScalarQ D))
      (g : (Fin D.m → DirectScalarQ D) → ℝ) :
      avgOver (uniformDistribution (DirectLdSpace D)) (fun s =>
          avgOver (uniformDistribution (DirectScalarQ D)) (fun t =>
            g (lineRepMap (V (s.index, s.direction)) s.point + t • V (s.index, s.direction)))) =
        avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) g := by
    let e : DirectLdSpace D × DirectScalarQ D ≃
        (Fin D.m × (Fin D.m → DirectScalarQ D)) × ((Fin D.m → DirectScalarQ D) × DirectScalarQ D) :=
      { toFun := fun p => ((p.1.index, p.1.direction), (p.1.point, p.2))
        invFun := fun w => (⟨w.2.1, w.1.1, w.1.2⟩, w.2.2)
        left_inv := by rintro ⟨⟨pt, i, dir⟩, t⟩; rfl
        right_inv := by rintro ⟨⟨i, dir⟩, pt, t⟩; rfl }
    have hmap : (uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map
        (fun p => lineRepMap (V (p.1.index, p.1.direction)) p.1.point + p.2 • V (p.1.index, p.1.direction)) =
        uniformDistribution (Fin D.m → DirectScalarQ D) := by
      rw [show (uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map _ =
          ((uniformDistribution (DirectLdSpace D × DirectScalarQ D)).map e).map
            (fun w => lineRepMap (V w.1) w.2.1 + w.2.2 • V w.1) by rw [Distribution.map_map]; rfl,
        uniformDistribution_map_equiv e,
        ← bind_uniformDistribution_map (fun (a : Fin D.m × (Fin D.m → DirectScalarQ D))
          (b : (Fin D.m → DirectScalarQ D) × DirectScalarQ D) => lineRepMap (V a) b.1 + b.2 • V a),
        show (fun a => (uniformDistribution _).map (fun b : (Fin D.m → DirectScalarQ D) × DirectScalarQ D =>
            lineRepMap (V a) b.1 + b.2 • V a)) =
          fun _ => uniformDistribution (Fin D.m → DirectScalarQ D) from
          funext fun a => uniformDistribution_map_lineRepMap_add_smul (V a)]
      exact Distribution.bind_const _ (uniformDistribution_isProbability _) _
    rw [← avgOver_uniform_prod, ← Distribution.avgOver_map _ _ g, hmap]
  have hdline (D : DirectLdParams) (g : (Fin D.m → DirectScalarQ D) → ℝ) :
      avgOver ((directLinePointDist D).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ D)) (fun t => g (line.base + t • line.direction))) =
      avgOver (uniformDistribution (Fin D.m → DirectScalarQ D)) g := by
    rw [Distribution.avgOver_map, directLinePointDist, WinImplications.avgOver_mix,
      directALinePointDist, Distribution.avgOver_map, directDLinePointDist, Distribution.avgOver_map]
    dsimp only [directALineDescOf, directDLineDescOf, DirectLineDesc.base, DirectLineDesc.direction]
    rw [hunif_add D (fun w => coordinateDirection w.1) g,
      hunif_add D (fun w => directPrefixProjection w.1 w.2) g]
    ring
  have hmarg : avgOver sublines.D (fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
          f (projX (directPointToPauli P (sample.1.base + t • sample.1.direction)),
             projZ (directPointToPauli P (sample.1.base + t • sample.1.direction))))) =
      avgOver ((directLinePointDist P.extendedDirectLd).map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
          f (projX (directPointToPauli P (line.base + t • line.direction)),
             projZ (directPointToPauli P (line.base + t • line.direction))))) := by
    rw [← sublines.extended_marginal, Distribution.avgOver_map]
  rw [hmarg, hdline P.extendedDirectLd (fun u => f (projX (directPointToPauli P u), projZ (directPointToPauli P u))),
    uniformDistribution_prod, ← uniformDistribution_map_projX_projZ_pauli, Distribution.avgOver_map]

/-! ## Section 4: Combined X/Z line measurement and consistency -/

def ProjectiveSetting.combinedLineMeasurement {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams) :
    Measurement (DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d))
      (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne
    (fun fs => (S.lineMeasExp side .X lineX).effect fs.1 *
      (S.lineMeasExp side .Z lineZ).effect fs.2 * (S.lineMeasExp side .X lineX).effect fs.1)
    (fun fs => (pastedMeasurement_isMeasurement
      (S.lineMeasExp side .Z lineZ) (S.lineMeasExp side .X lineX)
      (S.lineMeasExp_isProjective side .X lineX)).1 (fs.2, fs.1))
    (by
      classical
      have hsum := (pastedMeasurement_isMeasurement
        (S.lineMeasExp side .Z lineZ) (S.lineMeasExp side .X lineX)
        (S.lineMeasExp_isProjective side .X lineX)).2
      simp only [pastedMeasurement, Fintype.sum_prod_type] at hsum ⊢
      rw [Finset.sum_comm]; exact hsum)

@[simp] theorem ProjectiveSetting.combinedLineMeasurement_effect
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams)
    (fX fZ : DegPoly P.toLdParams (P.m * P.d)) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) =
      (S.lineMeasExp side .X lineX).effect fX *
        (S.lineMeasExp side .Z lineZ).effect fZ * (S.lineMeasExp side .X lineX).effect fX := rfl

theorem ProjectiveSetting.combinedLineMeasurement_axis_degree_X
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams) (fX fZ : DegPoly P.toLdParams (P.m * P.d))
    (haxis : lineX.kind = .axis) (hf : ¬ fX.FitsDegree P.d) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) = 0 := by
  simp only [S.combinedLineMeasurement_effect, S.lineMeasExp_effect,
    S.expLineOp_zero_of_not_deg_d side .X lineX haxis fX hf, zero_mul]

theorem ProjectiveSetting.combinedLineMeasurement_axis_degree_Z
    {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
    (lineX lineZ : LineDesc P.toLdParams) (fX fZ : DegPoly P.toLdParams (P.m * P.d))
    (haxis : lineZ.kind = .axis) (hf : ¬ fZ.FitsDegree P.d) :
    (S.combinedLineMeasurement side lineX lineZ).effect (fX, fZ) = 0 := by
  simp only [S.combinedLineMeasurement_effect, S.lineMeasExp_effect,
    S.expLineOp_zero_of_not_deg_d side .Z lineZ haxis fZ hf, mul_zero, zero_mul]

def bbAbBipartition (params : AdmissibleParams) (left right : Type*) :
    SixReg params left right ≃
      (right × PauliRegister params) ×
        ((left × PauliRegister params) × (PauliRegister params × PauliRegister params)) where
  toFun i := ((i.2.1, i.2.2.1), ((i.1.1, i.2.2.2), (i.1.2.1, i.1.2.2)))
  invFun i := ((i.2.1.1, (i.2.2.1, i.2.2.2)), (i.1.1, (i.1.2, i.2.1.2)))
  left_inv i := by cases i; rfl
  right_inv i := by cases i; rfl

set_option synthInstance.maxSize 400 in
theorem ProjectiveSetting.exists_opposite_bipartition {params : AdmissibleParams}
    {error : ℝ} (setting : ProjectiveSetting params error)
    (first second : Placement) (hopposite : first.IsOpposite second) :
    ∃ e : SixReg params setting.toStrategy.ιA setting.toStrategy.ιB ≃
        setting.ExpandedLocalSpace first.side ×
          (setting.ExpandedLocalSpace second.side × (PauliRegister params × PauliRegister params)),
      (∀ op : Op (setting.ExpandedLocalSpace first.side),
        reindexOp e (heteroKron op 1) = setting.place first op) ∧
      (∀ op : Op (setting.ExpandedLocalSpace second.side),
        reindexOp e (heteroKron 1 (heteroKron op (1 : Op (PauliRegister params × PauliRegister params)))) =
          setting.place second op) := by
  classical
  cases first <;> cases second <;> try exact False.elim hopposite
  · exact ⟨aaBaBipartition params _ _, setting.reindexOp_aaBaBipartition_left, setting.reindexOp_aaBaBipartition_right⟩
  · exact ⟨baAaBipartition params _ _, setting.reindexOp_baAaBipartition_left, setting.reindexOp_baAaBipartition_right⟩
  · refine ⟨bbAbBipartition params _ _, fun op => ?_, fun op => ?_⟩
    · ext r c
      change op (r.2.1, r.2.2.1) (c.2.1, c.2.2.1) *
        (1 : Op ((setting.toStrategy.ιA × PauliRegister params) × (PauliRegister params × PauliRegister params)))
          ((r.1.1, r.2.2.2), r.1.2) ((c.1.1, c.2.2.2), c.1.2) = _
      simp only [ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]; split_ifs <;> simp_all
    · ext r c
      change (1 : Op (setting.toStrategy.ιB × PauliRegister params)) (r.2.1, r.2.2.1) (c.2.1, c.2.2.1) *
        (op (r.1.1, r.2.2.2) (c.1.1, c.2.2.2) * (1 : Op (PauliRegister params × PauliRegister params)) r.1.2 c.1.2) = _
      simp only [ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff]; split_ifs <;> simp_all
  · exact ⟨abBbBipartition params _ _, setting.reindexOp_abBbBipartition_left, setting.reindexOp_abBbBipartition_right⟩

set_option synthInstance.maxSize 400 in
set_option maxHeartbeats 800000 in
-- Pasting and restoring discarded zero-direction mass elaborates nested postprocessed families.
theorem exists_combinedLinesWitness_ofPointsWitness (deltaQ : ℝ → ℝ)
    (hdeltaQ : IsPolyErr deltaQ) :
    ∃ deltaP : ℝ → ℝ → ℝ, IsPolyErr₂ deltaP ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (points : CombinedPointsWitness S (deltaQ ε)),
        Nonempty (CombinedLinesWitness S points
          (deltaP ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)))) := by
  obtain ⟨lineError, hlineError, hscalar⟩ :=
    exists_conditioned_polynomial_bound deltaQ hdeltaQ 2080 (by norm_num)
      heterogeneousPastingError heterogeneous_pasting_error_is_poly_err₂
  refine ⟨lineError, hlineError, fun P ε S points => ?_⟩
  let L := P.toLdParams
  -- 1. Zero-direction mass and retained nondegenerate mass bounds
  have haZero : avgOver (aLinePointDist L) (fun s => if s.1.direction = 0 then (1 : ℝ) else 0) = 0 := by
    unfold aLinePointDist; rw [Distribution.avgOver_map]
    have hdir (raw : LdSpace L) : (aLineDescOf L raw).direction ≠ 0 := fun hz => by
      have := congrFun hz (chiIndex L raw.seed)
      simp [aLineDescOf, LineDesc.direction, coordinateDirection] at this
    simp [avgOver, hdir]
  have hdZero : avgOver (dLinePointDist L) (fun s => if s.1.direction = 0 then (1 : ℝ) else 0) ≤
      1 / Fintype.card (ScalarQ L) := by
    let last : Fin L.m := ⟨L.m - 1, by have := L.hm; omega⟩
    let coord : LdIndex L := .inr last
    have hmap : (uniformDistribution (LdSpace L)).map (fun raw => raw coord) = uniformDistribution (ScalarQ L) := by
      change (uniformDistribution (LdSpace L)).map (fun raw => (Equiv.funSplitAt coord (ScalarQ L) raw).1) = _
      rw [← Distribution.map_map, uniformDistribution_map_equiv, uniformDistribution_map_fst]
    have hz : avgOver (uniformDistribution (LdSpace L)) (fun raw => if raw coord = 0 then (1 : ℝ) else 0) =
        1 / Fintype.card (ScalarQ L) := by
      rw [← Distribution.avgOver_map (uniformDistribution (LdSpace L)) (fun raw => raw coord)
        (fun v => if v = 0 then (1 : ℝ) else 0), hmap]
      simp [avgOver, uniformDistribution_weight_apply, mul_ite]
    unfold dLinePointDist clDistribution
    rw [Distribution.avgOver_map, Distribution.avgOver_map]
    refine (avgOver_mono _ _ _ fun raw => ?_).trans hz.le
    dsimp only; rw [dLineDescOf_ldDLineCL]
    split_ifs with hdir hc hc
    · exact le_rfl
    · exfalso; apply hc
      have hlast := congrFun hdir last
      change prefixProjection (chiIndex L (LdSpace.seed raw)) (LdSpace.direction raw) last = 0 at hlast
      have hidx : ¬ last.val < (chiIndex L (LdSpace.seed raw)).val := by
        have := (chiIndex L (LdSpace.seed raw)).isLt; dsimp [last]; omega
      simpa [prefixProjection, hidx, LdSpace.direction, coord] using hlast
    · norm_num
    · exact le_rfl
  have hlZero : avgOver (linePointDist L) (fun s => if s.1.direction = 0 then (1 : ℝ) else 0) ≤
      1 / (2 * Fintype.card (ScalarQ L)) := by
    rw [linePointDist, WinImplications.avgOver_mix, haZero]
    exact (by ring : _ = (1 / 2 : ℝ) * avgOver (dLinePointDist L) _).trans_le
      ((mul_le_mul_of_nonneg_left hdZero (by norm_num)).trans_eq (one_div_mul_one_div _ _))
  have hpZero : avgOver (Distribution.prod (linePointDist L) (linePointDist L))
      (fun s => if s.1.1.direction = 0 then (1 : ℝ) else 0) ≤ 1 / (2 * Fintype.card (ScalarQ L)) := by
    rw [SandwichProduct.avgOver_distribution_prod]
    change avgOver (linePointDist L) (fun s => avgOver (linePointDist L) (fun _ => if s.1.direction = 0 then 1 else 0)) ≤ _
    simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability L)]
    exact hlZero
  let ndMass : ℝ :=
    ∑ s ∈ (Distribution.prod (linePointDist L) (linePointDist L)).support.filter (fun s => s.1.1.direction ≠ 0),
      (Distribution.prod (linePointDist L) (linePointDist L)).weight s
  have hndBounds : 1 / 2 ≤ ndMass ∧ ndMass ≤ 1 := by
    let ind := fun s : LineDesc L × (Fin L.m → ScalarQ L) => if s.1.direction ≠ 0 then (1 : ℝ) else 0
    have hm : ndMass = avgOver (linePointDist L) ind := by
      dsimp [ndMass]
      rw [Distribution.sum_filter_weight_eq_avgOver, SandwichProduct.avgOver_distribution_prod]
      change avgOver (linePointDist L) (fun s => avgOver (linePointDist L) (fun _ => ind s)) = _
      simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability L)]
    have hax : avgOver (aLinePointDist L) ind = 1 := by
      rw [show ind = fun s => 1 - if s.1.direction = 0 then (1 : ℝ) else 0 from
          funext fun s => by by_cases hz : s.1.direction = 0 <;> simp [ind, hz],
        avgOver_sub, avgOver_const_of_isProbability _ (aLinePointDist_isProbability L), haZero]
      norm_num
    have hd0 : 0 ≤ avgOver (dLinePointDist L) ind :=
      avgOver_nonneg _ _ fun s => by by_cases hz : s.1.direction = 0 <;> simp [ind, hz]
    rw [hm]
    refine ⟨by rw [linePointDist, WinImplications.avgOver_mix, hax]; linarith, ?_⟩
    exact (avgOver_mono _ _ (fun _ => 1) fun s => by by_cases hz : s.1.direction = 0 <;> simp [ind, hz]).trans_eq
      (avgOver_const_of_isProbability _ (linePointDist_isProbability L) 1)
  have hndPos : 0 < ndMass := lt_of_lt_of_le (by norm_num) hndBounds.1
  let ndDist : Distribution (((LineDesc L × LineDesc L) × (LineDesc L × (Fin L.m → ScalarQ L))) ×
      (LineDesc L × (Fin L.m → ScalarQ L))) :=
    (Distribution.restrict (Distribution.prod (linePointDist L) (linePointDist L))
      (fun s => s.1.1.direction ≠ 0) hndPos).map (fun s => (((s.1.1, s.2.1), s.2), s.1))
  -- 2. Resampling and conditional collision bound
  have hresL (val : (LineDesc L × (Fin L.m → ScalarQ L)) → ℝ) :
      avgOver (linePointDist L) val =
        avgOver (linePointDist L) (fun s => avgOver (uniformDistribution (ScalarQ L))
          (fun t => val (s.1, s.1.base + t • s.1.direction))) := by
    have hA : avgOver (aLinePointDist L) val = avgOver (aLinePointDist L) (fun s =>
        avgOver (uniformDistribution (ScalarQ L)) (fun t => val (s.1, s.1.base + t • s.1.direction))) := by
      unfold aLinePointDist clDistribution
      simp only [Distribution.avgOver_map, aLineDescOf_ldALineCL]
      simp_rw [← uniformDistribution_map_equiv (ldSpaceBlockEquiv L).symm, Distribution.avgOver_map,
        uniformDistribution_prod (Fin L.m → ScalarQ L) (ScalarQ L × (Fin L.m → ScalarQ L)),
        SandwichProduct.avgOver_distribution_prod]
      rw [avgOver_comm, eq_comm, avgOver_comm, eq_comm]
      refine congrArg _ (funext fun blk => ?_)
      let dir : Fin L.m → ScalarQ L := coordinateDirection (chiIndex L blk.1)
      have hidem (pt : Fin L.m → ScalarQ L) :
          aLineDescOf L ((ldSpaceBlockEquiv L).symm (lineRepMap dir pt, blk)) =
            aLineDescOf L ((ldSpaceBlockEquiv L).symm (pt, blk)) := by
        dsimp only [aLineDescOf, ldSpaceBlockEquiv, LdSpace.point, LdSpace.seed, dir]
        exact (show ∀ (b b' : Fin L.m → ScalarQ L) (hb : b = b') h1 h2,
          LineDesc.axis b blk.1 h1 = LineDesc.axis b' blk.1 h2 by intro _ _ hb _ _; subst hb; rfl)
          _ _ (lineRepMap_apply_self _ _) _ _
      have hr := avgOver_uniform_lineRepMap_resample_parameter dir
        (fun base pt => val (aLineDescOf L ((ldSpaceBlockEquiv L).symm (base, blk)), pt))
      simp_rw [hidem] at hr
      exact hr
    have hD : avgOver (dLinePointDist L) val = avgOver (dLinePointDist L) (fun s =>
        avgOver (uniformDistribution (ScalarQ L)) (fun t => val (s.1, s.1.base + t • s.1.direction))) := by
      unfold dLinePointDist clDistribution
      simp only [Distribution.avgOver_map, dLineDescOf_ldDLineCL]
      simp_rw [← uniformDistribution_map_equiv (ldSpaceBlockEquiv L).symm, Distribution.avgOver_map,
        uniformDistribution_prod (Fin L.m → ScalarQ L) (ScalarQ L × (Fin L.m → ScalarQ L)),
        SandwichProduct.avgOver_distribution_prod]
      rw [avgOver_comm, eq_comm, avgOver_comm, eq_comm]
      refine congrArg _ (funext fun blk => ?_)
      let dir : Fin L.m → ScalarQ L := prefixProjection (chiIndex L blk.1) blk.2
      have hidem (pt : Fin L.m → ScalarQ L) :
          dLineDescOf L ((ldSpaceBlockEquiv L).symm (lineRepMap dir pt, blk)) =
            dLineDescOf L ((ldSpaceBlockEquiv L).symm (pt, blk)) := by
        dsimp only [dLineDescOf, ldSpaceBlockEquiv, LdSpace.point, LdSpace.seed, LdSpace.direction, dir]
        exact (show ∀ (b b' : Fin L.m → ScalarQ L) (hb : b = b') h1 h2 h3 h4,
          LineDesc.diagonal b blk.1 dir h1 h2 = LineDesc.diagonal b' blk.1 dir h3 h4 by
            intro _ _ hb _ _ _ _; subst hb; rfl)
          _ _ (lineRepMap_apply_self _ _) _ _ _ _
      have hr := avgOver_uniform_lineRepMap_resample_parameter dir
        (fun base pt => val (dLineDescOf L ((ldSpaceBlockEquiv L).symm (base, blk)), pt))
      simp_rw [hidem] at hr
      exact hr
    rw [linePointDist, WinImplications.avgOver_mix, WinImplications.avgOver_mix, hA, hD]
  have hcoll : HasConditionalCollisionBound ndDist
      (fun (poly : DegPoly L (P.m * P.d)) s => evalOpt s.1 s.2 poly)
      ((P.m * P.d : ℕ) / (Fintype.card (ScalarQ L) : ℝ)) := by
    intro question point _ f1 f2 hne
    have havg_u (v : _ → ℝ) : avgOver ndDist v = ∑ s, ndDist.weight s * v s :=
      (ndDist.sum_univ_eq_sum_support _ fun s hout => by rw [ndDist.outsideSupport s hout, zero_mul]).symm
    have hmass_w : (ndDist.map Prod.fst).weight (question, point) =
        avgOver ndDist (fun s => if s.1 = (question, point) then 1 else 0) := by
      rw [Distribution.map_weight]; unfold avgOver; rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun s _ => by by_cases hf : s.1 = (question, point) <;> simp [hf]
    rw [hmass_w]
    suffices hb : avgOver ndDist (fun s => if s.1 = (question, point) then
        (if evalOpt s.2.1 s.2.2 f1 = evalOpt s.2.1 s.2.2 f2 then 1 else 0) else 0) ≤
        ((P.m * P.d : ℕ) / (Fintype.card (ScalarQ L) : ℝ)) *
          avgOver ndDist (fun s => if s.1 = (question, point) then 1 else 0) by
      simpa [havg_u, Fintype.sum_prod_type, mul_ite] using hb
    dsimp only [ndDist]
    simp only [Distribution.avgOver_map]
    apply (mul_le_mul_iff_right₀ hndPos).mp
    rw [avgOver_restrict_mul_mass, mul_left_comm _ ((P.m * P.d : ℕ) / (Fintype.card (ScalarQ L) : ℝ)),
      avgOver_restrict_mul_mass, Finset.sum_filter, Finset.sum_filter]
    let wt (line : LineDesc L) (s2 : LineDesc L × (Fin L.m → ScalarQ L)) : ℝ :=
      if ((line, s2.1), s2) = (question, point) then 1 else 0
    have hwt : avgOver (Distribution.prod (linePointDist L) (linePointDist L)) (fun s =>
        if s.1.1.direction ≠ 0 then wt s.1.1 s.2 *
          (if evalOpt s.1.1 s.1.2 f1 = evalOpt s.1.1 s.1.2 f2 then 1 else 0) else 0) ≤
      ((P.m * P.d : ℕ) / (Fintype.card (ScalarQ L) : ℝ)) *
        avgOver (Distribution.prod (linePointDist L) (linePointDist L)) (fun s =>
          if s.1.1.direction ≠ 0 then wt s.1.1 s.2 else 0) := by
      simp only [SandwichProduct.avgOver_distribution_prod]
      rw [avgOver_comm, avgOver_comm (linePointDist L) (linePointDist L)
        (fun s1 s2 => if s1.1.direction ≠ 0 then wt s1.1 s2 else 0), ← avgOver_const_mul]
      refine avgOver_mono _ _ _ fun s2 => ?_
      rw [hresL, ← avgOver_const_mul]
      refine avgOver_mono _ _ _ fun s1 => ?_
      by_cases hdir : s1.1.direction ≠ 0
      · simp only [if_pos hdir]
        rw [avgOver_const_mul]
        have hucoll : avgOver (uniformDistribution (ScalarQ L)) (fun t =>
            if evalOpt s1.1 (s1.1.base + t • s1.1.direction) f1 =
              evalOpt s1.1 (s1.1.base + t • s1.1.direction) f2 then 1 else 0) ≤
            (P.m * P.d : ℕ) / (Fintype.card (ScalarQ L) : ℝ) := by
          have hevo (poly : DegPoly L (P.m * P.d)) (t : ScalarQ L) :
              evalOpt s1.1 (s1.1.base + t • s1.1.direction) poly = some (evalCoefficient poly t) := by
            refine WinImplications.evalOpt_eq_some_of_evaluatesTo s1.1 poly (s1.1.base + t • s1.1.direction)
              (evalCoefficient poly t) ⟨⟨t, rfl⟩, fun t' heq => ?_⟩
            have hsub : (t - t') • s1.1.direction = 0 := by rw [sub_smul, add_left_cancel heq, sub_self]
            rw [sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hdir)]
          simp_rw [hevo, Option.some.injEq]
          have hcard := evalCoefficient_collision_card_le f1 f2 hne
          unfold avgOver
          simp only [uniformDistribution_support, uniformDistribution_weight_apply, mul_ite, mul_one, mul_zero,
            ← Finset.sum_filter]
          rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
          exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
        exact (mul_le_mul_of_nonneg_left hucoll (by dsimp [wt]; split_ifs <;> norm_num)).trans_eq (mul_comm _ _)
      · simp [hdir, avgOver]
    unfold avgOver at hwt
    simp only [wt, mul_ite, mul_one, mul_zero] at hwt ⊢
    convert hwt using 1
    exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> rfl
  -- 3. Marginal comparisons and pasting on every opposite placement
  have hptU (val : (Fin L.m → ScalarQ L) → ℝ) :
      avgOver (linePointDist L) (fun s => val s.2) = avgOver (uniformDistribution (Fin L.m → ScalarQ L)) val := by
    rw [linePointDist, WinImplications.avgOver_mix,
      ← Distribution.avgOver_map (aLinePointDist L) Prod.snd val,
      ← Distribution.avgOver_map (dLinePointDist L) Prod.snd val,
      (aLinePointDist_point_marginal_uniform L).1, (dLinePointDist_point_marginal_uniform L).1]
    ring
  have hprodU (val : (Fin L.m → ScalarQ L) × (Fin L.m → ScalarQ L) → ℝ) :
      avgOver (Distribution.prod (linePointDist L) (linePointDist L)) (fun s => val (s.1.2, s.2.2)) =
        avgOver (uniformDistribution ((Fin L.m → ScalarQ L) × (Fin L.m → ScalarQ L))) val := by
    rw [uniformDistribution_prod, SandwichProduct.avgOver_distribution_prod, SandwichProduct.avgOver_distribution_prod]
    conv_lhs => arg 2; ext s; rw [hptU (fun pt => val (s.2, pt))]
    exact hptU (fun x => avgOver (uniformDistribution (Fin L.m → ScalarQ L)) fun y => val (x, y))
  have hopSome {Sample Answer : Type} [Fintype Answer] [DecidableEq Answer]
      (law : Distribution Sample) (p1 p2 : Placement)
      (M1 : Sample → Measurement Answer (S.ExpandedLocalSpace p1.side))
      (M2 : Sample → Measurement Answer (S.ExpandedLocalSpace p2.side)) :
      opFamilyDistSq law (fun s a => S.place p1 (((M1 s).postprocess some).effect a))
        (fun s a => S.place p2 (((M2 s).postprocess some).effect a)) S.psiHat =
      opFamilyDistSq law (fun s a => S.place p1 ((M1 s).effect a))
        (fun s a => S.place p2 ((M2 s).effect a)) S.psiHat := by
    unfold opFamilyDistSq
    congr 1; funext s; rw [Fintype.sum_option]
    simp [Measurement.postprocess, Submeasurement.postprocess, Finset.sum_filter, S.place_zero, applyOperatorToState]
  have hcons (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
      consistencyDefect (Distribution.prod (linePointDist L) (linePointDist L))
        (fun s a => S.place p1 (((S.combinedLineMeasurement p1.side s.1.1 s.2.1).postprocess
          fun fs => (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).effect a))
        (fun s a => S.place p2 (((points.Q p2.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2)).effect a))
        S.psiHat ≤ lineError ε (((P.m * P.d : ℕ) : ℝ) / (P.q : ℝ)) := by
    have hrev : p2.IsOpposite p1 := by cases p1 <;> cases p2 <;> trivial
    have hsymm : consistencyDefect (Distribution.prod (linePointDist L) (linePointDist L))
        (fun s a => S.place p1 (((S.combinedLineMeasurement p1.side s.1.1 s.2.1).postprocess
          fun fs => (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).effect a))
        (fun s a => S.place p2 (((points.Q p2.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2)).effect a))
        S.psiHat =
      consistencyDefect (Distribution.prod (linePointDist L) (linePointDist L))
        (fun s a => S.place p2 (((points.Q p2.side s.1.2 s.2.2).postprocess fun ab => (some ab.1, some ab.2)).effect a))
        (fun s a => S.place p1 (((S.combinedLineMeasurement p1.side s.1.1 s.2.1).postprocess
          fun fs => (evalOpt s.1.1 s.1.2 fs.1, evalOpt s.2.1 s.2.2 fs.2)).effect a))
        S.psiHat := by
      unfold consistencyDefect
      congr 1; funext s; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [S.place_comm p1 p2 hopp]; simp only [eq_comm]
    rw [hsymm]
    -- Same-placement line-point distance on p1
    have hLP_same (W : PauliKind) : opFamilyDistSq (linePointDist L)
        (fun s a => S.place p1 ((S.lineEvalMeasExp p1.side W s.1 s.2).effect a))
        (fun s a => S.place p1 ((S.pointMeasExpOption p1.side W s.2).effect a)) S.psiHat ≤
        1040 * (ε + deltaLine ε) := by
      have hp : opFamilyDistSq (linePointDist L)
          (fun s a => S.place p2 ((S.pointMeasExpOption p2.side W s.2).effect a))
          (fun s a => S.place p1 ((S.pointMeasExpOption p1.side W s.2).effect a)) S.psiHat ≤ 172 * ε := by
        unfold ProjectiveSetting.pointMeasExpOption
        erw [hopSome]
        unfold opFamilyDistSq
        rw [hptU (fun pt => ∑ a, ‖applyOperatorToState
          (S.place p2 ((S.pointMeasExp p2.side W pt).effect a) -
            S.place p1 ((S.pointMeasExp p1.side W pt).effect a)) S.psiHat‖ ^ 2)]
        exact exp_point_self_cons_explicit P ε S p2 p1 hrev W
      have htri := opFamilyDistSq_le_of_le_of_le (linePointDist L)
        (fun s a => S.place p1 ((S.lineEvalMeasExp p1.side W s.1 s.2).effect a))
        (fun s a => S.place p2 ((S.pointMeasExpOption p2.side W s.2).effect a))
        (fun s a => S.place p1 ((S.pointMeasExpOption p1.side W s.2).effect a)) S.psiHat _ _
        (exp_line_point_cons_explicit' P ε S p1 p2 hopp W) hp
      have := S.eps_nonneg; have : 0 ≤ deltaLine ε := Real.sqrt_nonneg ε; linarith
    -- Conditioned marginal defects on (p2, p1)
    have hmargX : consistencyDefect ndDist
        (fun q a => S.place p2 ((((points.Q p2.side q.2.2 q.1.2.2).postprocess
          (fun pair => (some pair.2, some pair.1))).postprocess Prod.snd).effect a))
        (fun q a => S.place p1 (((S.lineMeasExp p1.side .X q.1.1.1).postprocess
          (fun g => evalOpt q.2.1 q.2.2 g)).effect a)) S.psiHat ≤
        (8 * deltaQ ε + 2080 * (ε + deltaLine ε)) / ndMass := by
      have hsw (x z : Fin P.m → PauliScalar P) (a : Option (PauliScalar P)) :
          (((points.Q p2.side x z).postprocess (fun pair => (some pair.2, some pair.1))).postprocess Prod.snd).effect a =
            (((points.Q p2.side x z).postprocess Prod.fst).postprocess some).effect a := by
        simp only [Measurement.postprocess_comp]
      simp_rw [hsw]
      have hfst (x z : Fin P.m → PauliScalar P) (a : PauliScalar P) :
          ((points.Q p2.side x z).postprocess Prod.fst).effect a = ∑ b, (points.Q p2.side x z).effect (a, b) := by
        change (∑ p ∈ Finset.univ.filter (fun p : PauliScalar P × PauliScalar P => p.1 = a), _) = _
        simp only [Finset.sum_filter, Fintype.sum_prod_type]; rw [Finset.sum_comm]; simp
      let FX1 := fun (s : (LineDesc L × (Fin L.m → ScalarQ L)) × (LineDesc L × (Fin L.m → ScalarQ L))) a =>
        S.place p2 ((((points.Q p2.side s.1.2 s.2.2).postprocess Prod.fst).postprocess some).effect a)
      let FX2 := fun (s : (LineDesc L × (Fin L.m → ScalarQ L)) × (LineDesc L × (Fin L.m → ScalarQ L))) a =>
        S.place p1 ((S.pointMeasExpOption p1.side .X s.1.2).effect a)
      let FX3 := fun (s : (LineDesc L × (Fin L.m → ScalarQ L)) × (LineDesc L × (Fin L.m → ScalarQ L))) a =>
        S.place p1 ((S.lineEvalMeasExp p1.side .X s.1.1 s.1.2).effect a)
      have hm1 : opFamilyDistSq (Distribution.prod (linePointDist L) (linePointDist L)) FX1 FX2 S.psiHat ≤ 4 * deltaQ ε := by
        dsimp only [FX1, FX2]
        unfold ProjectiveSetting.pointMeasExpOption; erw [hopSome]
        simp_rw [hfst, S.place_finset_sum]
        unfold opFamilyDistSq
        rw [hprodU (fun xz => ∑ a, ‖applyOperatorToState
          ((∑ b, S.place p2 ((points.Q p2.side xz.1 xz.2).effect (a, b))) -
            S.place p1 ((S.pointMeasExp p1.side .X xz.1).effect a)) S.psiHat‖ ^ 2)]
        exact points.marginal_X_distance_le p2 p1 hrev
      have hm2 : opFamilyDistSq (Distribution.prod (linePointDist L) (linePointDist L)) FX2 FX3 S.psiHat ≤
          1040 * (ε + deltaLine ε) := by
        dsimp only [FX2, FX3]
        rw [opFamilyDistSq_symm]; unfold opFamilyDistSq
        rw [SandwichProduct.avgOver_distribution_prod]
        simp_rw [avgOver_const_of_isProbability _ (linePointDist_isProbability L)]
        exact hLP_same .X
      have huncond : consistencyDefect (Distribution.prod (linePointDist L) (linePointDist L)) FX1 FX3 S.psiHat ≤
          8 * deltaQ ε + 2080 * (ε + deltaLine ε) := by
        refine (consistencyDefect_le_opFamilyDistSq_of_projective (Distribution.prod (linePointDist L) (linePointDist L))
          (fun s => S.placedMeasurement p2 (((points.Q p2.side s.1.2 s.2.2).postprocess Prod.fst).postprocess some))
          (fun s => S.placedMeasurement p1 (S.lineEvalMeasExp p1.side .X s.1.1 s.1.2)) S.psiHat
          (fun _ => S.placedMeasurement_isProjective p2 _
            (SandwichProduct.postprocess_isProjective _
              (SandwichProduct.postprocess_isProjective _ (points.projective _ _ _) _) _))
          (fun _ => S.placedMeasurement_isProjective p1 _
            (SandwichProduct.postprocess_isProjective _ (S.lineMeasExp_isProjective _ _ _) _))).trans ?_
        have htri := opFamilyDistSq_le_of_le_of_le (Distribution.prod (linePointDist L) (linePointDist L))
          FX1 FX2 FX3 S.psiHat _ _ hm1 hm2
        dsimp only [ProjectiveSetting.placedMeasurement_effect, FX1, FX3] at htri ⊢; linarith
      dsimp only [ndDist]; unfold consistencyDefect; rw [Distribution.avgOver_map]
      exact (avgOver_restrict_le_div_mass _ _ _ _ fun s =>
        consistencyDefect_integrand_nonneg S p2 p1 hrev _ _).trans
        (div_le_div_of_nonneg_right huncond hndPos.le)
    have hmargZ : consistencyDefect ndDist
        (fun q a => S.place p2 ((((points.Q p2.side q.2.2 q.1.2.2).postprocess
          (fun pair => (some pair.2, some pair.1))).postprocess Prod.fst).effect a))
        (fun q a => S.place p1 (((S.lineMeasExp p1.side .Z q.1.1.2).postprocess
          (fun g => evalOpt q.1.2.1 q.1.2.2 g)).effect a)) S.psiHat ≤
        (8 * deltaQ ε + 2080 * (ε + deltaLine ε)) / ndMass := by
      have hsw (x z : Fin P.m → PauliScalar P) (a : Option (PauliScalar P)) :
          (((points.Q p2.side x z).postprocess (fun pair => (some pair.2, some pair.1))).postprocess Prod.fst).effect a =
            (((points.Q p2.side x z).postprocess Prod.snd).postprocess some).effect a := by
        simp only [Measurement.postprocess_comp]
      simp_rw [hsw]
      have hsnd (x z : Fin P.m → PauliScalar P) (b : PauliScalar P) :
          ((points.Q p2.side x z).postprocess Prod.snd).effect b = ∑ a, (points.Q p2.side x z).effect (a, b) := by
        change (∑ p ∈ Finset.univ.filter (fun p : PauliScalar P × PauliScalar P => p.2 = b), _) = _
        simp [Finset.sum_filter, Fintype.sum_prod_type]
      let FZ1 := fun (s : (LineDesc L × (Fin L.m → ScalarQ L)) × (LineDesc L × (Fin L.m → ScalarQ L))) a =>
        S.place p2 ((((points.Q p2.side s.1.2 s.2.2).postprocess Prod.snd).postprocess some).effect a)
      let FZ2 := fun (s : (LineDesc L × (Fin L.m → ScalarQ L)) × (LineDesc L × (Fin L.m → ScalarQ L))) a =>
        S.place p1 ((S.pointMeasExpOption p1.side .Z s.2.2).effect a)
      let FZ3 := fun (s : (LineDesc L × (Fin L.m → ScalarQ L)) × (LineDesc L × (Fin L.m → ScalarQ L))) a =>
        S.place p1 ((S.lineEvalMeasExp p1.side .Z s.2.1 s.2.2).effect a)
      have hm1 : opFamilyDistSq (Distribution.prod (linePointDist L) (linePointDist L)) FZ1 FZ2 S.psiHat ≤ 4 * deltaQ ε := by
        dsimp only [FZ1, FZ2]
        unfold ProjectiveSetting.pointMeasExpOption; erw [hopSome]
        simp_rw [hsnd, S.place_finset_sum]
        unfold opFamilyDistSq
        rw [hprodU (fun xz => ∑ b, ‖applyOperatorToState
          ((∑ a, S.place p2 ((points.Q p2.side xz.1 xz.2).effect (a, b))) -
            S.place p1 ((S.pointMeasExp p1.side .Z xz.2).effect b)) S.psiHat‖ ^ 2)]
        exact points.marginal_Z_distance_le p2 p1 hrev
      have hm2 : opFamilyDistSq (Distribution.prod (linePointDist L) (linePointDist L)) FZ2 FZ3 S.psiHat ≤
          1040 * (ε + deltaLine ε) := by
        dsimp only [FZ2, FZ3]
        rw [opFamilyDistSq_symm]; unfold opFamilyDistSq
        rw [SandwichProduct.avgOver_distribution_prod]
        erw [avgOver_const_of_isProbability _ (linePointDist_isProbability L)
          (opFamilyDistSq (linePointDist L)
            (fun s a => S.place p1 ((S.lineEvalMeasExp p1.side .Z s.1 s.2).effect a))
            (fun s a => S.place p1 ((S.pointMeasExpOption p1.side .Z s.2).effect a)) S.psiHat)]
        exact hLP_same .Z
      have huncond : consistencyDefect (Distribution.prod (linePointDist L) (linePointDist L)) FZ1 FZ3 S.psiHat ≤
          8 * deltaQ ε + 2080 * (ε + deltaLine ε) := by
        refine (consistencyDefect_le_opFamilyDistSq_of_projective (Distribution.prod (linePointDist L) (linePointDist L))
          (fun s => S.placedMeasurement p2 (((points.Q p2.side s.1.2 s.2.2).postprocess Prod.snd).postprocess some))
          (fun s => S.placedMeasurement p1 (S.lineEvalMeasExp p1.side .Z s.2.1 s.2.2)) S.psiHat
          (fun _ => S.placedMeasurement_isProjective p2 _
            (SandwichProduct.postprocess_isProjective _
              (SandwichProduct.postprocess_isProjective _ (points.projective _ _ _) _) _))
          (fun _ => S.placedMeasurement_isProjective p1 _
            (SandwichProduct.postprocess_isProjective _ (S.lineMeasExp_isProjective _ _ _) _))).trans ?_
        have htri := opFamilyDistSq_le_of_le_of_le (Distribution.prod (linePointDist L) (linePointDist L))
          FZ1 FZ2 FZ3 S.psiHat _ _ hm1 hm2
        dsimp only [ProjectiveSetting.placedMeasurement_effect, FZ1, FZ3] at htri ⊢; linarith
      dsimp only [ndDist]; unfold consistencyDefect; rw [Distribution.avgOver_map]
      exact (avgOver_restrict_le_div_mass _ _ _ _ fun s =>
        consistencyDefect_integrand_nonneg S p2 p1 hrev _ _).trans
        (div_le_div_of_nonneg_right huncond hndPos.le)
    -- Apply heterogeneous pasting
    obtain ⟨eqv, hf1, hf2⟩ := S.exists_opposite_bipartition p2 p1 hrev
    have hp0 := points.delta_nonneg
    have herr0 : 0 ≤ (8 * deltaQ ε + 2080 * (ε + deltaLine ε)) / ndMass :=
      div_nonneg (add_nonneg (by linarith) (mul_nonneg (by norm_num) (add_nonneg S.eps_nonneg (Real.sqrt_nonneg _)))) hndPos.le
    have hndProb : ndDist.IsProbability := (Distribution.restrict_isProbability _ _ hndPos).map _
    have heval_hk {A1 A2 R0 C0 U0 : Type} [Fintype A1] [Fintype A2] [DecidableEq R0]
        [Fintype C0] [DecidableEq C0] [Fintype U0] [DecidableEq U0]
        (m1 : A1 → Op C0) (m2 : A2 → Op C0) (ev : A1 → A2 → R0) (out : R0) :
        (∑ a1, ∑ a2, if ev a1 a2 = out then
          pastedMeasurement (fun a => heteroKron (m1 a) (1 : Op U0)) (fun a => heteroKron (m2 a) (1 : Op U0)) a1 a2 else 0) =
        heteroKron (∑ a1, ∑ a2, if ev a1 a2 = out then pastedMeasurement m1 m2 a1 a2 else 0) (1 : Op U0) := by
      simp only [pastedMeasurement, heteroKron_mul, mul_one]
      ext r c; simp [heteroKron, Matrix.kronecker, Matrix.sum_apply, Matrix.ite_apply, Finset.sum_mul, ite_mul]
    have hdef_bip {Q0 Ans : Type} [Fintype Q0] [DecidableEq Q0] [Fintype Ans] [DecidableEq Ans]
        (law : Distribution Q0)
        (F1 : Q0 → Ans → Op (S.ExpandedLocalSpace p2.side))
        (F2 : Q0 → Ans → Op (S.ExpandedLocalSpace p1.side)) :
        consistencyDefect law (fun q o => heteroKron (F1 q o) 1)
          (fun q o => heteroKron 1 (heteroKron (F2 q o) (1 : Op (PauliRegister P × PauliRegister P))))
          (reindexState eqv S.psiHat) =
        consistencyDefect law (fun q o => S.place p2 (F1 q o)) (fun q o => S.place p1 (F2 q o)) S.psiHat := by
      unfold consistencyDefect
      congr 1; funext q; refine Finset.sum_congr rfl fun o1 _ => Finset.sum_congr rfl fun o2 _ => ?_
      split_ifs
      · rfl
      · rw [consistency_term_eq_stateQForm, consistency_term_eq_stateQForm,
          WinImplications.stateQForm_reindexState, WinImplications.reindexOp_mul, hf1, hf2]
    have hpast := pasting_error_heterogeneous_explicit ndDist
      (fun (poly : DegPoly L (P.m * P.d)) s => evalOpt s.1 s.2 poly)
      (fun (poly : DegPoly L (P.m * P.d)) s => evalOpt s.1 s.2 poly)
      (fun pair => leftPlacedMeasurement (ιB := PauliRegister P × PauliRegister P) (S.lineMeasExp p1.side .Z pair.2))
      (fun pair => leftPlacedMeasurement (ιB := PauliRegister P × PauliRegister P) (S.lineMeasExp p1.side .X pair.1))
      (fun q => (points.Q p2.side q.2.2 q.1.2.2).postprocess (fun pair => (some pair.2, some pair.1)))
      (reindexState eqv S.psiHat)
      ((P.m * P.d : ℕ) / (Fintype.card (ScalarQ L) : ℝ))
      ((8 * deltaQ ε + 2080 * (ε + deltaLine ε)) / ndMass)
      hndProb (by rw [reindexState_norm_eq, S.psiHat_norm]) (by positivity) herr0
      (fun pair => MIPStarRE.QPBT.Measurement.isProjective_leftPlacement _ (S.lineMeasExp_isProjective p1.side .X pair.1))
      (fun _ => SandwichProduct.postprocess_isProjective _ (points.projective _ _ _) _)
      hcoll
      (by simp_rw [leftPlacedMeasurement_postprocess_effect]; exact (hdef_bip ndDist _ _).trans_le hmargZ)
      (by simp_rw [leftPlacedMeasurement_postprocess_effect]; exact (hdef_bip ndDist _ _).trans_le hmargX)
    simp only [leftPlacedMeasurement, Measurement.ofSumEqOne] at hpast
    simp_rw [heval_hk, hdef_bip] at hpast
    have hcond_zx : consistencyDefect ndDist
        (fun q o => S.place p2 (((points.Q p2.side q.2.2 q.1.2.2).postprocess (fun pair => (some pair.2, some pair.1))).effect o))
        (fun q o => S.place p1 (((S.combinedLineMeasurement p1.side q.1.1.1 q.1.1.2).postprocess
          (fun polys => (evalOpt q.1.1.2 q.1.2.2 polys.2, evalOpt q.1.1.1 q.2.2 polys.1))).effect o)) S.psiHat ≤
        heterogeneousPastingError ((P.m * P.d : ℕ) / (Fintype.card (ScalarQ L) : ℝ))
          ((8 * deltaQ ε + 2080 * (ε + deltaLine ε)) / ndMass) := by
      have hev_past (lX lZ : LineDesc L) (ptX ptZ : Fin P.m → PauliScalar P) (out : Option (PauliScalar P) × Option (PauliScalar P)) :
          ((S.combinedLineMeasurement p1.side lX lZ).postprocess
            (fun polys => (evalOpt lZ ptZ polys.2, evalOpt lX ptX polys.1))).effect out =
          ∑ pZ, ∑ pX, if (evalOpt lZ ptZ pZ, evalOpt lX ptX pX) = out then
            pastedMeasurement (S.lineMeasExp p1.side .Z lZ).effect (S.lineMeasExp p1.side .X lX).effect pZ pX else 0 := by
        rw [Measurement.postprocess_effect, Finset.sum_filter, Fintype.sum_prod_type]
        exact Finset.sum_comm
      have heq_past : consistencyDefect ndDist
          (fun q o => S.place p2 (((points.Q p2.side q.2.2 q.1.2.2).postprocess (fun pair => (some pair.2, some pair.1))).effect o))
          (fun q o => S.place p1 (((S.combinedLineMeasurement p1.side q.1.1.1 q.1.1.2).postprocess
            (fun polys => (evalOpt q.1.1.2 q.1.2.2 polys.2, evalOpt q.1.1.1 q.2.2 polys.1))).effect o)) S.psiHat =
        consistencyDefect ndDist
          (fun q o => S.place p2 (((points.Q p2.side q.2.2 q.1.2.2).postprocess (fun pair => (some pair.2, some pair.1))).effect o))
          (fun q o => S.place p1 (∑ pZ, ∑ pX, if (evalOpt q.1.2.1 q.1.2.2 pZ, evalOpt q.2.1 q.2.2 pX) = o then
            pastedMeasurement (S.lineMeasExp p1.side .Z q.1.1.2).effect (S.lineMeasExp p1.side .X q.1.1.1).effect pZ pX else 0))
          S.psiHat := by
        dsimp only [ndDist]; unfold consistencyDefect; rw [Distribution.avgOver_map, Distribution.avgOver_map]
        dsimp only; simp_rw [hev_past]
      rw [heq_past]; unfold heterogeneousPastingError
      exact hpast
    -- Swap answer pair back to X-then-Z and restore discarded zero-X-direction mass
    have hsw_eff {Ans C0 : Type} [Fintype Ans] [DecidableEq Ans] [Fintype C0] [DecidableEq C0]
        (M : Measurement Ans C0) (ev : Ans → Option (PauliScalar P) × Option (PauliScalar P))
        (out : Option (PauliScalar P) × Option (PauliScalar P)) :
        (M.postprocess (fun a => (ev a).swap)).effect out = (M.postprocess ev).effect out.swap := by
      simp only [Measurement.postprocess_effect]; congr 1; ext a; simp [Prod.ext_iff, and_comm]
    have hswP (x z : Fin P.m → PauliScalar P) (o : Option (PauliScalar P) × Option (PauliScalar P)) :
        ((points.Q p2.side x z).postprocess (fun pair => (some pair.2, some pair.1))).effect o =
          ((points.Q p2.side x z).postprocess (fun pair => (some pair.1, some pair.2))).effect o.swap :=
      hsw_eff (points.Q p2.side x z) (fun pair => (some pair.1, some pair.2)) o
    have hswL (lX lZ : LineDesc L) (ptX ptZ : Fin P.m → PauliScalar P) (o : Option (PauliScalar P) × Option (PauliScalar P)) :
        ((S.combinedLineMeasurement p1.side lX lZ).postprocess
          (fun polys => (evalOpt lZ ptZ polys.2, evalOpt lX ptX polys.1))).effect o =
        ((S.combinedLineMeasurement p1.side lX lZ).postprocess
          (fun polys => (evalOpt lX ptX polys.1, evalOpt lZ ptZ polys.2))).effect o.swap :=
      hsw_eff (S.combinedLineMeasurement p1.side lX lZ) (fun polys => (evalOpt lX ptX polys.1, evalOpt lZ ptZ polys.2)) o
    simp_rw [hswP, hswL] at hcond_zx
    have hcond_xz : consistencyDefect ndDist
        (fun q o => S.place p2 (((points.Q p2.side q.2.2 q.1.2.2).postprocess (fun pair => (some pair.1, some pair.2))).effect o))
        (fun q o => S.place p1 (((S.combinedLineMeasurement p1.side q.1.1.1 q.1.1.2).postprocess
          (fun polys => (evalOpt q.1.1.1 q.2.2 polys.1, evalOpt q.1.1.2 q.1.2.2 polys.2))).effect o)) S.psiHat ≤
        heterogeneousPastingError ((P.m * P.d : ℕ) / (Fintype.card (ScalarQ L) : ℝ))
          ((8 * deltaQ ε + 2080 * (ε + deltaLine ε)) / ndMass) :=
      (consistencyDefect_outcome_equiv ndDist (Equiv.prodComm _ _) _ _ S.psiHat).symm.trans_le hcond_zx
    have hrest : consistencyDefect (Distribution.prod (linePointDist L) (linePointDist L))
        (fun s o => S.place p2 (((points.Q p2.side s.1.2 s.2.2).postprocess (fun pair => (some pair.1, some pair.2))).effect o))
        (fun s o => S.place p1 (((S.combinedLineMeasurement p1.side s.1.1 s.2.1).postprocess
          (fun polys => (evalOpt s.1.1 s.1.2 polys.1, evalOpt s.2.1 s.2.2 polys.2))).effect o)) S.psiHat ≤
        ndMass * heterogeneousPastingError ((P.m * P.d : ℕ) / (Fintype.card (ScalarQ L) : ℝ))
          ((8 * deltaQ ε + 2080 * (ε + deltaLine ε)) / ndMass) + 1 / (2 * Fintype.card (ScalarQ L)) := by
      have hdisc : (∑ s ∈ (Distribution.prod (linePointDist L) (linePointDist L)).support.filter (fun s => ¬ s.1.1.direction ≠ 0),
          (Distribution.prod (linePointDist L) (linePointDist L)).weight s) ≤ 1 / (2 * Fintype.card (ScalarQ L)) := by
        rw [Distribution.sum_filter_weight_eq_avgOver]
        simpa only [ne_eq, not_not] using hpZero
      dsimp only [ndDist] at hcond_xz
      unfold consistencyDefect at hcond_xz ⊢
      rw [Distribution.avgOver_map] at hcond_xz
      dsimp only at hcond_xz
      let MP (s : (LineDesc L × (Fin L.m → ScalarQ L)) × (LineDesc L × (Fin L.m → ScalarQ L))) :=
        (points.Q p2.side s.1.2 s.2.2).postprocess (fun pair => (some pair.1, some pair.2))
      let ML (s : (LineDesc L × (Fin L.m → ScalarQ L)) × (LineDesc L × (Fin L.m → ScalarQ L))) :=
        (S.combinedLineMeasurement p1.side s.1.1 s.2.1).postprocess
          (fun polys => (evalOpt s.1.1 s.1.2 polys.1, evalOpt s.2.1 s.2.2 polys.2))
      have hsplit := avgOver_le_restrict_add_discarded_mass
        (Distribution.prod (linePointDist L) (linePointDist L))
        (fun s => s.1.1.direction ≠ 0) hndPos
        (fun s => ∑ o1, ∑ o2, if o1 = o2 then 0 else
          stateQForm S.psiHat (S.place p2 ((MP s).effect o1) * S.place p1 ((ML s).effect o2)))
        (fun s => consistencyDefect_integrand_le_one S p2 p1 hrev (MP s) (ML s))
      exact hsplit.trans (add_le_add (mul_le_mul_of_nonneg_left hcond_xz hndPos.le) hdisc)
    -- Final polynomial bound & unit cap
    have hcard : Fintype.card (ScalarQ L) = P.q := @FieldModel.card P.q P.model.toFieldModel
    have hrest_q : consistencyDefect (Distribution.prod (linePointDist L) (linePointDist L))
        (fun s o => S.place p2 (((points.Q p2.side s.1.2 s.2.2).postprocess (fun pair => (some pair.1, some pair.2))).effect o))
        (fun s o => S.place p1 (((S.combinedLineMeasurement p1.side s.1.1 s.2.1).postprocess
          (fun polys => (evalOpt s.1.1 s.1.2 polys.1, evalOpt s.2.1 s.2.2 polys.2))).effect o)) S.psiHat ≤
        ndMass * heterogeneousPastingError ((P.m * P.d : ℕ) / (P.q : ℝ))
          ((8 * deltaQ ε + 2080 * (ε + deltaLine ε)) / ndMass) + 1 / (2 * (P.q : ℝ)) :=
      hrest.trans_eq (by rw [hcard])
    have hq : (0 : ℝ) < P.q := by rw [← hcard]; exact_mod_cast Fintype.card_pos (α := ScalarQ L)
    have hmd : (1 : ℝ) ≤ (P.m * P.d : ℕ) := by exact_mod_cast Nat.mul_pos P.one_le_m P.hd
    have hdisc_md : 1 / (2 * (P.q : ℝ)) ≤ (P.m * P.d : ℕ) / (P.q : ℝ) :=
      (one_div_le_one_div_of_le hq (by linarith)).trans (div_le_div_of_nonneg_right hmd hq.le)
    have hunit : consistencyDefect (Distribution.prod (linePointDist L) (linePointDist L))
        (fun s o => S.place p2 (((points.Q p2.side s.1.2 s.2.2).postprocess (fun pair => (some pair.1, some pair.2))).effect o))
        (fun s o => S.place p1 (((S.combinedLineMeasurement p1.side s.1.1 s.2.1).postprocess
          (fun polys => (evalOpt s.1.1 s.1.2 polys.1, evalOpt s.2.1 s.2.2 polys.2))).effect o)) S.psiHat ≤ 1 := by
      unfold consistencyDefect
      exact (avgOver_mono (Distribution.prod (linePointDist L) (linePointDist L))
        (fun s => ∑ o1, ∑ o2, if o1 = o2 then 0 else stateQForm S.psiHat
          (S.place p2 (((points.Q p2.side s.1.2 s.2.2).postprocess (fun pair => (some pair.1, some pair.2))).effect o1) *
            S.place p1 (((S.combinedLineMeasurement p1.side s.1.1 s.2.1).postprocess
              (fun polys => (evalOpt s.1.1 s.1.2 polys.1, evalOpt s.2.1 s.2.2 polys.2))).effect o2)))
        (fun _ => 1) fun s => consistencyDefect_integrand_le_one S p2 p1 hrev
          ((points.Q p2.side s.1.2 s.2.2).postprocess (fun pair => (some pair.1, some pair.2)))
          ((S.combinedLineMeasurement p1.side s.1.1 s.2.1).postprocess
            (fun polys => (evalOpt s.1.1 s.1.2 polys.1, evalOpt s.2.1 s.2.2 polys.2)))).trans_eq
        (avgOver_const_of_isProbability _
          (Distribution.prod_isProbability _ _ (linePointDist_isProbability L) (linePointDist_isProbability L)) 1)
    exact (le_min hunit (hrest_q.trans (add_le_add le_rfl hdisc_md))).trans
      (hscalar ε _ _ S.eps_nonneg (by positivity) hndBounds.1 hndBounds.2)
  exact ⟨{
    T := S.combinedLineMeasurement
    axis_degree_X := S.combinedLineMeasurement_axis_degree_X
    axis_degree_Z := S.combinedLineMeasurement_axis_degree_Z
    consistent := hcons }⟩

end

end MIPStarRE.QPBT
