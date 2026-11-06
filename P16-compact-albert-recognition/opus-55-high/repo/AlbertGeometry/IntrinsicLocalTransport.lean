module

public import AlbertGeometry.ActualU2NativeGeometry
public import Glennie.Compact.LocalReconstruction

@[expose] public section
namespace AlbertGeometry.IntrinsicLocalTransport
noncomputable section

open Glennie
open AlbertGeometry.Cubic AlbertGeometry.BasedNormAdjointTransport
open Glennie.Compact.Affine20 Glennie.Compact.NativeQFamilyLedger Glennie.Compact.OperationalPhi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)
  (he : diagonalCubic P.form e = 1)
  (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)

/-- The trace of the recovered algebra, specified by the actual based metric. -/
def sourceTrace (x : E) : ℝ := 3 * logHessianForm P e x e

/-- The recovered product from the based cubic and its nondegenerate trace form. -/
def sourceProduct (x y : E) : E :=
  intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y

/-- Ordered source frames use the recovered trace, product, and unit. -/
structure SourceFrame (p : Fin 3 → E) : Prop where
  trace_one : ∀ i, sourceTrace P e (p i) = 1
  idempotent : ∀ i, sourceProduct P e he hp (p i) (p i) = p i
  orthogonal : ∀ i j, i ≠ j → sourceProduct P e he hp (p i) (p j) = 0
  sum_unit : p 0 + p 1 + p 2 = e

abbrev SourceTriple (E : Type*) := Fin 3 → Fin 3 → E

def mapTriple (A : E ≃ₗ[ℝ] Albert) (T : SourceTriple E) : Triple := fun a i => A (T a i)

def pullTriple (A : E ≃ₗ[ℝ] Albert) (T : Triple) : SourceTriple E :=
  fun a i => A.symm (T a i)

theorem mapTriple_pullTriple (A : E ≃ₗ[ℝ] Albert) (T : Triple) :
    mapTriple A (pullTriple A T) = T :=
  funext fun _ => funext fun _ => A.apply_symm_apply _

/-- The fixed frame encoder uses slot 2 minus slot 0. -/
def sourceEncoder (p : Fin 3 → E) : E := p 2 - p 0

theorem sourceEncoder_map (A : E ≃ₗ[ℝ] Albert) (p : Fin 3 → E) :
    A (sourceEncoder p) = encoder (fun i => A (p i)) := by simp [sourceEncoder, encoder, map_sub]

/-- The pairing of the recovered algebra. -/
def sourceInner (x y : E) : ℝ :=
  sourceTrace P e (sourceProduct P e he hp x y)

/-- The quadratic representation in the recovered algebra. -/
def sourceU (x z : E) : E :=
  (2 : ℝ) • sourceProduct P e he hp x (sourceProduct P e he hp x z) -
    sourceProduct P e he hp (sourceProduct P e he hp x x) z

/-- The signed degree-nine scalar formed entirely from the recovered product and pairing. -/
def sourcePhi (x y z : E) : ℝ :=
  sourceInner P e he hp
    (sourceU P e he hp x (sourceU P e he hp y z) -
      sourceU P e he hp y (sourceU P e he hp x z))
    (sourceU P e he hp z (sourceProduct P e he hp x y))

/-- The complete ordered overlap ledger formed from the recovered algebra. -/
def sourceLedger54 (T : SourceTriple E) : Ledger54 :=
  (fun i j k => sourceTrace P e
      (sourceProduct P e he hp
        (sourceProduct P e he hp (T 0 i) (T 1 j)) (T 2 k)),
    fun i j => sourceInner P e he hp (T 0 i) (T 1 j),
    fun j k => sourceInner P e he hp (T 1 j) (T 2 k),
    fun k i => sourceInner P e he hp (T 2 k) (T 0 i))

/-- The two fixed encoder powers used by the 26-value script. -/
def sourceFramePower (p : Fin 3 → E) (s : Fin 2) : E :=
  if s = 0 then sourceEncoder p
  else sourceProduct P e he hp (sourceEncoder p) (sourceEncoder p)

def sourceQSingle (T : SourceTriple E) (v : Fin 3) (s : Fin 2) : ℝ :=
  sourceInner P e he hp (sourceFramePower P e he hp (T v) 0)
    (sourceFramePower P e he hp (T v) s)

def sourceQPair (T : SourceTriple E) (v w : Fin 3) (s t : Fin 2) : ℝ :=
  sourceInner P e he hp (sourceFramePower P e he hp (T v) s)
    (sourceFramePower P e he hp (T w) t)

def sourceQTriple (T : SourceTriple E) (s t u : Fin 2) : ℝ :=
  sourceTrace P e
    (sourceProduct P e he hp
      (sourceProduct P e he hp
        (sourceFramePower P e he hp (T 0) s)
        (sourceFramePower P e he hp (T 1) t))
      (sourceFramePower P e he hp (T 2) u))

/-- The explicit order of the native 26 scalar expressions, in source operations. -/
def sourceQ26 (T : SourceTriple E) : Fin 26 → ℝ := ![
  sourceQSingle P e he hp T 0 0, sourceQSingle P e he hp T 0 1,
  sourceQSingle P e he hp T 1 0, sourceQSingle P e he hp T 1 1,
  sourceQSingle P e he hp T 2 0, sourceQSingle P e he hp T 2 1,
  sourceQPair P e he hp T 0 1 0 0, sourceQPair P e he hp T 0 1 0 1,
  sourceQPair P e he hp T 0 1 1 0, sourceQPair P e he hp T 0 1 1 1,
  sourceQPair P e he hp T 1 2 0 0, sourceQPair P e he hp T 1 2 0 1,
  sourceQPair P e he hp T 1 2 1 0, sourceQPair P e he hp T 1 2 1 1,
  sourceQPair P e he hp T 2 0 0 0, sourceQPair P e he hp T 2 0 0 1,
  sourceQPair P e he hp T 2 0 1 0, sourceQPair P e he hp T 2 0 1 1,
  sourceQTriple P e he hp T 0 0 0, sourceQTriple P e he hp T 0 0 1,
  sourceQTriple P e he hp T 0 1 0, sourceQTriple P e he hp T 0 1 1,
  sourceQTriple P e he hp T 1 0 0, sourceQTriple P e he hp T 1 0 1,
  sourceQTriple P e he hp T 1 1 0, sourceQTriple P e he hp T 1 1 1]

/-- The unnormalized half amplitude in the recovered algebra. -/
def sourceHalfAmplitude (x : E) : E := (1 / 2 : ℝ) • (e + x)

def sourceContrast (x y z v : E) : ℝ :=
  sourceInner P e he hp z
    (sourceU P e he hp y (sourceU P e he hp x (sourceU P e he hp z v)) -
      sourceU P e he hp x (sourceU P e he hp y (sourceU P e he hp z v)))

def sourceDelta (x y z a rho : E) : ℝ :=
  sourceContrast P e he hp x y z (sourceU P e he hp a rho)

/-- The three fixed-orientation algebraic contrasts on the trace-zero encoders. -/
def sourceScore (T : SourceTriple E) : ℝ :=
  let x := sourceEncoder (T 0)
  let y := sourceEncoder (T 1)
  let z := sourceEncoder (T 2)
  4 * sourceDelta P e he hp x y z (sourceHalfAmplitude e x) y -
    sourceDelta P e he hp x y z x y - sourceDelta P e he hp x y z e y

/-- The complete source product-and-trace automorphism group. -/
structure SourceAutomorphism where
  equiv : E ≃ₗ[ℝ] E
  map_product : ∀ x y,
    equiv (sourceProduct P e he hp x y) =
      sourceProduct P e he hp (equiv x) (equiv y)
  map_trace : ∀ x, sourceTrace P e (equiv x) = sourceTrace P e x

def sourceMapAtoms (g : SourceAutomorphism P e he hp)
    (T : SourceTriple E) : SourceTriple E := fun a i => g.equiv (T a i)

def sourceAutOrbit (T : SourceTriple E) : Set (SourceTriple E) :=
  {S | ∃ g : SourceAutomorphism P e he hp, sourceMapAtoms P e he hp g T = S}

/-- Actual ordered-frame fibres in the source algebra, at the decoded chart ledger. -/
def sourceFibre54 (b : Fin 20 → ℝ) : Set (SourceTriple E) :=
  {T | (∀ a, SourceFrame P e he hp (T a)) ∧
    sourceLedger54 P e he hp T = decode20 b}

def sourceFibre20 (b : Fin 20 → ℝ) : Set (SourceTriple E) :=
  {T | (∀ a, SourceFrame P e he hp (T a)) ∧
    encode20 (sourceLedger54 P e he hp T) = b}

def SameSourceScoreSign (T S : SourceTriple E) : Prop :=
  (sourceScore P e he hp T < 0 ∧ sourceScore P e he hp S < 0) ∨
    (0 < sourceScore P e he hp T ∧ 0 < sourceScore P e he hp S)

/-- Exact source-side local fibre and section conclusion. -/
def TwoOrbitSections (V : Set (Fin 20 → ℝ)) : Prop :=
  ∃ secPos secNeg : (Fin 20 → ℝ) → SourceTriple E,
    ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
    (∀ b ∈ V, ∀ a, SourceFrame P e he hp (secPos b a)) ∧
    (∀ b ∈ V, ∀ a, SourceFrame P e he hp (secNeg b a)) ∧
    (∀ b ∈ V, sourceLedger54 P e he hp (secPos b) =
      decode20 b) ∧
    (∀ b ∈ V, sourceLedger54 P e he hp (secNeg b) =
      decode20 b) ∧
    (∀ b ∈ V, 0 < sourceScore P e he hp (secPos b)) ∧
    (∀ b ∈ V, sourceScore P e he hp (secNeg b) < 0) ∧
    (∀ b ∈ V, sourceFibre54 P e he hp b =
      sourceAutOrbit P e he hp (secNeg b) ∪
        sourceAutOrbit P e he hp (secPos b)) ∧
    (∀ b ∈ V, Disjoint
      (sourceAutOrbit P e he hp (secNeg b))
      (sourceAutOrbit P e he hp (secPos b))) ∧
    (∀ b ∈ V, sourceFibre20 P e he hp b = sourceFibre54 P e he hp b)

/-- Exact source-side finite-observation orbit test on actual ordered frames. -/
def ScoreComplete (V : Set (Fin 20 → ℝ)) : Prop :=
  ∀ T S : SourceTriple E,
    (∀ a, SourceFrame P e he hp (T a)) →
    (∀ a, SourceFrame P e he hp (S a)) →
    encode20 (sourceLedger54 P e he hp T) ∈ V →
    sourceScore P e he hp T ≠ 0 ∧
    ((T ∈ sourceAutOrbit P e he hp S) ↔
      sourceQ26 P e he hp T = sourceQ26 P e he hp S ∧
        SameSourceScoreSign P e he hp T S)

/-- A linear equivalence onto the native algebra carrying the unit, metric and product. -/
structure IsModel (A : E ≃ₗ[ℝ] Albert) : Prop where
  unit : A e = 1
  metric : ∀ x y : E, logHessianForm P e x y = trace (jordan (A x) (A y)) / 3
  product : ∀ x y : E,
    A (intrinsicProduct P e (rawBilinearForm_nondegenerate P e he hp) x y) = jordan (A x) (A y)

variable {P e he hp} {A : E ≃ₗ[ℝ] Albert} (hA : IsModel P e he hp A)
include hA

theorem sourceTrace_eq (x : E) : sourceTrace P e x = trace (A x) := by
  rw [sourceTrace, hA.metric x e, hA.unit, jordan_unit_right]
  ring

theorem sourceProduct_map (x y : E) :
    A (sourceProduct P e he hp x y) = jordan (A x) (A y) :=
  hA.product x y

theorem sourceFrame_iff (p : Fin 3 → E) :
    SourceFrame P e he hp p ↔ Frame (fun i => A (p i)) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_, fun i j hij => ?_, ?_⟩
    · rw [← sourceTrace_eq hA]; exact h.trace_one i
    · rw [← sourceProduct_map hA, h.idempotent]
    · rw [← sourceProduct_map hA, h.orthogonal i j hij, map_zero]
    · simpa [← map_add, h.sum_unit, hA.unit]
  · intro h
    refine ⟨fun i => ?_, fun i => A.injective ?_, fun i j hij => A.injective ?_, A.injective ?_⟩
    · rw [sourceTrace_eq hA]; exact h.trace_one i
    · rw [sourceProduct_map hA]; exact h.idempotent i
    · rw [sourceProduct_map hA, map_zero]; exact h.orthogonal i j hij
    · simpa [map_add, hA.unit] using h.sum_unit

theorem sourceTriple_frames_iff (T : SourceTriple E) :
    (∀ a, SourceFrame P e he hp (T a)) ↔ (∀ a, Frame (mapTriple A T a)) :=
  forall_congr' fun a => sourceFrame_iff hA (T a)

theorem sourceInner_eq (x y : E) :
    sourceInner P e he hp x y = inner (A x) (A y) := by
  rw [sourceInner, sourceTrace_eq hA, sourceProduct_map hA]
  rfl

theorem sourceU_map (x z : E) : A (sourceU P e he hp x z) = U (A x) (A z) := by
  simp [sourceU, U, map_sub, map_smul, sourceProduct_map hA]

theorem sourcePhi_eq (x y z : E) :
    sourcePhi P e he hp x y z = phi (A x) (A y) (A z) := by
  simp [sourcePhi, sourceInner_eq hA, map_sub, sourceU_map hA, sourceProduct_map hA, phi]

theorem sourceLedger54_eq (T : SourceTriple E) :
    sourceLedger54 P e he hp T = ledger54 (mapTriple A T) := by
  simp [sourceLedger54, sourceTrace_eq hA, sourceProduct_map hA, sourceInner_eq hA]
  rfl

theorem sourceFramePower_map (p : Fin 3 → E) (s : Fin 2) :
    A (sourceFramePower P e he hp p s) = framePower (fun i => A (p i)) s := by
  by_cases hs : s = 0 <;> simp [sourceFramePower, framePower, hs, ↓reduceIte,
    sourceProduct_map hA, sourceEncoder_map]

theorem sourceQ26_eq (T : SourceTriple E) :
    sourceQ26 P e he hp T = q26 (mapTriple A T) := by
  funext i
  fin_cases i <;> simp [sourceQ26, q26, sourceQSingle, sourceQPair, sourceQTriple,
    sourceInner_eq hA, sourceTrace_eq hA, sourceProduct_map hA, sourceFramePower_map hA] <;> rfl

/-- Q26 and the full ledger have identical equality data on actual source frames. -/
theorem sourceQ26_eq_iff_ledger54_eq (T S : SourceTriple E)
    (hT : ∀ a, SourceFrame P e he hp (T a))
    (hS : ∀ a, SourceFrame P e he hp (S a)) :
    sourceQ26 P e he hp T = sourceQ26 P e he hp S ↔
      sourceLedger54 P e he hp T = sourceLedger54 P e he hp S := by
  rw [sourceQ26_eq hA, sourceQ26_eq hA, sourceLedger54_eq hA, sourceLedger54_eq hA]
  exact q26_eq_iff_ledger54_eq _ _ ((sourceTriple_frames_iff hA T).mp hT)
    ((sourceTriple_frames_iff hA S).mp hS)

theorem sourceDelta_eq (x y z a rho : E) :
    sourceDelta P e he hp x y z a rho = delta (A x) (A y) (A z) (A a) (A rho) := by
  simp [sourceDelta, sourceContrast, sourceInner_eq hA, map_sub, sourceU_map hA]
  rfl

theorem sourceScore_eq (T : SourceTriple E) :
    sourceScore P e he hp T = Glennie.Compact.LocalContrast.score (mapTriple A T) := by
  simp only [sourceScore, Glennie.Compact.LocalContrast.score, sourceDelta_eq hA,
    sourceHalfAmplitude, map_smul, map_add, hA.unit, sourceEncoder_map]
  rfl

theorem sourceScore_eq_twoPhi (T : SourceTriple E) :
    sourceScore P e he hp T =
      2 * sourcePhi P e he hp (sourceEncoder (T 0))
        (sourceEncoder (T 1)) (sourceEncoder (T 2)) := by
  rw [sourceScore_eq hA, Glennie.Compact.LocalContrast.score_eq_two_phi, sourcePhi_eq hA]
  simp [Glennie.Compact.Sections.phiOf, sourceEncoder_map]
  rfl

def sourceAutToNative (g : SourceAutomorphism P e he hp) : CompactAutomorphism where
  equiv := (A.symm.trans g.equiv).trans A
  map_jordan x y := by
    have hpre : A.symm (jordan x y) = sourceProduct P e he hp (A.symm x) (A.symm y) :=
      A.injective (by simp [A.apply_symm_apply, sourceProduct_map hA])
    change A (g.equiv (A.symm (jordan x y))) =
      jordan (A (g.equiv (A.symm x))) (A (g.equiv (A.symm y)))
    rw [hpre, g.map_product, sourceProduct_map hA]
  map_trace x := by
    change trace (A (g.equiv (A.symm x))) = trace x
    rw [← sourceTrace_eq hA, g.map_trace, sourceTrace_eq hA, A.apply_symm_apply]

def nativeAutToSource (k : CompactAutomorphism) : SourceAutomorphism P e he hp where
  equiv := (A.trans k.equiv).trans A.symm
  map_product x y := A.injective (by
    simp [LinearEquiv.trans_apply, A.apply_symm_apply, sourceProduct_map hA, k.map_jordan])
  map_trace x := by
    simp [sourceTrace_eq hA, LinearEquiv.trans_apply, A.apply_symm_apply, k.map_trace]

theorem sourceOrbit_iff_native (T S : SourceTriple E) :
    S ∈ sourceAutOrbit P e he hp T ↔
      mapTriple A S ∈ Glennie.Compact.FlatOrbit.autOrbit (mapTriple A T) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨sourceAutToNative hA g, funext fun a => funext fun i => ?_⟩
    simp only [mapAtoms_apply, mapTriple, sourceAutToNative, LinearEquiv.trans_apply,
      A.symm_apply_apply]
    exact congrArg A (congrFun (congrFun hg a) i)
  · rintro ⟨k, hk⟩
    refine ⟨nativeAutToSource hA k, funext fun a => funext fun i => A.injective ?_⟩
    simp [sourceMapAtoms, nativeAutToSource, LinearEquiv.trans_apply, A.apply_symm_apply]
    exact congrFun (congrFun hk a) i

theorem sourceFibre54_iff_native (b : Fin 20 → ℝ) (T : SourceTriple E) :
    T ∈ sourceFibre54 P e he hp b ↔ mapTriple A T ∈ Glennie.Compact.NearbyOrbits.fibre54 b := by
  simp [sourceFibre54, Glennie.Compact.NearbyOrbits.fibre54, 
    sourceTriple_frames_iff hA, sourceLedger54_eq hA]

theorem sourceFibre20_iff_native (b : Fin 20 → ℝ) (T : SourceTriple E) :
    T ∈ sourceFibre20 P e he hp b ↔ mapTriple A T ∈ Glennie.Compact.NearbyOrbits.fibre20 b := by
  simp [sourceFibre20, Glennie.Compact.NearbyOrbits.fibre20, 
    sourceTriple_frames_iff hA, sourceLedger54_eq hA]

/-- The chart, two-section classification, and score test hold on one open domain. -/
theorem common_local_reconstruction_of_equiv :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧
      encode20 (sourceLedger54 P e he hp (pullTriple A Glennie.Compact.Sections.flatBase)) ∈ V ∧
      TwoOrbitSections P e he hp V ∧ ScoreComplete P e he hp V := by
  obtain ⟨V1, hV1, hbase1, pos, neg, hcP, hcN, hfP, hfN,
      _heP, _heN, hlP, hlN, hpP, hpN, hcover, hdisj, h20⟩ :=
    Glennie.Compact.NearbyOrbitsClosed.nearby_fibres_two_orbits_unconditional
  obtain ⟨V2, hV2, hbase2, hclass⟩ :=
    Glennie.Compact.LocalReconstruction.nearby_q26_score_complete
  have hmp b : mapTriple A (pullTriple A b) = b := mapTriple_pullTriple A b
  have hcont := continuous_pi fun a => continuous_pi fun i =>
      A.symm.toLinearMap.continuous_of_finiteDimensional.comp
        (Glennie.Compact.FrameTopology.continuous_entry a i)
  have horb b T : T ∈ sourceAutOrbit P e he hp (pullTriple A b) ↔
      mapTriple A T ∈ Glennie.Compact.FlatOrbit.autOrbit b := by
    rw [sourceOrbit_iff_native hA, hmp]
  refine ⟨V1 ∩ V2, hV1.inter hV2, by rw [sourceLedger54_eq hA, hmp]; exact ⟨hbase1, hbase2⟩,
    ⟨fun b => pullTriple A (pos b), fun b => pullTriple A (neg b),
      (hcont.comp_continuousOn hcP).mono fun b hb => hb.1,
      (hcont.comp_continuousOn hcN).mono fun b hb => hb.1,
      fun b hb => (sourceTriple_frames_iff hA _).mpr (by rw [hmp]; exact hfP b hb.1),
      fun b hb => (sourceTriple_frames_iff hA _).mpr (by rw [hmp]; exact hfN b hb.1),
      fun b hb => by rw [sourceLedger54_eq hA, hmp]; exact hlP b hb.1,
      fun b hb => by rw [sourceLedger54_eq hA, hmp]; exact hlN b hb.1,
      fun b hb => ?_, fun b hb => ?_, fun b hb => Set.ext fun T => ?_,
      fun b hb => Set.disjoint_left.mpr fun T hN hP => Set.disjoint_left.mp (hdisj b hb.1)
        ((horb _ T).mp hN) ((horb _ T).mp hP),
      fun b hb => Set.ext fun T => by
        rw [sourceFibre20_iff_native hA, sourceFibre54_iff_native hA, h20 b hb.1]⟩,
    fun T S hT hS hb => ?_⟩
  · rw [sourceScore_eq hA, hmp, Glennie.Compact.LocalContrast.score_eq_two_phi]
    linarith [hpP b hb.1]
  · rw [sourceScore_eq hA, hmp, Glennie.Compact.LocalContrast.score_eq_two_phi]
    linarith [hpN b hb.1]
  · rw [Set.mem_union, sourceFibre54_iff_native hA, horb, horb, hcover b hb.1]
    rfl
  · rw [sourceLedger54_eq hA] at hb
    obtain ⟨hnz, hiff⟩ := hclass _ _ ((sourceTriple_frames_iff hA T).mp hT)
      ((sourceTriple_frames_iff hA S).mp hS) hb.2
    rw [sourceScore_eq hA, sourceOrbit_iff_native hA, sourceQ26_eq hA, sourceQ26_eq hA,
      SameSourceScoreSign, sourceScore_eq hA, sourceScore_eq hA]
    exact ⟨hnz, hiff⟩

end
end AlbertGeometry.IntrinsicLocalTransport
