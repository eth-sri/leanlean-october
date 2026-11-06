module
public import Glennie.Compact.ObservationScript
public import Glennie.Compact.LocalReconstruction
public import Glennie.NativeGenerationEndpointR01

@[expose] public section
namespace Glennie.Compact.ObservationTransport
noncomputable section
open Glennie Glennie.SubmissionR04Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {e : E} {t : E → ℝ} {j : E → E → E}
  (A : E ≃ₗ[ℝ] Albert) (hunit : A e = 1)
  (htrace : ∀ x, t x = trace (A x))
  (hproduct : ∀ x y, A (j x y) = jordan (A x) (A y))

def mapTriple (A : E ≃ₗ[ℝ] Albert) (T : Local.Triple E) :
    Glennie.Compact.Affine20.Triple := fun a i => A (T a i)
def pullTriple (A : E ≃ₗ[ℝ] Albert)
    (T : Glennie.Compact.Affine20.Triple) : Local.Triple E :=
  fun a i => A.symm (T a i)

theorem mapTriple_pullTriple (A : E ≃ₗ[ℝ] Albert)
    (T : Glennie.Compact.Affine20.Triple) :
    mapTriple A (pullTriple A T) = T := by
  funext a i
  exact A.apply_symm_apply _

theorem encoder_map (p : Fin 3 → E) :
    A (Local.encoder p) = encoder (fun i => A (p i)) := by
  simp only [Local.encoder, encoder, map_sub]

theorem continuous_pullTriple :
    Continuous (fun T : Glennie.Compact.Affine20.Triple => pullTriple A T) := by
  have hA : Continuous (fun x : Albert => A.symm x) :=
    A.symm.toLinearMap.continuous_of_finiteDimensional
  refine continuous_pi fun a => continuous_pi fun i => ?_
  exact hA.comp (Glennie.Compact.FrameTopology.continuous_entry a i)

include A hunit htrace hproduct

theorem frame_iff  (p : Fin 3 → E) :
    Local.Frame e t j p ↔ Frame (fun i => A (p i)) := by
  constructor <;> rintro ⟨ht, hi, ho, hs⟩ <;> constructor
  all_goals
    simp only [htrace, ← A.injective.eq_iff,
      map_add, map_zero, hunit, hproduct] at *
    assumption

theorem frames_iff  (T : Local.Triple E) :
    (∀ a, Local.Frame e t j (T a)) ↔
      (∀ a, Frame (mapTriple A T a)) := forall_congr' fun _ => frame_iff A hunit htrace hproduct _

theorem phi_eq  (x y z : E) :
    Local.phi t j x y z = phi (A x) (A y) (A z) := by
  simp only [Local.phi, Local.pairing, Local.quad, phi, U,
    map_sub, map_smul, htrace, hproduct, inner]

theorem ledger_eq  (T : Local.Triple E) :
    Local.ledger t j T = Glennie.Compact.Affine20.ledger54 (mapTriple A T) := by
  simp only [Local.ledger, htrace,
    hproduct,
    Local.pairing]
  rfl

theorem q26_eq (T : Local.Triple E) :
    Local.q26 t j T = Glennie.Compact.NativeQFamilyLedger.q26 (mapTriple A T) := by
  simp [Local.q26, Local.qSingle, Local.qPair, Local.qTriple,
    Local.pairing, Local.power, Local.encoder,
    Glennie.Compact.NativeQFamilyLedger.q26, mapTriple,
    htrace, hproduct]

theorem q26_iff_ledger  (T S : Local.Triple E)
    (hT : ∀ a, Local.Frame e t j (T a))
    (hS : ∀ a, Local.Frame e t j (S a)) :
    Local.q26 t j T = Local.q26 t j S ↔
      Local.ledger t j T = Local.ledger t j S := by
  rw [q26_eq A hunit htrace hproduct,
    q26_eq A hunit htrace hproduct,
    ledger_eq A hunit htrace hproduct,
    ledger_eq A hunit htrace hproduct]
  exact Glennie.Compact.NativeQFamilyLedger.q26_eq_iff_ledger54_eq
    (mapTriple A T) (mapTriple A S)
    ((frames_iff A hunit htrace hproduct T).mp hT)
    ((frames_iff A hunit htrace hproduct S).mp hS)

theorem score_eq (T : Local.Triple E) :
    Local.score e t j T = Glennie.Compact.LocalContrast.score (mapTriple A T) := by
  simp [Local.score, Local.delta, Local.contrast, Local.pairing,
    Local.quad, Local.encoder, Local.half,
    Glennie.Compact.LocalContrast.score, Glennie.SubmissionR03.f0, Glennie.SubmissionR03.f1,
    Glennie.SubmissionR03.f2, Glennie.Compact.OperationalPhi.delta,
    Glennie.Compact.OperationalPhi.contrast, Glennie.Compact.OperationalPhi.halfAmplitude,
    U, encoder, mapTriple, Glennie.inner, map_sub, map_smul, map_add, hunit,
    htrace, hproduct]

theorem score_eq_two_phi  (T : Local.Triple E) :
    Local.score e t j T =
      2 * Local.phi t j (Local.encoder (T 0))
        (Local.encoder (T 1)) (Local.encoder (T 2)) := by
  rw [score_eq A hunit htrace hproduct,
    Glennie.Compact.LocalContrast.score_eq_two_phi,
    phi_eq A hunit htrace hproduct]
  simp only [Glennie.Compact.Sections.phiOf, encoder_map]
  rfl

def autToNative
    (g : Local.Automorphism t j) : CompactAutomorphism where
  equiv := (A.symm.trans g.equiv).trans A
  map_jordan x y := by
    obtain ⟨x, rfl⟩ := A.surjective x
    obtain ⟨y, rfl⟩ := A.surjective y
    simp only [LinearEquiv.trans_apply, ← hproduct, A.symm_apply_apply, g.map_product]
  map_trace := by
    intro x
    change trace (A (g.equiv (A.symm x))) = trace x
    simpa only [htrace, A.apply_symm_apply]
      using g.map_trace (A.symm x)

def nativeToAut
    (k : CompactAutomorphism) : Local.Automorphism t j where
  equiv := (A.trans k.equiv).trans A.symm
  map_product := by
    intro x y
    apply A.injective
    simp only [LinearEquiv.trans_apply, A.apply_symm_apply,
      hproduct, k.map_jordan]
  map_trace := by
    intro x
    simp only [htrace, LinearEquiv.trans_apply,
      A.apply_symm_apply, k.map_trace]

theorem orbit_iff  (T S : Local.Triple E) :
    S ∈ Local.orbit t j T ↔
      mapTriple A S ∈ Glennie.Compact.FlatOrbit.autOrbit (mapTriple A T) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨autToNative A htrace hproduct g, ?_⟩
    funext a i
    simp only [Glennie.Compact.Affine20.mapAtoms_apply, mapTriple,
      autToNative, LinearEquiv.trans_apply, A.symm_apply_apply]
    exact congrArg A (congrFun (congrFun hg a) i)
  · rintro ⟨k, hk⟩
    refine ⟨nativeToAut A htrace hproduct k, ?_⟩
    funext a i
    apply A.injective
    simp only [Local.mapAtoms, nativeToAut,
      LinearEquiv.trans_apply, A.apply_symm_apply]
    exact congrFun (congrFun hk a) i

theorem fibre54_iff  (b : Fin 20 → ℝ) (T : Local.Triple E) :
    T ∈ Local.fibre54 e t j b ↔
      mapTriple A T ∈ Glennie.Compact.NearbyOrbits.fibre54 b := by
  simp only [Local.fibre54, Glennie.Compact.NearbyOrbits.fibre54, Set.mem_setOf_eq,
    frames_iff A hunit htrace hproduct,
    ledger_eq A hunit htrace hproduct]

theorem fibre20_iff  (b : Fin 20 → ℝ) (T : Local.Triple E) :
    T ∈ Local.fibre20 e t j b ↔
      mapTriple A T ∈ Glennie.Compact.NearbyOrbits.fibre20 b := by
  simp only [Local.fibre20, Glennie.Compact.NearbyOrbits.fibre20, Set.mem_setOf_eq,
    frames_iff A hunit htrace hproduct,
    ledger_eq A hunit htrace hproduct]

theorem local_score_complete (d : LocalOrbitQuotientR01.LocalData) :
    Local.ScoreComplete e t j d.V := by
  intro T S
  simpa only [frames_iff A hunit htrace hproduct,
    ledger_eq A hunit htrace hproduct,
    score_eq A hunit htrace hproduct,
    orbit_iff A hunit htrace hproduct,
    q26_eq A hunit htrace hproduct,
    Local.SameSign, Glennie.Compact.LocalReconstruction.SameScoreSign,
    Glennie.Compact.FlatOrbit.autOrbit, Set.mem_setOf_eq] using
    Glennie.Compact.LocalReconstruction.nearby_q26_score_complete d (mapTriple A T) (mapTriple A S)

theorem local_two_orbits (d : LocalOrbitQuotientR01.LocalData) :
    Local.TwoOrbitSections e t j d.V := by
  refine ⟨fun b => pullTriple A (d.pos b), fun b => pullTriple A (d.neg b),
    (continuous_pullTriple A).comp_continuousOn d.contPos,
    (continuous_pullTriple A).comp_continuousOn d.contNeg,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [Set.ext_iff, Set.mem_union, Set.disjoint_left,
    frames_iff A hunit htrace hproduct,
    ledger_eq A hunit htrace hproduct,
    score_eq A hunit htrace hproduct,
    fibre54_iff A hunit htrace hproduct,
    fibre20_iff A hunit htrace hproduct,
    orbit_iff A hunit htrace hproduct,
    mapTriple_pullTriple, Glennie.Compact.LocalContrast.score_eq_two_phi]
  · exact d.framePos
  · exact d.frameNeg
  · exact d.toSignedSections.ledgerPos
  · exact d.toSignedSections.ledgerNeg
  · intro b hb
    linarith [d.phiPos b hb]
  · intro b hb
    linarith [d.phiNeg b hb]
  · intro b hb T
    exact Set.ext_iff.mp (d.cover b hb) _
  · intro b hb T
    intro hn hp
    exact Set.disjoint_left.mp (d.toSignedSections.disj b hb) hn hp
  · intro b hb T
    rw [Glennie.Compact.NearbyOrbits.fibre20_eq_fibre54]

theorem local_reconstruction  :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧
      Glennie.SubmissionR03.encode20
        (Local.ledger t j
          (pullTriple A Glennie.Compact.Sections.flatBase)) ∈ V ∧
      Local.TwoOrbitSections e t j V ∧ Local.ScoreComplete e t j V := by
  let d := LocalOrbitQuotientR01.localData
  refine ⟨d.V, d.openV, ?_, local_two_orbits A hunit htrace hproduct d,
    local_score_complete A hunit htrace hproduct d⟩
  simpa only [ledger_eq A hunit htrace hproduct, mapTriple_pullTriple] using d.base

theorem atoms_generate {V : Set Local.Chart}
    (hc : Local.ScoreComplete e t j V) (T : Local.Triple E)
    (hT : Local.Admitted e t j V T) (K : Submodule ℝ E)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, j p q ∈ K)
    (hAtoms : ∀ a i, T a i ∈ K) : K = ⊤ := by
  have hs := (hc T T hT.1 hT.1 hT.2).1
  rw [score_eq A hunit htrace hproduct,
    Glennie.Compact.LocalContrast.score_eq_two_phi] at hs
  have hu : e ∈ K := by
    rw [← (hT.1 0).sum_unit]
    exact K.add_mem (K.add_mem (hAtoms 0 0) (hAtoms 0 1)) (hAtoms 0 2)
  have hL := Glennie.NativeGenerationEndpointR01.eq_top_of_phi_ne_zero
    (K.map A.toLinearMap) ⟨e, hu, hunit⟩
    (by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      exact ⟨j p q, hJ p hp q hq, hproduct p q⟩)
    (encoder (mapTriple A T 0)) (encoder (mapTriple A T 1))
    (encoder (mapTriple A T 2))
    ⟨Local.encoder (T 0), K.sub_mem (hAtoms 0 2) (hAtoms 0 0), encoder_map A _⟩
    ⟨Local.encoder (T 1), K.sub_mem (hAtoms 1 2) (hAtoms 1 0), encoder_map A _⟩
    ⟨Local.encoder (T 2), K.sub_mem (hAtoms 2 2) (hAtoms 2 0), encoder_map A _⟩
    (right_ne_zero_of_mul hs)
  aesop

theorem atom_stabilizer {V : Set Local.Chart}
    (hc : Local.ScoreComplete e t j V) (T : Local.Triple E)
    (hT : Local.Admitted e t j V T) (g : Local.Automorphism t j)
    (hfix : Local.mapAtoms g T = T) : g.equiv = LinearEquiv.refl ℝ E := by
  let K : Submodule ℝ E :=
    { carrier := {x | g.equiv x = x}
      zero_mem' := by simp
      add_mem' := by simp_all
      smul_mem' := by simp_all }
  have hK := atoms_generate A hunit htrace hproduct hc T hT K
    (by intro p hp q hq; change g.equiv (j p q) = j p q; rw [g.map_product, hp, hq])
    (fun a i => congrFun (congrFun hfix a) i)
  apply LinearEquiv.ext
  intro x
  exact show x ∈ K from hK ▸ Submodule.mem_top

theorem atom_derivation {V : Set Local.Chart}
    (hc : Local.ScoreComplete e t j V) (T : Local.Triple E)
    (hT : Local.Admitted e t j V T) (D : E →ₗ[ℝ] E)
    (hD : ∀ p q, D (j p q) = j (D p) q + j p (D q))
    (hkill : ∀ a i, D (T a i) = 0) : D = 0 := by
  have hK := atoms_generate A hunit htrace hproduct hc T hT (LinearMap.ker D)
    (by
      intro p hp q hq
      change D (j p q) = 0
      rw [hD, LinearMap.mem_ker.mp hp, LinearMap.mem_ker.mp hq]
      apply A.injective
      simp [hproduct]) hkill
  exact LinearMap.ker_eq_top.mp hK

end
end Glennie.Compact.ObservationTransport
