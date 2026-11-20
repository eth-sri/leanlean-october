module
public import Solution.FiniteObservations

/-! Transport the finite observations once, along any based algebra and trace
isomorphism. No cubic or curvature hypotheses enter the orbit argument. -/
@[expose] public section
namespace Glennie.SubmissionR04Intrinsic.Local
noncomputable section
open Glennie SubmissionR03

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure ChartIso (e : E) (t : E → ℝ) (j : E → E → E) where
  A : E ≃ₗ[ℝ] Albert
  unit : A e = 1
  tr : ∀ x, t x = trace (A x)
  prod : ∀ x y, A (j x y) = jordan (A x) (A y)

namespace ChartIso
variable {e : E} {t : E → ℝ} {j : E → E → E} (I : ChartIso e t j)
abbrev push (T : Triple E) : Triple Albert := fun a i => I.A (T a i)
abbrev pull (T : Triple Albert) : Triple E := fun a i => I.A.symm (T a i)
@[simp] theorem push_pull (T : Triple Albert) : I.push (I.pull T) = T := by funext a i; simp [push, pull]

theorem frame (p : Fin 3 → E) : Frame e t j p ↔ Glennie.Frame (fun i => I.A (p i)) := by
  constructor <;> rintro ⟨a,b,c,d⟩
  · exact ⟨fun i => (I.tr _).symm.trans (a i), fun i => (I.prod ..).symm.trans (congrArg I.A (b i)),
      fun i k h => by rw [← I.prod, c i k h, map_zero], by rw [← map_add, ← map_add, d, I.unit]⟩
  · exact ⟨fun i => (I.tr _).trans (a i), fun i => I.A.injective ((I.prod ..).trans (b i)),
      fun i k h => I.A.injective (by rw [I.prod, c i k h, map_zero]),
      I.A.injective (by simpa only [map_add, I.unit] using d)⟩

theorem frames (T : Triple E) : (∀ a, Frame e t j (T a)) ↔ ∀ a, Glennie.Frame (I.push T a) :=
  forall_congr' fun a => I.frame (T a)

theorem ledger_map (T : Triple E) : ledger t j T = fullLedger (I.push T) := by
  change ledger t j T = ledger trace jordan (I.push T)
  simp only [ledger, pairing, I.tr, I.prod, push]

private theorem quad_map (x y : E) : I.A (quad j x y) = U (I.A x) (I.A y) := by
  simp [quad, U, I.prod]

theorem phi_map (x y z : E) : phi t j x y z = Glennie.phi (I.A x) (I.A y) (I.A z) := by
  simp only [phi, Glennie.phi, pairing, inner, I.tr, I.prod, map_sub, I.quad_map]

theorem score_map (T : Triple E) : score e t j T = SubmissionR03.score (I.push T) := by
  simp only [score,SubmissionR03.score,delta,half,contrast,pairing,encoder,push,
    I.tr,I.unit,I.prod,map_add,map_sub,map_smul,I.quad_map,SubmissionR03.delta,
    SubmissionR03.contrast,SubmissionR03.halfAmplitude,Glennie.encoder,inner,
    f0_eq,f1_eq,f2_eq,Nat.cast_ofNat]

theorem q_map (T : Triple E) : q26 t j T = SubmissionR03.q26 (I.push T) := by
  change _ = q26 trace jordan (I.push T)
  simp only [q26, qSingle, qPair, qTriple, power, pairing, encoder, push, I.tr, I.prod,
    map_sub, apply_ite I.A]

private theorem symm_prod (x y : Albert) : I.A.symm (jordan x y) = j (I.A.symm x) (I.A.symm y) :=
  I.A.injective (by simp [I.prod])

def toAut (g : Automorphism t j) : CompactAutomorphism where
  equiv := (I.A.symm.trans g.equiv).trans I.A
  map_jordan x y := by simp [I.symm_prod, g.map_product, I.prod]
  map_trace x := by simp only [LinearEquiv.trans_apply, ← I.tr, g.map_trace]; simp [I.tr]

def fromAut (g : CompactAutomorphism) : Automorphism t j where
  equiv := (I.A.trans g.equiv).trans I.A.symm
  map_product x y := by simp [I.prod, g.map_jordan, I.symm_prod]
  map_trace x := by simp [I.tr, g.map_trace]

theorem orbit_map (S : Triple E) : orbit t j S = I.push ⁻¹' autOrbit (I.push S) := by
  ext T; constructor
  · rintro ⟨g,rfl⟩; refine ⟨I.toAut g, ?_⟩; funext a i; simp [toAut, push, mapAtoms, SubmissionR03.mapAtoms]
  · rintro ⟨g,h⟩; refine ⟨I.fromAut g, ?_⟩; funext a i
    apply I.A.injective
    simpa [mapAtoms, fromAut, push, SubmissionR03.mapAtoms] using congrFun (congrFun h a) i

theorem fibre (b : Chart) : fibre54 e t j b = I.push ⁻¹' SubmissionR03.fibre54 b := by
  ext T; exact and_congr (I.frames T) (by rw [I.ledger_map])
theorem fibre' (b : Chart) : fibre20 e t j b = I.push ⁻¹' SubmissionR03.fibre20 b := by
  ext T; exact and_congr (I.frames T) (by rw [I.ledger_map])

abbrev Generates (T : Triple E) := ∀ K : Submodule ℝ E,
  (∀ x ∈ K, ∀ y ∈ K, j x y ∈ K) → (∀ a i, T a i ∈ K) → K = ⊤

include I in
theorem generates {T : Triple E} (h : ∀ a, Frame e t j (T a)) (hs : score e t j T ≠ 0) :
    Generates (j := j) T := by
  intro K hj ha
  apply (Submodule.map_eq_top_iff (e := I.A)).mp
  apply atoms_generate_of_score (I.push T) ((I.frames T).mp h) (I.score_map T ▸ hs)
  · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩; exact ⟨_, hj x hx y hy, I.prod x y⟩
  · exact fun a i => ⟨_, ha a i, rfl⟩

theorem stabilizer {T : Triple E} (H : Generates (j := j) T) (g : Automorphism t j)
    (h : mapAtoms g T = T) : g.equiv = LinearEquiv.refl ℝ E := by
  apply LinearEquiv.toLinearMap_injective; apply LinearMap.eqLocus_eq_top.mp
  apply H
  · intro x hx y hy; change g.equiv (j x y) = j x y
    rw [g.map_product, show g.equiv x = x from hx, show g.equiv y = y from hy]
  · exact fun a i => congrFun (congrFun h a) i

include I in
theorem derivation {T : Triple E} (H : Generates (j := j) T) (D : E →ₗ[ℝ] E)
    (hD : ∀ x y, D (j x y) = j (D x) y + j x (D y)) (hk : ∀ a i, D (T a i) = 0) : D = 0 := by
  apply LinearMap.ker_eq_top.mp; apply H _ _ hk
  intro x hx y hy; change D (j x y) = 0; rw [hD, show D x = 0 from hx, show D y = 0 from hy]
  apply I.A.injective; simp [I.prod]

/-- Pull the native sections and orbit test back along the same chart isomorphism. -/
theorem result {N : E → ℝ} {a B : E → E → ℝ} {Gamma : E → E → E}
    {R : E → E → E → E} {nativeN : Albert → ℝ}
    (hn : ∀ x, nativeN (I.A x) = N x) (hm : ∀ x y, a x y = inner (I.A x) (I.A y) / 3)
    (hb : ∀ x y, B x y = inner (I.A x) (I.A y))
    (hg : ∀ x y, I.A (Gamma x y) = -jordan (I.A x) (I.A y))
    (hr : ∀ x y z, I.A (R x y z) = -(jordan (I.A x) (jordan (I.A y) (I.A z)) -
      jordan (I.A y) (jordan (I.A x) (I.A z)))) :
    Nonempty (Result e N t a B j Gamma R nativeN) := by
  let d := Compact.LocalOrbitQuotientR01.localData
  let V := d.V
  have complete : ScoreComplete e t j V := by
    intro T S hT hS h
    simpa only [SameSign, I.score_map, I.q_map, I.orbit_map, Set.mem_preimage, Compact.LocalReconstruction.SameScoreSign, autOrbit, Set.mem_setOf_eq] using
      Compact.LocalReconstruction.complete d (I.push T) (I.push S) ((I.frames _).mp hT) ((I.frames _).mp hS) (I.ledger_map T ▸ h)
  have gen (T : Triple E) (h : Admitted e t j V T) : Generates (j := j) T :=
    I.generates h.1 (complete T T h.1 h.1 h.2).1
  refine ⟨⟨I.A, I.unit, hn, hm, hb, I.tr, I.prod, hg, hr, V, d.openV,
    ?_, ?_, complete, ?_, ?_, gen, fun T h => stabilizer (gen T h),
    fun T h => I.derivation (gen T h)⟩⟩
  · change encode20 (ledger t j (I.pull flatBase)) ∈ V
    rw [I.ledger_map, I.push_pull]; exact d.base
  · have hc : Continuous I.pull := continuous_pi fun a => continuous_pi fun i =>
      I.A.symm.toLinearMap.continuous_of_finiteDimensional.comp ((continuous_apply i).comp (continuous_apply a))
    refine ⟨I.pull ∘ d.pos,I.pull ∘ d.neg, hc.comp_continuousOn d.contPos,
      hc.comp_continuousOn d.contNeg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intro b h
    · exact (I.frames _).mpr (by simpa only [Function.comp_apply, push_pull] using d.framePos b h)
    · exact (I.frames _).mpr (by simpa only [Function.comp_apply, push_pull] using d.frameNeg b h)
    · simpa only [Function.comp_apply, I.ledger_map, push_pull] using d.posL b h
    · simpa only [Function.comp_apply, I.ledger_map, push_pull] using d.negL b h
    · simp only [Function.comp_apply, I.score_map, push_pull, score_eq_two_phi]; exact mul_pos (by norm_num) (d.phiPos b h)
    · simp only [Function.comp_apply, I.score_map, push_pull, score_eq_two_phi]; exact mul_neg_of_pos_of_neg (by norm_num) (d.phiNeg b h)
    · simp only [I.fibre, I.orbit_map, Function.comp_apply, push_pull, ← Set.preimage_union]
      exact congrArg (Set.preimage I.push) (d.cover b h)
    · simpa only [I.orbit_map, Function.comp_apply, push_pull] using (d.disjoint b h).preimage I.push
    · rw [I.fibre', I.fibre]; exact congrArg (Set.preimage I.push) (Compact.NearbyOrbits.fibre_eq b)
  · intro T S hT hS; rw [I.q_map, I.q_map, I.ledger_map, I.ledger_map]
    exact q26_eq_iff_fullLedger_eq _ _ ((I.frames _).mp hT) ((I.frames _).mp hS)
  · intro T; rw [I.score_map, score_eq_two_phi, I.phi_map]; simp [phiOf, push, encoder, Glennie.encoder]

end ChartIso
end
end Glennie.SubmissionR04Intrinsic.Local
