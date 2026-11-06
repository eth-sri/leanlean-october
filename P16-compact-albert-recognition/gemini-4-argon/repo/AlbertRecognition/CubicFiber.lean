module

public import AlbertRecognition.FixedFrame.FixedFrameGate
public import Glennie.Native.Triality
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section
namespace AlbertRecognition.Transporter
noncomputable section
open Glennie
open scoped BigOperators

def halfRoot : ℝ := Real.sqrt (1 / 2)

theorem halfRoot_sq : halfRoot ^ 2 = (1 / 2 : ℝ) :=
  Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)

theorem rotation_condition : halfRoot ^ 2 + (-halfRoot) ^ 2 = 1 := by
  nlinarith [halfRoot_sq]

def p12Plus (a : Octonion) : Albert :=
  (1 / 2 : ℝ) • (e 1 + e 2 + (X12 a : Albert))

theorem p12Plus_coordinates (a : Octonion) :
    p12Plus a = ⟨0, 1 / 2, 1 / 2, 0, 0, (1 / 2 : ℝ) • a⟩ := by
  apply Albert.ext <;> norm_num [p12Plus, e, X12]

theorem swap_image : realSwap01Automorphism.equiv (e 0) = e 1 := by
  change realConjugateAlbert realSwap01 (e 0) = e 1
  rw [realSwap01_coordinates]; apply Albert.ext <;> simp [e, octConj]

theorem rotation_e1_coordinates (c s : ℝ) :
    realConjugateAlbert (realRotation12 c s) (e 1) =
      ⟨0, c*c, s*s, 0, 0, octScalar (-(c*s))⟩ := by
  ext <;>
    simp [realConjugateAlbert, fromMatrix, matrixConjugateReal,
      matrixRowMix, matrixColMix, realRotation12, toMatrix,
      Fin.sum_univ_three, e, octRe, octScalar, octConj, smul_eq_mul] <;> ring

def realHalfRotation : CompactAutomorphism :=
  realRotation12Automorphism halfRoot (-halfRoot) rotation_condition

theorem rotation_image :
    realHalfRotation.equiv (e 1) = p12Plus (octScalar 1) := by
  change realConjugateAlbert (realRotation12 halfRoot (-halfRoot)) (e 1) = _
  rw [rotation_e1_coordinates, p12Plus_coordinates]
  have hr : halfRoot * halfRoot = (1 / 2 : ℝ) := by nlinarith [halfRoot_sq]
  apply Albert.ext <;> simp [hr, octScalar_smul]

theorem middle_image (a : Octonion) (ha : octNormSq a = 1) :
    (octMiddleTriple a ha).compactAutomorphism.equiv (p12Plus (octScalar 1)) =
      p12Plus a := by
  rw [p12Plus_coordinates, p12Plus_coordinates]
  change (octMiddleTriple a ha).albertEquiv _ = _
  apply Albert.ext <;>
    simp [OctRelatedTriple.albertEquiv, OctRelatedTriple.middle_B,
      octMul_smul_left, octMul_scalar_left] <;> simp [octMul]

end
end AlbertRecognition.Transporter

namespace AlbertRecognition.ReferenceTransport
noncomputable section
open Glennie AlbertRecognition.FixedFrame
open scoped Quaternion

abbrev FamilyIndex := Fin 3 ⊕ (Fin 3 × Fin 8 × Bool)

def signedBasis (t : Fin 8) (plus : Bool) : Octonion :=
  if plus then octBasis t else -octBasis t

theorem octBasis_norm (t : Fin 8) : octNormSq (octBasis t) = 1 := by
  fin_cases t <;> norm_num [octBasis, octNormSq, Quaternion.normSq_def', octScalar, qi, qj, qk]

theorem signedBasis_norm (t : Fin 8) (plus : Bool) :
    octNormSq (signedBasis t plus) = 1 := by
  cases plus
  · change octNormSq (-octBasis t) = 1
    have hn : octNormSq (-octBasis t) = octNormSq (octBasis t) := by
      simp [octNormSq, Quaternion.normSq_def']
    rw [hn, octBasis_norm]
  · exact octBasis_norm t

def slotVector : Fin 3 → (Octonion →ₗ[ℝ] V) := ![X01, X02, X12]

def slotIdempotent (slot : Fin 3) (a : Octonion) : Albert :=
  ![⟨1/2,1/2,0,(1/2 : ℝ) • a,0,0⟩,
    ⟨1/2,0,1/2,0,(1/2 : ℝ) • a,0⟩,
    ⟨0,1/2,1/2,0,0,(1/2 : ℝ) • a⟩] slot

def transport12 (a : Octonion) (ha : octNormSq a = 1) : CompactAutomorphism :=
  (octMiddleTriple a ha).compactAutomorphism.comp
    (Transporter.realHalfRotation.comp realSwap01Automorphism)

def slotTransporter (slot : Fin 3) (a : Octonion)
    (ha : octNormSq a = 1) : CompactAutomorphism :=
  ![realSwap01Automorphism.comp (realSwap02Automorphism.comp (transport12 a ha)),
    realSwap01Automorphism.comp (transport12 a ha), transport12 a ha] slot

def transporter : FamilyIndex → CompactAutomorphism
  | Sum.inl i => ![CompactAutomorphism.refl, realSwap01Automorphism, realSwap02Automorphism] i
  | Sum.inr (slot,t,plus) => slotTransporter slot (signedBasis t plus) (signedBasis_norm t plus)

def familyIdempotent : FamilyIndex → Albert
  | Sum.inl i => e i
  | Sum.inr (slot,t,plus) => slotIdempotent slot (signedBasis t plus)

def direction (i : FamilyIndex) : V := automorphismV (transporter i) (h 0)

theorem transport12_image (a : Octonion) (ha : octNormSq a = 1) :
    (transport12 a ha).equiv (e 0) = Transporter.p12Plus a := by
  simp only [transport12, CompactAutomorphism.comp_apply]
  rw [Transporter.swap_image, Transporter.rotation_image, Transporter.middle_image]

theorem slotTransporter_image (slot : Fin 3) (a : Octonion)
    (ha : octNormSq a = 1) :
    (slotTransporter slot a ha).equiv (e 0) = slotIdempotent slot a := by
  fin_cases slot
  · change realSwap01Automorphism.equiv
      (realSwap02Automorphism.equiv ((transport12 a ha).equiv (e 0))) = _
    rw [transport12_image, Transporter.p12Plus_coordinates]
    change realConjugateAlbert realSwap01 (realConjugateAlbert realSwap02 _) = _
    rw [realSwap02_coordinates, realSwap01_coordinates]
    apply Albert.ext <;> simp [slotIdempotent, octConj_smul, octConj_conj, octConj]
    all_goals apply Prod.ext <;> rfl
  · change realSwap01Automorphism.equiv ((transport12 a ha).equiv (e 0)) = _
    rw [transport12_image, Transporter.p12Plus_coordinates]
    change realConjugateAlbert realSwap01 _ = _
    rw [realSwap01_coordinates]
    apply Albert.ext <;> simp [slotIdempotent, octConj]
  · exact (transport12_image a ha).trans (Transporter.p12Plus_coordinates a)

theorem transporter_image (i : FamilyIndex) :
    (transporter i).equiv (e 0) = familyIdempotent i := by
  cases i with
  | inl i =>
    fin_cases i
    · rfl
    · exact Transporter.swap_image
    · change realConjugateAlbert realSwap02 (e 0) = e 2
      rw [realSwap02_coordinates]; apply Albert.ext <;> simp [e, octConj]
  | inr i =>
    rcases i with ⟨slot,t,plus⟩
    exact slotTransporter_image slot (signedBasis t plus) (signedBasis_norm t plus)

theorem direction_coe (i : FamilyIndex) :
    (direction i : Albert) = (1 : Albert) - (3 : ℝ) • familyIdempotent i := by
  change (transporter i).equiv (h 0 : Albert) = _
  rw [h_coe, map_sub, map_smul, (transporter i).map_unit, transporter_image]

theorem direction_diagonal (i : Fin 3) : direction (Sum.inl i) = h i :=
  Subtype.ext (direction_coe (Sum.inl i))

theorem direction_difference (slot : Fin 3) (t : Fin 8) :
    direction (Sum.inr (slot,t,true)) - direction (Sum.inr (slot,t,false)) =
      (-3 : ℝ) • slotVector slot (octBasis t) := by
  have hp (a : Octonion) :
      slotIdempotent slot a - slotIdempotent slot (-a) = (slotVector slot a : Albert) := by
    fin_cases slot <;> (dsimp [slotIdempotent, slotVector, X01, X02, X12]; apply Albert.ext <;> simp [smul_neg] <;> module)
  apply Subtype.ext
  change (direction (Sum.inr (slot,t,true)) : Albert) -
      (direction (Sum.inr (slot,t,false)) : Albert) = _
  rw [direction_coe, direction_coe]
  change ((1 : Albert) - (3 : ℝ) • slotIdempotent slot (octBasis t)) -
      ((1 : Albert) - (3 : ℝ) • slotIdempotent slot (-octBasis t)) =
    (-3 : ℝ) • (slotVector slot (octBasis t) : Albert)
  rw [← hp (octBasis t)]; module

def familySpan : Submodule ℝ V := Submodule.span ℝ (Set.range direction)

theorem direction_mem_familySpan (i : FamilyIndex) : direction i ∈ familySpan :=
  Submodule.subset_span ⟨i,rfl⟩

theorem slot_basis_mem_familySpan (slot : Fin 3) (t : Fin 8) :
    slotVector slot (octBasis t) ∈ familySpan := by
  have hd := familySpan.sub_mem
    (direction_mem_familySpan (Sum.inr (slot,t,true)))
    (direction_mem_familySpan (Sum.inr (slot,t,false)))
  simpa only [direction_difference, smul_smul, show (-1/3 : ℝ) * (-3) = 1 by norm_num, one_smul] using
    familySpan.smul_mem (-1/3 : ℝ) hd

theorem slot_mem_familySpan (slot : Fin 3) (a : Octonion) :
    slotVector slot a ∈ familySpan := by
  rw [oct_decompose a]; simp only [map_add, map_smul]
  repeat' apply familySpan.add_mem
  all_goals exact familySpan.smul_mem _ (slot_basis_mem_familySpan slot _)

theorem h_mem_familySpan (i : Fin 3) : h i ∈ familySpan := by
  rw [← direction_diagonal]; exact direction_mem_familySpan (Sum.inl i)

theorem frameD_mem_familySpan : frameD ∈ familySpan := by
  rw [frameD_eq_h01]
  exact familySpan.add_mem (familySpan.smul_mem _ (h_mem_familySpan 0))
    (familySpan.smul_mem _ (h_mem_familySpan 1))

theorem frameSpin_mem_familySpan (s : Spin) : frameSpin s ∈ familySpan := by
  rcases s with ⟨u,v⟩; rw [frameSpin_apply]
  exact familySpan.add_mem (slot_mem_familySpan 0 u) (slot_mem_familySpan 1 v)

theorem span_directions : Submodule.span ℝ (Set.range direction) = ⊤ := by
  apply top_unique; intro x _
  rw [frame_decompose x]
  exact familySpan.add_mem (familySpan.add_mem (familySpan.add_mem
    (familySpan.smul_mem _ (h_mem_familySpan 0)) (familySpan.smul_mem _ frameD_mem_familySpan))
    (slot_mem_familySpan 2 _)) (frameSpin_mem_familySpan _)

theorem linear_ext_on_directions {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f g : V →ₗ[ℝ] W) (hfg : ∀ i : FamilyIndex, f (direction i) = g (direction i)) :
    f = g := by
  apply (Submodule.linearMap_eq_iff_of_span_eq_top f g span_directions).mpr
  rintro ⟨_,⟨i,rfl⟩⟩; exact hfg i

end
end AlbertRecognition.ReferenceTransport

namespace AlbertRecognition
noncomputable section

theorem symmetricCubic_eq_of_form_eq {B C : SymmetricCubic}
    (hform : B.form = C.form) : B = C := by
  cases B; cases C; cases hform; rfl

def scalarCubic (r : ℝ) (B : SymmetricCubic) : SymmetricCubic where
  form := r • B.form
  swap12 x y z := congrArg (fun a : ℝ => r * a) (B.swap12 x y z)
  swap23 x y z := congrArg (fun a : ℝ => r * a) (B.swap23 x y z)

@[simp] theorem scalarCubic_form (r : ℝ) (B : SymmetricCubic) (x y z : V) :
    (scalarCubic r B).form x y z = r * B.form x y z := rfl

theorem scalarCubic_one (B : SymmetricCubic) : scalarCubic 1 B = B :=
  symmetricCubic_eq_of_form_eq (one_smul ℝ B.form)

theorem KB_scalarCubic (r : ℝ) (B : SymmetricCubic) :
    KB (scalarCubic r B) = r • KB B := by
  apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
  apply metricDual.injective; apply LinearMap.ext; intro z
  change gA (KB (scalarCubic r B) x y) z = gA (r • KB B x y) z
  rw [KB_pairing, scalarCubic_form, gA_smul_left, KB_pairing]

theorem operatorComm_jacobi (P Q R : Module.End ℝ V) :
    operatorComm P (operatorComm Q R) + operatorComm Q (operatorComm R P) +
      operatorComm R (operatorComm P Q) = 0 := by
  apply LinearMap.ext; intro v
  simp only [operatorComm, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, map_sub, LinearMap.zero_apply]; abel

section SelfJacobi
attribute [local irreducible] KB

theorem A_q_self (B : SymmetricCubic) : A (q B) B = 0 := by
  set_option backward.isDefEq.respectTransparency true in
    with_reducible
      funext x y z
      simpa only [A, q, Pi.zero_apply] using operatorComm_jacobi (KB B x) (KB B y) (KB B z)

end SelfJacobi

theorem q_scalarCubic (r : ℝ) (B : SymmetricCubic) :
    q (scalarCubic r B) = r^2 • q B := by
  funext x y; apply LinearMap.ext; intro z
  change operatorComm (KB (scalarCubic r B) x) (KB (scalarCubic r B) y) z =
    r^2 • operatorComm (KB B x) (KB B y) z
  rw [KB_scalarCubic]
  change (r • KB B x) ((r • KB B y) z) - (r • KB B y) ((r • KB B x) z) =
    r^2 • ((KB B x) ((KB B y) z) - (KB B y) ((KB B x) z))
  simp only [LinearMap.smul_apply, map_smul, smul_smul, pow_two]; module

namespace FixedFrame
open Glennie

theorem KA_h0_inverse_polynomial (x : V) :
    (2 : ℝ) • KA (h 0) (KA (h 0) (KA (h 0) x)) +
      KA (h 0) (KA (h 0) x) - (2 : ℝ) • KA (h 0) x = x := by
  rcases hs : (frameCoordinates x).2.2.2 with ⟨u,v⟩
  rw [frame_decompose x, hs, frameSpin_apply]
  simp only [map_add, map_smul, KA_h_self, KA_h0_frameD, KA_h0_X01, KA_h0_X02, KA_h0_X12]
  module

theorem KA_h0_injective : Function.Injective (KA (h 0)) := by
  intro x y hxy
  have hz : KA (h 0) (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  have hinv := KA_h0_inverse_polynomial (x-y)
  simp only [hz, map_zero, smul_zero, add_zero, sub_zero] at hinv
  exact sub_eq_zero.mp hinv.symm

theorem h0_ne_zero : h 0 ≠ 0 := by
  intro hz
  have hd := congrArg (fun x : V => (x : Albert).d0) hz
  norm_num [h, e, unit] at hd

theorem transported_frame_constraint (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) (g : CompactAutomorphism) :
    ∃ c : ℝ, KB B (automorphismV g (h 0)) = c • KA (automorphismV g (h 0)) := by
  obtain ⟨c,hc⟩ := fixedFrame_gate_of_A_q_zero
    (pullbackCubic (automorphismV g) B) (A_q_pullback_zero g B hB)
  refine ⟨c, LinearMap.ext fun z => ?_⟩
  obtain ⟨w,rfl⟩ := (automorphismV g).surjective z
  calc KB B (automorphismV g (h 0)) (automorphismV g w)
    _ = automorphismV g (KB (pullbackCubic (automorphismV g) B) (h 0) w) :=
      (automorphismV_KB_pullback g B (h 0) w).symm
    _ = automorphismV g (c • KA (h 0) w) := congrArg (automorphismV g) (LinearMap.congr_fun hc w)
    _ = c • KA (automorphismV g (h 0)) (automorphismV g w) := by rw [map_smul, automorphismV_KA]

theorem transported_scalar_eq (B : SymmetricCubic) (g : CompactAutomorphism)
    (b c : ℝ) (hb : KB B (h 0) = b • KA (h 0))
    (hc : KB B (automorphismV g (h 0)) = c • KA (automorphismV g (h 0))) :
    b = c := by
  have hu : automorphismV g (h 0) ≠ 0 := fun hz =>
    h0_ne_zero ((automorphismV g).injective (by simpa only [map_zero] using hz))
  have hv : KA (h 0) (automorphismV g (h 0)) ≠ 0 := fun hz =>
    hu (KA_h0_injective (by simpa only [map_zero] using hz))
  have heq : b • KA (h 0) (automorphismV g (h 0)) =
      c • KA (h 0) (automorphismV g (h 0)) := by
    calc b • KA (h 0) (automorphismV g (h 0))
      _ = KB B (h 0) (automorphismV g (h 0)) := (LinearMap.congr_fun hb _).symm
      _ = KB B (automorphismV g (h 0)) (h 0) := KB_comm B _ _
      _ = c • KA (automorphismV g (h 0)) (h 0) := LinearMap.congr_fun hc _
      _ = _ := congrArg (fun x : V => c • x) (KA_comm _ _)
  exact smul_left_injective ℝ hv heq

theorem common_scalar_on_reference_frames (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ b : ℝ, ∀ g : CompactAutomorphism,
      KB B (automorphismV g (h 0)) = b • KA (automorphismV g (h 0)) := by
  obtain ⟨b,hb⟩ := fixedFrame_gate_of_A_q_zero B hB
  refine ⟨b, fun g => ?_⟩
  obtain ⟨c,hc⟩ := transported_frame_constraint B hB g
  exact transported_scalar_eq B g b c hb hc ▸ hc

theorem KB_eq_scalar_reference_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) : ∃ b : ℝ, KB B = b • KA := by
  obtain ⟨b,hb⟩ := common_scalar_on_reference_frames B hB
  refine ⟨b, ReferenceTransport.linear_ext_on_directions (KB B) (b • KA) fun i => ?_⟩
  exact hb (ReferenceTransport.transporter i)

theorem cubic_eq_scalar_reference_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ b : ℝ, B = scalarCubic b referenceCubic := by
  obtain ⟨b,hb⟩ := KB_eq_scalar_reference_of_A_q_zero B hB
  exact ⟨b, KB_injective (by rw [KB_scalarCubic, KB_referenceCubic]; exact hb)⟩

end FixedFrame

open FixedFrame Glennie

theorem q_reference_h0_h1_h0 :
    q referenceCubic (h 0) (h 1) (h 0) = h 0 + (2 : ℝ) • h 1 := by
  simp only [q, KB_referenceCubic, operatorComm_apply,
    KA_h_cross 1 0 (by decide), KA_h_cross 0 1 (by decide),
    KA_h_self, map_add, map_smul]; module

theorem q_reference_ne_zero : q referenceCubic ≠ 0 := by
  intro hz
  have hv := congrArg (fun T : V → V → Module.End ℝ V => T (h 0) (h 1) (h 0)) hz
  rw [q_reference_h0_h1_h0] at hv
  change h 0 + (2 : ℝ) • h 1 = 0 at hv
  have hd := congrArg (fun x : V => (x : Albert).d1) hv
  norm_num [h, e, unit] at hd

theorem q_fiber_reference (B : SymmetricCubic) :
    q B = q referenceCubic ↔
      B = referenceCubic ∨ B = scalarCubic (-1) referenceCubic := by
  constructor
  · intro hq
    have hB : A (q referenceCubic) B = 0 := by rw [← hq]; exact A_q_self B
    obtain ⟨b,hb⟩ := cubic_eq_scalar_reference_of_A_q_zero B hB
    have hs : b^2 • q referenceCubic = (1 : ℝ) • q referenceCubic := by
      rw [one_smul, ← q_scalarCubic, ← hb]; exact hq
    rcases sq_eq_one_iff.mp (smul_left_injective ℝ q_reference_ne_zero hs) with hb1 | hbm1
    · left; rw [hb1, scalarCubic_one] at hb; exact hb
    · right; simpa only [hbm1] using hb
  · rintro (rfl | rfl)
    · rfl
    · rw [q_scalarCubic]; norm_num

end
end AlbertRecognition
