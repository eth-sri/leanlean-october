module

public import Glennie.Compact.NearbyOrbits
public import Glennie.Native.OrderedPositivePair
public import Glennie.Theorems.ComplexSectorProbes
public import Glennie.Theorems.CubicNorm
public import Glennie.UnitShifts
public import Glennie.Compact.NativeNormKernelR01
@[expose] public section
namespace Glennie.Compact.PairNormNearby

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections Glennie.Compact.NearbyOrbits
open Glennie.NativeOrderedPositivePair NativeNormKernel
open Glennie.PeirceSlots
open Glennie.SubmissionR04Intrinsic (nativeCubic)

noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

theorem nonneg_sq_eq_of_sq_eq (a a' : ℝ) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (h : a ^ 2 = a' ^ 2) : a = a' := by
  simpa only [abs_of_nonneg ha, abs_of_nonneg ha'] using (sq_eq_sq_iff_abs_eq_abs _ _).mp h

theorem frame_eq_of_encoder_eq (q s : Fin 3 → Albert) (hq : Frame q) (hs : Frame s)
    (m : CompactAutomorphism) (hEnc : m.equiv (encoder q) = encoder s) (i : Fin 3) :
    m.equiv (q i) = s i := by
  have H := compactAutomorphism_projectorFrame m (encoder q) i
  rwa [hEnc, ← congrFun (frame_as_projector q hq) i, ← congrFun (frame_as_projector s hs) i] at H

private theorem flatFrameP_diag (i : Fin 3) : flatFrameP i = e (2-i) := by
  have h : jordan flatXN flatXN = diagonalAlbert 1 0 1 := by
    change jordan (diagonalAlbert 1 0 (-1)) (diagonalAlbert 1 0 (-1)) = _
    rw [diagonal_jordan]
    apply Albert.ext <;> norm_num [diagonalAlbert]
  simp only [flatFrameP, flatBase, Matrix.cons_val_zero, projectorFrame, h]
  fin_cases i <;> apply Albert.ext <;> norm_num [flatXN, e, diag, diagonalAlbert, Pi.single_apply]

private theorem inner_flatFrameP (x : Albert) (i : Fin 3) :
    inner (flatFrameP i) x = ![x.d2, x.d1, x.d0] i := by
  rw [flatFrameP_diag]
  fin_cases i <;> norm_num [e, diag, inner_coordinates, diagonalAlbert, octDot_coordinates, Pi.single_apply]

private theorem flatFrameP_inComplexSector (i : Fin 3) : InComplexSector (flatFrameP i) := by
  rw [flatFrameP_diag]
  fin_cases i <;> simp [e, diag, InComplexSector, OctInComplex, diagonalAlbert]

private theorem diagonals_eq {x y : Albert}
    (h : ∀ i, inner (flatFrameP i) x = inner (flatFrameP i) y) :
    x.d0 = y.d0 ∧ x.d1 = y.d1 ∧ x.d2 = y.d2 := by
  simp only [inner_flatFrameP] at h
  exact ⟨h 2, h 1, h 0⟩

@[simp] private theorem complexPart_octScalar (a : ℝ) : complexPart (octScalar a) = (a : ℂ) := rfl

/-- The pair ledger fixes the normalized slots: their sizes come from the
square, and the real part of the complex slot comes from the cubic. -/
private theorem normalized_pair_eq (q q' : Fin 3 → Albert) (hq : Frame q) (hq' : Frame q')
    (h : PositiveNormal (encoder q)) (h' : PositiveNormal (encoder q'))
    (ht : triangle (encoder q) ≠ 0)
    (hP : ∀ i j, inner (flatFrameP i) (q j) = inner (flatFrameP i) (q' j)) : q = q' := by
  obtain ⟨hc, ⟨a, ha, h01⟩, ⟨b, hb, h12⟩, hI⟩ := h
  obtain ⟨hc', ⟨a', ha', h01'⟩, ⟨b', hb', h12'⟩, hI'⟩ := h'
  have ha₀ : a ≠ 0 := fun e => ht (by simp [triangle, h01, e])
  have hb₀ : b ≠ 0 := fun e => ht (by simp [triangle, h12, e])
  have ⟨h0, h1, h2⟩ := diagonals_eq (x := encoder q) (y := encoder q')
    (by simp [encoder, inner_sub_right, hP])
  have ⟨s0, s1, s2⟩ := diagonals_eq (x := jordan (encoder q) (encoder q))
    (y := jordan (encoder q') (encoder q'))
    (by simp [frame_encoder_square _ hq, frame_encoder_square _ hq', inner_add_right, hP])
  have H := frame_encoder_cubicNorm _ hq |>.trans (frame_encoder_cubicNorm _ hq').symm
  have cx := complexAlbert_eq _ hc
  have cy := complexAlbert_eq _ hc'
  simp only [h01, h12, h01', h12', complexPart_octScalar, h0, h1, h2] at cx cy
  rw [← cx, ← cy] at s0 s1 s2 H
  set u := complexPart (encoder q).o02
  set v := complexPart (encoder q').o02
  simp [jordan_d0, jordan_d1, jordan_d2, complexAlbert, complexOct,
    octNormSq, Quaternion.normSq_def'] at s0 s1 s2
  have hA : a = a' := nonneg_sq_eq_of_sq_eq _ _ ha ha' (by linarith)
  have hB : b = b' := nonneg_sq_eq_of_sq_eq _ _ hb hb' (by linarith)
  subst a' b'
  have hN : u.re^2 + u.im^2 = v.re^2 + v.im^2 := by linarith
  have hR : u.re = v.re := by
    simpa [newtonCubicNorm_coordinates, complexAlbert, complexOct, oct_coord, hN, ha₀, hb₀] using H
  have hu : u = v := Complex.ext hR (nonneg_sq_eq_of_sq_eq _ _ hI hI' (by rw [hR] at hN; linarith))
  rw [frame_as_projector q hq, frame_as_projector q' hq', ← cx, ← cy, hu]
  rfl

theorem inner_sector_complexProjection (v W : Albert) (hv : InComplexSector v) :
    inner v W = inner v (complexProjection W) := by
  nth_rw 1 [← complex_hidden_decomposition W]
  rw [inner_add_right, ← complexProjection_eq_self v hv, complex_hidden_orthogonal, add_zero]

private theorem sectorComplexMatrix_proj (x : Albert) :
    sectorComplexMatrix (complexProjection x) = sectorComplexMatrix x := by
  rw [← complexAlbert_coordinates, sectorComplexMatrix, complexCoordinates_albert]
  rfl

/-- The complex matrix of the square recovers its hidden Gram term
out of the trace-complement map, which is injective in dimension three. -/
private theorem gram_eq_of_sector_data (z z' : Albert)
    (hC : sectorComplexMatrix z = sectorComplexMatrix z')
    (hJ : sectorComplexMatrix (jordan z z) = sectorComplexMatrix (jordan z' z')) :
    sectorColumnGram (hiddenMatrix z) = sectorColumnGram (hiddenMatrix z') := by
  apply sectorComplement_injective
  simpa only [sectorComplexMatrix_jordan, sectorProductComplex_square, hC, add_right_inj,
    sectorColumnGram] using hJ

set_option maxHeartbeats 1000000 in
private theorem newtonCubicNorm_sector (z : Albert) :
    nativeCubic z = ((sectorComplexMatrix z).det -
      (sectorComplexMatrix z * sectorColumnGram (hiddenMatrix z)).trace).re + 2 * (hiddenMatrix z).det.re := by
  simp [newtonCubicNorm_coordinates, sectorComplexMatrix, complexCoordinatesLinear,
    complexHermitianMatrix, sectorColumnGram, hiddenMatrix, hiddenColumn, complexPart,
    oct_coord, Matrix.trace, Matrix.diag,
    Matrix.det_fin_three, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  ring

private theorem su3_transport (M N : SectorMatrix)
    (hG : sectorColumnGram M = sectorColumnGram N) (hM : M.det ≠ 0) (hdet : N.det = M.det) :
    ∃ s : SectorUnitary, (s : SectorMatrix).det = 1 ∧ (s : SectorMatrix) * M = N := by
  have hI := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)
  have hU : (N * M⁻¹).conjTranspose * (N * M⁻¹) = 1 := by
    rw [Matrix.conjTranspose_mul, mul_assoc, ← mul_assoc N.conjTranspose,
      ← show M.conjTranspose * M = N.conjTranspose * N from hG, mul_assoc, hI, mul_one,
      ← Matrix.conjTranspose_mul, hI, Matrix.conjTranspose_one]
  refine ⟨⟨N * M⁻¹, Matrix.mem_unitaryGroup_iff'.mpr hU⟩, ?_, ?_⟩
  · change (N * M⁻¹).det = 1
    rw [Matrix.det_mul, hdet, ← Matrix.det_mul, hI, Matrix.det_one]
  · change N * M⁻¹ * M = N
    rw [mul_assoc, mul_eq_one_comm.mp hI, mul_one]

private theorem phi_flat (q r : Fin 3 → Albert) (hc : InComplexSector (encoder q)) :
    phiOf ![flatFrameP, q, r] = (-4 : ℝ) * triangle (encoder q) * (hiddenMatrix (encoder r)).det.im := by
  change phi (encoder flatFrameP) (encoder q) (encoder r) = _
  rw [flatFrameP_encoder, phi_of_diagonal_complex _ _ _ (by exact ⟨rfl,rfl,rfl⟩) hc]
  norm_num [flatXN, triangle]

private theorem projection_eq_of_probes (q : Fin 3 → Albert) (hq : Frame q)
    (hc : InComplexSector (encoder q))
    (ht : triangle (encoder q) ≠ 0)
    {u v : Albert}
    (hR : ∀ i, inner (flatFrameP i) u = inner (flatFrameP i) v)
    (hC : ∀ i j, inner (jordan (flatFrameP i) (q j)) u = inner (jordan (flatFrameP i) (q j)) v) :
    complexProjection u = complexProjection v := by
  let E := complexProjection (u-v)
  let K := (nativeInnerLinear (u-v)).ker
  have mem {x} (h : inner x u = inner x v) : x ∈ K := by
    change inner (u-v) x = 0
    rw [inner_comm, inner_sub_right, h, sub_self]
  have ef (i : Fin 3) : e i = flatFrameP (2-i) := by rw [flatFrameP_diag]; congr 1; omega
  have h := sector_le_of_probes K _ hc ht (fun i => mem (ef i ▸ hR (2-i)))
    (fun i => mem (by simp [ef, encoder, jordan_sub_right, inner_sub_left, hC]))
    (fun i => mem (by simp [ef, frame_encoder_square _ hq, jordan_add_right, inner_add_left, hC]))
    (complexProjection_mem (u-v))
  change inner (u-v) E = 0 at h
  rw [inner_comm, inner_sector_complexProjection _ _ ((complexSector_mem_iff E).mp (complexProjection_mem _))] at h
  exact sub_eq_zero.mp (by simpa [E, ← complexAlbert_coordinates, map_sub] using (inner_self_eq_zero E).mp h)

private theorem normalized_core (q r s : Fin 3 → Albert) (hq : Frame q) (hr : Frame r) (hs : Frame s)
    (hc : InComplexSector (encoder q))
    (hL : ledger54 ![flatFrameP, q, r] = ledger54 ![flatFrameP, q, s])
    (ht : triangle (encoder q) ≠ 0) (hd : (hiddenMatrix (encoder r)).det.im ≠ 0) :
    phiOf ![flatFrameP, q, r] ^ 2 = phiOf ![flatFrameP, q, s] ^ 2 ∧
      (phiOf ![flatFrameP, q, r] = phiOf ![flatFrameP, q, s] →
        ∃ g : CompactAutomorphism, mapAtoms g ![flatFrameP, q, r] = ![flatFrameP, q, s]) := by
  have atoms (k : Fin 3) : sectorComplexLinear (r k) = sectorComplexLinear (s k) := by
    have h := projection_eq_of_probes q hq hc ht (u := r k) (v := s k)
      (fun i => by rw [inner_comm (flatFrameP i) (r k), inner_comm (flatFrameP i) (s k)];
                   exact congrArg (fun L : Ledger54 => L.2.2.2 k i) hL)
      (fun i j => congrArg (fun L : Ledger54 => L.1 i j k) hL)
    change sectorComplexMatrix (r k) = sectorComplexMatrix (s k)
    simpa only [sectorComplexMatrix_proj] using congrArg sectorComplexMatrix h
  let x := encoder r
  let y := encoder s
  have hC : sectorComplexMatrix x = sectorComplexMatrix y := by
    simp only [← sectorComplexLinear_apply, x, y, encoder, map_sub, atoms]
  have hS : sectorComplexMatrix (jordan x x) = sectorComplexMatrix (jordan y y) := by
    simp only [← sectorComplexLinear_apply, x, y, frame_encoder_square _ hr, frame_encoder_square _ hs,
      map_add, atoms]
  have hG := gram_eq_of_sector_data _ _ hC hS
  have hRe : (hiddenMatrix x).det.re = (hiddenMatrix y).det.re := by
    have h := (frame_encoder_cubicNorm _ hr).trans (frame_encoder_cubicNorm _ hs).symm
    change nativeCubic x = nativeCubic y at h
    rw [newtonCubicNorm_sector, newtonCubicNorm_sector, hC, hG] at h
    linarith
  have hNorm := congrArg (fun G : SectorMatrix => G.det.re) hG
  simp only [sectorColumnGram, Matrix.det_mul, Matrix.det_conjTranspose, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im, hRe, neg_mul, sub_neg_eq_add, add_right_inj, x, y] at hNorm
  refine ⟨?_, ?_⟩
  · simp only [phi_flat _ _ hc, mul_pow]
    simp only [pow_two, hNorm]
  · intro h
    simp only [phi_flat _ _ hc] at h
    have hdet : (hiddenMatrix x).det = (hiddenMatrix y).det :=
      Complex.ext hRe (mul_left_cancel₀ (mul_ne_zero (by norm_num) ht) h)
    have hM : (hiddenMatrix x).det ≠ 0 := fun e => hd (by simp [x, e])
    obtain ⟨m, hm, hm'⟩ := su3_transport _ _ hG hM hdet.symm
    let g := sectorLeftSU3Automorphism m hm
    have hy : g.equiv x = y := sector_ext ((sectorLeftSU3_complex m hm x).trans hC)
      ((sectorLeftSU3_hidden m hm x).trans hm')
    refine ⟨g, ?_⟩
    funext f i
    fin_cases f
    · exact sectorLeftSU3_fixes_complex m hm _ (flatFrameP_inComplexSector i)
    · exact sectorLeftSU3_fixes_complex m hm _ ((complexSector_mem_iff _).mp (frame_in_complexSector q hq hc i))
    · exact frame_eq_of_encoder_eq r s hr hs g hy i

private theorem normalize_triple (T : Triple) (hT : IsFrameTriple T) :
    ∃ (g : CompactAutomorphism) (q r : Fin 3 → Albert),
      mapAtoms g T = ![flatFrameP, q, r] ∧ Frame q ∧ Frame r ∧ PositiveNormal (encoder q) := by
  obtain ⟨g, hp, hn⟩ := native_ordered_positive_pair (T 0) (hT 0) (encoder (T 1))
  refine ⟨g, mapAtoms g T 1, mapAtoms g T 2, ?_, frame_mapAtoms g T hT 1,
    frame_mapAtoms g T hT 2, (g.encoder_map _).symm ▸ hn⟩
  funext i j
  fin_cases i
  · exact hp j
  · rfl
  · rfl

/-- On every nonzero fibre, the ledger determines the absolute invariant, and
its sign identifies the orbit. Nonzero Phi supplies the needed pair nondegeneracy. -/
theorem nearby_core (T S : Triple)
    (hT : IsFrameTriple T) (hS : IsFrameTriple S)
    (hL : ledger54 T = ledger54 S) (hTne : phiOf T ≠ 0) :
    phiOf T ^ 2 = phiOf S ^ 2 ∧
      (phiOf T = phiOf S → ∃ k : CompactAutomorphism, mapAtoms k S = T) := by
  obtain ⟨g, q, r, hg, hq, hr, h⟩ := normalize_triple T hT
  obtain ⟨g', q', s, hg', hq', hs, h'⟩ := normalize_triple S hS
  have hφT : phiOf ![flatFrameP, q, r] = phiOf T := hg ▸ phiOf_mapAtoms g T
  have hn : phiOf ![flatFrameP, q, r] ≠ 0 := hφT ▸ hTne
  rw [phi_flat q r h.complex, mul_ne_zero_iff, mul_ne_zero_iff] at hn
  have hLg : ledger54 ![flatFrameP, q, r] = ledger54 ![flatFrameP, q', s] := by
    rwa [← hg, ← hg', ledger54_map, ledger54_map]
  have he := normalized_pair_eq q q' hq hq' h h' hn.1.2
    (fun i j => congrArg (fun L : Ledger54 => L.2.1 i j) hLg)
  subst q'
  have hφS : phiOf ![flatFrameP, q, s] = phiOf S := hg' ▸ phiOf_mapAtoms g' S
  obtain ⟨hSq, hO⟩ := normalized_core q r s hq hr hs h.complex hLg hn.1.2 hn.2
  rw [hφT, hφS] at hSq hO
  refine ⟨hSq, fun h => ?_⟩
  obtain ⟨k, hk⟩ := hO h
  refine ⟨g.symm.comp (k.symm.comp g'), ?_⟩
  rw [← mapAtoms_comp, ← mapAtoms_comp, hg', ← hk, mapAtoms_symm_mapAtoms, ← hg, mapAtoms_symm_mapAtoms]


theorem orbit_of_same_sign (T S : Triple) (hT : IsFrameTriple T) (hS : IsFrameTriple S)
    (hL : ledger54 T = ledger54 S)
    (hs : (phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) :
    ∃ k : CompactAutomorphism, mapAtoms k S = T := by
  obtain ⟨hsq, horbit⟩ := nearby_core T S hT hS hL (hs.elim (fun h => h.1.ne) (fun h => h.1.ne'))
  apply horbit
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · rcases hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> linarith

end
end Glennie.Compact.PairNormNearby
