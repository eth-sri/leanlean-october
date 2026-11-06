module

public import Glennie.Native.FixedPairHidden
public import Glennie.Native.SectorLeftAction

@[expose] public section
namespace Glennie.NativeFixedPairNormalization
open Glennie.Compact.FlatBase
open Glennie.NativeFixedPairHidden

theorem diagonal_third :
    Matrix.diagonal (fun _ => (1/3 : ℂ)) = (1/3 : ℂ) • (1 : SectorMatrix) := by ext <;> simp [Matrix.diagonal, Matrix.one_apply]

theorem scaled_left_inverse (M : SectorMatrix)
    (hM : M.conjTranspose * M = Matrix.diagonal (fun _ => (1/3 : ℂ))) :
    ((3 : ℂ) • M.conjTranspose) * M = 1 := by
  rw [Matrix.smul_mul, hM, diagonal_third, smul_smul]
  norm_num

/-- The only inverse used below is derived from the genuine scaled Gram identity. -/
theorem scaled_transport (M N : SectorMatrix)
    (hM : M.conjTranspose * M = Matrix.diagonal (fun _ => (1/3 : ℂ)))
    (hN : N.conjTranspose * N = Matrix.diagonal (fun _ => (1/3 : ℂ)))
    (hd : N.det = M.det) :
    ∃ s : SectorUnitary, (s : SectorMatrix).det = 1 ∧ (s : SectorMatrix) * M = N := by
  let A : SectorMatrix := (3 : ℂ) • M.conjTranspose
  let B : SectorMatrix := (3 : ℂ) • N.conjTranspose
  have hAM : A * M = 1 := scaled_left_inverse M hM
  have hMA : M * A = 1 := mul_eq_one_comm.mp hAM
  have hBN : B * N = 1 := scaled_left_inverse N hN
  have hStar : (N * A).conjTranspose = M * B := by aesop
  have hUnit : (N * A).conjTranspose * (N * A) = 1 := by grind
  let s : SectorUnitary := ⟨N * A, Matrix.mem_unitaryGroup_iff'.mpr hUnit⟩
  refine ⟨s, ?_, ?_⟩
  · change (N * A).det = 1
    rw [Matrix.det_mul, hd, ← Matrix.det_mul, hMA, Matrix.det_one]
  · grind

theorem left_maps_hidden (s : SectorUnitary) (hs : (s : SectorMatrix).det = 1)
    (x y : Albert) (hx : complexProjection x = 0) (hy : complexProjection y = 0)
    (hM : (s : SectorMatrix) * hiddenMatrix x = hiddenMatrix y) :
    (sectorLeftSU3Automorphism s hs).equiv x = y := by
  have hxr : hiddenAlbert (hiddenMatrix x) = x := by
    simpa [hx, zero_add] using complex_hidden_decomposition x
  have hyr : hiddenAlbert (hiddenMatrix y) = y := by
    simpa [hy, zero_add] using complex_hidden_decomposition y
  apply native_sector_ext
  · rw [sectorLeftSU3_complex, ← hxr, ← hyr]
    simp [sectorComplexMatrix, complexCoordinates_hiddenAlbert]
  · rw [sectorLeftSU3_hidden, hM]

theorem fixes_original_pair (s : SectorUnitary) (hs : (s : SectorMatrix).det = 1) :
    (∀ i : Fin 3, (sectorLeftSU3Automorphism s hs).equiv (flatFrameP i) = flatFrameP i) ∧
      (∀ i : Fin 3, (sectorLeftSU3Automorphism s hs).equiv (flatFrameQ i) = flatFrameQ i) := by
  have hp : InComplexSector (encoder flatFrameP) := by
    rw [flatFrameP_encoder]
    simp [InComplexSector, OctInComplex, flatXN]
  have hq : InComplexSector (encoder flatFrameQ) := by
    rw [flatFrameQ_encoder]
    simp [InComplexSector, OctInComplex, flatY1, octScalar, octI, quatI]
  constructor
  · intro i
    apply sectorLeftSU3_fixes_complex
    exact (complexSector_mem_iff _).mp
      (frame_in_complexSector flatFrameP flatFrameP_frame hp i)
  · intro i
    apply sectorLeftSU3_fixes_complex
    exact (complexSector_mem_iff _).mp
      (frame_in_complexSector flatFrameQ flatFrameQ_frame hq i)

/-- With the original first pair fixed, every genuine flat-ledger third frame is
carried to the original third frame or its ordered reversal by an actual left SU3
product automorphism. Its inverse and determinant sign are derived, never supplied. -/
theorem native_fixed_pair_third_frame_normalization (r : Fin 3 → Albert) (hr : Frame r)
    (hu : UniformLedger flatFrameP flatFrameQ r) :
    ∃ g : CompactAutomorphism,
      (∀ i : Fin 3, g.equiv (flatFrameP i) = flatFrameP i) ∧
      (∀ i : Fin 3, g.equiv (flatFrameQ i) = flatFrameQ i) ∧
      ((∀ i : Fin 3, g.equiv (r i) = flatFrameR i) ∨
        (∀ i : Fin 3, g.equiv (r i) = reverseFrame flatFrameR i)) := by
  obtain ⟨hx, hM, hMr, hMi⟩ := native_fixed_pair_hidden_gram_phase r hr hu
  obtain ⟨hy, hN, hNr, hNi⟩ :=
    native_fixed_pair_hidden_gram_phase flatFrameR flatFrameR_frame flat_uniform
  let M := hiddenMatrix (encoder r)
  let N := hiddenMatrix (encoder flatFrameR)
  have hMr0 : M.det.re = 0 := hMr
  have hNr0 : N.det.re = 0 := hNr
  have hPhase : M.det = N.det ∨ M.det = -N.det := by
    have hi : M.det.im = N.det.im ∨ M.det.im = -N.det.im :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (hMi.trans hNi.symm)
    rcases hi with hi | hi
    · left
      apply Complex.ext
      · linarith
      · linarith
    · right
      apply Complex.ext
      · simp_all
      · simp_all
  rcases hPhase with hd | hd
  · obtain ⟨s, hs, hMap⟩ := scaled_transport M N hM hN hd.symm
    have he := left_maps_hidden s hs (encoder r) (encoder flatFrameR) hx hy hMap
    have hf := fixes_original_pair s hs
    refine ⟨sectorLeftSU3Automorphism s hs, hf.1, hf.2, Or.inl ?_⟩
    intro i
    rw [frame_as_projector r hr, compactAutomorphism_projectorFrame, he]
    exact congrFun (frame_as_projector flatFrameR flatFrameR_frame).symm i
  · have hNegGram : (-N).conjTranspose * (-N) =
        Matrix.diagonal (fun _ => (1/3 : ℂ)) := by aesop
    have hNegDet : (-N).det = M.det := by
      rw [Matrix.det_neg]
      simp [Fintype.card_fin, show (-1 : ℂ) ^ 3 = -1 by norm_num]
      exact hd.symm
    obtain ⟨s, hs, hMap⟩ := scaled_transport M (-N) hM hNegGram hNegDet
    have hyNeg : complexProjection (-encoder flatFrameR) = 0 := by
      simpa [neg_one_smul, smul_zero] using
        (complexProjection_smul (-1) (encoder flatFrameR)).trans (by rw [hy, smul_zero])
    have hNegHidden := sectorHiddenLinear.map_neg (encoder flatFrameR)
    have he := left_maps_hidden s hs (encoder r) (-encoder flatFrameR) hx hyNeg
      (hMap.trans hNegHidden.symm)
    have hf := fixes_original_pair s hs
    refine ⟨sectorLeftSU3Automorphism s hs, hf.1, hf.2, Or.inr ?_⟩
    intro i
    rw [frame_as_projector r hr, compactAutomorphism_projectorFrame, he]
    have hp : projectorFrame (-encoder flatFrameR) = reverseFrame flatFrameR := by
      calc
        projectorFrame (-encoder flatFrameR) =
            projectorFrame ((-1 : ℝ) • encoder flatFrameR) := by rw [neg_one_smul]
        _ = reverseFrame (projectorFrame (encoder flatFrameR)) :=
          projectorFrame_neg_one_smul _
        _ = reverseFrame flatFrameR :=
          congrArg reverseFrame (frame_as_projector flatFrameR flatFrameR_frame).symm
    exact congrFun hp i

end Glennie.NativeFixedPairNormalization
