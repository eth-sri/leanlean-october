module

public import Glennie.Compact.Sections.Reversal
public import Glennie.Compact.Rank20Reduction
public import Glennie.Compact.FlatBase
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Glennie.Compact.Sections

open Glennie.Compact.Affine20 Glennie.Compact.FlowFamily
  Glennie.Compact.ChartTransfer Glennie.Compact.FlatBase Glennie.Compact.Rank20

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The chart point of T is recovered from the twenty rows at the base point of the family. -/
theorem rowsOf_chart_base (T : Triple) (hT : ∀ a : Fin 3, Frame (T a)) :
    rowsOf (encode20 (fullLedger T)) = rowLedger T 0 := by
  have h := rowsOf_motion T hT 0
  simp_all [motion_zero]

/-- The local section of the ledger map, indexed by chart coordinates.
The invertibility of the strict derivative is an explicit hypothesis, in exactly the
form `Rank20.rank20_of_bridge` (Rank20Reduction.lean) delivers it; nothing about rank or
determinants is assumed here. -/
theorem exists_section_of_equiv (T : Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T) :
    ∃ W : Set (Fin 20 → ℝ), IsOpen W ∧ encode20 (fullLedger T) ∈ W ∧
      ∃ sec : (Fin 20 → ℝ) → Triple,
        ContinuousOn sec W ∧
        sec (encode20 (fullLedger T)) = T ∧
        (∀ b ∈ W, ∀ a : Fin 3, Frame (sec b a)) ∧
        (∀ b ∈ W, encode20 (fullLedger (sec b)) = b) := by
  have hd : HasStrictFDerivAt (rowLedger T) (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) 0 :=
    hasStrictFDerivAt_rowLedger_of_equiv T e he
  -- Generalize the inverse-function-theorem term containing `Classical.choose` before using it.
  obtain ⟨Psi, hcoe, hsrc, htgt⟩ :
      ∃ Psi : OpenPartialHomeomorph (Fin 20 → ℝ) (Fin 20 → ℝ),
        (Psi : (Fin 20 → ℝ) → (Fin 20 → ℝ)) = rowLedger T ∧
          (0 : Fin 20 → ℝ) ∈ Psi.source ∧ rowLedger T 0 ∈ Psi.target :=
    ⟨hd.toOpenPartialHomeomorph (rowLedger T), hd.toOpenPartialHomeomorph_coe,
      hd.mem_toOpenPartialHomeomorph_source, hd.image_mem_toOpenPartialHomeomorph_target⟩
  have hb0 : rowsOf (encode20 (fullLedger T)) = rowLedger T 0 := rowsOf_chart_base T hT
  have hleft : Psi.symm (rowLedger T 0) = 0 := by
    have h := Psi.left_inv hsrc
    simp_all
  have hright : ∀ b : Fin 20 → ℝ, b ∈ Psi.target → rowLedger T (Psi.symm b) = b := by
    intro b hb
    have h := Psi.right_inv hb
    simpa [hcoe] using h
  have hsigma : ContinuousOn (fun b : Fin 20 → ℝ => Psi.symm (rowsOf b))
      (rowsOf ⁻¹' Psi.target) :=
    Psi.continuousOn_symm.comp' continuous_rowsOf.continuousOn (fun b hb => hb)
  refine ⟨rowsOf ⁻¹' Psi.target, Psi.open_target.preimage continuous_rowsOf, ?_,
    fun b => motion T (Psi.symm (rowsOf b)), ?_, ?_, ?_, ?_⟩
  · simp_all
  · refine continuousOn_pi' fun a => continuousOn_pi' fun i => ?_
    exact (continuous_motion T a i).comp_continuousOn' hsigma
  · simp [hb0, hleft, motion_zero]
  · intro b _ a
    apply motion_frame <;> assumption
  · intro b hb
    show encode20 (fullLedger (motion T (Psi.symm (rowsOf b)))) = b
    rw [encode_motion T hT, hright (rowsOf b) hb, chartVec_rowsOf]

/-- The same section, on a neighbourhood shrunk so that Phi stays strictly negative. -/
theorem exists_signed_section_of_equiv (T : Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T)
    {c : ℝ} (hneg : phiOf T < c) :
    ∃ W : Set (Fin 20 → ℝ), IsOpen W ∧ encode20 (fullLedger T) ∈ W ∧
      ∃ sec : (Fin 20 → ℝ) → Triple,
        ContinuousOn sec W ∧
        (∀ b ∈ W, ∀ a : Fin 3, Frame (sec b a)) ∧
        (∀ b ∈ W, encode20 (fullLedger (sec b)) = b) ∧
        (∀ b ∈ W, phiOf (sec b) < c) := by
  obtain ⟨W, hWopen, hmem, sec, hcont, hbase, hframes, hledger⟩ :=
    exists_section_of_equiv T hT e he
  have hphi : ContinuousOn (fun b : Fin 20 → ℝ => phiOf (sec b)) W :=
    continuous_phiOf.comp_continuousOn' hcont
  refine ⟨W ∩ (fun b : Fin 20 → ℝ => phiOf (sec b)) ⁻¹' Set.Iio c,
    hphi.isOpen_inter_preimage hWopen isOpen_Iio, ⟨hmem, ?_⟩, sec,
    hcont.mono Set.inter_subset_left, ?_, ?_, ?_⟩
  · show phiOf (sec (encode20 (fullLedger T))) ∈ Set.Iio c
    rw [hbase]
    exact hneg
  · intro b hb a
    exact hframes b hb.1 a
  · intro b hb
    exact hledger b hb.1
  · intro b hb
    exact hb.2

/-! ## The flat base -/

export _root_.Glennie.SubmissionR03 (flatBase)

theorem phiOf_flatBase : phiOf flatBase = -4 / 27 := flat_phi

private theorem uniform_fixed : transposeChart (encode20 (fullLedger flatBase)) = encode20 (fullLedger flatBase) := by
  rw [show fullLedger flatBase = _ from NativeFlatRank20.flat_ledger]
  funext i; fin_cases i <;> rfl

theorem flat_two_sections (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv flatBase) :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧ encode20 (fullLedger flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (fullLedger (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (fullLedger (secNeg b)) = b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < -(1/27)) := by
  obtain ⟨W, hWopen, hmem, sec, hcont, hframes, hledger, hsign⟩ :=
    exists_signed_section_of_equiv (c := -(1/27)) flatBase NativeFlatRank20.flat_frames e he
      (by rw [phiOf_flatBase]; norm_num)
  let V := W ∩ transposeChart ⁻¹' W
  have hc : ContinuousOn (fun b => flip (sec (transposeChart b))) V :=
    continuous_flip.comp_continuousOn' (hcont.comp' continuous_transposeChart.continuousOn fun _ h => h.2)
  refine ⟨V,hWopen.inter (hWopen.preimage continuous_transposeChart),⟨hmem,show transposeChart _ ∈ W by rw [uniform_fixed]; exact hmem⟩,
    _,sec,hc,hcont.mono Set.inter_subset_left,fun b h a => hframes _ h.2 _,fun b h => hframes b h.1,
    ?_,fun b h => hledger b h.1,?_,fun b h => hsign b h.1⟩
  · intro b h; rw [flip_chart,hledger _ h.2,transpose_twice]
  · intro b h; rw [phi_flip]; linarith [hsign _ h.2]

end
end Glennie.Compact.Sections
