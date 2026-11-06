module

public import Glennie.Compact.NativeFlatColumns01
public import Glennie.Compact.NativeFlatColumns45
public import Glennie.Compact.NativeFlatColumns89
public import Glennie.Compact.NativeFlatColumns1213
public import Glennie.Compact.NativeFlatColumns1617
public import Glennie.Compact.Sections

@[expose] public section

namespace Glennie.Compact.NativeFlatSections

open Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FlowFamily Glennie.Compact.Sections
open Glennie.Compact.Rank20Certificate

noncomputable section
set_option autoImplicit false

theorem jacobianEntry_flatBase_all (r n : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r n = JQ r n := by
  fin_cases n
  · exact Glennie.Compact.NativeFlatColumns01.jacobianEntry_flatBase_column_zero r
  · exact Glennie.Compact.NativeFlatColumns01.jacobianEntry_flatBase_column_one r
  · exact Glennie.Compact.NativeFlatColumns01.jacobianEntry_flatBase_column_two r
  · exact Glennie.Compact.NativeFlatColumns01.jacobianEntry_flatBase_column_three r
  · exact Glennie.Compact.NativeFlatColumns45.jacobianEntry_flatBase_column_four r
  · exact Glennie.Compact.NativeFlatColumns45.jacobianEntry_flatBase_column_five r
  · exact Glennie.Compact.NativeFlatColumns45.jacobianEntry_flatBase_column_six r
  · exact Glennie.Compact.NativeFlatColumns45.jacobianEntry_flatBase_column_seven r
  · exact Glennie.Compact.NativeFlatColumns89.jacobianEntry_flatBase_column_eight r
  · exact Glennie.Compact.NativeFlatColumns89.jacobianEntry_flatBase_column_nine r
  · exact Glennie.Compact.NativeFlatColumns89.jacobianEntry_flatBase_column_ten r
  · exact Glennie.Compact.NativeFlatColumns89.jacobianEntry_flatBase_column_eleven r
  · exact Glennie.Compact.NativeFlatColumns1213.jacobianEntry_flatBase_column_twelve r
  · exact Glennie.Compact.NativeFlatColumns1213.jacobianEntry_flatBase_column_thirteen r
  · exact Glennie.Compact.NativeFlatColumns1213.jacobianEntry_flatBase_column_fourteen r
  · exact Glennie.Compact.NativeFlatColumns1213.jacobianEntry_flatBase_column_fifteen r
  · exact Glennie.Compact.NativeFlatColumns1617.jacobianEntry_flatBase_column_sixteen r
  · exact Glennie.Compact.NativeFlatColumns1617.jacobianEntry_flatBase_column_seventeen r
  · exact Glennie.Compact.NativeFlatColumns1617.jacobianEntry_flatBase_column_eighteen r
  · exact Glennie.Compact.NativeFlatColumns1617.jacobianEntry_flatBase_column_nineteen r

theorem native_flat_two_sections_full54 :
    ∃ V : Set (Fin 20 → ℝ), IsOpen V ∧
      encode20 (ledger54 flatBase) ∈ V ∧
      ∃ secPos secNeg : (Fin 20 → ℝ) → Triple,
        ContinuousOn secPos V ∧ ContinuousOn secNeg V ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secPos b a)) ∧
        (∀ b ∈ V, ∀ a : Fin 3, Frame (secNeg b a)) ∧
        (∀ b ∈ V, encode20 (ledger54 (secPos b)) = b) ∧
        (∀ b ∈ V, encode20 (ledger54 (secNeg b)) = b) ∧
        (∀ b ∈ V, ledger54 (secPos b) = decode20 b) ∧
        (∀ b ∈ V, ledger54 (secNeg b) = decode20 b) ∧
        (∀ b ∈ V, 0 < phiOf (secPos b)) ∧
        (∀ b ∈ V, phiOf (secNeg b) < 0) := by
  obtain ⟨e, he⟩ := Glennie.Compact.Rank20.rank20_of_bridge flatBase jacobianEntry_flatBase_all
  obtain ⟨V, hVopen, hbase, secPos, secNeg, hcontPos, hcontNeg,
    hframesPos, hframesNeg, hchartPos, hchartNeg, hpos, hneg⟩ := flat_two_sections e he
  exact ⟨V, hVopen, hbase, secPos, secNeg, hcontPos, hcontNeg,
    hframesPos, hframesNeg, hchartPos, hchartNeg,
    fun b hb => (hchartPos b hb ▸ decode_encode_frames (secPos b) (hframesPos b hb)).symm,
    fun b hb => (hchartNeg b hb ▸ decode_encode_frames (secNeg b) (hframesNeg b hb)).symm,
    hpos, hneg⟩

end
end Glennie.Compact.NativeFlatSections
