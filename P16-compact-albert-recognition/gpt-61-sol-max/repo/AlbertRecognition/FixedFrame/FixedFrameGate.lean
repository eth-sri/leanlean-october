/- Native reference action and assembly of the fixed-frame identities. -/
module
public import Glennie.Native.CoordinateSimp

public import AlbertRecognition.FixedFrame.CyclicFrameData

@[expose] public section
namespace AlbertRecognition.FixedFrame
section
open Glennie

/-- The actual projected reference multiplication on each diagonal frame. -/
theorem KA_h_self (i : Fin 3) : KA (h i) (h i) = (-1 : ℝ) • h i := by
  fin_cases i <;> apply Subtype.ext <;> apply Albert.ext <;>
    norm_num [albert_coords, KA_apply_apply, project_apply_coe, traceless, trace, h, e, unit]

/-- Two distinct actual frame vectors have projected product h_i+h_j. -/
theorem KA_h_cross (i j : Fin 3) (hij : i ≠ j) :
    KA (h i) (h j) = h i + h j := by
  fin_cases i <;> fin_cases j
  all_goals first | exact False.elim (hij rfl) | skip
  all_goals apply Subtype.ext
  all_goals apply Albert.ext <;>
    norm_num [albert_coords, KA_apply_apply, project_apply_coe, traceless, trace, h, e, unit]

/-- A uniform eigenspace calculation for the three Peirce slots. -/
theorem KA_h_slots (i k : Fin 3) (u : Octonion) :
    KA (h i) (X k u) =
      (if i = k then (1 : ℝ) else -(1/2 : ℝ)) • X k u := by
  fin_cases i <;> fin_cases k <;> apply Subtype.ext <;> apply Albert.ext <;>
    simp [albert_coords, KA_apply_apply, project_apply_coe, traceless, trace, h, e,
      X, X01, X02, X12, smul_smul] <;>
    solve
    | norm_num
    | module
    | (apply Prod.ext <;> apply Quaternion.ext <;>
        norm_num [smul_eq_mul])

/-- Literal native diagonal spanning identity, with rational coefficients. -/
theorem frameD_eq_h01 :
    frameD = (-1/3 : ℝ) • h 0 + (-2/3 : ℝ) • h 1 := by
  apply Subtype.ext
  apply Albert.ext <;> norm_num [frameD, h, e, unit]

/-- The unchanged initial fixed-frame gate for an arbitrary genuine symmetric
trilinear form. There is no unknown invariance, Jordan or common-scalar premise. -/
theorem fixedFrame_gate_of_A_q_zero (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ b : ℝ, ∀ i : Fin 3, KB B (h i) = b • KA (h i) := by
  obtain ⟨data⟩ := threeFrameScalarData_of_A_q_zero B hB
  obtain ⟨b,ha,hb,hc⟩ := data.common_coefficients
  have hdiag (i j : Fin 3) : KB B (h i) (h j) = b • KA (h i) (h j) := by
    by_cases hij : i = j
    · subst j
      rw [(data i).on_h_self, ha i, KA_h_self]
      simp only [smul_smul]
      congr 1
      ring
    · rw [data.cross_h i j hij, hb i, ha i, KA_h_cross i j hij, smul_add]
      have hr : (b - -b)/2 = b := by ring
      rw [hr]
      exact add_comm _ _
  have hd (i : Fin 3) : KB B (h i) frameD = b • KA (h i) frameD := by
    rw [frameD_eq_h01]
    simp only [map_add, map_smul, hdiag, smul_add, smul_smul]
    module
  have hslot (i k : Fin 3) (u : Octonion) :
      KB B (h i) (X k u) = b • KA (h i) (X k u) := by
    rw [(data i).on_X, KA_h_slots]
    split_ifs <;> simp [hb, hc, smul_smul] <;> module
  refine ⟨b, ?_⟩
  intro i
  apply LinearMap.ext
  intro x
  change KB B (h i) x = b • KA (h i) x
  rcases hs : (frameCoordinates x).2.2.2 with ⟨u,v⟩
  rw [frame_decompose x, hs, frameSpin_apply]
  simp only [map_add, map_smul, hdiag, hd, ← show X 2 = X01 from rfl, ← show X 1 = X02 from rfl,
    ← show X 0 = X12 from rfl, hslot, smul_add, smul_smul]
  module

end
end AlbertRecognition.FixedFrame
