/- Actual reference-automorphism transport of the unrestricted Jacobi kernel.
-/
module

public import AlbertRecognition.FixedFrame.FixedFrameGate
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Tactic

@[expose] public section
namespace AlbertRecognition.FixedFrame
section
open Glennie

/-- The native diagonal coefficient has no kernel on the trace-zero subspace. -/
theorem KA_h0_injective : Function.Injective (KA (h 0)) := by
  intro x y hxy
  have hx := trace_V x
  have hy := trace_V y
  have hh := congrArg (fun u : V => (u : Albert)) hxy
  simp only [KA_apply_apply, project_apply_coe] at hh
  clear hxy
  norm_num [Albert.ext_iff, Prod.ext_iff, Quaternion.ext_iff,
    traceless, albert_coords, trace, h, e] at hh hx hy
  apply Subtype.ext
  ext <;> grind

theorem h0_ne_zero : h 0 ≠ 0 := by
  intro hz
  have hd := congrArg (fun x : V => (x : Albert).d0) hz
  norm_num [h, e, unit] at hd

/-- Pull back the arbitrary unknown, apply the proved fixed-frame gate, then
transport the equality back. There is no invariance assumption on B. -/
theorem transported_frame_constraint (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) (g : CompactAutomorphism) :
    ∃ c : ℝ, ∀ i : Fin 3,
      KB B (automorphismV g (h i)) = c • KA (automorphismV g (h i)) := by
  obtain ⟨c,hc⟩ := fixedFrame_gate_of_A_q_zero
    (pullbackCubic (automorphismV g) B) (A_q_pullback_zero g B hB)
  refine ⟨c, ?_⟩
  intro i
  apply LinearMap.ext
  intro z
  obtain ⟨w,rfl⟩ := (automorphismV g).surjective z
  calc
    KB B (automorphismV g (h i)) (automorphismV g w) =
        automorphismV g (KB (pullbackCubic (automorphismV g) B) (h i) w) :=
      (automorphismV_KB_pullback g B (h i) w).symm
    _ = automorphismV g (c • KA (h i) w) := congrArg (automorphismV g) (LinearMap.congr_fun (hc i) w)
    _ = c • KA (automorphismV g (h i)) (automorphismV g w) := by
      rw [map_smul, automorphismV_KA]

/-- Nonzero transported directions force their scalar to agree with the base
scalar, by product symmetry and the proved native injectivity at h0. -/
theorem transported_scalar_eq (B : SymmetricCubic) (g : CompactAutomorphism)
    (b c : ℝ) (hb : KB B (h 0) = b • KA (h 0))
    (hc : KB B (automorphismV g (h 0)) = c • KA (automorphismV g (h 0))) :
    b = c := by
  have hv : KA (h 0) (automorphismV g (h 0)) ≠ 0 := by
    simpa only [map_zero] using
      KA_h0_injective.ne ((automorphismV g).injective.ne h0_ne_zero)
  have heq : b • KA (h 0) (automorphismV g (h 0)) =
      c • KA (h 0) (automorphismV g (h 0)) := by
    calc
      _ = KB B (h 0) (automorphismV g (h 0)) :=
        (LinearMap.congr_fun hb _).symm
      _ = KB B (automorphismV g (h 0)) (h 0) := KB_comm B _ _
      _ = c • KA (automorphismV g (h 0)) (h 0) := LinearMap.congr_fun hc _
      _ = _ := congrArg (fun x : V => c • x) (KA_comm _ _)
  exact smul_left_injective ℝ hv heq

/-- One scalar works on every actual transported reference frame. The sole
hypothesis is the original unrestricted Jacobi equation. -/
theorem common_scalar_on_reference_frames (B : SymmetricCubic)
    (hB : A (q referenceCubic) B = 0) :
    ∃ b : ℝ, ∀ g : CompactAutomorphism, ∀ i : Fin 3,
      KB B (automorphismV g (h i)) = b • KA (automorphismV g (h i)) := by
  obtain ⟨b,hb⟩ := fixedFrame_gate_of_A_q_zero B hB
  refine ⟨b, ?_⟩
  intro g
  obtain ⟨c,hc⟩ := transported_frame_constraint B hB g
  have hbc         := transported_scalar_eq B g b c (hb 0) (hc 0)
  rw [← hbc] at hc
  exact hc

end
end AlbertRecognition.FixedFrame
