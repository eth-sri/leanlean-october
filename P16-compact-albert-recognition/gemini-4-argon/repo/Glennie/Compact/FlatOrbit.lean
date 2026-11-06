module
public import Glennie.Compactness
public import Glennie.Compact.Affine20
public import Glennie.Compact.FlatBase

@[expose] public section
namespace Glennie.Compact.FrameTopology
open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
noncomputable section
set_option autoImplicit false

theorem continuous_jordan_comp {α : Type*} [TopologicalSpace α] {f g : α → Albert}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun a => Glennie.jordan (f a) (g a)) := by
  simpa only [Function.comp_def] using continuous_jordan.comp (hf.prodMk hg)

theorem continuous_inner_comp {α : Type*} [TopologicalSpace α] {f g : α → Albert}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun a => Glennie.inner (f a) (g a)) := by
  simpa only [Function.comp_def] using continuous_native_inner.comp (hf.prodMk hg)

theorem continuous_trace : Continuous (fun x : Albert => Glennie.trace x) := by
  simpa only [inner_unit_right] using
    continuous_inner_comp continuous_id' (continuous_const (y := (1 : Albert)))

theorem continuous_trace_comp {α : Type*} [TopologicalSpace α] {f : α → Albert}
    (hf : Continuous f) : Continuous (fun a => Glennie.trace (f a)) := by
  simpa only [Function.comp_def] using continuous_trace.comp hf

theorem continuous_entry (a i : Fin 3) : Continuous (fun T : Triple => T a i) := by
  simpa only [Function.comp_def] using (continuous_apply i).comp (continuous_apply a)

theorem continuous_ledger54 : Continuous (fun T : Triple => ledger54 T) :=
  Continuous.prodMk
    (continuous_pi fun i => continuous_pi fun j => continuous_pi fun k =>
      continuous_trace_comp (continuous_jordan_comp
        (continuous_jordan_comp (continuous_entry 0 i) (continuous_entry 1 j))
        (continuous_entry 2 k)))
    (Continuous.prodMk
      (continuous_pi fun i => continuous_pi fun j =>
        continuous_inner_comp (continuous_entry 0 i) (continuous_entry 1 j))
      (Continuous.prodMk
        (continuous_pi fun j => continuous_pi fun k =>
          continuous_inner_comp (continuous_entry 1 j) (continuous_entry 2 k))
        (continuous_pi fun k => continuous_pi fun i =>
          continuous_inner_comp (continuous_entry 2 k) (continuous_entry 0 i))))

def flatBaseTriple : Triple := ![flatFrameP, flatFrameQ, flatFrameR]

end
end Glennie.Compact.FrameTopology

namespace Glennie.Compact.FlatOrbit
open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20 Glennie.Compact.FrameTopology
noncomputable section
set_option autoImplicit false

theorem mapAtoms_refl (T : Triple) :
    mapAtoms Glennie.CompactAutomorphism.refl T = T := by
  funext a i; rfl

theorem mapAtoms_comp (g h : Glennie.CompactAutomorphism) (T : Triple) :
    mapAtoms g (mapAtoms h T) = mapAtoms (g.comp h) T := rfl

theorem mapAtoms_symm_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple) :
    mapAtoms g.symm (mapAtoms g T) = T := by
  funext a i; exact g.equiv.symm_apply_apply (T a i)

def autOrbit (S : Triple) : Set Triple :=
  {T : Triple | ∃ g : Glennie.CompactAutomorphism, mapAtoms g S = T}

theorem autOrbit_eq_of_mem {S T : Triple} (h : T ∈ autOrbit S) :
    autOrbit T = autOrbit S := by
  obtain ⟨g, hg⟩ := h
  have hS : mapAtoms g.symm T = S := by rw [← hg, mapAtoms_symm_mapAtoms]
  refine Set.Subset.antisymm (fun X ⟨k, hk⟩ => ⟨k.comp g, by rw [← mapAtoms_comp, hg, hk]⟩)
    (fun X ⟨k, hk⟩ => ⟨k.comp g.symm, by rw [← mapAtoms_comp, hS, hk]⟩)

theorem frame_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple)
    (hT : ∀ a : Fin 3, Glennie.Frame (T a)) (a : Fin 3) :
    Glennie.Frame (mapAtoms g T a) :=
  g.map_frame (T a) (hT a)

theorem phi_mapAtoms (g : Glennie.CompactAutomorphism) (T : Triple) :
    Glennie.phi (Glennie.encoder (mapAtoms g T 0)) (Glennie.encoder (mapAtoms g T 1))
        (Glennie.encoder (mapAtoms g T 2)) =
      Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1))
        (Glennie.encoder (T 2)) := by
  have h (a : Fin 3) : Glennie.encoder (mapAtoms g T a) = g.equiv (Glennie.encoder (T a)) := by
    rw [mapAtoms_slot]; exact g.encoder_map (T a)
  rw [h 0, h 1, h 2, g.phi_map]

theorem phi_eq_of_mem_autOrbit {S T : Triple} (h : T ∈ autOrbit S) :
    Glennie.phi (Glennie.encoder (T 0)) (Glennie.encoder (T 1)) (Glennie.encoder (T 2)) =
      Glennie.phi (Glennie.encoder (S 0)) (Glennie.encoder (S 1))
        (Glennie.encoder (S 2)) := by
  obtain ⟨g, rfl⟩ := h
  exact phi_mapAtoms g S

end
end Glennie.Compact.FlatOrbit
