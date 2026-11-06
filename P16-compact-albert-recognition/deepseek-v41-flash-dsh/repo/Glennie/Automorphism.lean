/- Native invariance under an actual product- and trace-preserving linear equivalence.
No automorphism existence or transitivity is assumed or proved here. -/
module
public import Glennie.Obligations
public import Glennie.BasicLaws

@[expose] public section
namespace Glennie.CompactAutomorphism
noncomputable section

def refl : CompactAutomorphism where
  equiv := LinearEquiv.refl ℝ Albert
  map_jordan x y := by simp only [LinearEquiv.refl_apply]
  map_trace x := by simp only [LinearEquiv.refl_apply]

/-- Composition means first apply h, then g. -/
def comp (g h : CompactAutomorphism) : CompactAutomorphism where
  equiv := h.equiv.trans g.equiv
  map_jordan x y := by simp only [LinearEquiv.trans_apply, h.map_jordan, g.map_jordan]
  map_trace x := by simp only [LinearEquiv.trans_apply, g.map_trace, h.map_trace]

@[simp] theorem comp_apply (g h : CompactAutomorphism) (x : Albert) :
    (g.comp h).equiv x = g.equiv (h.equiv x) := rfl
variable (g : CompactAutomorphism)
include g in

def symm  : CompactAutomorphism where
  equiv := g.equiv.symm
  map_jordan x y := by
    apply g.equiv.injective
    simp only [LinearEquiv.apply_symm_apply, g.map_jordan]
  map_trace x := by
    simpa only [LinearEquiv.apply_symm_apply] using (g.map_trace (g.equiv.symm x)).symm
include g in

@[simp] theorem symm_apply  (x : Albert) :
    g.symm.equiv x = g.equiv.symm x := rfl
include g in

theorem map_unit  : g.equiv (1 : Albert) = 1 := by
  have h := g.map_jordan 1 (g.equiv.symm 1)
  simpa using h.symm
include g in

theorem inner_map  (x y : Albert) :
    inner (g.equiv x) (g.equiv y) = inner x y := by
  rw [inner, ← g.map_jordan, g.map_trace]
  rfl
include g in

theorem map_U  (x z : Albert) :
    g.equiv (U x z) = U (g.equiv x) (g.equiv z) := by
  simp only [U, map_sub, map_smul, g.map_jordan]
include g in

theorem phi_map  (x y z : Albert) :
    phi (g.equiv x) (g.equiv y) (g.equiv z) = phi x y z := by
  simp only [phi, ← g.map_U, ← map_sub, ← g.map_jordan, g.inner_map]
include g in

theorem map_traceless  (x : Albert) :
    g.equiv (traceless x) = traceless (g.equiv x) := by
  simp only [traceless, map_sub, map_smul, g.map_unit, g.map_trace]
include g in

theorem map_frame  (p : Fin 3 → Albert) (hp : Frame p) :
    Frame (fun i => g.equiv (p i)) where
  trace_one i := by rw [g.map_trace, hp.trace_one]
  idempotent i := by rw [← g.map_jordan, hp.idempotent]
  orthogonal i j hij := by rw [← g.map_jordan, hp.orthogonal i j hij, map_zero]
  sum_unit := by rw [← map_add, ← map_add, hp.sum_unit, g.map_unit]
include g in

theorem encoder_map  (p : Fin 3 → Albert) :
    encoder (fun i => g.equiv (p i)) = g.equiv (encoder p) := by
  simp [encoder]
include g in

theorem ledger_map  (p q r : Fin 3 → Albert) (i j k : Fin 3) :
    ledger (fun a => g.equiv (p a)) (fun a => g.equiv (q a))
      (fun a => g.equiv (r a)) i j k = ledger p q r i j k := by
  simp only [ledger, ← g.map_jordan, g.map_trace]

end
end Glennie.CompactAutomorphism
