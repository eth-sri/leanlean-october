module
public import Glennie.ExactCoordinates

@[expose] public section
namespace Glennie.Compact.NativeDictionary
open ExactCoordinates

variable {R S : Type*} [CommRing R] [CommRing S]

def unflatten (v : Fin 27 → R) : Coords R :=
  let a (i : Fin 26) := v i.succ
  v 0 • 1 + ⟨a 0 + a 1, -a 0 + a 1, -2 * a 1,
    (⟨a 2, a 3, -a 12, -a 13⟩, ⟨-a 18, -a 19, -a 24, a 25⟩),
    (⟨a 4, a 5, a 10, a 11⟩, ⟨a 16, a 17, a 22, -a 23⟩),
    (⟨a 6, a 7, -a 8, -a 9⟩, ⟨-a 14, -a 15, -a 20, a 21⟩)⟩

theorem map_unflatten (f : R →+* S) (v : Fin 27 → R) :
    coeffMap f (unflatten v) = unflatten (fun i => f (v i)) := by
  simp only [unflatten, coeffMap_add, coeffMap_smul, coeffMap_one]
  congr 1
  simp [coeffMap, ro, rq, map_ofNat]

def extUnit (n : Fin 27) : Fin 27 → R := fun i => if i = n then 1 else 0

def basisVector (n : Fin 27) : Coords R := unflatten (extUnit n)

@[simp] theorem map_basisVector (f : R →+* S) (n : Fin 27) :
    coeffMap f (basisVector n) = basisVector n := by
  simp [basisVector, map_unflatten, extUnit, apply_ite]
  rfl

noncomputable def nativeVector (i : Fin 27) : Albert := realize (RingHom.id ℝ) (basisVector i)

@[simp] theorem realize_basisVector (f : R →+* ℝ) (i : Fin 27) :
    realize f (basisVector i) = nativeVector i := by
  rw [nativeVector, ← map_basisVector f, realize_coeffMap]

end Glennie.Compact.NativeDictionary
