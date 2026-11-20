module

public import OAI.NumberTheory.PrimeGaps.MarkedMoments

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def extendPerm {n : ℕ} (e : Equiv.Perm (Fin n)) (d : ℕ) : Equiv.Perm (Fin (n+d)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin d))).trans finSumFinEquiv)

@[simp] theorem extendPerm_left {n d : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    extendPerm e d (i.castAdd d)=(e i).castAdd d := by
  simp [extendPerm]

@[simp] theorem extendPerm_right {n d : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin d) :
    extendPerm e d (i.natAdd n)=i.natAdd n := by
  simp [extendPerm]

end LargePrimeGaps

end OAI
