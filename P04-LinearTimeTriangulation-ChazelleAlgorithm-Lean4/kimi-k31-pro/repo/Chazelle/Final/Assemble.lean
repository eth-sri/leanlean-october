module

public import Chazelle.Final.LinkSplit
public import Chazelle.Rwx
public import Chazelle.SimpTactics

/-!
# Assembling the triangulations of the walked pieces

`triangulates_of_pairs` is the form of `Chazelle.Final.triangulates_of_rotations` used by the
output pass of the RAM program: the pieces come as a list `acc` of pairs (vertex list, weak
triangulation), the vertex lists being, member by member, rotations of a permutation of the
pieces `splitAll (List.range P.n) D`; no triangulation function on all pieces is needed.
-/

namespace Chazelle.Final

@[expose] public section

open Set
open Chazelle.Split (splitAll EnumDiags)
open Chazelle.EarClip (subPoly n_subPoly relabelList subPoly_rotate weakTriangulates_rotate)
open Chazelle.Existence (WeakTriangulates relabel triangulates_of_weak)
open Chazelle.Mountain (IsPiece)

variable {P : Polygon}

/-- **Assembling a list of triangulated rotated pieces.**  Let `D` enumerate the inserted
diagonals, `M'` a permutation of the pieces `splitAll (List.range P.n) D`, and `acc` a list of
pairs `(m, T)` whose vertex lists `m` are, member by member, rotations of the members of `M'`
and with `T` a weak triangulation of `subPoly P m`.  Then the triangles, relabelled to original
indices, triangulate `P`. -/
theorem triangulates_of_pairs (hP : P.Simple) {D : List (ℕ × ℕ)} (hD : EnumDiags P D)
    {M' : List (List ℕ)} (hperm : List.Perm M' (splitAll (List.range P.n) D))
    {acc : List (List ℕ × List Polygon.Triangle)}
    (hrot : List.Forall₂ (fun m' p => ∃ r, p.1 = m'.rotate r) M' acc)
    (hT : ∀ p ∈ acc, WeakTriangulates (subPoly P p.1) p.2) :
    P.Triangulates (acc.flatMap fun p => p.2.map (relabelList p.1)) := by
  classical
  have hG := (good_init hP hD).seqSplit
  rw [seqSplit_eq_splitAll (hD.diagSystem hP)] at hG
  have hG' := hG.perm hperm.symm
  have hnd : M'.Nodup := (pairwise_not_rotate_of_disj hG'.simple hG'.disj).imp fun h e =>
    h 0 (by rw [List.rotate_zero]; exact e.symm)
  have hpiece : ∀ m' ∈ M', IsPiece P m' := fun m' hm' => hD.isPiece hP (hperm.mem_iff.1 hm')
  set g : List ℕ → List ℕ × List Polygon.Triangle := fun m' => acc.getD (M'.idxOf m') ([], [])
    with hg
  have hlen  := hrot.length_eq
  have hMg : acc = M'.map g := by
    apply List.ext_getElem
    · rw [List.length_map, hlen]
    · intro t h1 h2
      simp only [List.getElem_map, hg]
      rw [hnd.idxOf_getElem, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
        Option.getD_some]
  have hgmem : ∀ m' ∈ M', g m' ∈ acc := by
    intro m' hm'
    rw [hMg]; exact List.mem_map_of_mem hm'
  have hgrot : ∀ m' ∈ M', ∃ r, (g m').1 = m'.rotate r := by
    intro m' hm'
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hm'
    have := List.forall₂_iff_get.1 hrot
    obtain ⟨r, hr⟩ := this.2 t ht (by omega)
    refine ⟨r, ?_⟩
    simp only [hg]
    rw [hnd.idxOf_getElem, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      Option.getD_some]
    simpa using hr
  set T' : List ℕ → List Polygon.Triangle := fun m' =>
    if h : ∃ r, (g m').1 = m'.rotate r then (g m').2.map (relabel (Classical.choose h) m'.length)
    else [] with hT'
  have hwT : ∀ m' ∈ M', WeakTriangulates (subPoly P m') (T' m') ∧
      (T' m').map (relabelList m') = (g m').2.map (relabelList (g m').1) := by
    intro m' hm'
    have h := hgrot m' hm'
    have hr := Classical.choose_spec h
    set r := Classical.choose h
    have hw0 : WeakTriangulates (subPoly P (g m').1) (g m').2 := hT _ (hgmem m' hm')
    have hw : WeakTriangulates ((subPoly P m').rotate r) (g m').2 := by
      rwx [← subPoly_rotate, ← hr]
    have hw' := weakTriangulates_rotate _ r hw
    rw [n_subPoly] at hw'
    have e : T' m' = (g m').2.map (relabel r m'.length) := by
      rw [hT']; sirfl only [dite_eq_left h]
    refine ⟨by rwx [e], ?_⟩
    rw [e, List.map_map]
    apply List.map_congr_left
    intro t ht
    have hb := Chazelle.Split.index_lt_of_weak hw ht
    rw [Chazelle.Existence.n_rotate, n_subPoly] at hb
    obtain ⟨t1, t2, t3⟩ := t
    simp only [Function.comp, relabelList, Chazelle.Existence.relabel_fst,
      Chazelle.Existence.relabel_snd_fst, Chazelle.Existence.relabel_snd_snd]
    rw [hr, getD_rotate_of_lt r hb.1, getD_rotate_of_lt r hb.2.1, getD_rotate_of_lt r hb.2.2,
      Nat.add_comm r t1, Nat.add_comm r t2, Nat.add_comm r t3]
  have heq : acc.flatMap (fun p => p.2.map (relabelList p.1)) =
      M'.flatMap (fun m' => (T' m').map (relabelList m')) := by
    rw [hMg, List.flatMap_map]
    apply List.flatMap_congr
    intro m' hm'
    exact (hwT m' hm').2.symm
  rw [heq]
  have hsplit : ∀ m ∈ splitAll (List.range P.n) D, WeakTriangulates (subPoly P m) (T' m) :=
    fun m hm => (hwT m (hperm.mem_iff.2 hm)).1
  exact triangulates_perm (triangulates_of_weak (hD.weakTriangulates hP hsplit))
    (List.Perm.flatMap_right _ hperm.symm)

end

end Chazelle.Final
