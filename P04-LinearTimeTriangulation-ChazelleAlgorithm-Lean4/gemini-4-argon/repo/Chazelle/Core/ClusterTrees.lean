module

public import Chazelle.Core.ClusterEnc
public import Chazelle.Core.ClusterBfs
public import Chazelle.Core.ClusterSplitMath

/-!
# WP-I, part 23: the trees of the breadth-first searches

* `primal_tree`: a breadth-first search from `0` on a rotation system encoding a connected
  planar map `M` (no flags) reaches every vertex and its parents and levels form a spanning tree
  `T` of `M` whose levels change by at most one along every dart (the property the slabs need);
* `dual_cotree`: a breadth-first search from the face `0` on a rotation system encoding the dual
  of the star map, with the darts of the tree `starTree T a` blocked, reaches every face, and its
  parents and levels form a rooted cotree `C`; its queue and parents form a well-formed
  preorder tree `R` (`BTree`) with the parents of `C`.
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

section primal

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {G : Env}

omit [Fintype F] [DecidableEq F] in
/-- With no flags, a connected map is reachable from every vertex. -/
theorem reach_all (hM : M.Connected) (hG : EnvEnc G M (fun v => (v : ℕ)) (fun d => (d : ℕ)))
    (hdb : ∀ d, d < N → G.db d ≠ 1) (hvb : ∀ v, v < μ → G.vb v ≠ 1) (u w : Fin μ) :
    G.Reach u w := by
  rw [hG.reach_iff]
  obtain ⟨p⟩ := M.reachable_of_connected hM u w
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | @cons a b c hadj p ih =>
    obtain ⟨-, d, hd1, hd2⟩ := hadj
    exact Relation.ReflTransGen.head ⟨d, hdb _ d.2, hd1, hd2, hvb _ a.2, hvb _ b.2⟩ ih

omit [Fintype F] [DecidableEq F] in
/-- **The primal breadth-first tree.** -/
theorem primal_tree (hM : M.Connected) (hμ : 0 < μ) (hGN : G.N = N)
    (hG : EnvEnc G M (fun v => (v : ℕ)) (fun d => (d : ℕ)))
    (hdb : ∀ d, d < N → G.db d ≠ 1) (hvb : ∀ v, v < μ → G.vb v ≠ 1)
    {L : ℕ} {lab0 lab lev par q : ℕ → ℕ} {t : ℕ} (hI : G.Inv 0 L lab0 lab lev par q t t) :
    ∃ T : SpanTree M, (T.root : ℕ) = 0 ∧ (∀ v, T.level v = lev v) ∧
      (∀ v, v ≠ T.root → par v < N ∧ (T.par v : ℕ) = G.opp (par v) ∧
        (T.parent v : ℕ) = G.vert (par v)) ∧
      (∀ d : Fin N, T.level (M.head d) ≤ T.level (M.vert d) + 1) ∧ (∀ v, T.level v < μ) := by
  have hN : 0 < N := by
    obtain ⟨d, -⟩ := M.vert_surj ⟨0, hμ⟩; exact Nat.lt_of_le_of_lt (Nat.zero_le _) d.2
  -- every vertex is queued
  have hq : ∀ v : Fin μ, ∃ i, i < t ∧ q i = v := fun v =>
    (hI.reach_iff v).mp (by
      have := reach_all hM hG hdb hvb ⟨0, hμ⟩ v
      simpa using this)
  have hpar : ∀ v : Fin μ, (v : ℕ) ≠ 0 → G.ParOK lev par q (Classical.choose (hq v)) := by
    intro v hv
    obtain ⟨hi, hqi⟩ := Classical.choose_spec (hq v)
    refine hI.par _ hi ?_
    by_contra h0
    have : Classical.choose (hq v) = 0 := by omega
    rw [this, hI.q0] at hqi
    exact hv hqi.symm
  have hqv : ∀ v : Fin μ, q (Classical.choose (hq v)) = v := fun v =>
    (Classical.choose_spec (hq v)).2
  set r : Fin μ := ⟨0, hμ⟩
  let pd : Fin μ → Fin N := fun v => ⟨par v % N, Nat.mod_lt _ hN⟩
  have hpd : ∀ v : Fin μ, (v : ℕ) ≠ 0 → par v < N ∧ (pd v : ℕ) = par v := by
    intro v hv
    have := (hpar v hv).1
    rw [hqv, hGN] at this
    exact ⟨this, Nat.mod_eq_of_lt this⟩
  have hne : ∀ v : Fin μ, v ≠ r → (v : ℕ) ≠ 0 := fun v hv h => hv (Fin.ext h)
  -- the head of the parent dart is `v`, its tail one level up
  have hhead : ∀ v : Fin μ, v ≠ r → M.head (pd v) = v := by
    intro v hv
    obtain ⟨-, -, hh, -⟩ := hpar v (hne v hv)
    rw [hqv] at hh
    apply Fin.ext
    rwa [← hG.head (pd v), (hpd v (hne v hv)).2]
  have hlev : ∀ v : Fin μ, v ≠ r → lev (M.vert (pd v)) + 1 = lev v := by
    intro v hv
    obtain ⟨-, -, -, j, -, hvj, hlj⟩ := hpar v (hne v hv)
    rw [hqv] at hvj hlj
    have : ((M.vert (pd v) : Fin μ) : ℕ) = q j := by
      rwa [← hG.vert (pd v), (hpd v (hne v hv)).2]
    rw [this, hlj]
  refine ⟨⟨r, fun v => lev v, fun v => M.opp (pd v), hI.lev0, fun v hv => ?_,
    fun v hv => ?_⟩, rfl, fun v => rfl, fun v hv => ?_, fun d => ?_, fun v => ?_⟩
  · show M.vert (M.opp (pd v)) = v
    exact hhead v hv
  · show lev (M.head (M.opp (pd v))) + 1 = lev v
    rw [M.head_opp]; exact hlev v hv
  · refine ⟨(hpd v (hne v hv)).1, ?_, ?_⟩
    · show ((M.opp (pd v) : Fin N) : ℕ) = G.opp (par v)
      rw [← (hpd v (hne v hv)).2, hG.opp]
    · rw [SpanTree.parent_of_ne _ hv]
      show ((M.head (M.opp (pd v)) : Fin μ) : ℕ) = G.vert (par v)
      rw [M.head_opp, ← (hpd v (hne v hv)).2, hG.vert]
  · show lev (M.head d) ≤ lev (M.vert d) + 1
    obtain ⟨i, hi, hqi⟩ := hq (M.vert d)
    have := hI.lev_head_le hi (hGN ▸ d.2) (by rw [hG.vert, hqi]) (hdb _ d.2)
      (by rw [hG.head]; exact hvb _ (M.head d).2)
    rwa [hG.head, hqi] at this
  · show lev v < μ
    obtain ⟨i, hi, hqi⟩ := hq v
    have h1 := hI.lev_le i hi
    have h2 := hI.tn
    have h3 : G.nv ≤ μ := by
      by_contra h
      obtain ⟨w, hw⟩ := hG.eV_surj μ (by omega)
      have := w.2
      omega
    rw [hqi] at h1
    omega

end primal

section dual

variable {μ N : ℕ} {F : Type} [Fintype F] [DecidableEq F] {M : CombMap (Fin μ) F (Fin N)}
  {T : SpanTree M} {a : F → Fin N} {ha : ∀ g, M.face (a g) = g} {G : Env}

omit [Fintype F] [DecidableEq F] in
/-- Reflexive-transitive closures of symmetric relations are symmetric. -/
theorem rtg_symm {α : Type*} {r : α → α → Prop} (hr : ∀ x y, r x y → r y x) {x y : α}
    (h : Relation.ReflTransGen r x y) : Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.head (hr _ _ hs) ih

omit [Fintype F] [DecidableEq F] in
/-- Monotonicity of reflexive-transitive closures. -/
theorem rtg_mono {α : Type*} {r p : α → α → Prop} (hrp : ∀ x y, r x y → p x y) {x y : α}
    (h : Relation.ReflTransGen r x y) : Relation.ReflTransGen p x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.tail ih (hrp _ _ hs)

omit [Fintype F] [DecidableEq F] in
/-- An equivalence closure of a symmetric relation is its reflexive-transitive closure. -/
theorem rtg_of_eqvGen {α : Type*} {r : α → α → Prop} (hr : ∀ x y, r x y → r y x) {x y : α}
    (h : Relation.EqvGen r x y) : Relation.ReflTransGen r x y := by
  induction h with
  | rel x y h => exact Relation.ReflTransGen.single h
  | refl => exact Relation.ReflTransGen.refl
  | symm x y _ ih => exact rtg_symm hr ih
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The dual breadth-first cotree.**  A search from face `0` on a rotation system encoding the
dual of the star map with exactly the tree darts of `starTree T a` blocked reaches all `N`
faces; its parent darts and levels form a rooted cotree `C`, and its queue and parents a
well-formed preorder tree `R` with the parents of `C`. -/
theorem dual_cotree (hM : M.Connected) (hN : 0 < N) (hGN : G.N = 3 * N) (hGnv : G.nv = N)
    (hG : EnvEnc G (star M).dual (fun g => (g : ℕ)) (enc N))
    (hdb : ∀ x, G.db (enc N x) = 1 ↔ (starTree T a ha).IsTreeDart x)
    (hvb : ∀ g, g < N → G.vb g ≠ 1)
    {L : ℕ} {lab0 lab lev par q : ℕ → ℕ} {t : ℕ} (hI : G.Inv 0 L lab0 lab lev par q t t) :
    t = N ∧ ∃ C : CoTree (starTree T a ha), (C.r0 : ℕ) = 0 ∧
      (∀ g, g ≠ C.r0 → par g < 3 * N ∧ enc N (C.fpar g) = par g) ∧
      (BTree.OK ⟨N, q, fun g => G.vert (par g)⟩) ∧
      (∀ g : Fin N, BTree.up ⟨N, q, fun g => G.vert (par g)⟩ g = (C.parent g : ℕ)) := by
  classical
  set TS := starTree T a ha
  -- the steps of the search are the non-tree crossings
  have hstep : ∀ u w : Fin N, EnvEnc.TStep G (star M).dual (fun g => (g : ℕ)) (enc N) u w ↔
      (star M).faceRel TS.coDarts u w := by
    intro u w
    constructor
    · rintro ⟨x, hx, rfl, rfl, -, -⟩
      refine ⟨x, ?_, rfl, rfl⟩
      rw [SpanTree.mem_coDarts]
      exact fun h => hx ((hdb x).mpr h)
    · rintro ⟨x, hx, rfl, rfl⟩
      refine ⟨x, fun h => (SpanTree.mem_coDarts TS).mp hx ((hdb x).mp h), rfl, rfl,
        hvb _ (Fin.isLt _), hvb _ (Fin.isLt _)⟩
  -- every face is reached
  have hreach : ∀ g : Fin N, G.Reach 0 g := by
    intro g
    have h0 := (hG.reach_iff ⟨0, hN⟩ g).mpr (by
      have hc := SpanTree.eqvGen_faceRel_coDarts TS (star_connected M hM) ⟨0, hN⟩ g
      have := rtg_of_eqvGen (r := (star M).faceRel TS.coDarts) (fun x y h => (star M).faceRel_opp
        (SpanTree.coDarts_oppClosed TS) h) hc
      exact rtg_mono (fun x y h => (hstep x y).mpr h) this)
    simpa using h0
  have hq : ∀ g : Fin N, ∃ i, i < t ∧ q i = g := fun g => (hI.reach_iff g).mp (hreach g)
  have ht : t = N := by
    have htn := hI.tn
    rw [hGnv] at htn
    refine le_antisymm htn ?_
    have hsub : Finset.range N ⊆ (Finset.range t).image q := by
      intro g hg
      obtain ⟨i, hi, hqi⟩ := hq ⟨g, Finset.mem_range.mp hg⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, hqi⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    exact this.trans (Finset.card_image_le.trans (by rw [Finset.card_range]))
  subst t
  set r0 : Fin N := ⟨0, hN⟩
  have hne : ∀ g : Fin N, g ≠ r0 → (g : ℕ) ≠ 0 := fun g hg h => hg (Fin.ext h)
  have hpar : ∀ g : Fin N, g ≠ r0 → G.ParOK lev par q (Classical.choose (hq g)) := by
    intro g hg
    obtain ⟨hi, hqi⟩ := Classical.choose_spec (hq g)
    refine hI.par _ hi ?_
    by_contra h0
    have : Classical.choose (hq g) = 0 := by omega
    rw [this, hI.q0] at hqi
    exact hne g hg hqi.symm
  have hqv : ∀ g : Fin N, q (Classical.choose (hq g)) = g := fun g =>
    (Classical.choose_spec (hq g)).2
  -- decoding the parent darts
  have hdec : ∀ g : Fin N, g ≠ r0 → ∃ x, enc N x = par g := by
    intro g hg
    have := (hpar g hg).1
    rw [hqv, hGN] at this
    exact hG.eD_surj _ (by rw [hGN]; exact this)
  let fp : Fin N → Fin N ⊕ Fin N ⊕ Fin N := fun g =>
    if hg : g ≠ r0 then Classical.choose (hdec g hg) else .inl r0
  have hfp : ∀ g : Fin N, g ≠ r0 → enc N (fp g) = par g := by
    intro g hg
    simp only [fp, dite_eq_left hg]
    exact Classical.choose_spec (hdec g hg)
  have hmem : ∀ g : Fin N, g ≠ r0 → fp g ∈ TS.coDarts := by
    intro g hg
    obtain ⟨-, hdb', -, -⟩ := hpar g hg
    rw [hqv, ← hfp g hg] at hdb'
    rw [SpanTree.mem_coDarts]
    exact fun h => hdb' ((hdb _).mpr h)
  have hhead : ∀ g : Fin N, g ≠ r0 → (star M).face ((star M).opp (fp g)) = g := by
    intro g hg
    obtain ⟨-, -, hh, -⟩ := hpar g hg
    rw [hqv, ← hfp g hg, hG.head] at hh
    exact Fin.ext hh
  have hlev : ∀ g : Fin N, g ≠ r0 → lev ((star M).face (fp g)) + 1 = lev g := by
    intro g hg
    obtain ⟨-, -, -, j, -, hvj, hlj⟩ := hpar g hg
    rw [hqv, ← hfp g hg, hG.vert] at hvj
    rw [hqv] at hlj
    have : (((star M).face (fp g) : Fin N) : ℕ) = q j := hvj
    rw [this, hlj]
  refine ⟨rfl, ⟨r0, fp, fun g => lev g, hI.lev0, hmem, hhead, hlev⟩, rfl,
    fun g hg => ⟨?_, hfp g hg⟩, ⟨hN, fun i hi => ?_, fun i hi j hj hij => hI.qinj i hi j hj hij,
    fun i hi0 hi => ?_⟩, fun g => ?_⟩
  · rw [← hfp g hg]; exact enc_lt _
  · have := hI.qlt i hi; rwa [hGnv] at this
  · obtain ⟨-, -, -, j, hj, hvj, -⟩ := hI.par i hi hi0
    exact ⟨j, hj, hvj.symm⟩
  · -- the parents agree
    unfold BTree.up BTree.root
    simp only
    rw [hI.q0]
    by_cases hg : g = r0
    · subst hg
      simp [CoTree.parent]
      intro h; exact absurd rfl h
    · have hg0 := hne g hg
      rw [ite_eq_right hg0, CoTree.parent_of_ne _ hg, ← hfp g hg, hG.vert]
      rfl

end dual

end

end Chazelle.Core.Cluster
