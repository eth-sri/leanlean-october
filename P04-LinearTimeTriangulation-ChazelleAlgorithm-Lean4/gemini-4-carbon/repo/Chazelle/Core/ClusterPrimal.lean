module

public import Chazelle.Core.ClusterLabel
public import Chazelle.Core.SpecKernels

/-!
# WP-I, part 12: the input map as a rotation system

`PlanarMapAt m B μ E` (the input of `ClusterSpec`) stores a planar combinatorial map
`M : CombMap (Fin μ) F (Fin (2E))` in three arrays.  Here:

* `MapArrays`: the arrays hold a combinatorial map (`PlanarMapAt.mapArrays`), with
  `MapArrays.opp_lt`, `rot_inj`, `vert_rot`, `orbit`, `vert_surj`, `opp_opp`, …;
* `primalEnv`: the rotation system read by the searches (with a `first` array and flag arrays);
  `primalEnv_ok`, `primalEnv_sym`;
* `reach_of_walk`: a walk of `memGraph` avoiding the flagged vertices is a reachability of the
  search (for the dart flags `db` not `1`).
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator

@[expose] public section

/-- The arrays at `bO`, `bR`, `bV` hold the combinatorial map `M` on `Fin μ` / `Fin N`. -/
def MapArrays (m : ℕ → ℕ) (bO bR bV μ N : ℕ) {F : Type} (M : CombMap (Fin μ) F (Fin N)) : Prop :=
  ∀ d : Fin N, m (bO + d) = M.opp d ∧ m (bR + d) = M.rot d ∧ m (bV + d) = M.vert d

section arrays

variable {m : ℕ → ℕ} {bO bR bV μ N : ℕ} {F : Type} {M : CombMap (Fin μ) F (Fin N)}

theorem MapArrays.opp (h : MapArrays m bO bR bV μ N M) {d : ℕ} (hd : d < N) :
    m (bO + d) = M.opp ⟨d, hd⟩ := (h ⟨d, hd⟩).1

theorem MapArrays.rot (h : MapArrays m bO bR bV μ N M) {d : ℕ} (hd : d < N) :
    m (bR + d) = M.rot ⟨d, hd⟩ := (h ⟨d, hd⟩).2.1

theorem MapArrays.vert (h : MapArrays m bO bR bV μ N M) {d : ℕ} (hd : d < N) :
    m (bV + d) = M.vert ⟨d, hd⟩ := (h ⟨d, hd⟩).2.2

/-- Iterating the stored rotation is iterating the rotation. -/
theorem MapArrays.iterate_rot (h : MapArrays m bO bR bV μ N M) (n : ℕ) (d : Fin N) :
    (fun x => view m bR N x)^[n] d = ((M.rot ^ n) d : ℕ) := by
  induction n generalizing d with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, pow_succ, Equiv.Perm.mul_apply]
    have : view m bR N (d : ℕ) = ((M.rot d : Fin N) : ℕ) := by
      rw [view_lt d.2, h.rot d.2]
    rw [this, ih]

end arrays

/-- The input of `ClusterSpec` holds a planar map in its arrays. -/
theorem PlanarMapAt.exists_arrays {m : ℕ → ℕ} {B μ E : ℕ} (h : PlanarMapAt m B μ E) :
    ∃ (F : Type) (_ : Fintype F) (_ : DecidableEq F) (M : CombMap (Fin μ) F (Fin (2 * E))),
      M.Planar ∧ MapArrays m (m B) (m (B + 1)) (m (B + 2)) μ (2 * E) M := by
  obtain ⟨F, i1, i2, M, hM, hA⟩ := h
  exact ⟨F, i1, i2, M, hM, fun d => hA d⟩

/-- **The rotation system of the input map** with a `first` array and flag arrays. -/
def primalEnv (m : ℕ → ℕ) (bO bR bV bF bDB bVB μ N : ℕ) : Env :=
  ⟨view m bO N, view m bR N, view m bV N, view m bF μ, view m bDB N, view m bVB μ, μ, N⟩

section env

variable {m : ℕ → ℕ} {bO bR bV bF bDB bVB μ N : ℕ} {F : Type} {M : CombMap (Fin μ) F (Fin N)}

/-- **The input map is a well-formed rotation system** once `first` names a dart at every
vertex. -/
theorem primalEnv_ok [Fintype F] (h : MapArrays m bO bR bV μ N M)
    (hF : ∀ u, u < μ → m (bF + u) < N ∧ m (bV + m (bF + u)) = u) :
    (primalEnv m bO bR bV bF bDB bVB μ N).OK := by
  refine ⟨fun d hd => ?_, fun d hd => ?_, fun d hd => ?_, fun d hd e he hde => ?_,
    fun d hd => ?_, fun d hd e he hde => ?_, fun u hu => ?_, fun u hu => ?_⟩
  all_goals simp only [primalEnv] at *
  · rw [view_lt hd, h.opp hd]; exact (M.opp ⟨d, hd⟩).2
  · rw [view_lt hd, h.rot hd]; exact (M.rot ⟨d, hd⟩).2
  · rw [view_lt hd, h.vert hd]; exact (M.vert ⟨d, hd⟩).2
  · rw [view_lt hd, view_lt he, h.rot hd, h.rot he] at hde
    have := M.rot.injective (Fin.ext hde)
    exact congrArg Fin.val this
  · rw [view_lt hd, h.rot hd, view_lt (M.rot ⟨d, hd⟩).2, h.vert (M.rot ⟨d, hd⟩).2,
      view_lt hd, h.vert hd]
    simp [M.vert_rot]
  · rw [view_lt hd, view_lt he, h.vert hd, h.vert he] at hde
    have hsc := M.sameCycle_of_vert ⟨d, hd⟩ ⟨e, he⟩ (Fin.ext hde)
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    have := h.iterate_rot n ⟨d, hd⟩
    rw [this, hn]
  · rw [view_lt hu]; exact (hF u hu).1
  · rw [view_lt hu, view_lt (hF u hu).1]; exact (hF u hu).2

/-- The input map is symmetric for symmetric dart flags. -/
theorem primalEnv_sym (h : MapArrays m bO bR bV μ N M)
    (hdb : ∀ d, d < N → m (bDB + m (bO + d)) = m (bDB + d)) :
    (primalEnv m bO bR bV bF bDB bVB μ N).Sym := by
  intro d hd
  change d < N at hd
  have ho : m (bO + d) < N := by rw [h.opp hd]; exact (M.opp ⟨d, hd⟩).2
  show view m bO N (view m bO N d) = d ∧ view m bDB N (view m bO N d) = view m bDB N d
  rw [view_lt hd, view_lt ho, view_lt ho, view_lt hd]
  refine ⟨?_, hdb d hd⟩
  rw [h.opp hd, h.opp (M.opp ⟨d, hd⟩).2]
  simp [M.opp_opp]

/-- **Walks of the stored graph avoiding the flagged vertices are reachabilities** (for dart
flags never equal to `1`). -/
theorem reach_of_walk (h : MapArrays m bO bR bV μ N M) (hdb : ∀ d, d < N → m (bDB + d) ≠ 1)
    {B E : ℕ} (hB : m B = bO) (hB2 : m (B + 2) = bV) (hN : N = 2 * E) {u v : Fin μ}
    (w : (memGraph m B μ E).Walk u v) (hw : ∀ x ∈ w.support, m (bVB + x) ≠ 1) :
    (primalEnv m bO bR bV bF bDB bVB μ N).Reach u v := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | @cons a b c hadj w ih =>
    have ha : m (bVB + a) ≠ 1 := hw a (by simp)
    have hb : m (bVB + b) ≠ 1 := hw b (by simp)
    have hrest := ih (fun x hx => hw x (by simp [hx]))
    have hstep : (primalEnv m bO bR bV bF bDB bVB μ N).Step a b := by
      obtain ⟨-, hd⟩ := hadj
      rcases hd with ⟨d, hd, h1, h2⟩ | ⟨d, hd, h1, h2⟩
      · rw [← hN] at hd
        rw [hB2] at h1 h2
        rw [hB] at h2
        have ho : m (bO + d) < N := by rw [h.opp hd]; exact (M.opp ⟨d, hd⟩).2
        refine ⟨d, hd, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [primalEnv, view_lt hd]; exact hdb d hd
        · simp only [primalEnv, view_lt hd]; exact h1
        · simp only [Env.head, primalEnv, view_lt hd, view_lt ho]; exact h2
        · simp only [primalEnv, view_lt a.2]; exact ha
        · simp only [primalEnv, view_lt b.2]; exact hb
      · -- the opposite dart goes from `a` to `b`
        rw [← hN] at hd
        rw [hB2] at h1 h2
        rw [hB] at h2
        have ho : m (bO + d) < N := by rw [h.opp hd]; exact (M.opp ⟨d, hd⟩).2
        have hoo : m (bO + m (bO + d)) = d := by
          rw [h.opp ho]; simp only [h.opp hd, Fin.eta, M.opp_opp]
        refine ⟨m (bO + d), ho, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [primalEnv, view_lt ho]; exact hdb _ ho
        · simp only [primalEnv, view_lt ho]; exact h2
        · show view m bV N (view m bO N (m (bO + d))) = _
          rw [view_lt ho, hoo, view_lt hd]
          exact h1
        · simp only [primalEnv, view_lt a.2]; exact ha
        · simp only [primalEnv, view_lt b.2]; exact hb
    exact Relation.ReflTransGen.head hstep hrest

end env

end

end Chazelle.Core.Cluster
