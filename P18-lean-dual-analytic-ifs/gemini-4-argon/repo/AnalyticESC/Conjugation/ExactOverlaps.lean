module

public import AnalyticESC.Conjugation.Characterisation
public import AnalyticESC.Separation

@[expose] public section

/-!
# Exact overlaps and sub-conjugation

The remark on exact overlaps in Section 1.2.3: an analytic IFS with a non-singleton attractor and
an exact overlap is sub-conjugated to a self-similar IFS.

The attractor `Λ` is invariant under every composition `f_w`. If `Λ` is finite, then the iterates
of a single map repeat on any two points of `Λ`; as the map is a contraction, injective on `I`,
the two points agree. So a non-singleton attractor is infinite, and an exact overlap `f_i = f_j`
on `Λ` holds on `[0,1]` by the identity theorem. Neither of `i`, `j` is a prefix of the other, so
`ij` and `ji` are distinct words of the same length with `f_{ij} = f_j ∘ f_j = f_{ji}` on `[0,1]`.
The map conjugating `f_{ij}` to a similarity (Theorem 1.12) conjugates the pair.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ## Compositions on `I` -/

/-- `f_{uv}(x) = f_u(f_v(x))`, with `f_v(x)` real, for `x ∈ I`. -/
theorem comp_append_ofReal (u v : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    Φ.comp (u ++ v) x = Φ.comp u ((Φ.comp v x).re : ℂ) := by
  rw [Φ.comp_append, Function.comp_apply, ← Φ.comp_ofReal v hx]

/-! ## The attractor -/

/-- The attractor is invariant under every composition `f_a`. -/
private theorem exact_re_comp_mem_attractor (a : List (Fin N)) {x : ℝ} :
    x ∈ Φ.attractor → (Φ.comp a x).re ∈ Φ.attractor := by
  rintro ⟨w, rfl⟩; exact ⟨_, Φ.natProj_prepend a w⟩

/-- If the attractor is `{p}`, every map fixes `p`. -/
theorem fixedPoint_of_attractor_singleton {p : ℝ} (hp : Φ.attractor = {p}) (k : Fin N) :
    (Φ.f k p).re = p := by
  have h1 : Φ.natProj (fun _ => k) = p := mem_singleton_iff.1 (hp ▸ ⟨_, rfl⟩)
  exact ((h1.symm.trans (Φ.natProj_eq_realMap _)).trans (congrArg _ h1)).symm

/-- The attractor of a system with at least one map is infinite unless it is a singleton. -/
theorem attractor_infinite (hN : 0 < N) (hnd : ¬ ∃ x, Φ.attractor = {x}) :
    Φ.attractor.Infinite := by
  intro hfin
  let k : Fin N := ⟨0, hN⟩
  set p := Φ.natProj fun _ => k
  have hp : p ∈ Φ.attractor := ⟨_, rfl⟩
  refine hnd ⟨p, Set.ext fun y => ⟨fun hy => ?_, fun h => h.symm ▸ hp⟩⟩
  have hyI := Φ.attractor_subset_I hy
  have key {n m : ℕ} (hlt : n < m)
      (he : (Φ.comp (List.replicate n k) y).re = (Φ.comp (List.replicate m k) y).re) : y = p := by
    have hd : List.replicate (m - n) k ≠ [] := by simp [Nat.sub_ne_zero_of_lt hlt]
    refine Φ.eq_of_fixed hd hyI (Φ.attractor_subset_I hp) ?_
      (by simpa [List.ofFn_const] using (Φ.natProj_eq_comp_prefix (fun _ => k) (m - n)).symm)
    refine Φ.injOn_re_comp (List.replicate n k) (Φ.re_comp_mem_I _ hyI) hyI ?_
    dsimp only
    rw [← Φ.comp_append_ofReal _ _ hyI, ← List.replicate_add, Nat.add_sub_of_le hlt.le, he]
  have := hfin.to_subtype
  obtain ⟨n, m, hnm, he⟩ := Finite.exists_ne_map_eq_of_infinite fun n =>
    (⟨_, Φ.exact_re_comp_mem_attractor (List.replicate n k) hy⟩ : Φ.attractor)
  exact (lt_or_gt_of_ne hnm).elim (fun h => key h (Subtype.ext_iff.1 he))
    (fun h => key h (Subtype.ext_iff.1 he).symm)

end IFS

end AnalyticESC
