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

/-- `|f_w(x) - f_w(y)| ≤ c_max^{|w|} |x - y|` on `I`. -/
private theorem exact_abs_re_comp_sub_le (w : List (Fin N)) {x y : ℝ} (hx : x ∈ I)
    (hy : y ∈ I) : |(Φ.comp w x).re - (Φ.comp w y).re| ≤ Φ.cmax ^ w.length * |x - y| := by
  have h := Φ.norm_comp_sub_le w (ofReal_mem_nbhd Φ.ε_pos hx) (ofReal_mem_nbhd Φ.ε_pos hy)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  rw [← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans h

/-- Two points of `I` fixed by `f_w`, for a nonempty word `w`, are equal. -/
private theorem exact_eq_of_fixed {w : List (Fin N)} (hw : w ≠ []) {x y : ℝ} (hx : x ∈ I)
    (hy : y ∈ I) (hfx : (Φ.comp w x).re = x) (hfy : (Φ.comp w y).re = y) : x = y := by
  have hle := Φ.exact_abs_re_comp_sub_le w hx hy
  rw [hfx, hfy] at hle
  have hc : Φ.cmax ^ w.length < 1 :=
    pow_lt_one₀ Φ.cmax_nonneg Φ.cmax_lt_one (List.length_pos_iff.2 hw).ne'
  by_contra hne
  have hpos : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hne)
  nlinarith

/-- `f_{uv}(x) = f_u(f_v(x))`, with `f_v(x)` real, for `x ∈ I`. -/
private theorem exact_comp_append_ofReal (u v : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    Φ.comp (u ++ v) x = Φ.comp u ((Φ.comp v x).re : ℂ) := by
  rw [Φ.comp_append, Function.comp_apply, ← Φ.comp_ofReal v hx]

/-! ## The attractor -/

/-- `π(a w) = f_a(π(w))` for a finite word `a` and an infinite word `w`. -/
private theorem exact_natProj_prepend (a : List (Fin N)) (w : ℕ → Fin N) :
    Φ.natProj (fun n => if h : n < a.length then a[n] else w (n - a.length)) =
      (Φ.comp a (Φ.natProj w)).re := by
  set v : ℕ → Fin N := fun n => if h : n < a.length then a[n] else w (n - a.length)
  have hlist : ∀ n, (List.ofFn fun k : Fin (n + a.length) => v k) =
      a ++ List.ofFn fun k : Fin n => w k := fun n =>
    List.ext_getElem (by simp [Nat.add_comm]) fun l h1 h2 => by
      simp only [List.getElem_ofFn, List.getElem_append, v]
  have hπ : Φ.natProj w ∈ I := Φ.attractor_subset_I ⟨w, rfl⟩
  have hc : ContinuousAt (fun t : ℝ => (Φ.comp a t).re) (Φ.natProj w) :=
    Complex.continuous_re.continuousAt.comp ((Φ.differentiableAt_comp a
      (subset_closure (ofReal_mem_nbhd Φ.ε_pos hπ))).continuousAt.comp
      Complex.continuous_ofReal.continuousAt)
  refine tendsto_nhds_unique (((tendsto_add_atTop_iff_nat a.length).2
    (Φ.tendsto_natProj v)).congr fun n => ?_) (hc.tendsto.comp (Φ.tendsto_natProj w))
  rw [Function.comp_apply, hlist n, ← Complex.ofReal_zero,
    Φ.exact_comp_append_ofReal _ _ (left_mem_Icc.2 zero_le_one)]

/-- The attractor is invariant under every composition `f_a`. -/
private theorem exact_re_comp_mem_attractor (a : List (Fin N)) {x : ℝ}
    (hx : x ∈ Φ.attractor) : (Φ.comp a x).re ∈ Φ.attractor := by
  obtain ⟨w, rfl⟩ := hx
  exact ⟨_, Φ.exact_natProj_prepend a w⟩

/-- If the attractor is `{p}`, every map fixes `p`. -/
theorem fixedPoint_of_attractor_singleton {p : ℝ} (hp : Φ.attractor = {p}) (k : Fin N) :
    Φ.f k p = p := by
  have hpA : p ∈ Φ.attractor := hp ▸ mem_singleton p
  have h := Φ.exact_re_comp_mem_attractor [k] hpA
  rw [hp] at h
  have hr : (Φ.f k p).re = p := by simpa using h
  have hi := (Φ.inClass k).im_eq_zero p
    (ofReal_mem_nbhd (by linarith [Φ.ε_pos]) (Φ.attractor_subset_I hpA))
  exact Complex.ext (by simpa using hr) (by simpa using hi)

/-- A finite attractor has at most one point. -/
private theorem exact_attractor_subsingleton (k : Fin N) (hfin : Φ.attractor.Finite) :
    Φ.attractor.Subsingleton := by
  intro x hx y hy
  have hxI := Φ.attractor_subset_I hx
  have hyI := Φ.attractor_subset_I hy
  -- if the iterates `f_k^n` and `f_k^m`, `n < m`, agree at `x` and at `y`, then `f_k^n(x)` and
  -- `f_k^n(y)` are fixed by `f_k^{m-n}`
  have key : ∀ n m, n < m →
      (Φ.comp (List.replicate n k) x).re = (Φ.comp (List.replicate m k) x).re →
      (Φ.comp (List.replicate n k) y).re = (Φ.comp (List.replicate m k) y).re → x = y := by
    intro n m hlt hx' hy'
    obtain ⟨d, rfl⟩ : ∃ d, m = d + n := ⟨m - n, by omega⟩
    have hfix : ∀ z ∈ I,
        (Φ.comp (List.replicate n k) z).re = (Φ.comp (List.replicate (d + n) k) z).re →
        (Φ.comp (List.replicate d k) ((Φ.comp (List.replicate n k) z).re : ℂ)).re =
          (Φ.comp (List.replicate n k) z).re := by
      intro z hz h
      rw [← Φ.exact_comp_append_ofReal _ _ hz, ← List.replicate_add]
      exact h.symm
    have hd : List.replicate d k ≠ [] := by
      rw [Ne, List.replicate_eq_nil_iff]
      omega
    exact Φ.injOn_re_comp _ hxI hyI (Φ.exact_eq_of_fixed hd (Φ.re_comp_mem_I _ hxI)
      (Φ.re_comp_mem_I _ hyI) (hfix x hxI hx') (hfix y hyI hy'))
  have := hfin.to_subtype
  obtain ⟨n, m, hnm, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (β := Φ.attractor × Φ.attractor) fun n =>
      (⟨_, Φ.exact_re_comp_mem_attractor (List.replicate n k) hx⟩,
        ⟨_, Φ.exact_re_comp_mem_attractor (List.replicate n k) hy⟩)
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at he
  rcases lt_or_gt_of_ne hnm with h | h
  · exact key n m h he.1 he.2
  · exact key m n h he.1.symm he.2.symm

/-- The attractor of a system with at least one map is infinite unless it is a singleton. -/
theorem attractor_infinite (hN : 0 < N) (hnd : ¬ ∃ x, Φ.attractor = {x}) :
    Φ.attractor.Infinite := by
  intro hfin
  have hk : Φ.natProj (fun _ => (⟨0, hN⟩ : Fin N)) ∈ Φ.attractor := ⟨_, rfl⟩
  rcases (Φ.exact_attractor_subsingleton ⟨0, hN⟩ hfin).eq_empty_or_singleton with he | he
  · rw [he] at hk
    exact hk
  · exact hnd he

/-! ## Words of the same length -/

end IFS

end AnalyticESC
