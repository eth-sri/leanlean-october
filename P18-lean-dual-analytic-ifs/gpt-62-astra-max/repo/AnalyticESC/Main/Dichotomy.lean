module

public import AnalyticESC.Separation
public import AnalyticESC.Main.Closeness


@[expose] public section

/-! # Failure of separation produces equal projections

Pad a close pair on the left, then cancel the common suffix. On its image there is
an exponentially wide window on which the two residual maps are super-exponentially
close. Repeated sampling there identifies every jet of two limiting projections.
-/
namespace AnalyticESC.IFS
open Set Metric Filter Topology
variable {N : ℕ} (Φ : IFS N)

private noncomputable abbrev decay (k : ℕ) : ℝ := (1/2)^k

private structure Pair (k : ℕ) where
  a : Address N
  b : Address N
  win : Letters N
  grow : k ≤ win.length
  diff : a 0 ≠ b 0
  close : ∀ x ∈ I, let n := win.length; let y := Φ.R win x;
    |Φ.R (block n a).reverse y - Φ.R (block n b).reverse y| ≤ decay k * decay k ^ n

private lemma pairs (h : ¬ Φ.SESC) (k : ℕ) : Nonempty (Φ.Pair k) := by
  have hq : 0 < decay k := by unfold decay; positivity
  have hq1 : decay k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨n,i,j,hij,hclose⟩ : ∃ n, ∃ i j : Block N n, i ≠ j ∧ Φ.supDist (.ofFn i) (.ofFn j) < (decay k^(k+2))^n := by
    by_contra! H; exact h ⟨_,pow_pos hq _,H⟩
  have hn := depth_pos hij
  let d := i ⟨0,hn⟩
  let addr (i : Block N n) := pad d (List.ofFn i).reverse
  have get (i : Block N n) : block n (addr i) = (List.ofFn i).reverse := by simpa [addr] using block_pad_length d (List.ofFn i).reverse
  obtain ⟨m,ml,e,ne⟩ := first_difference (diff_blocks (m := n) (v := addr i) (w := addr j) (by simpa [get] using hij))
  have hmn : m < n := by exact_mod_cast ml
  let u := (block m (addr i)).reverse
  let l := n+k
  let t := List.replicate (l-u.length) d
  have len : (u++t).length = l := by simp [t,u,block,l]; omega
  refine ⟨⟨shift m (addr i),shift m (addr j),u++t,by rw [len]; omega,by simpa [shift] using ne,?_⟩⟩
  intro x hx; dsimp only; rw [len,Φ.R_append _ _ hx]
  have hy := Φ.re_comp_mem_I t hx
  have ev (v : Block N n) (he : (block m (addr v)).reverse = u) :
      Φ.R (block l (shift m (addr v))).reverse (Φ.R u (Φ.R t x)) = Φ.R (List.replicate (k+m) d) (Φ.R (.ofFn v) (Φ.R t x)) := by
    rw [← he,← Φ.R_append _ _ hy,← List.reverse_append,← block_add]; dsimp only [addr]; rw [block_pad _ _ (by simp [l]; omega)]
    simp [l,List.reverse_append,Φ.R_append _ _ hy,Nat.add_assoc]
  rw [ev i rfl,ev j (congrArg List.reverse e.symm)]
  apply ((Φ.close_after _ _ _ hy).trans hclose.le).trans
  rw [← pow_mul,← pow_succ']; exact pow_le_pow_of_le_one hq.le hq1 (by dsimp [l]; nlinarith)

private lemma match_jets {v w : Address N} {p : I} {a b : ℕ → Address N} {W : Window Φ}
    (hn : Tendsto W.n atTop atTop) (hp : Tendsto (fun k => W.point k 0) atTop (𝓝 (p:ℝ))) (ha : Tendsto a atTop (𝓝 v)) (hb : Tendsto b atTop (𝓝 w))
    (h : W.small fun k x => W.proj a k x - W.proj b k x) : EqOn (Φ.dualProj ⊤ v) (Φ.dualProj ⊤ w) Φ.tube := by
  have hz (t : ℕ → I) : Tendsto (fun k => W.point k (t k)) atTop (𝓝 (p:ℝ)) :=
    hp.congr_dist (squeeze_zero (fun _ => dist_nonneg) (fun k => Φ.abs_re_comp_sub_le (W.word k) zero_I (t k).2) (Φ.shrinks.comp hn))
  apply agree_jets (convex_nbhd _).isPreconnected (Φ.real_mem p.2) (Φ.analytic_dual _ _) (Φ.analytic_dual _ _)
  intro r
  have an l w := analyticOnNhd_re_ofReal Φ.ε_pos (Φ.analytic_dual l w).differentiableOn
  obtain ⟨t,ht⟩ := W.samples hn (W.jets (fun k => an _ _) (fun k => an _ _) h r)
  have hI k := W.maps k (t k).2
  have H := ((Complex.continuous_ofReal.tendsto _).comp ht)
  have lim {v c} (hh : Tendsto c atTop (𝓝 v)) := Φ.proj_limit hh (ENat.tendsto_natCast_nhds_top.comp hn) (Φ.real_mem p.2) ((Complex.continuous_ofReal.tendsto _).comp (hz t)) r
  apply sub_eq_zero.mp (tendsto_nhds_unique ((lim ha).sub (lim hb)) ?_)
  simpa only [Function.comp_def,Complex.ofReal_sub,Complex.ofReal_zero,Window.proj,real_jet (isOpen_nbhd _) (Φ.analytic_dual _ _) (fun _ => Φ.im_dualProj_ofReal _ _) r (Φ.real_mem (hI _))] using H

/-- Pointwise separation for infinite words with different initial letters suffices. -/
theorem sesc_of_separated (h : ∀ i j : Address N, i 0 ≠ j 0 →
    ¬ ∀ x : I, Φ.P i x = Φ.P j x) : Φ.SESC := by
  classical
  by_contra hn
  let S k := (Φ.pairs hn k).some
  let z k : I := ⟨_,Φ.re_comp_mem_I (S k).win zero_I⟩
  let data k := (z k,(S k).a,(S k).b)
  obtain ⟨⟨p,i,j⟩,σ,hσ,lim⟩ := CompactSpace.tendsto_subseq data
  let T k := S (σ k)
  let W : Window Φ := ⟨fun k => (T k).win⟩
  have nlim : Tendsto W.n atTop atTop := tendsto_atTop_mono (fun k => (T k).grow) hσ.tendsto_atTop
  have ha := lim.snd_nhds.fst_nhds
  have hb := lim.snd_nhds.snd_nhds
  have hij : i 0 ≠ j 0 := (isClosed_discrete {p : Fin N × Fin N | p.1 ≠ p.2}).mem_of_tendsto
    ((tendsto_pi_nhds.mp ha 0).prodMk_nhds (tendsto_pi_nhds.mp hb 0)) (.of_forall fun k => (T k).diff)
  apply h i j hij; intro x
  apply Φ.match_jets (W := W) nlim (continuous_subtype_val.continuousAt.tendsto.comp lim.fst_nhds) ha hb _ (Φ.real_mem x.2); apply W.distort
  · intro a b ha hab hb δ hδ r hr
    have lim := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)).comp hσ.tendsto_atTop
    filter_upwards [lim.eventually_le_const hδ,lim.eventually_le_const hr] with k hk hl
    have hq : 0 ≤ decay (σ k) := by dsimp [decay]; positivity
    exact ⟨a,left_mem_Icc.mpr hab.le,((T k).close a ⟨ha,hab.le.trans hb⟩).trans
      (mul_le_mul hk (pow_le_pow_left₀ hq hl _) (pow_nonneg hq _) hδ.le)⟩

/-- Theorem 1.5: if `sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > 0` for all distinct `i, j ∈ Σ ∪ Σ_*` with
`|i| = |j|`, then `Φ` satisfies the SESC. -/
theorem theorem_1_5 (h : ∀ i j : Address N, i ≠ j → 0 < dev (Φ.dualProj ⊤ i) (Φ.dualProj ⊤ j)) : Φ.SESC := by
  apply Φ.sesc_of_separated; intro i j hij e
  have := h i j fun he => hij (congrFun he 0)
  dsimp only [P] at e; simp [dev,e] at this

end IFS
end AnalyticESC
