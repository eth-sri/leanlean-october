module

public import AnalyticESC.Dual.Projection

@[expose] public section

/-! Continuity follows by truncating the series, with a common geometric tail bound for
all nearby systems. -/

namespace AnalyticESC

open Set Metric Filter Topology
open scoped ENNReal

/-- Openness of a condition on an entire compact fibre (the tube lemma). -/
theorem isOpen_forall_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {A : Set (X × Y)} (hA : IsOpen A) : IsOpen {x | ∀ y : Y, (x, y) ∈ A} := by
  convert (isClosedMap_fst_of_compactSpace _ hA.isClosed_compl).isOpen_compl using 1
  aesop

namespace IFS.Continuity

variable {N : ℕ} {ε ε' : ℝ}

/-- Holomorphic jets restricted to the interval, with the uniform metric. -/
noncomputable def jet (Φ : IFS N ε) (i : Fin N) (j : ℕ) : C(I, ℂ) :=
  ⟨fun x => iteratedDeriv j (Φ.f i) (x : ℝ),
    ((Φ.differentiableOn_f i).iteratedDeriv_complex (isOpen_nbhd _) j).continuousOn.comp_continuous
      (Complex.continuous_ofReal.comp continuous_subtype_val)
      (fun x => ofReal_mem_nbhd_two Φ.ε_pos x.2)⟩

theorem jetDist_eq (Φ : IFS N ε) (Ψ : IFS N ε') (i : Fin N) (j : ℕ) :
    jetDist (Φ.f i) (Ψ.f i) j = dist (jet Φ i j) (jet Ψ i j) := by
  rw [ContinuousMap.dist_eq_iSup]
  exact iSup_congr fun _ => (dist_eq_norm ..).symm

/-- The three jets carry the ℓ¹ metric, and the system uses the maximum over its maps. -/
abbrev JetSpace (N : ℕ) := PiLp ∞ (fun _ : Fin N => PiLp 1 (fun _ : Fin 3 => C(I, ℂ)))

noncomputable abbrev jets (Φ : IFS N ε) : JetSpace N :=
  WithLp.toLp ∞ fun i => WithLp.toLp 1 (jet Φ i ∘ Fin.val)

theorem d2_eq_dist (Φ : IFS N ε) (Ψ : IFS N ε') : d2 Φ Ψ = dist (jets Φ) (jets Ψ) := by
  simp [d2, d2Sys_eq, d2Map, jetDist_eq, PiLp.dist_eq_iSup, PiLp.dist_eq_sum (p := 1) (by simp)]

end IFS.Continuity

/-- Analytic systems, equipped with the pseudometric of their jets on the interval. -/
structure System (N : ℕ) where
  val : Fin N → ℂ → ℂ
  property : InUnionClass val

namespace System

open IFS.Continuity

variable {N : ℕ}

noncomputable def ifs (F : System N) : IFS N F.property.choose :=
  ⟨F.val, F.property.choose_spec.1, F.property.choose_spec.2⟩

noncomputable instance : PseudoMetricSpace (System N) :=
  PseudoMetricSpace.induced (fun F => jets F.ifs) inferInstance

theorem dist_eq_d2 (F G : System N) : dist F G = d2Sys G.val F.val :=
  (dist_comm ..).trans (d2_eq_dist G.ifs F.ifs).symm

@[fun_prop]
theorem continuous_jet (i : Fin N) (j : Fin 3) : Continuous (fun F : System N => jets F.ifs i j) :=
  (show Continuous (fun F : JetSpace N => F i j) by fun_prop).comp continuous_induced_dom

@[fun_prop]
theorem continuous_jet_eval (i : Fin N) (j : Fin 3) :
    Continuous (fun p : System N × I => iteratedDeriv j (p.1.val i) (p.2 : ℝ)) :=
  ((continuous_jet i j).comp continuous_fst).eval continuous_snd

private theorem continuous_deriv_eval (i : Fin N) : Continuous
    (fun p : System N × I => deriv (p.1.val i) (p.2 : ℝ)) := by simpa only [Fin.val_one, iteratedDeriv_one] using continuous_jet_eval i 1

private theorem continuous_nonlin_eval (i : Fin N) : Continuous
    (fun p : System N × I => p.1.ifs.nonlin i (p.2 : ℝ)) := by
  simpa only [Fin.val_two, iteratedDeriv_succ, iteratedDeriv_zero, Pi.div_def, IFS.nonlin, System.ifs] using
    (continuous_jet_eval i 2).div (continuous_deriv_eval i) fun p =>
      (p.1.ifs.inClass i).deriv_ne_zero _ (p.1.ifs.real_mem_closed p.2.2)

/-- A strict bound on a compact fibre continues to hold on all nearby fibres. -/
private theorem eventually_norm_lt {g : System N × I → ℂ} (hg : Continuous g) {F : System N} {c : ℝ}
    (hc : ∀ x : I, ‖g (F, x)‖ < c) : ∀ᶠ G in 𝓝 F, ∀ x : I, ‖g (G, x)‖ < c := by
  exact (isOpen_forall_compact (isOpen_lt hg.norm continuous_const)).mem_nhds hc

local notation "State" => System N × (ℕ → Fin N) × I

private theorem continuous_onState {f : Fin N → System N × I → ℂ} (hf : ∀ i, Continuous (f i)) :
    Continuous (fun p : State => f (p.2.1 0) (p.1, p.2.2)) :=
  ((continuous_prod_of_discrete_left (f := fun p => f p.1 p.2)).2 hf).comp
    (f := fun p : State => (p.2.1 0, p.1, p.2.2)) (by fun_prop)

private theorem continuous_dualTerm (n : ℕ) : Continuous
    (fun p : State => p.1.ifs.dualTerm (.inf p.2.1) n p.2.2) := by
  let R (p : State) : I := ⟨(p.1.val (p.2.1 0) p.2.2).re, (p.1.ifs.inClass _).re_mem_I _ p.2.2.2⟩
  let T (p : State) : State := (p.1, (fun k => p.2.1 (k + 1)), R p)
  have hR : Continuous R := (Complex.continuous_re.comp (continuous_onState (continuous_jet_eval · 0))).subtype_mk _
  have hT : Continuous T := by fun_prop
  induction n with
  | zero => simpa [IFS.dualTerm] using continuous_onState continuous_nonlin_eval
  | succ n ih =>
    have he (p : State) : (R p : ℂ) = p.1.val (p.2.1 0) p.2.2 :=
      (p.1.ifs.comp_ofReal [p.2.1 0] p.2.2.2).symm
    simpa only [Function.comp_apply, Pi.mul_def, T, he,
      IFS.dualTerm_inf_succ _ _ _ ((System.ifs _).real_mem_closed (Subtype.property _)), System.ifs]
      using (continuous_onState continuous_deriv_eval).mul (ih.comp hT)

/-- Joint continuity in the system and word, by a common summable majorant. -/
theorem continuous_dualProj (x : I) : Continuous
    (fun q : System N × (ℕ → Fin N) => q.1.ifs.dualProj (.inf q.2) x) :=
  continuous_iff_continuousAt.2 fun p => by
    let F := p.1
    obtain ⟨c, hc₀, hc₁⟩ := exists_between F.ifs.cmax_lt_one
    have hc : 0 ≤ c := F.ifs.cmax_nonneg.trans hc₀.le
    obtain ⟨M, -, hM⟩ := F.ifs.exists_nonlin_bound
    have hd := eventually_all.2 fun i : Fin N => eventually_norm_lt (continuous_deriv_eval i)
      (F := F) fun x => (F.ifs.norm_deriv_le_cmax i (F.ifs.real_mem_closed x.2)).trans_lt hc₀
    have hn := eventually_all.2 fun i : Fin N => eventually_norm_lt (continuous_nonlin_eval i)
      (F := F) (c := M + 1) fun x => (hM i _ (F.ifs.real_mem_closed x.2)).trans_lt (lt_add_one _)
    -- The same geometric majorant works throughout a neighbourhood of the system.
    refine tendsto_tsum_of_dominated_convergence ((summable_geometric_of_lt_one hc hc₁).mul_left (M + 1))
      (fun n => ((continuous_dualTerm n).comp
        (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))).continuousAt.tendsto) ?_
    filter_upwards [continuousAt_fst.tendsto.eventually hd,
      continuousAt_fst.tendsto.eventually hn] with q hd hn n
    let G := q.1
    suffices ∀ (w : ℕ → Fin N) (x : I), ‖G.ifs.dualTerm (.inf w) n x‖ ≤ (M + 1) * c ^ n from this q.2 x
    intro w x
    induction n generalizing w x with
    | zero => simpa [IFS.dualTerm] using (hn (w 0) x).le
    | succ n ih =>
      let y : I := ⟨G.ifs.realMaps (w 0) x, (G.ifs.inClass _).re_mem_I _ x.2⟩
      have hy : G.ifs.f (w 0) x = (y : ℂ) := G.ifs.comp_ofReal [w 0] x.2
      rw [IFS.dualTerm_inf_succ _ _ _ (G.ifs.real_mem_closed x.2), hy, norm_mul, pow_succ', mul_left_comm]
      exact mul_le_mul (hd (w 0) x).le (ih _ y) (norm_nonneg _) hc

end System
end AnalyticESC
