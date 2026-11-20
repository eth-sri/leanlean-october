module
public import AnalyticESC.Generic.Distance
public import AnalyticESC.Dual.Recursion

@[expose] public section
namespace AnalyticESC.IFS
open Set Filter Topology Metric
variable {N : ℕ} (Φ : IFS N)

@[fun_prop] lemma continuous_jet {X : Type*} [TopologicalSpace X] {A : X → IFS N} {i : X → Fin N}
    (ha : Continuous A) (hi : Continuous i) (k : Fin 3) : Continuous (fun x => (A x).jet (i x) k) := by
  apply Continuous.comp (g := fun p : Fin N × X => (A p.2).jet p.1 k) _ (hi.prodMk continuous_id)
  apply continuous_prod_of_discrete_left.mpr; intro j
  exact (PiLp.continuous_apply 1 _ k).comp ((continuous_apply j).comp ((PseudoMetricSpace.isometry_induced (@code N)).continuous.comp ha))

abbrev Phase (N : ℕ) := Address N × I

noncomputable def model : C(Phase N,ℂ) where
  toFun p := Φ.P p.1 p.2
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr; rintro ⟨w,x⟩
    exact Φ.proj_limit (L := fun _ => ⊤) (continuous_fst.tendsto (w,x)) tendsto_const_nhds (Φ.real_mem x.2)
      (show Continuous (fun p : Phase N => (p.2:ℂ)) by fun_prop).continuousAt.tendsto 0

private noncomputable def action (F : C(Phase N,ℂ)) (q : IFS N × Phase N) :=
  let i := q.2.1 0; let x := q.2.2
  q.1.nonlin i x + deriv (q.1.f i) x * F (shift 1 q.2.1,q.1.next i x)

private lemma cont_action (F : C(Phase N,ℂ)) : Continuous (action F : IFS N × Phase N → ℂ) := by
  have J (k : Fin 3) : Continuous fun q : IFS N × Phase N => q.1.jet (q.2.1 0) k q.2.2 := by fun_prop
  have next : Continuous (fun q : IFS N × Phase N => q.1.next (q.2.1 0) q.2.2) := (Complex.continuous_re.comp (J 0)).subtype_mk _
  exact ((J 2).div (J 1) (fun q => (q.1.inClass _).deriv_ne_zero _ (q.1.closedReal q.2.2.2))).add ((J 1).mul (F.continuous.comp ((by unfold shift; fun_prop : Continuous fun q : IFS N × Phase N => shift 1 q.2.1).prodMk next)))

private noncomputable def transport (F : C(Phase N,ℂ)) := (⟨action F,cont_action F⟩ : C(IFS N × Phase N,ℂ)).curry
private noncomputable abbrev op (F : C(Phase N,ℂ)) := transport F Φ

private lemma fixed : Function.IsFixedPt Φ.op Φ.model := ContinuousMap.ext fun p => (Φ.head_rec p.1 p.2.2).symm

private noncomputable abbrev gain (A : IFS N) := ‖fun i => A.jet i 1‖₊

private lemma contracts : ContractingWith (gain Φ) Φ.op := by
  have H : gain Φ ≤ Φ.cmax := (pi_norm_le_iff_of_nonneg Φ.cmax_nonneg).mpr fun i =>
    (ContinuousMap.norm_le _ Φ.cmax_nonneg).mpr fun x => Φ.norm_deriv_le_cmax i (Φ.closedReal x.2)
  refine ⟨H.trans_lt Φ.cmax_lt_one,LipschitzWith.of_dist_le_mul fun F G => (ContinuousMap.dist_le (by positivity)).mpr fun p => ?_⟩
  change dist (Φ.nonlin _ _ + _ * F _) (_ + _ * G _) ≤ _
  rw [dist_add_left,dist_eq_norm,← mul_sub,norm_mul]
  gcongr
  · exact eval_le (fun i => Φ.jet i 1) _ _
  · rw [← dist_eq_norm]; exact ContinuousMap.dist_apply_le_dist _

@[fun_prop] lemma continuous_model : Continuous (@model N) := by
  apply continuous_iff_continuousAt.mpr; intro A
  have h := (transport A.model).continuous
  have cg : Continuous fun Ψ : IFS N => (gain Ψ : ℝ) := (continuous_pi fun i => continuous_jet continuous_id continuous_const 1).norm
  rw [ContinuousAt,Metric.tendsto_nhds] -- alternatively squeeze in the distance
  intro ε hε
  have ub := ((continuous_const (y := A.model)).dist h).continuousAt.tendsto.div (continuous_const.sub cg).continuousAt.tendsto A.contracts.one_sub_K_pos.ne'
  have ev := ub.eventually_lt_const (show dist A.model (A.op A.model) / (1-gain A) < ε by rw [A.fixed.eq]; simpa)
  filter_upwards [ev] with Ψ hΨ
  rw [dist_comm]; exact (Ψ.contracts.dist_le_of_fixedPoint A.model Ψ.fixed).trans_lt hΨ

def Good (i j : Fin N) : Set (IFS N) := {A | ¬ ∃ p : Address N × Address N,
  p.1 0 = i ∧ p.2 0 = j ∧ ∀ x : I, A.P p.1 x = A.P p.2 x}

lemma closed_exists {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y] {P : X → Y → Prop}
    (h : IsClosed {p : X × Y | P p.1 p.2}) : IsClosed {x | ∃ y, P x y} := by
  convert isClosedMap_fst_of_compactSpace _ h using 1; ext; simp

lemma good_open (i j : Fin N) : IsOpen (Good i j) := by
  refine (closed_exists ?_).isOpen_compl
  simp only [ofPred_and, ofPred_forall]
  refine (isClosed_eq (by fun_prop) continuous_const).inter ((isClosed_eq (by fun_prop) continuous_const).inter (isClosed_iInter fun x => ?_))
  change IsClosed {p : IFS N × Address N × Address N | p.1.model (p.2.1,x) = p.1.model (p.2.2,x)}
  exact isClosed_eq (by fun_prop) (by fun_prop)

end AnalyticESC.IFS
