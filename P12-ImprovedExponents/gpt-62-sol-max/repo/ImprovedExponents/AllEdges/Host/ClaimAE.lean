module

public import ImprovedExponents.AllEdges.Host.ProgramAE
public import ImprovedExponents.AllEdges.Model
public import ImprovedExponents.Pipeline.Claims
public import ImprovedExponents.ParamRoutines.Rat
public import ThreeSumApsp.Programs.Sec3.Theorem17.TimeBound.Total

@[expose] public section

/-! The all-edges host charges the solver at the true size of the middle part.
The remaining costs are bounded by the shared preparation, matrix construction, and scan bounds,
plus the cost of reading answers and maintaining the flags. -/

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec ParamRoutines

/-- Under the hypotheses of Theorem 17 the host does not fall back on the brute force. -/
private theorem not_smallCase_of_hyp {n D g : ℕ} (h16 : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g)
    (hg : (g : ℝ) ≤ Real.sqrt D) : ¬ SmallCase n D g := by
  have hgD : g ≤ Nat.sqrt D := by
    rw [Nat.le_sqrt']
    exact_mod_cast (Real.le_sqrt g.cast_nonneg D.cast_nonneg).1 hg
  unfold SmallCase
  omega

/-- The costs other than the calls to the solver: `ng · n²/√D` for reading answers,
plus the three terms of the bound of Theorem 17. -/
private noncomputable def restBoundAE (θ : CostParams) : ℝ :=
  (θ.n : ℝ) * θ.g * ((θ.n : ℝ) ^ 2 / Real.sqrt θ.D) + budget θ

/-- What is within the three terms is within `restBoundAE`. -/
private theorem _root_.Light.Sec3.Steps.toRestAE {t : CostParams → ℕ}
    (h : Steps t budget) : Steps t restBoundAE :=
  h.mono_right fun θ _ => le_add_of_nonneg_left (by positivity)

/-- A piece has `⌈s/g⌉ ≤ s` vertices. -/
private theorem steps_pieceSizeNatAE : StepsMon (fun θ => pieceSizeNat θ.D θ.g) 0 1 0 :=
  steps_sqrt.of_le fun θ _ => pieceSizeNat_le_sqrt θ.D θ.g

/-- The `n²` scans that set flags take `O(√D/g) · n² ≤ O(n² √D)` steps. -/
private theorem steps_scansAE :
    StepsMon (fun θ => tScanCallAE (pieceSizeNat θ.D θ.g) * (θ.n * θ.n)) 2 1 0 := by
  unfold tScanCallAE tScan
  growth [steps_n, steps_pieceSizeNatAE]

/-- Filling the `n²` flags. -/
private theorem steps_fillAE : StepsMon (fun θ => fillTime (θ.n * θ.n)) 2 0 0 := by
  unfold fillTime
  growth [steps_n]

/-- Copying the `n²` flags to the output. -/
private theorem steps_copyAE : StepsMon (fun θ => copyTime (θ.n * θ.n)) 2 0 0 := by
  unfold copyTime
  growth [steps_n]

private theorem steps_failedScansAE :
    Steps (fun θ => tScanCallAE (pieceSizeNat θ.D θ.g) * falsePositiveBound θ.n θ.U θ.D)
      budget := by
  simpa only [tScanCallAE, tScan, Nat.add_assoc] using steps_failedScans 24 65

@[simp] private theorem supTime_zero (n D cap : ℕ) : supTime (fun _ => 0) n D cap = 0 := by
  exact Finset.sup_bot _

private noncomputable def hostRestAE (tD tG : ℕ → ℕ) (θ : CostParams) : ℕ :=
  hostSetup tD tG θ.n θ.D + hostMainAE (fun _ => 0) θ.n θ.U θ.D θ.g
    + copyTime (θ.n * θ.n) + 20

private theorem steps_hostRestAE {tD tG : ℕ → ℕ} (hD : Steps (fun θ => tD θ.n) budget)
    (hG : Steps (fun θ => tG θ.D) budget) : Steps (hostRestAE tD tG) restBoundAE := by
  have read := (steps_instances.mul (steps_queryRead 68 6)).mono_right fun θ hθ =>
    le_add_of_nonneg_right (budget_nonneg hθ)
  refine ((steps_hostPreparation hD hG).toRestAE.add steps_instances_mul_tWrites.toRestAE
    |>.add read |>.add steps_failedScansAE.toRestAE |>.add steps_scansAE.withinBuild.toRestAE
    |>.add steps_fillAE.withinBuild.toRestAE |>.add steps_copyAE.withinBuild.toRestAE
    |>.add (Scale.SoftO.const 360).withinBuild.toRestAE).mono_left fun θ _ => le_of_eq ?_
  simp only [hostRestAE, hostMainAE, hostLoopBoundAE, hostPreparation, supTime_zero,
    tAnswersAE, Nat.add_zero]
  ring

/-- A bound `T` on the time of the solver that is monotone in the number of query pairs bounds its
largest time on the instances of the host. -/
private theorem cast_supTime_le {Tn : List ℕ → ℕ} {T : ℕ → ℕ → ℕ → ℝ}
    (hT : ∀ n D w w' : ℕ, 1 ≤ n → 1 ≤ D → w ≤ w' → (Tn [n, D, w] : ℝ) ≤ T n D w') {n D : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D) (cap : ℕ) : ((supTime Tn n D cap : ℕ) : ℝ) ≤ T n D cap := by
  obtain ⟨w, hw, hsup⟩ : ∃ w ∈ Finset.range (cap + 1),
      (Finset.range (cap + 1)).sup (fun w => Tn [n, D, w]) = Tn [n, D, w] :=
    Finset.exists_mem_eq_sup _ ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ _
  rw [supTime, hsup]
  simp_all

theorem obeysBound17Mid_hostTimeAE (D g : ℕ → ℕ) {Dfun Gfun tD tG : ℕ → ℕ}
    (hDf : ∀ n, Dfun n = D n) (hGf : ∀ n, 1 ≤ n → Gfun (D n) = g n)
    (hD : Steps (fun θ => tD θ.n) budget) (hG : Steps (fun θ => tG θ.D) budget) :
    ObeysBound17Mid strassen D g (hostTimeAE Dfun Gfun tD tG) := by
  obtain ⟨C, hC, hrest⟩ := steps_hostRestAE hD hG
  refine ⟨C, hC, fun Tn T hT n U κ h16 hDn hg1 hg hκ hU => ?_⟩
  let θ : CostParams := ⟨n, D n, g n, U, κ⟩
  have hθ : θ.Hyp := ⟨h16, hDn, hg1, hg, hκ, hU⟩
  have hsplit : hostTimeAE Dfun Gfun tD tG Tn n U =
      4 * n * g n * supTime Tn n (midSize (D n) (g n)) (queryCapNat n (D n))
        + hostRestAE tD tG θ := by
    simp [hostTimeAE, hostCoreTime, hDf n, hGf n hθ.one_le_n_nat,
      not_smallCase_of_hyp h16 hDn hg1 hg, hostRestAE, hostMainAE, hostLoopBoundAE, θ]
    ring
  have hsolver := cast_supTime_le hT hθ.one_le_n_nat (one_le_midSize h16 hg1) (queryCapNat n (D n))
  have hp := hrest θ hθ
  have hquery : 0 ≤ C * ((n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n))) := by positivity
  rw [hsplit, queryCapNat_eq n hθ.one_le_D_nat] at ⊢
  rw [queryCapNat_eq n hθ.one_le_D_nat] at hsolver
  push_cast
  have hc := mul_le_mul_of_nonneg_left hsolver (by positivity : 0 ≤ 4 * (n : ℝ) * g n)
  simp only [restBoundAE, budget, θ, hostCharge] at hp ⊢
  linarith

/-! ## The claim -/

theorem claim17MidAE_of_pack {D g : ℕ → ℕ} (pk : ParamPack D g) :
    HostBound lightModelAE strassen D g (fun n => midSize (D n) (g n)) := by
  refine claim17MidAE_of_host strassen D g _ (hostNeedAE pk.Dfun pk.Gfun pk.wD pk.wG) ?_
    (obeysBound17Mid_hostTimeAE D g pk.D_eq pk.G_eq pk.stepsD_budget pk.stepsG_budget)
  intro Q pS Tn r hr hs
  have h := ae17_solves (P₀ := Q ++ pk.procs Q.length) (hs.append _) (pk.procD Q) (pk.procG Q) pk.D_pos
  rw [List.append_assoc] at h
  exact ⟨_, _, h, hostNeed_poly pk.polyD pk.polyG pk.polyWD pk.polyWG hr⟩

/-- **`lightModelAE` has the host of Theorem 17 at the true size of the middle part**, at all
rational exponents `D(n) = ⌊n^{a/b}⌋`, `g = ⌈D^{c/d}⌉`, as `lightModel` does
(`ImprovedExponents.midHostRat_light`). -/
theorem midHostRat_ae : MidHostRat lightModelAE := fun a b c d hb hd hab hcd =>
  claim17MidAE_of_pack (paramPackRat a b c d hb hd hab hcd)

end ImprovedExponents.AllEdges
