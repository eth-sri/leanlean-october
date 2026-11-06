module
public import Mathlib

public import FixedPointTheorems.brouwer
public import PottsDiscontinuity.Bethe.RatioAnySign
public import PottsDiscontinuity.SixVertex.Cor34FinalExistence

/-!
# Theorem 1.3 ratio limit at the critical six-vertex parameter

The assembly uses Theorem 2.3 to select the two symmetric Bethe families,
the Fourier eigenvalue-ratio limit for both parities (`Bethe/Ratio*`), and the
proved Corollary 3.4 analytic-family identifications.
-/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.RCMProof

open Bethe BetheAnsatz SixVertex

structure EndpointBetheState (N n r : ℕ) (Δ c : ℝ)
    (hΔ : Δ < -1) (K : ℝ) where
  hn : 0 < n
  hsize : 2 * n ≤ N
  roots : Fin n → ℝ
  roots_mem : roots ∈ Bethe.S_n n
  roots_bethe : Bethe.DiscreteBetheEquation Δ N n roots
  density_bound : Bethe.densityNorm Δ hΔ
      (fun x => Bethe.rootStepDensity N n roots roots_mem hn hsize x -
        Bethe.rho Δ x)
      (Bethe.rootStepDensity_error_bddAbove hΔ roots roots_mem hn hsize) ≤ K / N
  lambda_eq : SixVertex.cor34BetheLambda N n c roots = Lambda c N r

/-- Theorem 1.3, equation (1.7), along the tail of the subsequence `N ∈ 4ℕ`.
The finite-size Bethe/Perron-root identification uses the proved Corollary 3.4
endpoint-family theorem. -/
theorem apply_17_at_critical_c
    (q : ℝ) (hq : 4 < q) (r : ℕ) (hr : 1 ≤ r) :
    ∃ B : ℕ, ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial
        (Real.arcosh (Real.sqrt q / 2))) atTop
        (𝓝 S) ∧
      Tendsto (fun i : ℕ =>
        Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * (i + B)) r /
          Lambda (Real.sqrt (2 + Real.sqrt q)) (4 * (i + B)) 0)
        atTop (𝓝 (Real.exp (-(r : ℝ) *
          (Real.arcosh (Real.sqrt q / 2) + 2 * S)))) := by
  let Δcrit  := -Real.sqrt q / 2
  let c  := Real.sqrt (2 + Real.sqrt q)
  
  have hsqrtq : 2 < Real.sqrt q := by
    
    
    nlinarith [Real.sq_sqrt (by linarith), Real.sqrt_nonneg q]
  have hΔcrit : Δcrit < -1 := by
    dsimp [Δcrit]
    linarith
  
  
  
  have hlamEq : Bethe.lamOf Δcrit = Real.arcosh (Real.sqrt q / 2) := Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (congrArg Real.arcosh (id (Eq.symm (by
                                                                                                                                                          
                                                                                                                                                          ring))))))
  have hcΔ : BetheAnsatz.anisotropy c = Δcrit := by
    grind [BetheAnsatz.anisotropy]
  have hcPhysical : Real.sqrt (2 - 2 * Δcrit) = c := by
    grind

  obtain ⟨Kq, hKq, Nq, hNq, hEndpointQ⟩ :=
    SixVertex.cor34_final_exists_family_at_endpoint r hΔcrit
  obtain ⟨Kp, hKp, Np, hNp, hEndpointP⟩ :=
    SixVertex.cor34_final_exists_family_at_endpoint 0 hΔcrit
  let B  := max (max Nq Np) (r + 2)
  let N  := fun i => 4 * (i + B)
  have hB : 0 < B := by  omega
  have hBq : Nq ≤ B := by  omega
  have hBp : Np ≤ B := by  omega
  have hBr : r + 2 ≤ B := by  omega
  have hhalf (i : ℕ) : N i / 2 = 2 * (i + B) := by
    grind
  have hNpos (i : ℕ) : 0 < N i := by
    dsimp [N]
    omega
  have hNeven (i : ℕ) : Even (N i) := by
    grind
  
  
  have h4 (i : ℕ) : 4 ∣ N i := by
    grind
  have hNlim : Tendsto (fun i  => (N i : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro x
    
    filter_upwards [Filter.eventually_ge_atTop (Nat.ceil x)] with i hi
    
    
    
    exact (Nat.le_ceil x).trans (by exact_mod_cast  by
                                                      grind )
  have hrBound (i : ℕ) : r ≤ N i / 2 := by
    rw [hhalf]
    omega
  have hsizeQ (i : ℕ) : 2 * (N i / 2 - r) ≤ N i := by
    omega
  have hnQ (i : ℕ) : 0 < N i / 2 - r := by
    rw [hhalf]
    omega
  have hsizeP (i : ℕ) : 2 * (N i / 2) ≤ N i := by omega
  
  
  
  

  have hdataQ : ∀ i ,
      Nonempty (EndpointBetheState (N i) (N i / 2 - r) r Δcrit c hΔcrit Kq) := by
    intro i
    obtain ⟨hn, hs, p, hp, hBE, hDensity, hLambda⟩ :=
      hEndpointQ (N i) ( fun (i : ℕ) => by
                           grind  i) (hNeven i)
    let data : EndpointBetheState (N i) (N i / 2 - r) r Δcrit c hΔcrit Kq :=
      { hn := hn
        hsize := hs
        roots := p
        roots_mem := hp
        roots_bethe := hBE
        density_bound := hDensity
        lambda_eq := by simpa [hcPhysical] using hLambda }
    exact ⟨data⟩
  have hdataP : ∀ i ,
      Nonempty (EndpointBetheState (N i) (N i / 2) 0 Δcrit c hΔcrit Kp) := by
    intro i
    obtain ⟨hn, hs, p, hp, hBE, hDensity, hLambda⟩ :=
      hEndpointP (N i) ( fun (i : ℕ) => by
                           grind  i) (hNeven i)
    let data : EndpointBetheState (N i) (N i / 2) 0 Δcrit c hΔcrit Kp :=
      { hn := hn
        hsize := hs
        roots := p
        roots_mem := hp
        roots_bethe := hBE
        density_bound := hDensity
        lambda_eq := by simpa [hcPhysical] using hLambda }
    exact ⟨data⟩
  let Dq  :=
    fun i => Classical.choice (hdataQ i)
  let Dp  :=
    fun i => Classical.choice (hdataP i)
  let rootsQ  := fun i => (Dq i).roots
  let rootsP  := fun i => (Dp i).roots
  have hrootsQmem (i : ℕ)  :=
    (Dq i).roots_mem
  have hrootsPmem (i : ℕ)  :=
    (Dp i).roots_mem
  have hrootsQBE (i : ℕ)  := (Dq i).roots_bethe
  have hrootsPBE (i : ℕ)  := (Dp i).roots_bethe
  have hbp (i : ℕ)  :=
    Bethe.rootStepDensity_error_bddAbove hΔcrit (rootsP i) (hrootsPmem i)
      ( fun (i : ℕ) => by rw [hhalf]; omega  i) (hsizeP i)
  have hbq (i : ℕ)  :=
    Bethe.rootStepDensity_error_bddAbove hΔcrit (rootsQ i) (hrootsQmem i)
      (hnQ i) (hsizeQ i)
  have hnormP (i : ℕ)  :=
    (Dp i).density_bound
  have hnormQ (i : ℕ)  :=
    (Dq i).density_bound
  
  have hK : 0 ≤  max Kp Kq  := le_of_lt (lt_max_of_lt_left hKp)
  

  have hSdata : ∃ S : ℝ,
      Tendsto (PottsDiscontinuity.altTanhPartial
        (Bethe.lamOf Δcrit)) atTop (𝓝 S) ∧
      Tendsto (fun i  =>
        (if r % 2 = 0 then BetheAnsatz.eigenvalueRegular c (rootsQ i)
         else BetheAnsatz.eigenvalueZero (N i) c (rootsQ i)
           ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩) /
          BetheAnsatz.eigenvalueRegular c (rootsP i)) atTop
        (𝓝  (Real.exp (- r  *
          (Bethe.lamOf Δcrit + 2 * S)) ) ) := by
    by_cases hrEven : r % 2 = 0
    · obtain ⟨S, hS, hratio⟩ := Bethe.ratio_even_eigenvalue_limit_fourier_any_sign
        hΔcrit r N h4 hrBound hNpos hnQ rootsP rootsQ
        hrootsPmem hrootsQmem hrootsPBE hrootsQBE hNlim hbp hbq hK (by
                                                                      filter_upwards with i
                                                                      constructor
                                                                      · exact hnormP i |>.trans (div_le_div_of_nonneg_right
                                                                          (le_max_left Kp Kq) (by positivity))
                                                                      · exact hnormQ i |>.trans (div_le_div_of_nonneg_right
                                                                          (le_max_right Kp Kq) (by positivity)))
        hrEven hr hcΔ
      refine ⟨S, hS, ?_⟩
      simpa [hrEven] using hratio
    · obtain ⟨S, hS, hratio⟩ := Bethe.ratio_odd_eigenvalue_limit_fourier_any_sign
        hΔcrit r N h4 hrBound hNpos hnQ rootsP rootsQ
        hrootsPmem hrootsQmem hrootsPBE hrootsQBE hNlim hbp hbq hK (by
                                                                      filter_upwards with i
                                                                      constructor
                                                                      · exact hnormP i |>.trans (div_le_div_of_nonneg_right
                                                                          (le_max_left Kp Kq) (by positivity))
                                                                      · exact hnormQ i |>.trans (div_le_div_of_nonneg_right
                                                                          (le_max_right Kp Kq) (by positivity)))
        hrEven hr hcΔ
      refine ⟨S, hS, ?_⟩
      simpa [hrEven] using hratio
  obtain ⟨S, hS, hratio⟩ := hSdata
  
  obtain ⟨S₀, T₀, hS₀, hT₀, hpositive, hvalue⟩ :=  PottsDiscontinuity.identity44
                                                     (Real.arcosh (Real.sqrt q / 2)) (Real.arcosh_pos (by nlinarith )) 
  
  
  

  have hPFtop (i : ℕ) : BetheAnsatz.eigenvalueRegular c (rootsP i) =
        PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c (N i / 2))   := by
    have hparity : Even (N i / 2) := by
      grind
    
    have hratio := Bethe.ratio_eigenvalueRegular (by
                                                    change 2 < Real.sqrt (2 + Real.sqrt q)
                                                    rw [Real.lt_sqrt (by norm_num )]
                                                    nlinarith ) (hrootsPmem i)
    
    have hindex : Lambda c (N i) 0 =
        PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c (N i / 2)) := by
      unfold Lambda
      simp
    calc
      _ = ( SixVertex.cor34BetheLambda (N i) (N i / 2) c (rootsP i)  : ℂ) :=  by
                                                                                    simpa [SixVertex.cor34BetheLambda, hparity] using hratio 
      _ =   Lambda c (N i) 0   := congrArg (fun x : ℝ => (x : ℂ)) (Dp i).lambda_eq
      _ =   PerronFrobenius.pfRoot
          (SixVertex.transferBlock (N i) c (N i / 2))   := by rw [hindex]
  have hPFbottomEven (i : ℕ) (hrEven : r % 2 = 0) :
      BetheAnsatz.eigenvalueRegular c (rootsQ i) =
          PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c
          (N i / 2 - r))   := by
    have hparity : Even (N i / 2 - r) := by
      grind
    
    have hratio := Bethe.ratio_eigenvalueRegular (by
                                                    change 2 < Real.sqrt (2 + Real.sqrt q)
                                                    rw [Real.lt_sqrt (by norm_num )]
                                                    nlinarith ) (hrootsQmem i)
    
    
    calc
      _ = ( SixVertex.cor34BetheLambda (N i) (N i / 2 - r) c (rootsQ i)  : ℂ) :=  by
                                                                                        simpa [SixVertex.cor34BetheLambda, hparity] using hratio 
      _ =   Lambda c (N i) r   := congrArg (fun x : ℝ => (x : ℂ)) (Dq i).lambda_eq
      _ =   PerronFrobenius.pfRoot
          (SixVertex.transferBlock (N i) c (N i / 2 - r))   := by rw [(by
                                                                           
                                                                           rfl : Lambda c (N i) r =
        PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c
          (N i / 2 - r)))]
  have hPFbottomOdd (i : ℕ) (hrOdd : r % 2 ≠ 0) :
      BetheAnsatz.eigenvalueZero (N i) c (rootsQ i)
        ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩ =
          PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c
          (N i / 2 - r))   := by
    have hparity : ¬ Even (N i / 2 - r) := by
      grind
    let qcenter  := (N i / 2 - r) / 2 + 1
    have hnq : N i / 2 - r + 1 = 2 * qcenter := by
      grind
    have hindex : qcenter - 1 = (N i / 2 - r) / 2 := by
      dsimp [qcenter]
    let l : Fin (N i / 2 - r) :=
      ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩
    have hcenter : rootsQ i l = 0 := by
      simpa [hindex] using
         cor34_odd_S_n_center_zero (hrootsQmem i) hnq 
    have hc : 2 < c := by
      
      rw [Real.lt_sqrt (by norm_num )]
      nlinarith [hsqrtq]
    have hratio := Bethe.ratio_eigenvalueZero (N := N i) hc (hrootsQmem i) l hcenter
    
    
    calc
      _ = ( SixVertex.cor34BetheLambda (N i) (N i / 2 - r) c (rootsQ i)  : ℂ) :=  by
                                                                                        simpa [SixVertex.cor34BetheLambda, hparity] using hratio 
      _ =   Lambda c (N i) r   := congrArg (fun x : ℝ => (x : ℂ)) (Dq i).lambda_eq
      _ =   PerronFrobenius.pfRoot
          (SixVertex.transferBlock (N i) c (N i / 2 - r))   := by rw [(by
                                                                           
                                                                           rfl : Lambda c (N i) r =
        PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c
          (N i / 2 - r)))]
  have hPFnum (i : ℕ) :
      (if r % 2 = 0 then BetheAnsatz.eigenvalueRegular c (rootsQ i)
       else BetheAnsatz.eigenvalueZero (N i) c (rootsQ i)
         ⟨(N i / 2 - r) / 2, Nat.div_lt_self (hnQ i) (by omega)⟩) =
          PerronFrobenius.pfRoot (SixVertex.transferBlock (N i) c
          (N i / 2 - r))   := by
    grind
  
  have hcomplex : Tendsto (fun i  =>
      ((Lambda c (N i) r / Lambda c (N i) 0 : ℝ) : ℂ)) atTop
      (𝓝  (Real.exp (- r  *
        (Bethe.lamOf Δcrit + 2 * S₀)) ) ) := by
    have htarget : Tendsto (fun i  =>
        ( Lambda c (N i) r / Lambda c (N i) 0  : ℂ)) atTop
        (𝓝  (Real.exp (- r  *
          (Bethe.lamOf Δcrit + 2 * S)) ) ) := Tendsto.congr  fun i => by
                                                                      rw [hPFnum i, hPFtop i]
                                                                      
                                                                      
                                                                      rfl  hratio
    simpa [ tendsto_nhds_unique (by
                                   simpa [hlamEq] using hS : Tendsto (PottsDiscontinuity.altTanhPartial
      (Real.arcosh (Real.sqrt q / 2)))
      atTop (𝓝 S))  hS₀  ] using htarget
  
  have hrealComplex : Tendsto (fun i  =>
      Complex.re  ↑(Lambda c (N i) r / Lambda c (N i) 0 ) ) atTop
      (𝓝 (Real.exp (- r  * (Bethe.lamOf Δcrit + 2 * S₀)))) := by
    have ht := Complex.continuous_re.continuousAt.tendsto.comp (by
                                                                  simpa only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
                                                                    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat] using hcomplex)
    
    have hexp : (Complex.exp (- r  *
        ( Bethe.lamOf Δcrit  + 2 *  S₀ ))).re =
        Real.exp (- r  * (Bethe.lamOf Δcrit + 2 * S₀)) := by
      simp [Complex.exp_re]
    rw [hexp] at ht
    exact ht
  have hRe : (fun i  =>
      Complex.re  ↑(Lambda c (N i) r / Lambda c (N i) 0 ) ) =
       fun i  => Lambda c (N i) r / Lambda c (N i) 0  := by
    
    simp
  rw [hRe] at hrealComplex
  
  
  refine ⟨B, S₀, ?_, ?_⟩
  · assumption
  · grind

end PottsDiscontinuity.RCMProof
