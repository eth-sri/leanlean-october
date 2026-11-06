module

public import OAI.NumberTheory.DirichletL.Reflection.Independent

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical MatrixGroups
open CubicEisenstein ShortDraftCRT CompletedGauss
noncomputable section

theorem simultaneous_controlled_matrices_dependent {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → ActualEisensteinCubic.O) (N a c : ActualEisensteinCubic.O) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (hc : c ≠ 0) (h9N : (9:ActualEisensteinCubic.O) ∣ N) (hcN : c ∣ N)
    (hprimary : ∀ x, ConcretePrimeRowBridge.goodLambda^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2 ∣ a-1 else ConcretePrimeRowBridge.goodLambda^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i)) :
    ∃ mat : ∀ x, (∀ i, (ActualEisensteinCubic.O ⧸ Ideal.span {p x i})ˣ) → SL(2,ActualEisensteinCubic.O),
      (∀ x v, mat x v 0 0 = (D x).matrix v 0 0) ∧
      (∀ x v, mat x v 1 0 = c*∏ i, p x i) ∧
      (∀ x v, if mode then (9:ActualEisensteinCubic.O) ∣ mat x v 0 1 ∧ (3:ActualEisensteinCubic.O) ∣ mat x v 1 1-1
        else (3:ActualEisensteinCubic.O) ∣ mat x v 0 1+1 ∧ (9:ActualEisensteinCubic.O) ∣ mat x v 1 1) ∧
      ∀ x y v w, sector x = sector y → ∀ i j, N ∣ mat x v i j-mat y w i j := by
  let X := Σ x : α, (∀ i, (ActualEisensteinCubic.O ⧸ Ideal.span {p x i})ˣ)
  let aa : X → ActualEisensteinCubic.O := fun x => (D x.1).matrix x.2 0 0
  let rr : X → ActualEisensteinCubic.O := fun x => ∏ i, p x.1 i
  let ss : X → Q := fun x => sector x.1
  have h3N := (show (3:ActualEisensteinCubic.O) ∣ 9 from ⟨3,by norm_num⟩).trans h9N
  have hacop (x : X) : IsCoprime (aa x) (c*rr x) := by
    refine ⟨(D x.1).matrix x.2 1 1, -(D x.1).matrix x.2 0 1, ?_⟩
    have hd := ((D x.1).matrix x.2).property
    rw [Matrix.det_fin_two] at hd
    change (D x.1).matrix x.2 0 0 * (D x.1).matrix x.2 1 1 -
      (D x.1).matrix x.2 0 1 * (D x.1).matrix x.2 1 0 = 1 at hd
    rw [(D x.1).denominator] at hd
    dsimp [aa,rr]
    linear_combination hd
  have haa (x y : X) (h : ss x = ss y) : N*c ∣ aa x-aa y := by
    dsimp [aa]
    rw [(D x.1).numerator,(D y.1).numerator]
    exact finiteCrossNumerator_fixed_sector N a c ramifiedTraceLambda
      (p x.1) ((D x.1).lift x.2) (p y.1) ((D y.1).lift y.2)
      hcN ((D x.1).lift_period x.2) ((D y.1).lift_period y.2) (by grind)
  have hrr (x y : X) (h : ss x = ss y) : N ∣ rr x-rr y :=
    (dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x.1 y.1 h)
  have hex : ∃ (b d : X → ActualEisensteinCubic.O) (C : Q → Matrix (Fin 2) (Fin 2) (ActualEisensteinCubic.O ⧸ Ideal.span {N})),
      (∀ x, aa x*d x-b x*(c*rr x)=1) ∧
      (∀ x, if mode then (9:ActualEisensteinCubic.O) ∣ b x ∧ (3:ActualEisensteinCubic.O) ∣ d x-1
        else (3:ActualEisensteinCubic.O) ∣ b x+1 ∧ (9:ActualEisensteinCubic.O) ∣ d x) ∧
      ∀ x, (!![aa x,b x;c*rr x,d x] : Matrix (Fin 2) (Fin 2) ActualEisensteinCubic.O).map
        (Ideal.Quotient.mk (Ideal.span {N})) = C (ss x) := by
    cases mode
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩ := exists_primary_denominator_sector_completions
        N c h9N hbase ss aa rr (fun x => hprimary x.1) hacop
        (by grind) haa hrr
      exact ⟨b,d,C,hd,by grind,hm⟩
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩ := exists_primary_numerator_sector_completions
        N c hc h9N ss aa rr
        (fun x => (D x.1).numerator_primary h3N (hprimary x.1) hbase x.2)
        (fun x => hprimary x.1) hacop (by grind) haa hrr
      exact ⟨b,d,C,hd,by grind,hm⟩
  obtain ⟨b,d,C,hdet,hcond,hmat⟩ := hex
  let mat := fun (x : α) (v : ∀ i, (ActualEisensteinCubic.O ⧸ Ideal.span {p x i})ˣ) =>
    controlledCompletionMatrix (aa ⟨x,v⟩) (b ⟨x,v⟩) (c*rr ⟨x,v⟩) (d ⟨x,v⟩) (by grind)
  refine ⟨mat,fun _ _ => rfl,fun _ _ => rfl,fun x v => hcond ⟨x,v⟩,?_⟩
  intro x y v w hs i j
  have hs' : ss ⟨x,v⟩ = ss ⟨y,w⟩ := hs
  have he := (hmat ⟨x,v⟩).trans ((congrArg C hs').trans (hmat ⟨y,w⟩).symm)
  have he' := congrArg (fun T : Matrix (Fin 2) (Fin 2) (ActualEisensteinCubic.O ⧸ Ideal.span {N}) => T i j) he
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he')

theorem exists_sector_controlled_arithmetic_dependent {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → ActualEisensteinCubic.O) (N a c : ActualEisensteinCubic.O) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (hc : c ≠ 0) (h9N : (9:ActualEisensteinCubic.O) ∣ N) (hcN : c ∣ N)
    (hprimary : ∀ x, ConcretePrimeRowBridge.goodLambda^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2 ∣ a-1 else ConcretePrimeRowBridge.goodLambda^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i)) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧
      (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧
      (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∀ x y v w, sector x = sector y → ∀ i j,
        N ∣ (E x).matrix v i j-(E y).matrix w i j := by
  obtain ⟨mat,ha,hr,hcond,hfixed⟩ := simultaneous_controlled_matrices_dependent
    p N a c mode D hc h9N hcN hprimary hbase hcop sector hsector
  let E : ∀ x, ControlledStratumArithmetic (p x) N a c mode := fun x =>
    { D x with
      matrix := mat x
      numerator := fun v => (ha x v).trans ((D x).numerator v)
      denominator := hr x
      matrix_fixed := by grind
      conditions := hcond x }
  exact ⟨E,by grind,by grind,by grind,by grind,hfixed⟩

theorem exists_sector_templates {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → ActualEisensteinCubic.O) (N a c : ActualEisensteinCubic.O) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:ActualEisensteinCubic.O)*c ∣ N)
    (hprimary : ∀ x, ConcretePrimeRowBridge.goodLambda^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2 ∣ a-1 else ConcretePrimeRowBridge.goodLambda^2 ∣ c-1)
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i))
    (hmatrix : ∀ x y, sector x = sector y → ∀ i j,
      N ∣ (D x).matrix (fun _ => 1) i j-(D y).matrix (fun _ => 1) i j) :
    ∃ (κ : Q → ℂ) (β : Q → ActualEisensteinCubic.Oˣ → ℕ → Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ),
      (∀ x, (D x).fixedFactor = κ (sector x)) ∧
      ∀ x u m n b,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c hc
            (Ideal.Quotient.mk _ (-((D x).matrix (fun _ => 1) 1 1)*(D x).U))
            (s.modelDualNumerator u) u) m n b = β (sector x) u m n b := by
  have hbad : ramifiedTraceLambda^3*c ∣ N := by
    apply (show ramifiedTraceLambda^3*c ∣ (9:ActualEisensteinCubic.O)*c from ?_).trans hN
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [← A4_traceLambda_pow_four]
    ring
  let A := fun x (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : Ideal ActualEisensteinCubic.O) =>
    fixedCuspArrayWithPhase s.index u
      (s.reflectionStaticPhase c hc
        (Ideal.Quotient.mk _ (-((D x).matrix (fun _ => 1) 1 1)*(D x).U))
        (s.modelDualNumerator u) u) m n b
  have hf : (fun x => (D x).fixedFactor).FactorsThrough sector := by
    intro x y hxy
    exact controlled_fixedFactor_eq (D x) (D y) hN (hprimary x) (hprimary y) hbase
      (by grind) (by grind)
  have ha : A.FactorsThrough sector := by
    intro x y hxy
    funext u m n b
    exact controlled_static_array_eq (D x) (D y) hc s hbad
      ((dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x y hxy))
      (by grind) u m n b
  obtain ⟨κ,hκ⟩ := (Function.factorsThrough_iff _).mp hf
  obtain ⟨β,hβ⟩ := (Function.factorsThrough_iff A).mp ha
  refine ⟨κ,β,fun x => congrFun hκ x,?_⟩
  intro x u m n b
  exact congrFun (congrFun (congrFun (congrFun (congrFun hβ x) u) m) n) b

theorem exists_separate_ray_templates {α : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → ActualEisensteinCubic.O) (N a c : ActualEisensteinCubic.O) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:ActualEisensteinCubic.O)*c ∣ N)
    (hprimary : ∀ x, ConcretePrimeRowBridge.goodLambda^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2 ∣ a-1 else ConcretePrimeRowBridge.goodLambda^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (f : ActualEisensteinCubic.O) (r P : α → ActualEisensteinCubic.O) (hprod : ∀ x, (∏ i, p x i) = f*r x*P x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧
      (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧
      (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∃ (κ : ((ActualEisensteinCubic.O ⧸ Ideal.span {N^2}) × (ActualEisensteinCubic.O ⧸ Ideal.span {N^2})) → ℂ)
        (β : ((ActualEisensteinCubic.O ⧸ Ideal.span {N^2}) × (ActualEisensteinCubic.O ⧸ Ideal.span {N^2})) →
          ActualEisensteinCubic.Oˣ → ℕ → Ideal ActualEisensteinCubic.O → Ideal ActualEisensteinCubic.O → ℂ),
        (∀ x, (E x).fixedFactor = κ (separateSector N (r x) (P x))) ∧
        ∀ x u m n b,
          fixedCuspArrayWithPhase s.index u
            (s.reflectionStaticPhase c hc
              (Ideal.Quotient.mk _ (-((E x).matrix (fun _ => 1) 1 1)*(E x).U))
              (s.modelDualNumerator u) u) m n b = β (separateSector N (r x) (P x)) u m n b := by
  let sector := fun x => separateSector N (r x) (P x)
  have hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i) := by
    intro x y hxy
    rw [hprod x,hprod y]
    exact separateSector_product N f (r x) (r y) (P x) (P y) hxy
  obtain ⟨E,hlift,hU,hσ,hε,hmat⟩ := exists_sector_controlled_arithmetic_dependent p N a c mode D
    hc ((dvd_mul_right 9 c).trans hN) ((dvd_mul_left c 9).trans hN)
    hprimary hbase hcop sector hsector
  refine ⟨E,hlift,hU,hσ,hε,?_⟩
  exact exists_sector_templates p N a c mode E s hc hN hprimary hbase sector hsector
    (fun x y hxy => hmat x y (fun _ => 1) (fun _ => 1) hxy)

end
end SevenEighths.InverseReflectedPhase

end OAI
