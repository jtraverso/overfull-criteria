module

public import OverfullWork.DirectedSeparatedRegularity
public import OverfullWork.OsthusStadenPureQuotientBudgets
public import OverfullWork.OsthusStadenReducedRoundDegree
public import OverfullWork.RobustReducedFactorization

@[expose] public section


/-! Construct the reduced factors of Osthus–Staden §5.1 on a pure
partition of the original regular robust digraph. -/
namespace OverfullWork.DirectedClusterQuotient

open Finset DirectedRobustExpansion DirectedRegularPairs DirectedPairEnergy
open scoped Classical
universe u

set_option maxHeartbeats 1000000 in
/-- The partition and both reduced graphs come from the same graph.
The factors consume distinct copies of the rounded sparse reduced
graph, and all balancing copies lie on its dense support. -/
theorem exists_osthus_staden_reduced_factors_with_budgets
    (ν τ α θ ε ζ d dense μ β γ tol : ℝ) (kMin : ℕ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1) (hτ : 0 < τ) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hθ : 0 < θ) (hθSmall : θ ≤ 1/16) (hθν : θ ≤ ν/48) (hθα : θ ≤ α/24)
    (hε : 0 < ε) (hε₁ : ε ≤ 1/2) (hζ : 0 < ζ) (hζθ : ζ ≤ θ) (hd : 0 ≤ d)
    (hCutν : d+ε+2*θ ≤ ν/2) (hCutα : d+ε ≤ α/2)
    (hMargin : 2*ζ+3*ε < θ^4/2)
    (hμ : 0 < μ) (hμν : μ ≤ ν/2) (hμτ : μ ≤ 2*τ) (hτα : 16*τ ≤ α)
    (hDense : 0 < dense) (hDenseMargin : 8*(μ+dense) ≤ ν^2)
    (hβ : 0 < β) (hβDense : β ≤ dense/2)
    (hγ : 0 < γ) (hγα : γ ≤ α) (hγDense : 12*γ ≤ dense*μ^2)
    (hTol : 0 ≤ tol) (hTol₁ : tol ≤ 1) (hTolμ : 16*tol ≤ μ)
    (hLoss : 2*(d+ε+6*θ)+β ≤ tol*γ/2)
    (hDenseDegree : 2*(d+ε+6*θ)+dense ≤ α/2)
    (hMin : 1 ≤ kMin) (hOrder : 8 ≤ (α/2)*(kMin:ℝ)) :
    ∃ N K : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V) (r : ℕ) (a : ℝ),
      N ≤ Fintype.card V → α ≤ a → a ≤ 1 → (r:ℝ) = a*(Fintype.card V:ℝ) →
      IsRealRobust G ν τ → (∀ v, inDegree G v = r ∧ outDegree G v = r) →
      ∃ (I : Type u) (inst : Fintype I),
        letI := inst
        ∃ (f : V → Option I) (H : Digraph V) (m : ℕ),
          0 < m ∧ (∀ i, (cluster f i).card = m) ∧ kMin ≤ Fintype.card I ∧
          Fintype.card I ≤ K ∧ ((exceptional f).card:ℝ) ≤ 4*θ*(Fintype.card V:ℝ) ∧ H ≤ G ∧
          (∀ i, ¬ (quotient H f).Adj i i) ∧
          (∀ i j, (quotient H f).Adj i j →
            IsUniform H (2*ε) (cluster f i) (cluster f j) ∧
              d-ε ≤ density H (cluster f i) (cluster f j)) ∧
          IsRealRobust (denseReduced H f dense) μ (2*τ) ∧
          (∀ i, (α/2)*(Fintype.card I:ℝ) ≤ (inDegree (denseReduced H f dense) i:ℝ)) ∧
          (∀ i, (α/2)*(Fintype.card I:ℝ) ≤ (outDegree (denseReduced H f dense) i:ℝ)) ∧
          let den := fun i j => density H (cluster f i) (cluster f j)
          let M := reducedMultiplicity (quotient H f) den β
          let C := reducedMultiplicity (denseReduced H f dense) den β
          let k := ⌊(a-γ)*(Fintype.card I:ℝ)/β⌋₊
          (∀ i, (a-2*(d+ε+6*θ)-β)*(Fintype.card I:ℝ) ≤ β*(↑(∑ j,M i j):ℝ) ∧
            β*(↑(∑ j,M i j):ℝ) ≤ (a+8*θ)*(Fintype.card I:ℝ)) ∧
          (∀ j, (a-2*(d+ε+6*θ)-β)*(Fintype.card I:ℝ) ≤ β*(↑(∑ i,M i j):ℝ) ∧
            β*(↑(∑ i,M i j):ℝ) ≤ (a+8*θ)*(Fintype.card I:ℝ)) ∧
          ∃ W : I → I → ℕ, (∀ i j, W i j ≤ C i j) ∧
            ∃ F : Fin k → Equiv.Perm I, ∀ i j,
              W i j + ((univ : Finset (Fin k)).filter (fun t => F t i = j)).card = M i j := by
  have hCutν' : d+ε ≤ ν/2 := by linarith only [hCutν,hθ]
  obtain ⟨N,K,hSetup⟩ := exists_robust_directed_pure_partition_separate_density.{u}
    ν τ α θ ε ζ d kMin hν hτ hα hθ hθSmall hθν hθα hε hε₁ hζ hζθ hd hCutν' hCutα hMargin
  refine ⟨N,K,?_⟩
  intro V _ G r a hN ha ha₁ hr hRob hReg
  let n := Fintype.card V
  have hLow : α*(n:ℝ) ≤ (r:ℝ) := hr ▸ mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)
  obtain ⟨I,inst,f,R,H,m,hm,hSize,hMinI,hMaxI,hExc,hLoops,_,_,_,_,hSub,rfl,hPairs,hBudget⟩ :=
    hSetup G hN hRob (fun v => by rw [(hReg v).1]; exact hLow)
      (fun v => by rw [(hReg v).2]; exact hLow)
  letI := inst
  let K' : ℝ := Fintype.card I
  have hK : 0 ≤ K' := Nat.cast_nonneg _
  have hKn : 1 ≤ K' := by
    dsimp only [K']
    exact_mod_cast hMin.trans hMinI
  have hn : 0 < n := by
    have hI : 0 < Fintype.card I := hMin.trans hMinI
    dsimp only [n]
    rw [order_eq f m hSize]
    exact Nat.lt_of_lt_of_le (Nat.mul_pos hm hI) (Nat.le_add_left _ _)
  have hζHalf : 4*θ ≤ 1/2 := by linarith only [hθSmall]
  have hExc' : ((exceptional f).card:ℝ) ≤ (ν/4)*(n:ℝ) := hExc.trans
    (mul_le_mul_of_nonneg_right (by linarith only [hθν,hν]) (Nat.cast_nonneg _))
  have hτHalf : 2*τ ≤ 1 := by linarith only [hτα,hα₁,hτ]
  have hDenseRob := real_robust_dense_reduced_of_pure_loss G H hSub f m hm hSize ν τ μ dense
    hν hν₁ hτ.le hτHalf hμ.le hμν hDense.le hDenseMargin hn hRob hExc' (fun v hv =>
      (hBudget v hv).1.trans (mul_le_mul_of_nonneg_right hCutν (Nat.cast_nonneg _)))
  refine ⟨I,inst,f,H,m,hm,hSize,hMinI,hMaxI,hExc,hSub,hLoops,hPairs,hDenseRob,?_⟩
  let den (i j : I) := density H (cluster f i) (cluster f j)
  let D := denseReduced H f dense
  let M := reducedMultiplicity (quotient H f) den β
  let C := reducedMultiplicity D den β
  let δ := 2*(d+ε+6*θ)+β
  let k := ⌊(a-γ)*K'/β⌋₊
  let c := ⌊dense/β⌋₊
  obtain ⟨hRow,hCol⟩ := pure_quotient_arc_budgets G H f m r a (d+ε+2*θ) (4*θ)
    hSub hSize hReg hr (hα.le.trans ha) ha₁ (by positivity) (by positivity) hζHalf hExc hBudget
  let lower := (a-2*(d+ε+6*θ))*K'
  let upper := (a+8*θ)*K'
  have hL : lower = (a-2*(d+ε+2*θ+4*θ))*K' := by dsimp only [lower]; ring
  have hU : upper = (a+2*(4*θ))*K' := by dsimp only [upper]; ring
  have hRow' (i : I) :
      lower*((m:ℝ)*(m:ℝ)) ≤ (incidences H (cluster f i) (lift f univ):ℝ) ∧
      (incidences H (cluster f i) (lift f univ):ℝ) ≤ upper*((m:ℝ)*(m:ℝ)) := by
    rw [hL,hU]
    exact hRow i
  have hCol' (i : I) :
      lower*((m:ℝ)*(m:ℝ)) ≤ (incidences H (lift f univ) (cluster f i):ℝ) ∧
      (incidences H (lift f univ) (cluster f i):ℝ) ≤ upper*((m:ℝ)*(m:ℝ)) := by
    rw [hL,hU]
    exact hCol i
  obtain ⟨hRows,hCols⟩ := reduced_semidegrees_from_cluster_arc_counts H f m β lower upper
    hβ hm hSize hRow' hCol'
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hDen := mul_pos hmR hmR
  obtain ⟨hDenseOut,hDenseIn⟩ := denseReduced_semidegrees_from_density_sums H f dense lower hDense.le
    (fun i => by rw [(quotient_density_sums H f m hSize i).1]; exact (le_div_iff₀ hDen).mpr (hRow' i).1)
    (fun i => by rw [(quotient_density_sums H f m hSize i).2]; exact (le_div_iff₀ hDen).mpr (hCol' i).1)
  have hDenseLower : (α/2)*K' ≤ lower-dense*K' := by
    have hCoeff : α/2 ≤ a-2*(d+ε+6*θ)-dense := by linarith only [hDenseDegree,ha]
    dsimp only [lower]
    rw [←sub_mul]
    exact mul_le_mul_of_nonneg_right hCoeff hK
  have hCapacity : (c:ℝ)*β ≤ dense := by
    dsimp only [c]
    exact (le_div_iff₀ hβ).mp (Nat.floor_le (div_nonneg hDense.le hβ.le))
  obtain ⟨hCapSub,hCap⟩ := reduced_dense_submatrix (quotient H f) D den β c hβ
    (denseReduced_le_quotient H f dense hDense) (fun _ _ hij => hCapacity.trans hij)
  have hcLow : dense/2 ≤ (c:ℝ)*β := by
    have hc₀ : dense/β < (c:ℝ)+1 := Nat.lt_floor_add_one (dense/β)
    have hc := (div_lt_iff₀ hβ).mp hc₀
    linarith only [hc,hβDense]
  have hBal : 3*(γ/β) ≤ (c:ℝ)*μ^2 := by
    have hPay := mul_le_mul_of_nonneg_right hcLow (sq_nonneg μ)
    apply (mul_le_mul_iff_of_pos_right hβ).mp
    rw [mul_assoc,div_mul_cancel₀ _ hβ.ne']
    have hγ' : 6*γ ≤ dense*μ^2 := by linarith only [hγDense,hγ]
    linear_combination hPay+hγ'/2
  have hRound : β ≤ (tol*γ/2)*K' := by
    have hβ' : β ≤ tol*γ/2 :=
      (show β ≤ 2*(d+ε+6*θ)+β by linarith only [hd,hε,hθ]).trans hLoss
    exact hβ'.trans (le_mul_of_one_le_right (by positivity) hKn)
  have hDefect (p : ℕ) (hP : lower-β*K' ≤ β*(p:ℝ) ∧ β*(p:ℝ) ≤ upper) :
      k ≤ p ∧ (1-tol)*(γ/β)*K' ≤ ((p-k:ℕ):ℝ) ∧
        ((p-k:ℕ):ℝ) ≤ (1+tol)*(γ/β)*K' := by
    have hEq : (a-δ)*K' = lower-β*K' := by dsimp only [lower,δ]; ring
    have hUpper : upper ≤ (a+δ)*K' := by
      apply mul_le_mul_of_nonneg_right _ hK
      dsimp only [δ]
      linarith only [hd,hε,hθ,hβ]
    exact osthus_staden_rounded_reduced_degree (Fintype.card I) a β γ δ tol hβ hγ
      (hγα.trans ha) hTol hTol₁ hLoss hRound p (hEq.trans_le hP.1) (hP.2.trans hUpper)
  have hDefRow (i : I) := hDefect _ (hRows i)
  have hDefCol (i : I) := hDefect _ (hCols i)
  have hWeighted : (a-2*(d+ε+6*θ)-β)*K' = lower-β*K' := by
    dsimp only [lower]
    ring
  refine ⟨fun i => hDenseLower.trans (hDenseIn i),fun i => hDenseLower.trans (hDenseOut i),
    fun i => ⟨hWeighted.trans_le (hRows i).1,(hRows i).2⟩,
    fun i => ⟨hWeighted.trans_le (hCols i).1,(hCols i).2⟩,?_⟩
  exact DirectedMultigraphFactors.exists_reduced_factorization M C D c k μ (2*τ) (α/2) tol (γ/β)
    hμ (by linarith only [hμν,hν₁]) hμτ (by linarith only [hτα]) hTol hTolμ
    (div_nonneg hγ.le hβ.le) hBal
    (hOrder.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hMinI) (by positivity))) hCapSub hCap
    hDenseRob (fun i => hDenseLower.trans (hDenseIn i)) (fun i => hDenseLower.trans (hDenseOut i))
    (fun i => (hDefRow i).1) (fun i => (hDefCol i).1)
    (fun i => (hDefRow i).2) (fun i => (hDefCol i).2)


/-- Reduced factorization on the pure partition of the robust host. -/
theorem exists_osthus_staden_reduced_factors
    (ν τ α θ ε ζ d dense μ β γ tol : ℝ) (kMin : ℕ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1) (hτ : 0 < τ) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hθ : 0 < θ) (hθSmall : θ ≤ 1/16) (hθν : θ ≤ ν/48) (hθα : θ ≤ α/24)
    (hε : 0 < ε) (hε₁ : ε ≤ 1/2) (hζ : 0 < ζ) (hζθ : ζ ≤ θ) (hd : 0 ≤ d)
    (hCutν : d+ε+2*θ ≤ ν/2) (hCutα : d+ε ≤ α/2)
    (hMargin : 2*ζ+3*ε < θ^4/2)
    (hμ : 0 < μ) (hμν : μ ≤ ν/2) (hμτ : μ ≤ 2*τ) (hτα : 16*τ ≤ α)
    (hDense : 0 < dense) (hDenseMargin : 8*(μ+dense) ≤ ν^2)
    (hβ : 0 < β) (hβDense : β ≤ dense/2)
    (hγ : 0 < γ) (hγα : γ ≤ α) (hγDense : 12*γ ≤ dense*μ^2)
    (hTol : 0 ≤ tol) (hTol₁ : tol ≤ 1) (hTolμ : 16*tol ≤ μ)
    (hLoss : 2*(d+ε+6*θ)+β ≤ tol*γ/2)
    (hDenseDegree : 2*(d+ε+6*θ)+dense ≤ α/2)
    (hMin : 1 ≤ kMin) (hOrder : 8 ≤ (α/2)*(kMin:ℝ)) :
    ∃ N K : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V) (r : ℕ) (a : ℝ),
      N ≤ Fintype.card V → α ≤ a → a ≤ 1 → (r:ℝ) = a*(Fintype.card V:ℝ) →
      IsRealRobust G ν τ → (∀ v, inDegree G v = r ∧ outDegree G v = r) →
      ∃ (I : Type u) (inst : Fintype I),
        letI := inst
        ∃ (f : V → Option I) (H : Digraph V) (m : ℕ),
          0 < m ∧ (∀ i, (cluster f i).card = m) ∧ kMin ≤ Fintype.card I ∧
          Fintype.card I ≤ K ∧ ((exceptional f).card:ℝ) ≤ 4*θ*(Fintype.card V:ℝ) ∧ H ≤ G ∧
          (∀ i, ¬ (quotient H f).Adj i i) ∧
          (∀ i j, (quotient H f).Adj i j →
            IsUniform H (2*ε) (cluster f i) (cluster f j) ∧
              d-ε ≤ density H (cluster f i) (cluster f j)) ∧
          IsRealRobust (denseReduced H f dense) μ (2*τ) ∧
          let den := fun i j => density H (cluster f i) (cluster f j)
          let M := reducedMultiplicity (quotient H f) den β
          let C := reducedMultiplicity (denseReduced H f dense) den β
          let k := ⌊(a-γ)*(Fintype.card I:ℝ)/β⌋₊
          ∃ W : I → I → ℕ, (∀ i j, W i j ≤ C i j) ∧
            ∃ F : Fin k → Equiv.Perm I, ∀ i j,
              W i j + ((univ : Finset (Fin k)).filter (fun t => F t i = j)).card = M i j := by
  obtain ⟨N,K,hN⟩ := exists_osthus_staden_reduced_factors_with_budgets.{u}
    ν τ α θ ε ζ d dense μ β γ tol kMin
    hν hν₁ hτ hα hα₁ hθ hθSmall hθν hθα hε hε₁ hζ hζθ hd hCutν hCutα hMargin
    hμ hμν hμτ hτα hDense hDenseMargin hβ hβDense hγ hγα hγDense
    hTol hTol₁ hTolμ hLoss hDenseDegree hMin hOrder
  refine ⟨N,K,?_⟩
  intro V _ G r a hSize ha ha₁ hr hRob hReg
  obtain ⟨I,inst,f,H,m,hm,hCells,hMinI,hMaxI,hExc,hSub,hLoop,hPair,hDenseRob,_,_,_,_,hFactors⟩ :=
    hN G r a hSize ha ha₁ hr hRob hReg
  exact ⟨I,inst,f,H,m,hm,hCells,hMinI,hMaxI,hExc,hSub,hLoop,hPair,hDenseRob,hFactors⟩

end OverfullWork.DirectedClusterQuotient
