module

public import OverfullWork.OsthusStadenPrimaryReservesFromHost
public import OverfullWork.OsthusStadenBridgesFromPrimarySlices

@[expose] public section


/-! The input to §5.3 on one robust host. The dense reduced graph
supplies both the Hamilton ordering of §5.5 and the support for §5.8. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs
open scoped Classical
universe u

set_option maxHeartbeats 2400000 in
/-- Fix the regularity and trimming scales after the parameters of the
primary reserves. The upper bound on the cluster count is uniform, so
the required physical cluster size can be imposed afterwards. -/
theorem exists_osthus_staden_primary_host_with_cycle
    (ν τ α dense μ d β γ ξ err excLimit : ℝ) (kMin b : ℕ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1) (hτ : 0 < τ) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hμ : 0 < μ) (hμν : μ ≤ ν/2) (hμτ : μ ≤ 2*τ) (hτα : 64*τ ≤ α)
    (hDense : 0 < dense) (hDenseMargin : 8*(μ+dense) ≤ ν^2)
    (hd : 0 < d) (hdν : d ≤ ν/8) (hβ : 0 < β) (hβd : β ≤ d/4) (hβDense : β ≤ dense/2)
    (hγ : 0 < γ) (hγDense : 12*γ ≤ dense*μ^2)
    (hLoss : 3*d+β ≤ (μ/16)*γ/2) (hDenseDegree : 3*d+dense ≤ α/2)
    (hCopyDegree : 3*d+β ≤ α/8)
    (hξ : 0 < ξ) (hξSmall : ξ ≤ 1/8) (hBad : 8*ξ ≤ γ*β)
    (hErr : 0 < err) (hErr₁ : err ≤ 1) (hThin : 2*err ≤ γ*β)
    (hExc : 0 < excLimit) (hb : 0 < b) :
    ∃ exc K, 0 < exc ∧ exc ≤ excLimit ∧ exc ≤ 1/9 ∧ 0 < K ∧
      ∀ sizeMin : ℕ, ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V) (r : ℕ) (a : ℝ),
        N ≤ Fintype.card V → α ≤ a → a ≤ 1 → (r:ℝ) = a*(Fintype.card V:ℝ) →
        IsRealRobust G ν τ → (∀ v, inDegree G v = r ∧ outDegree G v = r) →
        ∃ (I : Type u) (inst : Fintype I),
          letI := inst
          ∃ (f : V → Option I) (H : Digraph V) (m₀ : ℕ),
            kMin ≤ Fintype.card I ∧ 0 < Fintype.card I ∧ Fintype.card I ≤ K ∧ H ≤ G ∧
            2 ≤ (2*τ)*(Fintype.card I:ℝ) ∧ 8 ≤ (α/2)*(Fintype.card I:ℝ) ∧
            (∀ i, ¬ (quotient H f).Adj i i) ∧
            (∀ i j, (quotient H f).Adj i j → d/2+β ≤ density H (cluster f i) (cluster f j)) ∧
            let Q := quotient H f
            let S := denseReduced H f dense
            let den := fun i j => density H (cluster f i) (cluster f j)
            let M := reducedMultiplicity Q den β
            let k := ⌊(a-γ)*(Fintype.card I:ℝ)/β⌋₊
            IsRealRobust S μ (2*τ) ∧
            (∀ i, (α/2)*(Fintype.card I:ℝ) ≤ (inDegree S i:ℝ)) ∧
            (∀ i, (α/2)*(Fintype.card I:ℝ) ≤ (outDegree S i:ℝ)) ∧
            (∀ i j, S.Adj i j → 0 < M i j) ∧
            (∀ i, M i i = 0) ∧
            0 < k ∧ k ≤ ⌈(K:ℝ)/β⌉₊ ∧
            ∃ (C : Equiv.Perm I) (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ err a exc)
              (F : Fin k → Equiv.Perm I) (pick : Fin k → I → ReducedCopy M),
              (∀ i j, C.SameCycle i j) ∧ (∀ i, S.Adj i (C i)) ∧ (∀ i, Q.Adj i (C i)) ∧
              sizeMin ≤ B.size ∧ B.MainCopyIncidenceBound (2*ξ*(Fintype.card I:ℝ)/β) ∧
              (∀ t i, (pick t i).1 = (i,F t i)) ∧
              (∀ t i, Q.Adj i (F t i)) ∧
              Function.Injective (fun q : Fin k × I => pick q.1 q.2) := by
  let θ := min (min (d/24) (ν/48)) (min (min (α/48) (excLimit/8)) (1/64))
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  have hθd : θ ≤ d/24 := (min_le_left _ _).trans (min_le_left _ _)
  have hθν : θ ≤ ν/48 := (min_le_left _ _).trans (min_le_right _ _)
  have hθα : θ ≤ α/48 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hθexc : θ ≤ excLimit/8 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hθ64 : θ ≤ 1/64 := (min_le_right _ _).trans (min_le_right _ _)
  let σ := min (err/64) (min (excLimit/8) (1/64))
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hσErr : σ ≤ err/64 := min_le_left _ _
  have hσexc : σ ≤ excLimit/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hσ64 : σ ≤ 1/64 := (min_le_right _ _).trans (min_le_right _ _)
  let δ₁ := min (ξ*σ/4) (err/64)
  have hδ₁ : 0 < δ₁ := by dsimp only [δ₁]; positivity
  have hδσ : δ₁ ≤ ξ*σ/4 := min_le_left _ _
  have hδerr : δ₁ ≤ err/64 := min_le_right _ _
  let ε := min (min (θ^4/64) (θ/2)) (min (δ₁/8) (d/4))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεθ₄ : ε ≤ θ^4/64 := (min_le_left _ _).trans (min_le_left _ _)
  have hεθ : ε ≤ θ/2 := (min_le_left _ _).trans (min_le_right _ _)
  have hεδ : ε ≤ δ₁/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hεd : ε ≤ d/4 := (min_le_right _ _).trans (min_le_right _ _)
  let exc := 4*θ+2*σ
  have hExcPos : 0 < exc := by dsimp only [exc]; positivity
  have hExcSmall : exc ≤ 1/9 := by dsimp only [exc]; linarith only [hθ64,hσ64]
  have hExcLimit : exc ≤ excLimit := by dsimp only [exc]; linarith only [hθexc,hσexc,hExc]
  have hLower : 2*(d+ε+6*θ) ≤ 3*d := by linarith only [hεd,hθd]
  have hDenseα : dense ≤ α/2 := by linarith only [hDenseDegree,hd]
  have hμ₁ : μ ≤ 1 := by linarith only [hμν,hν₁]
  have hSq : μ^2 ≤ 1 := by
    nlinarith only [mul_le_mul hμ₁ hμ₁ hμ.le (by norm_num : (0:ℝ) ≤ 1)]
  have hγBound : 24*γ ≤ α := by
    linarith only [mul_le_mul_of_nonneg_left hSq hDense.le,hγDense,hDenseα]
  have hγSmall : γ ≤ α/2 := by linarith only [hγBound,hγ]
  obtain ⟨Ncycle,hCycle⟩ := exists_kuhn_osthus_ordered_reduced_cycle.{u} μ (2*τ) (α/2)
    hμ hμτ (by linarith only [hτα]) (by linarith only [hα₁])
  obtain ⟨Ndeg,hNdeg⟩ := exists_nat_ge (8/(α/2))
  obtain ⟨Nτ,hNτ⟩ := exists_nat_ge (2/(2*τ))
  let k₀ := max 1 (max kMin (max Ncycle (max Ndeg Nτ)))
  have hk₀ : 1 ≤ k₀ := le_max_left _ _
  have hNext : max kMin (max Ncycle (max Ndeg Nτ)) ≤ k₀ := le_max_right _ _
  have hCMin : Ncycle ≤ k₀ := (le_max_left _ _).trans ((le_max_right _ _).trans hNext)
  have hDMin : Ndeg ≤ k₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hNext))
  have hTMin : Nτ ≤ k₀ := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hNext))
  have hOrder : 8 ≤ (α/2)*(k₀:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ (by positivity : 0 < α/2)).mp (hNdeg.trans (by exact_mod_cast hDMin))
  have hHalf : 2 ≤ (2*τ)*(k₀:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ (by positivity : 0 < 2*τ)).mp (hNτ.trans (by exact_mod_cast hTMin))
  obtain ⟨N₀,K,hPrepare⟩ := exists_osthus_staden_primary_reserves_from_host_with_good_main.{u}
    ν τ α θ ε ε d dense μ β γ (μ/16) δ₁ (err/4) err ξ σ k₀ b
    hν hν₁ hτ hα hα₁ hθ (by linarith only [hθ64]) hθν (by linarith only [hθα,hα])
    hε (by linarith only [hεθ,hθ64]) hε (by linarith only [hεθ,hθ]) hd.le
    (by linarith only [hdν,hεd,hθν,hν]) (by linarith only [hDenseDegree,hDense,hεd,hd])
    (by linarith only [hεθ₄,pow_pos hθ 4])
    hμ hμν hμτ (by linarith only [hτα,hτ]) hDense hDenseMargin hβ hβDense
    hγ (by linarith only [hγSmall,hα]) hγDense
    (by positivity) (by linarith only [hμ₁]) (by linarith)
    (by linarith only [hLower,hLoss]) (by linarith only [hLower,hDenseDegree]) hk₀ hOrder hb
    (by linarith only [hβd,hεd,hd]) (by linarith only [hγBound,hα₁,hγ])
    hδ₁ (by linarith only [hδerr,hErr₁]) (by linarith only [hεδ])
    hσ (by linarith only [hσ64]) hExcSmall
    hξ hξSmall hBad (by linarith only [hδσ]) (by linarith only [hδerr,hσErr,hErr])
    le_rfl hErr hErr₁ hThin (by linarith only [hθα]) (by linarith only [hLower,hCopyDegree])
  let K' := max 1 K
  refine ⟨exc,K',hExcPos,hExcLimit,hExcSmall,Nat.zero_lt_one.trans_le (le_max_left _ _),?_⟩
  intro sizeMin
  refine ⟨max N₀ (2*(K'*sizeMin)),?_⟩
  intro V _ G r a hN ha ha₁ hr hRob hReg
  obtain ⟨I,inst,f,H,m₀,hMinI,hMaxI,hHost,hLoop,hPair,hRobS,hIn,hOut,
    ⟨B,hGood⟩,W,hW,F,hFactors,pick,hPick,hInject⟩ :=
    hPrepare G r a ((le_max_left _ _).trans hN) ha ha₁ hr hRob hReg
  letI := inst
  let Q := quotient H f
  let S := denseReduced H f dense
  let den := fun i j => density H (cluster f i) (cluster f j)
  let M := reducedMultiplicity Q den β
  let k := ⌊(a-γ)*(Fintype.card I:ℝ)/β⌋₊
  have hI : 0 < Fintype.card I := hk₀.trans hMinI
  have hMax : Fintype.card I ≤ K' := hMaxI.trans (le_max_right _ _)
  have hIR : 0 ≤ (Fintype.card I:ℝ) := Nat.cast_nonneg _
  have hGe : (k₀:ℝ) ≤ Fintype.card I := by exact_mod_cast hMinI
  have hDenseSub : S ≤ Q := denseReduced_le_quotient H f dense hDense
  have hDen (i j : I) (h : Q.Adj i j) : d/2+β ≤ den i j := by
    have h' := hPair i j h
    linarith only [h',hεd,hβd]
  have hCopy (i j : I) (hij : S.Adj i j) : 0 < M i j := by
    have hDen' : β ≤ den i j := by linarith only [hDen i j (hDenseSub hij),hd]
    rw [show M i j = if Q.Adj i j then ⌊den i j/β⌋₊ else 0 from rfl, if_pos (hDenseSub hij)]
    apply Nat.le_floor
    norm_num
    exact (le_div_iff₀ hβ).mpr (by simpa only [one_mul] using hDen')
  have hLoopM (i : I) : M i i = 0 := by dsimp only [M,reducedMultiplicity]; exact if_neg (hLoop i)
  have hγa : γ ≤ a := by linarith only [hγSmall,ha,hα]
  have hKpos : 0 < k := by
    have hKone : 1 ≤ (Fintype.card I:ℝ) := by exact_mod_cast hI
    have hβa : β ≤ a-γ := by linarith only [hβDense,hDenseα,hγSmall,ha,hα]
    have hRate := le_mul_of_one_le_right (sub_nonneg.mpr hγa) hKone
    apply Nat.le_floor
    norm_num
    exact (le_div_iff₀ hβ).mpr (by simpa only [one_mul] using hβa.trans hRate)
  have hKcount : k ≤ ⌈(K':ℝ)/β⌉₊ := by
    have hTop : (a-γ)*(Fintype.card I:ℝ) ≤ (K':ℝ) :=
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (show a-γ ≤ 1 by linarith only [ha₁,hγ]) hIR :
        (a-γ)*(Fintype.card I:ℝ) ≤ Fintype.card I).trans (by exact_mod_cast hMax)
    have hRate := div_le_div_of_nonneg_right hTop hβ.le
    exact Nat.floor_le_of_le (hRate.trans (Nat.le_ceil _))
  obtain ⟨e,hCycleArc,_,_⟩ := hCycle S (hCMin.trans hMinI) hRobS hIn hOut
  let C := e.permCongr (finRotate (Fintype.card I))
  have hC (i : I) : S.Adj i (C i) := by
    have h := hCycleArc (e.symm i)
    change S.Adj (e (e.symm i)) (e (finRotate (Fintype.card I) (e.symm i))) at h
    rw [e.apply_symm_apply] at h
    exact h
  have hCells (i : I) : (cluster B.partition i).card = B.size := by
    rw [←B.retained_cells i,card_map,card_univ,Fintype.card_fin]
  have hSize : sizeMin ≤ B.size := by
    have hEq : (Fintype.card V:ℝ) =
        ((exceptional B.partition).card:ℝ)+(B.size:ℝ)*(Fintype.card I:ℝ) := by
      exact_mod_cast order_eq B.partition B.size hCells
    have hBound := B.exceptional_le.trans
      (mul_le_mul_of_nonneg_right hExcSmall (Nat.cast_nonneg _))
    have hN' : Fintype.card V ≤ 2*(Fintype.card I*B.size) := by
      exact_mod_cast (show (Fintype.card V:ℝ) ≤ 2*((Fintype.card I:ℝ)*(B.size:ℝ)) by
        nlinarith only [hEq,hBound,Nat.cast_nonneg (α := ℝ) (Fintype.card V)])
    apply Nat.le_of_mul_le_mul_left _ hI
    have hTrans : 2*(K'*sizeMin) ≤ 2*(Fintype.card I*B.size) :=
      ((le_max_right _ _).trans hN).trans hN'
    have hProd : K'*sizeMin ≤ Fintype.card I*B.size := by omega
    exact (Nat.mul_le_mul_right _ hMax).trans hProd
  have hGood' : B.MainCopyIncidenceBound (2*ξ*(Fintype.card I:ℝ)/β) := by
    intro q i x
    apply (hGood q i x).trans
    apply div_le_div_of_nonneg_right _ hβ.le
    have hA : a+2*(4*θ) ≤ 2 := by linarith only [ha₁,hθ64]
    rw [mul_comm (2:ℝ) ξ, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hIR) hξ.le
  refine ⟨I,inst,f,H,m₀,(le_max_left _ _).trans (hNext.trans hMinI),hI,hMax,hHost,
    hHalf.trans (mul_le_mul_of_nonneg_left hGe (by positivity)),
    hOrder.trans (mul_le_mul_of_nonneg_left hGe (by positivity)),hLoop,hDen,
    hRobS,hIn,hOut,hCopy,hLoopM,hKpos,hKcount,C,B,F,pick,
    spanning_conjugate_finRotate e,hC,fun i => hDenseSub (hC i),hSize,hGood',hPick,?_,hInject⟩
  exact primary_factor_successor_in_support Q den β F pick hPick

end OverfullWork.DirectedRobustExpansion
