module

public import OverfullWork.OsthusStadenReducedFactorsFromHost
public import OverfullWork.OsthusStadenPrimaryReserveData

@[expose] public section


/-! Physical primary factors and all five thin reserves on one
partition of the original regular robust digraph. -/
namespace OverfullWork.DirectedClusterQuotient

open Finset DirectedRobustExpansion DirectedRegularPairs
open scoped Classical
universe u

set_option maxHeartbeats 1200000 in
/-- From the regular robust host, construct the primary factors and
assign distinct physical copies after the common divisible trim. -/
theorem exists_osthus_staden_primary_reserves_from_host_with_good_main
    (ν τ α θ ε ζ d dense μ β γ tol δ₁ δ₂ δ₃ ξ σ : ℝ) (kMin b : ℕ)
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
    (hMin : 1 ≤ kMin) (hOrder : 8 ≤ (α/2)*(kMin:ℝ))
    (hb : 0 < b) (hβPair : β ≤ d-ε) (hSum : 5*γ ≤ 1)
    (hδ₁ : 0 < δ₁) (hδ₁One : δ₁ ≤ 1) (hClone : 2*ε ≤ δ₁/4)
    (hσ : 0 < σ) (hσSmall : σ ≤ 1/4) (hExcScale : 4*θ+2*σ ≤ 1/9)
    (hξ : 0 < ξ) (hξSmall : ξ ≤ 1/8) (hBad : 8*ξ ≤ γ*β)
    (hTrimGood : 4*δ₁ ≤ ξ*σ) (hTrimReg : 4*(δ₁+σ) ≤ δ₂)
    (hReserve : δ₂ ≤ δ₃/4) (hδ₃ : 0 < δ₃) (hδ₃One : δ₃ ≤ 1) (hThin : 2*δ₃ ≤ γ*β)
    (hExcDegree : 48*θ ≤ α) (hCopyDegree : 2*(d+ε+6*θ)+β ≤ α/8) :
    ∃ N K : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V) (r : ℕ) (a : ℝ),
      N ≤ Fintype.card V → α ≤ a → a ≤ 1 → (r:ℝ) = a*(Fintype.card V:ℝ) →
      IsRealRobust G ν τ → (∀ v, inDegree G v = r ∧ outDegree G v = r) →
      ∃ (I : Type u) (inst : Fintype I),
        letI := inst
        ∃ (f : V → Option I) (H : Digraph V) (m₀ : ℕ),
          kMin ≤ Fintype.card I ∧ Fintype.card I ≤ K ∧ H ≤ G ∧
          (∀ i, ¬ (quotient H f).Adj i i) ∧
          (∀ i j, (quotient H f).Adj i j → d-ε ≤ density H (cluster f i) (cluster f j)) ∧
          IsRealRobust (denseReduced H f dense) μ (2*τ) ∧
          (∀ i, (α/2)*(Fintype.card I:ℝ) ≤ (inDegree (denseReduced H f dense) i:ℝ)) ∧
          (∀ i, (α/2)*(Fintype.card I:ℝ) ≤ (outDegree (denseReduced H f dense) i:ℝ)) ∧
          let den := fun i j => density H (cluster f i) (cluster f j)
          let M := reducedMultiplicity (quotient H f) den β
          let C := reducedMultiplicity (denseReduced H f dense) den β
          let k := ⌊(a-γ)*(Fintype.card I:ℝ)/β⌋₊
          (∃ B : OsthusStadenPrimaryReserveData H f M m₀ b β γ δ₃ a (4*θ+2*σ),
              B.MainCopyIncidenceBound (ξ*(a+2*(4*θ))*(Fintype.card I:ℝ)/β)) ∧
          ∃ W : I → I → ℕ, (∀ i j, W i j ≤ C i j) ∧
            ∃ F : Fin k → Equiv.Perm I,
              (∀ i j, W i j + ((univ : Finset (Fin k)).filter (fun t => F t i = j)).card = M i j) ∧
              ∃ pick : Fin k → I → ReducedCopy M,
                (∀ t i, (pick t i).1 = (i,F t i)) ∧
                Function.Injective (fun q : Fin k × I => pick q.1 q.2) := by
  have hβ₁ : β ≤ 1 := by linarith only [hβPair,hCutα,hα₁,hε]
  obtain ⟨N₁,hPrepare⟩ := exists_osthus_staden_primary_reserves_for_quotient_with_good_main.{u,u}
    β γ (2*ε) δ₁ δ₂ δ₃ ξ σ b hβ hβ₁ hγ hSum (by positivity) hClone hδ₁ hδ₁One
    hσ hσSmall hb hξ (by linarith only [hξSmall]) hBad hTrimGood hTrimReg hReserve hδ₃ hδ₃One hThin
  obtain ⟨N₂,K,hReduced⟩ := exists_osthus_staden_reduced_factors_with_budgets.{u}
    ν τ α θ ε ζ d dense μ β γ tol kMin
    hν hν₁ hτ hα hα₁ hθ hθSmall hθν hθα hε hε₁ hζ hζθ hd hCutν hCutα hMargin
    hμ hμν hμτ hτα hDense hDenseMargin hβ hβDense hγ hγα hγDense
    hTol hTol₁ hTolμ hLoss hDenseDegree hMin hOrder
  refine ⟨max N₂ (2*(K*N₁)),K,?_⟩
  intro V _ G r a hN ha ha₁ hr hRob hReg
  obtain ⟨I,inst,f,H,m₀,_,hCells,hMinI,hMaxI,hExc,hSub,hLoop,hPair,hDenseRob,hDenseIn,hDenseOut,hRow,hCol,
    W,hW,F,hExact⟩ := hReduced G r a ((le_max_left _ _).trans hN) ha ha₁ hr hRob hReg
  letI := inst
  have hCardI : 0 < Fintype.card I := hMin.trans hMinI
  have hNcap : Fintype.card V ≤ 2*(m₀*Fintype.card I) := by
    have hEq : (Fintype.card V:ℝ) = ((exceptional f).card:ℝ)+(m₀:ℝ)*(Fintype.card I:ℝ) := by
      exact_mod_cast order_eq f m₀ hCells
    have hScale := mul_le_mul_of_nonneg_right hθSmall (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
    have hHalf : (Fintype.card V:ℝ) ≤ 2*((m₀:ℝ)*(Fintype.card I:ℝ)) := by
      linarith only [hEq,hExc,hScale,Nat.cast_nonneg (α := ℝ) (Fintype.card V)]
    exact_mod_cast hHalf
  have hLower : 2*(K*N₁) ≤ Fintype.card V := (le_max_right _ _).trans hN
  have hm : N₁ ≤ m₀ := by
    have hCount : Fintype.card I*N₁ ≤ K*N₁ := Nat.mul_le_mul_right _ hMaxI
    have hM : Fintype.card I*N₁ ≤ Fintype.card I*m₀ := by
      rw [Nat.mul_comm (Fintype.card I) m₀]
      omega
    exact Nat.le_of_mul_le_mul_left hM hCardI
  let loss := (2*(d+ε+6*θ)+β)/4
  have hLose : 4*loss = 2*(d+ε+6*θ)+β := by dsimp only [loss]; ring
  have hLow : 3*a/4 ≤ (1-ξ)*(a-4*loss) := by
    have hlo : 7*a/8 ≤ a-4*loss := by rw [hLose]; linarith only [hCopyDegree,ha]
    have haPos : 0 < a := hα.trans_le ha
    have h := mul_le_mul (show 7/8 ≤ 1-ξ by linarith only [hξSmall]) hlo
      (show 0 ≤ 7*a/8 by positivity) (show 0 ≤ 1-ξ by linarith only [hξSmall])
    linarith only [h,haPos]
  have hCountLow : a-4*loss = a-2*(d+ε+6*θ)-β := by rw [hLose]; ring
  have hCountHigh : a+2*(4*θ) = a+8*θ := by ring
  have hPrepared := hPrepare H f m₀ a (4*θ) loss hm (hα.trans_le ha) (by positivity)
    hExcScale (by linarith only [hExcDegree,ha]) hCells hExc
    (fun i j hij => ⟨(hPair i j hij).1,hβPair.trans (hPair i j hij).2⟩)
    (by
      dsimp only
      intro s i
      cases s
      · simpa only [Bool.false_eq_true,ite_false,hCountLow,hCountHigh] using hCol i
      · simpa only [ite_true,hCountLow,hCountHigh] using hRow i)
    hLow
  refine ⟨I,inst,f,H,m₀,hMinI,hMaxI,hSub,hLoop,fun i j hij => (hPair i j hij).2,hDenseRob,
    hDenseIn,hDenseOut,hPrepared,W,hW,F,hExact,?_⟩
  exact exists_factor_copy_assignment _ F (fun i j => by have := hExact i j; omega)

/-- Construct the primary reserves and factors with their original interface. -/
theorem exists_osthus_staden_primary_reserves_from_host
    (ν τ α θ ε ζ d dense μ β γ tol δ₁ δ₂ δ₃ ξ σ : ℝ) (kMin b : ℕ)
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
    (hMin : 1 ≤ kMin) (hOrder : 8 ≤ (α/2)*(kMin:ℝ))
    (hb : 0 < b) (hβPair : β ≤ d-ε) (hSum : 5*γ ≤ 1)
    (hδ₁ : 0 < δ₁) (hδ₁One : δ₁ ≤ 1) (hClone : 2*ε ≤ δ₁/4)
    (hσ : 0 < σ) (hσSmall : σ ≤ 1/4) (hExcScale : 4*θ+2*σ ≤ 1/9)
    (hξ : 0 < ξ) (hξSmall : ξ ≤ 1/8) (hBad : 8*ξ ≤ γ*β)
    (hTrimGood : 4*δ₁ ≤ ξ*σ) (hTrimReg : 4*(δ₁+σ) ≤ δ₂)
    (hReserve : δ₂ ≤ δ₃/4) (hδ₃ : 0 < δ₃) (hδ₃One : δ₃ ≤ 1) (hThin : 2*δ₃ ≤ γ*β)
    (hExcDegree : 48*θ ≤ α) (hCopyDegree : 2*(d+ε+6*θ)+β ≤ α/8) :
    ∃ N K : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V) (r : ℕ) (a : ℝ),
      N ≤ Fintype.card V → α ≤ a → a ≤ 1 → (r:ℝ) = a*(Fintype.card V:ℝ) →
      IsRealRobust G ν τ → (∀ v, inDegree G v = r ∧ outDegree G v = r) →
      ∃ (I : Type u) (inst : Fintype I),
        letI := inst
        ∃ (f : V → Option I) (H : Digraph V) (m₀ : ℕ),
          kMin ≤ Fintype.card I ∧ Fintype.card I ≤ K ∧ H ≤ G ∧
          (∀ i, ¬ (quotient H f).Adj i i) ∧
          (∀ i j, (quotient H f).Adj i j → d-ε ≤ density H (cluster f i) (cluster f j)) ∧
          IsRealRobust (denseReduced H f dense) μ (2*τ) ∧
          let den := fun i j => density H (cluster f i) (cluster f j)
          let M := reducedMultiplicity (quotient H f) den β
          let C := reducedMultiplicity (denseReduced H f dense) den β
          let k := ⌊(a-γ)*(Fintype.card I:ℝ)/β⌋₊
          Nonempty (OsthusStadenPrimaryReserveData H f M m₀ b β γ δ₃ a (4*θ+2*σ)) ∧
          ∃ W : I → I → ℕ, (∀ i j, W i j ≤ C i j) ∧
            ∃ F : Fin k → Equiv.Perm I,
              (∀ i j, W i j + ((univ : Finset (Fin k)).filter (fun t => F t i = j)).card = M i j) ∧
              ∃ pick : Fin k → I → ReducedCopy M,
                (∀ t i, (pick t i).1 = (i,F t i)) ∧
                Function.Injective (fun q : Fin k × I => pick q.1 q.2) := by
  obtain ⟨N,K,hN⟩ := exists_osthus_staden_primary_reserves_from_host_with_good_main.{u}
    ν τ α θ ε ζ d dense μ β γ tol δ₁ δ₂ δ₃ ξ σ kMin b
    hν hν₁ hτ hα hα₁ hθ hθSmall hθν hθα hε hε₁ hζ hζθ hd hCutν hCutα hMargin
    hμ hμν hμτ hτα hDense hDenseMargin hβ hβDense hγ hγα hγDense hTol hTol₁ hTolμ
    hLoss hDenseDegree hMin hOrder hb hβPair hSum hδ₁ hδ₁One hClone hσ hσSmall hExcScale
    hξ hξSmall hBad hTrimGood hTrimReg hReserve hδ₃ hδ₃One hThin hExcDegree hCopyDegree
  refine ⟨N,K,?_⟩
  intro V _ G r a hSize ha ha₁ hr hRob hReg
  obtain ⟨I,inst,f,H,m₀,hMinI,hMaxI,hSub,hLoop,hPair,hDenseRob,_,_,⟨B,_⟩,hFactors⟩ :=
    hN G r a hSize ha ha₁ hr hRob hReg
  exact ⟨I,inst,f,H,m₀,hMinI,hMaxI,hSub,hLoop,hPair,hDenseRob,⟨B⟩,hFactors⟩

end OverfullWork.DirectedClusterQuotient
