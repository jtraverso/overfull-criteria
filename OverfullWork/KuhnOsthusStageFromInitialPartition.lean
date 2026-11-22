module

public import OverfullWork.KuhnOsthusExceptionalFactorSequence
public import OverfullWork.KuhnOsthusExceptionalWindingParameters
public import OverfullWork.KuhnOsthusInitialExceptionalMargins

@[expose] public section


/-! Apply the chosen numeric margins to a call on the initial
partition. Previous reserves enter only through their degree budgets. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u

set_option maxHeartbeats 1000000 in
/-- Prepare Lemma 7.6 for a fixed style count before any reserves are
chosen. The factor and deletion rates precede the slot budget and
degree envelope. The lower bound on the coarse cluster count precedes
its upper bound, as required to apply directed regularity. -/
theorem exists_kuhn_osthus_wound_stage_with_style_bounds
    (K : ℕ) (d α θ μ τ₀ : ℝ)
    (hK : 0 < K) (hd : 0 < d) (hd₁ : d ≤ 1)
    (hα : 0 < α) (hθ : 0 < θ) (hμ : 0 < μ) (hμτ : μ ≤ τ₀) (hτ₀ : τ₀ ≤ 1/4)
    (hατ : 6*τ₀ ≤ α) :
    ∃ σ ξMax ρ lossRate : ℝ, 0 < σ ∧ 0 < ξMax ∧ 0 < ρ ∧ 0 < lossRate ∧ σ ≤ 1/2 ∧ 2*σ ≤ d ∧ ξMax = σ/4 ∧
      ∀ (Λ : ℕ) (D ζMax : ℝ), 0 ≤ D → 0 < ζMax →
      ∃ (ζ : ℝ) (kMin : ℕ), 0 < ζ ∧ ζ ≤ ζMax ∧
      ∀ kMax : ℕ, 0 < kMax → ∃ mMin : ℕ, ∀ {V : Type u} [Fintype V] {l b k n L : ℕ}
        (G : Digraph V) (Z₀ Z : Finset V) (P : Fin k → Finset V)
        (A X : Fin n → Finset V) (R₀ : Digraph (Fin k))
        (_hl : 2 ≤ l) (hb : 6 ≤ b) (hk : 0 < k)
        (hIndex : n = l*(b*k)) (_hWinding : L = l*b)
        (m M r loss priorLoss : ℕ) (ξ εOld : ℝ),
        let parent := windingParent (n := n) k hk
        let R := fibrePullback R₀ parent parent
        let Y (i : Fin (l*(b*k))) := X (finCongr hIndex.symm i)
        WoundExceptionalPartition G Z₀ Z P A X R₀ hk L M (K*m) α θ εOld μ τ₀ →
        εOld ≤ τ₀ → θ ≤ 1-εOld →
        kMin ≤ k → n ≤ kMax → K*l ≤ Λ → mMin ≤ m → ξ ≤ ξMax →
        (Z.card:ℝ) ≤ ζ*(Fintype.card V:ℝ) →
        ((K*l*r+priorLoss:ℕ):ℝ) ≤ D*((K*m:ℕ):ℝ) →
        (r:ℝ) ≤ ρ*(m:ℝ) → (loss:ℝ) ≤ lossRate*((K*m:ℕ):ℝ) →
        (∀ i j, R.Adj i j → IsUniform G ξ (X i) (X j) ∧ 2*d ≤ density G (X i) (X j)) →
        (∀ i, IsLowerSuperregularPair G ξ (2*d) (X i) (X (finRotate n i))) →
        WoundFactorStage G Z Y (Nat.mul_pos (by omega) hk) K m r loss priorLoss σ := by
  obtain ⟨ε,ν,τ,γ,c,hε,hε₁,hν,hWidth,hτγ,hγ,hDensity,hCost,hFloor,hc,hCap,hmCut⟩ :=
    exists_wound_factor_packing_scales d hd hd₁
  obtain ⟨σ,δ,η,a,ρ,lossRate,hσ,hσHalf,hσStyle,hδ,hδ₁,hTol,hη,hη₁,ha,hScale,hCellTol,hGap,
    hPairFloor,hSuccessorTol,hρ,hRateCell,hRateSuccessor,hLossRate,hLossEq⟩ :=
    exists_wound_factor_local_margins K α θ d ε hα hθ hε hε₁ hDensity
  refine ⟨σ,σ/4,ρ,lossRate,hσ,by positivity,hρ,hLossRate,hσHalf,hPairFloor,rfl,?_⟩
  intro Λ D ζMax hD hζMax
  obtain ⟨ζ,hζ,hζHalf,hζMax',kEnd,hEnd⟩ :=
    exists_wound_factor_global_margins Λ c α θ μ D ζMax (by omega) hα hθ hμ hD hζMax
  obtain ⟨kRoute,hRoute⟩ := exists_wound_reduced_route_margins α μ τ₀ hμ hμτ hτ₀ hατ
  refine ⟨ζ,max kEnd kRoute,hζ,hζMax',?_⟩
  intro kMax hMax
  let B := 8*(kMax:ℝ)
  have hMax' : (0:ℝ) < kMax := by exact_mod_cast hMax
  have hB : 0 < B := by dsimp only [B]; positivity
  obtain ⟨N,hN⟩ := kuhn_osthus_wound_factor_stage.{u}
    B σ d δ ε ν τ γ hB hσ hν hWidth hε hε₁ hτγ hγ hDensity hCost hFloor hTol K c hK hc hCap
  let nMin := max (2*N) (max (2*c) ⌈1/ε⌉₊)
  refine ⟨nMin,?_⟩
  intro V _ l b k n L G Z₀ Z P A X R₀ hl hb hk hIndex hWinding m M r loss priorLoss ξ εOld parent R Y
    hPart hOld hTrim hkMin hnMax hSlots hmMin hξ hZ hExceptional hR hLoss hPairs hSup
  have hb' : 0 < b := by omega
  have hn : n = L*k := by rw [hIndex,hWinding,Nat.mul_assoc]
  have hmCut' : max (2*c) ⌈1/ε⌉₊ ≤ m := (le_max_right _ _).trans hmMin
  obtain ⟨hmc,hmε⟩ := hmCut m hmCut'
  have hm : 0 < m := by omega
  have hM : 0 < M := hPart.volume.trans_lt' (Nat.mul_pos (by rw [hWinding]; positivity) (by positivity))
  obtain ⟨hCard,hOrdDensity⟩ :=
    wound_exceptional_density_of_partition X Z (K*m) ζ (fun i => (hPart.fine_size i).1)
      hPart.fine_disjoint hPart.fine_ordinary hPart.fine_cover hζHalf hZ
  have hBudget : 4*(Fintype.card V:ℝ) ≤ B*((K*m:ℕ):ℝ) := by
    have hMass : (Fintype.card V:ℝ) ≤ 2*((n*(K*m):ℕ):ℝ) := by
      rw [←hCard,Nat.cast_add]
      have h := mul_le_mul_of_nonneg_right hζHalf (Nat.cast_nonneg (n*(K*m)) : (0:ℝ) ≤ ↑(n*(K*m)))
      linarith only [h,hOrdDensity]
    have hMaxMass : ((n*(K*m):ℕ):ℝ) ≤ (kMax:ℝ)*((K*m:ℕ):ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right (K*m) hnMax
    dsimp only [B]
    linarith only [hMass,hMaxMass]
  have hZ' : (Z.card:ℝ) ≤ ζ*((Z.card+L*k*(K*m):ℕ):ℝ) := by rw [←hn,hCard]; exact hZ
  obtain ⟨hEnds,hLoad⟩ := hEnd L k (K*m) m K l b Z.card r priorLoss σ
    ((le_max_left _ _).trans hkMin) (by omega) hb hm hσHalf hWinding rfl hSlots hZ' hExceptional
  obtain ⟨hLarge,hGrowth,hSemidegree⟩ := hRoute k b ((le_max_right _ _).trans hkMin) hb'
  have hUpper : d+(ξ+σ/4) ≤ 2*d := by linarith only [hξ,hPairFloor,hd]
  have hPairs' (i j : Fin n) (h : R.Adj i j) :
      IsUniform G ξ (X i) (X j) ∧ d+(ξ+σ/4) ≤ density G (X i) (X j) :=
    ⟨(hPairs i j h).1,hUpper.trans (hPairs i j h).2⟩
  have hSup' (i : Fin n) : IsLowerSuperregularPair G ξ d (X i) (X (finRotate n i)) := by
    obtain ⟨d',hLow,hHigh,hPair⟩ := hSup i
    exact ⟨d',(by linarith only [hd,hLow]),hHigh,hPair⟩
  have hFactorBudget (u : ℝ) (hu : ρ ≤ a*u) : (r:ℝ) ≤ a*((m:ℝ)*u) := by
    have h := hR.trans (mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg m))
    linarith only [h]
  have hτ₀pos : 0 < τ₀ := hμ.trans_le hμτ
  exact hN G Z₀ Z P A X R₀ hl hb' hk hIndex hWinding m M r loss priorLoss α θ εOld μ τ₀ a η ξ (σ/4)
    hPart hM ((le_max_left _ _).trans hmMin) hmc hmε hBudget (by positivity)
    (by linarith only [hξ]) (by rwa [hLossEq,mul_assoc,mul_comm σ _] at hLoss)
    hPairs' hSup' hα.le hθ.le (by linarith only [hατ,hτ₀pos]) hOld hTrim
    (by linarith only [hσHalf]) hσStyle hEnds hμ hμτ hτ₀ hLarge hGrowth hSemidegree hLoad
    ha.le hη hη₁ hScale hCellTol (hFactorBudget _ hRateCell) hGap hδ hδ₁ hPairFloor
    hSuccessorTol (hFactorBudget _ hRateSuccessor)

/-- Prepare Lemma 7.6 for a fixed style count before any reserves are
chosen. The factor and deletion rates precede the slot budget and
degree envelope. The lower bound on the coarse cluster count precedes
its upper bound, as required to apply directed regularity. -/
theorem exists_kuhn_osthus_wound_stage_from_initial_partition
    (K : ℕ) (d α θ μ τ₀ : ℝ)
    (hK : 0 < K) (hd : 0 < d) (hd₁ : d ≤ 1)
    (hα : 0 < α) (hθ : 0 < θ) (hμ : 0 < μ) (hμτ : μ ≤ τ₀) (hτ₀ : τ₀ ≤ 1/4)
    (hατ : 6*τ₀ ≤ α) :
    ∃ σ ξMax ρ lossRate : ℝ, 0 < σ ∧ 0 < ξMax ∧ 0 < ρ ∧ 0 < lossRate ∧
      ∀ (Λ : ℕ) (D ζMax : ℝ), 0 ≤ D → 0 < ζMax →
      ∃ (ζ : ℝ) (kMin : ℕ), 0 < ζ ∧ ζ ≤ ζMax ∧
      ∀ kMax : ℕ, 0 < kMax → ∃ mMin : ℕ, ∀ {V : Type u} [Fintype V] {l b k n L : ℕ}
        (G : Digraph V) (Z₀ Z : Finset V) (P : Fin k → Finset V)
        (A X : Fin n → Finset V) (R₀ : Digraph (Fin k))
        (_hl : 2 ≤ l) (hb : 6 ≤ b) (hk : 0 < k)
        (hIndex : n = l*(b*k)) (_hWinding : L = l*b)
        (m M r loss priorLoss : ℕ) (ξ εOld : ℝ),
        let parent := windingParent (n := n) k hk
        let R := fibrePullback R₀ parent parent
        let Y (i : Fin (l*(b*k))) := X (finCongr hIndex.symm i)
        WoundExceptionalPartition G Z₀ Z P A X R₀ hk L M (K*m) α θ εOld μ τ₀ →
        εOld ≤ τ₀ → θ ≤ 1-εOld →
        kMin ≤ k → n ≤ kMax → K*l ≤ Λ → mMin ≤ m → ξ ≤ ξMax →
        (Z.card:ℝ) ≤ ζ*(Fintype.card V:ℝ) →
        ((K*l*r+priorLoss:ℕ):ℝ) ≤ D*((K*m:ℕ):ℝ) →
        (r:ℝ) ≤ ρ*(m:ℝ) → (loss:ℝ) ≤ lossRate*((K*m:ℕ):ℝ) →
        (∀ i j, R.Adj i j → IsUniform G ξ (X i) (X j) ∧ 2*d ≤ density G (X i) (X j)) →
        (∀ i, IsLowerSuperregularPair G ξ (2*d) (X i) (X (finRotate n i))) →
        WoundFactorStage G Z Y (Nat.mul_pos (by omega) hk) K m r loss priorLoss σ := by
  obtain ⟨σ,ξMax,ρ,loss,hσ,hξ,hρ,hLoss,_,_,_,hStage⟩ :=
    exists_kuhn_osthus_wound_stage_with_style_bounds.{u} K d α θ μ τ₀ hK hd hd₁ hα hθ hμ hμτ hτ₀ hατ
  exact ⟨σ,ξMax,ρ,loss,hσ,hξ,hρ,hLoss,hStage⟩

end OverfullWork.DirectedRobustExpansion
