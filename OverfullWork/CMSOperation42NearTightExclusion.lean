module

public import OverfullWork.CMSOperation42UniformEnding
public import OverfullWork.CMSOperation41ProjectedLayers

@[expose] public section


/-! Starting with the actual odd cut, run Operation 4.2 and exclude its
outcomes. The regular branch uses the already verified factorization.
The input margins are those used in the run from the initial cut. -/
namespace OverfullWork.CMSMatchingRemoval

open Finset SimpleGraph RobustExpansion NormalizedClassTwoStep
open scoped Classical
attribute [-instance] SimpleGraph.Sdiff.adjDecidable SimpleGraph.Sup.adjDecidable
  SimpleGraph.instDecidableRelAdjEdge
universe u

set_option maxHeartbeats 3000000 in
theorem cms_no_near_tight_odd_cut_after_trimming (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ,0 < τ ∧ τ ≤ α/512 ∧ ∀ ν : ℝ,0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (b A K : ℕ),
          let n := Fintype.card V
          let B := b+2*(A+K)
          let r := ⌈ν*(n:ℝ)⌉₊
          let t := ⌈τ*(n:ℝ)⌉₊
          Odd X.card → Xᶜ.card ≤ K → N+3+K ≤ n → 2*K ≤ n →
          ¬G.EdgeColorable G.maxDegree → ¬G.HasOverfullSubgraph →
          (∀ u v,G.Adj u v → G.maxDegree ≤ G.degree u+G.degree v+A) →
          ClassTwoMatchingRun.budget G X ≤ G.maxDegree+b →
          IsRealRobust G (8*ν) (τ/4) →
          ((B+4:ℕ):ℝ) ≤ η*((n-K-1:ℕ):ℝ) →
          ((K+1:ℕ):ℝ) ≤ 2*η^2*((n-K-1:ℕ):ℝ) →
          ((B/2+K:ℕ):ℝ) ≤ ν*(n:ℝ) →
          8*((K+3:ℕ):ℝ) ≤ ν*(n:ℝ) → 16*((K+3:ℕ):ℝ) ≤ τ*(n:ℝ) →
          α*(n:ℝ)+((B+K+3+B/2:ℕ):ℝ) ≤ (G.maxDegree:ℝ) →
          4*(B+K+2)+1+B/2 ≤ G.maxDegree →
          B+2*(A+K)+2+B/2 ≤ G.maxDegree →
          G.maxDegree ≤ (r-1)*(r-1) → 2*B+2*t+1+B/2 ≤ G.maxDegree → False := by
  obtain ⟨σ,hσ,hTerminal⟩ := cms_no_matching_removal_terminal_of_small_budgets.{u} α hα hα₁
  obtain ⟨τ₀,hτ₀,hRegular⟩ := EvenHamiltonFactorization.robust_regular_colourable.{u} α hα hα₁
  let τ := min (α/512) (min σ τ₀)
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτα : 512*τ ≤ α := by linarith only [(min_le_left _ _ : τ ≤ α/512)]
  have hτσ : τ ≤ σ := (min_le_right _ _).trans (min_le_left _ _)
  have hτ₀' : τ ≤ τ₀ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨τ,hτ,min_le_left _ _,?_⟩
  intro ν hν hντ
  obtain ⟨ηMax,hηMax,hTerminal⟩ := hTerminal (ν/8) (by positivity)
    (by linarith only [hντ,hτσ,hσ])
  obtain ⟨N₀,hRegular⟩ := hRegular (8*ν) (by positivity)
  obtain ⟨N₁,hRun⟩ := cms_operation_4_2_from_near_tight_odd_cut.{u} ν τ α hν hντ hτα hα₁
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηMax
  obtain ⟨N₂,hTerminal⟩ := hTerminal η hη hηMax
  let N := max N₀ (max N₁ N₂)
  refine ⟨N,?_⟩
  intro V _ _ G _ X b A K n B r t hOdd hK hn hnHalf hNC hNo hVAL hBudget hRob hB hK₀
    hBν hνK hτK hDens hRoom hGap hRate hPair
  have hN₀ : N₀ ≤ n := (le_max_left _ _).trans (by omega : N ≤ n)
  have hN₁ : N₁+3+K ≤ n := by dsimp only [N] at hn; omega
  have hN₂ : N₂+K+2 ≤ n := by dsimp only [N] at hn; omega
  rcases hRun G X b A K hOdd hK hN₁ hnHalf hNC hNo hVAL hBudget hRob hBν hνK hτK
      hDens hRoom hGap hRate hPair with hReg | ⟨H,Q,Z,j,hHG,hMaxH,hOddZ,hSmallZ,p,a,hStop,hRobQ,hd,hQ,hj⟩
  · have hEven : Even n := by
      rcases Nat.even_or_odd n with h | h
      · exact h
      exfalso
      apply hNo
      refine ⟨univ,?_⟩
      rw [filter_eq_self.mpr (fun e _ => subset_univ e.toFinset),card_univ]
      have hd : 0 < G.maxDegree := by omega
      have hCount := G.sum_degrees_eq_twice_card_edges
      simp only [hReg,sum_const,card_univ,nsmul_eq_mul] at hCount
      obtain ⟨k,hk⟩ := h
      have hDiv : n/2 = k := by omega
      have hRe : n*G.maxDegree = 2*(G.maxDegree*(n/2))+G.maxDegree := by
        rw [hDiv,hk]
        ring
      change n*G.maxDegree = _ at hCount
      change G.maxDegree*(n/2) < G.edgeFinset.card
      omega
    have hRob₀ : IsRealRobust G (8*ν) τ₀ :=
      real_robust_of_subgraph_degree_loss G G le_rfl 0 (8*ν) (8*ν) (τ/4) τ₀ le_rfl
        (by linarith only [hτ₀',hτ]) (by simp) (fun _ => by simp) hRob
    have hDensity : α*(n:ℝ) ≤ (G.maxDegree:ℝ) :=
      le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) hDens
    obtain ⟨C⟩ := hRegular G G.maxDegree hN₀ hEven hDensity hRob₀ hReg
    exact hNC (CMSTrimmingRound.simple_colourable_of_copy_colouring G C)
  · have hInd : Q.IsIndepSet (Zᶜ : Set V) := by
      intro y hy z hz hyz hadj
      have hVAL' := CleanedSourceVAL.weak_VAL Q Zᶜ a.ready y (by simpa using hy) z hadj
      have hp := a.pairs y (by simpa using hy) z (by simpa using hz) hyz
      omega
    let c : NormalizedAlmostStoppingRun.Certificate Q B K :=
      { set := Z
        odd := hOddZ
        complement_small := hSmallZ
        budget := by unfold ClassTwoMatchingRun.budget at hQ; omega
        ordered := a.ordered
        light_pairs := by
          intro y hy z hz hyz
          have hp := a.pairs y hy z hz hyz
          omega
        independent := hInd }
    let s : State V B K := ⟨Q,c,a.ready,a.uncolourable,a.no_overfull⟩
    have hDensity : α*(n:ℝ) ≤ (Q.maxDegree:ℝ) := by
      have hJ : (j:ℝ) ≤ ((B+K+3+B/2:ℕ):ℝ) := by exact_mod_cast (show j ≤ B+K+3+B/2 by omega)
      have hEq : (Q.maxDegree:ℝ)+j = (G.maxDegree:ℝ) := by exact_mod_cast hd
      linarith only [hJ,hDens,hEq]
    have hRob' : IsRealRobust Q (8*(ν/8)) σ :=
      real_robust_of_subgraph_degree_loss Q Q le_rfl 0 ν (8*(ν/8)) τ σ
        (by ring_nf; exact le_rfl) hτσ (by ring_nf; simp) (fun _ => by simp) hRobQ
    exact hTerminal s hN₂ hDensity hB hK₀ hRob' hStop

set_option maxHeartbeats 2600000 in
/-- The near-tight branch of Stage II, with its scales chosen in order
and the numerical run guards derived from the two small budgets. -/
theorem cms_no_near_tight_odd_cut_of_small_budgets (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ,0 < τ ∧ ∀ ν : ℝ,0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ,0 < ηMax ∧ ∀ η : ℝ,0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (b A K : ℕ),
          let n := Fintype.card V
          let B := b+2*(A+K)
          Odd X.card → Xᶜ.card ≤ K → N+3+K ≤ n → α*(n:ℝ) ≤ (G.maxDegree:ℝ) →
          ¬G.EdgeColorable G.maxDegree → ¬G.HasOverfullSubgraph →
          (∀ u v,G.Adj u v → G.maxDegree ≤ G.degree u+G.degree v+A) →
          ClassTwoMatchingRun.budget G X ≤ G.maxDegree+b →
          IsRealRobust G (8*ν) (τ/4) →
          ((B+4:ℕ):ℝ) ≤ η*((n-K-1:ℕ):ℝ) →
          ((K+1:ℕ):ℝ) ≤ 2*η^2*((n-K-1:ℕ):ℝ) → False := by
  have hα₂ : 0 < α/2 := by positivity
  obtain ⟨τ,hτ,hτCap,hUse⟩ := cms_no_near_tight_odd_cut_after_trimming.{u} (α/2) hα₂ (by linarith)
  have hτa : τ ≤ α/1024 := by linarith only [hτCap]
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  have hνa := hντ.trans hτa
  have hνOne : ν ≤ 1 := by linarith only [hνa,hα₁]
  obtain ⟨η₀,hη₀,hUse⟩ := hUse ν hν hντ
  let ηMax := min η₀ (min 1 (ν/128))
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  have hηone : η ≤ 1 := (hηMax.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hην : η ≤ ν/128 := (hηMax.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨N₀,hUse⟩ := hUse η hη (hηMax.trans (min_le_left _ _))
  let N := max N₀ ⌈4/ν^2⌉₊
  refine ⟨N,?_⟩
  intro V _ _ G _ X b A K n B hOdd hSmall hn hDensity hNC hNo hVAL hBudget hRob hB₀ hK₀
  have hSize : N₀+3+K ≤ n := by dsimp only [N] at hn; omega
  have hnR : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hαN := mul_le_mul_of_nonneg_right hνa hnR
  have hνN := mul_le_mul_of_nonneg_right hνOne hnR
  have hτN := mul_le_mul_of_nonneg_right hντ hnR
  have hCmp : ((n-K-1:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast (show n-K-1 ≤ n by omega)
  have hB : ((B+4:ℕ):ℝ) ≤ (ν/128)*(n:ℝ) :=
    hB₀.trans ((mul_le_mul_of_nonneg_left hCmp hη.le).trans (mul_le_mul_of_nonneg_right hην hnR))
  have hK : ((K+1:ℕ):ℝ) ≤ (ν/64)*(n:ℝ) := by
    have hSq : η^2 ≤ η := by nlinarith only [mul_nonneg hη.le (sub_nonneg.mpr hηone)]
    have hSlope : 2*η^2 ≤ ν/64 := by linarith only [hSq,hην]
    exact hK₀.trans ((mul_le_mul_of_nonneg_left hCmp (by positivity)).trans
      (mul_le_mul_of_nonneg_right hSlope hnR))
  have hK3 : ((K+3:ℕ):ℝ) ≤ (3*ν/64)*(n:ℝ) := by
    push_cast at hK ⊢
    linarith only [hK,Nat.cast_nonneg (α := ℝ) K]
  have hHalf : 2*K ≤ n := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast at hK ⊢
    linarith only [hK,hνN,hnR]
  have hBν : ((B/2+K:ℕ):ℝ) ≤ ν*(n:ℝ) := by
    have hB' : ((B/2:ℕ):ℝ) ≤ B := by exact_mod_cast Nat.div_le_self B 2
    push_cast at hB hK ⊢
    linarith only [hB,hK,hB',mul_nonneg hν.le hnR]
  have hνK : 8*((K+3:ℕ):ℝ) ≤ ν*(n:ℝ) := by
    linarith only [hK3,mul_nonneg hν.le hnR]
  have hτK : 16*((K+3:ℕ):ℝ) ≤ τ*(n:ℝ) := by
    linarith only [hK3,hτN,mul_nonneg hν.le hnR]
  have hBhalf : ((B/2:ℕ):ℝ) ≤ B := by exact_mod_cast Nat.div_le_self B 2
  have hDens : (α/2)*(n:ℝ)+((B+K+3+B/2:ℕ):ℝ) ≤ (G.maxDegree:ℝ) := by
    push_cast at hB hK3 ⊢
    linarith only [hB,hK3,hBhalf,hαN,hDensity,mul_nonneg hα.le hnR]
  have hRoom : 4*(B+K+2)+1+B/2 ≤ G.maxDegree := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast at hB hK3 ⊢
    linarith only [hB,hK3,hBhalf,hαN,hDensity,mul_nonneg hα.le hnR]
  have hGap : B+2*(A+K)+2+B/2 ≤ G.maxDegree := by
    have hBparts : 2*(A:ℝ)+2*(K:ℝ) ≤ B := by
      exact_mod_cast (show 2*A+2*K ≤ B by dsimp only [B]; omega)
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast at hB ⊢
    linarith only [hB,hBparts,hBhalf,hαN,hDensity,mul_nonneg hα.le hnR]
  let r := ⌈ν*(n:ℝ)⌉₊
  have hRate : G.maxDegree ≤ (r-1)*(r-1) := by
    have hLarge : 4/ν^2 ≤ (n:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈4/ν^2⌉₊ ≤ n by dsimp only [N] at hn; omega))
    have h4 : 4 ≤ ν^2*(n:ℝ) := by
      simpa only [mul_comm (ν^2)] using (div_le_iff₀ (by positivity : 0 < ν^2)).mp hLarge
    have h2 : 2 ≤ ν*(n:ℝ) := by
      have hν2 : ν^2 ≤ ν := by nlinarith only [mul_nonneg hν.le (sub_nonneg.mpr hνOne)]
      linarith only [h4,mul_le_mul_of_nonneg_right hν2 hnR]
    have hr : ν*(n:ℝ) ≤ (r:ℝ) := Nat.le_ceil _
    have hrOne : 1 ≤ r := by exact_mod_cast (show (1:ℝ) ≤ r by linarith only [h2,hr])
    have hR' : (ν/2)*(n:ℝ) ≤ ((r-1:ℕ):ℝ) := by
      rw [Nat.cast_sub hrOne,Nat.cast_one]
      linarith only [h2,hr]
    have hSq := mul_self_le_mul_self (show 0 ≤ (ν/2)*(n:ℝ) by positivity) hR'
    have hProd := mul_le_mul_of_nonneg_right h4 hnR
    have hd : (G.maxDegree:ℝ) ≤ (n:ℝ) := by
      let : Nonempty V := Fintype.card_pos_iff.mp (show 0 < n by omega)
      exact_mod_cast G.maxDegree_lt_card_verts.le
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    nlinarith only [hSq,hProd,hd]
  have hPair : 2*B+2*⌈τ*(n:ℝ)⌉₊+1+B/2 ≤ G.maxDegree := by
    have hCeil := Nat.ceil_lt_add_one (show 0 ≤ τ*(n:ℝ) by positivity)
    have hτBoundN := mul_le_mul_of_nonneg_right hτa hnR
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast at hB ⊢
    linarith only [hB,hBhalf,hCeil,hτBoundN,hαN,hDensity,mul_nonneg hα.le hnR]
  exact hUse G X b A K hOdd hSmall hSize hHalf hNC hNo hVAL hBudget hRob hB₀ hK₀
    hBν hνK hτK hDens hRoom hGap hRate hPair

end OverfullWork.CMSMatchingRemoval
