module

public import OverfullWork.CMSBalancedCellHalving
public import OverfullWork.CMSCrossingRegularLifting
public import OverfullWork.CMSReducedEvenPartition

@[expose] public section


/-! Construct the balanced robust cut in CMS Lemma 5.4. The
expansion window is widened to (4τ) and the discrepancy can be
any prescribed positive linear tolerance. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph PrunedCore DirectedClusterQuotient
open scoped Classical
universe u

set_option maxHeartbeats 2500000 in
/-- A sufficiently large robust graph of even order has a balanced
cut with robust expansion in both directions, simultaneous degree
balance, and the prescribed vertices on opposite sides. -/
theorem exists_balanced_robust_cut_at_rate (ν τ ζ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτcap : τ ≤ 1/8) (hζ : 0 < ζ) :
    ∃ ρcut : ℝ, ρcut = ν^4/524288 ∧ 0 < ρcut ∧ ρcut ≤ ν ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (x y : V),
        N ≤ Fintype.card V → Fintype.card V = 2*m → x ≠ y →
        RobustExpansion.IsRealRobust G ν τ →
        ∃ A : Finset V, A.card = m ∧ Aᶜ.card = m ∧ x ∈ A ∧ y ∉ A ∧
          (∀ v, |(neighboursIn G A v:ℝ)-(neighboursIn G Aᶜ v:ℝ)| < ζ*(m:ℝ)) ∧
          BipartiteRobustMargin.ExpandsTo G A Aᶜ ⌈ρcut*(m:ℝ)⌉₊ ⌈4*τ*(m:ℝ)⌉₊ ∧
          BipartiteRobustMargin.ExpandsTo G Aᶜ A ⌈ρcut*(m:ℝ)⌉₊ ⌈4*τ*(m:ℝ)⌉₊ := by
  let ρ := ν/4
  let τR := 2*τ
  let d := ν^2/64
  let ε := min (d/64) (ρ/512)
  let β := ν^2/32
  let σ := ρ/64
  let δ := d/2
  let ρcut := δ*ρ^2/256
  let kMin := max 4 ⌈4/τR⌉₊
  have hτ : 0 < τ := hν.trans_le hντ
  have hν₁ : ν ≤ 1 := by linarith only [hντ,hτcap]
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hρ₁ : ρ ≤ 1 := by dsimp only [ρ]; linarith only [hν₁]
  have hτR : 0 < τR := by dsimp only [τR]; positivity
  have hτRcap : τR ≤ 1/4 := by dsimp only [τR]; linarith only [hτcap]
  have hd : 0 < d := by dsimp only [d]; positivity
  have hd₁ : d ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hν₁ hν.le
    dsimp only [d]
    nlinarith only [hh,hν₁]
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεd : ε ≤ d/64 := min_le_left _ _
  have hερ : ε ≤ ρ/512 := min_le_right _ _
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδ₁ : δ ≤ 1 := by dsimp only [δ]; linarith only [hd₁]
  have hCut : 0 < ρcut := by dsimp only [ρcut]; positivity
  have hCutν : ρcut ≤ ν := by
    have hsq := mul_le_mul_of_nonneg_right hρ₁ hρ.le
    have hh := mul_le_mul_of_nonneg_right hδ₁ (sq_nonneg ρ)
    have hρν : ρ ≤ ν := by dsimp only [ρ]; linarith only [hν]
    dsimp only [ρcut]
    nlinarith only [hsq,hh,hρν,hρ.le]
  have hBudget : 4*ε+β/2+4*d ≤ (ν/2)^2 := by
    dsimp only [d,β] at hεd ⊢
    nlinarith only [hεd,sq_nonneg ν]
  obtain ⟨K,N₀,hPart⟩ := exists_reduced_even_partition.{u} ν τ ε d β σ kMin
    hν hτ hε (by linarith only [hεd,hd₁]) hd.le
    (by dsimp only [β]; positivity) (by dsimp only [σ]; positivity) hBudget
  obtain ⟨m₀,hHalf⟩ := exists_halving_cut.{u} ζ hζ
  obtain ⟨m₁,hm₁⟩ := exists_nat_ge (max ((K:ℝ)/(ρ/64)) (2/(δ*ρ^2/128)))
  have hExact : ρcut = ν^4/524288 := by
    dsimp only [ρcut,δ,d,ρ]
    ring
  refine ⟨ρcut,hExact,hCut,hCutν,max N₀ (2*max m₀ m₁),?_⟩
  intro V _ _ G _ m x y hN hCard hxy hRob
  have hm : max m₀ m₁ ≤ m := by
    have hh := (le_max_right _ _).trans hN
    rw [hCard] at hh
    omega
  have hmReal := hm₁.trans (show (m₁:ℝ) ≤ (m:ℝ) by
    exact_mod_cast (le_max_right _ _).trans hm)
  obtain ⟨I,inst,hdata⟩ := hPart G m x y ((le_max_left _ _).trans hN) hCard hxy hRob
  letI := inst
  obtain ⟨f,R,l,_hk,hkMin,hkMax,hl,hx,hy,hEven,hF,hExc,hR,hPairs⟩ := hdata
  obtain ⟨S,hS,hSc,hSep,hSCells,hScCells,hDis⟩ :=
    hHalf G m l f x y ((le_max_left _ _).trans hm) hCard hxy (hx.trans hy.symm) hEven hF
  let A := if x ∈ S then S else Sᶜ
  have hA : A.card = m := by by_cases h : x ∈ S <;> simp [A,h,hS,hSc]
  have hAc : Aᶜ.card = m := by by_cases h : x ∈ S <;> simp [A,h,hS,hSc]
  have hxA : x ∈ A := by by_cases h : x ∈ S <;> simp [A,h]
  have hyA : y ∉ A := by
    by_cases h : x ∈ S
    · simpa [A,h] using hSep.mp h
    · have hh : y ∈ S := by by_contra hn; exact h (hSep.mpr hn)
      simp [A,h,hh]
  have hAB : ∀ i, (A ∩ cluster f i).card = l := by
    intro i
    by_cases h : x ∈ S <;> simp [A,h,hSCells i,hScCells i]
  have hBA : ∀ i, (Aᶜ ∩ cluster f i).card = l := by
    intro i
    by_cases h : x ∈ S <;> simp [A,h,hSCells i,hScCells i]
  have hDisA (v : V) : |(neighboursIn G A v:ℝ)-(neighboursIn G Aᶜ v:ℝ)| < ζ*(m:ℝ) := by
    by_cases h : x ∈ S
    · simpa [A,h] using hDis v
    · simpa [A,h,abs_sub_comm] using hDis v
  have hCount : 4 ≤ Fintype.card I := (le_max_left _ _).trans hkMin
  have hWindow : 4 ≤ τR*(Fintype.card I:ℝ) := by
    rw [mul_comm]
    apply (div_le_iff₀ hτR).mp
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hkMin)
  have hLarge : 2 ≤ δ*ρ^2*(m:ℝ)/128 := by
    have hh := (div_le_iff₀ (show 0 < δ*ρ^2/128 by positivity)).mp ((le_max_right _ _).trans hmReal)
    nlinarith only [hh]
  have hRound : (Fintype.card I:ℝ) ≤ ρ*(m:ℝ)/64 := by
    have hh := (div_le_iff₀ (show 0 < ρ/64 by positivity)).mp ((le_max_left _ _).trans hmReal)
    have hK : (Fintype.card I:ℝ) ≤ (K:ℝ) := by exact_mod_cast hkMax
    nlinarith only [hh,hK]
  have hExc' : ((exceptional f).card:ℝ) ≤ ρ*(m:ℝ)/32 := by
    rw [hCard] at hExc
    push_cast at hExc
    dsimp only [σ] at hExc
    nlinarith only [hExc]
  have hSides (B C : Finset V) (hB : B.card = m) (hC : C.card = m)
      (hBCells : ∀ i, (B ∩ cluster f i).card = l)
      (hCCells : ∀ i, (C ∩ cluster f i).card = l) :
      BipartiteRobustMargin.ExpandsTo G B C ⌈ρcut*(m:ℝ)⌉₊ ⌈4*τ*(m:ℝ)⌉₊ := by
    obtain ⟨a,b,ha,hb⟩ := exists_embeddings_of_equal_card B C (hB.trans hC.symm)
    have hReg (i j : I) (hij : R.Adj i j) :
        G.IsUniform (4*ε) (B ∩ cluster f i) (C ∩ cluster f j) ∧
        4*ε+δ ≤ (G.edgeDensity (B ∩ cluster f i) (C ∩ cluster f j):ℝ) := by
      obtain ⟨hUniform,hDense⟩ := hPairs i j hij
      have hi : ((cluster f i).card:ℝ) = 2*((B ∩ cluster f i).card:ℝ) := by
        rw [hF,hBCells,Nat.cast_mul]; norm_num
      have hj : ((cluster f j).card:ℝ) = 2*((C ∩ cluster f j).card:ℝ) := by
        rw [hF,hCCells,Nat.cast_mul]; norm_num
      have hεcap : 2*ε ≤ 1/2 := by linarith only [hεd,hd₁]
      have hNew := RegularPairNeighbourhood.uniform_on_half_subcells G hεcap hUniform
        inter_subset_right inter_subset_right hi.le hj.le
      have hw (c : ℝ) (hc : 0 ≤ c) : (2*c)*(2*ε) ≤ c := by
        have hh := mul_le_mul_of_nonneg_right hεcap (show 0 ≤ 2*c by positivity)
        nlinarith only [hh]
      have hDiff := hUniform inter_subset_right inter_subset_right
        (by rw [hi]; exact hw _ (Nat.cast_nonneg _))
        (by rw [hj]; exact hw _ (Nat.cast_nonneg _))
      rw [show 2*(2*ε) = 4*ε by ring] at hNew
      exact ⟨hNew,by dsimp only [δ]; linarith only [hDense,(abs_lt.mp hDiff).1,hεd,hd.le]⟩
    have hh := expands_to_of_regular_half_cells G a b B C ha hb f R l ρ τR (4*ε) δ
      (by omega) hρ hρ₁ hτR (by dsimp only [ρ,τR]; linarith only [hντ,hτ])
      hτRcap (by positivity) (by linarith only [hερ,hρ]) hδ hδ₁ hCount hWindow
      (by rwa [hB]) (by rwa [hB]) (by rwa [hB]) hBCells hCCells
      (fun i j hij => (hReg i j hij).1) (fun i j hij => (hReg i j hij).2) hR
    simpa only [hB,ρcut,show 2*τR = 4*τ by dsimp only [τR]; ring] using hh
  exact ⟨A,hA,hAc,hxA,hyA,hDisA,hSides A Aᶜ hA hAc hAB hBA,hSides Aᶜ A hAc hA hBA hAB⟩

theorem exists_balanced_robust_cut (ν τ ζ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτcap : τ ≤ 1/8) (hζ : 0 < ζ) :
    ∃ ρcut : ℝ, 0 < ρcut ∧ ρcut ≤ ν ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (x y : V),
        N ≤ Fintype.card V → Fintype.card V = 2*m → x ≠ y →
        RobustExpansion.IsRealRobust G ν τ →
        ∃ A : Finset V, A.card = m ∧ Aᶜ.card = m ∧ x ∈ A ∧ y ∉ A ∧
          (∀ v, |(neighboursIn G A v:ℝ)-(neighboursIn G Aᶜ v:ℝ)| < ζ*(m:ℝ)) ∧
          BipartiteRobustMargin.ExpandsTo G A Aᶜ ⌈ρcut*(m:ℝ)⌉₊ ⌈4*τ*(m:ℝ)⌉₊ ∧
          BipartiteRobustMargin.ExpandsTo G Aᶜ A ⌈ρcut*(m:ℝ)⌉₊ ⌈4*τ*(m:ℝ)⌉₊ := by
  obtain ⟨r,_,hr,hrν,h⟩ := exists_balanced_robust_cut_at_rate.{u} ν τ ζ hν hντ hτcap hζ
  exact ⟨r,hr,hrν,h⟩

end OverfullWork.CMSBalancedCut
