module

public import OverfullWork.RobustHeavyPairPeeling

@[expose] public section


/-! The ambient hypotheses that pay for the first cycle removals
of the heavy branch of CMS Theorem 4.2. -/
namespace OverfullWork.HeavyPairPeeling
open Finset SimpleGraph HeavyPairBoundary RobustExpansion
open scoped Classical
universe u

/-- The degree profile on vertices other than the heavy pair and the
small boundary size suffice to pay the size, robustness and copy
budgets of the initial Case 1 peeling. -/
theorem exists_certificate_of_heavy_pair_profile
    (α ν τ η : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτ : 2048*τ ≤ α) (hη : 96*η ≤ α) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] (M : MultiGraph V) (d : ℕ)
      (a b : V) (hab : a ≠ b),
      let n := Fintype.card V
      let q := d-M.mult s(a,b)
      N ≤ n → Even n → M.IsRegularOfDegree d → ¬ M.HasOverfullSubset d →
      α*(n:ℝ) ≤ (d:ℝ) → IsRealRobust M.supportGraph ν τ →
      (q:ℝ) ≤ (min ν α/32)*(n:ℝ) →
      (∀ x : outside a b, (d:ℝ)/2-6*η*(n:ℝ) ≤ (M.supportGraph.degree x.val:ℝ)) →
      Nonempty (Certificate M d q a b) := by
  obtain ⟨N₁,hN₁⟩ := exists_robust_certificate.{u} (ν/8) (2*τ) (α/4)
    (by positivity) (by linarith only [hν,hντ]) (by linarith only [hτ])
    (by linarith only [hα₁])
  obtain ⟨N₂,hN₂⟩ := exists_nat_ge (max (4/ν) (16/α))
  refine ⟨max 4 (max (N₁+2) N₂),?_⟩
  intro V _ _ M d a b hab n q hN hEven hReg hNo hDeg hRob hSmall hProfile
  let S := outside a b
  let G := M.supportGraph.induce (S : Set V)
  have hCard : S.card+2 = n := by
    rw [←Fintype.card_coe S]
    exact card_outside a b hab
  have hCardR : (S.card:ℝ)+2 = (n:ℝ) := by exact_mod_cast hCard
  have h₄ : 4 ≤ n := (le_max_left _ _).trans hN
  have h₄R : (4:ℝ) ≤ n := by exact_mod_cast h₄
  have hN₁' : N₁+2 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂' : N₂ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hPay := hN₂.trans (show (N₂:ℝ) ≤ n by exact_mod_cast hN₂')
  have hμ : 4 ≤ ν*(n:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hν).mp ((le_max_left _ _).trans hPay)
  have hαn : 16 ≤ α*(n:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hα).mp ((le_max_right _ _).trans hPay)
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hS : (n:ℝ)/2 ≤ S.card := by linarith only [h₄R,hCardR]
  have hLoss : (q:ℝ) ≤ (ν/32)*(n:ℝ) := hSmall.trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)) hn)
  have hLoss' : (q:ℝ) ≤ (α/32)*(n:ℝ) := hSmall.trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) hn)
  have hClose : q ≤ M.mult s(a,b) := by
    have hk := M.mult_pair_le_degree a b
    rw [hReg a] at hk
    have eq : (q:ℝ)+(M.mult s(a,b):ℝ) = (d:ℝ) := by
      exact_mod_cast (show q+M.mult s(a,b)=d by dsimp only [q]; omega)
    exact_mod_cast (show (q:ℝ) ≤ M.mult s(a,b) by nlinarith only [eq,hDeg,hLoss'])
  have hDelete : (univ \ S).card = 2 := by simp [S,outside,sdiff_eq_inter_compl,card_pair hab]
  have hRob' : IsRealRobust G (2*(ν/8)) (2*τ) := by
    apply isRealRobust_induce_with_loss M.supportGraph S ν (2*(ν/8)) τ (2*τ) _ _ hRob
    · nlinarith only [mul_le_mul_of_nonneg_left hS (show 0 ≤ τ by linarith only [hντ,hν])]
    · rw [hDelete]
      push_cast
      nlinarith only [hμ,mul_le_mul_of_nonneg_left (show (S.card:ℝ) ≤ n by linarith only [hCardR]) hν.le]
  have hN₁S : N₁ ≤ Fintype.card ↥(outside a b) := by rw [Fintype.card_coe]; change N₁ ≤ S.card; omega
  refine hN₁ M d a b hab hN₁S hEven hReg hNo hRob' (fun x => ?_) ?_ hClose
  · let e : (↥(S : Set V)) ↪ V := Function.Embedding.subtype _
    have hMap : (G.neighborFinset x).map e =
        M.supportGraph.neighborFinset x.val \ ({a,b} : Finset V) := by
      ext y
      simp only [mem_map,mem_neighborFinset,mem_sdiff]
      constructor
      · rintro ⟨w,hw,rfl⟩
        refine ⟨hw,?_⟩
        change w.val ∉ ({a,b} : Finset V)
        exact Finset.mem_compl.mp w.property
      · rintro ⟨hy,hout⟩
        have hS' : y ∈ S := by simpa [S,outside] using hout
        exact ⟨⟨y,hS'⟩,hy,rfl⟩
    have hEq := congrArg Finset.card hMap
    rw [card_map,card_neighborFinset_eq_degree] at hEq
    have hOld := card_le_card_sdiff_add_card (s := M.supportGraph.neighborFinset x.val)
      (t := ({a,b} : Finset V))
    rw [card_neighborFinset_eq_degree,← hEq,card_pair hab] at hOld
    have hOldR : (M.supportGraph.degree x.val:ℝ) ≤ (G.degree x:ℝ)+2 := by exact_mod_cast hOld
    rw [Fintype.card_coe]
    exact (show (α/4)*(S.card:ℝ)+2*(q:ℝ) ≤ (G.degree x:ℝ) by
      nlinarith only [hProfile x,hOldR,hCardR,hDeg,hαn,hLoss',
        mul_le_mul_of_nonneg_right hη hn,hα])
  · rw [Fintype.card_coe]
    exact (show 2*(q:ℝ) ≤ (ν/8)*(S.card:ℝ) by
      nlinarith only [hLoss,mul_le_mul_of_nonneg_left hS hν.le])

end OverfullWork.HeavyPairPeeling
