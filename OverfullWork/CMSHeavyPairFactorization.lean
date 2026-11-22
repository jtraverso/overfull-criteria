module

public import OverfullWork.CMSHeavyPairScale
public import OverfullWork.RobustHeavyPairRemainder
public import OverfullWork.OrdinaryParallelMatchingPartition

@[expose] public section


/-! Assemble the heavy branch of CMS §5.2 from the two ordinary
simple-degree profiles and global robustness. -/
namespace OverfullWork.HeavyPairPeeling
open Finset SimpleGraph MultiGraph HeavyPairBoundary RobustExpansion
open scoped Classical
universe u

/-- Removing the two centres absorbs their contribution to the excess.
The loss of one comes from retaining the simple copy at the first centre. -/
theorem Certificate.ordinary_excess_le_of_simple_profile
    {V : Type u} [Fintype V] [DecidableEq V]
    {M : MultiGraph V} {d q : ℕ} {a b : V}
    (c : Certificate M d q a b) (hab : a ≠ b)
    (hReg : M.IsRegularOfDegree d) (err : ℝ) (x : outside a b)
    (hProfile : (d:ℝ)-(M.mult s(a,x.val):ℝ)-err ≤ (M.supportGraph.degree x.val:ℝ)) :
    ((ordinary c.residual a b).parallelExcess x:ℝ) ≤ err+1 := by
  have hSum := congrArg (fun Q : MultiGraph V => Q.degree x.val) M.simple_add_parallelCopies
  rw [degree_addCopies,degree_ofSimpleGraph,degree_parallelCopies,hReg] at hSum
  let f := fun y => M.mult s(x.val,y)-1
  have hDecomp := sum_outside_add f a b hab
  have hOrd :
      (ordinary c.residual a b).parallelExcess x ≤ ∑ w : outside a b, f w.val := by
    apply sum_le_sum
    intro y _
    rw [ordinary_mult]
    exact Nat.sub_le_sub_right (Nat.sub_le _ _) _
  have hBound :
      (ordinary c.residual a b).parallelExcess x + (M.mult s(a,x.val)-1) ≤
        M.parallelExcess x.val := by
    change _ + _ + _ = M.parallelExcess x.val at hDecomp
    rw [show s(a,x.val) = s(x.val,a) from Sym2.eq_swap]
    have ha : f a = M.mult s(x.val,a)-1 := rfl
    omega
  have hr :
      ((ordinary c.residual a b).parallelExcess x:ℝ)+((M.mult s(a,x.val)-1:ℕ):ℝ) ≤
        (M.parallelExcess x.val:ℝ) := by exact_mod_cast hBound
  have hMult : (M.mult s(a,x.val):ℝ) ≤ ((M.mult s(a,x.val)-1:ℕ):ℝ)+1 := by
    exact_mod_cast (show M.mult s(a,x.val) ≤ (M.mult s(a,x.val)-1)+1 by omega)
  have hSumR : (M.supportGraph.degree x.val:ℝ)+(M.parallelExcess x.val:ℝ) = (d:ℝ) := by
    exact_mod_cast hSum
  linarith only [hProfile,hSumR,hr,hMult]

set_option maxHeartbeats 2300000 in
/-- Factorize the heavy branch with explicit margins on the small
boundary, using the profiles corresponding to CMS 4.2(1b–c). -/
theorem cms_heavy_pair_colourable
    (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ → ∃ ηMax : ℝ, 0 < ηMax ∧
      ∀ η : ℝ, η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (M : MultiGraph V) (d : ℕ) (a b : V), a ≠ b →
          N ≤ Fintype.card V → Even (Fintype.card V) →
          M.IsRegularOfDegree d → ¬ M.HasOverfullSubset d →
          α*(Fintype.card V:ℝ) ≤ (d:ℝ) → IsRealRobust M.supportGraph ν τ →
          ((d-M.mult s(a,b):ℕ):ℝ) ≤ (min ν α/32)*(Fintype.card V:ℝ) →
          (∀ x : outside a b, (d:ℝ)/2-6*η*(Fintype.card V:ℝ) ≤ (M.supportGraph.degree x.val:ℝ)) →
          (∀ x : outside a b, (d:ℝ)-(M.mult s(a,x.val):ℝ)-6*η*(Fintype.card V:ℝ) ≤
            (M.supportGraph.degree x.val:ℝ)) →
          Nonempty (M.EdgeColoring d) := by
  obtain ⟨τ₀,hτ₀,hOrd⟩ := EvenHamiltonFactorization.robust_regular_multigraph_colourable_small_parallel_excess.{u}
    (α/2) (by positivity) (by linarith only [hα₁])
  let τ := min (τ₀/2) (α/2048)
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have hτ₁ : 2*τ ≤ τ₀ := by linarith only [(min_le_left _ _ : τ ≤ τ₀/2)]
  have hτ₂ : 2048*τ ≤ α := by linarith only [(min_le_right _ _ : τ ≤ α/2048)]
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨ε,hε,N₀,hN₀⟩ := hOrd (ν/8) (by positivity)
  let ηMax := min (α/96) (ε/24)
  have hηMax : 0 < ηMax := lt_min (by positivity) (by positivity)
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη
  have hηα : 96*η ≤ α := by linarith only [hη.trans (min_le_left _ _ : ηMax ≤ α/96)]
  have hηε : 6*η ≤ ε/4 := by linarith only [hη.trans (min_le_right _ _ : ηMax ≤ ε/24)]
  obtain ⟨N₁,hN₁⟩ := exists_certificate_of_heavy_pair_profile.{u} α ν τ η hα hα₁ hν hντ hτ₂ hηα
  obtain ⟨N₂,hN₂⟩ := exists_nat_ge (max (4/ε) (4/ν))
  refine ⟨max 4 (max N₁ (max (N₀+2) N₂)),?_⟩
  intro V _ _ M d a b hab hN hEven hReg hNo hDegree hRob hHeavy hRank hProfile
  have hTail : max N₁ (max (N₀+2) N₂) ≤ Fintype.card V := (le_max_right _ _).trans hN
  obtain ⟨c⟩ := hN₁ M d a b hab ((le_max_left _ _).trans hTail)
    hEven hReg hNo hDegree hRob hHeavy hRank
  let q := d-M.mult s(a,b)
  let n := Fintype.card V
  let S := outside a b
  let W := ↥(outside a b)
  let R := ordinary c.residual a b
  have hS : Fintype.card W+2 = n := card_outside a b hab
  have hSR : (S.card:ℝ)+2 = (n:ℝ) := by exact_mod_cast (show S.card+2=n by simpa only [W,Fintype.card_coe] using hS)
  have hW : (n:ℝ)/2 ≤ (S.card:ℝ) := by
    have h₄ : (4:ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hN
    linarith only [h₄,hSR]
  have hN₀W : N₀ ≤ Fintype.card W := by
    have h := (le_max_left _ _).trans ((le_max_right _ _).trans hTail)
    change N₀ + 2 ≤ n at h
    omega
  have hN₂n : (N₂:ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hTail)
  have hPayν : 4 ≤ ν*(n:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hν).mp ((le_max_right _ _).trans (hN₂.trans hN₂n))
  have hPayε : 4 ≤ ε*(n:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hε).mp ((le_max_left _ _).trans (hN₂.trans hN₂n))
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hqν : (q:ℝ) ≤ (ν/32)*(n:ℝ) := hHeavy.trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)) hn)
  have hqα : (q:ℝ) ≤ (α/32)*(n:ℝ) := hHeavy.trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) hn)
  have hNsub : (S.card:ℝ) ≤ n := by linarith only [hSR]
  have hDelete : (univ \ S).card = 2 := by simp [S,outside,sdiff_eq_inter_compl,card_pair hab]
  have hCoreRob : IsRealRobust (M.supportGraph.induce (S : Set V)) (ν/4) (2*τ) := by
    apply isRealRobust_induce_with_loss M.supportGraph S ν (ν/4) τ (2*τ) _ _ hRob
    · nlinarith only [mul_le_mul_of_nonneg_left hW hτ.le]
    · rw [hDelete]
      push_cast
      nlinarith only [hPayν,mul_le_mul_of_nonneg_left hNsub hν.le]
  have hOrdRob : IsRealRobust R.supportGraph (ν/8) τ₀ :=
    c.ordinary_robust (ν/4) (ν/8) (2*τ) τ₀ (by linarith only [hν]) hτ₁
      (by nlinarith only [hqν,mul_le_mul_of_nonneg_left hW hν.le]) hCoreRob
  have hOrdEven : Even (Fintype.card W) := by
    obtain ⟨k,hk⟩ := hEven
    exact ⟨k-1,by omega⟩
  have hOrdDegree : (α/2)*(Fintype.card W:ℝ) ≤ ((d-2*q:ℕ):ℝ) := by
    have hc : 2*q ≤ d := by
      exact_mod_cast (show (2:ℝ)*(q:ℝ) ≤ d by nlinarith only [hqα,hDegree,mul_nonneg hα.le hn])
    rw [show Fintype.card W=S.card from Fintype.card_coe _,Nat.cast_sub hc]
    push_cast
    nlinarith only [hDegree,hqα,mul_le_mul_of_nonneg_left hNsub hα.le,mul_nonneg hα.le hn]
  have hExcess (x : W) : (R.parallelExcess x:ℝ) ≤ ε*(Fintype.card W:ℝ) := by
    have h := c.ordinary_excess_le_of_simple_profile hab hReg (6*η*(n:ℝ)) x (hProfile x)
    rw [show Fintype.card W=S.card from Fintype.card_coe _]
    nlinarith only [h,hPayε,mul_le_mul_of_nonneg_right hηε hn,mul_le_mul_of_nonneg_left hW hε.le]
  obtain ⟨C⟩ := hN₀ R (d-2*q) hN₀W hOrdEven hOrdDegree (c.ordinary_regular hab) hOrdRob hExcess
  exact c.colouring_of_ordinary hab hReg rfl C

end OverfullWork.HeavyPairPeeling
