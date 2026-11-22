module

public import OverfullWork.CMSTheorem13
public import OverfullWork.CaoChenCriticalAverageProof
public import OverfullWork.Gate8JClosureTarget

@[expose] public section


/-! The reduction in §2.1 of Chen–McDonald–Shan. The total deficit
pays both for expansion via an induced dense core and for the
exceptional-set hypothesis of Theorem 1.3. -/
namespace OverfullWork.Gate8J

open Finset SimpleGraph RobustExpansion SparseDeficitCore CMSTrimmingRound
open scoped Classical

universe u

set_option maxHeartbeats 2400000 in
theorem cms_critical_exclusion : CriticalExclusion.{u} := by
  intro ε hε
  obtain ⟨τ,hτ,hCMS⟩ := cms_theorem_1_3.{u} (1/2) (by norm_num)
  obtain ⟨q,hq⟩ := exists_nat_gt (max (2:ℝ) (max (5/(16*ε)) (1/τ)))
  have hqNat : 2 ≤ q := by
    exact_mod_cast ((le_max_left (2:ℝ) _).trans hq.le)
  have hqPos : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqε : (5:ℝ) ≤ 16*(q:ℝ)*ε := by
    have h : 5/(16*ε) ≤ (q:ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hq.le
    have h' := (div_le_iff₀ (show (0:ℝ) < 16*ε by positivity)).mp h
    linarith only [h']
  have hqτ : 1/(q:ℝ) ≤ τ := by
    have h : 1/τ ≤ (q:ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans hq.le
    exact (div_le_iff₀ hqPos).mpr (by
      have h' := (div_le_iff₀ hτ).mp h
      linarith only [h'])
  let ν := 1/(4096*(q:ℝ)^2)
  obtain ⟨η,hη,NCMS,hCMS⟩ := hCMS ν (by positivity)
  let coefficient := min (1/(262144*(q:ℝ)^3)) (η^3)
  have hCoeff : 0 < coefficient := lt_min (by positivity) (by positivity)
  obtain ⟨D₀,hDeficit⟩ := CaoChenCriticalAverage.deficit_bound.{u} coefficient hCoeff
  let N := max (2*D₀) (max NCMS (4096*q^2))
  refine ⟨N,?_⟩
  intro V _ _ G _ hn hCritical _ hNo hDensity
  let n := Fintype.card V
  have hn₀ : 4096*q^2 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hq₀ : 0 < q := by omega
  have hnPos : 0 < n := (show 0 < 4096*q^2 by positivity).trans_le hn₀
  let : Nonempty V := Fintype.card_pos_iff.mp hnPos
  have hnReal : 0 < (n:ℝ) := by exact_mod_cast hnPos
  have hHalf : (1/2:ℝ)*(n:ℝ) ≤ (G.maxDegree:ℝ) := by
    have h := mul_nonneg hε.le hnReal.le
    linarith only [hDensity,h]
  have hnDelta : n ≤ 2*G.maxDegree := by
    exact_mod_cast (show (n:ℝ) ≤ 2*(G.maxDegree:ℝ) by linarith only [hHalf])
  have hD₀ : D₀ ≤ G.maxDegree := by
    have h : 2*D₀ ≤ n := (le_max_left _ _).trans hn
    omega
  have hDelta : (G.maxDegree:ℝ) ≤ n := by exact_mod_cast G.maxDegree_lt_card_verts.le
  have hMass : (totalDeficit G G.maxDegree:ℝ) ≤ coefficient*(n:ℝ)^2 := by
    calc
      _ ≤ coefficient*(G.maxDegree:ℝ)*n := hDeficit G hCritical hD₀
      _ ≤ coefficient*(n:ℝ)^2 := by
        rw [pow_two,←mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDelta hCoeff.le) hnReal.le
  have hBudget := hMass.trans (mul_le_mul_of_nonneg_right
    (show coefficient ≤ 1/(262144*(q:ℝ)^3) from min_le_left _ _) (sq_nonneg (n:ℝ)))
  let a := n/(8*q)
  let k := n/(4096*q^2)
  have hRob : IsRobustAt G (k+1) (a+k) :=
    (isRobustAt_of_quadratic_deficit_scale G ε hε q hqNat hqε hn₀ hDensity hBudget).2.2
  have hRadius : ν*(n:ℝ) ≤ ((k+1:ℕ):ℝ) := by
    have hDiv : n < (4096*q^2)*(k+1) := Nat.lt_mul_div_succ n (by positivity)
    unfold ν
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (show 0 < (4096:ℝ)*(q:ℝ)^2 by positivity)).mpr
    exact_mod_cast (show n ≤ (k+1)*(4096*q^2) from by rw [Nat.mul_comm]; exact hDiv.le)
  have hWindow : ((a+k:ℕ):ℝ) ≤ τ*(n:ℝ) := by
    have ha : 8*(q:ℝ)*(a:ℝ) ≤ n := by
      exact_mod_cast Nat.mul_div_le n (8*q)
    have hk : 4096*(q:ℝ)^2*(k:ℝ) ≤ n := by
      exact_mod_cast Nat.mul_div_le n (4096*q^2)
    have ha' : (q:ℝ)*(a:ℝ) ≤ (n:ℝ)/8 := by linarith only [ha]
    have hk' : (q:ℝ)*(k:ℝ) ≤ (n:ℝ)/8 := by
      have hq' : (1:ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
      have hScale := mul_le_mul_of_nonneg_right hq' (show 0 ≤ (q:ℝ)*(k:ℝ) by positivity)
      nlinarith only [hk,hScale]
    calc
      ((a+k:ℕ):ℝ) ≤ (n:ℝ)/(q:ℝ) := by
        apply (le_div_iff₀ hqPos).mpr
        push_cast
        linarith only [ha',hk',hnReal.le]
      _ ≤ τ*(n:ℝ) := by
        rw [←one_div_mul_eq_div]
        exact mul_le_mul_of_nonneg_right hqτ hnReal.le
  have hRealRobust := isRealRobust_of_integer G _ _ ν τ hRob hRadius hWindow
  let t := ⌊η*(n:ℝ)⌋₊
  have hRound : initialExceptionalSet G η = exceptions G G.maxDegree t := by
    ext v
    simp only [initialExceptionalSet,exceptions,mem_filter,mem_univ,true_and]
    change η*(n:ℝ) < (G.maxDegree:ℝ)-G.degree v ↔ G.degree v+t < G.maxDegree
    rw [←Nat.cast_sub (G.degree_le_maxDegree v),←Nat.floor_lt (by positivity)]
    omega
  have hTail : ((t:ℝ)+1)*((initialExceptionalSet G η).card:ℝ) ≤
      (totalDeficit G G.maxDegree:ℝ) := by
    rw [hRound]
    exact_mod_cast exception_count_le_mass G G.maxDegree t
  have hEtaMass := hMass.trans (mul_le_mul_of_nonneg_right
    (show coefficient ≤ η^3 from min_le_right _ _) (sq_nonneg (n:ℝ)))
  have hFew : ((initialExceptionalSet G η).card:ℝ) ≤ η^2*(n:ℝ) := by
    have hScale := mul_le_mul_of_nonneg_right (Nat.lt_floor_add_one (η*(n:ℝ))).le
      (Nat.cast_nonneg ((initialExceptionalSet G η).card) : (0:ℝ) ≤ _)
    apply (mul_le_mul_iff_of_pos_left (mul_pos hη hnReal)).mp
    calc
      _ ≤ _ := hScale.trans (hTail.trans hEtaMass)
      _ = _ := by ring
  have hSize : NCMS ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hUse := hCMS G hSize hHalf hRealRobust (fun _ _ h => Overfull.deg_add hCritical h)
    ⟨η,hη,le_rfl,hFew⟩
  exact hCritical.2.1 (hUse.mpr hNo)

/-- The fixed-margin criterion with the same target as Gate 8J. -/
theorem cms_above_half_goal : AboveHalfGoal.{u} :=
  aboveHalfGoal_iff_criticalExclusion.mpr cms_critical_exclusion

/-- Chen–McDonald–Shan, Theorem 1.4, with the paper's degree threshold. -/
theorem cms_theorem_1_4 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], N ≤ Fintype.card V →
      ((1+ε)/2)*(Fintype.card V:ℝ) ≤ (G.maxDegree:ℝ) →
      (G.EdgeColorable G.maxDegree ↔ ¬G.HasOverfullSubgraph) := by
  obtain ⟨N,hColour⟩ := cms_above_half_goal.{u} (ε/2) (by positivity)
  refine ⟨N,?_⟩
  intro V _ _ G _ hn hΔ
  have hMargin : (1/2:ℝ)+ε/2 = (1+ε)/2 := by ring
  exact hColour G hn (by rwa [hMargin])

end OverfullWork.Gate8J
