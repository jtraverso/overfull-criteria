module

public import OverfullWork.CMSSimpleStoppingProfiles
public import OverfullWork.CMSOddDeficitExtension

@[expose] public section


/-! The odd continuation of CMS Stage II Case 1.1, including both
parity extensions specified in the paper and the restriction of the
completed colouring to the actual stopping graph. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph RobustExpansion OddCutDeficit
open scoped Classical
universe u

set_option maxHeartbeats 3500000 in
theorem cms_colourable_of_odd_simple_with_degree_profiles (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
          let n := Fintype.card V
          let d := G.maxDegree
          N ≤ n → Odd n → α*(n:ℝ) ≤ (d:ℝ) →
          (∀ v,0 < G.degree v) →
          (∀ u v,G.degree u ≤ 2 → G.Adj u v → d+2 ≤ G.degree u+G.degree v) →
          ((∃ z : V,∀ v,v ≠ z → (d:ℝ)-6*η*(n:ℝ) ≤ (G.degree v:ℝ)) ∨
            (deficitMass G d univ:ℝ) ≤ (d:ℝ)+5*η*(n:ℝ)) →
          ¬G.HasOverfullSubgraph → IsRealRobust G ν τ → G.EdgeColorable d := by
  obtain ⟨σ,hσ,hUse⟩ := cms_colourable_of_even_simple_with_degree_profiles (α/2)
    (by positivity) (by linarith only [hα₁])
  let τ := min (σ/2) (α/32)
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτσ : τ ≤ σ/2 := min_le_left _ _
  have hτα : τ ≤ α/32 := min_le_right _ _
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨η₀,hη₀,hU⟩ := hUse (ν/2) (by positivity) (by linarith only [hντ,hτσ,hσ])
  let ηMax := min η₀ (α/24)
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  obtain ⟨N₀,hN⟩ := hU η hη (hηMax.trans (min_le_left _ _))
  obtain ⟨Q,hQ⟩ := exists_nat_ge (max (8/α) (max (4/ν) (2/τ)))
  refine ⟨max N₀ Q,?_⟩
  intro V _ _ G _ n d hn hOdd hDens hPos hWeak hDef hNo hRob
  have hQR : (Q:ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  have hRes := hQ.trans hQR
  have hαn : 8 ≤ α*(n:ℝ) := by
    have h := (div_le_iff₀ hα).mp ((le_max_left _ _).trans hRes)
    linarith only [h]
  have hνn : 4 ≤ ν*(n:ℝ) := by
    have h := (div_le_iff₀ hν).mp ((le_max_left _ _).trans ((le_max_right _ _).trans hRes))
    linarith only [h]
  have hτn : 2 ≤ τ*(n:ℝ) := by
    have h := (div_le_iff₀ hτ).mp ((le_max_right _ _).trans ((le_max_right _ _).trans hRes))
    linarith only [h]
  have hν₁ : ν ≤ 1 := by linarith only [hντ,hτα,hα₁]
  have hNonnegN : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hηTimes := mul_le_mul_of_nonneg_right (hηMax.trans (min_le_right _ _)) hNonnegN
  have hτTimes := mul_le_mul_of_nonneg_right hτα hNonnegN
  have hMin (v : V) : 2 ≤ G.degree v := by
    by_contra hh
    obtain ⟨w,hw⟩ := (G.degree_pos_iff_exists_adj v).mp (hPos v)
    have hBound := G.degree_le_maxDegree w
    have h := hWeak v w (by omega) hw
    omega
  let r := ⌈ν*(n:ℝ)⌉₊
  let t := ⌈τ*(n:ℝ)⌉₊
  have hr : 0 < r := Nat.ceil_pos.mpr (by linarith only [hνn])
  have hTUpper : (t:ℝ) < τ*(n:ℝ)+1 :=
    Nat.ceil_lt_add_one (by linarith only [hτn])
  have : Nonempty V := Fintype.card_pos_iff.mp (by obtain ⟨k,hk⟩ := hOdd; omega)
  have hException : ∃ z : V,∀ v,v ≠ z → max t 3 ≤ G.degree v := by
    rcases hDef with ⟨z,hz⟩ | hDeficit
    · refine ⟨z,fun v hv => max_le ?_ ?_⟩
      · have hh := hz v hv
        exact_mod_cast (show (t:ℝ) ≤ G.degree v by
          linarith only [hh,hDens,hαn,hηTimes,hτTimes,hTUpper])
      · have hh := hz v hv
        exact_mod_cast (show (3:ℝ) ≤ G.degree v by linarith only [hh,hDens,hαn,hηTimes])
    · let B := ⌊5*η*(n:ℝ)⌋₊
      have hB : (B:ℝ) ≤ 5*η*(n:ℝ) := Nat.floor_le (by positivity)
      have hBudget : deficitMass G d univ ≤ d+B := by
        have h := Nat.le_floor hDeficit
        rw [add_comm (d:ℝ),Nat.floor_add_natCast (by positivity : 0 ≤ 5*η*(n:ℝ))] at h
        simpa only [B,Nat.add_comm] using h
      have hGap : B+2*max t 3 < d+2 := by
        by_cases ht : 3 ≤ t
        · rw [max_eq_left ht]
          exact_mod_cast (show (B:ℝ)+2*t < d+2 by
            linarith only [hB,hTUpper,hτTimes,hηTimes,hDens,hαn])
        · have ht' : t ≤ 3 := by omega
          rw [max_eq_right ht']
          exact_mod_cast (show (B:ℝ)+2*3 < d+2 by linarith only [hB,hηTimes,hDens,hαn])
      exact one_low_degree_of_global_deficit_budget G B (max t 3) hBudget hGap
  obtain ⟨z,hz⟩ := hException
  have hOrd (v : V) (hv : v ≠ z) : 3 ≤ G.degree v := (le_max_right _ _).trans (hz v hv)
  have hOrdT (v : V) (hv : v ≠ z) : t ≤ G.degree v := (le_max_left _ _).trans (hz v hv)
  have hD : 2 ≤ d := (hMin z).trans (G.degree_le_maxDegree _)
  have hRobI : IsRobustAt G r t := integer_robust_of_real G ν τ hν.le hRob
  have hExtendedOrder : Fintype.card (Option V) = n+1 := Fintype.card_option
  have hExtendedEven : Even (Fintype.card (Option V)) := OddTwoEdgeExtension.even_order hOdd
  have hExtendedDensity : (α/2)*(Fintype.card (Option V):ℝ) ≤ (d:ℝ) := by
    rw [hExtendedOrder,Nat.cast_add,Nat.cast_one]
    linarith only [hDens,hαn,hα₁]
  have hRScale : (ν/2)*(Fintype.card (Option V):ℝ) ≤ ((r-1:ℕ):ℝ) := by
    rw [hExtendedOrder,Nat.cast_add,Nat.cast_one,Nat.cast_sub hr,Nat.cast_one]
    have h := Nat.le_ceil (ν*(n:ℝ))
    change ν*(n:ℝ) ≤ (r:ℝ) at h
    linarith only [h,hνn,hν₁]
  have hTScale : ((t+1:ℕ):ℝ) ≤ σ*(Fintype.card (Option V):ℝ) := by
    rw [hExtendedOrder,Nat.cast_add,Nat.cast_one,Nat.cast_add,Nat.cast_one]
    have hh := mul_le_mul_of_nonneg_right hτσ hNonnegN
    linarith only [hh,hTUpper,hτn,hσ]
  have hFinish (H : SimpleGraph (Option V)) [DecidableRel H.Adj]
      (C : Copy G H) (hOld : ∀ u v,G.Adj u v → H.Adj (some u) (some v))
      (hMax : H.maxDegree = d) (hDeg : ∀ v,G.degree v ≤ H.degree (some v))
      (hNoH : ¬H.HasOverfullSubgraph)
      (hBudget : ∀ p : Option V,(∀ v,H.degree p ≤ H.degree v) →
        (∑ v ∈ univ.erase p,(H.maxDegree-H.degree v))+H.degree p = deficitMass G d univ)
      (hLocal : ∀ p q : Option V,p ≠ q → (∀ v,H.degree p ≤ H.degree v) →
        (∀ v,v ≠ p → H.degree q ≤ H.degree v) → ((H.neighborFinset p).erase q).card ≤ 1 →
          (∃ w : Option V,w ≠ p ∧ w ≠ q ∧ H.degree w < H.maxDegree ∧
            ∀ v,v ∉ ({p,q,w}:Finset (Option V)) → H.degree v = H.maxDegree) ∨
          ∀ v,v ≠ p → v ≠ q → H.maxDegree ≤ OddCutDeficit.cutEdges H {p,q,v}) :
      G.EdgeColorable d := by
    have hRobH : IsRealRobust H (ν/2) σ := isRealRobust_of_integer H (r-1) (t+1)
      (ν/2) σ (robust_after_one_added_vertex G H hOld r t hr hRobI) hRScale hTScale
    have hProfile :
        (∃ x y : Option V,∀ v,v ≠ x → v ≠ y →
          (H.maxDegree:ℝ)-6*η*(Fintype.card (Option V):ℝ) ≤ H.degree v) ∨
        ∀ p : Option V,(∀ v,H.degree p ≤ H.degree v) →
          ((∑ v ∈ univ.erase p,(H.maxDegree-H.degree v))+H.degree p : ℕ) ≤
            (H.maxDegree:ℝ)+5*η*(Fintype.card (Option V):ℝ) := by
      rcases hDef with ⟨z',hz'⟩ | hDeficit
      · left
        refine ⟨none,some z',?_⟩
        intro v hx hy
        cases v with
        | none => exact (hx rfl).elim
        | some v =>
          rw [hMax,hExtendedOrder,Nat.cast_add,Nat.cast_one]
          have hh := hz' v (fun h => hy (congrArg some h))
          have hdV : (G.degree v:ℝ) ≤ H.degree (some v) := by exact_mod_cast hDeg v
          linarith only [hh,hdV,hη]
      · right
        intro p hp
        rw [hBudget p hp,hMax,hExtendedOrder,Nat.cast_add,Nat.cast_one]
        linarith only [hDeficit,hη]
    have hColour := hN H (by rw [hExtendedOrder]; exact ((le_max_left _ _).trans hn).trans (Nat.le_succ _))
      hExtendedEven (by rwa [hMax]) hProfile hLocal hNoH hRobH
    rw [hMax] at hColour
    exact Critical.colourable_of_copy C hColour
  by_cases hThree : 3 ≤ (univ.filter fun v => G.degree v < G.maxDegree).card
  · obtain ⟨a,b,c,hab,hca,hcb,ha,hb,hcA,hcB⟩ := exists_two_deficient_attachments G hThree
    refine hFinish (OddTwoEdgeExtension.extension G a b) (OddTwoEdgeExtension.oldCopy G a b)
      (fun _ _ h => h) (OddTwoEdgeExtension.maxDegree_eq G a b hab hD ha hb) ?_
      (odd_two_edge_extension_no_overfull_of_robust G a b z hab hOdd hD ha hb hNo r t hr hRobI hPos hOrdT)
      (odd_two_edge_extension_preserves_first_vertex_budget G a b hab hD ha hb hMin) ?_
    · intro v
      rw [OddTwoEdgeExtension.degree_old]
      exact Nat.le_add_right _ _
    · intro p q hpq hp hq hSmall
      have hh := two_edge_extension_smallest_pair_has_two_other_neighbours G a b c z hab hca hcb
        hMin hOrd hcA hcB p q hpq hp hq
      omega
  · have hTwo := two_deficient_of_odd_no_overfull G hOdd hPos hNo
    have hExactly : (univ.filter fun v => G.degree v < G.maxDegree).card = 2 := by omega
    refine hFinish (isolatedStoppingExtension G) (isolatedStoppingCopy G)
      (fun u v => (isolated_stopping_extension_adj_old G u v).mpr)
      (isolated_stopping_extension_maxDegree G)
      (fun v => (isolated_stopping_extension_degree_old G v).ge)
      (isolated_stopping_extension_no_overfull G hNo)
      (isolated_extension_preserves_first_vertex_budget G hPos) ?_
    intro p q hpq hp hq _
    exact Or.inl (isolated_stopping_extension_three_deficient G hPos hExactly p q hpq hp hq)

theorem cms_colourable_of_odd_dense_simple_stop (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 < η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
          let n := Fintype.card V
          let d := G.maxDegree
          N ≤ n → Odd n → α*(n:ℝ) ≤ (d:ℝ) →
          (∀ v,0 < G.degree v) →
          (∀ u v,G.degree u ≤ 2 → G.Adj u v → d+2 ≤ G.degree u+G.degree v) →
          (∃ z : V,∀ v,v ≠ z → (d:ℝ)-6*η*(n:ℝ) ≤ (G.degree v:ℝ)) →
          ¬G.HasOverfullSubgraph → IsRealRobust G ν τ → G.EdgeColorable d := by
  obtain ⟨τ,hτ,hUse⟩ := cms_colourable_of_odd_simple_with_degree_profiles α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨ηMax,hηMax,hUse⟩ := hUse ν hν hντ
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηMax
  obtain ⟨N,hN⟩ := hUse η hη hηMax
  refine ⟨N,?_⟩
  intro V _ _ G _ n d hn hOdd hDens hPos hWeak hOrd hNo hRob
  exact hN G hn hOdd hDens hPos hWeak (Or.inl hOrd) hNo hRob

end OverfullWork.CanonicalRegularization
