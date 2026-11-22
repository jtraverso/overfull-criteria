module

public import OverfullWork.CMSTwoCentreSourceProfiles
public import OverfullWork.CMSRegularizationImageTransport

@[expose] public section


/-! Colour the actual cleaned source of CMS Subcase 2.4. Robustness
and no-overfullness of the two-group quotient are both conclusions. -/
namespace OverfullWork.TwoIndependentIdentifications

open Finset SimpleGraph RobustExpansion CanonicalRegularization
open scoped Classical
universe u

set_option maxHeartbeats 1800000 in
theorem cms_colourable_of_two_centre_stop (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ σ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 ≤ η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
          (Z A : Finset V) (hA : A ⊆ Z) (hInd : G.IsIndepSet (Z : Set V)),
          let M := graph G Z A hA hInd
          let m := Fintype.card (Vertices Z)
          let d := G.maxDegree
          let F := ∑ x : Outside Z, (d-G.degree x.val)
          N ≤ m → α*(m:ℝ) ≤ (d:ℝ) → Even m →
          2 ≤ Z.card → (Z.card:ℝ) ≤ 2*η^2*(m:ℝ) →
          (∀ j : Bool, (M.degree (Sum.inl j):ℝ) ≤ 10*η*(m:ℝ)) →
          M.degree (Sum.inl false) ≤ M.degree (Sum.inl true) →
          M.degree (Sum.inl true) ≤ M.degree (Sum.inl false)+F →
          (F:ℝ) ≤ 6*η*(m:ℝ) →
          (∀ x : Outside Z, (d:ℝ)-5*η*(m:ℝ) ≤ (G.degree x.val:ℝ)) →
          (∀ u ∈ Z, ∀ v, G.Adj u v → d+2 ≤ G.degree u+G.degree v) →
          ¬G.HasOverfullSubgraph → IsRealRobust G ν σ →
          G.EdgeColorable d := by
  obtain ⟨τ,hτ,hUse⟩ := cms_colourable_of_clean_two_identifications.{u} α hα hα₁
  let σ := min (τ/2) (α/128)
  have hσ : 0 < σ := lt_min (by positivity) (by positivity)
  have hστ : 2*σ ≤ τ := by
    have h := min_le_left (τ/2) (α/128)
    linarith only [h]
  have hσα : σ ≤ α/128 := min_le_right _ _
  have hσHalf : σ ≤ 1/2 := by linarith only [hσα,hα₁]
  refine ⟨σ,hσ,?_⟩
  intro ν hν hνσ
  have hντ : ν/2 ≤ τ := by linarith only [hνσ,hστ,hσ]
  obtain ⟨η₀,hη₀,hUseColour⟩ := hUse (ν/2) (by positivity) hντ
  let ηMax := min η₀ (min (ν/16) (α/512))
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  obtain ⟨N₀,hColour⟩ := hUseColour η hη (hηMax.trans (min_le_left _ _))
  have hην : η ≤ ν/16 := (hηMax.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hηα : η ≤ α/512 := (hηMax.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hHalf : η ≤ 1/2 := by linarith only [hηα,hα₁]
  obtain ⟨N₁,hN₁⟩ := exists_nat_ge (max (1/(ν/2)^2) (max (4/σ) (max (8/ν) (32/α))))
  refine ⟨max N₀ N₁,?_⟩
  intro V _ _ G _ Z A hA hInd M m d F hN hDensity hEven hZ hZSize hLow hOrder hBalance
    hDef hDeg hWeak hNo hRob
  let n := Fintype.card V
  have hm₀ : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  have hηm := mul_le_mul_of_nonneg_right hηα hm₀
  have hσm := mul_le_mul_of_nonneg_right hσα hm₀
  have hαm := mul_le_mul_of_nonneg_right hα₁ hm₀
  have hηmν := mul_le_mul_of_nonneg_right hην hm₀
  have hηmHalf := mul_le_mul_of_nonneg_right hHalf hm₀
  have hZLin : (Z.card:ℝ) ≤ η*(m:ℝ) := by
    have hηQuad := mul_nonneg hη (sub_nonneg.mpr hHalf)
    exact hZSize.trans (mul_le_mul_of_nonneg_right (show 2*η^2 ≤ η by nlinarith only [hηQuad]) hm₀)
  have hN₁m : (N₁:ℝ) ≤ m := by exact_mod_cast (le_max_right _ _).trans hN
  have hReserves := hN₁.trans hN₁m
  have hSquare : 1 ≤ (ν/2)^2*(m:ℝ) := by
    have h := (div_le_iff₀ (show 0 < (ν/2)^2 by positivity)).mp ((le_max_left _ _).trans hReserves)
    linarith only [h]
  have hσLarge : 4 ≤ σ*(m:ℝ) := by
    have h := (div_le_iff₀ hσ).mp ((le_max_left _ _).trans ((le_max_right _ _).trans hReserves))
    linarith only [h]
  have hνLarge : 8 ≤ ν*(m:ℝ) := by
    have h := (div_le_iff₀ hν).mp ((le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hReserves)))
    linarith only [h]
  have hαLarge : 32 ≤ α*(m:ℝ) := by
    have h := (div_le_iff₀ hα).mp ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hReserves)))
    linarith only [h]
  have hCard : m+Z.card = n+2 := by
    have hh := card_add_card_compl Z
    change m+Z.card = Fintype.card V+2
    dsimp only [m]
    rw [card_vertices]
    omega
  have hmn : m ≤ n := by omega
  have hCardN : (n:ℝ) ≤ m+Z.card := by exact_mod_cast (show n ≤ m+Z.card by omega)
  have hLength : σ*(n:ℝ)+2 ≤ (2*σ)*(m:ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_left hCardN hσ.le
    have h₂ := mul_le_mul_of_nonneg_left (hZLin.trans hηmHalf) hσ.le
    linarith only [h₁,h₂,hσLarge]
  have hLoss : (Z.card:ℝ)+2 ≤ (ν/2)*(n:ℝ) := by
    have hnn : (m:ℝ) ≤ n := by exact_mod_cast hmn
    have h := mul_le_mul_of_nonneg_left hnn (by positivity : (0:ℝ) ≤ ν/2)
    linarith only [hZLin,hηmν,hνLarge,h]
  have hRobM := real_robust_two_identifications G Z A hA hInd ν σ hν.le hσ.le hσHalf hZ hLength hLoss hRob
  have hOut : (Fintype.card (Outside Z):ℝ)+2 = m := by
    exact_mod_cast (show Fintype.card (Outside Z)+2 = m by
      dsimp only [m,Vertices]
      rw [Fintype.card_sum,Fintype.card_bool,Nat.add_comm])
  have hBudget : F+M.degree (Sum.inl false)+M.degree (Sum.inl true) <
      Fintype.card (Outside Z) := by
    apply (Nat.cast_lt (α := ℝ)).mp
    push_cast
    linarith only [hDef,hLow false,hLow true,hηm,hαm,hαLarge,hOut]
  have hStrict : d < m := maxDegree_lt_quotient_order_of_budget G Z A hA hInd hBudget
  have hSupport (x : Outside Z) :
      (d:ℝ)-6*η*(m:ℝ) ≤ (M.supportGraph.degree (Sum.inr x):ℝ) := by
    have hh : (G.degree x.val:ℝ) ≤ (M.supportGraph.degree (Sum.inr x):ℝ)+Z.card := by
      exact_mod_cast support_degree_loss_at_ordinary G Z A hA hInd x
    linarith only [hh,hZLin,hDeg x]
  let r := ⌈(ν/2)*(m:ℝ)⌉₊
  let t := ⌈(2*σ)*(m:ℝ)⌉₊
  have hRate : d ≤ r*r := by
    have hCeil : (ν/2)*(m:ℝ) ≤ (r:ℝ) := Nat.le_ceil _
    have hSquare' := mul_le_mul hCeil hCeil (by positivity : 0 ≤ (ν/2)*(m:ℝ)) (Nat.cast_nonneg (α := ℝ) r)
    have hGrow := mul_le_mul_of_nonneg_right hSquare hm₀
    have hD : (d:ℝ) ≤ m := by exact_mod_cast hStrict.le
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    nlinarith only [hSquare',hGrow,hD]
  have hPair (x y : Outside Z) (_hxy : x ≠ y) :
      d+2*t ≤ M.supportGraph.degree (Sum.inr x)+M.supportGraph.degree (Sum.inr y) := by
    have hCeil : (t:ℝ) < (2*σ)*(m:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    linarith only [hSupport x,hSupport y,hCeil,hαLarge,hσm,hDensity,hηm]
  have hSum : M.degree (Sum.inl false)+M.degree (Sum.inl true) ≤ d := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    linarith only [hLow false,hLow true,hηm,hDensity,hαLarge]
  have hMin (x : Outside Z) : M.degree (Sum.inl false) ≤ G.degree x.val := by
    apply (Nat.cast_le (α := ℝ)).mp
    linarith only [hLow false,hDeg x,hηm,hDensity,hαLarge]
  have hRobI : IsRobustAt M.supportGraph r t :=
    integer_robust_of_real M.supportGraph (ν/2) (2*σ) (by positivity) hRobM
  have hNoM : ¬M.HasOverfullSubset d := no_overfull_two_identifications_of_robust
    G Z A hA hInd r t hEven hNo hRobI hRate hPair hSum hMin hOrder hBalance
  have hRob' : IsRealRobust M.supportGraph (ν/2) τ := by
    intro S hlo hhi
    have h := mul_le_mul_of_nonneg_right hστ hm₀
    exact hRobM S (h.trans hlo) (by linarith only [h,hhi])
  exact hColour G Z A hA hInd ((le_max_left _ _).trans hN) hStrict hDensity hEven hZSize hLow hSupport hWeak hNoM hRob'

end OverfullWork.TwoIndependentIdentifications
