module

public import OverfullWork.CMSCaseTwoSeedCompletion
public import OverfullWork.DynamicBudgetMargins
public import OverfullWork.FixedLayerRoundScales

@[expose] public section


/-! Uniform reserves for the alternating-path iteration at positive
relative degree, using the existing dynamic-budget estimates. -/
namespace OverfullWork.CMSBalancedCut

open NormalizedCanonicalCandidate
open scoped Classical

set_option maxHeartbeats 1200000 in
theorem exists_completion_scales (ρ α : ℝ) (hρ : 0 < ρ) (hα : 0 < α) :
    ∃ γ δ : ℝ, 0 < γ ∧ γ ≤ ρ ∧ 0 < δ ∧ ∃ ell N : ℕ,
      ∀ (m d r t e : ℕ) (ξ B A loss : ℝ), N ≤ m →
        ρ*(m:ℝ) ≤ (r:ℝ) → 2*α*(m:ℝ) ≤ (d:ℝ) →
        (t:ℝ) ≤ α*(m:ℝ)/8 → loss ≤ α*(m:ℝ)/4 →
        (e:ℝ) ≤ γ*(m:ℝ)/32 → 0 ≤ ξ →
        6*ξ ≤ A → B+2*ξ ≤ A → A ≤ δ*(m:ℝ) →
        ∃ h g q Wbar : ℕ, 0 < h ∧ 0 < g ∧ 5*ξ ≤ (h:ℝ) ∧ (h:ℝ) ≤ γ*(m:ℝ)/256 ∧
          4*ξ*(5+6*(ell:ℝ)*(m:ℝ)) ≤ (γ*(m:ℝ)/256)*(h:ℝ) ∧
          (t:ℝ)+loss/2+(Wbar:ℝ)+((2+⌈6*ξ⌉₊+h:ℕ):ℝ) ≤ (d:ℝ)/4 ∧
          4+((ell:ℝ)+1)*(B+2*ξ)+2*(e:ℝ)+4*ξ*(5+6*(ell:ℝ)*(m:ℝ))/(h:ℝ) ≤ (Wbar:ℝ) ∧
          Wbar+g ≤ r ∧ m/g+3 ≤ ell ∧ 4+2*ell < q ∧
          q ≤ r-(2+⌈6*ξ⌉₊+h) := by
  obtain ⟨D,hD⟩ := exists_nat_gt (max (1/ρ) (16/α))
  have hDR : (0:ℝ) < D := (by positivity : (0:ℝ) < 1/ρ).trans_le
    ((le_max_left _ _).trans hD.le)
  have hDpos : 0 < D := by exact_mod_cast hDR
  let γ := 1/(2*(D:ℝ))
  have hγ : 0 < γ := by dsimp only [γ]; positivity
  have hγρ : γ ≤ ρ := by
    have hh := (div_lt_iff₀ hρ).mp ((le_max_left _ _).trans_lt hD)
    apply (div_le_iff₀ (show 0 < 2*(D:ℝ) by positivity)).mpr
    nlinarith only [hh]
  have hγα : γ ≤ α/32 := by
    have hh := (div_lt_iff₀ hα).mp ((le_max_right _ _).trans_lt hD)
    apply (div_le_iff₀ (show 0 < 2*(D:ℝ) by positivity)).mpr
    nlinarith only [hh]
  let ell := 8*D+3
  obtain ⟨δ,hδ,hBudget⟩ := exists_dynamic_budget_margins (γ/32) (by positivity) ell
  obtain ⟨N₀,hN₀⟩ := hBudget 0
  refine ⟨γ,δ,hγ,hγρ,hδ,ell,max N₀ (16*D),?_⟩
  intro m d r t e ξ B A loss hN hRob hDeg hCut hLoss hE hξ hξA hBA hA
  obtain ⟨h,hPos,hCap,hForbidden,hDeleted,hReserve⟩ :=
    hN₀ m ((le_max_left _ _).trans hN) A (by linarith only [hξ,hξA]) hA
  have hOrder : 16*D ≤ m := (le_max_right _ _).trans hN
  have hOrderR : 16*(D:ℝ) ≤ (m:ℝ) := by exact_mod_cast hOrder
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hScale : (8:ℝ) ≤ γ*(m:ℝ) := by
    dsimp only [γ]
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ (show 0 < 2*(D:ℝ) by positivity)).mpr
    linarith only [hOrderR]
  have hRate : γ*(m:ℝ) ≤ (r:ℝ) :=
    (mul_le_mul_of_nonneg_right hγρ hm).trans hRob
  let g := m/(4*D)
  let Wbar := ⌈γ*(m:ℝ)/8⌉₊
  let q := r-(2+⌈6*ξ⌉₊+h)
  have hWlow : γ*(m:ℝ)/8 ≤ (Wbar:ℝ) := Nat.le_ceil _
  have hWupper : (Wbar:ℝ) < γ*(m:ℝ)/8+1 := Nat.ceil_lt_add_one (by positivity)
  have hGainBound : (g:ℝ) ≤ γ*(m:ℝ)/2 := by
    have hh : ((4*D:ℕ):ℝ)*(g:ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.mul_div_le m (4*D)
    push_cast at hh
    have hDiv : (g:ℝ) ≤ (m:ℝ)/(4*(D:ℝ)) :=
      (le_div_iff₀ (show 0 < 4*(D:ℝ) by positivity)).mpr (by nlinarith only [hh])
    convert hDiv using 1 <;> dsimp only [γ] <;> field_simp <;> ring
  have hGain : Wbar+g ≤ r := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    linarith only [hWupper,hGainBound,hScale,hRate]
  have hRound := fixed_layer_round_bound D m hDpos (by omega)
  have hDel : ((2+⌈6*ξ⌉₊+h:ℕ):ℝ) ≤ (γ/32)*(m:ℝ)/8 := by
    have hceil : ⌈6*ξ⌉₊ ≤ ⌈6*A⌉₊ :=
      Nat.ceil_le_ceil (by linarith only [hξA,hξ])
    exact (show ((2+⌈6*ξ⌉₊+h:ℕ):ℝ) ≤ ((2+⌈6*A⌉₊+h:ℕ):ℝ) by
      exact_mod_cast (show 2+⌈6*ξ⌉₊+h ≤ 2+⌈6*A⌉₊+h by omega)).trans
        (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hDeleted)
  have hQ : 4+2*ell < q := by
    have hRhs : (4:ℝ)+2*(ell:ℝ)+((2+⌈6*ξ⌉₊+h:ℕ):ℝ) < (r:ℝ) := by
      push_cast
      have hceil : (⌈6*ξ⌉₊:ℝ) ≤ (⌈6*A⌉₊:ℝ) := by
        exact_mod_cast Nat.ceil_le_ceil (show 6*ξ ≤ 6*A by linarith only [hξ,hξA])
      linarith only [hReserve,hRate,hceil,mul_nonneg hγ.le hm]
    have hNat : (4+2*ell)+(2+⌈6*ξ⌉₊+h) < r := by exact_mod_cast hRhs
    dsimp only [q]
    omega
  have hBoot : (t:ℝ)+loss/2+(Wbar:ℝ)+((2+⌈6*ξ⌉₊+h:ℕ):ℝ) ≤ (d:ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right hγα hm
    linarith only [hCut,hLoss,hWupper,hDel,hDeg,hh,hScale,mul_nonneg hγ.le hm]
  have hA0 : 0 ≤ A := by linarith only [hξ,hξA]
  have hNum : 4*ξ*(5+6*(ell:ℝ)*(m:ℝ)) ≤ 4*A*(5+(ell:ℝ)*((m:ℝ)+1)) := by
    have hOne := mul_le_mul_of_nonneg_right hξA (show 0 ≤ 5+(ell:ℝ)*(m:ℝ) by positivity)
    nlinarith only [hOne,hξ,show 0 ≤ A*(ell:ℝ) by positivity]
  have hFrac := div_le_div_of_nonneg_right hNum (Nat.cast_nonneg (α := ℝ) h)
  norm_num only [Nat.cast_zero,mul_zero,add_zero] at hForbidden
  have hFraction : 4*ξ*(5+6*(ell:ℝ)*(m:ℝ))/(h:ℝ) ≤ γ*(m:ℝ)/256 := by
    have hBase : 0 ≤ ((ell:ℝ)+1)*(6*A+2)+8 := by positivity
    linarith only [hFrac,hForbidden,hBase]
  have hWeighted : 4*ξ*(5+6*(ell:ℝ)*(m:ℝ)) ≤ (γ*(m:ℝ)/256)*(h:ℝ) :=
    (div_le_iff₀ (show (0:ℝ) < h by exact_mod_cast hPos)).mp hFraction
  have hForb : 4+((ell:ℝ)+1)*(B+2*ξ)+2*(e:ℝ)+
       4*ξ*(5+6*(ell:ℝ)*(m:ℝ))/(h:ℝ) ≤ (Wbar:ℝ) := by
    have hCol := mul_le_mul_of_nonneg_left
      (show B+2*ξ ≤ 6*A+2 by linarith only [hBA,hξA,hξ]) (show 0 ≤ (ell:ℝ)+1 by positivity)
    linarith only [hCol,hFrac,hForbidden,hE,hWlow]
  refine ⟨h,g,q,Wbar,hPos,hRound.1,by linarith only [hCap,hξA,hξ],
    ?_,hWeighted,hBoot,hForb,hGain,hRound.2,hQ,le_rfl⟩
  push_cast at hDel
  linarith only [hDel,Nat.cast_nonneg (α := ℝ) ⌈6*ξ⌉₊]

open Finset SimpleGraph MultiGraph.PartialColouring

/-- At a fixed positive relative degree and expansion rate, one
threshold and one route cap work for all initial seed states. -/
theorem exists_uniform_completed_seed (ρ α : ℝ) (hρ : 0 < ρ) (hα : 0 < α) :
    ∃ γ δ : ℝ, 0 < γ ∧ γ ≤ ρ ∧ 0 < δ ∧ ∃ ell N : ℕ,
      ∀ {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {a b w : V}
        {d m L r t k : ℕ} {η ξ B : ℝ}
        (s : CaseTwoPartition M a b d m L r t η) (R : M.PartialColouring k)
        (budget : s.InitialRouteBudget R w ξ B) (E : Finset V) (loss : ℝ),
        a ∈ E → b ∈ E → N ≤ m → Fintype.card V = 2*m → 2*t ≤ m →
        (∀ v, v ≠ a → v ≠ b → (d:ℝ)/2-loss ≤ M.supportGraph.degree v) →
        ρ*(m:ℝ) ≤ (r:ℝ) → 2*α*(m:ℝ) ≤ (d:ℝ) →
        (t:ℝ) ≤ α*(m:ℝ)/8 → loss+η*(m:ℝ) ≤ α*(m:ℝ)/4 →
        (E.card:ℝ) ≤ γ*(m:ℝ)/32 → max (6*ξ) (B+2*ξ) ≤ δ*(m:ℝ) →
        ∃ Q : M.PartialColouring k, ∃ h n u : ℕ,
          GoodRouteRun s.part E h ell R Q n u ∧ 5*ξ ≤ (h:ℝ) ∧ (h:ℝ) ≤ γ*(m:ℝ)/256 ∧
          4*ξ*(5+6*(ell:ℝ)*(m:ℝ)) ≤ (γ*(m:ℝ)/256)*(h:ℝ) ∧
          (∀ i : Fin k, ∀ v, (Q.colouring.colourGraph i).degree v = 1) ∧
          (∀ v, (Q.available.internalPart s.part).degree v ≤ h) ∧
          (Q.available.internalPart s.part).degree a = 0 ∧
          (Q.available.internalPart s.part).mult s(b,w) = 0 ∧
          ((Q.available.internalPart s.part).edgeCount:ℝ) < ξ*(5+6*(ell:ℝ)*(m:ℝ)) := by
  obtain ⟨γ,δ,hγ,hγρ,hδ,ell,N,hScale⟩ := exists_completion_scales ρ α hρ hα
  refine ⟨γ,δ,hγ,hγρ,hδ,ell,N,?_⟩
  intro V _ _ M a b w d m L r t k η ξ B s R budget E loss ha hb hN hCard hWindow
    hSupport hExpand hDegree hCut hLoss hE hSmall
  have hξ : 0 ≤ ξ := by
    have hh : (0:ℝ) ≤ (R.colouring.missingPalette a).card := Nat.cast_nonneg _
    linarith only [hh,budget.vertex_missing a]
  obtain ⟨h,g,q,Wbar,hPos,hg,hCap,hCapUpper,hWeighted,hBoot,hForb,hGain,hRounds,hReserve,hPred⟩ :=
    hScale m d r t E.card ξ B (max (6*ξ) (B+2*ξ)) (loss+η*(m:ℝ)) hN
      hExpand hDegree hCut hLoss hE hξ (le_max_left _ _) (le_max_right _ _) hSmall
  obtain ⟨Q,n,u,hRun,hRest⟩ := budget.exists_completed_seed E ha hb h ell g q Wbar loss
    hSupport hCap hCard hWindow hPos hg hBoot hForb hGain hRounds hReserve hPred
  exact ⟨Q,h,n,u,hRun,hCap,hCapUpper,hWeighted,hRest⟩

end OverfullWork.CMSBalancedCut
