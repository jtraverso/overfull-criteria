module

public import OverfullWork.OsthusStadenCoreSplitBudgetFromSizes
public import OverfullWork.OsthusStadenSpecialBudgetFromPrimarySizes
public import OverfullWork.OsthusStadenSpecialH1Budget

@[expose] public section


/-! Joint numerical conditions of §§5.6–5.8, with the integer target
and the actual number of requests in each bank. -/
namespace OverfullWork.DirectedRobustExpansion

/-- Choose both splitting tolerances after the common bound on the
number of primary clusters. The degree budgets and the total ordinary
red cap hold simultaneously for the same layer sizes. -/
theorem exists_osthus_staden_red_budgets_from_sizes
    (Kmax s p : ℕ) (α β γ ξ loss exc εBase redRate : ℝ)
    (hs : 4 ≤ s) (hp : 3 ≤ p) (hα : 0 < α) (hα₁ : α ≤ 1)
    (hβ : 0 < β) (hβSmall : β ≤ α/4) (hγ : 0 < γ) (hγSmall : γ ≤ α/4)
    (hγ₁ : 5*γ ≤ 1) (hξ : 0 < ξ) (hLoss : 0 < loss) (hExc : 0 ≤ exc)
    (hε : 0 ≤ εBase) (hRed : 0 < redRate)
    (hDirections : 1 ≤ (γ/8)*(s:ℝ))
    (hExceptional : exc+8*εBase ≤ (γ/8)*α)
    (hCoreCap : 288*exc*β*(p:ℝ) ≤ α*(redRate/4))
    (hClip : 288*loss*((((2*s)*p*2):ℕ):ℝ) ≤ (γ/8)*α)
    (hFill : 4*loss ≤ ξ) (hSupply : 320*(p:ℝ)*ξ ≤ γ*α)
    (hSpecialCap : 2*(3*loss)*β ≤ ξ*(redRate/16))
    (hH1Lower : (s:ℝ)*(8*εBase/((((2*s)*p*2):ℕ):ℝ)+9*loss) ≤ γ*α/(180*(p:ℝ)))
    (hH1Upper : (s:ℝ)*(8*εBase) ≤ γ*α/(3*(p:ℝ))) :
    ∃ splitCore splitSpecial : ℝ, 0 < splitCore ∧ 0 < splitSpecial ∧
      ∃ N : ℕ, ∀ (r K m n M z halfLoss : ℕ) (a : ℝ),
        N ≤ m → 0 < K → K ≤ Kmax → α ≤ a → a ≤ 1 →
        r = ⌊(a-γ)*(K:ℝ)/β⌋₊ → (2*(p:ℝ))*β ≤ γ*(K:ℝ) →
        1 ≤ ξ*(K:ℝ)/β → (z:ℝ) ≤ exc*(n:ℝ) →
        let ell := ((2*s)*p*2:ℕ)
        let volume := (((2*s)*p*K:ℕ):ℝ)
        let κ := ⌊(1-γ)*(1-5*γ)*β*((2*m:ℕ):ℝ)⌋₊
        let kCore := exceptionalPhaseBankSize r (2*s) p
        let types := ⌈2*(2*ξ*(K:ℝ)/β)+4*loss*(r:ℝ)+1⌉₊
        let kSpecial := types*((2*s-1)*(p-1))+1
        let e := 8*εBase
        let requests := (K:ℝ)*((s-1:ℕ):ℝ)
        let total := γ*a*(n:ℝ)
        let capCore := (z:ℝ)/(kCore:ℝ)+splitCore*(n:ℝ)
        volume*((2*m:ℕ):ℝ) ≤ (n:ℝ) → (n:ℝ) ≤ 2*(volume*((2*m:ℕ):ℝ)) →
        ell*m ≤ M → M ≤ 2*(ell*m) → (K:ℝ)*(M:ℝ) ≤ (n:ℝ) →
        (halfLoss:ℝ) ≤ 8*loss*(M:ℝ) →
        1 ≤ loss*((2*m:ℕ):ℝ) ∧ halfLoss+1 ≤ m/4 ∧
        (κ:ℝ) ≤ ((s-1:ℕ):ℝ)*(1-e)*(a*(n:ℝ)-(z:ℝ)-e*((K:ℝ)*(M:ℝ))) /
            ((ell:ℝ)*(kCore:ℝ)) -
          requests*(splitCore*(n:ℝ)+((halfLoss+1:ℕ):ℝ)/(kCore:ℝ)) ∧
        requests*((1-e)*(e*(M:ℝ)/(ell:ℝ))+((halfLoss+1:ℕ):ℝ)) ≤ total/(180*(p:ℝ)) ∧
        requests*e*(M:ℝ) ≤ total/(3*(p:ℝ)) ∧
        (κ:ℝ)+splitSpecial*(n:ℝ) ≤ (total/(20*(p:ℝ)))/(kSpecial:ℝ) ∧
        (∀ zSpecial : ℕ, (zSpecial:ℝ) ≤ 3*loss*(n:ℝ) →
          (zSpecial:ℝ)/(kSpecial:ℝ)+splitSpecial*(n:ℝ) ≤ (redRate/4)*(m:ℝ)) ∧
        1+capCore+(redRate/4)*(m:ℝ) ≤ redRate*(m:ℝ) := by
  let ζ := γ/8
  let Vmax := (2*s)*p*Kmax
  let ell := ((2*s)*p*2:ℕ)
  have hζ : 0 < ζ := by dsimp only [ζ]; positivity
  have hEll : 0 < ell := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by decide)
  obtain ⟨splitCore,hCore,hCoreBudget⟩ :=
    exists_osthus_staden_core_split_budget Vmax β ζ (redRate/4) hβ hζ (by positivity)
  obtain ⟨splitSpecial,hSpec,hSpecBudget⟩ :=
    exists_osthus_staden_special_budgets_of_sizes Kmax s p α β γ ξ loss (3*loss) (redRate/16)
      hs hp hβ hγ.le hξ hLoss.le (by positivity) (by positivity) hFill hSupply hSpecialCap
  let threshold := max (1/loss) (max (18/(ζ*α)) (max (2/redRate) 8))
  obtain ⟨N,hN⟩ := exists_nat_ge threshold
  refine ⟨splitCore,splitSpecial,hCore,hSpec,N,?_⟩
  intro r K m n M z halfLoss a hm hK hKmax ha ha₁ hr hSlack hScale hZ
    ell' volume κ kCore types kSpecial e requests total capCore hOrd hSize hM hM' hVolume hHalfLoss
  have hThreshold : threshold ≤ (m:ℝ) := hN.trans (by exact_mod_cast hm)
  have ha₀ : 0 ≤ a := hα.le.trans ha
  have hMpos : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg _
  have hRealLoss : 1 ≤ loss*(m:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hLoss).mp ((le_max_left _ _).trans hThreshold)
  have hRealClip : 18 ≤ (ζ*α)*(m:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ (mul_pos hζ hα)).mp
      ((le_max_left _ _).trans ((le_max_right _ _).trans hThreshold))
  have hRealRed : 2 ≤ redRate*(m:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hRed).mp
      ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hThreshold)))
  have hm₈ : 8 ≤ m := by
    exact_mod_cast ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hThreshold)) : (8:ℝ) ≤ (m:ℝ))
  have hmTwo : (m:ℝ) ≤ ((2*m:ℕ):ℝ) := by exact_mod_cast (show m ≤ 2*m by omega)
  have hSpecialPop : 1 ≤ loss*((2*m:ℕ):ℝ) :=
    hRealLoss.trans (mul_le_mul_of_nonneg_left hmTwo hLoss.le)
  have hV : volume ≤ (Vmax:ℝ) := by
    change ((((2*s)*p*K:ℕ):ℝ)) ≤ ((((2*s)*p*Kmax:ℕ):ℝ))
    exact_mod_cast Nat.mul_le_mul_left ((2*s)*p) hKmax
  have hV' : requests ≤ (Vmax:ℝ) := by
    have hReq : K*(s-1) ≤ Vmax := by
      calc
        _ ≤ Kmax*(2*s) := Nat.mul_le_mul hKmax (by omega)
        _ ≤ Vmax := by
          have h := Nat.le_mul_of_pos_right (Kmax*(2*s)) (show 0 < p by omega)
          simpa only [Vmax,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h
    change (K:ℝ)*((s-1:ℕ):ℝ) ≤ (Vmax:ℝ)
    exact_mod_cast hReq
  have hNvol : (n:ℝ) ≤ 4*(Vmax:ℝ)*(m:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hV (Nat.cast_nonneg (α := ℝ) (2*m))
    push_cast at h hSize
    nlinarith only [h,hSize]
  obtain ⟨hSplitError,hSplitLoad⟩ := hCoreBudget m requests n (by positivity) (by dsimp only [requests]; positivity) hV' hNvol
  have hR : (r:ℝ) ≤ (K:ℝ)/β := by
    have hγa : γ ≤ a := (show γ ≤ α by linarith only [hγSmall,hα]).trans ha
    have hKnum : (a-γ)*(K:ℝ) ≤ (K:ℝ) := mul_le_of_le_one_left (Nat.cast_nonneg _)
      (by linarith only [ha₁,hγ])
    rw [hr]
    exact (Nat.floor_le (by positivity)).trans (div_le_div_of_nonneg_right hKnum hβ.le)
  have hFloorUp : (κ:ℝ) ≤ (1-γ)*(1-5*γ)*β*((2*m:ℕ):ℝ) := by
    exact Nat.floor_le (mul_nonneg (mul_nonneg
      (mul_nonneg (by linarith only [hγ₁]) (by linarith only [hγ₁])) hβ.le) (Nat.cast_nonneg _))
  have hTarget : (κ:ℝ) ≤ (1-4*ζ)*(β*((2*m:ℕ):ℝ)) := by
    have hBase : (1-γ)*(1-5*γ) ≤ 1-4*ζ := by
      dsimp only [ζ]
      have h := mul_le_of_le_one_right (show 0 ≤ 1-γ by linarith only [hγ₁])
        (show 1-5*γ ≤ 1 by linarith only [hγ])
      linarith only [h,hγ]
    exact hFloorUp.trans (by
      rw [mul_assoc ((1-γ)*(1-5*γ))]
      exact mul_le_mul_of_nonneg_right hBase (show 0 ≤ β*((2*m:ℕ):ℝ) by positivity))
  have hκ : (κ:ℝ) ≤ β*((2*m:ℕ):ℝ) :=
    hTarget.trans (mul_le_of_le_one_left (by positivity) (by linarith only [hζ]))
  have hHalfClip : 9*((halfLoss+1:ℕ):ℝ) ≤ ζ*α*(m:ℝ) := by
    have hMcast : (M:ℝ) ≤ 2*(ell:ℝ)*(m:ℝ) := by exact_mod_cast (show M ≤ (2*ell)*m by rwa [Nat.mul_assoc])
    have h₁ := mul_le_mul_of_nonneg_left hMcast (show 0 ≤ 8*loss by positivity)
    change 288*loss*(ell:ℝ) ≤ ζ*α at hClip
    have h₂ := mul_le_mul_of_nonneg_right hClip (Nat.cast_nonneg (α := ℝ) m)
    push_cast
    nlinarith only [hHalfLoss,h₁,h₂,hRealClip]
  have hHalfSmall : halfLoss+1 ≤ m/4 := by
    have hαζ : ζ*α ≤ 1 := by
      dsimp only [ζ]
      have h := mul_le_mul_of_nonneg_left hα₁ (show 0 ≤ γ/8 by positivity)
      linarith only [h,hγ₁]
    have hThree : 9*(halfLoss+1) ≤ m := by
      exact_mod_cast hHalfClip.trans (mul_le_of_le_one_left (Nat.cast_nonneg _) hαζ)
    omega
  have hClipping := core_exception_clipping_budget r s p K m halfLoss a α β γ ζ n splitCore
    (by omega) hp hK hα ha hβ hβSmall hγSmall hr hSplitError hHalfClip
  have hExc' : (z:ℝ)+e*((K:ℝ)*(M:ℝ)) ≤ ζ*(a*(n:ℝ)) := by
    have he : 0 ≤ e := by dsimp only [e]; positivity
    change exc+e ≤ ζ*α at hExceptional
    calc
      _ ≤ (exc+e)*(n:ℝ) := by linarith only [hZ,mul_le_mul_of_nonneg_left hVolume he]
      _ ≤ (ζ*α)*(n:ℝ) := mul_le_mul_of_nonneg_right hExceptional (Nat.cast_nonneg _)
      _ ≤ _ := by
        nlinarith only [mul_le_mul_of_nonneg_right ha (show 0 ≤ ζ*(n:ℝ) by positivity)]
  have hEζ : e ≤ ζ := by
    have h := mul_le_of_le_one_right hζ.le hα₁
    change exc+e ≤ ζ*α at hExceptional
    linarith only [h,hExceptional,hExc]
  have hDirections' : (1-ζ)*(s:ℝ) ≤ ((s-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ s),Nat.cast_one]
    change 1 ≤ ζ*(s:ℝ) at hDirections
    linarith only [hDirections]
  have hCells : (2*(s:ℝ))*(p:ℝ)*(2*(m:ℝ))*(K:ℝ) ≤ (n:ℝ) := by
    dsimp only [volume] at hOrd
    push_cast at hOrd
    nlinarith only [hOrd]
  have hCore' := core_exception_layer_budget_from_target r s p K M κ a γ β n m e ζ z
    (requests*(splitCore*(n:ℝ)+((halfLoss+1:ℕ):ℝ)/(kCore:ℝ))) (by omega) hp hβ ha₀
    (by linarith only [hγSmall,ha,hα]) (by positivity) (by positivity) (by dsimp only [e]; positivity)
    hEζ (by dsimp only [ζ]; linarith only [hγ₁]) hr hSlack hCells hDirections' hExc'
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hClipping)
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hTarget)
  have hHalfRel : ((halfLoss+1:ℕ):ℝ) ≤ 9*loss*(M:ℝ) := by
    have hMm : (m:ℝ) ≤ (M:ℝ) := by
      exact_mod_cast (show m ≤ M from (Nat.le_mul_of_pos_left m hEll).trans hM)
    rw [Nat.cast_add,Nat.cast_one]
    linarith only [hHalfLoss,hRealLoss,mul_le_mul_of_nonneg_left hMm hLoss.le]
  obtain ⟨hH1Lo,hH1Hi⟩ := special_red_profile_error_budget K n M s p ell halfLoss e (9*loss) γ a
    hEll (by dsimp only [e]; positivity) (by positivity) hVolume hHalfRel
    (hH1Lower.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha hγ.le) (by positivity)))
    (hH1Upper.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha hγ.le) (by positivity)))
  obtain ⟨hSpecialDegree,hSpecialLoad⟩ :=
    hSpecBudget r K m n κ a hKmax ha hScale hR hκ hOrd (by nlinarith only [hSize])
  have hCoreLoad := osthus_staden_core_cap_from_primary_sizes r K s p m n z a α β γ exc splitCore
    (redRate/4) (by omega) hp hK hα ha hβ hβSmall hγSmall hExc hr hSize hZ hCoreCap hSplitLoad
  refine ⟨hSpecialPop,hHalfSmall,hCore',hH1Lo,hH1Hi,hSpecialDegree,?_,?_⟩
  · intro zSpecial hz
    have h := hSpecialLoad zSpecial hz
    linarith only [h]
  · dsimp only [capCore]
    nlinarith only [hCoreLoad,hRealRed]

end OverfullWork.DirectedRobustExpansion
