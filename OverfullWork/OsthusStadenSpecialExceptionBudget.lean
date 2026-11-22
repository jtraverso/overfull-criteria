module

public import OverfullWork.OsthusStadenCoreDegreeBudget

@[expose] public section


/-! Integer occurrence budgets and the degree margins in (29)–(30). -/
namespace OverfullWork.DirectedRobustExpansion

/-- Round the optional deletion budget and the original-type occurrence
bound while paying at most two additional units in total. -/
theorem exists_special_exception_type_caps (r : ℕ) (loss atypical : ℝ)
    (hLoss : 0 ≤ loss) (hAtypical : 0 ≤ atypical) :
    ∃ fillCap typeCap : ℕ, 0 < fillCap ∧ 4*loss*(r:ℝ) ≤ (fillCap:ℝ) ∧
      2*atypical+(fillCap:ℝ) ≤ (typeCap:ℝ) ∧
      (typeCap:ℝ) ≤ 2*atypical+4*loss*(r:ℝ)+2 := by
  let f := 4*loss*(r:ℝ)
  let fillCap := max 1 ⌈f⌉₊
  let typeCap := ⌈2*atypical+(fillCap:ℝ)⌉₊
  have hf : 0 ≤ f := by dsimp only [f]; positivity
  have hFill : (fillCap:ℝ) ≤ f+1 := by
    rw [Nat.cast_max]
    exact max_le (by simpa only [Nat.cast_one] using le_add_of_nonneg_left hf) (Nat.ceil_lt_add_one hf).le
  refine ⟨fillCap,typeCap,(by dsimp only [fillCap]; omega),?_,Nat.le_ceil _,?_⟩
  · exact (Nat.le_ceil f).trans (by exact_mod_cast le_max_right 1 ⌈f⌉₊)
  · have h := (Nat.ceil_lt_add_one (show 0 ≤ 2*atypical+(fillCap:ℝ) by positivity)).le
    dsimp only [typeCap]
    linarith only [h,hFill]

/-- The two expected-degree inequalities of Claim 5.4 with slack for
the uniform splitting error. `volume` counts all p-cells. The lower
and upper bounds allow constant slack in the occurrence budget. -/
theorem special_exception_split_degree_budget
    (n mp p k κ z : ℕ) (volume ξ β γ a e split load : ℝ)
    (hp : 0 < p) (hk : 0 < k) (hβ : 0 < β) (hξ : 0 ≤ ξ)
    (he : 0 ≤ e) (hSplit : 0 ≤ split) (hload : 0 ≤ load)
    (hOrd : volume*(mp:ℝ) ≤ (n:ℝ)) (hSize : (n:ℝ) ≤ 2*volume*(mp:ℝ))
    (hKlo : ξ*volume ≤ (k:ℝ)*β) (hKhi : (k:ℝ)*β ≤ 8*ξ*volume)
    (hSupply : 320*(p:ℝ)*ξ ≤ γ*a) (hDemand : (κ:ℝ) ≤ β*(mp:ℝ))
    (hZ : (z:ℝ) ≤ e*(n:ℝ)) (hCap : 2*e*β ≤ ξ*load)
    (hSplitLo : split*(2*volume) ≤ β) (hSplitHi : split*(2*volume) ≤ load) :
    (κ:ℝ)+split*(n:ℝ) ≤ (γ*a*(n:ℝ)/(20*(p:ℝ)))/(k:ℝ) ∧
    (z:ℝ)/(k:ℝ)+split*(n:ℝ) ≤ 2*load*(mp:ℝ) := by
  have hpR : 0 < (p:ℝ) := by exact_mod_cast hp
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have hm : 0 ≤ (mp:ℝ) := Nat.cast_nonneg _
  have hVol : 0 ≤ volume := by
    by_contra! h
    have hn : 8*ξ*volume ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h.le
    exact (not_le_of_gt (mul_pos hkR hβ)) (hKhi.trans hn)
  have hErr (cap : ℝ) (h : split*(2*volume) ≤ cap) : split*(n:ℝ) ≤ cap*(mp:ℝ) := by
    calc
      _ ≤ split*(2*volume*(mp:ℝ)) := mul_le_mul_of_nonneg_left hSize hSplit
      _ = (split*(2*volume))*(mp:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h hm
  have hLower : 2*β*(mp:ℝ) ≤ (γ*a*(n:ℝ)/(20*(p:ℝ)))/(k:ℝ) := by
    apply (le_div_iff₀ hkR).mpr
    apply (le_div_iff₀ (by positivity : 0 < 20*(p:ℝ))).mpr
    calc
      _ = ((k:ℝ)*β)*(40*(p:ℝ)*(mp:ℝ)) := by ring
      _ ≤ (8*ξ*volume)*(40*(p:ℝ)*(mp:ℝ)) := mul_le_mul_of_nonneg_right hKhi (by positivity)
      _ = (320*(p:ℝ)*ξ)*(volume*(mp:ℝ)) := by ring
      _ ≤ (320*(p:ℝ)*ξ)*(n:ℝ) := mul_le_mul_of_nonneg_left hOrd (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hSupply (Nat.cast_nonneg _)
  have hUpper : (z:ℝ)/(k:ℝ) ≤ load*(mp:ℝ) := by
    apply (div_le_iff₀ hkR).mpr
    apply (mul_le_mul_iff_of_pos_right hβ).mp
    calc
      _ ≤ (e*(n:ℝ))*β := mul_le_mul_of_nonneg_right hZ hβ.le
      _ ≤ (e*(2*volume*(mp:ℝ)))*β :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSize he) hβ.le
      _ = (2*e*β)*(volume*(mp:ℝ)) := by ring
      _ ≤ (ξ*load)*(volume*(mp:ℝ)) := mul_le_mul_of_nonneg_right hCap (by positivity)
      _ = (ξ*volume)*(load*(mp:ℝ)) := by ring
      _ ≤ ((k:ℝ)*β)*(load*(mp:ℝ)) := mul_le_mul_of_nonneg_right hKlo (by positivity)
      _ = _ := by ring
  constructor
  · have h := hErr β hSplitLo
    exact (show (κ:ℝ)+split*(n:ℝ) ≤ 2*β*(mp:ℝ) by linarith only [hDemand,h]).trans hLower
  · have h := hErr load hSplitHi
    linarith only [hUpper,h]

end OverfullWork.DirectedRobustExpansion
