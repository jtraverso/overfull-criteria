module

public import OverfullWork.OsthusStadenBalancingBudget

@[expose] public section


/-! Choose the integer shadow demands and H2 capacities with one
threshold for all sizes up to the bounds fixed by §5.1. -/
namespace OverfullWork.DirectedRobustExpansion

/-- Choose the pair capacity rate before the allowable red load. Both
can be selected independently of the primary cluster bound and order. -/
theorem exists_osthus_staden_balancing_rates (p : ℕ) (β ν err densityMargin redLimit : ℝ)
    (hβ : 0 < β) (hν : 0 < ν) (hErr : 0 < err) (hDensity : 0 < densityMargin) (hLimit : 0 < redLimit) :
    ∃ rate redRate : ℝ, 0 < rate ∧ 0 < redRate ∧
      128*rate ≤ β*densityMargin ∧ 32*rate ≤ redLimit ∧ 4*redRate ≤ redLimit ∧
      40*(p:ℝ)*redRate ≤ err*rate*(ν^2/2)^2 := by
  let rate := min (β*densityMargin/128) (redLimit/32)
  have hRate : 0 < rate := by dsimp only [rate]; positivity
  let redRate := min (redLimit/4) (err*rate*(ν^2/2)^2/(40*((p:ℝ)+1)))
  have hRed : 0 < redRate := by dsimp only [redRate]; positivity
  refine ⟨rate,redRate,hRate,hRed,?_,?_,?_,?_⟩
  · linarith only [(min_le_left _ _ : rate ≤ β*densityMargin/128)]
  · linarith only [(min_le_right _ _ : rate ≤ redLimit/32)]
  · linarith only [(min_le_left _ _ : redRate ≤ redLimit/4)]
  · have h := (le_div_iff₀ (by positivity : 0 < 40*((p:ℝ)+1))).mp
      (min_le_right (redLimit/4) (err*rate*(ν^2/2)^2/(40*((p:ℝ)+1))))
    nlinarith only [h,hRed]

/-- The capacity per pair is normalized by the number of refined
cells. Both reuse across the layers and the total ordinary red load
are then controlled by the same chosen rate. -/
theorem exists_osthus_staden_uniform_balancing_budgets
    (Umax p : ℕ) (β ν err densityMargin redRate rate redLimit : ℝ)
    (hβ : 0 < β) (hβ₁ : β ≤ 1) (hν : 0 < ν) (hErr : 0 < err)
    (hDensity : 0 < densityMargin) (hRed : 0 < redRate) (hRate : 0 < rate) (hLimit : 0 < redLimit)
    (hReuse : 128*rate ≤ β*densityMargin)
    (hLoad : 32*rate ≤ redLimit) (hRedSmall : 4*redRate ≤ redLimit)
    (hShadow : 40*(p:ℝ)*redRate ≤ err*rate*(ν^2/2)^2) :
    ∃ N : ℕ, ∀ (m U shadow layers halfLoss : ℕ) (redCap : ℝ),
      N ≤ m → 0 < U → U ≤ Umax → 0 < shadow → U ≤ 2*p*shadow →
      (layers:ℝ) ≤ (U:ℝ)/β → halfLoss+1 ≤ m/4 →
      0 ≤ redCap → redCap ≤ redRate*(m:ℝ) →
      ∃ c bound cap loss cutoff used : ℕ,
        ((2*m-1:ℕ):ℝ)*redCap ≤ err*(c:ℝ) ∧
        3*((c:ℝ)/(shadow:ℝ)) ≤ (bound:ℝ)*(ν^2/2)^2 ∧
        0 < cutoff ∧ cutoff = m/2 ∧ 0 < cap ∧
        bound ≤ cap*loss ∧ cutoff+loss+halfLoss+1 ≤ m ∧ (layers-1)*cap ≤ used ∧
        0 ≤ densityMargin*(cutoff:ℝ)-(used:ℝ) ∧
        (bound:ℝ) ≤ (densityMargin*(cutoff:ℝ)-(used:ℝ))*(cutoff:ℝ) ∧
        redCap+((U*cap:ℕ):ℝ) ≤ redLimit*(m:ℝ) := by
  let size := max (8:ℝ) (max (err/redRate)
    (max (2*(Umax:ℝ)/rate) (max (16*(Umax:ℝ)/(β*densityMargin)) (2*(Umax:ℝ)/redLimit))))
  obtain ⟨N,hN⟩ := exists_nat_ge size
  refine ⟨N,?_⟩
  intro m U shadow layers halfLoss redCap hm hU hUmax hS hSU hLayers hHalf hCap hCapSize
  have hmSize : size ≤ (m:ℝ) := hN.trans (by exact_mod_cast hm)
  have hm₈ : 8 ≤ m := by exact_mod_cast ((le_max_left _ _).trans hmSize : (8:ℝ) ≤ (m:ℝ))
  have hmR : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hUR : 0 < (U:ℝ) := by exact_mod_cast hU
  have hUmaxR : (U:ℝ) ≤ (Umax:ℝ) := by exact_mod_cast hUmax
  have hSR : 0 < (shadow:ℝ) := by exact_mod_cast hS
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hSquare : (m:ℝ) ≤ (m:ℝ)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hm1 hmR.le]
  have hTail := (le_max_right _ _).trans hmSize
  have hTail₂ := (le_max_right _ _).trans hTail
  have hTail₃ := (le_max_right _ _).trans hTail₂
  have hErrPay : err ≤ (m:ℝ)*redRate := (div_le_iff₀ hRed).mp ((le_max_left _ _).trans hTail)
  have hFloorPay : 2*(Umax:ℝ) ≤ (m:ℝ)*rate :=
    (div_le_iff₀ hRate).mp ((le_max_left _ _).trans hTail₂)
  have hReusePay : 16*(Umax:ℝ) ≤ (m:ℝ)*(β*densityMargin) :=
    (div_le_iff₀ (mul_pos hβ hDensity)).mp ((le_max_left _ _).trans hTail₃)
  have hLoadPay : 2*(Umax:ℝ) ≤ (m:ℝ)*redLimit :=
    (div_le_iff₀ hLimit).mp ((le_max_right _ _).trans hTail₃)
  let c := ⌈(2*redRate/err)*(m:ℝ)^2⌉₊
  let raw := rate*(m:ℝ)^2/(U:ℝ)
  let bound := ⌊raw⌋₊
  have hRaw : 0 ≤ raw := by dsimp only [raw]; positivity
  have hRawTwo : 2 ≤ raw := by
    dsimp only [raw]
    apply (le_div_iff₀ hUR).mpr
    nlinarith only [hFloorPay,mul_le_mul_of_nonneg_left hUmaxR (by norm_num : (0:ℝ) ≤ 2),
      mul_le_mul_of_nonneg_left hSquare hRate.le]
  have hLo : raw/2 ≤ (bound:ℝ) := by
    have h := Nat.lt_floor_add_one raw
    change raw < (bound:ℝ)+1 at h
    linarith only [h,hRawTwo]
  have hHi : (bound:ℝ) ≤ raw := Nat.floor_le hRaw
  have hC : (c:ℝ) ≤ (3*redRate/err)*(m:ℝ)^2 := by
    have hPay : 1 ≤ (redRate/err)*(m:ℝ)^2 := by
      have h' := mul_le_mul_of_nonneg_right hSquare hRed.le
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hErr).mpr (by nlinarith only [hErrPay,h'])
    have h := (Nat.ceil_lt_add_one (show 0 ≤ (2*redRate/err)*(m:ℝ)^2 by positivity)).le
    change (c:ℝ) ≤ _ at h
    calc
      _ ≤ (2*redRate/err)*(m:ℝ)^2+1 := h
      _ ≤ (2*redRate/err)*(m:ℝ)^2+(redRate/err)*(m:ℝ)^2 := add_le_add_right hPay _
      _ = _ := by ring
  have hCDemand : ((2*m-1:ℕ):ℝ)*redCap ≤ err*(c:ℝ) := by
    have hCell : ((2*m-1:ℕ):ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast Nat.sub_le (2*m) 1
    have h := mul_le_mul_of_nonneg_left (Nat.le_ceil ((2*redRate/err)*(m:ℝ)^2)) hErr.le
    change _ ≤ err*(c:ℝ) at h
    calc
      _ ≤ (2*(m:ℝ))*(redRate*(m:ℝ)) := mul_le_mul hCell hCapSize hCap (by positivity)
      _ = err*((2*redRate/err)*(m:ℝ)^2) := by field_simp <;> ring
      _ ≤ _ := h
  have hShadowCap : 3*((c:ℝ)/(shadow:ℝ)) ≤ (bound:ℝ)*(ν^2/2)^2 := by
    have hSCount : (U:ℝ) ≤ (2*(p:ℝ))*(shadow:ℝ) := by exact_mod_cast hSU
    have hSmall : 2*(18*(p:ℝ)*redRate/err) ≤ rate*(ν^2/2)^2 := by
      apply (mul_le_mul_iff_of_pos_right hErr).mp
      have hEq : 2*(18*(p:ℝ)*redRate/err)*err = 36*(p:ℝ)*redRate := by field_simp <;> ring
      rw [hEq]
      have hPos : 0 ≤ (p:ℝ)*redRate := by positivity
      nlinarith only [hPos,hShadow]
    calc
      _ ≤ 3*((3*redRate/err)*(m:ℝ)^2/(shadow:ℝ)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hC hSR.le) (by norm_num)
      _ ≤ (18*(p:ℝ)*redRate/err)*(m:ℝ)^2/(U:ℝ) := by
        apply (le_div_iff₀ hUR).mpr
        have h := mul_le_mul_of_nonneg_left hSCount (show 0 ≤ 3*((3*redRate/err)*(m:ℝ)^2/(shadow:ℝ)) by positivity)
        exact h.trans_eq (by field_simp <;> ring)
      _ ≤ (raw/2)*(ν^2/2)^2 := by
        dsimp only [raw]
        calc
          _ ≤ (rate*(ν^2/2)^2/2)*(m:ℝ)^2/(U:ℝ) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hSmall]) (sq_nonneg _)) hUR.le
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLo (sq_nonneg _)
  have hCut : (m:ℝ)/3 ≤ ((m/2:ℕ):ℝ) := by
    have h : m ≤ 3*(m/2) := by omega
    have h' : (m:ℝ) ≤ 3*((m/2:ℕ):ℝ) := by exact_mod_cast h
    linarith only [h']
  have hUsed :
      2*((layers-1:ℕ):ℝ)*(8*(bound:ℝ)/(m:ℝ)+1) ≤ densityMargin*((m/2:ℕ):ℝ) := by
    have hLayer : ((layers-1:ℕ):ℝ) ≤ (U:ℝ)/β :=
      (by exact_mod_cast Nat.sub_le layers 1 : ((layers-1:ℕ):ℝ) ≤ layers).trans hLayers
    have hB := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHi (by norm_num : (0:ℝ) ≤ 8)) hmR.le
    calc
      _ ≤ 2*((U:ℝ)/β)*(8*raw/(m:ℝ)+1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hLayer (by norm_num)) (add_le_add_left hB _)
          (by positivity) (by positivity)
      _ = 16*rate*(m:ℝ)/β+2*(U:ℝ)/β := by dsimp only [raw]; field_simp <;> ring
      _ ≤ densityMargin*(m:ℝ)/4 := by
        apply (mul_le_mul_iff_of_pos_right hβ).mp
        rw [add_mul,div_mul_cancel₀ _ hβ.ne',div_mul_cancel₀ _ hβ.ne']
        nlinarith only [hReusePay,mul_le_mul_of_nonneg_left hUmaxR (by norm_num : (0:ℝ) ≤ 16),
          mul_le_mul_of_nonneg_right hReuse hmR.le]
      _ = densityMargin*((m:ℝ)/4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hCut,hmR]) hDensity.le
  have hNeed : 2*(bound:ℝ) ≤ densityMargin*((m/2:ℕ):ℝ)^2 := by
    have hOne : (1:ℝ) ≤ U := by exact_mod_cast hU
    have hMargin : 18*rate ≤ densityMargin := by
      have h := mul_le_mul_of_nonneg_right hβ₁ hDensity.le
      linarith only [h,hReuse,hRate]
    calc
      _ ≤ 2*raw := mul_le_mul_of_nonneg_left hHi (by norm_num)
      _ ≤ 2*(rate*(m:ℝ)^2) := mul_le_mul_of_nonneg_left (div_le_self (by positivity) hOne) (by norm_num)
      _ ≤ densityMargin*((m:ℝ)/3)^2 := by
        nlinarith only [mul_le_mul_of_nonneg_right hMargin (sq_nonneg (m:ℝ))]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hCut _) hDensity.le
  obtain ⟨cap,loss,cutoff,used,hCutPos,hCapPos,hCutoff,hDemand,hKeep,hPrev,hCapUp,hSlack,hEnough⟩ :=
    exists_balancing_pair_budgets m layers bound halfLoss densityMargin hm₈ hHalf hDensity.le hUsed hNeed
  refine ⟨c,bound,cap,loss,cutoff,used,hCDemand,hShadowCap,hCutPos,hCutoff,hCapPos,hDemand,
    hKeep,hPrev,hSlack,hEnough,?_⟩
  have hProduct : ((U:ℝ)*(cap:ℝ)) ≤ 8*rate*(m:ℝ)+(U:ℝ) := by
    calc
      _ ≤ (U:ℝ)*(8*(bound:ℝ)/(m:ℝ)+1) := mul_le_mul_of_nonneg_left hCapUp hUR.le
      _ ≤ (U:ℝ)*(8*raw/(m:ℝ)+1) := mul_le_mul_of_nonneg_left
        (add_le_add_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHi (by norm_num)) hmR.le) _) hUR.le
      _ = _ := by dsimp only [raw]; field_simp <;> ring
  rw [Nat.cast_mul]
  nlinarith only [hProduct,hCapSize,hLoadPay,hUmaxR,mul_le_mul_of_nonneg_right hLoad hmR.le,
    mul_le_mul_of_nonneg_right hRedSmall hmR.le]

end OverfullWork.DirectedRobustExpansion
