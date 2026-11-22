module

public import OverfullWork.KuhnOsthusExceptionalWindingParameters
public import OverfullWork.KuhnOsthusExceptionalStageBudgets
public import OverfullWork.KuhnOsthusChordReserveScales

@[expose] public section


/-! Choose the integer degrees of (11.7)–(11.14) before constructing
the three reserves. -/
namespace OverfullWork.DirectedRobustExpansion

open scoped Classical

set_option maxHeartbeats 850000 in
/-- Fix the chord density before the upper bound on the cluster count
is used to choose the preprocessing rates. Floors for the original
leftover and the two reserves, and a ceiling for the extender degree,
work for every partition within that bound. The leftover rate can
be capped after the preprocessing and extender rates are fixed. -/
theorem exists_kuhn_osthus_initial_degree_schedule_with_dependent_leftover_bound
    (l f q ell g kMax : ℕ) (α μ d₁ ρ₈ ρ₉ ρ₁₀ loss₉ loss₁₀ d₃Max : ℝ)
    (ηMax : ℝ → ℝ → ℝ)
    (hl : 0 < l) (hf : 0 < f) (hq : 0 < q) (hMax : 0 < kMax)
    (hα : 0 < α) (hμ : 0 < μ) (hμ₁ : μ ≤ 1)
    (hd₁ : 0 < d₁) (hd₁₁ : d₁ ≤ 1) (h₈ : 0 < ρ₈) (h₉ : 0 < ρ₉) (hL₉ : 0 < loss₉)
    (h₁₀ : 3*d₁ ≤ ρ₁₀) (hL₁₀ : 4*d₁ ≤ loss₁₀) (hDMax : 0 < d₃Max) (hEtaMax : ∀ x y, 0 < x → 0 < y → 0 < ηMax x y) :
    ∃ d₃ c η : ℝ, 0 < d₃ ∧ 0 < c ∧ 0 < η ∧
      d₃ ≤ d₃Max ∧ η ≤ ηMax d₃ c ∧
      8*c < μ*d₃ ∧ 2*d₃ ≤ μ^2 ∧ d₃ ≤ loss₉ ∧ d₃*(kMax:ℝ)^2 ≤ d₁ ∧
      ∃ T : ℕ, ∀ (k m n r m₈ m₉ : ℕ),
        0 < k → k ≤ kMax → f ≤ k → 96*ell*g^2 ≤ k → q ∣ f*k →
        T ≤ m → m ≤ n → n ≤ 2*k*m → r ≤ n → α*(n:ℝ) ≤ (r:ℝ) →
        m = 50*m₈ → f*m = q*m₉ →
        let r₀ := ⌊η*(r:ℝ)⌋₊
        let p := ⌊d₃*(m:ℝ)⌋₊
        let a := 50*l*r₀
        let t := p-a
        let r₁ := ⌊d₁*(m:ℝ)⌋₊
        let r₂ := 96*ell*g^2*k*t
        let D := ⌈c*(m:ℝ)⌉₊
        0 < r₀ ∧ a+t = p ∧ p*k^2 ≤ r₁ ∧ r₁ ≤ m ∧ t*k*f^2 ≤ m ∧
        (r₀:ℝ) ≤ ρ₈*(m₈:ℝ) ∧ (p:ℝ) ≤ loss₉*(m:ℝ) ∧ (r₀:ℝ) ≤ c*(m:ℝ) ∧
        ∃ r₃ L : ℕ,
          let s := r₁+r₂+t-(q-1)*r₃
          t*(f*k) = q*r₃ ∧ q*r₃ ≤ r₁ ∧ r₂ ≤ r₁ ∧ r₃ ≤ r₁ ∧
          (q-1)*r₃+s = r₁+r₂+t ∧ r₂+t+r₃ ≤ s ∧
          (r₃:ℝ) ≤ ρ₉*(m₉:ℝ) ∧ (s:ℝ) ≤ ρ₁₀*(m:ℝ) ∧
          ((p+r₁+r₂+r₃:ℕ):ℝ) ≤ loss₁₀*(m:ℝ) ∧ p+r₁+r₂+r₃+6*s ≤ 22*r₁ ∧
          max a (max (q*r₃+a) (7*s+(a+q*r₃))) ≤ 23*r₁ ∧
          D+r₀ ≤ p-L ∧ L ≤ p ∧ p ≤ 2*L ∧
          2*(p-L)*(k*m) ≤ L*⌈μ*((k*m:ℕ):ℝ)⌉₊ ∧ 2*p*(k*m) ≤ ⌈μ*((k*m:ℕ):ℝ)⌉₊^2 := by
  let KM : ℝ := kMax
  have hKM : 0 < KM := by dsimp only [KM]; exact_mod_cast hMax
  have hfR : (0:ℝ) < f := by exact_mod_cast hf
  let d₃ := min (min (min (d₁/KM^2) (ρ₉/KM)) (min loss₉ (μ^2/2)))
    (min d₃Max (1/(KM*(f:ℝ)^2)))
  have hd₃ : 0 < d₃ := lt_min
    (lt_min (lt_min (by positivity) (by positivity)) (lt_min hL₉ (by positivity)))
    (lt_min hDMax (by positivity))
  have hD₃Max : d₃ ≤ d₃Max := (min_le_right _ _).trans (min_le_left _ _)
  have hSpace : d₃*(KM*(f:ℝ)^2) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp ((min_le_right _ _).trans (min_le_right _ _))
  have hDChord : d₃*KM^2 ≤ d₁ := (le_div_iff₀ (by positivity)).mp
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hDCount : d₃*KM ≤ ρ₉ := (le_div_iff₀ hKM).mp
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hDLoss : d₃ ≤ loss₉ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hDμ : 2*d₃ ≤ μ^2 := by
    have h : d₃ ≤ μ^2/2 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  let c := μ*d₃/16
  have hc : 0 < c := by dsimp [c]; positivity
  have hGap : 8*c < μ*d₃ := by
    dsimp only [c]
    linarith only [mul_pos hμ hd₃]
  let coeff := min (min c (min (ρ₈/50) (d₃/(100*(l:ℝ))))) (ηMax d₃ c)
  have hCoeff : 0 < coeff := lt_min (lt_min hc (lt_min (by positivity) (by positivity))) (hEtaMax d₃ c hd₃ hc)
  let η := coeff/(2*KM)
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηEq : η*(2*KM) = coeff := div_mul_cancel₀ _ (by positivity)
  have hEta' : η ≤ ηMax d₃ c := by
    have hOne : (1:ℝ) ≤ KM := by dsimp only [KM]; exact_mod_cast hMax
    have hShrink := mul_le_mul_of_nonneg_left (show 1 ≤ 2*KM by linarith only [hOne]) hη.le
    linarith only [hShrink,hηEq,(show coeff ≤ ηMax d₃ c from min_le_right _ _)]
  obtain ⟨T₀,hT₀⟩ :=
    exists_kuhn_osthus_preprocessing_degree_scales c d₃ μ hc.le hd₃ hμ.le hμ₁ hGap hDμ
  let T₁ := ⌈1/(η*α)⌉₊
  refine ⟨d₃,c,η,hd₃,hc,hη,hD₃Max,hEta',hGap,hDμ,hDLoss,hDChord,max T₀ T₁,?_⟩
  intro k m n r m₈ m₉ hk hkMax hkF hkWalk hDiv hT hmN hn hr hDense hBase₈ hBase₉
    r₀ p a t r₁ r₂ D
  have hKMR : (k:ℝ) ≤ KM := by dsimp only [KM]; exact_mod_cast hkMax
  have hmR : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hrR : (r:ℝ) ≤ (2*KM)*(m:ℝ) := by
    have hNat : r ≤ 2*kMax*m := hr.trans (hn.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hkMax)))
    dsimp only [KM]
    exact_mod_cast hNat
  have hR₀ : (r₀:ℝ) ≤ coeff*(m:ℝ) := by
    have hFloor : (r₀:ℝ) ≤ η*(r:ℝ) := Nat.floor_le (by positivity)
    calc
      _ ≤ η*((2*KM)*(m:ℝ)) := hFloor.trans (mul_le_mul_of_nonneg_left hrR hη.le)
      _ = _ := by rw [←mul_assoc,hηEq]
  have hR₀pos : 0 < r₀ := by
    have hM : 1/(η*α) ≤ (m:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show T₁ ≤ m from (le_max_right T₀ T₁).trans hT))
    have hLower := (div_le_iff₀ (mul_pos hη hα)).mp hM
    have hN := mul_le_mul_of_nonneg_left (by exact_mod_cast hmN : (m:ℝ) ≤ n) hα.le
    have hR := mul_le_mul_of_nonneg_left (hN.trans hDense) hη.le
    have hOne : (1:ℝ) ≤ η*(r:ℝ) := by nlinarith only [hLower,hR]
    exact Nat.floor_pos.mpr hOne
  have hR₀c : (r₀:ℝ) ≤ c*(m:ℝ) := hR₀.trans
    (mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) hmR)
  have hR₀₈ : 50*(r₀:ℝ) ≤ ρ₈*(m:ℝ) := by
    have hC : coeff ≤ ρ₈/50 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith only [hR₀,mul_le_mul_of_nonneg_right hC hmR]
  have ha : (a:ℝ) ≤ (d₃/2)*(m:ℝ) := by
    have hC : coeff ≤ d₃/(100*(l:ℝ)) := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hl' : 0 < (l:ℝ) := by exact_mod_cast hl
    have hC' := (le_div_iff₀ (show 0 < 100*(l:ℝ) by positivity)).mp hC
    have h := mul_le_mul_of_nonneg_left hR₀ (show 0 ≤ 100*(l:ℝ) by positivity)
    have h' := mul_le_mul_of_nonneg_right hC' hmR
    dsimp only [a]
    push_cast
    nlinarith only [h,h']
  obtain ⟨_,hSum,_,_,L,hLow,hLe,hHigh,hBalanceGap,hSquare⟩ :=
    hT₀ m (k*m) r₀ a ((le_max_left T₀ T₁).trans hT) (Nat.le_mul_of_pos_left _ hk) hR₀c ha
  have hSum' : a+t = p := hSum
  have hap : a ≤ p := hSum' ▸ Nat.le_add_right a t
  have hpK : p*k^2 ≤ r₁ := by
    apply chord_absorption_budget_of_floors d₃ d₁ m k hd₃.le
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg k) hKMR 2) hd₃.le).trans hDChord
  have hp : p ≤ r₁ := (Nat.le_mul_of_pos_right _ (pow_pos hk 2)).trans hpK
  have hpR : (p:ℝ) ≤ d₃*(m:ℝ) := Nat.floor_le (by positivity)
  have hReserveRoom : t*k*f^2 ≤ m := by
    have htR : (t:ℝ) ≤ (p:ℝ) := by exact_mod_cast Nat.sub_le p a
    have hK := mul_le_mul_of_nonneg_right hKMR (sq_nonneg (f:ℝ))
    have h := (mul_le_mul_of_nonneg_left hK hd₃.le).trans hSpace
    have htM := mul_le_mul_of_nonneg_right (htR.trans hpR) (show 0 ≤ (k:ℝ)*(f:ℝ)^2 by positivity)
    exact_mod_cast (show (t:ℝ)*(k:ℝ)*(f:ℝ)^2 ≤ (m:ℝ) by
      linarith only [htM,mul_le_mul_of_nonneg_right h hmR])
  have hr₁R : (r₁:ℝ) ≤ d₁*(m:ℝ) := Nat.floor_le (by positivity)
  have hr₁m : r₁ ≤ m := by exact_mod_cast hr₁R.trans (mul_le_of_le_one_left hmR hd₁₁)
  obtain ⟨r₃,hChord,_,hQr,h₂,h₃,hPar,hSpend,hTotal⟩ :=
    exists_kuhn_osthus_absorption_degrees p a r₁ k f q ell g hap hk hq hkF hkWalk hpK hDiv
  have h₂' : r₂ ≤ r₁ := h₂
  have ht : t ≤ r₁ := (Nat.sub_le p a).trans hp
  let s := r₁+r₂+t-(q-1)*r₃
  have hS : s ≤ 3*r₁ := calc
    _ ≤ r₁+r₂+t := Nat.sub_le _ _
    _ ≤ r₁+r₁+r₁ := Nat.add_le_add (Nat.add_le_add_left h₂' _) ht
    _ = _ := by omega
  have hR₃₉ : (p:ℝ)*(k:ℝ) ≤ ρ₉*(m:ℝ) := by
    have hC := (mul_le_mul_of_nonneg_left hKMR hd₃.le).trans hDCount
    calc
      _ ≤ (d₃*(m:ℝ))*(k:ℝ) := mul_le_mul_of_nonneg_right hpR (Nat.cast_nonneg _)
      _ = (d₃*(k:ℝ))*(m:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC hmR
  obtain ⟨hPre,hChordRate,hParityRate⟩ :=
    wound_exceptional_factor_rates f q k m m₈ m₉ r₀ p a r₁ r₃ s ρ₈ ρ₉ ρ₁₀ hf hq
      hBase₈ hBase₉ hChord.symm hS hR₀₈ hR₃₉ (by
        linarith only [mul_le_mul_of_nonneg_right h₁₀ hmR,hr₁R])
  have hLoss₁₀ : ((p+r₁+r₂+r₃:ℕ):ℝ) ≤ loss₁₀*(m:ℝ) := by
    have hOrd : p+r₁+r₂+r₃ ≤ 4*r₁ :=
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right hp _) h₂') h₃).trans (by omega)
    have hSumR : ((p+r₁+r₂+r₃:ℕ):ℝ) ≤ 4*(r₁:ℝ) := by exact_mod_cast hOrd
    linarith only [hSumR,hr₁R,mul_le_mul_of_nonneg_right hL₁₀ hmR]
  have hQr' : q*r₃ ≤ r₁ := hChord ▸ hQr
  obtain ⟨_,hStage₉,hStage₁₀,_,_⟩ := wound_exceptional_counts_of_absorption_degrees
    l r₀ p a r₁ r₂ r₃ q s rfl hap hp h₂' h₃ hQr' hPar
  have hStages : max a (max (q*r₃+a) (7*s+(a+q*r₃))) ≤ 23*r₁ :=
    max_le (hap.trans (hp.trans (by omega))) (max_le (hStage₉.trans (by omega)) hStage₁₀)
  exact ⟨hR₀pos,hSum,hpK,hr₁m,hReserveRoom,hPre,hpR.trans (mul_le_mul_of_nonneg_right hDLoss hmR),hR₀c,
    r₃,L,hChord,hChord ▸ hQr,h₂,h₃,hPar,hSpend,hChordRate,hParityRate,hLoss₁₀,hTotal,
    hStages,hLow,hLe,hHigh,hBalanceGap,hSquare⟩

/-- Version of the rounded degree schedule with a fixed upper bound on the leftover rate. -/
theorem exists_kuhn_osthus_initial_degree_schedule
    (l f q ell g kMax : ℕ) (α μ d₁ ρ₈ ρ₉ ρ₁₀ loss₉ loss₁₀ d₃Max ηMax : ℝ)
    (hl : 0 < l) (hf : 0 < f) (hq : 0 < q) (hMax : 0 < kMax)
    (hα : 0 < α) (hμ : 0 < μ) (hμ₁ : μ ≤ 1)
    (hd₁ : 0 < d₁) (hd₁₁ : d₁ ≤ 1) (h₈ : 0 < ρ₈) (h₉ : 0 < ρ₉) (hL₉ : 0 < loss₉)
    (h₁₀ : 3*d₁ ≤ ρ₁₀) (hL₁₀ : 4*d₁ ≤ loss₁₀) (hDMax : 0 < d₃Max) (hEtaMax : 0 < ηMax) :
    ∃ d₃ c η : ℝ, 0 < d₃ ∧ 0 < c ∧ 0 < η ∧
      d₃ ≤ d₃Max ∧ η ≤ ηMax ∧
      8*c < μ*d₃ ∧ 2*d₃ ≤ μ^2 ∧ d₃ ≤ loss₉ ∧ d₃*(kMax:ℝ)^2 ≤ d₁ ∧
      ∃ T : ℕ, ∀ (k m n r m₈ m₉ : ℕ),
        0 < k → k ≤ kMax → f ≤ k → 96*ell*g^2 ≤ k → q ∣ f*k →
        T ≤ m → m ≤ n → n ≤ 2*k*m → r ≤ n → α*(n:ℝ) ≤ (r:ℝ) →
        m = 50*m₈ → f*m = q*m₉ →
        let r₀ := ⌊η*(r:ℝ)⌋₊
        let p := ⌊d₃*(m:ℝ)⌋₊
        let a := 50*l*r₀
        let t := p-a
        let r₁ := ⌊d₁*(m:ℝ)⌋₊
        let r₂ := 96*ell*g^2*k*t
        let D := ⌈c*(m:ℝ)⌉₊
        0 < r₀ ∧ a+t = p ∧ p*k^2 ≤ r₁ ∧ r₁ ≤ m ∧ t*k*f^2 ≤ m ∧
        (r₀:ℝ) ≤ ρ₈*(m₈:ℝ) ∧ (p:ℝ) ≤ loss₉*(m:ℝ) ∧ (r₀:ℝ) ≤ c*(m:ℝ) ∧
        ∃ r₃ L : ℕ,
          let s := r₁+r₂+t-(q-1)*r₃
          t*(f*k) = q*r₃ ∧ q*r₃ ≤ r₁ ∧ r₂ ≤ r₁ ∧ r₃ ≤ r₁ ∧
          (q-1)*r₃+s = r₁+r₂+t ∧ r₂+t+r₃ ≤ s ∧
          (r₃:ℝ) ≤ ρ₉*(m₉:ℝ) ∧ (s:ℝ) ≤ ρ₁₀*(m:ℝ) ∧
          ((p+r₁+r₂+r₃:ℕ):ℝ) ≤ loss₁₀*(m:ℝ) ∧ p+r₁+r₂+r₃+6*s ≤ 22*r₁ ∧
          max a (max (q*r₃+a) (7*s+(a+q*r₃))) ≤ 23*r₁ ∧
          D+r₀ ≤ p-L ∧ L ≤ p ∧ p ≤ 2*L ∧
          2*(p-L)*(k*m) ≤ L*⌈μ*((k*m:ℕ):ℝ)⌉₊ ∧ 2*p*(k*m) ≤ ⌈μ*((k*m:ℕ):ℝ)⌉₊^2 :=
  exists_kuhn_osthus_initial_degree_schedule_with_dependent_leftover_bound
    l f q ell g kMax α μ d₁ ρ₈ ρ₉ ρ₁₀ loss₉ loss₁₀ d₃Max (fun _ _ => ηMax)
    hl hf hq hMax hα hμ hμ₁ hd₁ hd₁₁ h₈ h₉ hL₉ h₁₀ hL₁₀ hDMax (fun _ _ _ _ => hEtaMax)

end OverfullWork.DirectedRobustExpansion
