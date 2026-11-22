module

public import OverfullWork.CMSCaseTwoFactorizationBudgets
public import OverfullWork.CMSCaseTwoThroughSeedCompletion

@[expose] public section


/-! The non-heavy case of CMS Theorem 4.2 at explicit parameter
scales. The degree profiles and the domination of centre bundles
are the inputs supplied by the canonical completion. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph RegularHeavyCutRepair
open scoped Classical
universe u

set_option maxHeartbeats 2700000 in
theorem cms_theorem_4_2_case_two (ν τ α κ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτcap : τ ≤ 1/16) (hτsmall : τ ≤ α/64)
    (hα : 0 < α) (hκ : 0 < κ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ η : ℝ, 0 < η → η ≤ ζ → ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (M : MultiGraph V) (a b : V) (d m E₀ : ℕ),
        N ≤ Fintype.card V → Fintype.card V = 2*m → a ≠ b →
        M.IsRegularOfDegree d → 2*α*(m:ℝ) ≤ (d:ℝ) → d ≤ 3*m →
        RobustExpansion.IsRealRobust M.supportGraph ν τ →
        ¬ M.HasOverfullSubset d → (E₀:ℝ) ≤ η*(m:ℝ) →
        (M.mult s(a,b):ℝ)+κ*(m:ℝ) ≤ (d:ℝ) →
        (∀ v, v ≠ a → M.mult s(a,v) ≤ M.mult s(a,b)+E₀) →
        (∀ v, v ≠ a → d ≤ M.supportGraph.degree v+M.mult s(a,v)+E₀) →
        (∀ v, v ≠ a → v ≠ b → (d:ℝ)/2-(E₀:ℝ) ≤ M.supportGraph.degree v) →
        ∃ C : M.EdgeColoring d, C.IsFactorization := by
  obtain ⟨γ,δ,hγ,_hγρ,hγκ,hγα,hδ,ell,hSeed⟩ :=
    exists_nonheavy_completed_seed_with_rows.{u} ν τ α κ hν hντ hτcap hτsmall hα hκ
  let δ₁ := min δ (γ/512)
  obtain ⟨ζ,hζ,T,hT,hScale⟩ := exists_nonheavy_seed_input_scales α κ δ₁ hα hκ
    (by dsimp only [δ₁]; positivity)
  obtain ⟨N₀,hN₀⟩ := hScale T le_rfl
  obtain ⟨N₁,hN₁⟩ := exists_nat_ge (65536/γ)
  refine ⟨ζ,hζ,?_⟩
  intro η hη hηζ
  obtain ⟨N₂,hN₂⟩ := hSeed T η hT hη
  refine ⟨max N₂ (2*max N₀ N₁),?_⟩
  intro V _ _ M a b d m E₀ hN hOrder hab hReg hDensity hD hRob hNo hE hGap hCompare hProfile hSupport
  have hm : max N₀ N₁ ≤ m := by
    have hh := (le_max_right _ _).trans hN
    rw [hOrder] at hh
    omega
  have hm₀ : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hΓ : 65536 ≤ γ*(m:ℝ) :=
    (by
      have hm₁ : (N₁:ℝ) ≤ m := by exact_mod_cast (le_max_right _ _).trans hm
      have hh := (div_le_iff₀ hγ).mp (hN₁.trans hm₁)
      nlinarith only [hh])
  have hΓκ := mul_le_mul_of_nonneg_right hγκ hm₀
  have hΓα := mul_le_mul_of_nonneg_right hγα hm₀
  let J := 3*T+1
  let r := ⌈(ν^4/524288)*(m:ℝ)⌉₊-4*J
  let t := ⌈4*τ*(m:ℝ)⌉₊+2*J
  let Λ := ⌊κ*(m:ℝ)/64⌋₊
  let U := η*(m:ℝ)+3*(E₀:ℝ)+(m/T:ℕ)+6*(T:ℝ)+10
  let k := ⌈((d:ℝ)+U)/2⌉₊+(E₀+2)
  let ξ := U+(E₀:ℝ)+3
  let B := (2/α)*ξ+2
  have hξ0 : 0 ≤ ξ := by dsimp only [ξ,U]; positivity
  have hΛLow : κ*(m:ℝ)/64 < (Λ:ℝ)+1 := Nat.lt_floor_add_one _
  have hΛUp : (Λ:ℝ) ≤ κ*(m:ℝ)/64 := Nat.floor_le (by positivity)
  obtain ⟨hErrA,hErrK,hErrD⟩ := hN₀ m E₀ ((le_max_left _ _).trans hm) η hη hηζ hE
  change max (6*ξ) (B+2*ξ) ≤ δ₁*(m:ℝ) at hErrD
  have hSmall : ξ ≤ γ*(m:ℝ)/3072 := by
    have hh := mul_le_mul_of_nonneg_right (show δ₁ ≤ γ/512 from min_le_right _ _) hm₀
    have hLeft := (le_max_left (6*ξ) (B+2*ξ)).trans hErrD
    nlinarith only [hh,hLeft]
  have hΛ : m/T ≤ Λ := by
    apply (Nat.cast_le (α := ℝ)).mp
    have hh : ((m/T:ℕ):ℝ) ≤ ξ := by
      dsimp only [ξ,U]
      linarith only [mul_nonneg hη.le hm₀,Nat.cast_nonneg (α := ℝ) E₀,Nat.cast_nonneg (α := ℝ) T]
    linarith only [hh,hSmall,hΛLow,hΓκ,hΓ]
  obtain ⟨s,w,hRate,hWidth,_hHalf,_hk,hw,hException,copies,R,budget,rows,hq,hComplete⟩ :=
    hN₂ M a b d m Λ E₀ ((le_max_left _ _).trans hN) hOrder hab hReg hDensity hD hRob hNo
      hΛ hGap hProfile hSupport hErrA hErrK
      (hErrD.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hm₀))
  let occ := ⌈γ*(m:ℝ)/256⌉₊+2
  let u := ⌊γ*(m:ℝ)/40⌋₊
  have hOccLow : γ*(m:ℝ)/256+2 ≤ (occ:ℝ) := by
    dsimp only [occ]
    push_cast
    linarith only [Nat.le_ceil (γ*(m:ℝ)/256)]
  have hOccUp : (occ:ℝ) ≤ γ*(m:ℝ)/128 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ γ*(m:ℝ)/256 by positivity)
    dsimp only [occ]
    push_cast
    linarith only [hh,hΓ]
  have huLow : γ*(m:ℝ)/40 < (u:ℝ)+1 := Nat.lt_floor_add_one _
  have huUp : (u:ℝ) ≤ γ*(m:ℝ)/40 := Nat.floor_le (by positivity)
  obtain ⟨E,ha,hb,hECard,hPick⟩ := exists_protected_centre_neighbours s.part R a b u
  have hECardR : (E.card:ℝ) ≤ γ*(m:ℝ)/32 := by
    have hh : (E.card:ℝ) ≤ (u:ℝ)+2 := by exact_mod_cast hECard
    linarith only [hh,huUp,hΓ]
  obtain ⟨Q,h,n,v,hRun,hCapLower,hCapUpper,hWeighted,hFactors,hCap,hCentre,hProtected,hResidue⟩ :=
    hComplete E ha hb hECardR
  let F := ⌈5*ξ⌉₊+3*h
  let del := 2+⌈6*ξ⌉₊+h
  let delB := 1+⌈3*ξ⌉₊
  have hF : (F:ℝ) ≤ γ*(m:ℝ)/64 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 5*ξ by positivity)
    dsimp only [F]
    push_cast
    linarith only [hCapUpper,hSmall,hh,hΓ]
  have hDel : (del:ℝ) ≤ γ*(m:ℝ)/128 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 6*ξ by positivity)
    dsimp only [del]
    push_cast
    linarith only [hCapUpper,hSmall,hh,hΓ]
  have hDelB : (delB:ℝ) ≤ γ*(m:ℝ)/512 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 3*ξ by positivity)
    dsimp only [delB]
    push_cast
    linarith only [hSmall,hh,hΓ]
  have hErr0 : (E₀:ℝ)+η*(m:ℝ) ≤ ξ := by
    dsimp only [ξ,U]
    linarith only [Nat.cast_nonneg (α := ℝ) E₀,Nat.cast_nonneg (α := ℝ) T,
      Nat.cast_nonneg (α := ℝ) (m/T)]
  have hHeavyCount : s.heavyVertices.card ≤ 3*T+1 := by
    have hh := heavySet_card_at_scale M a b d m T hReg hD hT
    exact (card_insert_le _ _).trans (Nat.add_le_add_right hh 1)
  have hRowCost : ((E₀+3+s.heavyVertices.card:ℕ):ℝ) ≤ ξ := by
    have hh : (s.heavyVertices.card:ℝ) ≤ 3*(T:ℝ)+1 := by exact_mod_cast hHeavyCount
    dsimp only [ξ,U]
    push_cast
    linarith only [hh,mul_nonneg hη.le hm₀,Nat.cast_nonneg (α := ℝ) E₀,
      Nat.cast_nonneg (α := ℝ) T,Nat.cast_nonneg (α := ℝ) (m/T)]
  have hK : (k:ℝ) < (d:ℝ)/2+3*ξ/2 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ ((d:ℝ)+U)/2 by dsimp only [U]; positivity)
    dsimp only [k,ξ]
    push_cast
    linarith only [hh,Nat.cast_nonneg (α := ℝ) E₀,show 0 ≤ U by dsimp only [U]; positivity]
  have hInitCap (x : V) : (R.available.internalPart s.part).degree x ≤ h := by
    have hh : (R.available.internalPart s.part).edgeCount ≤ h := by
      exact_mod_cast budget.residue.le.trans hCapLower
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)).trans hh
  have hRatio : 2*(Q.available.internalPart s.part).edgeCount+6*h ≤ (3*h)*occ := by
    have hp := mul_le_mul_of_nonneg_right hOccLow (Nat.cast_nonneg (α := ℝ) h)
    have hΓh := mul_nonneg (mul_nonneg hγ.le hm₀) (Nat.cast_nonneg (α := ℝ) h)
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    nlinarith only [hp,hΓh,hResidue,hWeighted]
  have hba := hab.symm
  apply copies.exists_factorization_of_residue_budgets budget rows E hRun hReg ha hb hw hFactors
    hCap hInitCap hCentre hProtected Λ E₀ occ κ E₀ hΛ hException hq hCompare
    (hProfile b hba) hSupport hGap (by dsimp only [occ]; omega) hRatio
  · change k+F < d
    apply (Nat.cast_lt (α := ℝ)).mp
    push_cast
    linarith only [hK,hF,hSmall,hΓα,hDensity,hΓ]
  · change E₀+3+2*(⌈ξ⌉₊+F)+E₀ ≤ Λ
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    have hh := Nat.ceil_lt_add_one hξ0
    linarith only [hErr0,mul_nonneg hη.le hm₀,hh,hF,hSmall,hΛLow,hΓκ,hΓ]
  · change ((k+F:ℕ):ℝ)+(M.mult s(a,b):ℝ)/2+((E₀+3+s.heavyVertices.card:ℕ):ℝ)+2*(Λ:ℝ) < (d:ℝ)
    push_cast at hRowCost ⊢
    linarith only [hK,hF,hSmall,hΓκ,hRowCost,hΛUp,hGap,hΓ]
  · change η*(m:ℝ)+2*((occ+delB+F:ℕ):ℝ)+2+(E₀:ℝ) ≤ κ*(m:ℝ)
    push_cast
    linarith only [hErr0,hSmall,hOccUp,hDelB,hF,hΓκ,hΓ]
  · rcases hPick with hSub | hLarge
    · exact Or.inl hSub
    · apply Or.inr
      have hOccF : occ+F ≤ u := by
        apply (Nat.cast_le (α := ℝ)).mp
        push_cast
        linarith only [hOccUp,hF,huLow,hΓ]
      exact hOccF.trans_lt hLarge
  · apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    linarith only [hOccUp,hRate,hΓ]
  · change del+F < r
    apply (Nat.cast_lt (α := ℝ)).mp
    push_cast
    linarith only [hDel,hF,hRate,hΓ]
  · change (t:ℝ)+((E₀:ℝ)+η*(m:ℝ))/2+((occ+4+del+F:ℕ):ℝ) ≤ (d:ℝ)/4
    push_cast
    linarith only [hWidth,hErr0,hSmall,hOccUp,hDel,hF,hΓα,hΓ,hDensity]

end OverfullWork.CMSBalancedCut
