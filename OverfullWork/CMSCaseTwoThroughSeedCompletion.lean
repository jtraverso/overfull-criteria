module

public import OverfullWork.CMSCaseTwoCompletionScales

@[expose] public section


/-! Compose the first three steps of CMS Theorem 4.2, Case 2.
The graph-dependent remaining inputs are the prescribed degree
profiles and the size of the set to protect from internal erasures. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph MultiGraph.PartialColouring
open scoped Classical
universe u

set_option maxHeartbeats 2000000 in
theorem exists_nonheavy_completed_seed_with_rows (ν τ α κ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτcap : τ ≤ 1/16) (hτsmall : τ ≤ α/64)
    (hα : 0 < α) (hκ : 0 < κ) :
    ∃ γ δ : ℝ, 0 < γ ∧ γ ≤ (ν^4/524288)/2 ∧ γ ≤ κ/1024 ∧ γ ≤ α/1024 ∧ 0 < δ ∧ ∃ ell : ℕ,
      ∀ (T : ℕ) (η : ℝ), 1 ≤ T → 0 < η → ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (M : MultiGraph V) (a b : V) (d m Λ E₀ : ℕ),
        N ≤ Fintype.card V → Fintype.card V = 2*m → a ≠ b →
        M.IsRegularOfDegree d → 2*α*(m:ℝ) ≤ (d:ℝ) → d ≤ 3*m →
        RobustExpansion.IsRealRobust M.supportGraph ν τ →
        ¬ M.HasOverfullSubset d → m/T ≤ Λ →
        (M.mult s(a,b):ℝ)+κ*(m:ℝ) ≤ (d:ℝ) →
        (∀ v, v ≠ a → d ≤ M.supportGraph.degree v+M.mult s(a,v)+E₀) →
        (∀ v, v ≠ a → v ≠ b → (d:ℝ)/2-(E₀:ℝ) ≤ M.supportGraph.degree v) →
        let h := 3*T+1
        let r := ⌈(ν^4/524288)*(m:ℝ)⌉₊-4*h
        let t := ⌈4*τ*(m:ℝ)⌉₊+2*h
        let U := η*(m:ℝ)+3*(E₀:ℝ)+(m/T:ℕ)+6*(T:ℝ)+10
        let k := ⌈((d:ℝ)+U)/2⌉₊+(E₀+2)
        let ξ := U+(E₀:ℝ)+3
        let B := (2/α)*ξ+2
        ξ ≤ α*(m:ℝ)/8 → ξ ≤ κ*(m:ℝ)/8 → max (6*ξ) (B+2*ξ) ≤ δ*(m:ℝ) →
        ∃ (s : CaseTwoPartition M a b d m (m/T) r t η) (w : V),
          γ*(m:ℝ) ≤ (r:ℝ) ∧ (t:ℝ) ≤ α*(m:ℝ)/8 ∧
          d ≤ 2*k ∧ k ≤ d ∧ w ∉ s.part ∧
          (if (exceptionCandidates M a b Λ).card = 1 then
             w ∈ exceptionCandidates M a b Λ else w = b) ∧
          ∃ (copies : CaseTwoMiddleCopies s w) (R : M.PartialColouring k),
            s.InitialRouteBudget R w ξ B ∧ copies.InitialCrossingRows R ξ ∧
            M.mult s(b,w) ≤ E₀+2 ∧
            ∀ E : Finset V, a ∈ E → b ∈ E → (E.card:ℝ) ≤ γ*(m:ℝ)/32 →
              ∃ Q : M.PartialColouring k, ∃ h₀ n u : ℕ,
                GoodRouteRun s.part E h₀ ell R Q n u ∧ 5*ξ ≤ (h₀:ℝ) ∧ (h₀:ℝ) ≤ γ*(m:ℝ)/256 ∧
                4*ξ*(5+6*(ell:ℝ)*(m:ℝ)) ≤ (γ*(m:ℝ)/256)*(h₀:ℝ) ∧
                (∀ i : Fin k, ∀ v, (Q.colouring.colourGraph i).degree v = 1) ∧
                (∀ v, (Q.available.internalPart s.part).degree v ≤ h₀) ∧
                (Q.available.internalPart s.part).degree a = 0 ∧
                (Q.available.internalPart s.part).mult s(b,w) = 0 ∧
                ((Q.available.internalPart s.part).edgeCount:ℝ) < ξ*(5+6*(ell:ℝ)*(m:ℝ)) := by
  let ρ := ν^4/524288
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  let ρ₁ := min (ρ/2) (min (κ/1024) (α/1024))
  have hρ₁ : 0 < ρ₁ := by dsimp only [ρ₁]; positivity
  have hρrate : ρ₁ ≤ ρ/2 := min_le_left _ _
  obtain ⟨γ,δ,hγ,hγρ,hδ,ell,N₀,hComplete⟩ := exists_uniform_completed_seed ρ₁ α hρ₁ hα
  refine ⟨γ,δ,hγ,hγρ.trans hρrate,
    hγρ.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hγρ.trans ((min_le_right _ _).trans (min_le_right _ _)),hδ,ell,?_⟩
  intro T η hT hη
  let h := 3*T+1
  obtain ⟨ρ₀,hExact,_,_,N₁,hPartition⟩ :=
    exists_case_two_partition_at_rate.{u} ν τ η T hν hντ hτcap hη hT
  have hρ₀ : ρ₀ = ρ := hExact
  obtain ⟨N₂,hN₂⟩ := exists_nat_ge (max (8*(h:ℝ)/ρ)
    (max (16*(2*(h:ℝ)+1)/α) (32/κ)))
  refine ⟨max N₁ (2*max N₀ N₂),?_⟩
  intro V _ _ M a b d m Λ E₀ hN hCard hab hReg hDens hD hRob hNo hΛ hHeavy hProfile hSupport
  let r := ⌈ρ*(m:ℝ)⌉₊-4*h
  let t := ⌈4*τ*(m:ℝ)⌉₊+2*h
  let U := η*(m:ℝ)+3*(E₀:ℝ)+(m/T:ℕ)+6*(T:ℝ)+10
  let k := ⌈((d:ℝ)+U)/2⌉₊+(E₀+2)
  let ξ := U+(E₀:ℝ)+3
  let B := (2/α)*ξ+2
  change ξ ≤ α*(m:ℝ)/8 → ξ ≤ κ*(m:ℝ)/8 → max (6*ξ) (B+2*ξ) ≤ δ*(m:ℝ) → _
  intro hErrorα hErrorκ hErrorδ
  have hm : max N₀ N₂ ≤ m := by
    have hh := (le_max_right _ _).trans hN
    rw [hCard] at hh
    omega
  have hM2 : (N₂:ℝ) ≤ (m:ℝ) := by exact_mod_cast (le_max_right _ _).trans hm
  have hNr := hN₂.trans hM2
  have hDist : 8*(h:ℝ) ≤ ρ*(m:ℝ) := by
    have hh := (div_le_iff₀ hρ).mp ((le_max_left _ _).trans hNr)
    nlinarith only [hh]
  have hCeil := Nat.le_ceil (ρ*(m:ℝ))
  have hSub : 4*h ≤ ⌈ρ*(m:ℝ)⌉₊ := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    linarith only [hDist,hCeil,Nat.cast_nonneg (α := ℝ) h]
  have hRate : (ρ/2)*(m:ℝ) ≤ (r:ℝ) := by
    dsimp only [r]
    rw [Nat.cast_sub hSub]
    push_cast
    linarith only [hDist,hCeil]
  have hTcut : (t:ℝ) ≤ α*(m:ℝ)/8 := by
    have hτ := hν.trans_le hντ
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 4*τ*(m:ℝ) by positivity)
    have hLarge := (div_le_iff₀ hα).mp ((le_max_left _ _).trans ((le_max_right _ _).trans hNr))
    have hMul := mul_le_mul_of_nonneg_right hτsmall (Nat.cast_nonneg (α := ℝ) m)
    dsimp only [t]
    push_cast
    nlinarith only [hh,hLarge,hMul]
  have hScaleκ : 32 ≤ κ*(m:ℝ) := by
    have hh := (div_le_iff₀ hκ).mp ((le_max_right _ _).trans ((le_max_right _ _).trans hNr))
    nlinarith only [hh]
  obtain ⟨_,hWindow,⟨s⟩⟩ :=
    hPartition M a b d m ((le_max_left _ _).trans hN) hCard hab hReg hD hRob
  rw [hρ₀] at s
  have hξE : (E₀:ℝ)+η*(m:ℝ)+3 ≤ ξ := by
    dsimp only [ξ,U]
    linarith only [Nat.cast_nonneg (α := ℝ) E₀,Nat.cast_nonneg (α := ℝ) (m/T),
      Nat.cast_nonneg (α := ℝ) T]
  have hSmall : 2*(E₀+2) ≤ d := by
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    linarith only [hDens,hErrorα,hξE,mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) m),
      mul_nonneg hα.le (Nat.cast_nonneg (α := ℝ) m)]
  have hDens' : α*(Fintype.card V:ℝ) ≤ d := by
    rw [hCard]
    push_cast
    linarith only [hDens]
  obtain ⟨w,hw,hException,hq,copies,C,_,hHalf,hMissing,_,hColour⟩ :=
    s.exists_equitable_seed T Λ E₀ α hα hDens' hReg hNo hD hT hΛ hSmall hProfile
  have hk : k ≤ d := by
    have hUpper := Nat.ceil_lt_add_one (show 0 ≤ ((d:ℝ)+U)/2 by dsimp only [U]; positivity)
    apply (Nat.cast_le (α := ℝ)).mp
    dsimp only [k]
    push_cast
    have hU : U ≤ ξ := by dsimp only [ξ]; linarith only [Nat.cast_nonneg (α := ℝ) E₀]
    linarith only [hUpper,hU,hξE,hDens,hErrorα,
      mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) m),
      mul_nonneg hα.le (Nat.cast_nonneg (α := ℝ) m)]
  have hba : b ≠ a := hab.symm
  have hGap : (M.mult s(a,b):ℝ)+(E₀:ℝ)+η*(m:ℝ)+6*ξ+4 ≤ (d:ℝ) := by
    linarith only [hHeavy,hErrorκ,hScaleκ,hξE]
  obtain ⟨R,budget,rows⟩ := copies.exists_initial_route_budget_with_rows C hw (by rwa [hReg a]) E₀ ξ B
    hCard hMissing hColour (hProfile b hba) hGap
  have hRateγ : γ*(m:ℝ) ≤ (r:ℝ) :=
    (mul_le_mul_of_nonneg_right (hγρ.trans hρrate) (Nat.cast_nonneg _)).trans hRate
  refine ⟨s,w,hRateγ,hTcut,hHalf,hk,hw,hException,copies,R,budget,rows,hq,?_⟩
  intro E ha hb hE
  exact hComplete s R budget E (E₀:ℝ) ha hb ((le_max_left _ _).trans hm)
    hCard hWindow hSupport ((mul_le_mul_of_nonneg_right hρrate (Nat.cast_nonneg _)).trans hRate) hDens hTcut (by
      linarith only [hξE,hErrorα,mul_nonneg hα.le (Nat.cast_nonneg (α := ℝ) m)]) hE hErrorδ

theorem exists_nonheavy_completed_seed (ν τ α κ : ℝ)
    (hν : 0 < ν) (hντ : ν ≤ τ) (hτcap : τ ≤ 1/16) (hτsmall : τ ≤ α/64)
    (hα : 0 < α) (hκ : 0 < κ) :
    ∃ γ δ : ℝ, 0 < γ ∧ 0 < δ ∧ ∃ ell : ℕ,
      ∀ (T : ℕ) (η : ℝ), 1 ≤ T → 0 < η → ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (M : MultiGraph V) (a b : V) (d m Λ E₀ : ℕ),
        N ≤ Fintype.card V → Fintype.card V = 2*m → a ≠ b →
        M.IsRegularOfDegree d → 2*α*(m:ℝ) ≤ (d:ℝ) → d ≤ 3*m →
        RobustExpansion.IsRealRobust M.supportGraph ν τ →
        ¬ M.HasOverfullSubset d → m/T ≤ Λ →
        (M.mult s(a,b):ℝ)+κ*(m:ℝ) ≤ (d:ℝ) →
        (∀ v, v ≠ a → d ≤ M.supportGraph.degree v+M.mult s(a,v)+E₀) →
        (∀ v, v ≠ a → v ≠ b → (d:ℝ)/2-(E₀:ℝ) ≤ M.supportGraph.degree v) →
        let h := 3*T+1
        let r := ⌈(ν^4/524288)*(m:ℝ)⌉₊-4*h
        let t := ⌈4*τ*(m:ℝ)⌉₊+2*h
        let U := η*(m:ℝ)+3*(E₀:ℝ)+(m/T:ℕ)+6*(T:ℝ)+10
        let k := ⌈((d:ℝ)+U)/2⌉₊+(E₀+2)
        let ξ := U+(E₀:ℝ)+3
        let B := (2/α)*ξ+2
        ξ ≤ α*(m:ℝ)/8 → ξ ≤ κ*(m:ℝ)/8 → max (6*ξ) (B+2*ξ) ≤ δ*(m:ℝ) →
        ∃ (s : CaseTwoPartition M a b d m (m/T) r t η) (w : V),
          d ≤ 2*k ∧ k ≤ d ∧ w ∉ s.part ∧
          (if (exceptionCandidates M a b Λ).card = 1 then
             w ∈ exceptionCandidates M a b Λ else w = b) ∧
          ∃ (copies : CaseTwoMiddleCopies s w) (R : M.PartialColouring k),
            s.InitialRouteBudget R w ξ B ∧
            ∀ E : Finset V, a ∈ E → b ∈ E → (E.card:ℝ) ≤ γ*(m:ℝ)/32 →
              ∃ Q : M.PartialColouring k, ∃ h₀ n u : ℕ,
                GoodRouteRun s.part E h₀ ell R Q n u ∧ (h₀:ℝ) ≤ γ*(m:ℝ)/16 ∧
                (∀ i : Fin k, ∀ v, (Q.colouring.colourGraph i).degree v = 1) ∧
                (∀ v, (Q.available.internalPart s.part).degree v ≤ h₀) ∧
                (Q.available.internalPart s.part).degree a = 0 ∧
                (Q.available.internalPart s.part).mult s(b,w) = 0 ∧
                ((Q.available.internalPart s.part).edgeCount:ℝ) < ξ*(5+6*(ell:ℝ)*(m:ℝ)) := by
  obtain ⟨γ,δ,hγ,_,_,_,hδ,ell,hRows⟩ :=
    exists_nonheavy_completed_seed_with_rows.{u} ν τ α κ hν hντ hτcap hτsmall hα hκ
  refine ⟨γ,δ,hγ,hδ,ell,?_⟩
  intro T η hT hη
  obtain ⟨N,hN⟩ := hRows T η hT hη
  refine ⟨N,?_⟩
  intro V _ _ M a b d m Λ E₀ hn hcard hab hreg hDens hD hRob hNo hΛ hHeavy hProfile hSupport
  dsimp only
  intro hErrorα hErrorκ hErrorδ
  obtain ⟨s,w,_,_,hHalf,hk,hw,hEx,copies,R,budget,_,_,h⟩ :=
    hN M a b d m Λ E₀ hn hcard hab hreg hDens hD hRob hNo hΛ hHeavy hProfile hSupport
      hErrorα hErrorκ hErrorδ
  refine ⟨s,w,hHalf,hk,hw,hEx,copies,R,budget,?_⟩
  intro E ha hb hE
  obtain ⟨Q,h₀,n,u,hRun,_,hUpper,_,hRest⟩ := h E ha hb hE
  exact ⟨Q,h₀,n,u,hRun,hUpper.trans (by linarith only [mul_nonneg hγ.le (Nat.cast_nonneg (α := ℝ) m)]),hRest⟩

/-- Choose the seed-scale tolerances before the host. The error
budget includes the integer cutoff and the exceptional-row excess. -/
theorem exists_nonheavy_seed_input_scales (α κ δ : ℝ)
    (hα : 0 < α) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ T₀ : ℕ, 1 ≤ T₀ ∧
      ∀ T : ℕ, T₀ ≤ T → ∃ m₀ : ℕ, ∀ m E₀ : ℕ, m₀ ≤ m →
        ∀ η : ℝ, 0 < η → η ≤ ζ → (E₀:ℝ) ≤ η*(m:ℝ) →
        let ξ := η*(m:ℝ)+3*(E₀:ℝ)+(m/T:ℕ)+6*(T:ℝ)+10+(E₀:ℝ)+3
        let B := (2/α)*ξ+2
        ξ ≤ α*(m:ℝ)/8 ∧ ξ ≤ κ*(m:ℝ)/8 ∧ max (6*ξ) (B+2*ξ) ≤ δ*(m:ℝ) := by
  let c : ℝ := max 6 (2/α+2)
  have hc : 6 ≤ c := le_max_left _ _
  have hc₀ : 0 < c := by linarith only [hc]
  let z := min (α/8) (min (κ/8) (δ/(2*c)))
  have hz : 0 < z := by dsimp only [z]; positivity
  let T₀ := max 1 ⌈4/z⌉₊
  refine ⟨z/20,by positivity,T₀,le_max_left _ _,?_⟩
  intro T hT
  have hTpos : 0 < T := lt_of_lt_of_le (by decide : 0 < 1) ((le_max_left _ _).trans hT)
  have hTR : (0:ℝ) < T := by exact_mod_cast hTpos
  have hTsize : 4/z ≤ (T:ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right _ _).trans hT)
  obtain ⟨m₀,hm₀⟩ := exists_nat_ge (max (4*(6*(T:ℝ)+13)/z) (4/δ))
  refine ⟨m₀,?_⟩
  intro m E₀ hm η hη hηz hE
  have hmReal := hm₀.trans (show (m₀:ℝ) ≤ (m:ℝ) by exact_mod_cast hm)
  have hm₀' : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hFin : 4*(6*(T:ℝ)+13) ≤ z*(m:ℝ) := by
    have hh := (div_le_iff₀ hz).mp ((le_max_left _ _).trans hmReal)
    nlinarith only [hh]
  have hLarge : 4 ≤ δ*(m:ℝ) := by
    have hh := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hmReal)
    nlinarith only [hh]
  have hCut : ((m/T:ℕ):ℝ) ≤ z*(m:ℝ)/4 := by
    have hh : ((m/T:ℕ):ℝ)*(T:ℝ) ≤ (m:ℝ) := by
      exact_mod_cast (Nat.div_mul_le_self m T)
    have hReq := (div_le_iff₀ hz).mp hTsize
    apply (le_of_mul_le_mul_right ?_ hTR)
    have hReq' := mul_le_mul_of_nonneg_right hReq hm₀'
    nlinarith only [hh,hReq']
  let ξ := η*(m:ℝ)+3*(E₀:ℝ)+(m/T:ℕ)+6*(T:ℝ)+10+(E₀:ℝ)+3
  have hξ₀ : 0 ≤ ξ := by dsimp only [ξ]; positivity
  have hξ : ξ ≤ z*(m:ℝ) := by
    have hetaM := mul_le_mul_of_nonneg_right hηz hm₀'
    dsimp only [ξ]
    linarith only [hetaM,hE,hCut,hFin,mul_nonneg hz.le hm₀']
  have hα' : z ≤ α/8 := min_le_left _ _
  have hκ' : z ≤ κ/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ' : z ≤ δ/(2*c) := (min_le_right _ _).trans (min_le_right _ _)
  have hPaid : c*ξ+2 ≤ δ*(m:ℝ) := by
    have hh := (le_div_iff₀ (show 0 < 2*c by positivity)).mp hδ'
    have hhm := mul_le_mul_of_nonneg_right hh hm₀'
    have hcx := mul_le_mul_of_nonneg_left hξ hc₀.le
    nlinarith only [hhm,hcx,hLarge]
  refine ⟨?_,?_,max_le ?_ ?_⟩
  · have hh := hξ.trans (mul_le_mul_of_nonneg_right hα' hm₀')
    linarith only [hh]
  · have hh := hξ.trans (mul_le_mul_of_nonneg_right hκ' hm₀')
    linarith only [hh]
  · exact (mul_le_mul_of_nonneg_right hc hξ₀).trans (by linarith only [hPaid])
  · have hh := mul_le_mul_of_nonneg_right
      (show 2/α+2 ≤ c from le_max_right _ _) hξ₀
    change 2/α*ξ+2+2*ξ ≤ δ*(m:ℝ)
    nlinarith only [hh,hPaid]

end OverfullWork.CMSBalancedCut
