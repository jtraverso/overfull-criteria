module

public import OverfullWork.DirectedSeparatedRegularity
public import OverfullWork.KuhnOsthusCoarseRoundingMargins
public import OverfullWork.KuhnOsthusTrimmedWoundPartition
public import OverfullWork.KuhnOsthusExceptionalStageBudgets

@[expose] public section


/-! Construct the first common partition and universal walk of the
proof of Theorem 1.2 directly from the robust directed host. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs DirectedClusterQuotient
open scoped Classical
universe u

set_option maxHeartbeats 2200000 in
/-- The density floor and the two divisibility moduli may be fixed
before choosing the exceptional rate and the regularity tolerance.
The upper bound on the coarse cluster count precedes the requested
lower bound on the final cell size. -/
theorem exists_kuhn_osthus_setup_from_robust_host
    (ν τ α d ζ target θ : ℝ) (b ℓ L f q kMin : ℕ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1) (hντ : ν ≤ τ)
    (hα : 0 < α) (hα₁ : α ≤ 1) (hTau : 64*τ ≤ α)
    (hd : 0 < d) (hdν : 8*d ≤ ν) (hdα : d ≤ α)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1/2) (hTarget : 0 < target) (hθ : θ < 1)
    (hb : 0 < b) (hℓ : 0 < ℓ) (hq : 0 < q) (hfq : f ∣ q)
    (hWalk : ⌈25/((ν/8)^2/2)^2⌉₊+4 ≤ L) :
    ∃ ε η : ℝ, 0 < ε ∧ ε ≤ 4*τ ∧ θ ≤ 1-ε ∧ 0 < η ∧ η ≤ target ∧
    ∃ K : ℕ, ∀ T : ℕ, ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V),
      N ≤ Fintype.card V → IsRealRobust G ν τ →
      (∀ v, (8*α)*(Fintype.card V:ℝ) ≤ (inDegree G v:ℝ) ∧
        (8*α)*(Fintype.card V:ℝ) ≤ (outDegree G v:ℝ)) →
      ∃ (k m a : ℕ) (hk : 0 < k) (Z₀ Z : Finset V) (P : Fin k → Finset V)
        (R₀ : Digraph (Fin k)) (A X : Fin (ℓ*k) → Finset V) (l : Fin (ℓ*k) → List (Fin (ℓ*k)))
        (F : Fin (L+1) → Equiv.Perm (Fin (ℓ*k))),
        let n := ℓ*k
        let parent := windingParent (n := n) k hk
        let R := fibrePullback R₀ parent parent
        kMin ≤ k ∧ k ≤ K ∧ 2 ≤ (4*τ)*(k:ℝ) ∧ b ∣ k ∧ T ≤ a ∧ 200*(L+1)*(q/f) ∣ a ∧
        WoundExceptionalPartition G Z₀ Z P A X R₀ hk ℓ (ℓ*m) a α θ ε (ν/8) (4*τ) ∧
        Z₀ ⊆ Z ∧ Z.card = Z₀.card+(m-a)*n ∧ (Z.card:ℝ) ≤ ζ*(Fintype.card V:ℝ) ∧
        (∀ i j, R.Adj i j → IsUniform G η (X i) (X j) ∧ d ≤ density G (X i) (X j)) ∧
        (∀ s i, IsLowerSuperregularPair G η d (X i) (X (F s i))) ∧
        F 0 = finRotate n ∧ (∀ s i, R.Adj i (F s i)) ∧
        (∀ j, DirectedListRoutes.Route (reindexSources R (finRotate n).symm) j (finRotate n j) (l j) ∧
          ((l j).length:ℝ) ≤ 3/((ν/8)^2/2)) ∧
        (∀ x y, ((univ : Finset (Fin (L+1))).filter (fun j => F j x = y)).card =
          elementaryChordMultiplicity (finRotate n) l x y +
            if finRotate n x = y then L+1 - (∑ z, elementaryChordMultiplicity (finRotate n) l x z) else 0) ∧
        HasSpanningCycle (fun e f : (Σ _ : Fin (L+1), Fin n) => F e.1 e.2 = f.2) := by
  have hτ : 0 < τ := hν.trans_le hντ
  let δ := min (ζ/2) (α/3)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδζ : δ ≤ ζ/2 := min_le_left _ _
  have hδα : δ ≤ α/3 := min_le_right _ _
  let ρ := min target (min (ζ/2) (min (d/4) (4*τ)))
  have hρ : 0 < ρ := lt_min hTarget (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  let B := 200*(L+1)*(q/f)
  obtain ⟨ε,ξ,η,hε,hξ,hξ₁,hη,hη₁,hScale,hScale',hηρ,hTrim,M,hM⟩ :=
    exists_kuhn_osthus_joint_trim_tolerances ℓ L B ρ (4*τ) θ hρ (by positivity) hθ
  have hηTarget : η ≤ target := hηρ.trans (min_le_left _ _)
  have hηζ : η ≤ ζ/2 := hηρ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηd : η ≤ d/4 := hηρ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hητ : η ≤ 4*τ := hηρ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hξη : 4*ξ ≤ η := by
    let m := max 1 M
    have hm : (0:ℝ) < m := by exact_mod_cast (show 0 < max 1 M by omega)
    apply (mul_le_mul_iff_of_pos_right hm).mp
    have h := hM m (le_max_right _ _)
    linarith only [h,mul_nonneg (Nat.cast_nonneg (α := ℝ) (2*(L+1))) (show 0 ≤ 2*ξ*(m:ℝ) by positivity),
      Nat.cast_nonneg (α := ℝ) B]
  have hετ : ε ≤ 4*τ := by linarith only [hητ,hξη,hScale',hε]
  have hθ' : θ ≤ 1-ε := by
    have h : η/(4*τ) ≤ 1-ε-θ := (div_le_iff₀ (show 0 < 4*τ by positivity)).mpr hTrim
    have hNonneg : 0 ≤ η/(4*τ) := by positivity
    linarith only [h,hNonneg]
  let θ₀ := min (1/16:ℝ) (min (ν/48) (min ((8*α)/24) (δ/8)))
  have hθ₀ : 0 < θ₀ := lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hθ₀' : θ₀ ≤ 1/16 := min_le_left _ _
  have hθ₀ν : θ₀ ≤ ν/48 := (min_le_right _ _).trans (min_le_left _ _)
  have hθ₀α : θ₀ ≤ (8*α)/24 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθ₀δ : θ₀ ≤ δ/8 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let e := min (ε/4) (θ₀^4/64)
  let z := min θ₀ (θ₀^4/64)
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have hz : 0 < z := lt_min hθ₀ (by positivity)
  have heε : e ≤ ε/4 := min_le_left _ _
  have hPad : d+ξ+ε+2*e ≤ 2*d-e := by linarith only [hηd,hξη,hScale',heε,hd]
  obtain ⟨Ncycle,hCycle⟩ :=
    exists_kuhn_osthus_ordered_coarse_partition.{u,u} (ν/4) (2*τ) α
      (by positivity) (by linarith only [hν₁]) (by linarith only [hντ,hτ])
      (by linarith only [hTau]) hα₁
  let kNeed := max kMin (max 2 ⌈2/(4*τ)⌉₊)
  let kRaw := Ncycle+kNeed+b+⌈32*(b:ℝ)/ν⌉₊+⌈2*(b:ℝ)/τ⌉₊+⌈4*(b:ℝ)/δ⌉₊+⌈(b:ℝ)/α⌉₊
  obtain ⟨Nreg,K,hReg⟩ := exists_robust_directed_regular_partition_separate_density.{u}
    ν τ (8*α) θ₀ e z (2*d) kRaw hν hτ (by positivity) hθ₀ hθ₀' hθ₀ν hθ₀α
    he (by linarith only [heε,hScale',hξ₁]) hz (min_le_left _ _) (by positivity)
    (by linarith only [hdν,heε,hηd,hξη,hScale',hd]) (by linarith only [hdα,heε,hηd,hξη,hScale',hd])
    (by linarith only [(min_le_right _ _ : e ≤ θ₀^4/64),(min_le_right _ _ : z ≤ θ₀^4/64),pow_pos hθ₀ 4])
  refine ⟨ε,η,hε,hετ,hθ',hη,hηTarget,K,?_⟩
  intro T
  let C := 4*((K+1:ℕ):ℝ)
  have hC : 0 < C := by dsimp only [C]; positivity
  obtain ⟨Ntrim,hTrimmed⟩ := exists_kuhn_osthus_trimmed_wound_partition.{u}
    C ε ξ η d α θ (ν/8) (4*τ) ℓ L f q hC hε hℓ hq hfq hξ hξ₁ hη.le hη₁ hScale hScale'
    (by positivity) (by linarith only [hντ,hτ]) (by linarith only [hTau,hα₁])
    (by linarith only [hTau,hτ]) hTrim hWalk
  let M₀ := max (2*T) (max Ntrim M)
  obtain ⟨Nround,hRound⟩ := exists_kuhn_osthus_coarse_rounding_margins b ℓ (K+1) M₀
    (4*θ₀) δ hb hℓ (by omega) (by linarith only [hθ₀']) hδ (by linarith only [hδζ,hζ₁])
  refine ⟨max Nreg Nround,?_⟩
  intro V _ G hN hRob hDegrees
  obtain ⟨J,inst,g,D,mRaw,hmRaw,hSizes,hkRaw,hkK,hExc,hLoop,hRobD,hInD,hOutD,hPairs⟩ :=
    hReg G ((le_max_left _ _).trans hN) hRob (fun v => (hDegrees v).1) (fun v => (hDegrees v).2)
  let _ : Fintype J := inst
  let nRaw := Fintype.card J
  have hCut (x : ℝ) (hx : ⌈x⌉₊ ≤ kRaw) : x ≤ (nRaw:ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈x⌉₊ ≤ Fintype.card J from hx.trans hkRaw))
  have hbN : ((b-1:ℕ):ℝ) ≤ (b:ℝ) := by exact_mod_cast Nat.sub_le b 1
  have hBudgetν : 8*((b-1:ℕ):ℝ) ≤ (ν/4)*(nRaw:ℝ) := by
    linarith only [hbN,(div_le_iff₀ hν).mp (hCut (32*(b:ℝ)/ν) (by dsimp only [kRaw]; omega))]
  have hBudgetτ : 4*((b-1:ℕ):ℝ) ≤ (2*τ)*(nRaw:ℝ) := by
    linarith only [hbN,(div_le_iff₀ hτ).mp (hCut (2*(b:ℝ)/τ) (by dsimp only [kRaw]; omega))]
  have hLabels : 4*((b-1:ℕ):ℝ) ≤ δ*(nRaw:ℝ) := by
    linarith only [hbN,(div_le_iff₀ hδ).mp (hCut (4*(b:ℝ)/δ) (by dsimp only [kRaw]; omega))]
  obtain ⟨hRoom,hMC,hExcRounded⟩ := hRound (Fintype.card V) (exceptional g).card nRaw mRaw
    ((le_max_right _ _).trans hN) (hkK.trans (by omega)) (order_eq g mRaw hSizes) hExc hLabels
  let p := ⌊2*α*(nRaw:ℝ)⌋₊
  have hp : (p:ℝ) ≤ 2*α*(nRaw:ℝ) := Nat.floor_le (by positivity)
  have hBudgetDegree : α*(nRaw:ℝ)+((b-1:ℕ):ℝ) ≤ (p:ℝ) := by
    have hB := (div_le_iff₀ hα).mp (hCut ((b:ℝ)/α) (by dsimp only [kRaw]; omega))
    have hFloor : 2*α*(nRaw:ℝ) < (p:ℝ)+1 := Nat.lt_floor_add_one _
    have hB' : ((b-1:ℕ):ℝ) = (b:ℝ)-1 := by
      rw [Nat.cast_sub (show 1 ≤ b by omega),Nat.cast_one]
    linarith only [hB,hFloor,hB']
  have hDegreeD (i : J) : p ≤ inDegree D i ∧ p ≤ outDegree D i := by
    have hp' : (p:ℝ) ≤ (8*α/4)*(Fintype.card J:ℝ) := by dsimp only [nRaw] at hp; linarith only [hp]
    exact ⟨by exact_mod_cast hp'.trans (hInD i),by exact_mod_cast hp'.trans (hOutD i)⟩
  obtain ⟨k,Z₀,P,R₀,_,hkRound,hDiv,hSizeP,hDisP,hOrd,hCover,hZCount,hLoopR,hCycleR,hRobR,hInR,hOutR,hPairsR⟩ :=
    hCycle G D g b ℓ mRaw p (2*e) (d+ξ+ε) hb hℓ hRoom
      (by dsimp only [kRaw] at hkRaw; omega) hSizes (by positivity) (by linarith only [heε,hξ₁,hScale'])
      hRobD hLoop hBudgetν hBudgetτ hBudgetDegree hDegreeD
      (fun i j h => ⟨(hPairs i j h).1,hPad.trans (hPairs i j h).2⟩)
  let m := mRaw/ℓ
  have hKraw : k ≤ nRaw := hkRound ▸ Nat.div_mul_le_self nRaw b
  have hKneed : kNeed ≤ k := by
    have hOrder : nRaw%b+k = nRaw := by rw [hkRound,Nat.mul_comm (nRaw/b) b]; exact Nat.mod_add_div _ _
    have hMod := Nat.mod_lt nRaw hb
    dsimp only [kRaw] at hkRaw
    omega
  have hTwo : 2 ≤ k := ((le_max_left 2 ⌈2/(4*τ)⌉₊).trans (le_max_right kMin _)).trans hKneed
  have hk : 0 < k := by omega
  have hOrder : 2 ≤ (4*τ)*(k:ℝ) := by
    have hN : ⌈2/(4*τ)⌉₊ ≤ k := ((le_max_right 2 _).trans (le_max_right kMin _)).trans hKneed
    have hR : 2/(4*τ) ≤ (k:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    simpa only [mul_comm] using (div_le_iff₀ (show 0 < 4*τ by positivity)).mp hR
  have hExc' : (Z₀.card:ℝ) ≤ δ*(Fintype.card V:ℝ) := by
    rw [hZCount,hkRound]
    exact hExcRounded.trans (mul_le_mul_of_nonneg_right (by linarith only [hθ₀δ]) (Nat.cast_nonneg _))
  have hCover' (x : V) (hx : x ∉ Z₀) : ∃ i, x ∈ P i := by
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp (hCover x hx)
    exact ⟨i,hi⟩
  obtain ⟨hVol,hZ₀⟩ := wound_exceptional_density_of_partition P Z₀ (ℓ*m) δ hSizeP hDisP hOrd hCover'
    (by linarith only [hδζ,hζ₁]) hExc'
  have hProfiles : 2*(Fintype.card V:ℝ) ≤ C*((ℓ*m:ℕ):ℝ) := by
    have hδ₂ : 2*δ ≤ 1 := by linarith only [hδζ,hζ₁]
    have hMass : (Z₀.card:ℝ) ≤ ((k*(ℓ*m):ℕ):ℝ) :=
      hZ₀.trans (mul_le_of_le_one_left (Nat.cast_nonneg _) hδ₂)
    have hCut := mul_le_mul_of_nonneg_right
      (show (k:ℝ) ≤ ((K+1:ℕ):ℝ) by exact_mod_cast hKraw.trans (hkK.trans (by omega))) (Nat.cast_nonneg (ℓ*m))
    rw [←hVol,Nat.cast_add]
    change _ ≤ 4*((K+1:ℕ):ℝ)*((ℓ*m:ℕ):ℝ)
    push_cast at hMass hCut ⊢
    linarith only [hMass,hCut]
  have hPairs' (i j : Fin k) (h : R₀.Adj i j) :
      IsUniform G ε (P i) (P j) ∧ d+ξ+ε ≤ density G (P i) (P j) := by
    refine ⟨?_,(hPairsR i j h).2⟩
    intro A hA B hB hAL hBL
    have he' : 2*(2*e) ≤ ε := by linarith only [heε]
    exact ((hPairsR i j h).1 A hA B hB
      ((mul_le_mul_of_nonneg_left he' (Nat.cast_nonneg _)).trans hAL)
      ((mul_le_mul_of_nonneg_left he' (Nat.cast_nonneg _)).trans hBL)).trans_le he'
  have hTm : M ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hMC)
  have hNm : Ntrim ≤ ℓ*m :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans hMC)).trans (Nat.le_mul_of_pos_left _ hℓ)
  have hMargin := hM m hTm
  let t := ⌈((2*(L+1):ℕ):ℝ)*(2*ξ*(m:ℝ))⌉₊
  let a := ((m-t)/B)*B
  have hRob' : IsRealRobust R₀ (ν/8) (4*τ) := by
    have hν' : ν/4/2 = ν/8 := by ring
    have hτ' : 2*(2*τ) = 4*τ := by ring
    simpa only [hν',hτ'] using hRobR
  have hDegree : α*(Fintype.card V:ℝ) ≤ (8*α)*(Fintype.card V:ℝ) := by
    linarith only [mul_nonneg hα.le (Nat.cast_nonneg (Fintype.card V))]
  obtain ⟨A,X,Z,l,F,hPart,hZincl,hCount,hAdd,hDiv',hPair,hSuper,hFirst,hF,hRoutes,hMult,hWalk'⟩ :=
    hTrimmed G Z₀ P R₀ hk m hNm hTwo hOrder hSizeP hDisP hOrd hCover
      (hExc'.trans (mul_le_mul_of_nonneg_right hδα (Nat.cast_nonneg _)))
      (fun v => ⟨hDegree.trans (hDegrees v).1,hDegree.trans (hDegrees v).2⟩)
      hProfiles hPairs' hCycleR hLoopR hRob' hInR hOutR hMargin
  have hB : 0 < B := (kuhn_osthus_cluster_size_divisibilities f q (L+1) B hq hfq (by omega) (dvd_refl B)).1
  obtain ⟨ht,_,_,hPay⟩ :=
    kuhn_osthus_integral_superregularity_budget m B (2*(L+1)) ξ η hB hξ.le hη.le hη₁ hMargin
  have ha : a ≤ m := (round_down_cluster_size m t B hB (by omega)).2.1.trans (Nat.sub_le _ _)
  have hLost : ((m-a:ℕ):ℝ) ≤ (m:ℝ)/2 := by
    have hηHalf : η ≤ 1/2 := by linarith only [hηζ,hζ₁]
    have h1 := mul_le_mul_of_nonneg_right hηHalf (Nat.cast_nonneg a)
    have h2 : (a:ℝ) ≤ (m:ℝ) := by exact_mod_cast ha
    linarith only [hPay,h1,h2,mul_nonneg hξ.le (Nat.cast_nonneg m)]
  have hAfter : T ≤ a := by
    have h := (le_max_left (2*T) _).trans hMC
    have h' : (2:ℝ)*(T:ℝ) ≤ (m:ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub ha] at hLost
    have hA : (T:ℝ) ≤ a := by linarith only [hLost,h']
    exact_mod_cast hA
  have hZFinal : (Z.card:ℝ) ≤ ζ*(Fintype.card V:ℝ) := by
    have h := mul_le_mul_of_nonneg_right (show δ+η ≤ ζ by linarith only [hδζ,hηζ]) (Nat.cast_nonneg (Fintype.card V))
    linarith only [hAdd,hExc',h]
  exact ⟨k,m,a,hk,Z₀,Z,P,R₀,A,X,l,F,(le_max_left _ _).trans hKneed,hKraw.trans hkK,hOrder,hDiv,hAfter,hDiv',
    hPart,hZincl,hCount,hZFinal,hPair,hSuper,hFirst,hF,hRoutes,hMult,hWalk'⟩

end OverfullWork.DirectedRobustExpansion
