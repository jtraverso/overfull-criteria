module

public import OverfullWork.KuhnOsthusChordFromWoundPack
public import OverfullWork.KuhnOsthusPhysicalSubclusterWalk
public import OverfullWork.KuhnOsthusWindingOrdinaryCoordinates

@[expose] public section


/-! The physical chord reserve on the common trimmed partition of §11. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe u

private theorem lower_superregular_relax_error {V : Type*} [Fintype V] {G : Digraph V}
    {A B : Finset V} {ε η d : ℝ} (h : IsLowerSuperregularPair G ε d A B) (hle : ε ≤ η) :
    IsLowerSuperregularPair G η d A B := by
  obtain ⟨d',hLow,hHigh,hPair⟩ := h
  refine ⟨d',hLow,hHigh,?_⟩
  have hA := mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg A.card)
  have hB := mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg B.card)
  exact ⟨fun S hS T hT hSL hTL =>
      (hPair.1 S hS T hT ((by simpa only [mul_comm] using hA : (A.card:ℝ)*ε ≤ (A.card:ℝ)*η).trans hSL)
        ((by simpa only [mul_comm] using hB : (B.card:ℝ)*ε ≤ (B.card:ℝ)*η).trans hTL)).trans_le hle,
    hPair.2.1.trans hle,
    fun x hx => (hPair.2.2.1 x hx).trans hB,
    fun x hx => (hPair.2.2.2 x hx).trans hA⟩

set_option maxHeartbeats 2900000 in
/-- Fix a bound on the cycle degree before the cluster count is chosen.
The errors for the cycle sampler and the walk refinement come next.
Once the number of clusters has an upper bound, the smaller degree of
preprocessing and one common size threshold suffice for Lemma 9.4. -/
theorem exists_kuhn_osthus_chord_on_common_partition (d : ℝ) (ell : ℕ)
    (hd : 0 < d) (hd₁ : d ≤ 1) (hell : 0 < ell) :
    ∃ d₁Max : ℝ, 0 < d₁Max ∧
      ∀ d₁ : ℝ, 0 < d₁ → d₁ ≤ d₁Max → d₁ < d →
      ∃ ξMax εC : ℝ, 0 < ξMax ∧ 0 < εC ∧ εC ≤ d₁/512 ∧
      ∀ (J : ℕ) (ξ : ℝ), 0 < J → 0 < ξ → ξ ≤ ξMax →
      ∃ d₃Max : ℝ, 0 < d₃Max ∧ ∃ T : ℕ,
      ∀ {V : Type u} [Fintype V] {n f j K : ℕ} (G PG : Digraph V) (Z : Finset V)
        (X : Fin n → Finset V) (F : Fin ell → Equiv.Perm (Fin n))
        (hi : n = f*j) (hj : 0 < j) (base mWalk mStyle lossPG t r₂ r₃ : ℕ) (d₃ σ : ℝ),
        let e := finCongr hi.symm
        let Y (i : Fin (f*j)) := X (e i)
        let r₁ := ⌊d₁*(base:ℝ)⌋₊
        let sub := Function.Embedding.subtype (· ∈ Zᶜ)
        2 ≤ f → 0 < K → n ≤ J → PG ≤ G →
        (∀ x ∉ Z, inDegree PG x ≤ lossPG ∧ outDegree PG x ≤ lossPG) →
        0 ≤ d₃ → d₃ ≤ d₃Max → lossPG = ⌊d₃*(base:ℝ)⌋₊ → t ≤ lossPG →
        t*(f*n) = (K*f)*r₃ → r₂ ≤ r₁ → r₃ ≤ r₁ →
        2*Z.card ≤ Fintype.card V → Zᶜ.card = n*base →
        T ≤ mWalk → T ≤ base → base = 4*ell*mWalk →
        (∀ i, (X i).card = base) → (∀ i i', i ≠ i' → Disjoint (X i) (X i')) →
        (∀ i, Disjoint (X i) Z) → (∀ v ∉ Z, ∃ i, v ∈ X i) →
        HasSpanningCycle (fun u v : (Σ _ : Fin ell, Fin n) => F u.1 u.2 = v.2) →
        (∀ a i, IsLowerSuperregularPair G ξ d (X i) (X (F a i))) →
        (∀ i, IsLowerSuperregularPair G ξ d (X i) (X (finRotate n i))) →
        ∀ E : WoundFactorPacking (G \ PG) Z Y hj K mStyle r₃ σ,
        ∃ (order : Fin (ell*n) ≃ Fin ell × Fin n) (c : ↥Zᶜ → Fin (f*j))
          (B : Digraph ↥Zᶜ) (Q : Fin (ell*n) × Fin 4 → Finset ↥Zᶜ)
          (M : ∀ i, Fin r₂ → Q i ≃ Q (((finRotate (ell*n)).prodCongr (Equiv.refl (Fin 4))) i)),
          let s := finRotate (f*j)
          let A (i : Fin (f*j)) := (univ : Finset ↥Zᶜ).filter (fun v => c v = i)
          let L := liftDirectedPair sub sub B
          let U := liftDirectedPair sub sub
            (successorCellMatchingUnion Q ((finRotate (ell*n)).prodCongr (Equiv.refl (Fin 4))) M)
          let EF := ⨆ i, ⨆ j, (E.factors i j).digraph
          let CA := (U ⊔ EF) ⊔ L
          (∀ i, (order (finRotate (ell*n) i)).2 = F (order i).1 (order i).2) ∧
          (∀ i v, c v = i ↔ v.val ∈ Y i) ∧ (∀ i, (A i).card = base) ∧
          CA ≤ G \ PG ∧ EF ≤ CA ∧ Disjoint U EF ∧ Disjoint (U ⊔ EF) L ∧
          (∀ i, IsSuperregularPair (induced L Zᶜ) εC d₁ (A i) (A (s i))) ∧
          (∀ x y, L.Adj x y → ∃ u v : ↥Zᶜ, u.val = x ∧ v.val = y ∧ c v = s (c u)) ∧
          (∀ v, ∃ i, v ∈ Q i) ∧ (∀ i v, v ∈ Q i → c v = e.symm (order i.1).2) ∧
          (∀ i, (Q i).card = mWalk) ∧ (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
          (∀ i p z, p ≠ z → ∀ x, M i p x ≠ M i z x) ∧
          ∀ x, let D := if x ∈ Z then (K*f)*r₃ else r₁+r₂+r₃
            inDegree CA x = D ∧ outDegree CA x = D := by
  have hellR : (0:ℝ) < ell := by exact_mod_cast hell
  let ηW := d/16
  let εW := ηW/32
  let aW := ηW/8
  have hηW : 0 < ηW := by dsimp only [ηW]; positivity
  have hεW : 0 < εW := by dsimp only [εW]; positivity
  have haW : 0 < aW := by dsimp only [aW]; positivity
  let d₁Max := aW*ηW/(8*(ell:ℝ))
  have hd₁Max : 0 < d₁Max := by dsimp only [d₁Max]; positivity
  refine ⟨d₁Max,hd₁Max,?_⟩
  intro d₁ hd₁Pos hd₁Cap hd₁d
  obtain ⟨εB,ηB,δB,hεB,hεB₁,hηB,hηB₁,hδB,hTolB,hBaseBudget,hCentre,hTolC⟩ :=
    exists_chord_cycle_sampling_tolerances d₁ d hd₁Pos (hd₁d.le.trans hd₁) hd₁d
  let εD := εB/4
  let ε₀ := εD/8
  let aD := εD/8
  let εStart := min ε₀ εW/8
  let aPG := εStart
  let ξMax := εStart/(4*max 2 (ell:ℝ))
  have hεD : 0 < εD := by dsimp only [εD]; positivity
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  have haD : 0 < aD := by dsimp only [aD]; positivity
  have hStart : 0 < εStart := div_pos (lt_min hε₀ hεW) (by norm_num)
  have hξMax : 0 < ξMax := by dsimp only [ξMax]; positivity
  refine ⟨ξMax,ηB+εB, hξMax,by positivity,hTolC,?_⟩
  intro J ξ hJ hξ hξCap
  have hJR : (0:ℝ) < J := by exact_mod_cast hJ
  let d₃Max := min (aPG*ε₀) (min ((aPG*εW)/(ell:ℝ)) ((aD*εD)/(J:ℝ)))
  have hAPG : 0 < aPG := hStart
  have hd₃Max : 0 < d₃Max := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hStart₀ : 4*εStart ≤ ε₀ := by
    have h : min ε₀ εW ≤ ε₀ := min_le_left _ _
    dsimp only [εStart]
    linarith only [h,hε₀]
  have hStartW : 4*εStart ≤ εW := by
    have h : min ε₀ εW ≤ εW := min_le_right _ _
    dsimp only [εStart]
    linarith only [h,hεW]
  have hεW₁ : εW ≤ 1 := by dsimp only [εW,ηW]; linarith only [hd₁]
  have hηW₁ : ηW ≤ 1 := by dsimp only [ηW]; linarith only [hd₁]
  have hStart₁ : εStart ≤ 1 := by linarith only [hStartW,hεW₁]
  have hεD₁ : εD ≤ 1 := by dsimp only [εD]; linarith only [hεB₁]
  have hε₀₁ : ε₀ ≤ 1 := by dsimp only [ε₀]; linarith only [hεD₁]
  have hRef : 2*(max 2 (ell:ℝ)*ξ) ≤ εStart := by
    have hm : 0 < max 2 (ell:ℝ) := (by norm_num : (0:ℝ) < 2).trans_le (le_max_left _ _)
    have h := (le_div_iff₀ (by positivity : 0 < 4*max 2 (ell:ℝ))).mp hξCap
    linarith only [h,mul_nonneg hm.le hξ.le,hStart]
  have hξStart : ξ ≤ εStart := by
    have h := mul_le_mul_of_nonneg_right (le_max_left 2 (ell:ℝ)) hξ.le
    linarith only [h,hRef,hξ]
  have hFloor : 2*ξ ≤ d := by
    have hW : εW ≤ d := by dsimp only [εW,ηW]; linarith only [hd]
    linarith only [hξStart,hStartW,hW,hξ]
  obtain ⟨NW,hNW⟩ := exists_kuhn_osthus_physical_subcluster_walk.{u} (8*(J:ℝ)) ξ εStart d ell hell
    (by positivity) hξ hStart hStart₁ hFloor hRef
  obtain ⟨N₁,N₂,hN⟩ := kuhn_osthus_chord_reserve_from_wound_pack.{u}
    (2*(ell:ℝ)*(J:ℝ)) εStart ε₀ εD εB ηB δB εW ηW d d₁ d aD aW aPG
    (by positivity) hε₀ hε₀₁ hεD hεD₁ le_rfl hεB hεB₁ hηB hηB₁ hδB hTolB hBaseBudget
    hεW hεW₁ hηW hηW₁ haD.le haW.le hAPG.le hd₁Pos.le hCentre
    (by dsimp only [εW,ηW]; linarith only [hd]) (by dsimp only [ηW]; linarith only [hd])
    (by dsimp only [aPG]; linarith only [hStart₀]) (by dsimp only [aPG]; linarith only [hStartW])
    (by dsimp only [ε₀,aD]; linarith only [hεD])
    (by dsimp only [εW,aW]; linarith only [hηW])
  let T := max 1 (max NW (max N₁ N₂))
  refine ⟨d₃Max,hd₃Max,T,?_⟩
  intro V _ n f j K G PG Z X F hi hj base mWalk mStyle lossPG t r₂ r₃ d₃ σ e Y r₁ sub
    hf hK hnJ hPG hLoss hd₃ hd₃Cap hLossEq ht hChord hR₂ hR₃ hHalf hOrd hTWalk hTBase hBase
    hSize hDis hOrdinary hCover hWalk hPairs hCycle E
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  have htm : 0 < mWalk := (le_max_left _ _).trans hTWalk
  have hBasePos : 0 < base := (le_max_left _ _).trans hTBase
  have hV : Fintype.card V ≤ 2*n*base := by
    have h := card_compl_add_card Z
    rw [hOrd] at h
    rw [Nat.mul_assoc]
    omega
  have hVR : (Fintype.card V:ℝ) ≤ 2*(J:ℝ)*(base:ℝ) := by
    exact_mod_cast hV.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hnJ))
  have hPhysicalSize : base = ell*(4*mWalk) := hBase.trans (by ring)
  have hSizeW : NW ≤ ell*(4*mWalk) := by
    have h := (le_max_left NW _).trans ((le_max_right 1 _).trans hTBase)
    rwa [←hPhysicalSize]
  have hProfile : 4*(Fintype.card V:ℝ) ≤ (8*(J:ℝ))*((ell*(4*mWalk):ℕ):ℝ) := by
    rw [←hPhysicalSize]
    linarith only [hVR]
  have hWalkData := hNW G X F (4*mWalk) hWalk (by omega) hSizeW
    (fun i => (hSize i).trans hPhysicalSize) hProfile hDis hPairs
  have hWalkSize : ell*Fintype.card (Fin n) = ell*n := congrArg (ell*·) (Fintype.card_fin n)
  rw [hWalkSize] at hWalkData
  obtain ⟨order,D,hOrder,_,hD,hDDis,hDCover,hDPair⟩ := hWalkData
  let W : Fin (ell*n) → Finset ↥Zᶜ := fun i => (D i).subtype (· ∈ Zᶜ)
  have hDOrd (i) : D i ⊆ Zᶜ := fun v hv => mem_compl.mpr fun hz =>
    disjoint_left.mp (hOrdinary (order i).2) ((hD i).2 hv) hz
  have hWMap (i) : (W i).map sub = D i := by
    ext v
    constructor
    · intro hv
      obtain ⟨w,hw,rfl⟩ := mem_map.mp hv
      exact mem_subtype.mp hw
    · intro hv
      exact mem_map.mpr ⟨⟨v,hDOrd i hv⟩,mem_subtype.mpr hv,rfl⟩
  have hWSize (i) : (W i).card = 4*mWalk :=
    (card_map sub).symm.trans ((congrArg card (hWMap i)).trans (hD i).1)
  have hWPair (i : Fin (ell*n)) :
      IsLowerSuperregularPair (induced G Zᶜ) εStart d (W i) (W (finRotate (ell*n) i)) := by
    obtain ⟨d',hL,hH,hP⟩ := hDPair i
    refine ⟨d',hL,hH,superregular_pullDirectedPair G sub sub _ _ _ _ ?_⟩
    rwa [hWMap,hWMap]
  obtain ⟨c,hCoord,hMap,hSizeY,hTransfer⟩ := exists_kuhn_osthus_winding_ordinary_coordinates G Z Y
    (fun i => hOrdinary (e i)) (fun i j h => hDis _ _ (e.injective.ne h)) (fun v hv => by
      obtain ⟨i,hi⟩ := hCover v hv
      exact ⟨e.symm i,by simpa only [Y,e.apply_symm_apply] using hi⟩)
  let A (i : Fin (f*(j+1))) := (univ : Finset ↥Zᶜ).filter (fun v => c v = i)
  have hACard (i : Fin (f*(j+1))) : (A i).card = base := by
    convert (hSizeY i).trans (hSize (e i)) using 1
    apply congrArg card
    ext v
    simp only [A,mem_filter]
  have hRotate (i : Fin (f*(j+1))) : e (finRotate (f*(j+1)) i) = finRotate n (e i) := by
    apply Fin.ext
    change (finRotate (f*(j+1)) i).val = (finRotate n (e i)).val
    rw [finRotate_val_modulo,finRotate_val_modulo]
    exact congrArg ((i.val+1) % ·) hi.symm
  have hAPair (i : Fin (f*(j+1))) :
      IsLowerSuperregularPair (induced G Zᶜ) εStart d (A i) (A (finRotate (f*(j+1)) i)) := by
    have hPair : IsLowerSuperregularPair G εStart d (Y i) (Y (finRotate (f*(j+1)) i)) :=
      lower_superregular_relax_error (by simpa only [Y,hRotate] using hCycle (e i)) hξStart
    convert hTransfer i _ εStart d hPair using 1 <;> ext v <;> simp only [A,mem_filter]
  have hBW : (base:ℝ) = 4*(ell:ℝ)*(mWalk:ℝ) := by exact_mod_cast hBase
  have hLossR : (lossPG:ℝ) ≤ d₃*(base:ℝ) := by rw [hLossEq]; exact Nat.floor_le (by positivity)
  have hDBase : d₃ ≤ aPG*ε₀ := hd₃Cap.trans (min_le_left _ _)
  have hDWalk : d₃*(ell:ℝ) ≤ aPG*εW := (le_div_iff₀ hellR).mp
    (hd₃Cap.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hDExc : d₃*(J:ℝ) ≤ aD*εD := (le_div_iff₀ hJR).mp
    (hd₃Cap.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hPG₀ : (lossPG:ℝ) ≤ aPG*((base:ℝ)*ε₀) := by
    linarith only [hLossR,mul_le_mul_of_nonneg_right hDBase (Nat.cast_nonneg base)]
  have hPGW : (lossPG:ℝ) ≤ aPG*(((4*mWalk:ℕ):ℝ)*εW) := by
    have h := mul_le_mul_of_nonneg_right hDWalk (Nat.cast_nonneg (4*mWalk) : (0:ℝ) ≤ ↑(4*mWalk))
    push_cast at h ⊢
    rw [hBW] at hLossR
    linarith only [h,hLossR]
  have hChord' : K*r₃ = t*n := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < f)
    calc
      f*(K*r₃) = (K*f)*r₃ := by ring
      _ = t*(f*n) := hChord.symm
      _ = f*(t*n) := by ring
  have hExc : (r₃:ℝ) ≤ aD*((base:ℝ)*εD) := by
    have hPay : r₃ ≤ lossPG*J := calc
      r₃ ≤ K*r₃ := Nat.le_mul_of_pos_left _ hK
      _ = t*n := hChord'
      _ ≤ lossPG*J := Nat.mul_le_mul ht hnJ
    have hR : (r₃:ℝ) ≤ (lossPG:ℝ)*(J:ℝ) := by exact_mod_cast hPay
    have hPay₁ := mul_le_mul_of_nonneg_right hLossR hJR.le
    have hPay₂ := mul_le_mul_of_nonneg_right hDExc (Nat.cast_nonneg base)
    linarith only [hR,hPay₁,hPay₂]
  have hCap₁ := (le_div_iff₀ (by positivity : 0 < 8*(ell:ℝ))).mp hd₁Cap
  have hR₁ : (r₁:ℝ) ≤ d₁*(base:ℝ) := Nat.floor_le (by positivity)
  have hR₁W : (2:ℝ)*(r₁:ℝ) ≤ aW*((mWalk:ℝ)*ηW) := by
    rw [hBW] at hR₁
    linarith only [hR₁,mul_le_mul_of_nonneg_right hCap₁ (Nat.cast_nonneg mWalk)]
  have hPayW : ((r₁+r₃:ℕ):ℝ) ≤ aW*((mWalk:ℝ)*ηW) := by
    have h : (r₃:ℝ) ≤ r₁ := by exact_mod_cast hR₃
    push_cast
    linarith only [hR₁W,h]
  have hTwo : (r₂:ℝ) ≤ r₁ := by exact_mod_cast hR₂
  have hmR : (0:ℝ) < mWalk := by exact_mod_cast htm
  have hDemand : (r₂:ℝ) < (d-2*ηW)*((mWalk:ℝ)*ηW) := by
    have h : aW < d-2*ηW := by dsimp only [aW,ηW]; linarith only [hd]
    linarith only [hTwo,hR₁W,mul_lt_mul_of_pos_right h (by positivity : 0 < (mWalk:ℝ)*ηW)]
  have hRoom : (r₂:ℝ) ≤ (d-3*ηW)*(mWalk:ℝ) := by
    have hA : aW*ηW ≤ d-3*ηW := by
      have h := mul_le_of_le_one_right haW.le hηW₁
      dsimp only [aW,ηW] at h ⊢
      linarith only [h,hd]
    linarith only [hTwo,hR₁W,mul_le_mul_of_nonneg_right hA hmR.le]
  have hVolume : 2*(Fintype.card ↥Zᶜ:ℝ) ≤ (2*(ell:ℝ)*(J:ℝ))*((4*mWalk:ℕ):ℝ) := by
    rw [Fintype.card_coe,hOrd,Nat.cast_mul,hBW]
    push_cast
    have h := mul_le_mul_of_nonneg_right (by exact_mod_cast hnJ : (n:ℝ) ≤ J)
      (by positivity : 0 ≤ 8*(ell:ℝ)*(mWalk:ℝ))
    linarith only [h]
  have h₁ : N₁ ≤ base := (le_max_left _ _).trans ((le_max_right NW _).trans ((le_max_right 1 _).trans hTBase))
  have h₂ : N₂ ≤ 4*mWalk :=
    ((le_max_right N₁ _).trans ((le_max_right NW _).trans ((le_max_right 1 _).trans hTWalk))).trans (by omega)
  obtain ⟨B,Q,M,hCA,hKeep,hApart,hApart',hSuper,hNext,_,hQCover,hQParent,hQSize,hQDis,hM,hDegree⟩ :=
    hN G PG Z c W (finRotate (ell*n)) (fun i => e.symm (order i).2) Y base mWalk mStyle lossPG σ hf hPG hLoss
      (fun i => by
        convert hMap i using 1
        congr 1
        ext v
        simp only [mem_filter])
      (fun v => by
        obtain ⟨i,hi⟩ := hDCover v.val (hCover v.val (mem_compl.mp v.prop))
        exact ⟨i,mem_subtype.mpr hi⟩)
      (fun i j hij => disjoint_left.mpr (fun v h1 h2 =>
        disjoint_left.mp (hDDis i j hij) (mem_subtype.mp h1) (mem_subtype.mp h2)))
      (fun i v hv => (hCoord _ _).mpr (by
        simpa only [Y,e.apply_symm_apply] using (hD i).2 (mem_subtype.mp hv)))
      h₁ hBasePos hACard h₂ htm hWSize hVolume hAPair hWPair hPG₀ hPGW hExc hPayW hDemand hRoom E
  exact ⟨order,c,B,Q,M,hOrder,hCoord,hACard,hCA,hKeep,hApart,hApart',hSuper,hNext,
    hQCover,hQParent,hQSize,hQDis,hM,hDegree⟩

end OverfullWork.DirectedRobustExpansion
