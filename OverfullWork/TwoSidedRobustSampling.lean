module

public import OverfullWork.NormalizedSampleWindows
public import OverfullWork.DirectedRegularPairSampling

@[expose] public section


/-! Fully normalized fixed-size sampling from bounded two-sided regular
data. Every window and integer rounding condition is discharged. -/
namespace OverfullWork.UniformSubsetSampling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

theorem probability_mono_on_card (k : ℕ) {P Q : Finset V → Prop}
    (h : ∀ X,X.card=k → P X → Q X) : probability k P ≤ probability k Q := by
  unfold probability
  apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro X hX
  obtain ⟨hSupport,hP⟩ := mem_filter.mp hX
  exact mem_filter.mpr ⟨hSupport,h X (mem_powersetCard.mp hSupport).2 hP⟩

end OverfullWork.UniformSubsetSampling

namespace OverfullWork.TwoSidedClusterQuotient
open Finset DirectedRobustExpansion DirectedRegularPairs DirectedClusterQuotient
open InducedDigraphSampling UniformSubsetSampling
open scoped Classical
universe u v
set_option maxHeartbeats 18000000

noncomputable def samplingProfiles {V : Type u} {I : Type v} [Fintype V]
    (f g : V → Option I) (ib : Option (I × Bool)) : Finset V :=
  match ib with
  | none => exceptional f
  | some ib => if ib.2 then cluster f ib.1 else cluster g ib.1

theorem exists_normalized_sampling_threshold (K : ℕ) (ρ τ ε d δ c η σ : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hτ : 0 < τ) (hτQuarter : τ ≤ 1/4) (hρτ : ρ ≤ τ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc : 0 < c) (hc1 : c ≤ 1)
    (hη : 0 < η) (hσ : 0 < σ) (hηK : η*(K:ℝ) ≤ ρ*c/1024) (hηSmall : η ≤ c*σ/4)
    (hε : 0 < ε) (hεc : ε ≤ c/2) (hεSmall : 4*ε/c ≤ ρ/128)
    (hDensityMargin : 4*ε/c+δ ≤ d-ε) :
    ∃ N : ℕ,∀ {V : Type u} [Fintype V] {I : Type v} [Fintype I]
      (D : Digraph V) (R : Digraph I) (f g : V → Option I) (m₀ k : ℕ),
      N ≤ Fintype.card V → k ≤ Fintype.card V → c*(Fintype.card V:ℝ) ≤ (k:ℝ) →
      0 < m₀ → 0 < Fintype.card I → Fintype.card I ≤ K →
      (∀ i,(cluster f i).card=m₀) → (∀ i,(cluster g i).card=m₀) →
      σ*(Fintype.card V:ℝ) ≤ (m₀:ℝ) →
      ((exceptional f).card:ℝ) ≤ ρ*(Fintype.card V:ℝ)/128 →
      IsRealRobust R ρ τ → 8 ≤ τ*(Fintype.card I:ℝ) →
      (∀ i j,R.Adj i j → IsUniform D ε (cluster f i) (cluster g j)) →
      (∀ i j,R.Adj i j → d ≤ density D (cluster f i) (cluster g j)) →
      probability k (fun X => ¬IsRealRobust (induced D X) (δ*ρ^2/256) (2*τ))
        ≤ 1/(Fintype.card V:ℝ)^2 := by
  obtain ⟨N₀,hTail⟩ := exists_uniform_profile_threshold.{u,v} 3 η (by norm_num) hη
  let N₁ := ⌈1024*(K:ℝ)/(ρ*c)⌉₊
  let N₂ := ⌈256/(δ*ρ^2*c)⌉₊
  refine ⟨max N₀ (max 2 (max N₁ N₂)),?_⟩
  intro V _ I _ D R f g m₀ k hn hk hSize hm₀ hIPos hIK hF hG hCells hE hR hTauQ hPairs hDensity
  have hnPos : 0 < Fintype.card V := by omega
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hnPos
  have hKPos : 0 < K := lt_of_lt_of_le hIPos hIK
  have hIOrder : Fintype.card I ≤ Fintype.card V := by
    have hh := order_eq f m₀ hF
    nlinarith only [hh,hm₀]
  have hQProfile : (Fintype.card (Option (I × Bool)):ℝ) ≤ 3*(Fintype.card V:ℝ) := by
    simp only [Fintype.card_option,Fintype.card_prod,Fintype.card_bool,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    exact_mod_cast (show Fintype.card I*2+1 ≤ 3*Fintype.card V by omega)
  have hTail' := hTail (samplingProfiles f g) k (by omega) hk hQProfile
  apply (probability_mono_on_card k ?_).trans hTail'
  intro X hXCard hBad
  by_contra hGood
  have hErrors : ∀ ib : Option (I × Bool),|((X ∩ samplingProfiles f g ib).card:ℝ)-
      ((k:ℝ)/(Fintype.card V:ℝ))*((samplingProfiles f g ib).card:ℝ)| < η*(Fintype.card V:ℝ) := by
    simpa only [not_exists,not_le] using hGood
  let p := (k:ℝ)/(Fintype.card V:ℝ)
  let z := p*(m₀:ℝ)
  let E := η*(Fintype.card V:ℝ)
  let m := ⌊z-E⌋₊
  let M := ⌈z+E⌉₊
  have hp : 0 ≤ p := by dsimp only [p];positivity
  have hp1 : p ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hk)
  have hKRound : (K:ℝ) ≤ ρ*(k:ℝ)/1024 := by
    have hN : 1024*(K:ℝ)/(ρ*c) ≤ (Fintype.card V:ℝ) :=
      (Nat.le_ceil _).trans (by simpa only [N₁,Nat.cast_mul,Nat.cast_ofNat] using (show (N₁:ℝ) ≤ (Fintype.card V:ℝ) by exact_mod_cast (show N₁ ≤ Fintype.card V by omega)))
    have hPaid := (div_le_iff₀ (mul_pos hρ hc)).mp hN
    have hScaled := mul_le_mul_of_nonneg_left hSize hρ.le
    nlinarith only [hPaid,hScaled]
  have hRound : (Fintype.card I:ℝ) ≤ ρ*(k:ℝ)/1024 := (show (Fintype.card I:ℝ) ≤ K by exact_mod_cast hIK).trans hKRound
  have hErrorQ : E*(Fintype.card I:ℝ) ≤ ρ*(k:ℝ)/1024 := by
    have hBound := mul_le_mul_of_nonneg_left (show (Fintype.card I:ℝ) ≤ K by exact_mod_cast hIK)
      (show (0:ℝ) ≤ E by dsimp only [E];positivity)
    have hError := mul_le_mul_of_nonneg_right hηK hnR.le
    have hScaled := mul_le_mul_of_nonneg_left hSize hρ.le
    dsimp only [E] at hBound
    nlinarith only [hBound,hError,hScaled]
  have hpN : p*(Fintype.card V:ℝ)=(k:ℝ) := by dsimp only [p];field_simp
  have hExpectedExc : p*((exceptional f).card:ℝ) ≤ ρ*(k:ℝ)/128 := by
    have hh := mul_le_mul_of_nonneg_left hE hp
    have hId := congrArg (fun z : ℝ => ρ*z/128) hpN
    nlinarith only [hh,hId]
  have hExcSample : p*((exceptional f).card:ℝ) ≤ ρ*(k:ℝ)/64 := by
    have hPos : 0 ≤ ρ*(k:ℝ) := by positivity
    linarith only [hExpectedExc,hPos]
  have hOrder : (Fintype.card V:ℝ)=((exceptional f).card:ℝ)+(m₀:ℝ)*(Fintype.card I:ℝ) := by
    exact_mod_cast order_eq f m₀ hF
  have hExpected : z*(Fintype.card I:ℝ)=(k:ℝ)-p*((exceptional f).card:ℝ) := by
    dsimp only [z,p]
    field_simp
    nlinarith only [hOrder]
  have hpE : p*((exceptional f).card:ℝ) ≤ ((exceptional f).card:ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp1 (Nat.cast_nonneg (exceptional f).card : (0:ℝ) ≤ _)
  have hExpectedLow : (1-ρ/64)*(k:ℝ) ≤ z*(Fintype.card I:ℝ) := by
    nlinarith only [hExpected,hExcSample]
  have hExpectedHigh : z*(Fintype.card I:ℝ) ≤ (k:ℝ) := by
    have hPos : 0 ≤ p*((exceptional f).card:ℝ) := by positivity
    linarith only [hExpected,hPos]
  have hkPos : 0 < k := by
    have hh : (0:ℝ) < k := (mul_pos hc hnR).trans_le hSize
    exact_mod_cast hh
  obtain ⟨hm,hmM,hMass,hGap,hUpper,hRound',hCell,hSource,hNonvacuous,hZ⟩ :=
    normalized_sample_windows k (Fintype.card I) z E ρ τ (4*ε/c) hkPos hIPos hρ hρ1 hτ hτQuarter hTauQ
      (by dsimp only [E];positivity) (by positivity) hεSmall hExpectedLow hExpectedHigh hErrorQ hRound
  have hWindowF : ∀ i,m ≤ (X ∩ cluster f i).card ∧ (X ∩ cluster f i).card ≤ M := by
    intro i
    have hh := hErrors (some (i,true))
    simp only [samplingProfiles,if_true,hF] at hh
    change |((X ∩ cluster f i).card:ℝ)-z| < E at hh
    have hLo := Nat.floor_le (show 0 ≤ z-E by linarith only [hZ])
    have hHi := Nat.le_ceil (z+E)
    constructor
    · have hCast : (m:ℝ) ≤ ((X ∩ cluster f i).card:ℝ) := by
        have he := (abs_lt.mp hh).1;change (⌊z-E⌋₊:ℝ) ≤ _;linarith only [hLo,he]
      exact_mod_cast hCast
    · have hCast : ((X ∩ cluster f i).card:ℝ) ≤ (M:ℝ) := by
        have he := (abs_lt.mp hh).2;change _ ≤ (⌈z+E⌉₊:ℝ);linarith only [hHi,he]
      exact_mod_cast hCast
  have hWindowG : ∀ i,m ≤ (X ∩ cluster g i).card ∧ (X ∩ cluster g i).card ≤ M := by
    intro i
    have hh := hErrors (some (i,false))
    simp only [samplingProfiles,Bool.false_eq_true,if_false,hG] at hh
    change |((X ∩ cluster g i).card:ℝ)-z| < E at hh
    have hLo := Nat.floor_le (show 0 ≤ z-E by linarith only [hZ])
    have hHi := Nat.le_ceil (z+E)
    constructor
    · have hCast : (m:ℝ) ≤ ((X ∩ cluster g i).card:ℝ) := by
        have he := (abs_lt.mp hh).1;change (⌊z-E⌋₊:ℝ) ≤ _;linarith only [hLo,he]
      exact_mod_cast hCast
    · have hCast : ((X ∩ cluster g i).card:ℝ) ≤ (M:ℝ) := by
        have he := (abs_lt.mp hh).2;change _ ≤ (⌈z+E⌉₊:ℝ);linarith only [hHi,he]
      exact_mod_cast hCast
  have hLargeF : ∀ i,(c/2)*((cluster f i).card:ℝ) ≤ ((X ∩ cluster f i).card:ℝ) := by
    intro i
    apply RegularPairVertexSampling.sampled_cell_large X (cluster f i) k c σ hc hσ hnPos hSize
      (by simpa only [hF] using hCells)
    have hh := hErrors (some (i,true))
    simp only [samplingProfiles,if_true] at hh
    exact hh.trans_le (mul_le_mul_of_nonneg_right hηSmall hnR.le)
  have hLargeG : ∀ i,(c/2)*((cluster g i).card:ℝ) ≤ ((X ∩ cluster g i).card:ℝ) := by
    intro i
    apply RegularPairVertexSampling.sampled_cell_large X (cluster g i) k c σ hc hσ hnPos hSize
      (by simpa only [hG] using hCells)
    have hh := hErrors (some (i,false))
    simp only [samplingProfiles,Bool.false_eq_true,if_false] at hh
    exact hh.trans_le (mul_le_mul_of_nonneg_right hηSmall hnR.le)
  let fX := fun v : X => f v.val
  let gX := fun v : X => g v.val
  have hPair : ∀ i j,R.Adj i j → IsUniform (induced D X) (4*ε/c) (cluster fX i) (cluster gX j) ∧
      4*ε/c+δ ≤ density (induced D X) (cluster fX i) (cluster gX j) := by
    intro i j hij
    have hh := regular_pair_on_sample D X (cluster f i) (cluster g j) c ε d hc hc1 hε.le hεc
      (hPairs i j hij) (hDensity i j hij) (hLargeF i) (hLargeG j)
    constructor
    · apply uniform_induced D X (cluster fX i) (cluster gX j) (4*ε/c)
      simpa only [fX,gX,host_cluster] using hh.1
    · rw [induced_density]
      simp only [fX,gX,host_cluster]
      exact hDensityMargin.trans hh.2
  have hN_X : Fintype.card X=k := by simpa only [Fintype.card_coe] using hXCard
  have hExcCard : (exceptional fX).card=(X ∩ exceptional f).card := by
    unfold exceptional
    apply card_bij (fun v _ => v.val)
    · intro v hv
      exact mem_inter.mpr ⟨v.property,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩⟩
    · intro v _ w _ hh;exact Subtype.ext hh
    · intro v hv
      exact ⟨⟨v,(mem_inter.mp hv).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp (mem_inter.mp hv).2).2⟩,rfl⟩
  have hExcX : ((exceptional fX).card:ℝ) ≤ ρ*(Fintype.card X:ℝ)/32 := by
    have hh := hErrors none
    change |((X ∩ exceptional f).card:ℝ)-p*((exceptional f).card:ℝ)| < E at hh
    have hErr : E ≤ ρ*(k:ℝ)/1024 := by
      have hQone : (1:ℝ) ≤ Fintype.card I := by exact_mod_cast hIPos
      have hMult := mul_le_mul_of_nonneg_left hQone (show (0:ℝ) ≤ E by dsimp only [E];positivity)
      nlinarith only [hMult,hErrorQ]
    rw [hN_X,hExcCard]
    have hHigh := (abs_lt.mp hh).2
    have hPos : 0 ≤ ρ*(k:ℝ) := by positivity
    linarith only [hHigh,hExpectedExc,hErr,hPos]
  have hLargeTarget : 2 ≤ δ*ρ^2*(Fintype.card X:ℝ)/128 := by
    have hN : 256/(δ*ρ^2*c) ≤ (Fintype.card V:ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (show N₂ ≤ Fintype.card V by omega))
    have hPaid := (div_le_iff₀ (by positivity : 0 < δ*ρ^2*c)).mp hN
    have hScaled := mul_le_mul_of_nonneg_left hSize (show 0 ≤ δ*ρ^2 by positivity)
    rw [hN_X]
    nlinarith only [hPaid,hScaled]
  apply hBad
  apply normalized_regular_lifting (induced D X) R fX gX m M ρ τ (4*ε/c) δ hIPos hm hmM hρ hρ1
    hτ hδ hδ1 (by positivity) hρτ
  · intro i;simpa only [gX,sampled_cluster_card] using (hWindowG i).1
  · intro i;have hh := lt_of_lt_of_le hm (hWindowF i).1
    simpa only [fX,sampled_cluster_card] using hh
  · intro i;simpa only [fX,sampled_cluster_card] using (hWindowF i).2
  · intro i;simpa only [gX,sampled_cluster_card] using (hWindowG i).2
  · exact fun i j hij => (hPair i j hij).1
  · exact fun i j hij => (hPair i j hij).2
  · exact hR
  · exact hNonvacuous
  · simpa only [hN_X] using hMass
  · simpa only [hN_X] using hGap
  · exact hExcX
  · simpa only [hN_X] using hUpper
  · simpa only [hN_X] using hRound'
  · simpa only [hN_X] using hCell
  · simpa only [hN_X] using hSource
  · exact hLargeTarget

end OverfullWork.TwoSidedClusterQuotient
