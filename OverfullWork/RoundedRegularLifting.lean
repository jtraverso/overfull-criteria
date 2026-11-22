module

public import OverfullWork.RegularClusterLifting

@[expose] public section


/-! Explicit rounded budgets for normalized reverse robust transfer.
The real parameters precede the graph; ceilings and floors are paid. -/
namespace OverfullWork.DirectedClusterQuotient
open Finset DirectedRobustExpansion DirectedRegularPairs
open scoped Classical
set_option maxHeartbeats 18000000

theorem rounded_lifting_budgets (n k m M e : ℕ) (ρ τ ε δ : ℝ)
    (hk : 0 < k) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hτ : 0 < τ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hερ : 0 ≤ ε) (hρτ : ρ ≤ τ)
    (hMass : n ≤ 2*m*k)
    (hGap : ((M-m:ℕ):ℝ)*(k:ℝ) ≤ ρ*(n:ℝ)/32)
    (hExc : (e:ℝ) ≤ ρ*(n:ℝ)/32)
    (hUpper : (M:ℝ)*(k:ℝ) ≤ (1+ρ/32)*(n:ℝ))
    (hRound : (k:ℝ) ≤ ρ*(n:ℝ)/64)
    (hCell : (M:ℝ) ≤ τ*(n:ℝ)/4)
    (hSource : ε*(M:ℝ)*(k:ℝ) ≤ ρ*(n:ℝ)/64) :
    let h := ⌈ρ*(n:ℝ)/(64*(k:ℝ))⌉₊
    let r := ⌈ρ*(k:ℝ)⌉₊
    let t := ⌈τ*(k:ℝ)⌉₊
    let s := ⌊δ*ρ^2*(n:ℝ)/128⌋₊
    let T := ⌈2*τ*(n:ℝ)⌉₊
    ε*(M:ℝ) ≤ (h:ℝ) ∧
    (s:ℝ) ≤ δ*(h:ℝ)*(r:ℝ) ∧
    e+h*k+M*t ≤ T ∧
    e+((M-m)+h+h)*k+s ≤ m*r := by
  dsimp only
  let h := ⌈ρ*(n:ℝ)/(64*(k:ℝ))⌉₊
  let r := ⌈ρ*(k:ℝ)⌉₊
  let t := ⌈τ*(k:ℝ)⌉₊
  let s := ⌊δ*ρ^2*(n:ℝ)/128⌋₊
  let T := ⌈2*τ*(n:ℝ)⌉₊
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hHLo : ρ*(n:ℝ)/64 ≤ (h:ℝ)*(k:ℝ) := by
    have hh := Nat.le_ceil (ρ*(n:ℝ)/(64*(k:ℝ)))
    have hh' : (ρ*(n:ℝ)/64)/(k:ℝ) ≤ (h:ℝ) := by simpa only [h,div_mul_eq_div_div] using hh
    exact (div_le_iff₀ hkR).mp hh'
  have hHHi : (h:ℝ)*(k:ℝ) ≤ ρ*(n:ℝ)/32 := by
    have hh : (h:ℝ) < ρ*(n:ℝ)/(64*(k:ℝ))+1 := Nat.ceil_lt_add_one (by positivity)
    have hh' : (h:ℝ)-1 < (ρ*(n:ℝ)/64)/(k:ℝ) := by
      rw [div_mul_eq_div_div] at hh
      linarith only [hh]
    have hPaid := (lt_div_iff₀ hkR).mp hh'
    nlinarith only [hPaid,hRound]
  have hRLo : ρ*(k:ℝ) ≤ (r:ℝ) := Nat.le_ceil _
  have hTUpper : (t:ℝ) < τ*(k:ℝ)+1 := Nat.ceil_lt_add_one (by positivity)
  have hSUpper : (s:ℝ) ≤ δ*ρ^2*(n:ℝ)/128 := Nat.floor_le (by positivity)
  have hTLo : 2*τ*(n:ℝ) ≤ (T:ℝ) := Nat.le_ceil _
  have hSLinear : (s:ℝ) ≤ ρ*(n:ℝ)/32 := by
    have hSquare : ρ^2 ≤ ρ := by nlinarith only [hρ,hρ1]
    have hD := mul_le_mul_of_nonneg_right hδ1 (show (0:ℝ) ≤ ρ^2 by positivity)
    have hDSquare : δ*ρ^2 ≤ ρ := by nlinarith only [hD,hSquare]
    have hN := mul_le_mul_of_nonneg_right hDSquare (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    have hPos : 0 ≤ ρ*(n:ℝ) := by positivity
    nlinarith only [hSUpper,hN,hPos]
  refine ⟨?_,?_,?_,?_⟩
  · apply (mul_le_mul_iff_left₀ hkR).mp
    nlinarith only [hSource,hHLo]
  · have hRH := mul_le_mul_of_nonneg_left hRLo (Nat.cast_nonneg h : (0:ℝ) ≤ h)
    have hHH := mul_le_mul_of_nonneg_left hHLo hρ.le
    have hBound : ρ^2*(n:ℝ)/64 ≤ (h:ℝ)*(r:ℝ) := by nlinarith only [hRH,hHH]
    have hScaled := mul_le_mul_of_nonneg_left hBound hδ.le
    have hPos : 0 ≤ δ*ρ^2*(n:ℝ) := by positivity
    nlinarith only [hSUpper,hScaled,hPos]
  · have hMT := mul_le_mul_of_nonneg_left hTUpper.le (Nat.cast_nonneg M : (0:ℝ) ≤ M)
    have hτUpper := mul_le_mul_of_nonneg_left hUpper hτ.le
    have hρn := mul_le_mul_of_nonneg_right hρτ (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    have hρτn := mul_le_mul_of_nonneg_right hρ1 (show (0:ℝ) ≤ τ*(n:ℝ) by positivity)
    have hCast : (e:ℝ)+(h:ℝ)*(k:ℝ)+(M:ℝ)*(t:ℝ) ≤ (T:ℝ) := by
      nlinarith only [hExc,hHHi,hMT,hτUpper,hCell,hρn,hρτn,hTLo]
    simpa only [h,t,T,Nat.cast_mul,Nat.cast_ofNat] using (by exact_mod_cast hCast : e+h*k+M*t ≤ T)
  · have hMR := mul_le_mul_of_nonneg_left hRLo (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    have hMassR : (n:ℝ) ≤ 2*(m:ℝ)*(k:ℝ) := by exact_mod_cast hMass
    have hScaled := mul_le_mul_of_nonneg_left hMassR hρ.le
    have hPos : 0 ≤ ρ*(n:ℝ) := by positivity
    have hCast : (e:ℝ)+(((M-m:ℕ):ℝ)+(h:ℝ)+(h:ℝ))*(k:ℝ)+(s:ℝ) ≤ (m:ℝ)*(r:ℝ) := by
      nlinarith only [hExc,hGap,hHHi,hSLinear,hMR,hScaled,hPos]
    simpa only [h,r,s,Nat.cast_mul,Nat.cast_ofNat] using (by exact_mod_cast hCast : e+((M-m)+h+h)*k+s ≤ m*r)

variable {V I : Type*} [Fintype V] [Fintype I]

theorem normalized_regular_lifting (D : Digraph V) (R : Digraph I) (f : V → Option I)
    (m M : ℕ) (ρ τ ε δ : ℝ) (hk : 0 < Fintype.card I)
    (hm : 0 < m) (hmM : m ≤ M) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hτ : 0 < τ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hρτ : ρ ≤ τ)
    (hLower : ∀ i,m ≤ (cluster f i).card) (hUpperSize : ∀ i,(cluster f i).card ≤ M)
    (hPairs : ∀ i j,R.Adj i j → IsUniform D ε (cluster f i) (cluster f j))
    (hDensity : ∀ i j,R.Adj i j → ε+δ ≤ density D (cluster f i) (cluster f j))
    (hR : IsRealRobust R ρ τ) (hNonvacuous : 2*⌈τ*(Fintype.card I:ℝ)⌉₊ ≤ Fintype.card I)
    (hMass : Fintype.card V ≤ 2*m*Fintype.card I)
    (hGap : ((M-m:ℕ):ℝ)*(Fintype.card I:ℝ) ≤ ρ*(Fintype.card V:ℝ)/32)
    (hExc : ((exceptional f).card:ℝ) ≤ ρ*(Fintype.card V:ℝ)/32)
    (hUpper : (M:ℝ)*(Fintype.card I:ℝ) ≤ (1+ρ/32)*(Fintype.card V:ℝ))
    (hRound : (Fintype.card I:ℝ) ≤ ρ*(Fintype.card V:ℝ)/64)
    (hCell : (M:ℝ) ≤ τ*(Fintype.card V:ℝ)/4)
    (hSource : ε*(M:ℝ)*(Fintype.card I:ℝ) ≤ ρ*(Fintype.card V:ℝ)/64)
    (hLarge : 2 ≤ δ*ρ^2*(Fintype.card V:ℝ)/128) :
    IsRealRobust D (δ*ρ^2/256) (2*τ) := by
  let h := ⌈ρ*(Fintype.card V:ℝ)/(64*(Fintype.card I:ℝ))⌉₊
  let r := ⌈ρ*(Fintype.card I:ℝ)⌉₊
  let t := ⌈τ*(Fintype.card I:ℝ)⌉₊
  let s := ⌊δ*ρ^2*(Fintype.card V:ℝ)/128⌋₊
  let T := ⌈2*τ*(Fintype.card V:ℝ)⌉₊
  obtain ⟨hh,hThreshold,hInterval,hGrowth⟩ := rounded_lifting_budgets (Fintype.card V)
    (Fintype.card I) m M (exceptional f).card ρ τ ε δ hk hρ hρ1 hτ hδ hδ1 hε.le
    hρτ hMass hGap hExc hUpper hRound hCell hSource
  have hr : 0 < r := by
    have hPos : 0 < ρ*(Fintype.card I:ℝ) := mul_pos hρ (by exact_mod_cast hk)
    exact Nat.ceil_pos.mpr hPos
  have hInteger := robust_of_regular_clusters D R f m M h h r t s T ε (ε+δ)
    hm hmM hr hε (by linarith only [hδ]) hLower hUpperSize hPairs hDensity
    (integer_of_real R ρ τ hρ.le hR) hNonvacuous (by simpa [h,Nat.cast_mul,mul_comm] using hh)
    (by simpa [h,Nat.cast_mul,mul_comm] using hh) (by convert hThreshold using 1 <;> ring)
    hInterval hGrowth
  apply real_of_integer_at_ceil_interval D s (δ*ρ^2/256) (2*τ) (by positivity) hInteger
  have hFloor := Nat.lt_floor_add_one (δ*ρ^2*(Fintype.card V:ℝ)/128)
  change δ*ρ^2/256*(Fintype.card V:ℝ) ≤ (⌊δ*ρ^2*(Fintype.card V:ℝ)/128⌋₊:ℝ)
  linarith only [hFloor,hLarge]

end OverfullWork.DirectedClusterQuotient
