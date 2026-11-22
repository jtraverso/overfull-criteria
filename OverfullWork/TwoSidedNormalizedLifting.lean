module

public import OverfullWork.TwoSidedRegularLifting
public import OverfullWork.RoundedRegularLifting

@[expose] public section


/-! Normalized reverse transfer for different source and target fibres. -/
namespace OverfullWork.TwoSidedClusterQuotient
open Finset DirectedRobustExpansion DirectedRegularPairs DirectedClusterQuotient
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

theorem normalized_regular_lifting (D : Digraph V) (R : Digraph I) (f g : V → Option I)
    (m M : ℕ) (ρ τ ε δ : ℝ) (hk : 0 < Fintype.card I)
    (hm : 0 < m) (hmM : m ≤ M) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hτ : 0 < τ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hρτ : ρ ≤ τ)
    (hLower : ∀ i,m ≤ (cluster g i).card)
    (hSourceLower : ∀ i,0 < (cluster f i).card) (hUpperSize : ∀ i,(cluster f i).card ≤ M)
    (hTargetUpper : ∀ i,(cluster g i).card ≤ M)
    (hPairs : ∀ i j,R.Adj i j → IsUniform D ε (cluster f i) (cluster g j))
    (hDensity : ∀ i j,R.Adj i j → ε+δ ≤ density D (cluster f i) (cluster g j))
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
  obtain ⟨hh,hThreshold,hInterval,hGrowth⟩ := DirectedClusterQuotient.rounded_lifting_budgets (Fintype.card V)
    (Fintype.card I) m M (exceptional f).card ρ τ ε δ hk hρ hρ1 hτ hδ hδ1 hε.le
    hρτ hMass hGap hExc hUpper hRound hCell hSource
  have hr : 0 < r := by
    have hPos : 0 < ρ*(Fintype.card I:ℝ) := mul_pos hρ (by exact_mod_cast hk)
    exact Nat.ceil_pos.mpr hPos
  have hInteger := robust_of_regular_clusters D R f g m M h h r t s T ε (ε+δ)
    hm hmM hr hε (by linarith only [hδ]) hLower hSourceLower hUpperSize hTargetUpper hPairs hDensity
    (integer_of_real R ρ τ hρ.le hR) hNonvacuous (by simpa [h,Nat.cast_mul,mul_comm] using hh)
    (by simpa [h,Nat.cast_mul,mul_comm] using hh) (by convert hThreshold using 1 <;> ring)
    hInterval hGrowth
  apply real_of_integer_at_ceil_interval D s (δ*ρ^2/256) (2*τ) (by positivity) hInteger
  have hFloor := Nat.lt_floor_add_one (δ*ρ^2*(Fintype.card V:ℝ)/128)
  change δ*ρ^2/256*(Fintype.card V:ℝ) ≤ (⌊δ*ρ^2*(Fintype.card V:ℝ)/128⌋₊:ℝ)
  linarith only [hFloor,hLarge]

end OverfullWork.TwoSidedClusterQuotient
