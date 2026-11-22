module

public import OverfullWork.RobustClusterQuotient

@[expose] public section


/-! Two-sided quotients: source fibres and target fibres may differ.
This is sufficient for transfer of robust out-expansion; it does not
assert that the two partitions agree or that such partitions exist. -/
namespace OverfullWork.TwoSidedClusterQuotient
open Finset DirectedRobustExpansion DirectedClusterQuotient
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]
set_option maxHeartbeats 18000000

def quotient (D : Digraph V) (f g : V → Option I) : Digraph I where
  Adj i j := ∃ u v,f u=some i ∧ g v=some j ∧ D.Adj u v

theorem equal_exceptional_card (f g : V → Option I) (m : ℕ)
    (hF : ∀ i,(cluster f i).card=m) (hG : ∀ i,(cluster g i).card=m) :
    (exceptional f).card=(exceptional g).card := by
  have hf := order_eq f m hF
  have hg := order_eq g m hG
  omega

theorem inNeighbours_lift_le (D : Digraph V) (f g : V → Option I) (m : ℕ)
    (hF : ∀ i,(cluster f i).card=m) (S : Finset I) (v : V) (j : I) (hv : g v=some j) :
    inNeighbours D (lift f S) v ≤ m*inNeighbours (quotient D f g) S j := by
  let A := (lift f S).filter fun u => D.Adj u v
  let B := S.filter fun i => (quotient D f g).Adj i j
  have hSub : A ⊆ lift f B := by
    intro u hu
    obtain ⟨i,hi,hui⟩ := (mem_lift f S u).mp (mem_filter.mp hu).1
    exact (mem_lift f B u).mpr ⟨i,mem_filter.mpr ⟨hi,⟨u,v,hui,hv,(mem_filter.mp hu).2⟩⟩,hui⟩
  have hCount := card_le_card hSub
  rw [lift_card f m hF] at hCount
  exact hCount

theorem robust_from_host (D H : Digraph V) (f g : V → Option I) (m : ℕ)
    (hm : 0 < m) (hF : ∀ i,(cluster f i).card=m) (hG : ∀ i,(cluster g i).card=m)
    (r t s T L : ℕ) (hRobust : IsRobustAt D r t)
    (hLoss : ∀ A v,g v ≠ none → inNeighbours D A v ≤ inNeighbours H A v+L)
    (hInterval : t ≤ m*T) (hBudget : (exceptional g).card+L+m*s ≤ r) :
    IsRobustAt (quotient H f g) s T := by
  intro S hLo hHi
  have hLiftLo : t ≤ (lift f S).card := by
    rw [lift_card f m hF]
    exact hInterval.trans (Nat.mul_le_mul_left m hLo)
  have hLiftHi : (lift f S).card+t ≤ Fintype.card V := by
    have hMul := Nat.mul_le_mul_left m hHi
    have hOrder := order_eq f m hF
    rw [lift_card f m hF]
    nlinarith only [hMul,hOrder,hInterval]
  have hGrow := hRobust (lift f S) hLiftLo hLiftHi
  rw [lift_card f m hF] at hGrow
  have hMap : ∀ v ∈ neighbourhood D r (lift f S),∀ i,g v=some i →
      i ∈ neighbourhood (quotient H f g) s S := by
    intro v hv i hgi
    have hSource : r ≤ inNeighbours D (lift f S) v := (mem_filter.mp hv).2
    have hPay := hLoss (lift f S) v (by rw [hgi];exact Option.some_ne_none i)
    have hUpper := inNeighbours_lift_le H f g m hF S v i hgi
    have hMul : m*s ≤ m*inNeighbours (quotient H f g) S i := by omega
    exact mem_filter.mpr ⟨mem_univ _,(mul_le_mul_iff_right₀ hm).mp hMul⟩
  have hUpper := card_le_exceptional_add_lift g m hG
    (neighbourhood D r (lift f S)) (neighbourhood (quotient H f g) s S) hMap
  have hMul : m*(S.card+s) ≤ m*(neighbourhood (quotient H f g) s S).card := by
    nlinarith only [hGrow,hUpper,hBudget]
  exact (mul_le_mul_iff_right₀ hm).mp hMul

end OverfullWork.TwoSidedClusterQuotient
