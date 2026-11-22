module

public import OverfullWork.PriorityCopyAllocation

@[expose] public section


/-! # Construct the second middle-copy allocation with controlled deficits

This is the two-stage priority choice in CMS Case 2, Step 2, in a
slightly weaker quantitative form: all paired lower-bound deficits sum
to at most F+card(H)+1. Actual source budgets can pay this loss.
-/
namespace OverfullWork.BalancedMiddleAllocation
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

def cap (c f p : V → ℕ) (v : V) : ℕ := (c v-f v-p v+1)/2

structure Selection (c f p : V → ℕ) (H : Finset V) (a b F : ℕ) where
  extra : V → ℕ
  deficit : V → ℕ
  capacity : ∀ v, extra v ≤ cap c f p v
  total : (∑ v, extra v) = (b-a-F)/2
  priority : (∑ v ∈ H, extra v) = min ((b-a-F)/2) (∑ v ∈ H, cap c f p v)
  copies_le : ∀ v, f v+extra v ≤ c v
  deficit_outside : ∀ v, v ∉ H → deficit v = 0
  deficit_sum : (∑ v, deficit v) ≤ F+H.card+1
  paired_lower : ∀ v ∈ H, c v ≤ 2*(f v+extra v)+p v+2*deficit v
  bundle_upper : ∀ v, 2*(f v+extra v) ≤ c v+F+1
  centre_lower : a+b-1 ≤ 2*(a+F+(b-a-F)/2)
  centre_upper : 2*(a+F+(b-a-F)/2) ≤ a+b+F

theorem exists_selection (c f p : V → ℕ) (H : Finset V) (a b F : ℕ)
    (hf : ∀ v, f v ≤ c v) (hC : (∑ v, c v) = b) (hF : (∑ v, f v) = F)
    (hP : (∑ v, p v) ≤ a) (hab : a ≤ b) (hFI : F ≤ b-a)
    (hPaired : ∀ v ∈ H, p v ≤ c v)
    (hDifference : (∑ v ∈ H, (c v-p v)) ≤ b-a) :
    Nonempty (Selection c f p H a b F) := by
  let t := (b-a-F)/2
  have hCap : ∀ v, cap c f p v ≤ c v-f v := by intro v;dsimp only [cap];omega
  have hPoint : ∀ v, c v ≤ 2*cap c f p v+f v+p v := by intro v;dsimp only [cap];omega
  have hSum := sum_le_sum (s := univ) (fun v _ => hPoint v)
  rw [sum_add_distrib,sum_add_distrib,←mul_sum,hC,hF] at hSum
  have hEnough : t ≤ ∑ v, cap c f p v := by dsimp only [t];omega
  obtain ⟨g,hg,hTotal,hPriority⟩ := PriorityCopyAllocation.exists_allocation (cap c f p) H t hEnough
  have hCapPoint : ∀ v ∈ H, 2*cap c f p v ≤ c v-p v+1 := by
    intro v hv
    have hp := hPaired v hv
    dsimp only [cap]
    omega
  have hCapSum := sum_le_sum hCapPoint
  rw [←mul_sum,sum_add_distrib] at hCapSum
  simp only [sum_const,smul_eq_mul,mul_one] at hCapSum
  have hCapBound : 2*(∑ v ∈ H, cap c f p v) ≤ b-a+H.card := by omega
  let loss : V → ℕ := fun v => if v ∈ H then cap c f p v-g v else 0
  have hLossSum : (∑ v, loss v)+(∑ v ∈ H, g v) = ∑ v ∈ H, cap c f p v := by
    have hLoss : (∑ v, loss v) = ∑ v ∈ H, (cap c f p v-g v) := by simp [loss]
    rw [hLoss,←sum_add_distrib]
    exact sum_congr rfl (fun v _ => Nat.sub_add_cancel (hg v))
  have hLossBudget : (∑ v, loss v) ≤ F+H.card+1 := by
    rw [hPriority] at hLossSum
    change (∑ v, loss v)+min ((b-a-F)/2) (∑ v ∈ H, cap c f p v) =
      ∑ v ∈ H, cap c f p v at hLossSum
    omega
  refine ⟨{
    extra := g
    deficit := loss
    capacity := hg
    total := hTotal
    priority := hPriority
    copies_le := ?_
    deficit_outside := ?_
    deficit_sum := hLossBudget
    paired_lower := ?_
    bundle_upper := ?_
    centre_lower := by omega
    centre_upper := by omega
  }⟩
  · intro v
    have hcv := hCap v
    have hgv := hg v
    have hfv := hf v
    omega
  · intro v hv;exact if_neg hv
  · intro v hv
    have hl : cap c f p v ≤ g v+loss v := by
      dsimp only [loss]
      rw [if_pos hv]
      omega
    have hp := hPoint v
    omega
  · intro v
    have hfv : f v ≤ F := by
      rw [←hF]
      exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ v)
    have hgv := hg v
    dsimp only [cap] at hgv
    have hvc := hf v
    omega

end OverfullWork.BalancedMiddleAllocation
