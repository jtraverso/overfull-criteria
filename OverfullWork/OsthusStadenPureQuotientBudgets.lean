module

public import OverfullWork.OsthusStadenDenseReducedSupport
public import OverfullWork.KuhnOsthusCodegreeCount
public import OverfullWork.SuperregularMergeReserve

@[expose] public section


/-! Degree budgets on the same pure partition used for the dense support in §5.1. -/
namespace OverfullWork.DirectedClusterQuotient

open Finset DirectedRobustExpansion DirectedRegularPairs DirectedPairEnergy
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]

private theorem partition_profile (f : V → Option I) (p : V → Prop) :
    (univ.filter p).card =
      ((exceptional f).filter p).card+((lift f univ).filter p).card := by
  rw [←exceptional_union_lift f,filter_union,
    card_union_of_disjoint ((exceptional_disjoint_lift f univ).mono
      (filter_subset _ _) (filter_subset _ _))]

/-- Summing the retained ordinary arcs over either side of a cell gives
the density budget in (6), before rounding. -/
theorem pure_quotient_arc_budgets (G H : Digraph V) (f : V → Option I) (m r : ℕ)
    (a loss ζ : ℝ) (hSub : H ≤ G)
    (hSize : ∀ i, (cluster f i).card = m)
    (hRegular : ∀ v, inDegree G v = r ∧ outDegree G v = r)
    (hr : (r:ℝ) = a*(Fintype.card V:ℝ)) (ha : 0 ≤ a) (haOne : a ≤ 1)
    (hloss : 0 ≤ loss) (hζ : 0 ≤ ζ) (hζHalf : ζ ≤ 1/2)
    (hException : ((exceptional f).card:ℝ) ≤ ζ*(Fintype.card V:ℝ))
    (hLoss : ∀ v, f v ≠ none →
      (inDegree (G \ H) v:ℝ) ≤ loss*(Fintype.card V:ℝ) ∧
      (outDegree (G \ H) v:ℝ) ≤ loss*(Fintype.card V:ℝ)) :
    let A := lift f univ
    let lo := (a-2*(loss+ζ))*(Fintype.card I:ℝ)
    let hi := (a+2*ζ)*(Fintype.card I:ℝ)
    (∀ i, lo*((m:ℝ)*(m:ℝ)) ≤ (incidences H (cluster f i) A:ℝ) ∧
      (incidences H (cluster f i) A:ℝ) ≤ hi*((m:ℝ)*(m:ℝ))) ∧
    ∀ i, lo*((m:ℝ)*(m:ℝ)) ≤ (incidences H A (cluster f i):ℝ) ∧
      (incidences H A (cluster f i):ℝ) ≤ hi*((m:ℝ)*(m:ℝ)) := by
  let n : ℝ := Fintype.card V
  let k : ℝ := Fintype.card I
  let e : ℝ := (exceptional f).card
  have hOrder : n = e+(m:ℝ)*k := by
    dsimp only [n,e,k]
    exact_mod_cast order_eq f m hSize
  have hE : e ≤ ζ*n := hException
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have he₀ : 0 ≤ e := Nat.cast_nonneg _
  have hOrd : n ≤ 2*((m:ℝ)*k) := by
    have h := mul_le_mul_of_nonneg_right hζHalf hn
    linarith only [hOrder,hE,h]
  have hBounds (t l b c : ℕ)
      (hSplit : t = b+c) (hTotal : l+t = r) (hB : (b:ℝ) ≤ e)
      (hL : (l:ℝ) ≤ loss*n) :
      (a-2*(loss+ζ))*((m:ℝ)*k) ≤ (c:ℝ) ∧ (c:ℝ) ≤ (a+2*ζ)*((m:ℝ)*k) := by
    have hSplitR : (t:ℝ) = (b:ℝ)+(c:ℝ) := by exact_mod_cast hSplit
    have hTotalR : (l:ℝ)+(t:ℝ) = a*n := by rw [←hr]; exact_mod_cast hTotal
    have hErr := mul_le_mul_of_nonneg_left hOrd (add_nonneg hloss hζ)
    have hSmall := mul_le_mul_of_nonneg_left hOrd hζ
    have hLow := mul_le_mul_of_nonneg_left (show (m:ℝ)*k ≤ n by linarith only [hOrder,he₀]) ha
    have hHigh := mul_le_of_le_one_left he₀ haOne
    have hExp : a*n = a*e+a*((m:ℝ)*k) := by rw [hOrder]; ring
    have hLo : a*((m:ℝ)*k)-(loss+ζ)*(2*((m:ℝ)*k)) ≤ (c:ℝ) := by
      linarith only [hSplitR,hTotalR,hB,hL,hE,hErr,hLow]
    have hHi : (c:ℝ) ≤ a*((m:ℝ)*k)+ζ*(2*((m:ℝ)*k)) := by
      linarith only [hSplitR,hTotalR,hHigh,hExp,hSmall,hE,
        Nat.cast_nonneg (α := ℝ) l,Nat.cast_nonneg (α := ℝ) b]
    constructor
    · convert hLo using 1 <;> ring
    · convert hHi using 1 <;> ring
  have hVertex (v : V) (hv : f v ≠ none) :
      ((a-2*(loss+ζ))*((m:ℝ)*k) ≤ (inNeighbours H (lift f univ) v:ℝ) ∧
        (inNeighbours H (lift f univ) v:ℝ) ≤ (a+2*ζ)*((m:ℝ)*k)) ∧
      ((a-2*(loss+ζ))*((m:ℝ)*k) ≤ (outTo H (lift f univ) v:ℝ) ∧
        (outTo H (lift f univ) v:ℝ) ≤ (a+2*ζ)*((m:ℝ)*k)) := by
    have hDegrees := residual_semidegrees G H hSub v
    constructor
    · apply hBounds (inDegree H v) (inDegree (G \ H) v) (inNeighbours H (exceptional f) v)
      · exact partition_profile f (fun w => H.Adj w v)
      · exact hDegrees.1.trans (hRegular v).1
      · dsimp only [inNeighbours,e]
        exact_mod_cast card_le_card (filter_subset (fun w => H.Adj w v) (exceptional f))
      · exact (hLoss v hv).1
    · apply hBounds (outDegree H v) (outDegree (G \ H) v) (outTo H (exceptional f) v)
      · exact partition_profile f (H.Adj v)
      · exact hDegrees.2.trans (hRegular v).2
      · dsimp only [outTo,e]
        exact_mod_cast card_le_card (filter_subset (H.Adj v) (exceptional f))
      · exact (hLoss v hv).2
  have hSum (i : I) (d : V → ℕ)
      (hd : ∀ v ∈ cluster f i,
        (a-2*(loss+ζ))*((m:ℝ)*k) ≤ (d v:ℝ) ∧ (d v:ℝ) ≤ (a+2*ζ)*((m:ℝ)*k)) :
      ((a-2*(loss+ζ))*k)*((m:ℝ)*(m:ℝ)) ≤ (↑(∑ v ∈ cluster f i,d v):ℝ) ∧
      (↑(∑ v ∈ cluster f i,d v):ℝ) ≤ ((a+2*ζ)*k)*((m:ℝ)*(m:ℝ)) := by
    have hl := sum_le_sum (fun v hv => (hd v hv).1)
    have hu := sum_le_sum (fun v hv => (hd v hv).2)
    simp only [sum_const,nsmul_eq_mul,hSize,←Nat.cast_sum] at hl hu
    constructor
    · rw [show ((a-2*(loss+ζ))*k)*((m:ℝ)*(m:ℝ)) =
        (m:ℝ)*((a-2*(loss+ζ))*((m:ℝ)*k)) by ring]
      exact hl
    · rw [show ((a+2*ζ)*k)*((m:ℝ)*(m:ℝ)) =
        (m:ℝ)*((a+2*ζ)*((m:ℝ)*k)) by ring]
      exact hu
  refine ⟨fun i => ?_,fun i => ?_⟩
  · rw [incidences_eq_sum_outTo]
    simpa only [Nat.cast_sum] using
      hSum i _ (fun v hv => (hVertex v (by rw [(mem_cluster f i v).mp hv]; simp)).2)
  · exact hSum i _ (fun v hv => (hVertex v (by rw [(mem_cluster f i v).mp hv]; simp)).1)

/-- Each weighted semidegree is at most the number of dense
neighbours plus the threshold times the number of cells. -/
theorem denseReduced_semidegrees_from_density_sums
    (H : Digraph V) (f : V → Option I) (d b : ℝ) (hd : 0 ≤ d)
    (hRow : ∀ i, b ≤ ∑ j, density H (cluster f i) (cluster f j))
    (hCol : ∀ j, b ≤ ∑ i, density H (cluster f i) (cluster f j)) :
    (∀ i, b-d*(Fintype.card I:ℝ) ≤ (outDegree (denseReduced H f d) i:ℝ)) ∧
    ∀ j, b-d*(Fintype.card I:ℝ) ≤ (inDegree (denseReduced H f d) j:ℝ) := by
  have hCount (x : I → ℝ) (hUpper : ∀ i, x i ≤ 1) (hLower : b ≤ ∑ i,x i) :
      b-d*(Fintype.card I:ℝ) ≤ ((univ.filter (fun i => d ≤ x i)).card:ℝ) := by
    have hTerm (i : I) : x i ≤ (if d ≤ x i then (1:ℝ) else 0)+d := by
      split_ifs with hi
      · linarith only [hUpper i,hd]
      · linarith only [lt_of_not_ge hi]
    have hSum := sum_le_sum (s := (univ : Finset I)) (fun i _ => hTerm i)
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ] at hSum
    rw [←sum_filter] at hSum
    simp only [sum_const,nsmul_eq_mul,mul_one] at hSum
    linarith only [hLower,hSum]
  exact ⟨fun i => hCount _ (fun j => density_le_one H _ _) (hRow i),
    fun j => hCount _ (fun i => density_le_one H _ _) (hCol j)⟩

end OverfullWork.DirectedClusterQuotient
