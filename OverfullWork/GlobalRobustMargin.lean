module

public import OverfullWork.ProfiledCanonicalCandidate

@[expose] public section


/-! # Global robust expansion with an actual bounded exceptional set

This counts neighbours in the whole graph. It is not an inference from
bipartite robust expansion of a cut.
-/
namespace OverfullWork.GlobalRobustMargin
open SimpleGraph Finset PrunedCore RobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

theorem degree_sum_with_exceptions (G : SimpleGraph V) [DecidableRel G.Adj]
    (E S : Finset V) (δ a : ℕ) (hE : E.card≤a)
    (hGood : ∀v,v∉E → δ≤G.degree v) :
    δ*S.card≤(∑v:V,neighboursIn G S v)+δ*a := by
  have hSum:δ*(S\E).card≤∑v:V,neighboursIn G S v:=by
    rw [sum_neighboursIn_eq_sum_degrees]
    calc
      _ = ∑_v∈S\E,δ :=by simp [Nat.mul_comm]
      _ ≤ ∑v∈S\E,G.degree v :=by
        apply sum_le_sum
        intro v hv
        exact hGood v (mem_sdiff.mp hv).2
      _ ≤ _ :=sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _=>Nat.zero_le _)
  have hInter:(S∩E).card≤a:=(card_le_card inter_subset_right).trans hE
  have hSplit:=card_sdiff_add_card_inter S E
  have hMul:=Nat.mul_le_mul_left δ hInter
  nlinarith only [hSum,hSplit,hMul]

/-- A finite global analogue of the above-half incidence criterion.
The bounded exceptions are paid in both the count and the size margin. -/
theorem isRobustAt_of_margin (G : SimpleGraph V) [DecidableRel G.Adj]
    (E : Finset V) (n δ q r t a : ℕ)
    (hn : Fintype.card V=n) (hE : E.card≤a)
    (hGood : ∀v,v∉E → δ≤G.degree v)
    (hδ : δ≤n) (hMargin : n+2*q≤2*δ) (hr : 0<r)
    (hrq : r≤q) (hBudget : r+a≤t)
    (hScale : 4*r*n+2*n*a≤q*t) : IsRobustAt G r t := by
  intro S ht hSize
  have hScard:S.card≤n:=by rw [←hn];exact card_le_univ S
  by_cases hSmall:2*S.card≤n+q
  · by_contra hBad
    have hRN:(neighbourhood G r S).card<S.card+r:=by omega
    have hPos:0<S.card:=by omega
    have hLower:=degree_sum_with_exceptions G E S δ a hE hGood
    have hUpper:=sum_neighboursIn_le_threshold_split G r S
    rw [hn] at hUpper
    have hStrict:(neighbourhood G r S).card*S.card<(S.card+r)*S.card:=
      Nat.mul_lt_mul_of_pos_right hRN hPos
    have hRem:(n-(neighbourhood G r S).card)*(r-1)≤n*r:=
      Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
    have hRS:=Nat.mul_le_mul_left r hScard
    have hCount:(∑v:V,neighboursIn G S v)<S.card*S.card+2*r*n:=by
      nlinarith only [hUpper,hStrict,hRem,hRS]
    have hRoom:2*S.card+q≤2*δ:=by omega
    have hMul:=Nat.mul_le_mul_right S.card hRoom
    have hQT:=Nat.mul_le_mul_left q ht
    have hδa:=Nat.mul_le_mul_right a hδ
    nlinarith only [hLower,hCount,hMul,hQT,hδa,hScale]
  · have hRoom:n+r≤δ+S.card:=by omega
    have hSub:Eᶜ⊆neighbourhood G r S:=by
      intro v hv
      have hd:=hGood v (mem_compl.mp hv)
      have hN:=degree_add_card_le_neighboursIn_add_order G S v
      rw [hn] at hN
      exact mem_filter.mpr ⟨mem_univ _,by omega⟩
    have hRN:=card_le_card hSub
    rw [card_compl,hn] at hRN
    rw [hn] at hSize
    have hEle:E.card≤n:=by rw [←hn];exact card_le_univ E
    omega

end OverfullWork.GlobalRobustMargin
