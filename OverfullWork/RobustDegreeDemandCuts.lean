module

public import OverfullWork.DirectedArcSelection

@[expose] public section


/-! Cut inequalities for robust directed degree demands, with the same capacity on each arc. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

omit [Fintype V] in
private theorem incidences_by_source (D : Digraph V) (S T : Finset V) :
    incidences D S T = ∑ x ∈ S,(T.filter (D.Adj x)).card := by
  simp only [incidences,inNeighbours,card_filter]
  rw [sum_comm]

private theorem count_complement (A : Finset V) (p : V → Prop) :
    (univ.filter p).card ≤ (Aᶜ.filter p).card + A.card := by
  let B := univ.filter p
  have he : B \ A = Aᶜ.filter p := by
    ext v
    simp only [B,mem_sdiff,mem_filter,mem_univ,true_and,mem_compl]
    tauto
  exact he ▸ card_le_card_sdiff_add_card (s := B) (t := A)

/-- Balanced demands sufficiently close to a small common degree
satisfy every directed cut constraint. -/
theorem scaled_degree_demand_cut_bound (D : Digraph V) (r t L U c : ℕ) (p q : V → ℕ)
    (hR : IsRobustAt D r t) (hLU : L ≤ U) (hTwo : U ≤ 2*L)
    (hGap : 2*(U-L)*Fintype.card V ≤ L*r)
    (hSquare : 2*U*Fintype.card V ≤ c*r*r)
    (hIn : ∀ v, c*t+U ≤ c*inDegree D v) (hOut : ∀ v, 2*c*t+U ≤ c*outDegree D v)
    (hp : ∀ v, L ≤ p v ∧ p v ≤ U) (hq : ∀ v, L ≤ q v ∧ q v ≤ U)
    (hBalance : (∑ v,p v) = ∑ v,q v) (S T : Finset V) :
    (∑ v ∈ S,p v) ≤ (∑ v ∈ T,q v)+c*incidences D S Tᶜ := by
  have hPS : (∑ v ∈ S,p v) ≤ U*S.card := by
    calc
      _ ≤ ∑ _v ∈ S,U := sum_le_sum fun v _ => (hp v).2
      _ = _ := by simp [Nat.mul_comm]
  have hQT : L*T.card ≤ ∑ v ∈ T,q v := by
    calc
      _ = ∑ _v ∈ T,L := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum fun v _ => (hq v).1
  by_cases hDone : (∑ v ∈ S,p v) ≤ ∑ v ∈ T,q v
  · exact hDone.trans (Nat.le_add_right _ _)
  have hStrict : L*T.card < U*S.card := hQT.trans_lt ((lt_of_not_ge hDone).trans_le hPS)
  by_cases hSmall : S.card < t
  · have hT : T.card ≤ 2*S.card := by
      by_contra hn
      have h := Nat.mul_le_mul_left L (show 2*S.card ≤ T.card by omega)
      have hh := Nat.mul_le_mul_right S.card hTwo
      nlinarith only [h,hh,hStrict]
    have hCount : U*S.card ≤ c*incidences D S Tᶜ := by
      rw [incidences_by_source,mul_sum]
      calc
        _ = ∑ _v ∈ S,U := by simp [Nat.mul_comm]
        _ ≤ _ := by
          apply sum_le_sum
          intro x _
          have h := count_complement T (D.Adj x)
          change outDegree D x ≤ _ at h
          have hx := hOut x
          have hMul := Nat.mul_le_mul_left c h
          have hCard : T.card ≤ 2*t := by omega
          have hPay := Nat.mul_le_mul_left c hCard
          nlinarith only [hMul,hPay,hx]
    omega
  by_cases hLarge : Fintype.card V < S.card+t
  · have hS : Sᶜ.card ≤ t := by rw [card_compl]; omega
    have hCount : (∑ v ∈ Tᶜ,q v) ≤ c*incidences D S Tᶜ := by
      rw [incidences,mul_sum]
      apply sum_le_sum
      intro v _
      have hh := count_complement Sᶜ (fun x => D.Adj x v)
      rw [compl_compl] at hh
      change inDegree D v ≤ inNeighbours D S v + Sᶜ.card at hh
      have hv := hIn v
      have hqv := (hq v).2
      have hMul := Nat.mul_le_mul_left c hh
      have hPay := Nat.mul_le_mul_left c hS
      nlinarith only [hMul,hPay,hv,hqv]
    have hP := sum_add_sum_compl (f := p) S
    have hQ := sum_add_sum_compl (f := q) T
    omega
  · have hCard := card_le_univ S
    have hGT : L*(2*T.card) ≤ L*(2*S.card+r) := by
      have h1 := Nat.mul_le_mul_left (2*(U-L)) hCard
      have h2 : U = L+(U-L) := (Nat.add_sub_of_le hLU).symm
      nlinarith only [h1,h2,hGap,hStrict]
    have hT : 2*T.card ≤ 2*S.card+r := by
      have hL : 0 < L := by
        by_contra! hn
        have h0 : L = 0 := by omega
        have hU0 : U = 0 := by omega
        simp [h0,hU0] at hStrict
      exact (mul_le_mul_iff_right₀ hL).mp (by simpa only [Nat.mul_comm L] using hGT)
    let W := neighbourhood D r S
    have hW : S.card+r ≤ W.card := hR S (by omega) (by omega)
    have hPaid := card_le_card_sdiff_add_card (s := W) (t := T)
    have hSize : r ≤ 2*(W \ T).card := by omega
    have hInc : r*(W \ T).card ≤ incidences D S Tᶜ := by
      calc
        _ = ∑ _v ∈ W \ T,r := by simp [Nat.mul_comm]
        _ ≤ ∑ v ∈ W \ T,inNeighbours D S v :=
          sum_le_sum fun v hv => (mem_filter.mp (mem_sdiff.mp hv).1).2
        _ ≤ _ := sum_le_sum_of_subset (fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2)
    have hTotal : U*Fintype.card V ≤ c*incidences D S Tᶜ := by
      have h := Nat.mul_le_mul_left (c*r) hSize
      have hi := Nat.mul_le_mul_left c hInc
      nlinarith only [h,hSquare,hi]
    have hUniv := Nat.mul_le_mul_left U hCard
    omega

/-- Unit-capacity specialization of the cut bound. -/
theorem degree_demand_cut_bound (D : Digraph V) (r t L U : ℕ) (p q : V → ℕ)
    (hR : IsRobustAt D r t) (hLU : L ≤ U) (hTwo : U ≤ 2*L)
    (hGap : 2*(U-L)*Fintype.card V ≤ L*r)
    (hSquare : 2*U*Fintype.card V ≤ r*r)
    (hIn : ∀ v, t+U ≤ inDegree D v) (hOut : ∀ v, 2*t+U ≤ outDegree D v)
    (hp : ∀ v, L ≤ p v ∧ p v ≤ U) (hq : ∀ v, L ≤ q v ∧ q v ≤ U)
    (hBalance : (∑ v,p v) = ∑ v,q v) (S T : Finset V) :
    (∑ v ∈ S,p v) ≤ (∑ v ∈ T,q v)+incidences D S Tᶜ := by
  simpa only [one_mul, mul_one] using
    scaled_degree_demand_cut_bound D r t L U 1 p q hR hLU hTwo hGap
      (by simpa only [one_mul]) (by simpa only [one_mul])
      (by simpa only [one_mul,mul_one]) hp hq hBalance S T

end OverfullWork.DirectedRobustExpansion
