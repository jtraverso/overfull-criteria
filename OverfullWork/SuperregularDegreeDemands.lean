module

public import OverfullWork.DirectedDemandHall

@[expose] public section


/-! The capacity argument for Osthus–Staden Lemma 4.2. The two vertex
classes of equal size are indexed by separate copies of the same type. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

private theorem rectangle_budget {b n L U x y : ℝ}
    (hb : 0 ≤ b) (hx : 0 ≤ x) (hxy : x ≤ y) (hyn : y ≤ n)
    (hL : 2*b*n ≤ 3*L) (hU : U ≤ b*n) (hSlack : b*n-L ≤ 2*(b*n-U)) :
    U*x-L*(n-y) ≤ b*x*y := by
  have hgap := mul_nonneg (sub_nonneg.mpr hU) hx
  have hyn' : 0 ≤ n-y := sub_nonneg.mpr hyn
  by_cases hs : 3*x ≤ 2*n
  · have hbL : b*x ≤ L := by
      have h := mul_le_mul_of_nonneg_left hs hb
      nlinarith only [h,hL]
    nlinarith only [hgap,mul_nonneg (sub_nonneg.mpr hbL) hyn']
  · by_cases hCoeff : b*x ≤ L
    · nlinarith only [hgap,mul_nonneg (sub_nonneg.mpr hCoeff) hyn']
    · have h1 : b*x-L ≤ 2*(b*n-U) := by
        have h := mul_le_mul_of_nonneg_left (hxy.trans hyn) hb
        linarith only [h,hSlack]
      have h2 : n-y ≤ x/2 := by linarith only [hs,hxy]
      have h := mul_le_mul h1 h2 hyn' (by linarith only [hU])
      nlinarith only [h]

private theorem incidence_at_least_out (D : Digraph V) (S T : Finset V)
    (U : ℕ) (hOut : ∀ v, U+T.card ≤ outDegree D v) : U*S.card ≤ incidences D S Tᶜ := by
  have hRow (v : V) : U ≤ (Tᶜ.filter (D.Adj v)).card := by
    have h := sum_add_sum_compl (f := fun w => if D.Adj v w then (1:ℕ) else 0) T
    have hBound := card_le_card (filter_subset (fun w => D.Adj v w) T)
    have hMin := hOut v
    simp only [card_filter] at hBound
    simp only [outDegree,card_filter] at hMin
    simp only [card_filter]
    omega
  simp only [incidences,inNeighbours,card_filter]
  rw [sum_comm]
  simp only [←card_filter]
  calc
    _ = ∑ _v ∈ S,U := by simp [Nat.mul_comm]
    _ ≤ _ := sum_le_sum fun v _ => hRow v

/-- Realize balanced demands in a bipartite pair given lower bounds on its
two minimum degrees and on every sufficiently large rectangle. -/
theorem exists_demands_of_dense_pair (D : Digraph V) (e L U : ℕ) (b : ℝ)
    (p q : V → ℕ) (hb : 0 ≤ b) (hTwo : U ≤ 2*L)
    (hL : 2*b*(Fintype.card V:ℝ) ≤ 3*(L:ℝ))
    (hU : (U:ℝ) ≤ b*(Fintype.card V:ℝ))
    (hSlack : b*(Fintype.card V:ℝ)-(L:ℝ) ≤ 2*(b*(Fintype.card V:ℝ)-(U:ℝ)))
    (hOut : ∀ v, U+2*e ≤ outDegree D v) (hIn : ∀ v, U+2*e ≤ inDegree D v)
    (hRect : ∀ S Y : Finset V, e ≤ S.card → e ≤ Y.card →
      b*(S.card:ℝ)*(Y.card:ℝ) ≤ (incidences D S Y:ℝ))
    (hp : ∀ v, L ≤ p v ∧ p v ≤ U) (hq : ∀ v, L ≤ q v ∧ q v ≤ U)
    (hBalance : (∑ v,p v) = ∑ v,q v) :
    ∃ H : Digraph V, H ≤ D ∧ (∀ v, outDegree H v = p v) ∧ ∀ v, inDegree H v = q v := by
  apply DirectedDemandHall.exists_subdigraph_of_capacity_cuts D p q hBalance
  intro S T
  let Y := Tᶜ
  have hP (A : Finset V) : L*A.card ≤ ∑ v ∈ A,p v ∧ (∑ v ∈ A,p v) ≤ U*A.card := by
    constructor
    · simpa [Nat.mul_comm] using (sum_le_sum (s := A) fun v _ => (hp v).1)
    · simpa [Nat.mul_comm] using (sum_le_sum (s := A) fun v _ => (hp v).2)
  have hQ (A : Finset V) : L*A.card ≤ ∑ v ∈ A,q v ∧ (∑ v ∈ A,q v) ≤ U*A.card := by
    constructor
    · simpa [Nat.mul_comm] using (sum_le_sum (s := A) fun v _ => (hq v).1)
    · simpa [Nat.mul_comm] using (sum_le_sum (s := A) fun v _ => (hq v).2)
  have hDiff : (∑ v ∈ S,p v) + (∑ v ∈ Sᶜ,p v) =
      (∑ v ∈ T,q v) + (∑ v ∈ Y,q v) := by
    rw [sum_add_sum_compl,hBalance]
    exact (sum_add_sum_compl T q).symm
  by_cases hDone : (∑ v ∈ S,p v) ≤ ∑ v ∈ T,q v
  · omega
  by_cases hs : S.card < e
  · have hLt : L*T.card < U*S.card := by
      have h1 := (hQ T).1
      have h2 := (hP S).2
      omega
    have hT : T.card ≤ 2*e := by
      by_contra! h
      have h1 := Nat.mul_le_mul_left L (show 2*S.card ≤ T.card by omega)
      have h2 := Nat.mul_le_mul_right S.card hTwo
      nlinarith only [h1,h2,hLt]
    exact (hP S).2.trans ((incidence_at_least_out D S T U
      (fun v => (Nat.add_le_add_left hT U).trans (hOut v))).trans (Nat.le_add_left _ _))
  by_cases hy : Y.card < e
  · have hLt : L*Sᶜ.card < U*Y.card := by
      have h1 := (hP Sᶜ).1
      have h2 := (hQ Y).2
      omega
    have hSc : Sᶜ.card ≤ 2*e := by
      by_contra! h
      have h1 := Nat.mul_le_mul_left L (show 2*Y.card ≤ Sᶜ.card by omega)
      have h2 := Nat.mul_le_mul_right Y.card hTwo
      nlinarith only [h1,h2,hLt]
    have hBound : U*Y.card ≤ incidences D S Y := by
      unfold incidences
      calc
        _ = ∑ _v ∈ Y,U := by simp [Nat.mul_comm]
        _ ≤ _ := by
          apply sum_le_sum
          intro v _
          have h := sum_add_sum_compl (f := fun w => if D.Adj w v then (1:ℕ) else 0) S
          simp only [←card_filter] at h
          have hCap := card_le_card (filter_subset (fun w => D.Adj w v) Sᶜ)
          have hMin := hIn v
          change U+2*e ≤ (univ.filter (fun w => D.Adj w v)).card at hMin
          change U ≤ (S.filter (fun w => D.Adj w v)).card
          omega
    have hQY := (hQ Y).2
    change (∑ v ∈ S,p v) ≤ (∑ v ∈ T,q v)+incidences D S Y
    omega
  have hR := hRect S Y (by omega) (by omega)
  have hnS : (S.card:ℝ) ≤ (Fintype.card V:ℝ) := by exact_mod_cast card_le_univ S
  have hnY : (Y.card:ℝ) ≤ (Fintype.card V:ℝ) := by exact_mod_cast card_le_univ Y
  have hT : (Fintype.card V:ℝ)-(Y.card:ℝ) = (T.card:ℝ) := by
    have he : T.card+Y.card = Fintype.card V := by
      dsimp only [Y]
      rw [card_compl,add_comm,Nat.sub_add_cancel (card_le_univ T)]
    exact sub_eq_of_eq_add (by exact_mod_cast he.symm)
  have hSc : (Fintype.card V:ℝ)-(S.card:ℝ) = (Sᶜ.card:ℝ) := by
    have he : Sᶜ.card+S.card = Fintype.card V := by
      rw [card_compl,Nat.sub_add_cancel (card_le_univ S)]
    exact sub_eq_of_eq_add (by exact_mod_cast he.symm)
  by_cases hSy : S.card ≤ Y.card
  · have h := rectangle_budget hb (Nat.cast_nonneg _) (by exact_mod_cast hSy) hnY hL hU hSlack
    rw [hT] at h
    have hc : U*S.card ≤ L*T.card+incidences D S Y := by
      exact_mod_cast (show (U:ℝ)*(S.card:ℝ) ≤ (L:ℝ)*(T.card:ℝ)+(incidences D S Y:ℝ) by linarith)
    have hpS := (hP S).2
    have hqT := (hQ T).1
    change (∑ v ∈ S,p v) ≤ (∑ v ∈ T,q v)+incidences D S Y
    omega
  · have h := rectangle_budget hb (Nat.cast_nonneg _) (by exact_mod_cast (le_of_not_ge hSy)) hnS hL hU hSlack
    rw [hSc] at h
    have hc : U*Y.card ≤ L*Sᶜ.card+incidences D S Y := by
      exact_mod_cast (show (U:ℝ)*(Y.card:ℝ) ≤ (L:ℝ)*(Sᶜ.card:ℝ)+(incidences D S Y:ℝ) by nlinarith)
    have hqY := (hQ Y).2
    have hpSc := (hP Sᶜ).1
    change (∑ v ∈ S,p v) ≤ (∑ v ∈ T,q v)+incidences D S Y
    omega

end OverfullWork.DirectedRobustExpansion
