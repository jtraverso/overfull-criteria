module

public import OverfullWork.ThinReserveDegrees

@[expose] public section


/-! Count the bad vertex–copy incidences before trimming the primary
clusters in Osthus–Staden §5.1. Both tails of the degree estimate matter. -/
namespace OverfullWork.DirectedRegularPairs

open Finset DirectedRobustExpansion
open scoped Classical
variable {W : Type*} [Fintype W]

theorem few_high_pair_semidegrees (D : Digraph W) (d ε : ℝ)
    (hD : IsCentredRegular D ε d) (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 0 < Fintype.card W) :
    (((univ : Finset W).filter (fun v => (d+2*ε)*(Fintype.card W:ℝ) < (outDegree D v:ℝ))).card:ℝ)
      < ε*(Fintype.card W:ℝ) ∧
    (((univ : Finset W).filter (fun v => (d+2*ε)*(Fintype.card W:ℝ) < (inDegree D v:ℝ))).card:ℝ)
      < ε*(Fintype.card W:ℝ) := by
  let n := (Fintype.card W:ℝ)
  have hnR : 0 < n := by dsimp only [n]; exact_mod_cast hn
  have hLarge : n*ε ≤ n := mul_le_of_le_one_right hnR.le hε1
  have hUpper (A B : Finset W) (hA : n*ε ≤ A.card) (hB : n*ε ≤ B.card) :
      (incidences D A B : ℝ) < (d+2*ε)*(A.card : ℝ)*(B.card : ℝ) := by
    have h := (abs_lt.mp (hD.1 A (subset_univ _) B (subset_univ _)
      (by simpa only [card_univ] using hA) (by simpa only [card_univ] using hB))).2
    have hd := (abs_le.mp hD.2).2
    have hPosA : (0 : ℝ) < A.card := (mul_pos hnR hε).trans_le hA
    have hPosB : (0 : ℝ) < B.card := (mul_pos hnR hε).trans_le hB
    have hdensity : density D A B < d+2*ε := by linarith only [h,hd]
    have hPay := (div_lt_iff₀ (mul_pos hPosA hPosB)).mp hdensity
    exact hPay.trans_eq (mul_assoc _ _ _).symm
  constructor
  · let A := (univ : Finset W).filter (fun v => (d+2*ε)*n < (outDegree D v:ℝ))
    change (A.card : ℝ) < ε*n
    by_contra! hA
    have hSum : (A.card : ℝ)*((d+2*ε)*n) ≤ ∑ v ∈ A,(outDegree D v:ℝ) := by
      simpa [mul_comm] using (sum_le_sum (s := A) fun v hv => (mem_filter.mp hv).2.le)
    have hInc : (incidences D A univ : ℝ) = ∑ v ∈ A,(outDegree D v:ℝ) := by
      rw [incidences_eq_sum,sum_comm]
      simp only [outDegree,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    have h := hUpper A univ (by linarith only [hA]) (by simpa using hLarge)
    rw [hInc,card_univ] at h
    change (∑ v ∈ A,(outDegree D v:ℝ)) < (d+2*ε)*(A.card:ℝ)*n at h
    nlinarith only [hSum,h]
  · let B := (univ : Finset W).filter (fun v => (d+2*ε)*n < (inDegree D v:ℝ))
    change (B.card : ℝ) < ε*n
    by_contra! hB
    have hSum : (B.card : ℝ)*((d+2*ε)*n) ≤ ∑ v ∈ B,(inDegree D v:ℝ) := by
      simpa [mul_comm] using (sum_le_sum (s := B) fun v hv => (mem_filter.mp hv).2.le)
    have h := hUpper univ B (by simpa using hLarge) (by linarith only [hB])
    simp only [incidences,Nat.cast_sum,card_univ] at h
    change (∑ v ∈ B,(inDegree D v:ℝ)) < (d+2*ε)*n*(B.card:ℝ) at h
    nlinarith only [hSum,h]

noncomputable def pairSemidegree (outgoing : Bool) (D : Digraph W) (x : W) : ℕ :=
  if outgoing then outDegree D x else inDegree D x

/-- On each side of a regular copy, at most twice the regularity
fraction violates the two-sided degree estimate. -/
theorem bad_copy_degree_count (D : Digraph W) (outgoing : Bool) (ε d : ℝ)
    (hD : IsCentredRegular D ε d) (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 0 < Fintype.card W) :
    (((univ : Finset W).filter (fun v =>
      2*ε*(Fintype.card W:ℝ) < |(pairSemidegree outgoing D v:ℝ)-d*(Fintype.card W:ℝ)|)).card:ℝ)
      ≤ 2*ε*(Fintype.card W:ℝ) := by
  let n := (Fintype.card W:ℝ)
  let low := (univ : Finset W).filter (fun v => (pairSemidegree outgoing D v:ℝ) < (d-2*ε)*n)
  let high := (univ : Finset W).filter (fun v => (d+2*ε)*n < (pairSemidegree outgoing D v:ℝ))
  have hl : (low.card:ℝ) ≤ ε*n := by
    cases outgoing
    · exact (few_low_pair_semidegrees D d ε hD hε hε1 hn).2.le
    · exact (few_low_pair_semidegrees D d ε hD hε hε1 hn).1.le
  have hh : (high.card:ℝ) ≤ ε*n := by
    cases outgoing
    · exact (few_high_pair_semidegrees D d ε hD hε hε1 hn).2.le
    · exact (few_high_pair_semidegrees D d ε hD hε hε1 hn).1.le
  have he : ((univ : Finset W).filter (fun v =>
      2*ε*n < |(pairSemidegree outgoing D v:ℝ)-d*n|)) = low ∪ high := by
    ext x
    simp only [mem_filter,mem_univ,true_and,mem_union,low,high,lt_abs]
    constructor <;> intro h
    · rcases h with h | h
      · right; linarith only [h]
      · left; linarith only [h]
    · rcases h with h | h
      · right; linarith only [h]
      · left; linarith only [h]
  change (((univ : Finset W).filter _).card:ℝ) ≤ 2*ε*n
  rw [he]
  have hu : ((low ∪ high).card:ℝ) ≤ (low.card:ℝ)+high.card := by exact_mod_cast card_union_le low high
  linarith only [hl,hh,hu]

/-- Double-count a thresholded exceptional set for a family of copies.
The bound is explicit even for an empty family. -/
theorem bad_incidence_count {I : Type*} (J : Finset I) (bad : I → W → Prop) (B L : ℝ)
    (hB : ∀ i ∈ J, (((univ : Finset W).filter (bad i)).card : ℝ) ≤ B) :
    L*(((univ : Finset W).filter (fun v => L < ((J.filter (fun i => bad i v)).card : ℝ))).card : ℝ)
      ≤ (J.card : ℝ)*B := by
  let K := (univ : Finset W).filter (fun v => L < ((J.filter (fun i => bad i v)).card : ℝ))
  have hl : L*(K.card : ℝ) ≤ ∑ v ∈ K,((J.filter (fun i => bad i v)).card : ℝ) := by
    simpa [mul_comm] using sum_le_sum (s := K) (fun v hv => (mem_filter.mp hv).2.le)
  have hn : ∑ v ∈ K,((J.filter (fun i => bad i v)).card : ℝ) ≤
      ∑ v : W,((J.filter (fun i => bad i v)).card : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
  have hs : (∑ v : W,((J.filter (fun i => bad i v)).card : ℝ)) =
      ∑ i ∈ J,(((univ : Finset W).filter (bad i)).card : ℝ) := by
    simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [sum_comm]
  exact hl.trans (hn.trans (hs.trans_le (by simpa [mul_comm] using sum_le_sum hB)))

/-- Select equal-size retained clusters, with at most the prescribed
fraction of atypical copies at every retained vertex, in each direction.
Choosing the deletion count to make the retained size divisible requires
only increasing the deletion budget. -/
theorem exists_retained_good_copy_profiles {I U : Type*} [Fintype I]
    (endpoint : Bool → I → U) (D : I → Digraph W) (d ε ξ : ℝ) (t : ℕ)
    (hD : ∀ i, IsCentredRegular (D i) ε d)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hξ : 0 < ξ) (hn : 0 < Fintype.card W)
    (hBudget : 4*ε*(Fintype.card W : ℝ) ≤ ξ*(t : ℝ)) :
    ∃ keep : U → Finset W,
      (∀ u, (keep u).card = Fintype.card W-t) ∧
      ∀ s u v, v ∈ keep u →
        ((((univ : Finset I).filter (fun i => endpoint s i = u)).filter (fun i =>
          2*ε*(Fintype.card W:ℝ) < |(pairSemidegree s (D i) v:ℝ)-d*(Fintype.card W:ℝ)|)).card:ℝ)
          ≤ ξ*(((univ : Finset I).filter (fun i => endpoint s i = u)).card:ℝ) := by
  let J (s : Bool) (u : U) := (univ : Finset I).filter (fun i => endpoint s i = u)
  let atypical (s : Bool) (i : I) (v : W) :=
    2*ε*(Fintype.card W:ℝ) < |(pairSemidegree s (D i) v:ℝ)-d*(Fintype.card W:ℝ)|
  let bad (s : Bool) (u : U) := (univ : Finset W).filter (fun v =>
    ξ*((J s u).card:ℝ) < (((J s u).filter (fun i => atypical s i v)).card:ℝ))
  have hCard (s : Bool) (u : U) : ξ*((bad s u).card:ℝ) ≤ 2*ε*(Fintype.card W:ℝ) := by
    by_cases hJ : (J s u).card = 0
    · have he : J s u = ∅ := card_eq_zero.mp hJ
      simpa [bad,he] using (show 0 ≤ 2*ε*(Fintype.card W:ℝ) by positivity)
    · have hPos : (0 : ℝ) < (J s u).card := by exact_mod_cast Nat.pos_of_ne_zero hJ
      have h := bad_incidence_count (J s u) (atypical s)
        (2*ε*(Fintype.card W:ℝ)) (ξ*((J s u).card:ℝ))
        (fun i _ => bad_copy_degree_count (D i) s ε d (hD i) hε hε1 hn)
      change (ξ*((J s u).card:ℝ))*((bad s u).card:ℝ) ≤ _ at h
      apply (mul_le_mul_iff_right₀ hPos).mp
      simpa only [mul_right_comm ξ, mul_comm ((J s u).card:ℝ)] using h
  have hBad (u : U) : (bad false u ∪ bad true u).card ≤ t := by
    have hUn : (((bad false u ∪ bad true u).card) : ℝ) ≤
        ((bad false u).card : ℝ)+(bad true u).card := by exact_mod_cast card_union_le (bad false u) (bad true u)
    have hMul := mul_le_mul_of_nonneg_left hUn hξ.le
    have hf := hCard false u
    have ht := hCard true u
    have hb : ξ*((bad false u ∪ bad true u).card:ℝ) ≤ ξ*(t:ℝ) := by
      linarith only [hBudget,hf,ht,hMul,mul_add ξ ((bad false u).card:ℝ) ((bad true u).card:ℝ)]
    have hh : ((bad false u ∪ bad true u).card:ℝ) ≤ (t:ℝ) := (mul_le_mul_iff_of_pos_left hξ).mp hb
    exact_mod_cast hh
  have hChoose (u : U) : ∃ K ⊆ (bad false u ∪ bad true u)ᶜ,
      K.card = Fintype.card W-t := by
    apply exists_subset_card_eq
    rw [card_compl]
    exact Nat.sub_le_sub_left (hBad u) _
  choose keep hKeep hSize using hChoose
  refine ⟨keep,hSize,?_⟩
  intro s u v hv
  have hmem : v ∉ bad false u ∪ bad true u := mem_compl.mp (hKeep u hv)
  have hNot : v ∉ bad s u := by
    cases s
    · exact fun h => hmem (mem_union_left _ h)
    · exact fun h => hmem (mem_union_right _ h)
  change (((J s u).filter (fun i => atypical s i v)).card:ℝ) ≤ ξ*((J s u).card:ℝ)
  exact not_lt.mp (fun h => hNot (mem_filter.mpr ⟨mem_univ _,h⟩))

end OverfullWork.DirectedRegularPairs
