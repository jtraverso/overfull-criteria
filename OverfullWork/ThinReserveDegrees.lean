module

public import OverfullWork.ThinReserveAssembly

@[expose] public section


/-! Add the thin contributions of the parallel pairs in §5.2.
The total number of atypical vertices is bounded by the sum of the local
exceptional populations. -/
namespace OverfullWork.DirectedRegularPairs
open Finset DirectedRobustExpansion
open scoped Classical
variable {V I : Type*} [Fintype V]

private theorem out_cut_sum (D : Digraph V) (A : Finset V) :
    (incidences D A univ:ℝ) = ∑ v ∈ A,(outDegree D v:ℝ) := by
  rw [incidences_eq_sum,sum_comm]
  simp only [outDegree,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem few_low_pair_semidegrees (D : Digraph V) (d ε : ℝ)
    (hD : IsCentredRegular D ε d) (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 0 < Fintype.card V) :
    (((univ : Finset V).filter (fun v => (outDegree D v:ℝ) < (d-2*ε)*(Fintype.card V:ℝ))).card:ℝ)
      < ε*(Fintype.card V:ℝ) ∧
    (((univ : Finset V).filter (fun v => (inDegree D v:ℝ) < (d-2*ε)*(Fintype.card V:ℝ))).card:ℝ)
      < ε*(Fintype.card V:ℝ) := by
  let n := (Fintype.card V:ℝ)
  have hnR : 0 < n := by dsimp only [n]; exact_mod_cast hn
  have hLarge : ((univ : Finset V).card:ℝ)*ε ≤ ((univ : Finset V).card:ℝ) :=
    mul_le_of_le_one_right (Nat.cast_nonneg _) hε1
  have hDensity : d-ε ≤ density D univ univ := by
    have h := (abs_le.mp hD.2).1
    linarith only [h]
  have hOut (B : Finset V) (hB : n*ε ≤ (B.card:ℝ))
      (hV : ∀ v ∈ B, (outDegree D v:ℝ) < (d-2*ε)*n) : False := by
    have hBpos : B.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos hnR hε).trans_le hB)
    have h := uniform_incidences_lower D hD.1 hDensity (subset_univ B) (subset_refl univ)
      (by simpa only [card_univ] using hB) hLarge hBpos (card_pos.mp (by rwa [card_univ]))
    simp only [out_cut_sum,card_univ] at h
    have hUpper := sum_le_sum (s := B) fun x hx => (hV x hx).le
    simp only [sum_const,nsmul_eq_mul] at hUpper
    nlinarith only [h,hUpper]
  have hIn (B : Finset V) (hB : n*ε ≤ (B.card:ℝ))
      (hV : ∀ v ∈ B, (inDegree D v:ℝ) < (d-2*ε)*n) : False := by
    have hBpos : B.Nonempty := card_pos.mp (by exact_mod_cast (mul_pos hnR hε).trans_le hB)
    have h := uniform_incidences_lower D hD.1 hDensity (subset_refl univ) (subset_univ B)
      hLarge (by simpa only [card_univ] using hB) (card_pos.mp (by rwa [card_univ])) hBpos
    simp only [incidences,Nat.cast_sum,card_univ] at h
    change (d-ε-ε)*n*(B.card:ℝ) < ∑ x ∈ B,(inDegree D x:ℝ) at h
    have hUpper := sum_le_sum (s := B) fun x hx => (hV x hx).le
    simp only [sum_const,nsmul_eq_mul] at hUpper
    nlinarith only [h,hUpper]
  constructor
  · by_contra! h
    exact hOut _ (by simpa only [mul_comm] using h) (fun _ hv => (mem_filter.mp hv).2)
  · by_contra! h
    exact hIn _ (by simpa only [mul_comm] using h) (fun _ hv => (mem_filter.mp hv).2)

def indexedArcUnion (J : Finset I) (D : I → Digraph V) : Digraph V :=
  ⟨fun x y => ∃ i ∈ J, (D i).Adj x y⟩

private theorem card_filter_arc_union (J : Finset I) (P : I → V → Prop)
    (A : Finset V) (hA : ∀ v, v ∈ A ↔ ∃ i ∈ J, P i v)
    (hDis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∀ v, ¬(P i v ∧ P j v)) :
    A.card = ∑ i ∈ J,((univ : Finset V).filter (P i)).card := by
  let B := fun i => (univ : Finset V).filter (P i)
  have hB : A = J.biUnion B := by
    ext v
    simp [hA,B]
  rw [hB]
  exact card_biUnion (fun i hi j hj hne => disjoint_left.mpr (fun v hv hw =>
    hDis i hi j hj hne v ⟨(mem_filter.mp hv).2,(mem_filter.mp hw).2⟩))

theorem indexedArcUnion_semidegrees (J : Finset I) (D : I → Digraph V)
    (hDis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (D i) (D j)) (v : V) :
    outDegree (indexedArcUnion J D) v = ∑ i ∈ J,outDegree (D i) v ∧
    inDegree (indexedArcUnion J D) v = ∑ i ∈ J,inDegree (D i) v := by
  constructor
  · let Q := fun w => (indexedArcUnion J D).Adj v w
    let A := @Finset.filter V Q (Classical.decPred _) univ
    have hA (w : V) : w ∈ A ↔ ∃ i ∈ J, (D i).Adj v w := by
      letI : DecidablePred Q := Classical.decPred _
      change w ∈ univ.filter Q ↔ _
      simp only [mem_filter,mem_univ,true_and]
      rfl
    exact card_filter_arc_union J (fun i w => (D i).Adj v w) A hA
      (fun i hi j hj hne w h => (disjoint_iff_inf_le.mp (hDis i hi j hj hne)) h)
  · let Q := fun w => (indexedArcUnion J D).Adj w v
    let A := @Finset.filter V Q (Classical.decPred _) univ
    have hA (w : V) : w ∈ A ↔ ∃ i ∈ J, (D i).Adj w v := by
      letI : DecidablePred Q := Classical.decPred _
      change w ∈ univ.filter Q ↔ _
      simp only [mem_filter,mem_univ,true_and]
      rfl
    exact card_filter_arc_union J (fun i w => (D i).Adj w v) A hA
      (fun i hi j hj hne w h => (disjoint_iff_inf_le.mp (hDis i hi j hj hne)) h)

/-- The parallel pairs lose at most one exceptional fraction per copy.
On the common good set their degree contributions add exactly. -/
theorem typical_degrees_in_parallel_reserves (J : Finset I) (D : I → Digraph V) (d ε : ℝ)
    (hD : ∀ i ∈ J, IsCentredRegular (D i) ε d)
    (hDis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (D i) (D j))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hn : 0 < Fintype.card V) :
    ∃ badOut badIn : Finset V,
      (badOut.card:ℝ) ≤ (J.card:ℝ)*ε*(Fintype.card V:ℝ) ∧
      (badIn.card:ℝ) ≤ (J.card:ℝ)*ε*(Fintype.card V:ℝ) ∧
      (∀ v, v ∉ badOut → (J.card:ℝ)*(d-2*ε)*(Fintype.card V:ℝ) ≤
        (outDegree (indexedArcUnion J D) v:ℝ)) ∧
      (∀ v, v ∉ badIn → (J.card:ℝ)*(d-2*ε)*(Fintype.card V:ℝ) ≤
        (inDegree (indexedArcUnion J D) v:ℝ)) := by
  let n := (Fintype.card V:ℝ)
  let B := fun (f : Digraph V → V → ℕ) i =>
    (univ : Finset V).filter (fun v => (f (D i) v:ℝ) < (d-2*ε)*n)
  have hBound (f : Digraph V → V → ℕ)
      (hSize : ∀ i ∈ J, ((B f i).card:ℝ) ≤ ε*n) :
      ((J.biUnion (B f)).card:ℝ) ≤ (J.card:ℝ)*ε*n := by
    have hCard : ((J.biUnion (B f)).card:ℝ) ≤ ∑ i ∈ J,((B f i).card:ℝ) := by
      exact_mod_cast (card_biUnion_le : (J.biUnion (B f)).card ≤ ∑ i ∈ J,(B f i).card)
    apply hCard.trans
    calc
      _ ≤ ∑ _ ∈ J,ε*n := sum_le_sum hSize
      _ = _ := by simp [mul_assoc]
  have hGood (f : Digraph V → V → ℕ) (v : V) (hv : v ∉ J.biUnion (B f)) :
      (J.card:ℝ)*(d-2*ε)*n ≤ ∑ i ∈ J,(f (D i) v:ℝ) := by
    calc
      _ = ∑ _ ∈ J,(d-2*ε)*n := by simp [mul_assoc]
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        by_contra! h
        exact hv (mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨mem_univ _,h⟩⟩)
  refine ⟨J.biUnion (B outDegree),J.biUnion (B inDegree),
    hBound _ (fun i hi => (few_low_pair_semidegrees _ _ _ (hD i hi) hε hε1 hn).1.le),
    hBound _ (fun i hi => (few_low_pair_semidegrees _ _ _ (hD i hi) hε hε1 hn).2.le),?_,?_⟩
  · intro v hv
    rw [(indexedArcUnion_semidegrees J D hDis v).1,Nat.cast_sum]
    exact hGood _ v hv
  · intro v hv
    rw [(indexedArcUnion_semidegrees J D hDis v).2,Nat.cast_sum]
    exact hGood _ v hv

/-- The H0 bound for the parallel copies of a reduced edge. -/
theorem h0_degree_bounds (J : Finset I) (D : I → Digraph V) (d β γ ε ε' : ℝ)
    (hD : ∀ i ∈ J, IsCentredRegular (D i) ε (γ*β))
    (hDis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (D i) (D j))
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hε' : 0 ≤ ε') (hγ : 0 ≤ γ)
    (hErr : 4*ε ≤ γ*β) (hExc : ε ≤ ε'*β)
    (hCount : d ≤ (J.card:ℝ)*β ∧ (J.card:ℝ)*β ≤ 1) (hn : 0 < Fintype.card V) :
    ∃ badOut badIn : Finset V,
      (badOut.card:ℝ) ≤ ε'*(Fintype.card V:ℝ) ∧
      (badIn.card:ℝ) ≤ ε'*(Fintype.card V:ℝ) ∧
      (∀ v, v ∉ badOut → γ*d*(Fintype.card V:ℝ)/2 ≤ (outDegree (indexedArcUnion J D) v:ℝ)) ∧
      (∀ v, v ∉ badIn → γ*d*(Fintype.card V:ℝ)/2 ≤ (inDegree (indexedArcUnion J D) v:ℝ)) := by
  obtain ⟨A,B,hA,hB,hOut,hIn⟩ := typical_degrees_in_parallel_reserves J D (γ*β) ε hD hDis hε hε1 hn
  have hJ := Nat.cast_nonneg J.card (α := ℝ)
  have hN := Nat.cast_nonneg (Fintype.card V) (α := ℝ)
  have hBad : (J.card:ℝ)*ε*(Fintype.card V:ℝ) ≤ ε'*(Fintype.card V:ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hN
    nlinarith only [mul_le_mul_of_nonneg_left hExc hJ,mul_le_mul_of_nonneg_left hCount.2 hε']
  have hHalf : γ*d*(Fintype.card V:ℝ)/2 ≤ (J.card:ℝ)*(γ*β-2*ε)*(Fintype.card V:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right (show γ*d/2 ≤ γ*((J.card:ℝ)*β)/2 by
      nlinarith only [mul_le_mul_of_nonneg_left hCount.1 hγ]) hN
    have h2 := mul_le_mul_of_nonneg_right
      (show γ*β/2 ≤ γ*β-2*ε by linarith only [hErr]) (mul_nonneg hJ hN)
    nlinarith only [h1,h2]
  exact ⟨A,B,hA.trans hBad,hB.trans hBad,fun v hv => hHalf.trans (hOut v hv),
    fun v hv => hHalf.trans (hIn v hv)⟩

/-- The degree estimate used for the H1 reserves. The upper bound
allows exceptional summands with the full cell degree. -/
theorem thin_reserve_profile_sum (J good : Finset I) (f : I → ℕ) (β γ a m : ℝ)
    (hGood : good ⊆ J) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hm : 0 ≤ m)
    (hLower : 2*a ≤ 3*β*(good.card:ℝ))
    (hUpper : 6*β*(J.card:ℝ) ≤ 7*a)
    (hBad : 4*((J \ good).card:ℝ) ≤ γ*a)
    (hTypical : ∀ i ∈ good, γ*β*m/2 ≤ (f i:ℝ) ∧ (f i:ℝ) ≤ 3*γ*β*m/2)
    (hMax : ∀ i ∈ J, (f i:ℝ) ≤ m) :
    γ*a*m/3 ≤ ∑ i ∈ J,(f i:ℝ) ∧ (∑ i ∈ J,(f i:ℝ)) ≤ 2*γ*a*m := by
  have hSmall : γ*β*m/2*(good.card:ℝ) ≤ ∑ i ∈ good,(f i:ℝ) := by
    simpa only [sum_const,nsmul_eq_mul,mul_comm] using
      (sum_le_sum (s := good) fun i hi => (hTypical i hi).1)
  have hIncluded : (∑ i ∈ good,(f i:ℝ)) ≤ ∑ i ∈ J,(f i:ℝ) :=
    sum_le_sum_of_subset_of_nonneg hGood (fun i _ _ => Nat.cast_nonneg (f i))
  constructor
  · nlinarith only [hSmall,hIncluded,mul_le_mul_of_nonneg_left hLower (mul_nonneg hγ hm)]
  · have hDegree : (∑ i ∈ good,(f i:ℝ)) ≤ (good.card:ℝ)*(3*γ*β*m/2) := by
      simpa only [sum_const,nsmul_eq_mul] using
        (sum_le_sum (s := good) fun i hi => (hTypical i hi).2)
    have hError : (∑ i ∈ J \ good,(f i:ℝ)) ≤ ((J \ good).card:ℝ)*m := by
      simpa only [sum_const,nsmul_eq_mul] using
        (sum_le_sum (s := J \ good) fun i hi => hMax i (mem_sdiff.mp hi).1)
    have hSum := sum_sdiff hGood (f := fun i => (f i:ℝ))
    have hCard : (good.card:ℝ) ≤ (J.card:ℝ) := by exact_mod_cast card_le_card hGood
    have hUpperGood := (mul_le_mul_of_nonneg_left hCard hβ).trans (show β*(J.card:ℝ) ≤ 7*a/6 by
      nlinarith only [hUpper])
    nlinarith only [hDegree,hError,hSum,mul_le_mul_of_nonneg_right hUpperGood
      (show 0 ≤ 3*γ*m by positivity),mul_le_mul_of_nonneg_right hBad hm]

end OverfullWork.DirectedRegularPairs
