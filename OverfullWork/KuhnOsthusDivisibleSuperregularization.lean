module

public import OverfullWork.KuhnOsthusSetupDivisibility
public import OverfullWork.KuhnOsthusBaseCycleBlowup
public import OverfullWork.DirectedPairEnergy
public import OverfullWork.MergeReservePacking

@[expose] public section


/-! Simultaneous superregularization and rounding in Kühn–Osthus
Lemma 4.4 and the opening of the proof of Theorem 1.2. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs DirectedClusterQuotient DirectedPairEnergy
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]

private theorem profileCount_filter (A : Finset V) (p : V → Prop) :
    profileCount A (univ.filter p) = ((A.filter p).card:ℝ) := by
  have he : A ∩ univ.filter p = A.filter p := by
    ext x
    simp only [mem_inter,mem_filter,mem_univ,true_and]
  rw [profileCount,he]

omit [Fintype V] in
private theorem typical_profile_after_trimming (A B Q : Finset V) (hBA : B ⊆ A)
    (d e η : ℝ) (hd : 0 ≤ d) (hd₁ : d ≤ 1)
    (hTypical : |profileCount A Q-d*(A.card:ℝ)| ≤ e*(A.card:ℝ))
    (hPay : e*(A.card:ℝ)+((A \ B).card:ℝ) ≤ η*(B.card:ℝ)) :
    |profileCount B Q-d*(B.card:ℝ)| ≤ η*(B.card:ℝ) := by
  have hLower := exceptional_overlap_loss Q A B
  rw [inter_eq_right.mpr hBA] at hLower
  have hUpper : profileCount B Q ≤ profileCount A Q := by
    unfold profileCount
    exact_mod_cast card_le_card (inter_subset_inter hBA Subset.rfl : B ∩ Q ⊆ A ∩ Q)
  have hSize : (A.card:ℝ) = (B.card:ℝ)+((A \ B).card:ℝ) := by
    exact_mod_cast (card_sdiff_add_card_eq_card hBA).symm.trans (Nat.add_comm _ _)
  have hId : d*(A.card:ℝ) = d*(B.card:ℝ)+d*((A \ B).card:ℝ) := by rw [hSize,mul_add]
  have hLo := mul_nonneg hd (Nat.cast_nonneg (A \ B).card : (0:ℝ) ≤ _)
  have hHi := mul_le_of_le_one_left (Nat.cast_nonneg (A \ B).card : (0:ℝ) ≤ _) hd₁
  obtain ⟨h₁,h₂⟩ := abs_le.mp hTypical
  exact abs_le.mpr ⟨by linarith only [hLower,hId,hLo,h₁,hPay],
    by linarith only [hUpper,hId,hHi,h₂,hPay]⟩

set_option maxHeartbeats 650000 in
/-- Delete all vertices failing a degree test on any selected pair,
then trim each cluster to the same multiple of `b`. Every selected
pair becomes superregular, and the reduced pairs retain regularity
on the same labels. -/
theorem kuhn_osthus_divisible_superregularization (G : Digraph V) (f : V → Option I)
    (R H : Digraph I) (m t b Δ : ℕ) (ε η d : ℝ)
    (hR : H ≤ R) (hSize : ∀ i, (cluster f i).card = m)
    (hb : 0 < b) (ht : t+b ≤ m)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hη₁ : η ≤ 1) (hTol : 2*ε ≤ η)
    (hDegree : ∀ i, inDegree H i+outDegree H i ≤ Δ)
    (hBad : (Δ:ℝ)*(2*ε*(m:ℝ)) ≤ t)
    (hReg : ∀ i j, R.Adj i j → IsUniform G ε (cluster f i) (cluster f j) ∧
      d+ε ≤ density G (cluster f i) (cluster f j)) :
    let a := ((m-t)/b)*b
    2*ε*(m:ℝ)+((m-a:ℕ):ℝ) ≤ η*(a:ℝ) →
    ∃ g : V → Option I, (∀ i, cluster g i ⊆ cluster f i ∧ (cluster g i).card = a) ∧
      (∀ i, b ∣ (cluster g i).card) ∧
      (exceptional g).card = (exceptional f).card+(m-a)*Fintype.card I ∧
      (exceptional g).card ≤ (exceptional f).card+(t+b-1)*Fintype.card I ∧
      (∀ i j, R.Adj i j → IsUniform G η (cluster g i) (cluster g j) ∧
        d ≤ density G (cluster g i) (cluster g j)) ∧
      ∀ i j, H.Adj i j → IsLowerSuperregularPair G η d (cluster g i) (cluster g j) := by
  intro a hPay
  let X := cluster f
  have hX (i : I) : (X i).card = m := hSize i
  let e (i : I) : Fin m ≃ X i :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hSize i)).symm
  let emb (i : I) : Fin m ↪ V := clusterEmbedding (e i)
  have hMap (i : I) : (univ : Finset (Fin m)).map (emb i) = X i := by
    ext v
    rw [mem_map]
    exact ⟨fun ⟨x,_,h⟩ => h ▸ (e i x).prop,
      fun hv => ⟨(e i).symm ⟨v,hv⟩,mem_univ _,congrArg Subtype.val ((e i).apply_symm_apply _)⟩⟩
  let D (i j : I) := pullDirectedPair (emb i) (emb j) G
  let c (i j : I) := density G (X i) (X j)
  have hCentre (i j : I) (hij : H.Adj i j) : IsCentredRegular (D i j) ε (c i j) := by
    refine ⟨?_,?_⟩
    · apply uniform_pullDirectedPair
      simpa only [hMap] using (hReg i j (hR hij)).1
    · dsimp only [D,c]
      rw [density_pullDirectedPair,hMap,hMap,sub_self,abs_zero]
      exact hε.le
  let atypical (out : Bool) (i j : I) :=
    (univ : Finset (Fin m)).filter (fun v =>
      2*ε*(m:ℝ) < |(pairSemidegree out (D i j) v:ℝ)-c i j*(m:ℝ)|)
  let outBad (i j : I) := (atypical true i j).map (emb i)
  let inBad (i j : I) := (atypical false i j).map (emb j)
  have hm : 0 < m := by omega
  have hOne (out : Bool) (i j : I) (hij : H.Adj i j) :
      ((atypical out i j).card:ℝ) ≤ 2*ε*(m:ℝ) := by
    simpa only [atypical,Fintype.card_fin] using bad_copy_degree_count (D i j) out ε (c i j)
      (hCentre i j hij) hε hε₁ (by simpa only [Fintype.card_fin] using hm)
  let outLabels (i : I) := (univ : Finset I).filter (H.Adj i)
  let inLabels (i : I) := (univ : Finset I).filter (fun j => H.Adj j i)
  let Bad (i : I) := (outLabels i).biUnion (outBad i) ∪ (inLabels i).biUnion (fun j => inBad j i)
  have hBadSize (i : I) : (Bad i).card ≤ t := by
    have hOut : (((outLabels i).biUnion (outBad i)).card:ℝ) ≤
        (outDegree H i:ℝ)*(2*ε*(m:ℝ)) := by
      calc
        _ ≤ ∑ j ∈ outLabels i,((outBad i j).card:ℝ) := by exact_mod_cast card_biUnion_le
        _ ≤ ∑ _j ∈ outLabels i,2*ε*(m:ℝ) := sum_le_sum (fun j hj => by
          simpa only [outBad,card_map] using hOne true i j (mem_filter.mp hj).2)
        _ = _ := by simp [outLabels,outDegree,nsmul_eq_mul]
    have hIn : (((inLabels i).biUnion (fun j => inBad j i)).card:ℝ) ≤
        (inDegree H i:ℝ)*(2*ε*(m:ℝ)) := by
      calc
        _ ≤ ∑ j ∈ inLabels i,((inBad j i).card:ℝ) := by exact_mod_cast card_biUnion_le
        _ ≤ ∑ _j ∈ inLabels i,2*ε*(m:ℝ) := sum_le_sum (fun j hj => by
          simpa only [inBad,card_map] using hOne false j i (mem_filter.mp hj).2)
        _ = _ := by simp [inLabels,inDegree,inNeighbours,nsmul_eq_mul]
    have hUnion : ((Bad i).card:ℝ) ≤
        (((outLabels i).biUnion (outBad i)).card:ℝ) +
          (((inLabels i).biUnion (fun j => inBad j i)).card:ℝ) := by
      exact_mod_cast card_union_le _ _
    have hTotal : (inDegree H i:ℝ)+(outDegree H i:ℝ) ≤ Δ := by exact_mod_cast hDegree i
    have hMul := mul_le_mul_of_nonneg_right hTotal
      (show 0 ≤ 2*ε*(m:ℝ) by positivity)
    exact_mod_cast (show ((Bad i).card:ℝ) ≤ t by linarith only [hUnion,hIn,hOut,hMul,hBad])
  obtain ⟨g,hG,hDiv,hVol,hVol'⟩ := exists_divisible_cluster_trimming f Bad m t b hb (by omega) hSize hBadSize
  let Y := cluster g
  have hSub (i : I) : Y i ⊆ X i := (hG i).1.trans sdiff_subset
  have hY (i : I) : (Y i).card = a := (hG i).2
  have hPay' : (m:ℝ)*ε ≤ (a:ℝ)*η := by
    linarith only [hPay,show 0 ≤ ε*(m:ℝ) by positivity,Nat.cast_nonneg (α := ℝ) (m-a)]
  have hPay'' : (m:ℝ)*ε ≤ a :=
    hPay'.trans (mul_le_of_le_one_right (Nat.cast_nonneg _) hη₁)
  have hDrop (i : I) : (X i \ Y i).card = m-a := by rw [card_sdiff_of_subset (hSub i),hSize i,hY i]
  have hUniform (i j : I) (hij : R.Adj i j) : IsUniform G η (Y i) (Y j) := by
    apply uniform_on_subcells G (hReg i j hij).1 (hSub i) (hSub j)
    · simpa only [hSize,hY] using hPay''
    · simpa only [hSize,hY] using hPay''
    · simpa only [hSize,hY] using hPay'
    · simpa only [hSize,hY] using hPay'
    · exact hTol
  have hDensity (i j : I) (hij : R.Adj i j) :
      |density G (Y i) (Y j)-c i j| < ε :=
    (hReg i j hij).1 (Y i) (hSub i) (Y j) (hSub j)
      (by simpa only [hSize,hY] using hPay'') (by simpa only [hSize,hY] using hPay'')
  refine ⟨g,fun i => ⟨hSub i,hY i⟩,hDiv,hVol,hVol',?_,?_⟩
  · intro i j hij
    exact ⟨hUniform i j hij,by linarith only [(abs_lt.mp (hDensity i j hij)).1,(hReg i j hij).2]⟩
  · intro i j hij
    refine ⟨c i j,by linarith only [(hReg i j (hR hij)).2,hε],density_le_one G _ _,
      hUniform i j (hR hij),(hDensity i j (hR hij)).le.trans (by linarith),?_,?_⟩
    · intro x hx
      let v := (e i).symm ⟨x,hSub i hx⟩
      have he : emb i v = x := congrArg Subtype.val ((e i).apply_symm_apply _)
      have hGood : v ∉ atypical true i j := by
        intro hv
        exact (mem_sdiff.mp ((hG i).1 hx)).2
          (mem_union_left _ (mem_biUnion.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,hij⟩,mem_map.mpr ⟨v,hv,he⟩⟩))
      have hOld : |profileCount (X j) (outProfile G x)-c i j*((X j).card:ℝ)| ≤ (2*ε)*((X j).card:ℝ) := by
        have hh := not_lt.mp (fun h => hGood (mem_filter.mpr ⟨mem_univ _,h⟩))
        rw [pullDirectedPair_semidegree,if_pos rfl,hMap,he] at hh
        rw [outProfile,profileCount_filter,hSize]
        exact hh
      exact typical_profile_after_trimming _ _ _ (hSub j) _ _ _
        (density_nonneg G _ _) (density_le_one G _ _) hOld
        (by simpa only [hX,hY,hDrop] using hPay)
    · intro x hx
      let v := (e j).symm ⟨x,hSub j hx⟩
      have he : emb j v = x := congrArg Subtype.val ((e j).apply_symm_apply _)
      have hGood : v ∉ atypical false i j := by
        intro hv
        exact (mem_sdiff.mp ((hG j).1 hx)).2
          (mem_union_right _ (mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hij⟩,mem_map.mpr ⟨v,hv,he⟩⟩))
      have hOld : |profileCount (X i) (inProfile G x)-c i j*((X i).card:ℝ)| ≤ (2*ε)*((X i).card:ℝ) := by
        have hh := not_lt.mp (fun h => hGood (mem_filter.mpr ⟨mem_univ _,h⟩))
        rw [pullDirectedPair_semidegree,if_neg Bool.false_ne_true,hMap,he] at hh
        rw [inProfile,profileCount_filter,hSize]
        exact hh
      exact typical_profile_after_trimming _ _ _ (hSub i) _ _ _
        (density_nonneg G _ _) (density_le_one G _ _) hOld
        (by simpa only [hX,hY,hDrop] using hPay)

/-- Choose the mandatory deletion count by rounding up the actual
degree-test budget. The remaining integer cluster size pays for all
local deviations. -/
theorem kuhn_osthus_integral_superregularity_budget
    (m b Δ : ℕ) (ε η : ℝ) (hb : 0 < b) (hε : 0 ≤ ε) (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hMargin : 2*(2*ε*(m:ℝ)+(Δ:ℝ)*(2*ε*(m:ℝ))+(b:ℝ)+1) ≤ η*(m:ℝ)) :
    let t := ⌈(Δ:ℝ)*(2*ε*(m:ℝ))⌉₊
    let a := ((m-t)/b)*b
    t+b ≤ m ∧ (Δ:ℝ)*(2*ε*(m:ℝ)) ≤ t ∧ 2*ε ≤ η ∧
      2*ε*(m:ℝ)+((m-a:ℕ):ℝ) ≤ η*(a:ℝ) := by
  intro t a
  let w := (Δ:ℝ)*(2*ε*(m:ℝ))
  have hw : 0 ≤ w := by unfold w; positivity
  have ht : (t:ℝ) < w+1 := Nat.ceil_lt_add_one hw
  have hUp : η*(m:ℝ) ≤ (m:ℝ) := mul_le_of_le_one_left (Nat.cast_nonneg _) hη₁
  have hεm : 0 ≤ 2*ε*(m:ℝ) := by positivity
  have hbR : 0 < (b:ℝ) := by exact_mod_cast hb
  have hHalf : (t:ℝ)+(b:ℝ) ≤ (m:ℝ)/2 := by
    change 2*(2*ε*(m:ℝ)+w+(b:ℝ)+1) ≤ η*(m:ℝ) at hMargin
    linarith only [hMargin,hUp,ht,hεm]
  have hm : (t+b:ℕ) ≤ m := by
    have hmR : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
    exact_mod_cast (show (t:ℝ)+(b:ℝ) ≤ (m:ℝ) by linarith only [hHalf,hmR])
  obtain ⟨_,hA,_,hLoss⟩ := round_down_cluster_size m t b hb (by omega)
  have hLoss' : ((m-a:ℕ):ℝ) < (t:ℝ)+(b:ℝ) := by exact_mod_cast hLoss
  have ha : a ≤ m := hA.trans (Nat.sub_le _ _)
  have hAR : (m:ℝ)/2 ≤ (a:ℝ) := by
    rw [Nat.cast_sub ha] at hLoss'
    linarith only [hLoss',hHalf]
  have hScale := mul_le_mul_of_nonneg_left hAR hη
  have hPay : 2*ε*(m:ℝ)+((m-a:ℕ):ℝ) ≤ η*((m:ℝ)/2) := by
    change 2*(2*ε*(m:ℝ)+w+(b:ℝ)+1) ≤ η*(m:ℝ) at hMargin
    linarith only [hMargin,hLoss',ht]
  have hPosM : 0 < (m:ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hTolerance : 2*ε ≤ η := by
    apply (mul_le_mul_iff_left₀ hPosM).mp
    change 2*(2*ε*(m:ℝ)+w+(b:ℝ)+1) ≤ η*(m:ℝ) at hMargin
    linarith only [hMargin,hεm,hw,hbR]
  refine ⟨hm,Nat.le_ceil _,?_,hPay.trans hScale⟩
  exact hTolerance

/-- After the coarse refinement, choose the common cluster size for
all three refinements of the proof and superregularize every pair
used by the cycle and the universal walk in the same operation. -/
theorem kuhn_osthus_divisible_superregular_setup
    (G : Digraph V) (f : V → Option I) (R H : Digraph I)
    (m Δ ℓ p q : ℕ) (ε η d : ℝ)
    (hR : H ≤ R) (hSize : ∀ i, (cluster f i).card = m)
    (hq : 0 < q) (hPQ : p ∣ q) (hℓ : 0 < ℓ)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hDegree : ∀ i, inDegree H i+outDegree H i ≤ Δ)
    (hReg : ∀ i j, R.Adj i j → IsUniform G ε (cluster f i) (cluster f j) ∧
      d+ε ≤ density G (cluster f i) (cluster f j)) :
    let b := 200*ℓ*(q/p)
    let t := ⌈(Δ:ℝ)*(2*ε*(m:ℝ))⌉₊
    let a := ((m-t)/b)*b
    2*(2*ε*(m:ℝ)+(Δ:ℝ)*(2*ε*(m:ℝ))+(b:ℝ)+1) ≤ η*(m:ℝ) →
    ∃ g : V → Option I, (∀ i, cluster g i ⊆ cluster f i ∧ (cluster g i).card = a) ∧
      50 ∣ a ∧ (4*ℓ) ∣ a ∧ (∃ z : ℕ, a = (q/p)*z ∧ p*a = q*z) ∧
      (exceptional g).card = (exceptional f).card+(m-a)*Fintype.card I ∧
      (exceptional g).card ≤ (exceptional f).card+(t+b-1)*Fintype.card I ∧
      (∀ i j, R.Adj i j → IsUniform G η (cluster g i) (cluster g j) ∧
        d ≤ density G (cluster g i) (cluster g j)) ∧
      ∀ i j, H.Adj i j → IsLowerSuperregularPair G η d (cluster g i) (cluster g j) := by
  intro b t a hMargin
  have hb : 0 < b := (kuhn_osthus_cluster_size_divisibilities p q ℓ b hq hPQ hℓ (dvd_refl b)).1
  obtain ⟨ht,hBad,hTol,hPay⟩ := kuhn_osthus_integral_superregularity_budget m b Δ ε η hb
    hε.le hη hη₁ hMargin
  have hDvd : b ∣ a := (round_down_cluster_size m t b hb (by omega)).1
  obtain ⟨_,h50,h4,hStyles⟩ := kuhn_osthus_cluster_size_divisibilities p q ℓ a hq hPQ hℓ hDvd
  obtain ⟨g,hG,_,hCount,hCount',hUniform,hSuper⟩ :=
    kuhn_osthus_divisible_superregularization G f R H m t b Δ ε η d hR hSize hb ht
      hε hε₁ hη₁ hTol hDegree hBad hReg hPay
  exact ⟨g,hG,h50,h4,hStyles,hCount,hCount',hUniform,hSuper⟩

/-- Apply the joint trim to the actual arc occurrences of the
universal walk. The factor at index zero may be the base cycle.
Repeated occurrences contribute to the degree budget only through
the union of their arcs. -/
theorem kuhn_osthus_superregular_setup_for_walk {L : ℕ}
    (G : Digraph V) (f : V → Option I) (R : Digraph I) (F : Fin L → Equiv.Perm I)
    (m ℓ p q : ℕ) (ε η d : ℝ)
    (hF : ∀ a i, R.Adj i (F a i)) (hSize : ∀ i, (cluster f i).card = m)
    (hq : 0 < q) (hPQ : p ∣ q) (hℓ : 0 < ℓ)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hReg : ∀ i j, R.Adj i j → IsUniform G ε (cluster f i) (cluster f j) ∧
      d+ε ≤ density G (cluster f i) (cluster f j)) :
    let b := 200*ℓ*(q/p)
    let Δ := 2*L
    let t := ⌈(Δ:ℝ)*(2*ε*(m:ℝ))⌉₊
    let a := ((m-t)/b)*b
    2*(2*ε*(m:ℝ)+(Δ:ℝ)*(2*ε*(m:ℝ))+(b:ℝ)+1) ≤ η*(m:ℝ) →
    ∃ g : V → Option I, (∀ i, cluster g i ⊆ cluster f i ∧ (cluster g i).card = a) ∧
      50 ∣ a ∧ (4*ℓ) ∣ a ∧ (∃ z : ℕ, a = (q/p)*z ∧ p*a = q*z) ∧
      (exceptional g).card = (exceptional f).card+(m-a)*Fintype.card I ∧
      (exceptional g).card ≤ (exceptional f).card+(t+b-1)*Fintype.card I ∧
      (∀ i j, R.Adj i j → IsUniform G η (cluster g i) (cluster g j) ∧
        d ≤ density G (cluster g i) (cluster g j)) ∧
      ∀ a i, IsLowerSuperregularPair G η d (cluster g i) (cluster g (F a i)) := by
  intro b Δ t a hMargin
  have hLe : matchingUnion F ≤ R := by
    rintro i j ⟨a,rfl⟩
    exact hF a i
  have hDegree (i : I) : inDegree (matchingUnion F) i + outDegree (matchingUnion F) i ≤ Δ := by
    obtain ⟨hi,ho⟩ := matchingUnion_semidegrees F i
    dsimp only [Δ]
    omega
  obtain ⟨g,hG,h50,h4,hStyles,hCount,hCount',hUniform,hSuper⟩ :=
    kuhn_osthus_divisible_superregular_setup G f R (matchingUnion F) m Δ ℓ p q ε η d
      hLe hSize hq hPQ hℓ hε hε₁ hη hη₁ hDegree hReg hMargin
  exact ⟨g,hG,h50,h4,hStyles,hCount,hCount',hUniform,fun a i => hSuper i (F a i) ⟨a,rfl⟩⟩

end OverfullWork.DirectedRobustExpansion
