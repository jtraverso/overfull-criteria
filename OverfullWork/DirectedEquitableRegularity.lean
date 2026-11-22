module

public import OverfullWork.DirectedEquitableRefinement
public import OverfullWork.DirectedWeightedRegularity
public import OverfullWork.ChunkedCellPartitions

@[expose] public section


/-! Equitable directed regularity via the same common energy
increment. Rechunk after each witness refinement, keeping all the
short remainders as parts until the iteration terminates. -/
namespace OverfullWork.DirectedPairEnergy

open Finset Finpartition DirectedClusterQuotient
open scoped Classical
universe u

private noncomputable def equitableResolution (ζ : ℝ) (k : ℕ) : ℕ → ℕ
  | 0 => max (2*k) (max 2 ⌈1/ζ⌉₊)
  | i+1 =>
    let s := equitableResolution ζ k i
    max s ⌈(refinementBound (3*s) 1:ℝ)/ζ⌉₊

set_option maxHeartbeats 1800000 in
/-- The directed energy iteration gives one common partition with
uniform-size ordinary cells. Both the irregular mass and the total
size of the short remainders can be prescribed independently. -/
theorem exists_equitable_directed_regular_partition
    (ε ζ : ℝ) (hε : 0 < ε) (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1/2) (k : ℕ) :
    ∃ N K : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V), N ≤ Fintype.card V →
      ∃ (m : ℕ) (P : Finpartition (univ : Finset V)),
        0 < m ∧ 2*k*m ≤ Fintype.card V ∧ P.parts.card ≤ K ∧
        (∀ U ∈ P.parts, U.card ≤ m) ∧
        (∑ U ∈ P.parts, if U.card = m then (0:ℝ) else (U.card:ℝ)) ≤ ζ*(Fintype.card V:ℝ) ∧
        irregularMass G P ε < ε := by
  obtain ⟨t,ht⟩ := exists_nat_gt (1/ε^5)
  let B := equitableResolution ζ k
  have hBM : Monotone B := monotone_nat_of_le_succ (fun i => le_max_left _ _)
  have hB₂ (i : ℕ) : 2 ≤ B i :=
    ((le_max_left 2 ⌈1/ζ⌉₊).trans (le_max_right (2*k) _)).trans (hBM (Nat.zero_le i))
  have hBk (i : ℕ) : 2*k ≤ B i :=
    (le_max_left (2*k) (max 2 ⌈1/ζ⌉₊)).trans (hBM (Nat.zero_le i))
  refine ⟨2*(B t),3*(B t),?_⟩
  intro V _ G hV
  let n := Fintype.card V
  have hSize (i : ℕ) (hi : i ≤ t) : 2*(B i) ≤ n :=
    (Nat.mul_le_mul_left 2 (hBM hi)).trans hV
  have hRechunk (P : Finpartition (univ : Finset V)) (i : ℕ) (hi : i ≤ t)
      (hP : (P.parts.card:ℝ) ≤ ζ*((B i:ℕ):ℝ)) :
      ∃ (m : ℕ) (Q : Finpartition (univ : Finset V)),
        0 < m ∧ 2*k*m ≤ n ∧ Q.parts.card ≤ 3*(B i) ∧
        (∀ U ∈ Q.parts, U.card ≤ m) ∧
        (∑ U ∈ Q.parts, if U.card = m then (0:ℝ) else (U.card:ℝ)) ≤ ζ*(n:ℝ) ∧
        partitionEnergy G P ≤ partitionEnergy G Q := by
    let s := B i
    let m := n/s
    have hs : 0 < s := by have h := hB₂ i; change 2 ≤ s at h; omega
    have hm : 2 ≤ m := (Nat.le_div_iff_mul_le hs).mpr (hSize i hi)
    have hm0 : 0 < m := by omega
    have hVol : m*s ≤ n := Nat.div_mul_le_self n s
    have hBound : n/m ≤ 2*s := by
      have hRem : n%s ≤ s*m := (Nat.mod_lt _ hs).le.trans (Nat.le_mul_of_pos_right _ hm0)
      have hOrder : n%s+s*m = n := Nat.mod_add_div n s
      have hN : n ≤ 2*s*m := by
        rw [←hOrder,show 2*s*m = s*m+s*m by ring]
        exact Nat.add_le_add_right hRem _
      exact (Nat.div_le_div_right hN).trans (by rw [Nat.mul_div_cancel _ hm0])
    obtain ⟨Q,_,hEnergy,hCount,hPart,hRest⟩ := exists_equitable_refinement_at_size G P m hm0
    have hP' : P.parts.card ≤ s := by
      have hζ' : ζ ≤ 1 := by linarith only [hζ₁]
      exact_mod_cast hP.trans (mul_le_of_le_one_left (Nat.cast_nonneg s) hζ')
    have hMass : (P.parts.card:ℝ)*((m:ℝ)-1) ≤ ζ*(n:ℝ) := by
      have hProd : (m:ℝ)*(s:ℝ) ≤ n := by exact_mod_cast hVol
      have h₁ := mul_le_mul_of_nonneg_right hP (Nat.cast_nonneg m)
      have h₂ := mul_le_mul_of_nonneg_left hProd hζ.le
      linarith only [h₁,h₂,Nat.cast_nonneg (α := ℝ) P.parts.card]
    have hOrd : 2*k*m ≤ n := (Nat.mul_le_mul_right _ (hBk i)).trans (by rwa [mul_comm])
    exact ⟨m,Q,hm0,hOrd,hCount.trans ((Nat.add_le_add hBound hP').trans (by omega)),
      hPart,hRest.trans hMass,hEnergy⟩
  have hPInit : (univ : Finset V) ≠ ⊥ := by
    have hN := hSize 0 (Nat.zero_le t)
    have hS := hB₂ 0
    intro h
    have h0 : n = 0 := by
      rw [show n = (univ : Finset V).card from card_univ.symm,h]
      rfl
    omega
  have hIter (i : ℕ) (hi : i ≤ t) : ∃ (m : ℕ) (P : Finpartition (univ : Finset V)),
      0 < m ∧ 2*k*m ≤ n ∧ P.parts.card ≤ 3*(B i) ∧
      (∀ U ∈ P.parts, U.card ≤ m) ∧
      (∑ U ∈ P.parts, if U.card = m then (0:ℝ) else (U.card:ℝ)) ≤ ζ*(n:ℝ) ∧
      (irregularMass G P ε < ε ∨ (i:ℝ)*ε^5 ≤ partitionEnergy G P) := by
    induction i with
    | zero =>
      let P := Finpartition.indiscrete hPInit
      have hOne : (1:ℝ)/ζ ≤ (B 0:ℕ) := (Nat.le_ceil _).trans (by
        exact_mod_cast (show ⌈1/ζ⌉₊ ≤ B 0 from (le_max_right _ _).trans (le_max_right _ _)))
      have hOld : (P.parts.card:ℝ) ≤ ζ*(B 0:ℕ) := by
        have h := (div_le_iff₀ hζ).mp hOne
        simpa [P,Finpartition.indiscrete,mul_comm] using h
      obtain ⟨m,Q,hm,hOrd,hCount,hPart,hRest,_⟩ := hRechunk P 0 hi hOld
      exact ⟨m,Q,hm,hOrd,hCount,hPart,hRest,Or.inr (by simpa using partitionEnergy_nonneg G Q)⟩
    | succ i ih =>
      obtain ⟨m,P,hm,hOrd,hCount,hPart,hRest,hEither⟩ := ih (Nat.le_of_succ_le hi)
      by_cases hGood : irregularMass G P ε < ε
      · exact ⟨m,P,hm,hOrd,hCount.trans (Nat.mul_le_mul_left _ (hBM (Nat.le_succ i))),
          hPart,hRest,Or.inl hGood⟩
      let R := witnessRefinement G P ε hε
      have hR : R.parts.card ≤ refinementBound (3*(B i)) 1 :=
        (witnessRefinement_card G P ε hε).trans (by
          simp only [refinementBound]
          exact Nat.mul_le_mul hCount (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 hCount)))
      have hCut : (refinementBound (3*(B i)) 1:ℝ)/ζ ≤ (B (i+1):ℕ) := (Nat.le_ceil _).trans (by
        exact_mod_cast (show ⌈(refinementBound (3*(B i)) 1:ℝ)/ζ⌉₊ ≤ B (i+1) from le_max_right _ _))
      have hR' : (R.parts.card:ℝ) ≤ ζ*(B (i+1):ℕ) := by
        have h := (div_le_iff₀ hζ).mp hCut
        exact (by exact_mod_cast hR : (R.parts.card:ℝ) ≤ refinementBound (3*(B i)) 1).trans
          (by simpa only [mul_comm] using h)
      obtain ⟨a,Q,ha,hNewOrd,hNewCount,hNewPart,hNewRest,hEnergy⟩ := hRechunk R (i+1) hi hR'
      have hGain := witnessRefinement_uniform_gain G P ε hε (le_of_not_gt hGood)
      have hPrevious := hEither.resolve_left hGood
      refine ⟨a,Q,ha,hNewOrd,hNewCount,hNewPart,hNewRest,Or.inr ?_⟩
      push_cast
      linarith only [hGain.trans hEnergy,hPrevious]
  obtain ⟨m,P,hm,hOrd,hCount,hPart,hRest,hEither⟩ := hIter t le_rfl
  refine ⟨m,P,hm,hOrd,hCount,hPart,hRest,hEither.resolve_right ?_⟩
  intro hBad
  have h := (div_lt_iff₀ (pow_pos hε 5)).mp ht
  exact (not_lt_of_ge (partitionEnergy_le_one G P)) (h.trans_le hBad)

/-- Read the full blocks as a cluster map. The vertices in all short
blocks are exactly the exceptional set of that map. -/
theorem equitable_partition_cluster_map {V : Type*} [Fintype V]
    (P : Finpartition (univ : Finset V)) (m k : ℕ) (hm : 0 < m)
    (hOrder : 2*k*m ≤ Fintype.card V)
    (hRest : (∑ U ∈ P.parts, if U.card = m then (0:ℝ) else (U.card:ℝ)) ≤ (Fintype.card V:ℝ)/2) :
    let I := P.parts.filter (fun U => U.card = m)
    ∃ f : V → Option I, k ≤ I.card ∧ I.card ≤ P.parts.card ∧
      (∀ i : I, cluster f i = i.val ∧ (cluster f i).card = m) ∧
      ((exceptional f).card:ℝ) = ∑ U ∈ P.parts, if U.card = m then (0:ℝ) else (U.card:ℝ) := by
  intro I
  let f : V → Option I := mapCells Subtype.val
  have hLabel (i : I) : cluster f i = i.val :=
    cluster_mapCells Subtype.val
      (fun i j h => P.disjoint (mem_filter.mp i.prop).1 (mem_filter.mp j.prop).1 (fun he => h (Subtype.ext he))) i
  have hSize (i : I) : (cluster f i).card = m := (congrArg card (hLabel i)).trans (mem_filter.mp i.prop).2
  have hCount := order_eq f m hSize
  rw [Fintype.card_coe I] at hCount
  have hFull : ∑ U ∈ I, U.card = m*I.card := by
    rw [sum_congr rfl (fun U hU => (mem_filter.mp hU).2)]
    simp only [sum_const,nsmul_eq_mul]
    exact Nat.mul_comm _ _
  have hPart := sum_filter_add_sum_filter_not P.parts (fun U => U.card = m) card
  change (∑ U ∈ I, U.card)+(∑ U ∈ P.parts.filter (fun U => ¬ U.card = m), U.card) =
    ∑ U ∈ P.parts, U.card at hPart
  rw [hFull,P.sum_card_parts,card_univ,hCount] at hPart
  have hRem : (exceptional f).card = ∑ U ∈ P.parts.filter (fun U => ¬ U.card = m), U.card := by omega
  have hRemR : ((exceptional f).card:ℝ) = ∑ U ∈ P.parts, if U.card = m then (0:ℝ) else (U.card:ℝ) := by
    rw [hRem,Nat.cast_sum,Finset.sum_filter]
    apply sum_congr rfl
    intro U _
    by_cases h : U.card = m <;> simp [h]
  have hHalf : 2*(exceptional f).card ≤ Fintype.card V := by
    rw [←hRemR] at hRest
    exact_mod_cast (show (2:ℝ)*((exceptional f).card:ℝ) ≤ (Fintype.card V:ℝ) by linarith only [hRest])
  have hCards : Fintype.card V ≤ 2*(m*I.card) := by omega
  have hK : k ≤ I.card := Nat.le_of_mul_le_mul_left
    (show (2*m)*k ≤ (2*m)*I.card from by
      calc
        _ = 2*k*m := by ring
        _ ≤ _ := hOrder.trans hCards
        _ = _ := by ring)
    (by positivity)
  exact ⟨f,hK,card_le_card (filter_subset _ _),fun i => ⟨hLabel i,hSize i⟩,hRemR⟩

end OverfullWork.DirectedPairEnergy
