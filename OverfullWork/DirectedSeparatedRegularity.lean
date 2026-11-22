module

public import OverfullWork.DirectedCleanReducedPartition
public import OverfullWork.DirectedLowDensityCleaning
public import OverfullWork.KuhnOsthusFinalAssembly

@[expose] public section


/-! The density floor spends a bounded part of the ambient semidegree.
It does not constrain the subsequent exceptional-set size. -/
namespace OverfullWork.DirectedClusterQuotient

open Finset Finpartition DirectedPairEnergy DirectedRobustExpansion DirectedRegularPairs
  DirectedDegreeTrimming
open scoped Classical
universe u

set_option maxHeartbeats 1600000 in
/-- Degree-form regularity with independently small exceptional
fraction. Only the regularity tolerance and the fraction of short
cells enter the fourth-power bound used to trim exceptional vertices. -/
theorem exists_robust_directed_pure_partition_separate_density
    (ν τ α θ ε ζ d : ℝ) (kMin : ℕ)
    (hν : 0 < ν) (hτ : 0 < τ) (hα : 0 < α)
    (hθ : 0 < θ) (hθSmall : θ ≤ 1/16) (hθν : θ ≤ ν/48) (hθα : θ ≤ α/24)
    (hε : 0 < ε) (hε₁ : ε ≤ 1/2) (hζ : 0 < ζ) (hζθ : ζ ≤ θ) (hd : 0 ≤ d)
    (hCutν : d+ε ≤ ν/2) (hCutα : d+ε ≤ α/2)
    (hMargin : 2*ζ+3*ε < θ^4/2) :
    ∃ N K : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V), N ≤ Fintype.card V →
      IsRealRobust G ν τ →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (inDegree G v:ℝ)) →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (outDegree G v:ℝ)) →
      ∃ (J : Type u) (inst : Fintype J),
        letI := inst
        ∃ (g : V → Option J) (R : Digraph J) (H : Digraph V) (base : ℕ),
          0 < base ∧ (∀ j, (cluster g j).card = base) ∧
          kMin ≤ Fintype.card J ∧ Fintype.card J ≤ K ∧
          ((exceptional g).card:ℝ) ≤ 4*θ*(Fintype.card V:ℝ) ∧
          (∀ j, ¬ R.Adj j j) ∧ IsRealRobust R (ν/4) (2*τ) ∧
          (∀ j, (α/4)*(Fintype.card J:ℝ) ≤ (inDegree R j:ℝ)) ∧
          (∀ j, (α/4)*(Fintype.card J:ℝ) ≤ (outDegree R j:ℝ)) ∧
          (∀ i j, R.Adj i j → IsUniform G (2*ε) (cluster g i) (cluster g j) ∧
            d-ε ≤ density G (cluster g i) (cluster g j)) ∧
          H ≤ G ∧ R = quotient H g ∧
          (∀ i j, R.Adj i j → IsUniform H (2*ε) (cluster g i) (cluster g j) ∧
            d-ε ≤ density H (cluster g i) (cluster g j)) ∧
          ∀ v, g v ≠ none →
            (inDegree (G \ H) v:ℝ) ≤ (d+ε+2*θ)*(Fintype.card V:ℝ) ∧
            (outDegree (G \ H) v:ℝ) ≤ (d+ε+2*θ)*(Fintype.card V:ℝ) := by
  let gap := θ^4/2-(2*ζ+3*ε)
  have hGap : 0 < gap := sub_pos.mpr hMargin
  let k := max (2*kMin) (max ⌈16/ν⌉₊ ⌈1/gap⌉₊)
  have hζ₁ : ζ ≤ 1/2 := by linarith only [hθSmall,hζθ]
  obtain ⟨N,K,hN⟩ := exists_equitable_directed_regular_partition.{u} ε ζ hε hζ hζ₁ k
  let T := max N (max ⌈1/θ⌉₊ ⌈2/τ⌉₊)
  refine ⟨T,K,?_⟩
  intro V _ G hT hRob hIn hOut
  let n := Fintype.card V
  have hLarge : (1:ℝ) ≤ θ*(n:ℝ) := by
    have hR : 1/θ ≤ (n:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈1/θ⌉₊ ≤ n from ((le_max_left _ _).trans (le_max_right _ _)).trans hT))
    simpa only [mul_comm] using (div_le_iff₀ hθ).mp hR
  have hWindow : (2:ℝ) ≤ τ*(n:ℝ) := by
    have hR : 2/τ ≤ (n:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈2/τ⌉₊ ≤ n from ((le_max_right _ _).trans (le_max_right _ _)).trans hT))
    simpa only [mul_comm] using (div_le_iff₀ hτ).mp hR
  have hn : 0 < n := by
    by_contra! h
    norm_num [Nat.eq_zero_of_le_zero h] at hLarge
  have hK : 8 ≤ (ν/2)*(k:ℝ) := by
    have hC : 16/ν ≤ (k:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈16/ν⌉₊ ≤ k from (le_max_left _ _).trans (le_max_right _ _)))
    linarith only [(div_le_iff₀ hν).mp hC]
  have hKg : 1 ≤ gap*(k:ℝ) := by
    have hC : 1/gap ≤ (k:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈1/gap⌉₊ ≤ k from (le_max_right _ _).trans (le_max_right _ _)))
    simpa only [mul_comm] using (div_le_iff₀ hGap).mp hC
  obtain ⟨m,P,hm,hOrder,hCount,hSize,hRest,hIrr⟩ := hN G ((le_max_left _ _).trans hT)
  have hB : (2*ζ+ε+2*ε)*(n:ℝ)^2+(m:ℝ)*(n:ℝ) ≤ θ^4*(n:ℝ)^2/2 := by
    have hKM : (k:ℝ)*(m:ℝ) ≤ n := by exact_mod_cast (show k*m ≤ n from
      (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)).trans (by simpa only [Nat.mul_assoc] using hOrder))
    have hM : (m:ℝ) ≤ gap*(n:ℝ) := by
      exact (by simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hKg (Nat.cast_nonneg m) :
        (m:ℝ) ≤ gap*((k:ℝ)*(m:ℝ))).trans (mul_le_mul_of_nonneg_left hKM hGap.le)
    have h := mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg n)
    dsimp only [gap] at h
    linarith only [h]
  let I := P.parts.filter (fun U => U.card = m)
  obtain ⟨f,hLower,hUpper,hLabel,hZ⟩ := equitable_partition_cluster_map P m k hm hOrder
    (hRest.trans (by linarith only [mul_le_mul_of_nonneg_right hζ₁ (Nat.cast_nonneg (Fintype.card V))]))
  let B := typicalLowArcs G f ε d
  let D := G \ B
  let H := restrictPairs G f (regularReduced G f ε d)
  have hE : ((exceptional f).card:ℝ) ≤ θ*(n:ℝ) :=
    hZ.trans_le (hRest.trans (mul_le_mul_of_nonneg_right hζθ (Nat.cast_nonneg n)))
  have hCap : (total (D \ H):ℝ) ≤ θ^4*(n:ℝ)^2/2 := by
    refine (equitable_pure_deletion_bound_of_low_pairs G D P m ε ζ d (2*ε)
      (fun _ _ h => h.1) hn (by positivity) hSize hRest hIrr.le f (fun i => (hLabel i).1) ?_).trans hB
    intro i j hNe hReg hLow
    have hCell (i : I) : (cluster f i).Nonempty := card_pos.mp (by rw [(hLabel i).2]; exact hm)
    exact typicalLowArcs_remaining_pair G f ε d i j hNe (hCell i) (hCell j) hε (by linarith) hReg hLow
  have hDegrees := typicalLowArcs_semidegrees G f ε d (by positivity)
  have hDrob : IsRealRobust D (ν/2) τ :=
    hRob.after_indegree_deletion (by linarith) (fun v => (hDegrees v).1.trans (by
      have h := mul_le_mul_of_nonneg_right hCutν (Nat.cast_nonneg n)
      linarith only [h]))
  have hDdegree (v : V) : (α/2)*(n:ℝ) ≤ (inDegree D v:ℝ) ∧
      (α/2)*(n:ℝ) ≤ (outDegree D v:ℝ) := by
    obtain ⟨hi,ho⟩ := residual_semidegrees G B (typicalLowArcs_le G f ε d) v
    have hi' : (inDegree D v:ℝ)+(inDegree B v:ℝ) = inDegree G v := by exact_mod_cast hi
    have ho' : (outDegree D v:ℝ)+(outDegree B v:ℝ) = outDegree G v := by exact_mod_cast ho
    have h := mul_le_mul_of_nonneg_right hCutα (Nat.cast_nonneg n)
    exact ⟨by linarith only [hi',(hDegrees v).1,h,hIn v],by linarith only [ho',(hDegrees v).2,h,hOut v]⟩
  have hK' : 8 ≤ (ν/2)*(Fintype.card I:ℝ) := by
    rw [Fintype.card_coe]
    exact hK.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hLower) (by positivity))
  obtain ⟨J,inst,g,R,base,hBase,hBaseSize,hRet,hUpperJ,hExc,hLoop,hR,hInR,hOutR,hPairs,hQuotient,hDefect,hPairsH⟩ :=
    exists_clean_reduced_partition_with_pure_data G D f m ε d θ (ν/2) τ (α/2) hn hm
      (by positivity) hτ (by positivity) hθ hθSmall (by linarith only [hθν]) (by linarith only [hθα])
      hε.le hε₁ hLarge hWindow hK' (fun i => (hLabel i).2) hE hDrob
      (fun v => (hDdegree v).1) (fun v => (hDdegree v).2)
      (regularPure_le_after_typicalLowArcs G f ε d) hCap
  let _ : Fintype J := inst
  have hkMin : kMin ≤ Fintype.card J := by
    apply Nat.le_of_mul_le_mul_left _ (by decide : 0 < 2)
    have h : k ≤ Fintype.card I := by simpa only [Fintype.card_coe] using hLower
    exact (le_max_left _ _).trans (h.trans hRet)
  have hkMax : Fintype.card J ≤ K := hUpperJ.trans (by
    rw [Fintype.card_coe]
    exact hUpper.trans hCount)
  have he (x : ℝ) : x/2/2 = x/4 := by ring
  have hH : H ≤ G := restrictPairs_le G f _
  have hHtoD : H ≤ D := regularPure_le_after_typicalLowArcs G f ε d
  refine ⟨J,inst,g,R,H,base,hBase,hBaseSize,hkMin,hkMax,hExc,hLoop,
    by simpa only [he] using hR,by simpa only [he] using hInR,by simpa only [he] using hOutR,hPairs,
    hH,hQuotient,hPairsH,?_⟩
  intro v hv
  let L := ⌈θ^2*(n:ℝ)⌉₊
  have hL : (L:ℝ) ≤ 2*θ*(n:ℝ) := by
    have h := (Nat.ceil_lt_add_one (by positivity : 0 ≤ θ^2*(n:ℝ))).le
    have hθ₂ := mul_le_mul_of_nonneg_right (show θ ≤ 1 by linarith only [hθSmall]) hθ.le
    have hBound := mul_le_mul_of_nonneg_right hθ₂ (Nat.cast_nonneg n)
    dsimp only [L]
    linarith only [h,hBound,hLarge]
  obtain ⟨hiD,hoD⟩ := residual_semidegrees G B (typicalLowArcs_le G f ε d) v
  obtain ⟨hiH,hoH⟩ := residual_semidegrees D H hHtoD v
  obtain ⟨hiG,hoG⟩ := residual_semidegrees G H hH v
  have hI : inDegree (G \ H) v ≤ inDegree B v+L := by
    have hh := (hDefect v hv).1
    change inDegree (D \ H) v ≤ L at hh
    change inDegree D v+inDegree B v = inDegree G v at hiD
    omega
  have hO : outDegree (G \ H) v ≤ outDegree B v+L := by
    have hh := (hDefect v hv).2
    change outDegree (D \ H) v ≤ L at hh
    change outDegree D v+outDegree B v = outDegree G v at hoD
    omega
  have hIR : (inDegree (G \ H) v:ℝ) ≤ (inDegree B v:ℝ)+L := by exact_mod_cast hI
  have hOR : (outDegree (G \ H) v:ℝ) ≤ (outDegree B v:ℝ)+L := by exact_mod_cast hO
  exact ⟨by linarith only [hIR,(hDegrees v).1,hL],by linarith only [hOR,(hDegrees v).2,hL]⟩

/-- The robust reduced partition without the additional physical degree data. -/
theorem exists_robust_directed_regular_partition_separate_density
    (ν τ α θ ε ζ d : ℝ) (kMin : ℕ)
    (hν : 0 < ν) (hτ : 0 < τ) (hα : 0 < α)
    (hθ : 0 < θ) (hθSmall : θ ≤ 1/16) (hθν : θ ≤ ν/48) (hθα : θ ≤ α/24)
    (hε : 0 < ε) (hε₁ : ε ≤ 1/2) (hζ : 0 < ζ) (hζθ : ζ ≤ θ) (hd : 0 ≤ d)
    (hCutν : d+ε ≤ ν/2) (hCutα : d+ε ≤ α/2)
    (hMargin : 2*ζ+3*ε < θ^4/2) :
    ∃ N K : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V), N ≤ Fintype.card V →
      IsRealRobust G ν τ →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (inDegree G v:ℝ)) →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (outDegree G v:ℝ)) →
      ∃ (J : Type u) (inst : Fintype J),
        letI := inst
        ∃ (g : V → Option J) (R : Digraph J) (base : ℕ),
          0 < base ∧ (∀ j, (cluster g j).card = base) ∧
          kMin ≤ Fintype.card J ∧ Fintype.card J ≤ K ∧
          ((exceptional g).card:ℝ) ≤ 4*θ*(Fintype.card V:ℝ) ∧
          (∀ j, ¬ R.Adj j j) ∧ IsRealRobust R (ν/4) (2*τ) ∧
          (∀ j, (α/4)*(Fintype.card J:ℝ) ≤ (inDegree R j:ℝ)) ∧
          (∀ j, (α/4)*(Fintype.card J:ℝ) ≤ (outDegree R j:ℝ)) ∧
          ∀ i j, R.Adj i j → IsUniform G (2*ε) (cluster g i) (cluster g j) ∧
            d-ε ≤ density G (cluster g i) (cluster g j) := by
  obtain ⟨N,K,hN⟩ := exists_robust_directed_pure_partition_separate_density.{u} ν τ α θ ε ζ d kMin
    hν hτ hα hθ hθSmall hθν hθα hε hε₁ hζ hζθ hd hCutν hCutα hMargin
  refine ⟨N,K,?_⟩
  intro V _ G hSize hRob hIn hOut
  obtain ⟨J,inst,g,R,H,base,hBase,hSizes,hLower,hUpper,hExc,hLoop,hR,hInR,hOutR,hPairs,_,_,_,_⟩ :=
    hN G hSize hRob hIn hOut
  exact ⟨J,inst,g,R,base,hBase,hSizes,hLower,hUpper,hExc,hLoop,hR,hInR,hOutR,hPairs⟩


end OverfullWork.DirectedClusterQuotient
