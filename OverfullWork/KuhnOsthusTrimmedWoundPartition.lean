module

public import OverfullWork.KuhnOsthusCommonWoundFactors
public import OverfullWork.ChunkedCellPartitions
public import OverfullWork.KuhnOsthusDivisibleSuperregularization
public import OverfullWork.KuhnOsthusUniversalWalkFromExpansion
public import OverfullWork.KuhnOsthusWoundSetup

@[expose] public section


/-! Build the consistent system of Theorem 1.2 from the ordered
coarse reduced cycle and trim all pairs of the actual universal walk. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs DirectedClusterQuotient
open scoped Classical
universe u

/-- Choose the profile error and the two regularity errors before the
cluster sizes are known. A common lower bound on the cluster size
pays for the last rounding and preserves the margin in (CSys8). -/
theorem exists_kuhn_osthus_joint_trim_tolerances
    (ℓ L b : ℕ) (target τ θ : ℝ) (hTarget : 0 < target) (hτ : 0 < τ) (hθ : θ < 1) :
    ∃ ε ξ η : ℝ, 0 < ε ∧ 0 < ξ ∧ ξ ≤ 1 ∧ 0 < η ∧ η ≤ 1 ∧
      (ℓ:ℝ)*ε ≤ ξ ∧ 2*ε ≤ ξ ∧ η ≤ target ∧ η ≤ (1-ε-θ)*τ ∧
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        2*(2*ξ*(m:ℝ)+((2*(L+1):ℕ):ℝ)*(2*ξ*(m:ℝ))+(b:ℝ)+1) ≤ η*(m:ℝ) := by
  let η := min (min 1 target) ((1-θ)*τ/4)
  let D := (((2*(L+1):ℕ):ℝ)+1)
  have hθ' : 0 < 1-θ := sub_pos.mpr hθ
  have hη : 0 < η := lt_min (lt_min (by norm_num) hTarget) (by positivity)
  have hη₁ : η ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hηTarget : η ≤ target := (min_le_left _ _).trans (min_le_right _ _)
  have hηTrim : η ≤ (1-θ)*τ/4 := min_le_right _ _
  have hD : 1 ≤ D := by dsimp only [D]; exact le_add_of_nonneg_left (by positivity)
  let ξ := η/(16*D)
  have hξ : 0 < ξ := by dsimp only [ξ]; positivity
  have hξEq : ξ*(16*D) = η := div_mul_cancel₀ _ (by positivity)
  have hξ₁ : ξ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hD hξ.le
    linarith only [h,hη₁,hξEq,hξ]
  let ε := min ((1-θ)/2) (ξ/(2*((ℓ:ℝ)+1)))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεθ : ε ≤ (1-θ)/2 := min_le_left _ _
  have hεξ : ε*(2*((ℓ:ℝ)+1)) ≤ ξ :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hTrim : η ≤ (1-ε-θ)*τ := by
    have h := mul_le_mul_of_nonneg_right hεθ hτ.le
    linarith only [hηTrim,h,mul_pos hθ' hτ]
  let M := ⌈4*((b:ℝ)+1)/η⌉₊
  refine ⟨ε,ξ,η,hε,hξ,hξ₁,hη,hη₁,?_,?_,hηTarget,hTrim,M,?_⟩
  · linarith only [hεξ,hε,mul_nonneg (Nat.cast_nonneg ℓ) hε.le]
  · linarith only [hεξ,mul_nonneg (Nat.cast_nonneg ℓ) hε.le]
  · intro m hm
    have hm' : (M:ℝ) ≤ m := by exact_mod_cast hm
    have hM : 4*((b:ℝ)+1)/η ≤ (m:ℝ) := (Nat.le_ceil _).trans hm'
    have hRound := (div_le_iff₀ hη).mp hM
    have h := mul_le_mul_of_nonneg_right hξEq.le (Nat.cast_nonneg m)
    dsimp only [D] at h
    linarith only [hRound,h,mul_nonneg hη.le (Nat.cast_nonneg m)]

set_option maxHeartbeats 1250000 in
/-- The output already satisfies the common partition hypothesis of
Lemma 7.6. The same trimmed cells work for all arcs of the chosen
universal walk. Both the original profiles and the exact count of
added exceptional vertices are retained. -/
theorem exists_kuhn_osthus_trimmed_wound_partition
    (C ε ξ η d α θ μ τ : ℝ) (ℓ L f q : ℕ)
    (hC : 0 < C) (hε : 0 < ε) (hℓ : 0 < ℓ) (hq : 0 < q) (hfq : f ∣ q)
    (hξ : 0 < ξ) (hξ₁ : ξ ≤ 1) (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hScale : (ℓ:ℝ)*ε ≤ ξ) (hScale' : 2*ε ≤ ξ)
    (hμ : 0 < μ) (hμτ : μ ≤ τ) (hτ : τ ≤ 1/4) (hατ : 4*τ ≤ α)
    (hTrim : η ≤ (1-ε-θ)*τ) (hWalk : ⌈25/(μ^2/2)^2⌉₊+4 ≤ L) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {k : ℕ}
      (G : Digraph V) (Z₀ : Finset V) (P : Fin k → Finset V) (R₀ : Digraph (Fin k))
      (hk : 0 < k) (m : ℕ),
      let n := ℓ*k
      let parent := windingParent (n := n) k hk
      let R := fibrePullback R₀ parent parent
      let b := 200*(L+1)*(q/f)
      let t := ⌈((2*(L+1):ℕ):ℝ)*(2*ξ*(m:ℝ))⌉₊
      let a := ((m-t)/b)*b
      N ≤ ℓ*m → 2 ≤ k → 2 ≤ τ*(k:ℝ) →
      (∀ i, (P i).card = ℓ*m) → (∀ i j, i ≠ j → Disjoint (P i) (P j)) →
      (∀ i, Disjoint (P i) Z₀) → (∀ v, v ∉ Z₀ → v ∈ univ.biUnion P) →
      (Z₀.card:ℝ) ≤ (α/3)*(Fintype.card V:ℝ) →
      (∀ v, α*(Fintype.card V:ℝ) ≤ (inDegree G v:ℝ) ∧ α*(Fintype.card V:ℝ) ≤ (outDegree G v:ℝ)) →
      2*(Fintype.card V:ℝ) ≤ C*((ℓ*m:ℕ):ℝ) →
      (∀ i j, R₀.Adj i j → IsUniform G ε (P i) (P j) ∧ d+ξ+ε ≤ density G (P i) (P j)) →
      (∀ i, R₀.Adj i (finRotate k i)) → (∀ i, ¬ R₀.Adj i i) →
      IsRealRobust R₀ μ τ →
      (∀ i, α*(k:ℝ) ≤ (inDegree R₀ i:ℝ)) → (∀ i, α*(k:ℝ) ≤ (outDegree R₀ i:ℝ)) →
      2*(2*ξ*(m:ℝ)+((2*(L+1):ℕ):ℝ)*(2*ξ*(m:ℝ))+(b:ℝ)+1) ≤ η*(m:ℝ) →
      ∃ (A X : Fin n → Finset V) (Z : Finset V) (l : Fin n → List (Fin n))
        (F : Fin (L+1) → Equiv.Perm (Fin n)),
        WoundExceptionalPartition G Z₀ Z P A X R₀ hk ℓ (ℓ*m) a α θ ε μ τ ∧
        Z₀ ⊆ Z ∧ Z.card = Z₀.card+(m-a)*n ∧
        (Z.card:ℝ) ≤ (Z₀.card:ℝ)+η*(Fintype.card V:ℝ) ∧ b ∣ a ∧
        (∀ i j, R.Adj i j → IsUniform G η (X i) (X j) ∧ d ≤ density G (X i) (X j)) ∧
        (∀ s i, IsLowerSuperregularPair G η d (X i) (X (F s i))) ∧
        F 0 = finRotate n ∧ (∀ s i, R.Adj i (F s i)) ∧
        (∀ j, DirectedListRoutes.Route (reindexSources R (finRotate n).symm) j (finRotate n j) (l j) ∧
          ((l j).length:ℝ) ≤ 3/(μ^2/2)) ∧
        (∀ x y, ((univ : Finset (Fin (L+1))).filter (fun j => F j x = y)).card =
          elementaryChordMultiplicity (finRotate n) l x y +
            if finRotate n x = y then L+1 - (∑ z, elementaryChordMultiplicity (finRotate n) l x z) else 0) ∧
        HasSpanningCycle (fun e f : (Σ _ : Fin (L+1), Fin n) => F e.1 e.2 = f.2) := by
  obtain ⟨N,hN⟩ := exists_kuhn_osthus_wound_refinement.{u} C ε hC hε ℓ hℓ
  refine ⟨N,?_⟩
  intro V _ k G Z₀ P R₀ hk m n parent R b t a hNm hTwo hOrder hSize hDis hOrd hCover hZ hG hProfiles
    hReg hCycle hLoop hRob hIn hOut hMargin
  obtain ⟨A,hA,hADis,hACover,hUniform,hAReg,hNext,hR,hDegrees⟩ :=
    hN G R₀ P hk ξ (d+ξ) μ τ hNm hSize hProfiles hDis hScale hScale' hξ₁ hReg hCycle hμ hμτ hτ hOrder hRob
  have hn : 2 ≤ n := hTwo.trans (Nat.le_mul_of_pos_left _ hℓ)
  have hK : (k:ℝ) ≤ n := by exact_mod_cast Nat.le_mul_of_pos_left k hℓ
  have hτpos : 0 < τ := hμ.trans_le hμτ
  have hμ' : 0 < μ^2/2 := by positivity
  have hSq : μ^2 ≤ τ := by
    have hμ₁ : μ ≤ 1 := by linarith only [hμτ,hτ]
    linarith only [mul_le_of_le_one_right hμ.le hμ₁,hμτ]
  have hDegree (i : Fin n) : 2*(2*τ)*(n:ℝ) ≤ (inDegree R i:ℝ) ∧
      2*(2*τ)*(n:ℝ) ≤ (outDegree R i:ℝ) := by
    rw [(hDegrees i).1,(hDegrees i).2]
    dsimp only [n]
    push_cast
    have h1 := mul_le_mul_of_nonneg_right (hIn (parent i)) (Nat.cast_nonneg ℓ)
    have h2 := mul_le_mul_of_nonneg_right (hOut (parent i)) (Nat.cast_nonneg ℓ)
    have h3 := mul_le_mul_of_nonneg_right hατ (show 0 ≤ (ℓ:ℝ)*(k:ℝ) by positivity)
    exact ⟨by linarith only [h1,h3],by linarith only [h2,h3]⟩
  obtain ⟨l,F,hRoutes,hFirst,hF,hMult,hFWalk⟩ :=
    kuhn_osthus_universal_walk_on_ordered_cycle (μ^2/2) (2*τ) hμ'
      (by linarith only [hSq,hτ]) (by linarith only [hSq,hτpos]) n L R hn hWalk
      (by linarith only [hOrder,mul_le_mul_of_nonneg_left hK hτpos.le]) hR
      (fun i => (hNext i).2) (fun i => (hDegree i).1) (fun i => (hDegree i).2)
  let u := mapCells A
  have hu (i : Fin n) : cluster u i = A i := cluster_mapCells A hADis i
  have hExceptional (x : V) : x ∈ exceptional u ↔ ¬ ∃ i, x ∈ A i := by
    rw [mem_exceptional]
    by_cases h : ∃ i, x ∈ A i <;> simp [u,mapCells,h]
  have hU : exceptional u = Z₀ := by
    ext v
    rw [hExceptional]
    refine ⟨fun hv => ?_,fun hz => ?_⟩
    · by_contra hz
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp (hCover v hz)
      rw [←hACover i] at hi
      obtain ⟨j,_,hj⟩ := mem_biUnion.mp hi
      exact hv ⟨intervalPosition j i,hj⟩
    · rintro ⟨j,hj⟩
      exact disjoint_left.mp (hOrd (parent j)) ((hA j).2 hj) hz
  have hUs (i : Fin n) : (cluster u i).card = m := (congrArg card (hu i)).trans (hA i).1
  obtain ⟨v,hX,_,_,_,hCount,_,hPair,hSuper⟩ := kuhn_osthus_superregular_setup_for_walk
    G u R F m (L+1) f q ξ η d hF hUs hq hfq (by omega) hξ hξ₁ hη hη₁
    (fun i j h => by simpa only [hu] using hAReg i j h) hMargin
  let X := cluster v
  let Z := exceptional v
  have hSub (i : Fin n) : X i ⊆ A i := (hu i) ▸ (hX i).1
  have hb : 0 < b := (kuhn_osthus_cluster_size_divisibilities f q (L+1) b hq hfq (by omega) (dvd_refl b)).1
  obtain ⟨ht,_,_,hPay⟩ :=
    kuhn_osthus_integral_superregularity_budget m b (2*(L+1)) ξ η hb hξ.le hη hη₁ hMargin
  obtain ⟨hDiv,ha,_,_⟩ := round_down_cluster_size m t b hb (by omega)
  have ha' : a ≤ m := ha.trans (Nat.sub_le _ _)
  have hLoss : ((m-a:ℕ):ℝ) ≤ η*(m:ℝ) := by
    have hm := mul_le_mul_of_nonneg_left (show (a:ℝ) ≤ m by exact_mod_cast ha') hη
    linarith only [hPay,hm,mul_nonneg hξ.le (Nat.cast_nonneg m)]
  have hTrim' (i : Fin n) : ((A i \ X i).card:ℝ) ≤ (1-ε-θ)*(τ*((ℓ*m:ℕ):ℝ)/(ℓ:ℝ)) := by
    have hℓR : (ℓ:ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
    have hEq : τ*((ℓ*m:ℕ):ℝ)/(ℓ:ℝ) = τ*(m:ℝ) := by push_cast; field_simp
    rw [card_sdiff_of_subset (hSub i),(hA i).1,(hX i).2,hEq]
    have h := hLoss.trans (mul_le_mul_of_nonneg_right hTrim (Nat.cast_nonneg m))
    linarith only [h]
  have hCount' : Z.card = Z₀.card+(m-a)*n := by
    simpa only [Z,hU,Fintype.card_fin] using hCount
  have hZSubset : Z₀ ⊆ Z := by
    intro x hx
    apply (mem_exceptional v x).mpr
    by_contra h
    obtain ⟨i,hi⟩ := Option.ne_none_iff_exists'.mp h
    exact disjoint_left.mp (hOrd (parent i)) ((hA i).2 (hSub i ((mem_cluster v i x).mpr hi))) hx
  have hZTotal : (Z.card:ℝ) ≤ (Z₀.card:ℝ)+η*(Fintype.card V:ℝ) := by
    have hNSize : m*n ≤ Fintype.card V := by
      have h := order_eq u m hUs
      rw [Fintype.card_fin] at h
      exact h.symm ▸ Nat.le_add_left (m*n) (exceptional u).card
    have hmN : (m:ℝ)*(n:ℝ) ≤ Fintype.card V := by exact_mod_cast hNSize
    rw [hCount']
    push_cast
    linarith only [mul_le_mul_of_nonneg_right hLoss (Nat.cast_nonneg n),mul_le_mul_of_nonneg_left hmN hη]
  refine ⟨A,X,Z,l,F,?_,hZSubset,hCount',hZTotal,hDiv,hPair,hSuper,hFirst,hF,hRoutes,hMult,hFWalk⟩
  refine ⟨hSize,hDis,hCover,hZ,fun x _ => hG x,fun i => ⟨(hX i).2,hSub i⟩,
    (fun _ _ h => clusters_disjoint v h),?_,?_,Nat.mul_le_mul_left _ ha',hTrim',
    (fun i => (hUniform i).1),(fun i => (hUniform i).2),hLoop,hRob,hIn,hOut⟩
  · intro i
    exact (exceptional_disjoint_lift v {i}).symm.mono_left
      (fun x hx => (mem_lift v {i} x).mpr ⟨i,mem_singleton_self _,(mem_cluster v i x).mp hx⟩)
  · intro x hx
    obtain ⟨i,hi⟩ := Option.ne_none_iff_exists'.mp (fun h => hx ((mem_exceptional v x).mpr h))
    exact ⟨i,(mem_cluster v i x).mpr hi⟩

end OverfullWork.DirectedRobustExpansion
