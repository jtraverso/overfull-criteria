module

public import OverfullWork.DirectedEquitablePureBudget
public import OverfullWork.RegularizedRobustQuotient
public import OverfullWork.PurePairPreservation

@[expose] public section


/-! Convert the equitable directed partition into a robust reduced
graph whose edges still represent regular pairs of the original host. -/
namespace OverfullWork.DirectedClusterQuotient

open Finset Finpartition DirectedPairEnergy DirectedRobustExpansion DirectedRegularPairs
  DirectedDegreeTrimming
open scoped Classical
universe u

set_option maxHeartbeats 1200000 in
/-- Clean a pure subgraph after a preliminary bounded-degree deletion.
The initial pairs and their density floor still refer to the original
host. Only the remaining arc loss is used to trim the clusters. -/
theorem exists_clean_reduced_partition_with_pure_data {V I : Type u} [Fintype V] [Fintype I]
    (G D : Digraph V) (f : V → Option I) (m : ℕ) (ε d θ ν τ α : ℝ)
    (hV : 0 < Fintype.card V) (hm : 0 < m) (hν : 0 < ν) (hτ : 0 < τ) (hα : 0 < α)
    (hθ : 0 < θ) (hθSmall : θ ≤ 1/16) (hθν : θ ≤ ν/24) (hθα : θ ≤ α/12)
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1/2)
    (hLarge : 1 ≤ θ*(Fintype.card V:ℝ)) (hWindow : 2 ≤ τ*(Fintype.card V:ℝ))
    (hClusters : 8 ≤ ν*(Fintype.card I:ℝ)) (hSizeF : ∀ i, (cluster f i).card = m)
    (hE : ((exceptional f).card:ℝ) ≤ θ*(Fintype.card V:ℝ))
    (hRobust : IsRealRobust D ν τ)
    (hIn : ∀ v, α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v, α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) :
    let H := restrictPairs G f (regularReduced G f ε d)
    H ≤ D → (total (D \ H):ℝ) ≤ θ^4*(Fintype.card V:ℝ)^2/2 →
    ∃ (J : Type u) (inst : Fintype J),
      letI := inst
      ∃ (g : V → Option J) (R : Digraph J) (base : ℕ),
        0 < base ∧ (∀ j, (cluster g j).card = base) ∧
        Fintype.card I ≤ 2*Fintype.card J ∧ Fintype.card J ≤ Fintype.card I ∧
        ((exceptional g).card:ℝ) ≤ 4*θ*(Fintype.card V:ℝ) ∧
        (∀ j, ¬ R.Adj j j) ∧ IsRealRobust R (ν/2) (2*τ) ∧
        (∀ j, (α/2)*(Fintype.card J:ℝ) ≤ (inDegree R j:ℝ)) ∧
        (∀ j, (α/2)*(Fintype.card J:ℝ) ≤ (outDegree R j:ℝ)) ∧
        (∀ i j, R.Adj i j → IsUniform G (2*ε) (cluster g i) (cluster g j) ∧
          d-ε ≤ density G (cluster g i) (cluster g j)) ∧ R = quotient H g ∧
        (∀ v, g v ≠ none → inDegree (D \ H) v ≤ ⌈θ^2*(Fintype.card V:ℝ)⌉₊ ∧
          outDegree (D \ H) v ≤ ⌈θ^2*(Fintype.card V:ℝ)⌉₊) ∧
        ∀ i j, R.Adj i j → IsUniform H (2*ε) (cluster g i) (cluster g j) ∧
          d-ε ≤ density H (cluster g i) (cluster g j) := by
  intro H hLe hLoss
  let L := ⌈θ^2*(Fintype.card V:ℝ)⌉₊
  let q := ⌊θ*(m:ℝ)⌋₊
  let J := retained f (bad (D \ H) L) q
  have hL : θ^2*(Fintype.card V:ℝ) ≤ (L:ℝ)+1 := (Nat.le_ceil _).trans (le_add_of_nonneg_right (by norm_num))
  have hq : θ*(m:ℝ) ≤ (q:ℝ)+1 := (Nat.lt_floor_add_one _).le
  have hRet := retained_at_least_half f (bad (D \ H) L) m q θ hm hSizeF hθ
    (by linarith only [hθSmall]) hE (bad_fraction_of_total D H L θ hV hθ hLoss hL) hq
  obtain ⟨g,hSizeG,hBase,hSub,hExc,hRob,hIn',hOut',hDefect⟩ :=
    exists_regularized_robust_quotient_with_loss D H hLe f m θ ν τ α hm hSizeF
      hθ hθSmall hθν hθα hν hτ hα hLarge hClusters hWindow hE hLoss hRobust hIn hOut
  let R := quotient H g
  have hOrigins {i j : J} (h : R.Adj i j) : (regularReduced G f ε d).Adj i.val j.val := by
    obtain ⟨x,y,hx,hy,hxy⟩ := h
    obtain ⟨_,a,b,ha,hb,hPair⟩ := hxy
    have hxi := (mem_cluster f i.val x).mp (hSub i ((mem_cluster g i x).mpr hx))
    have hyj := (mem_cluster f j.val y).mp (hSub j ((mem_cluster g j y).mpr hy))
    exact (Option.some.inj (ha.symm.trans hxi)) ▸ (Option.some.inj (hb.symm.trans hyj)) ▸ hPair
  have hFull : m ≤ 2*(m-q) := by
    have hFloor : (q:ℝ) ≤ θ*(m:ℝ) := Nat.floor_le (by positivity)
    have hSmall := mul_le_mul_of_nonneg_right hθSmall (Nat.cast_nonneg m)
    have hq' : 2*q ≤ m := by
      exact_mod_cast (show (2:ℝ)*(q:ℝ) ≤ (m:ℝ) by
        linarith only [hFloor,hSmall,Nat.cast_nonneg (α := ℝ) m])
    omega
  let f' : V → Option J := mapCells (fun i : J => cluster f i.val)
  have hF' (i : J) : cluster f' i = cluster f i.val := cluster_mapCells _ (fun _ _ h =>
    clusters_disjoint f (fun he => h (Subtype.ext he))) i
  have hPairs (i j : J) (h : R.Adj i j) :
      IsUniform G (2*ε) (cluster g i) (cluster g j) ∧ d-ε ≤ density G (cluster g i) (cluster g j) := by
    have hPair := hOrigins h
    apply regular_equal_fibres G f' g (m-q) m (fun i => by rw [hF',hSizeF]) hSizeG
      (fun i => by rw [hF']; exact hSub i) hFull i j ε d hε hε₁
    · simpa only [hF'] using hPair.2.1
    · simpa only [hF'] using hPair.2.2
  refine ⟨J,inferInstance,g,R,m-q,hBase,hSizeG,?_,?_,hExc,fun j h => (hOrigins h).1 rfl,hRob,hIn',hOut',
    hPairs,rfl,hDefect,?_⟩
  · rw [Fintype.card_coe]
    exact hRet
  · rw [Fintype.card_coe]
    exact card_le_univ J
  · intro i j hij
    have hAgree (x : V) (hx : x ∈ cluster g i) (y : V) (hy : y ∈ cluster g j) :
        G.Adj x y ↔ H.Adj x y := by
      constructor
      · intro h
        exact ⟨h,i.val,j.val,(mem_cluster f i.val x).mp (hSub i hx),
          (mem_cluster f j.val y).mp (hSub j hy),hOrigins hij⟩
      · exact fun h => h.1
    exact ⟨(uniform_congr_on G H _ _ _ hAgree).mp (hPairs i j hij).1,
      (hPairs i j hij).2.trans_eq (density_congr_on G H _ _ hAgree)⟩

/-- Clean the retained clusters and record their regular pairs in the host. -/
theorem exists_clean_reduced_partition_from_pure_loss {V I : Type u} [Fintype V] [Fintype I]
    (G D : Digraph V) (f : V → Option I) (m : ℕ) (ε d θ ν τ α : ℝ)
    (hV : 0 < Fintype.card V) (hm : 0 < m) (hν : 0 < ν) (hτ : 0 < τ) (hα : 0 < α)
    (hθ : 0 < θ) (hθSmall : θ ≤ 1/16) (hθν : θ ≤ ν/24) (hθα : θ ≤ α/12)
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1/2)
    (hLarge : 1 ≤ θ*(Fintype.card V:ℝ)) (hWindow : 2 ≤ τ*(Fintype.card V:ℝ))
    (hClusters : 8 ≤ ν*(Fintype.card I:ℝ)) (hSizeF : ∀ i, (cluster f i).card = m)
    (hE : ((exceptional f).card:ℝ) ≤ θ*(Fintype.card V:ℝ))
    (hRobust : IsRealRobust D ν τ)
    (hIn : ∀ v, α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v, α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) :
    let H := restrictPairs G f (regularReduced G f ε d)
    H ≤ D → (total (D \ H):ℝ) ≤ θ^4*(Fintype.card V:ℝ)^2/2 →
    ∃ (J : Type u) (inst : Fintype J),
      letI := inst
      ∃ (g : V → Option J) (R : Digraph J) (base : ℕ),
        0 < base ∧ (∀ j, (cluster g j).card = base) ∧
        Fintype.card I ≤ 2*Fintype.card J ∧ Fintype.card J ≤ Fintype.card I ∧
        ((exceptional g).card:ℝ) ≤ 4*θ*(Fintype.card V:ℝ) ∧
        (∀ j, ¬ R.Adj j j) ∧ IsRealRobust R (ν/2) (2*τ) ∧
        (∀ j, (α/2)*(Fintype.card J:ℝ) ≤ (inDegree R j:ℝ)) ∧
        (∀ j, (α/2)*(Fintype.card J:ℝ) ≤ (outDegree R j:ℝ)) ∧
        ∀ i j, R.Adj i j → IsUniform G (2*ε) (cluster g i) (cluster g j) ∧
          d-ε ≤ density G (cluster g i) (cluster g j) := by
  intro H hLe hLoss
  obtain ⟨J,inst,g,R,base,hBase,hSize,hLower,hUpper,hExc,hLoop,hR,hIn',hOut',hPairs,_,_,_⟩ :=
    exists_clean_reduced_partition_with_pure_data G D f m ε d θ ν τ α hV hm hν hτ hα
      hθ hθSmall hθν hθα hε hε₁ hLarge hWindow hClusters hSizeF hE hRobust hIn hOut hLe hLoss
  exact ⟨J,inst,g,R,base,hBase,hSize,hLower,hUpper,hExc,hLoop,hR,hIn',hOut',hPairs⟩

/-- Clean vertices with excessive arc loss and equalize the retained
clusters. The reduced expansion survives, and every retained reduced
edge admits the sliced pair in the original, uncleaned graph. -/
theorem exists_clean_reduced_partition_of_equitable {V : Type u} [Fintype V]
    (G : Digraph V) (P : Finpartition (univ : Finset V)) (m k : ℕ) (ε ζ d θ ν τ α : ℝ)
    (hV : 0 < Fintype.card V) (hm : 0 < m) (hν : 0 < ν) (hτ : 0 < τ) (hα : 0 < α)
    (hθ : 0 < θ) (hθSmall : θ ≤ 1/16) (hθν : θ ≤ ν/24) (hθα : θ ≤ α/12)
    (hζ : ζ ≤ θ) (hε : 0 ≤ ε) (hε₁ : ε ≤ 1/2) (hd : 0 ≤ d)
    (hLarge : 1 ≤ θ*(Fintype.card V:ℝ)) (hWindow : 2 ≤ τ*(Fintype.card V:ℝ))
    (hK : 8 ≤ ν*(k:ℝ)) (hOrder : 2*k*m ≤ Fintype.card V)
    (hSize : ∀ U ∈ P.parts, U.card ≤ m)
    (hRest : (∑ U ∈ P.parts, if U.card = m then (0:ℝ) else (U.card:ℝ)) ≤ ζ*(Fintype.card V:ℝ))
    (hIrregular : irregularMass G P ε ≤ ε)
    (hBudget : (2*ζ+ε+d)*(Fintype.card V:ℝ)^2+(m:ℝ)*(Fintype.card V:ℝ) ≤
      θ^4*(Fintype.card V:ℝ)^2/2)
    (hRobust : IsRealRobust G ν τ)
    (hIn : ∀ v, α*(Fintype.card V:ℝ) ≤ (inDegree G v:ℝ))
    (hOut : ∀ v, α*(Fintype.card V:ℝ) ≤ (outDegree G v:ℝ)) :
    ∃ (J : Type u) (inst : Fintype J),
      letI := inst
      ∃ (g : V → Option J) (R : Digraph J) (base : ℕ),
        0 < base ∧ (∀ j, (cluster g j).card = base) ∧
        k ≤ 2*Fintype.card J ∧ Fintype.card J ≤ P.parts.card ∧
        ((exceptional g).card:ℝ) ≤ 4*θ*(Fintype.card V:ℝ) ∧
        (∀ j, ¬ R.Adj j j) ∧ IsRealRobust R (ν/2) (2*τ) ∧
        (∀ j, (α/2)*(Fintype.card J:ℝ) ≤ (inDegree R j:ℝ)) ∧
        (∀ j, (α/2)*(Fintype.card J:ℝ) ≤ (outDegree R j:ℝ)) ∧
        ∀ i j, R.Adj i j → IsUniform G (2*ε) (cluster g i) (cluster g j) ∧
          d-ε ≤ density G (cluster g i) (cluster g j) := by
  let I := P.parts.filter (fun U => U.card = m)
  have hZθ := hRest.trans (mul_le_mul_of_nonneg_right hζ (Nat.cast_nonneg (Fintype.card V)))
  have hHalf : (∑ U ∈ P.parts, if U.card = m then (0:ℝ) else (U.card:ℝ)) ≤ (Fintype.card V:ℝ)/2 := by
    linarith only [hZθ,mul_le_mul_of_nonneg_right hθSmall (Nat.cast_nonneg (Fintype.card V)),
      Nat.cast_nonneg (α := ℝ) (Fintype.card V)]
  obtain ⟨f,hLower,hUpper,hLabel,hZ⟩ := equitable_partition_cluster_map P m k hm hOrder hHalf
  let H := restrictPairs G f (regularReduced G f ε d)
  have hE : ((exceptional f).card:ℝ) ≤ θ*(Fintype.card V:ℝ) := hZ.trans_le hZθ
  have hLoss : (total (G \ H):ℝ) ≤ θ^4*(Fintype.card V:ℝ)^2/2 :=
    (equitable_pure_deletion_bound G P m ε ζ d hV hd hSize hRest hIrregular f (fun i => (hLabel i).1)).trans hBudget
  have hSizeF (i : I) : (cluster f i).card = m := (hLabel i).2
  have hClusters : 8 ≤ ν*(Fintype.card I:ℝ) := by
    rw [Fintype.card_coe]
    exact hK.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hLower) hν.le)
  obtain ⟨J,inst,g,R,base,hBase,hSizeG,hRet,hUpperJ,hExc,hLoop,hR,hIn',hOut',hPair⟩ :=
    exists_clean_reduced_partition_from_pure_loss G G f m ε d θ ν τ α hV hm hν hτ hα
      hθ hθSmall hθν hθα hε hε₁ hLarge hWindow hClusters hSizeF hE hRobust hIn hOut
      (restrictPairs_le _ _ _) hLoss
  let _ : Fintype J := inst
  have hLower' : k ≤ Fintype.card I := by simpa only [Fintype.card_coe] using hLower
  have hUpper' : Fintype.card I ≤ P.parts.card := by simpa only [Fintype.card_coe] using hUpper
  exact ⟨J,inst,g,R,base,hBase,hSizeG,hLower'.trans hRet,hUpperJ.trans hUpper',hExc,hLoop,hR,hIn',hOut',hPair⟩

/-- Degree-form directed regularity for a robust host, in the form
needed by the coarse winding construction. The cluster bound and
the host threshold are uniform over the graph. -/
theorem exists_robust_directed_regular_partition
    (ν τ α θ ε ζ d : ℝ) (kMin : ℕ)
    (hν : 0 < ν) (hτ : 0 < τ) (hα : 0 < α)
    (hθ : 0 < θ) (hθSmall : θ ≤ 1/16) (hθν : θ ≤ ν/24) (hθα : θ ≤ α/12)
    (hε : 0 < ε) (hε₁ : ε ≤ 1/2) (hζ : 0 < ζ) (hζθ : ζ ≤ θ) (hd : 0 ≤ d)
    (hMargin : 2*ζ+ε+d < θ^4/2) :
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
          (∀ j, ¬ R.Adj j j) ∧ IsRealRobust R (ν/2) (2*τ) ∧
          (∀ j, (α/2)*(Fintype.card J:ℝ) ≤ (inDegree R j:ℝ)) ∧
          (∀ j, (α/2)*(Fintype.card J:ℝ) ≤ (outDegree R j:ℝ)) ∧
          ∀ i j, R.Adj i j → IsUniform G (2*ε) (cluster g i) (cluster g j) ∧
            d-ε ≤ density G (cluster g i) (cluster g j) := by
  let gap := θ^4/2-(2*ζ+ε+d)
  have hGap : 0 < gap := sub_pos.mpr hMargin
  let k := max (2*kMin) (max ⌈8/ν⌉₊ ⌈1/gap⌉₊)
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
  have hK : 8 ≤ ν*(k:ℝ) := by
    have hC : 8/ν ≤ (k:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈8/ν⌉₊ ≤ k from (le_max_left _ _).trans (le_max_right _ _)))
    simpa only [mul_comm] using (div_le_iff₀ hν).mp hC
  have hKg : 1 ≤ gap*(k:ℝ) := by
    have hC : 1/gap ≤ (k:ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈1/gap⌉₊ ≤ k from (le_max_right _ _).trans (le_max_right _ _)))
    simpa only [mul_comm] using (div_le_iff₀ hGap).mp hC
  obtain ⟨m,P,hm,hOrder,hCount,hSize,hRest,hIrr⟩ := hN G ((le_max_left _ _).trans hT)
  have hB : (2*ζ+ε+d)*(n:ℝ)^2+(m:ℝ)*(n:ℝ) ≤ θ^4*(n:ℝ)^2/2 := by
    have hKM : (k:ℝ)*(m:ℝ) ≤ n := by exact_mod_cast (show k*m ≤ n from
      (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)).trans (by simpa only [Nat.mul_assoc] using hOrder))
    have hM : (m:ℝ) ≤ gap*(n:ℝ) := by
      exact (by simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hKg (Nat.cast_nonneg m) :
        (m:ℝ) ≤ gap*((k:ℝ)*(m:ℝ))).trans (mul_le_mul_of_nonneg_left hKM hGap.le)
    have h := mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg n)
    dsimp only [gap] at h
    linarith only [h]
  obtain ⟨J,inst,g,R,base,hBase,hBaseSize,hLower,hUpper,hExc,hLoop,hR,hInR,hOutR,hPairs⟩ :=
    exists_clean_reduced_partition_of_equitable G P m k ε ζ d θ ν τ α hn hm hν hτ hα hθ hθSmall hθν hθα
      hζθ hε.le hε₁ hd hLarge hWindow hK hOrder hSize hRest hIrr.le hB hRob hIn hOut
  let _ : Fintype J := inst
  have hkMin : kMin ≤ Fintype.card J :=
    Nat.le_of_mul_le_mul_left ((le_max_left _ _).trans hLower) (by decide)
  exact ⟨J,inst,g,R,base,hBase,hBaseSize,hkMin,hUpper.trans hCount,hExc,hLoop,hR,hInR,hOutR,hPairs⟩

end OverfullWork.DirectedClusterQuotient
