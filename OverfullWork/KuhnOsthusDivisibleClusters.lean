module

public import OverfullWork.DirectedInducedPerturbation
public import OverfullWork.ClusterEqualization

@[expose] public section


/-! The two rounding operations at the beginning of the proof of
Kühn–Osthus Theorem 1.2. They act on actual cluster labels or
vertices and charge the removed sets to the exceptional budget. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedClusterQuotient DirectedRegularPairs InducedDigraphSampling
open scoped Classical
variable {V I : Type*} [Fintype V] [Fintype I]

/-- Round down after paying for mandatory deletions. The further
rounding removes strictly fewer than one modulus. -/
theorem round_down_cluster_size (m t b : ℕ) (hb : 0 < b) (ht : t ≤ m) :
    let a := ((m-t)/b)*b
    b ∣ a ∧ a ≤ m-t ∧ m-a = t+(m-t)%b ∧ m-a < t+b := by
  intro a
  have ha : a ≤ m-t := Nat.div_mul_le_self _ _
  have hRem := Nat.mod_add_div (m-t) b
  have hRemLt := Nat.mod_lt (m-t) hb
  rw [Nat.mul_comm b ((m-t)/b)] at hRem
  change (m-t)%b+a = m-t at hRem
  have hd : b ∣ a := dvd_mul_left _ _
  exact ⟨hd,ha,by omega,by omega⟩

/-- First round the *number* of clusters. The reduced digraph is
restricted to the retained labels, with an explicit robustness
budget and both semidegrees preserved up to the deletion count. -/
theorem exists_divisible_induced_reduced_digraph
    (D : Digraph I) (A : Finset I) (b d : ℕ) (ν τ : ℝ)
    (hb : 0 < b) (hν : 0 ≤ ν) (hν₁ : ν ≤ 1) (hτ : 0 ≤ τ) (hτ₁ : τ ≤ 1/2)
    (hRob : IsRealRobust (induced D A) ν τ)
    (hBudgetν : 8*((b-1:ℕ):ℝ) ≤ ν*(A.card:ℝ))
    (hBudgetτ : 4*((b-1:ℕ):ℝ) ≤ τ*(A.card:ℝ))
    (hDeg : ∀ x : A, d ≤ inDegree (induced D A) x ∧ d ≤ outDegree (induced D A) x) :
    ∃ B ⊆ A, B.card = (A.card/b)*b ∧ b ∣ B.card ∧ (A \ B).card = A.card%b ∧
      IsRealRobust (induced D B) (ν/2) (2*τ) ∧
      ∀ x : B, d-A.card%b ≤ inDegree (induced D B) x ∧
        d-A.card%b ≤ outDegree (induced D B) x := by
  obtain ⟨B,hBA,hSize⟩ := exists_subset_card_eq (s := A) (Nat.div_mul_le_self A.card b)
  have hDrop : (A \ B).card = A.card%b := by
    rw [card_sdiff_of_subset hBA,hSize]
    have h := Nat.mod_add_div A.card b
    rw [Nat.mul_comm b (A.card/b)] at h
    omega
  have hLoss : (A \ B).card ≤ b-1 := by
    rw [hDrop]
    exact Nat.le_pred_of_lt (Nat.mod_lt _ hb)
  have hNoAdd : (B \ A).card ≤ b-1 := by simp [sdiff_eq_empty_iff_subset.mpr hBA]
  refine ⟨B,hBA,hSize,hSize.symm ▸ dvd_mul_left _ _,hDrop,
    induced_robust_after_small_vertex_changes D A B ν τ (b-1)
      hν hν₁ hτ hτ₁ hRob hLoss hNoAdd hBudgetν hBudgetτ,?_⟩
  have hCount (U : Finset I) : (A ∩ U).card ≤ (B ∩ U).card + A.card%b := by
    have hSub : (A ∩ U) \ (B ∩ U) ⊆ A \ B := by
      intro x hx
      obtain ⟨hxA,hxU⟩ := mem_inter.mp (mem_sdiff.mp hx).1
      exact mem_sdiff.mpr ⟨hxA,fun h => (mem_sdiff.mp hx).2 (mem_inter.mpr ⟨h,hxU⟩)⟩
    have hDiff := card_le_card hSub
    rw [hDrop] at hDiff
    exact (card_le_card_sdiff_add_card (s := A ∩ U) (t := B ∩ U)).trans (by omega)
  intro x
  let y : A := ⟨x.val,hBA x.prop⟩
  obtain ⟨hi,ho⟩ := hDeg y
  simp only [induced_inDegree,induced_outDegree] at hi ho ⊢
  change d ≤ (A ∩ inProfile D x.val).card at hi
  change d ≤ (A ∩ outProfile D x.val).card at ho
  exact ⟨by have := hCount (inProfile D x.val); omega,
    by have := hCount (outProfile D x.val); omega⟩

/-- Round the sizes of all clusters simultaneously in the original
vertex type. The mandatory sets are removed before choosing the
remaining vertices, and the exceptional count is exact. -/
theorem exists_divisible_cluster_trimming (f : V → Option I) (Bad : I → Finset V)
    (m t b : ℕ) (hb : 0 < b) (ht : t ≤ m)
    (hSize : ∀ i, (cluster f i).card = m) (hBad : ∀ i, (Bad i).card ≤ t) :
    let a := ((m-t)/b)*b
    ∃ g : V → Option I,
      (∀ i, cluster g i ⊆ cluster f i \ Bad i ∧ (cluster g i).card = a) ∧
      (∀ i, b ∣ (cluster g i).card) ∧
      (exceptional g).card = (exceptional f).card+(m-a)*Fintype.card I ∧
      (exceptional g).card ≤ (exceptional f).card+(t+b-1)*Fintype.card I := by
  intro a
  obtain ⟨hDiv,hLe,_,hLoss⟩ := round_down_cluster_size m t b hb ht
  have hRoom (i : I) : a ≤ (cluster f i \ Bad i).card := by
    have hs := card_le_card_sdiff_add_card (s := cluster f i) (t := Bad i)
    rw [hSize i] at hs
    have h := hBad i
    omega
  choose B hB hBC using fun i => exists_subset_card_eq (hRoom i)
  have hSub (i : I) : B i ⊆ cluster f i := (hB i).trans sdiff_subset
  let g := equalize f B
  have hCells (i : I) : cluster g i = B i := cluster_equalize f B hSub i
  have hG (i : I) : (cluster g i).card = a := by rw [hCells,hBC]
  have hVol : (exceptional g).card = (exceptional f).card+(m-a)*Fintype.card I := by
    have hf := order_eq f m hSize
    have hg := order_eq g a hG
    have he : m = a+(m-a) := by omega
    rw [he,Nat.add_mul] at hf
    omega
  refine ⟨g,fun i => ⟨hCells i ▸ hB i,hG i⟩,fun i => hG i ▸ hDiv,hVol,?_⟩
  rw [hVol]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _

/-- Discard whole clusters before refinement. The surviving labels
carry their original physical cells, their regular pairs, and the
induced robust reduced graph. -/
theorem exists_divisible_coarse_partition (G : Digraph V) (D : Digraph I)
    (f : V → Option I) (b m d : ℕ) (ν τ ε ρ : ℝ)
    (hb : 0 < b) (hSize : ∀ i, (cluster f i).card = m)
    (hν : 0 ≤ ν) (hν₁ : ν ≤ 1) (hτ : 0 ≤ τ) (hτ₁ : τ ≤ 1/2)
    (hRob : IsRealRobust D ν τ)
    (hBudgetν : 8*((b-1:ℕ):ℝ) ≤ ν*(Fintype.card I:ℝ))
    (hBudgetτ : 4*((b-1:ℕ):ℝ) ≤ τ*(Fintype.card I:ℝ))
    (hDeg : ∀ x, d ≤ inDegree D x ∧ d ≤ outDegree D x)
    (hPairs : ∀ i j, D.Adj i j → IsUniform G ε (cluster f i) (cluster f j) ∧
      ρ ≤ density G (cluster f i) (cluster f j)) :
    ∃ (B : Finset I) (g : V → Option B),
      B.card = (Fintype.card I/b)*b ∧ b ∣ B.card ∧
      (∀ i : B, cluster g i = cluster f i.val) ∧
      (exceptional g).card = (exceptional f).card+m*(Fintype.card I%b) ∧
      IsRealRobust (induced D B) (ν/2) (2*τ) ∧
      (∀ x : B, d-Fintype.card I%b ≤ inDegree (induced D B) x ∧
        d-Fintype.card I%b ≤ outDegree (induced D B) x) ∧
      ∀ i j : B, (induced D B).Adj i j → IsUniform G ε (cluster g i) (cluster g j) ∧
        ρ ≤ density G (cluster g i) (cluster g j) := by
  have hR : IsRealRobust (induced D (univ : Finset I)) ν τ := by
    apply (induced_real_robust_iff ..).mpr
    intro S _ hLo hHi
    exact hRob S (by simpa only [card_univ] using hLo) (by simpa only [card_univ] using hHi)
  have hD (i : (univ : Finset I)) :
      d ≤ inDegree (induced D univ) i ∧ d ≤ outDegree (induced D univ) i := by
    rw [induced_inDegree,induced_outDegree,univ_inter,univ_inter,inProfile_card,outProfile_card]
    exact hDeg i.val
  obtain ⟨B,_,hCard,hDiv,hDrop,hRobB,hDegB⟩ := exists_divisible_induced_reduced_digraph
    D univ b d ν τ hb hν hν₁ hτ hτ₁ hR (by simpa only [card_univ] using hBudgetν)
    (by simpa only [card_univ] using hBudgetτ) hD
  rw [card_univ] at hCard hDegB
  let g (v : V) : Option B := match f v with
    | none => none
    | some i => if hi : i ∈ B then some ⟨i,hi⟩ else none
  have hCell (i : B) : cluster g i = cluster f i.val := by
    ext v
    simp only [mem_cluster]
    cases hv : f v with
    | none => simp [g,hv]
    | some j =>
      by_cases hj : j ∈ B
      · simp [g,hv,hj,Subtype.ext_iff]
      · have hji : j ≠ i.val := fun h => hj (h.symm ▸ i.prop)
        simp [g,hv,hj,hji]
  have hExc : (exceptional g).card = (exceptional f).card+m*(Fintype.card I%b) := by
    have hOld := order_eq f m hSize
    have hNew := order_eq g m (fun i => (congrArg card (hCell i)).trans (hSize i.val))
    rw [Fintype.card_coe] at hNew
    have hCount := card_sdiff_add_card_eq_card (subset_univ B)
    rw [hDrop,card_univ] at hCount
    rw [←hCount,Nat.mul_add] at hOld
    omega
  refine ⟨B,g,hCard,hDiv,hCell,hExc,hRobB,hDegB,?_⟩
  intro i j hij
  rw [hCell,hCell]
  exact hPairs i.val j.val hij

/-- Round both dimensions before the first refinement. Keep the
same reduced graph on the surviving labels and account exactly
for the vertices lost in the two rounding operations. -/
theorem kuhn_osthus_coarse_partition_for_refinement (G : Digraph V) (D : Digraph I)
    (f : V → Option I) (b ℓ m d : ℕ) (ν τ ε ρ : ℝ)
    (hb : 0 < b) (hℓ : 0 < ℓ) (hRoom : 2*(ℓ-1) ≤ m) (hSize : ∀ i, (cluster f i).card = m)
    (hν : 0 ≤ ν) (hν₁ : ν ≤ 1) (hτ : 0 ≤ τ) (hτ₁ : τ ≤ 1/2)
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1/2)
    (hRob : IsRealRobust D ν τ)
    (hBudgetν : 8*((b-1:ℕ):ℝ) ≤ ν*(Fintype.card I:ℝ))
    (hBudgetτ : 4*((b-1:ℕ):ℝ) ≤ τ*(Fintype.card I:ℝ))
    (hDeg : ∀ x, d ≤ inDegree D x ∧ d ≤ outDegree D x)
    (hPairs : ∀ i j, D.Adj i j → IsUniform G ε (cluster f i) (cluster f j) ∧
      ρ+ε ≤ density G (cluster f i) (cluster f j)) :
    ∃ (B : Finset I) (g : V → Option B),
      B.card = (Fintype.card I/b)*b ∧ b ∣ B.card ∧
      (∀ i : B, cluster g i ⊆ cluster f i.val ∧ (cluster g i).card = ℓ*(m/ℓ)) ∧
      (exceptional g).card = (exceptional f).card+m*(Fintype.card I%b)+(m%ℓ)*B.card ∧
      IsRealRobust (induced D B) (ν/2) (2*τ) ∧
      (∀ x : B, d-Fintype.card I%b ≤ inDegree (induced D B) x ∧
        d-Fintype.card I%b ≤ outDegree (induced D B) x) ∧
      ∀ i j : B, (induced D B).Adj i j → IsUniform G (2*ε) (cluster g i) (cluster g j) ∧
        ρ ≤ density G (cluster g i) (cluster g j) := by
  obtain ⟨B,h,hB,hDiv,hCell,hExc,hRobB,hDegB,hPairsB⟩ :=
    exists_divisible_coarse_partition G D f b m d ν τ ε (ρ+ε)
      hb hSize hν hν₁ hτ hτ₁ hRob hBudgetν hBudgetτ hDeg hPairs
  have hSizeH (i : B) : (cluster h i).card = m := by rw [hCell,hSize]
  let a := (m/ℓ)*ℓ
  obtain ⟨g,hG,_,hVol,_⟩ := exists_divisible_cluster_trimming h (fun _ => ∅) m 0 ℓ hℓ
    (Nat.zero_le m) hSizeH (fun _ => by simp)
  simp only [sdiff_empty,Nat.sub_zero] at hG hVol
  have hEq : m%ℓ+a = m := by
    have hh := Nat.mod_add_div m ℓ
    simpa only [a,Nat.mul_comm ℓ (m/ℓ)] using hh
  have hHalf : m ≤ 2*a := by
    have hh : m%ℓ ≤ ℓ-1 := Nat.le_pred_of_lt (Nat.mod_lt m hℓ)
    omega
  have hSub (i : B) : cluster g i ⊆ cluster h i := (hG i).1
  have hSizeG (i : B) : (cluster g i).card = a := (hG i).2
  refine ⟨B,g,hB,hDiv,?_,?_,hRobB,hDegB,?_⟩
  · intro i
    exact ⟨hCell i ▸ hSub i,(hSizeG i).trans (Nat.mul_comm _ _)⟩
  · have hLoss : m-a = m%ℓ := by omega
    change (exceptional g).card = (exceptional f).card+m*(Fintype.card I%b)+(m%ℓ)*B.card
    rwa [hExc,show (m/ℓ)*ℓ = a by rfl,hLoss,Fintype.card_coe] at hVol
  · intro i j hij
    obtain ⟨hU,hρ⟩ := hPairsB i j hij
    have hh := regular_equal_fibres G h g a m (fun v => (hSizeH v).le) hSizeG hSub hHalf
      i j ε (ρ+ε) hε hε₁ hU hρ
    exact ⟨hh.1,by linarith only [hh.2]⟩

end OverfullWork.DirectedRobustExpansion
