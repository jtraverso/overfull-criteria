module

public import OverfullWork.OsthusStadenCoreExceptionBaseHalves
public import OverfullWork.OsthusStadenH1RedProfiles
public import OverfullWork.OsthusStadenCoreDegreeBudget

@[expose] public section


/-! Transfer the assigned pieces to the adapted red halves and sum (26). -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical

/-- Restrict an outgoing exceptional piece to the retained ordinary
half. Its first endpoint is already restricted by the assignment. -/
def retainCoreTargets {V : Type*} (D : Digraph V) (T : Finset V) : Digraph V :=
  ⟨fun x y => D.Adj x y ∧ y ∈ T⟩

theorem retainCoreTargets_outDegree {V : Type*} [Fintype V]
    (D : Digraph V) (B : Finset V) (x : V) :
    (outDegree (retainCoreTargets D B) x:ℝ) = profileCount B (outProfile D x) := by
  have h : (univ.filter ((retainCoreTargets D B).Adj x)) = B ∩ outProfile D x := by
    ext y
    simp only [mem_filter,mem_univ,true_and,mem_inter,outProfile]
    exact and_comm
  unfold outDegree profileCount
  rw [h]

/-- The one-sided loss from (26) on the actual piece. -/
theorem retainCoreTargets_outDegree_lower {V : Type*} [Fintype V]
    (D : Digraph V) (old new : Finset V) (x : V)
    (h : ∀ y, D.Adj x y → y ∈ old) :
    (outDegree D x:ℝ)-((old \ new).card:ℝ) ≤ (outDegree (retainCoreTargets D new) x:ℝ) := by
  have hSub : outProfile D x ⊆ old := fun _ hy => h _ (mem_filter.mp hy).2
  have hOld : profileCount old (outProfile D x) = (outDegree D x:ℝ) := by
    unfold profileCount
    rw [inter_eq_right.mpr hSub]
    rfl
  rw [retainCoreTargets_outDegree]
  have hLoss := exceptional_overlap_loss (outProfile D x) old new
  rw [hOld] at hLoss
  have hEq : (old ∩ new) ∩ outProfile D x = new ∩ outProfile D x := by
    rw [inter_comm old new,inter_assoc,inter_eq_right.mpr hSub]
  simpa only [profileCount,hEq] using hLoss

theorem UniformProfileCell.lower_with_small_profiles {V J : Type*}
    {profiles : J → Finset V} {P B : Finset V} {k : ℕ} {ε : ℝ}
    (h : UniformProfileCell profiles P B k ε) (j : J)
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    (1-ε)*(profileCount P (profiles j)-ε*(P.card:ℝ))/(k:ℝ) ≤ profileCount B (profiles j) := by
  by_cases hBig : ε*(P.card:ℝ) ≤ profileCount P (profiles j)
  · have hRaw := (abs_le.mp (h j hBig)).1
    calc
      _ ≤ (1-ε)*profileCount P (profiles j)/(k:ℝ) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [mul_nonneg hε (Nat.cast_nonneg P.card)])
          (sub_nonneg.mpr hε₁)) (Nat.cast_nonneg _)
      _ ≤ _ := by rw [mul_div_assoc]; linarith only [hRaw]
  · exact (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hε₁) (by linarith only [lt_of_not_ge hBig]))
      (Nat.cast_nonneg _)).trans (Nat.cast_nonneg _)

set_option maxHeartbeats 1200000 in
/-- Sum the supplied degree lower bounds on the retained pieces. The
ordinary endpoint occurs in at most one base half. -/
theorem core_exception_outgoing_with_retained_degrees
    {V I U : Type*} [Fintype V] [Fintype I]
    (G : Digraph V) (Z : Finset V) (parent : I → Finset V)
    (base retained : I → U → Finset V) (chosen : I → Finset U) (piece : I → U → Digraph V)
    (b M ℓ k : ℕ) (e splitting loss cap A : ℝ)
    (hℓ : 0 < ℓ) (hk : 0 < k) (he : 0 ≤ e) (he₁ : e ≤ 1) (hcap : 0 ≤ cap)
    (hParent : ∀ i, (parent i).card = M)
    (hCount : ∀ i, (chosen i).card = b)
    (hDis : ∀ u v : I × U, u ≠ v → Disjoint (base u.1 u.2) (base v.1 v.2))
    (hProfile : ∀ i z, z ∈ chosen i → UniformProfileCell (outProfile G) (parent i) (base i z) ℓ e)
    (hArcs : ∀ i z x y, z ∈ chosen i → (piece i z).Adj x y →
      G.Adj x y ∧ x ∈ Z ∧ y ∈ base i z)
    (hLower : ∀ i z, z ∈ chosen i → ∀ x ∈ Z,
      profileCount (base i z) (outProfile G x)/(k:ℝ)-(splitting+loss) ≤
        (outDegree (retainCoreTargets (piece i z) (retained i z)) x:ℝ))
    (hCap : ∀ i z, z ∈ chosen i → ∀ y ∈ base i z, (inDegree (piece i z) y:ℝ) ≤ cap)
    (hOrd : ∀ x ∈ Z, A-(Z.card:ℝ) ≤ ∑ i,profileCount (parent i) (outProfile G x)) :
    let J := (univ : Finset I).biUnion (fun i => (chosen i).map ⟨Prod.mk i,fun _ _ h => (Prod.mk.inj h).2⟩)
    let E := indexedArcUnion J (fun q => retainCoreTargets (piece q.1 q.2) (retained q.1 q.2))
    (∀ x y, E.Adj x y → ∃ i z, z ∈ chosen i ∧ (piece i z).Adj x y ∧ y ∈ retained i z) ∧
    (∀ x ∈ Z,
      (b:ℝ)*(1-e)*(A-(Z.card:ℝ)-e*((Fintype.card I:ℝ)*(M:ℝ)))/((ℓ:ℝ)*(k:ℝ))
        -(Fintype.card I:ℝ)*(b:ℝ)*(splitting+loss) ≤ (outDegree E x:ℝ)) ∧
    ∀ x, (inDegree E x:ℝ) ≤ cap := by
  let emb (i : I) : U ↪ I × U := ⟨Prod.mk i,fun _ _ h => (Prod.mk.inj h).2⟩
  let J := (univ : Finset I).biUnion (fun i => (chosen i).map (emb i))
  let R (q : I × U) := retainCoreTargets (piece q.1 q.2) (retained q.1 q.2)
  let E := indexedArcUnion J R
  have hJ (q : I × U) : q ∈ J ↔ q.2 ∈ chosen q.1 := by
    constructor
    · intro h
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp h
      obtain ⟨z,hz,rfl⟩ := mem_map.mp hi
      exact hz
    · intro h
      exact mem_biUnion.mpr ⟨q.1,mem_univ _,mem_map.mpr ⟨q.2,h,rfl⟩⟩
  have hPair (u : I × U) (hu : u ∈ J) (v : I × U) (hv : v ∈ J) (hne : u ≠ v) :
      Disjoint (R u) (R v) := by
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hx,hy⟩
    exact disjoint_left.mp (hDis u v hne) (hArcs _ _ _ _ ((hJ u).mp hu) hx.1).2.2
      (hArcs _ _ _ _ ((hJ v).mp hv) hy.1).2.2
  have hSum (g : I × U → ℝ) : ∑ q ∈ J,g q = ∑ i,∑ z ∈ chosen i,g (i,z) := by
    unfold J
    rw [sum_biUnion]
    · apply sum_congr rfl
      intro i _
      rw [sum_map]
      rfl
    · intro i _ j _ hij
      apply disjoint_left.mpr
      intro q hq hr
      obtain ⟨x,_,rfl⟩ := mem_map.mp hq
      obtain ⟨y,_,he⟩ := mem_map.mp hr
      exact hij (congrArg Prod.fst he.symm)
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hℓR : (0:ℝ) < ℓ := by exact_mod_cast hℓ
  refine ⟨?_,?_,?_⟩
  · rintro x y ⟨q,hq,h⟩
    exact ⟨q.1,q.2,(hJ _).mp hq,h.1,h.2⟩
  · intro x hx
    have hPiece (i : I) (z : U) (hz : z ∈ chosen i) :
        (1-e)*(profileCount (parent i) (outProfile G x)-e*(M:ℝ))/((ℓ:ℝ)*(k:ℝ))
          -(splitting+loss) ≤ (outDegree (R (i,z)) x:ℝ) := by
      have hRef := (hProfile i z hz).lower_with_small_profiles x he he₁
      rw [hParent i] at hRef
      have hRef' := div_le_div_of_nonneg_right hRef hkR.le
      have hBase := hLower i z hz x hx
      change _ ≤ (outDegree (R (i,z)) x:ℝ) at hBase
      rw [div_div] at hRef'
      linarith only [hRef',hBase]
    have hLocal (i : I) :
        (b:ℝ)*((1-e)*(profileCount (parent i) (outProfile G x)-e*(M:ℝ))/((ℓ:ℝ)*(k:ℝ))
          -(splitting+loss)) ≤ ∑ z ∈ chosen i,(outDegree (R (i,z)) x:ℝ) := by
      simpa only [sum_const,nsmul_eq_mul,hCount] using sum_le_sum (fun z hz => hPiece i z hz)
    have hBound := sum_le_sum (s := (univ : Finset I)) (fun i _ => hLocal i)
    have hTel (i : I) : (b:ℝ)*((1-e)*(profileCount (parent i) (outProfile G x)-e*(M:ℝ))/((ℓ:ℝ)*(k:ℝ))
        -(splitting+loss)) =
      ((b:ℝ)*(1-e)/((ℓ:ℝ)*(k:ℝ)))*profileCount (parent i) (outProfile G x) -
        (((b:ℝ)*(1-e)/((ℓ:ℝ)*(k:ℝ)))*(e*(M:ℝ))+(b:ℝ)*(splitting+loss)) := by ring
    simp only [hTel,sum_sub_distrib,←mul_sum,sum_const,card_univ,nsmul_eq_mul] at hBound
    have hPay := mul_le_mul_of_nonneg_left (hOrd x hx)
      (show 0 ≤ (b:ℝ)*(1-e)/((ℓ:ℝ)*(k:ℝ)) from
        div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr he₁)) (mul_nonneg hℓR.le hkR.le))
    change _ ≤ (outDegree E x:ℝ)
    rw [(indexedArcUnion_semidegrees J R hPair x).1,Nat.cast_sum,hSum]
    have hEq :
        (b:ℝ)*(1-e)*(A-(Z.card:ℝ)-e*((Fintype.card I:ℝ)*(M:ℝ)))/((ℓ:ℝ)*(k:ℝ))
          -(Fintype.card I:ℝ)*(b:ℝ)*(splitting+loss) =
        (b:ℝ)*(1-e)/((ℓ:ℝ)*(k:ℝ))*(A-(Z.card:ℝ)) -
          (Fintype.card I:ℝ)*((b:ℝ)*(1-e)/((ℓ:ℝ)*(k:ℝ))*(e*(M:ℝ))+(b:ℝ)*(splitting+loss)) := by ring
    rw [hEq]
    exact (sub_le_sub_right hPay _).trans hBound
  · intro y
    have hOff (q : I × U) (hq : q ∈ J) (hy : y ∉ base q.1 q.2) : inDegree (R q) y = 0 := by
      unfold inDegree inNeighbours
      apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro x _ h
      exact hy (hArcs _ _ _ _ ((hJ q).mp hq) h.1).2.2
    change (inDegree E y:ℝ) ≤ cap
    rw [(indexedArcUnion_semidegrees J R hPair y).2,Nat.cast_sum]
    by_cases hSome : ∃ q ∈ J,y ∈ base q.1 q.2
    · obtain ⟨q,hq,hy⟩ := hSome
      rw [sum_eq_single q (fun v hv hne => by
        rw [hOff v hv (fun h => disjoint_left.mp (hDis v q hne) h hy)]
        norm_num) (fun h => (h hq).elim)]
      have hLe : inDegree (R q) y ≤ inDegree (piece q.1 q.2) y := by
        unfold inDegree inNeighbours
        apply card_le_card
        intro x hx
        have he : (R q).Adj x y := (mem_filter.mp hx).2
        exact mem_filter.mpr ⟨mem_univ _,he.1⟩
      exact (show (inDegree (R q) y:ℝ) ≤ (inDegree (piece q.1 q.2) y:ℝ) by exact_mod_cast hLe).trans
        (hCap _ _ ((hJ q).mp hq) y hy)
    · rw [sum_eq_zero (fun q hq => by rw [hOff q hq (fun h => hSome ⟨q,hq,h⟩)]; norm_num)]
      exact hcap

set_option maxHeartbeats 1200000 in
/-- On one layer and one direction, sum the clipped pieces. The lower
bound charges one splitting error and one clipping error per request,
while the ordinary endpoint occurs in at most one base half. -/
theorem core_exception_outgoing_after_trim
    {V I U : Type*} [Fintype V] [Fintype I]
    (G : Digraph V) (Z : Finset V) (parent : I → Finset V)
    (base retained : I → U → Finset V) (chosen : I → Finset U) (piece : I → U → Digraph V)
    (b M ℓ k : ℕ) (e splitting loss cap A : ℝ)
    (hℓ : 0 < ℓ) (hk : 0 < k) (he : 0 ≤ e) (he₁ : e ≤ 1) (hcap : 0 ≤ cap)
    (hParent : ∀ i, (parent i).card = M)
    (hCount : ∀ i, (chosen i).card = b)
    (hDis : ∀ u v : I × U, u ≠ v → Disjoint (base u.1 u.2) (base v.1 v.2))
    (hProfile : ∀ i z, z ∈ chosen i → UniformProfileCell (outProfile G) (parent i) (base i z) ℓ e)
    (hLoss : ∀ i z, z ∈ chosen i → (((base i z) \ retained i z).card:ℝ) ≤ loss)
    (hArcs : ∀ i z x y, z ∈ chosen i → (piece i z).Adj x y →
      G.Adj x y ∧ x ∈ Z ∧ y ∈ base i z)
    (hLower : ∀ i z, z ∈ chosen i → ∀ x ∈ Z,
      profileCount (base i z) (outProfile G x)/(k:ℝ)-splitting ≤ (outDegree (piece i z) x:ℝ))
    (hCap : ∀ i z, z ∈ chosen i → ∀ y ∈ base i z, (inDegree (piece i z) y:ℝ) ≤ cap)
    (hOrd : ∀ x ∈ Z, A-(Z.card:ℝ) ≤ ∑ i,profileCount (parent i) (outProfile G x)) :
    let J := (univ : Finset I).biUnion (fun i => (chosen i).map ⟨Prod.mk i,fun _ _ h => (Prod.mk.inj h).2⟩)
    let E := indexedArcUnion J (fun q => retainCoreTargets (piece q.1 q.2) (retained q.1 q.2))
    (∀ x y, E.Adj x y → ∃ i z, z ∈ chosen i ∧ (piece i z).Adj x y ∧ y ∈ retained i z) ∧
    (∀ x ∈ Z,
      (b:ℝ)*(1-e)*(A-(Z.card:ℝ)-e*((Fintype.card I:ℝ)*(M:ℝ)))/((ℓ:ℝ)*(k:ℝ))
        -(Fintype.card I:ℝ)*(b:ℝ)*(splitting+loss) ≤ (outDegree E x:ℝ)) ∧
    ∀ x, (inDegree E x:ℝ) ≤ cap := by
  apply core_exception_outgoing_with_retained_degrees G Z parent base retained chosen piece b M ℓ k
    e splitting loss cap A hℓ hk he he₁ hcap hParent hCount hDis hProfile hArcs ?_ hCap hOrd
  intro i z hz x hx
  have hBase := hLower i z hz x hx
  have hTrim := retainCoreTargets_outDegree_lower (piece i z) (base i z) (retained i z) x
    (fun y h => (hArcs i z x y hz h).2.2)
  linarith only [hBase,hTrim,hLoss i z hz]

end OverfullWork.DirectedRobustExpansion
