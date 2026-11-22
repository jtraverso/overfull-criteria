module

public import OverfullWork.OsthusStadenCoreException
public import OverfullWork.OsthusStadenH1Assembly

@[expose] public section


/-! Transfer (H1) to red neighbours after cutting the reserves to a base
half-cell phase, as in (H1′) of Osthus–Staden §5.7. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical

private theorem profileCount_mono {V : Type*} {A B : Finset V} (Q : Finset V) (h : A ⊆ B) :
    profileCount A Q ≤ profileCount B Q := by
  unfold profileCount
  exact_mod_cast card_le_card (inter_subset_inter h (subset_refl Q))

theorem profile_count_disjoint_union {I V : Type*} (J : Finset I)
    (A : I → Finset V) (Q : Finset V)
    (hDis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (A i) (A j)) :
    profileCount (J.biUnion A) Q = ∑ i ∈ J,profileCount (A i) Q := by
  have h : J.biUnion A ∩ Q = J.biUnion (fun i => A i ∩ Q) := by
    ext x
    simp only [mem_biUnion,mem_inter]
    constructor
    · rintro ⟨⟨i,hi,hxi⟩,hq⟩
      exact ⟨i,hi,hxi,hq⟩
    · rintro ⟨i,hi,hxi,hq⟩
      exact ⟨⟨i,hi,hxi⟩,hq⟩
  unfold profileCount
  rw [h,card_biUnion (fun i hi j hj hij =>
    (hDis i hi j hj hij).mono inter_subset_left inter_subset_left),Nat.cast_sum]

/-- Bounds for a base half-cell after intersecting with its adapted
version. The additive error covers profiles below the (URef) threshold. -/
theorem clipped_profile_bounds {V : Type*} (P A B Q : Finset V) (k : ℕ) (ε L : ℝ)
    (hA : A ⊆ P) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hL : 0 ≤ L)
    (hLoss : ((A \ B).card : ℝ) ≤ L)
    (hRef : UniformProfileCell (fun _ : Unit => Q) P A k ε) :
    (1-ε)*(profileCount P Q/(k:ℝ)) -
        ((1-ε)*(ε*(P.card:ℝ)/(k:ℝ))+L) ≤ profileCount (A ∩ B) Q ∧
      profileCount (A ∩ B) Q ≤ (1+ε)*(profileCount P Q/(k:ℝ))+ε*(P.card:ℝ) := by
  let q := profileCount P Q
  let a := profileCount A Q
  let v := profileCount (A ∩ B) Q
  have hClip : a-L ≤ v := by
    have h := exceptional_overlap_loss Q A B
    linarith only [h,hLoss]
  have hMono : v ≤ a := profileCount_mono Q inter_subset_left
  have hQ : 0 ≤ q := Nat.cast_nonneg _
  have hV : 0 ≤ v := Nat.cast_nonneg _
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  by_cases hLarge : ε*(P.card:ℝ) ≤ q
  · have h := abs_le.mp (hRef () hLarge)
    change - (ε*(q/(k:ℝ))) ≤ a-q/(k:ℝ) ∧ a-q/(k:ℝ) ≤ ε*(q/(k:ℝ)) at h
    have hErr := mul_nonneg (sub_nonneg.mpr hε1) (div_nonneg (mul_nonneg hε (Nat.cast_nonneg P.card)) hk)
    have hErr' := mul_nonneg hε (Nat.cast_nonneg P.card : (0:ℝ) ≤ _)
    constructor <;> linarith only [h.1,h.2,hClip,hMono,hErr,hErr']
  · have hSmall : q ≤ ε*(P.card:ℝ) := le_of_not_ge hLarge
    have hUpper : v ≤ q := hMono.trans (profileCount_mono Q hA)
    have hAdd := mul_nonneg (by linarith only [hε] : 0 ≤ 1+ε) (div_nonneg hQ hk)
    have hLow := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hSmall hk) (sub_nonneg.mpr hε1)
    constructor <;> linarith only [hV,hUpper,hSmall,hAdd,hLow,hL]

/-- Quantitative (H1′) for a single neighbourhood profile. Incoming
and outgoing reserves use the same argument with opposite profiles.
The budgets sum the losses from the retained halves and the small
parent profiles. -/
theorem h1_red_profile_of_aligned_halves {U I V : Type*} [Fintype U]
    (parent : U → Finset V) (base adapted : U → I → Finset V) (selected : U → Finset I)
    (Q : Finset V) (m k b p : ℕ) (ε loss g : ℝ)
    (hp : 0 < p) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hLoss : 0 ≤ loss)
    (hParent : ∀ u, (parent u).card = m)
    (hParentDis : ∀ u v, u ≠ v → Disjoint (parent u) (parent v))
    (hSelect : ∀ u, (selected u).card = b)
    (hBase : ∀ u i, i ∈ selected u → base u i ⊆ parent u)
    (hBaseDis : ∀ u i j, i ≠ j → Disjoint (base u i) (base u j))
    (hNear : ∀ u i, i ∈ selected u → (((base u i) \ (adapted u i)).card:ℝ) ≤ loss)
    (hRef : ∀ u i, i ∈ selected u → UniformProfileCell (fun _ : Unit => Q) (parent u) (base u i) k ε)
    (hSupport : Q ⊆ (univ : Finset U).biUnion parent)
    (hDegree : g/3 ≤ (Q.card:ℝ) ∧ (Q.card:ℝ) ≤ 2*g)
    (hLo : 1/(6*(p:ℝ)) ≤ (b:ℝ)*(1-ε)/(k:ℝ))
    (hHi : (b:ℝ)*(1+ε)/(k:ℝ) ≤ 1/(3*(p:ℝ)))
    (hErrLo : (Fintype.card U:ℝ)*(b:ℝ)*((1-ε)*(ε*(m:ℝ)/(k:ℝ))+loss) ≤ g/(180*(p:ℝ)))
    (hErrHi : (Fintype.card U:ℝ)*(b:ℝ)*ε*(m:ℝ) ≤ g/(3*(p:ℝ))) :
    let A := univ.biUnion (fun u => (selected u).biUnion (fun i => base u i ∩ adapted u i))
    g/(20*(p:ℝ)) ≤ profileCount A Q ∧ profileCount A Q ≤ g/(p:ℝ) := by
  let B (u : U) := (selected u).biUnion (fun i => base u i ∩ adapted u i)
  let q (u : U) := profileCount (parent u) Q
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hB (u : U) : B u ⊆ parent u := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hx
    exact hBase u i hi (mem_inter.mp hx).1
  have hBSum (u : U) : profileCount (B u) Q =
      ∑ i ∈ selected u,profileCount (base u i ∩ adapted u i) Q :=
    profile_count_disjoint_union _ _ _ (fun i _ j _ h =>
      (hBaseDis u i j h).mono inter_subset_left inter_subset_left)
  have hTot : (∑ u,q u) = (Q.card:ℝ) := by
    rw [← profile_count_disjoint_union univ parent Q (fun u _ v _ h => hParentDis u v h)]
    unfold profileCount
    rw [inter_eq_right.mpr hSupport]
  have hUnion : profileCount (univ.biUnion B) Q = ∑ u,profileCount (B u) Q :=
    profile_count_disjoint_union _ _ _ (fun u _ v _ h => (hParentDis u v h).mono (hB u) (hB v))
  let err := (1-ε)*(ε*(m:ℝ)/(k:ℝ))+loss
  have hLocal (u : U) :
      (b:ℝ)*((1-ε)*(q u/(k:ℝ))-err) ≤ profileCount (B u) Q ∧
      profileCount (B u) Q ≤ (b:ℝ)*((1+ε)*(q u/(k:ℝ))+ε*(m:ℝ)) := by
    have hL (i : I) (hi : i ∈ selected u) :=
      clipped_profile_bounds (parent u) (base u i) (adapted u i) Q k ε loss
        (hBase u i hi) hε hε1 hLoss (hNear u i hi) (hRef u i hi)
    have hLow := sum_le_sum (s := selected u) fun i hi => (hL i hi).1
    have hHigh := sum_le_sum (s := selected u) fun i hi => (hL i hi).2
    rw [hBSum]
    exact ⟨by simpa only [hParent,q,err,sum_const,hSelect,nsmul_eq_mul] using hLow,
      by simpa only [hParent,q,sum_const,hSelect,nsmul_eq_mul] using hHigh⟩
  have hLower := sum_le_sum (s := (univ : Finset U)) fun u _ => (hLocal u).1
  have hUpper := sum_le_sum (s := (univ : Finset U)) fun u _ => (hLocal u).2
  have hLowEq (u : U) : (b:ℝ)*((1-ε)*(q u/(k:ℝ))-err) =
      ((b:ℝ)*(1-ε)/(k:ℝ))*q u-(b:ℝ)*err := by ring
  have hHighEq (u : U) : (b:ℝ)*((1+ε)*(q u/(k:ℝ))+ε*(m:ℝ)) =
      ((b:ℝ)*(1+ε)/(k:ℝ))*q u+(b:ℝ)*ε*(m:ℝ) := by ring
  simp only [hLowEq,sum_sub_distrib,←mul_sum,hTot,sum_const,card_univ,nsmul_eq_mul] at hLower
  simp only [hHighEq,sum_add_distrib,←mul_sum,hTot,sum_const,card_univ,nsmul_eq_mul] at hUpper
  change g/(20*(p:ℝ)) ≤ profileCount (univ.biUnion B) Q ∧
    profileCount (univ.biUnion B) Q ≤ g/(p:ℝ)
  rw [hUnion]
  have hL := mul_le_mul_of_nonneg_right hLo (Nat.cast_nonneg Q.card)
  have hH := mul_le_mul_of_nonneg_right hHi (Nat.cast_nonneg Q.card)
  have hG1 := mul_le_mul_of_nonneg_left hDegree.1 (by positivity : 0 ≤ 1/(6*(p:ℝ)))
  have hG2 := mul_le_mul_of_nonneg_left hDegree.2 (by positivity : 0 ≤ 1/(3*(p:ℝ)))
  change (Fintype.card U:ℝ)*(b:ℝ)*err ≤ _ at hErrLo
  have hR1 : (1/(6*(p:ℝ)))*(g/3)-g/(180*(p:ℝ)) = g/(20*(p:ℝ)) := by ring
  have hR2 : (1/(3*(p:ℝ)))*(2*g)+g/(3*(p:ℝ)) = g/(p:ℝ) := by ring
  exact ⟨by nlinarith only [hL,hG1,hLower,hErrLo,hR1],
    by nlinarith only [hH,hG2,hUpper,hErrHi,hR2]⟩

/-- Physical H1 arcs have both endpoints in the retained primary
cells. Consequently its neighbourhood profiles have exactly the
support and cardinality required by the red-half estimate. -/
theorem reserve_profile_on_retained_cells {U I V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    (a : U → W ↪ V) (source target : I → U) (D : I → Digraph W)
    (s : Bool) (x : V) :
    let H := directedPairUnion (a ∘ source) (a ∘ target) D
    let Q := if s then outProfile H x else inProfile H x
    Q ⊆ univ.biUnion (fun u => (univ : Finset W).map (a u)) ∧
      Q.card = pairSemidegree s H x := by
  cases s
  · refine ⟨?_,rfl⟩
    intro y hy
    change y ∈ inProfile (directedPairUnion (a ∘ source) (a ∘ target) D) x at hy
    obtain ⟨i,v,_,hy,_,_⟩ := (mem_filter.mp hy).2
    exact mem_biUnion.mpr ⟨source i,mem_univ _,mem_map.mpr ⟨v,mem_univ _,hy⟩⟩
  · refine ⟨?_,rfl⟩
    intro y hy
    change y ∈ outProfile (directedPairUnion (a ∘ source) (a ∘ target) D) x at hy
    obtain ⟨i,_,w,_,hy,_⟩ := (mem_filter.mp hy).2
    exact mem_biUnion.mpr ⟨target i,mem_univ _,mem_map.mpr ⟨w,mem_univ _,hy⟩⟩

end OverfullWork.DirectedRobustExpansion
