module

public import OverfullWork.OsthusStadenPreparedSlices
public import Mathlib.Combinatorics.Hall.Finite

@[expose] public section


/-! The bridge-cell selection and intersection of useful vertex sets
in Osthus–Staden §5.5, Claims 5.1 and 5.2. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- Select bridge cells above the edges of a reduced Hamilton ordering.
The target in the next primary cluster is in-red, while the predecessor
of the source in its slice cycle is out-red. -/
theorem exists_bridge_cells {U W : Type*}
    (R : Digraph U) (project : W → U) (C σ : Equiv.Perm U) (F : Equiv.Perm W)
    (inRed outRed : Finset W)
    (hC : ∀ u, R.Adj u (C u)) (hProj : ∀ w, project (F w) = σ (project w))
    (hIn : ∀ u, ∃ w ∈ inRed, project w = u)
    (hOut : ∀ u, 1 < (outRed.filter (fun w => project w = u)).card) :
    ∃ A B : U → W,
      (∀ u, project (A u) = u ∧ project (B u) = C u) ∧
      (∀ u, R.Adj (project (A u)) (project (B u))) ∧
      (∀ u, F.symm (A u) ∈ outRed ∧ B u ∈ inRed) ∧
      Function.Injective A ∧ Function.Injective B ∧ (∀ u v, A u ≠ B v) := by
  choose incoming hMem hIncoming using hIn
  have hA (u : U) : ∃ w ∈ outRed, project w = σ.symm u ∧ F w ≠ incoming u := by
    obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (hOut (σ.symm u))
    rw [mem_filter] at ha hb
    by_cases h : F a = incoming u
    · exact ⟨b,hb.1,hb.2,fun hb' => hab (F.injective (h.trans hb'.symm))⟩
    · exact ⟨a,ha.1,ha.2,h⟩
  choose predecessor hPred hPredProj hDifferent using hA
  let A := fun u => F (predecessor u)
  let B := fun u => incoming (C u)
  have hProjectA (u : U) : project (A u) = u := by
    rw [hProj,hPredProj,Equiv.apply_symm_apply]
  have hProjectB (u : U) : project (B u) = C u := hIncoming (C u)
  refine ⟨A,B,fun u => ⟨hProjectA u,hProjectB u⟩,?_,?_,?_,?_,?_⟩
  · intro u
    rw [hProjectA,hProjectB]
    exact hC u
  · intro u
    simp only [A,Equiv.symm_apply_apply]
    exact ⟨hPred u,hMem (C u)⟩
  · intro u v h
    exact (hProjectA u).symm.trans ((congrArg project h).trans (hProjectA v))
  · intro u v h
    apply C.injective
    exact (hProjectB u).symm.trans ((congrArg project h).trans (hProjectB v))
  · intro u v h
    have he := (hProjectA u).symm.trans ((congrArg project h).trans (hProjectB v))
    exact hDifferent u (h.trans (congrArg incoming he.symm))

/-- The two three-quarter estimates in Claim 5.2 yield at least half
of the source cell as useful bridge vertices. -/
theorem useful_bridge_count {V : Type*} (A : Finset V) (P Q : V → Prop)
    (hP : 3*A.card ≤ 4*(A.filter P).card)
    (hQ : 3*A.card ≤ 4*(A.filter Q).card) :
    A.card ≤ 2*(A.filter (fun x => P x ∧ Q x)).card := by
  have hInter : (A.filter P) ∩ (A.filter Q) = A.filter (fun x => P x ∧ Q x) := by
    ext x
    simp only [mem_inter,mem_filter]
    tauto
  have hUnion : (A.filter P) ∪ (A.filter Q) ⊆ A :=
    union_subset (filter_subset _ _) (filter_subset _ _)
  have hMax := card_le_card hUnion
  have hSum := card_union_add_card_inter (A.filter P) (A.filter Q)
  rw [hInter] at hSum
  omega

/-- When different slices use slightly different physical cells, assign
distinct vertices inside the corresponding base cells. The capacity is
checked per base cell, across all slices. -/
theorem exists_distinct_aligned_vertices {I J V : Type*} [Fintype I]
    (base : J → Finset V) (tag : I → J) (candidate : I → Finset V)
    (hDis : ∀ j k, j ≠ k → Disjoint (base j) (base k))
    (hCapacity : ∀ i, ((univ : Finset I).filter (fun q => tag q = tag i)).card ≤
      (candidate i ∩ base (tag i)).card) :
    ∃ choice : I → V, Function.Injective choice ∧
      ∀ i, choice i ∈ candidate i ∧ choice i ∈ base (tag i) := by
  classical
  let requests (j : J) := (univ : Finset I).filter (fun q => tag q = j)
  have hLocal (j : J) : ∃ f : requests j → V, Function.Injective f ∧
      ∀ i : requests j, f i ∈ candidate i ∩ base j := by
    apply (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun i : requests j => candidate i ∩ base j)).mp
    intro S
    by_cases hS : S.Nonempty
    · obtain ⟨i,hi⟩ := hS
      have hTag : tag i = j := (mem_filter.mp i.property).2
      have hCap := hCapacity i
      change (requests (tag i)).card ≤ _ at hCap
      rw [hTag] at hCap
      have hCover : candidate i ∩ base j ⊆ S.biUnion (fun q => candidate q ∩ base j) :=
        fun _ hv => mem_biUnion.mpr ⟨i,hi,hv⟩
      exact ((card_le_univ S).trans (by rw [Fintype.card_coe]; exact hCap)).trans
        (card_le_card hCover)
    · simp [not_nonempty_iff_eq_empty.mp hS]
  choose f hInject hMem using hLocal
  let chooseIn (i : I) : requests (tag i) := ⟨i,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
  let g := fun i => f (tag i) (chooseIn i)
  have hOK (i : I) : g i ∈ candidate i ∧ g i ∈ base (tag i) :=
    mem_inter.mp (hMem _ (chooseIn i))
  refine ⟨g,?_,hOK⟩
  intro i i' h
  have hTag : tag i = tag i' := by
    by_contra hn
    exact disjoint_left.mp (hDis _ _ hn) (hOK i).2 (h ▸ (hOK i').2)
  have hChoice (j : J) (q : I) (hq : tag q = j) :
      f j ⟨q,mem_filter.mpr ⟨mem_univ _,hq⟩⟩ = g q := by
    subst j
    rfl
  have he : f (tag i) ⟨i,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩ =
      f (tag i) ⟨i',mem_filter.mpr ⟨mem_univ _,hTag.symm⟩⟩ := by
    rw [hChoice (tag i) i rfl,hChoice (tag i) i' hTag.symm]
    exact h
  exact congrArg Subtype.val (hInject (tag i) he)

private theorem refined_profile_lower {V J : Type*} {profiles : J → Finset V}
    {P A : Finset V} {k : ℕ} {ε a : ℝ} (j : J)
    (hSplit : UniformProfileCell profiles P A k ε) (hSize : P.card = k*A.card)
    (hk : 0 < k) (hε1 : ε ≤ 1) (hThreshold : ε ≤ a)
    (hDegree : a*(P.card : ℝ) ≤ profileCount P (profiles j)) :
    (1-ε)*a*(A.card : ℝ) ≤ profileCount A (profiles j) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hP : (P.card : ℝ) = (k : ℝ)*A.card := by exact_mod_cast hSize
  have hLarge := (mul_le_mul_of_nonneg_right hThreshold (Nat.cast_nonneg P.card)).trans hDegree
  have h := (abs_le.mp (hSplit j hLarge)).1
  have hDiv : a*(A.card : ℝ) ≤ profileCount P (profiles j)/(k : ℝ) := by
    apply (le_div_iff₀ hkR).mpr
    rw [hP] at hDegree
    nlinarith only [hDegree]
  have hLower := mul_le_mul_of_nonneg_left hDiv (sub_nonneg.mpr hε1)
  nlinarith only [h,hLower]

/-- A quantitative form of Claim 5.2. The H0 estimates in the parent
clusters propagate to the two red halves and yield the useful vertices. -/
theorem useful_bridge_vertices_of_refinements {V : Type*} [Fintype V]
    (HIn HOut : Digraph V) (source parentIn parentOut halfIn halfOut badIn badOut : Finset V)
    (k : ℕ) (ε a κ : ℝ)
    (hk : 0 < k) (hε1 : ε ≤ 1) (hThreshold : ε ≤ a)
    (hInSize : parentIn.card = k*halfIn.card) (hOutSize : parentOut.card = k*halfOut.card)
    (hInRef : UniformProfileCell (inProfile HIn) parentIn halfIn k ε)
    (hOutRef : UniformProfileCell (outProfile HOut) parentOut halfOut k ε)
    (hBadIn : 4*badIn.card ≤ source.card) (hBadOut : 4*badOut.card ≤ source.card)
    (hIn : ∀ x ∈ source, x ∉ badIn → a*(parentIn.card : ℝ) ≤ profileCount parentIn (inProfile HIn x))
    (hOut : ∀ x ∈ source, x ∉ badOut → a*(parentOut.card : ℝ) ≤ profileCount parentOut (outProfile HOut x))
    (hInBudget : κ < (1-ε)*a*(halfIn.card : ℝ))
    (hOutBudget : κ < (1-ε)*a*(halfOut.card : ℝ)) :
    source.card ≤ 2*(source.filter (fun x =>
      κ < profileCount halfIn (inProfile HIn x) ∧ κ < profileCount halfOut (outProfile HOut x))).card := by
  apply useful_bridge_count
  · have hSub : source \ badIn ⊆ source.filter (fun x => κ < profileCount halfIn (inProfile HIn x)) := by
      intro x hx
      obtain ⟨hx,hx'⟩ := mem_sdiff.mp hx
      exact mem_filter.mpr ⟨hx,hInBudget.trans_le
        (refined_profile_lower x hInRef hInSize hk hε1 hThreshold (hIn x hx hx'))⟩
    have hKeep := le_card_sdiff badIn source
    have hCard := card_le_card hSub
    omega
  · have hSub : source \ badOut ⊆ source.filter (fun x => κ < profileCount halfOut (outProfile HOut x)) := by
      intro x hx
      obtain ⟨hx,hx'⟩ := mem_sdiff.mp hx
      exact mem_filter.mpr ⟨hx,hOutBudget.trans_le
        (refined_profile_lower x hOutRef hOutSize hk hε1 hThreshold (hOut x hx hx'))⟩
    have hKeep := le_card_sdiff badOut source
    have hCard := card_le_card hSub
    omega

end OverfullWork.DirectedRobustExpansion
