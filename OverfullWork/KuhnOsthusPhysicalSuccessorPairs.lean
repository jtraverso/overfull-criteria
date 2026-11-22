module

public import OverfullWork.KuhnOsthusBalancedChordExtension
public import OverfullWork.KuhnOsthusSuccessorMerge
public import OverfullWork.DenseHall

@[expose] public section


/-! The successor-pair hypotheses can be checked on physical vertex
sets before any perfect matching or cycle is chosen. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

/-- The factor identifies the free sources with the free targets of
the successor cluster, which need not have the same vertex labels. -/
noncomputable def freeSuccessorEquiv {I : Type*} (D R : Digraph V)
    (cluster : V → I) (s : Equiv.Perm I) (σ : Equiv.Perm V)
    (hKeep : ∀ x y, D.Adj x y → σ x = y)
    (hNew : ∀ x, (∃ y, D.Adj x y) ∨ (R.Adj x (σ x) ∧ cluster (σ x) = s (cluster x)))
    (i : I) : freeOut D cluster i ≃ freeIn D cluster (s i) where
  toFun a := ⟨σ a,by
    have ha := mem_freeOut.mp a.prop
    have hn := (hNew a).resolve_left ha.2
    apply mem_freeIn.mpr
    refine ⟨hn.2.trans (congrArg s ha.1),?_⟩
    rintro ⟨w,hw⟩
    have he := σ.injective (hKeep w (σ a) hw)
    exact ha.2 ⟨σ a,he ▸ hw⟩⟩
  invFun b := ⟨σ.symm b,successor_target_is_free_source D R cluster s σ hKeep hNew i b.prop⟩
  left_inv a := Subtype.ext (σ.symm_apply_apply a)
  right_inv b := Subtype.ext (σ.apply_symm_apply b)

private theorem reserve_incidence_image (R : Digraph V) (σ : Equiv.Perm V)
    (S : Finset V) (X Y : Finset S) :
    incidences (successorReserve R σ S) X Y =
      incidences R (X.image fun x => x.val) (Y.image fun y : S => σ y) := by
  rw [←Nat.cast_inj (R := ℝ),incidences_eq_sum,incidences_eq_sum]
  have hinj : Function.Injective (fun y : S => σ y) := σ.injective.comp Subtype.coe_injective
  rw [sum_image hinj.injOn]
  apply sum_congr rfl
  intro y _
  rw [sum_image Subtype.coe_injective.injOn]
  rfl

private theorem reserve_indegree_physical (R : Digraph V) (σ : Equiv.Perm V)
    (S : Finset V) (y : S) :
    inDegree (successorReserve R σ S) y = inNeighbours R S (σ y) := by
  have h := reserve_incidence_image R σ S univ {y}
  rw [incidences_degree, image_singleton] at h
  have he : ((univ : Finset S).image fun x => x.val) = S := by simp
  rw [he,incidences,sum_singleton] at h
  exact h

omit [Fintype V] in
private theorem outgoing_incidence_singleton
    (G : Digraph V) (a : V) (B : Finset V) :
    incidences G {a} B = (B.filter (G.Adj a)).card := by
  simp only [incidences,inNeighbours,card_filter,sum_singleton]

private theorem reserve_outdegree_physical (R : Digraph V) (σ : Equiv.Perm V)
    (S T : Finset V) (f : S ≃ T) (hf : ∀ x : S, (f x).val = σ x) (x : S) :
    outDegree (successorReserve R σ S) x = (T.filter (R.Adj x)).card := by
  have h := reserve_incidence_image R σ S {x} univ
  rw [outgoing_incidence_singleton,image_singleton,outgoing_incidence_singleton] at h
  have he : ((univ : Finset S).image fun y : S => σ y) = T := by
    ext v
    constructor
    · rintro hv
      obtain ⟨y,_,rfl⟩ := mem_image.mp hv
      rw [←hf]
      exact (f y).prop
    · intro hv
      exact mem_image.mpr ⟨f.symm ⟨v,hv⟩,mem_univ _,by
        rw [←hf,f.apply_symm_apply]⟩
  rw [he] at h
  exact h

/-- Hall's rectangle test in terms of incidences of the physical
digraph on two finite sides. -/
theorem exists_matching_on_of_rectangle_threshold (R : Digraph V) (S T : Finset V)
    (r : ℕ) (hSize : S.card = T.card)
    (hOut : ∀ x ∈ S, r ≤ (T.filter (R.Adj x)).card)
    (hIn : ∀ y ∈ T, r ≤ inNeighbours R S y)
    (hRect : ∀ X ⊆ S, ∀ Y ⊆ T, r ≤ X.card → r ≤ Y.card → 0 < incidences R X Y) :
    ∃ f : S ≃ T, ∀ x : S, R.Adj x (f x) := by
  classical
  apply exists_matching_of_rectangle_threshold (fun x : S => fun y : T => R.Adj x y) r
  · simpa only [Fintype.card_coe] using hSize
  · intro x
    rw [DenseHall.subtype_filter_card]
    exact hOut x x.prop
  · intro y
    rw [DenseHall.subtype_filter_card (S) (fun v => R.Adj v y)]
    exact hIn y y.prop
  · intro X Y hx hy
    let A := X.image (fun x : S => x.val)
    let B := Y.image (fun y : T => y.val)
    have hSub {U : Finset V} (L : Finset U) : (L.image fun x => x.val) ⊆ U := by
      intro v hv
      obtain ⟨x,_,rfl⟩ := mem_image.mp hv
      exact x.prop
    have hA : A.card = X.card := card_image_of_injective _ Subtype.coe_injective
    have hB : B.card = Y.card := card_image_of_injective _ Subtype.coe_injective
    have hPos := hRect A (hSub X) B (hSub Y) (by rwa [hA]) (by rwa [hB])
    by_contra! hNone
    have hZero : incidences R A B = 0 := by
      apply sum_eq_zero
      intro b hb
      obtain ⟨y,hy',rfl⟩ := mem_image.mp hb
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨x,hx',rfl⟩ := mem_image.mp (mem_filter.mp ha).1
      exact hNone x hx' y hy' (mem_filter.mp ha).2
    omega

/-- Complete a locally balanced path system using only size, degree
and rectangle conditions on the physical free pairs. -/
theorem exists_hamilton_completion_of_physical_successor_pairs
    (d ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 0 < d) (hCost : ν ≤ d*τ) (hDegrees : γ ≤ d) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {n : ℕ} (D R : Digraph W)
      (cluster : W → Fin (n+1)) (r : Fin (n+1) → ℕ),
      let s := finRotate (n+1)
      let S := freeOut D cluster
      let T i := freeIn D cluster (s i)
      IsDirectedPathSystem D →
      (∀ i, (S i).card = (T i).card) →
      (∀ i, ∃ x, x ∈ freeIn D cluster i ∧ x ∈ S i) →
      (∀ i, N ≤ (S i).card) →
      (∀ i, 0 < r i ∧ ε*((S i).card:ℝ) ≤ (r i:ℝ) ∧ (r i:ℝ) ≤ d*((S i).card:ℝ)) →
      (∀ i, ∀ X ⊆ S i, ∀ Y ⊆ T i,
        ε*((S i).card:ℝ) ≤ (X.card:ℝ) → ε*((S i).card:ℝ) ≤ (Y.card:ℝ) →
        d*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences R X Y:ℝ)) →
      (∀ i v, v ∈ T i → d*((S i).card:ℝ) ≤ (inNeighbours R (S i) v:ℝ)) →
      (∀ i v, v ∈ S i → d*((S i).card:ℝ) ≤ (((T i).filter (R.Adj v)).card:ℝ)) →
      ∃ ρ : Equiv.Perm W, HasSpanningCycle (fun x y => ρ x = y) ∧
        (∀ x y, D.Adj x y → ρ x = y) ∧ (∀ x, (D ⊔ R).Adj x (ρ x)) := by
  obtain ⟨N,hN⟩ := exists_hamilton_completion_of_successor_reserves.{u} d ε ν τ γ
    hν hWidth hε hτγ hγ hd
  refine ⟨N,?_⟩
  intro W _ n D R cluster r s S T hPath hBal hOverlap hSize hr hRect hIn hOut
  have hSub {U : Finset W} (X : Finset U) : (X.image fun x => x.val) ⊆ U := by
    rintro v hv
    obtain ⟨x,_,rfl⟩ := mem_image.mp hv
    exact x.prop
  have hMatch (i : Fin (n+1)) : ∃ f : S i ≃ T i, ∀ x : S i, R.Adj x (f x) := by
    apply exists_matching_on_of_rectangle_threshold R (S i) (T i) (r i) (hBal i)
    · intro x hx
      exact_mod_cast (hr i).2.2.trans (hOut i x hx)
    · intro y hy
      exact_mod_cast (hr i).2.2.trans (hIn i y hy)
    · intro X hX Y hY hx hy
      have hxa : (r i:ℝ) ≤ X.card := by exact_mod_cast hx
      have hyb : (r i:ℝ) ≤ Y.card := by exact_mod_cast hy
      have hp := hRect i X hX Y hY ((hr i).2.1.trans hxa) ((hr i).2.1.trans hyb)
      have hr' : (0:ℝ) < r i := by exact_mod_cast (hr i).1
      have hPos : (0:ℝ) < incidences R X Y :=
        (mul_pos (mul_pos hd (hr'.trans_le hxa)) (hr'.trans_le hyb)).trans_le hp
      exact_mod_cast hPos
  obtain ⟨σ,hKeep,hNew,_⟩ := exists_factor_completion_of_successor_matchings D R cluster s hPath hMatch
  let f i := freeSuccessorEquiv D R cluster s σ hKeep hNew i
  apply hN D R cluster σ hPath.acyclic hKeep hNew hOverlap hSize hCost hDegrees
  · intro i A B ha hb
    rw [reserve_incidence_image]
    have hb' : (B.image fun y : S i => σ y) ⊆ T i := by
      intro y hy
      obtain ⟨v,_,rfl⟩ := mem_image.mp hy
      exact (f i v).prop
    have hA : (A.image fun v : S i => v.val).card = A.card :=
      card_image_of_injective _ Subtype.coe_injective
    have hB : (B.image fun v : S i => σ v).card = B.card :=
      card_image_of_injective _ (σ.injective.comp Subtype.coe_injective)
    have h := hRect i _ (hSub A) _ hb' (by rwa [hA]) (by rwa [hB])
    change d * ((A.image fun v : S i => v.val).card:ℝ) *
        ((B.image fun v : S i => σ v).card:ℝ) ≤ _ at h
    rw [hA,hB] at h
    exact h
  · intro i v
    rw [reserve_indegree_physical]
    exact hIn i _ (f i v).prop
  · intro i v
    rw [reserve_outdegree_physical R σ (S i) (T i) (f i) (fun _ => rfl)]
    exact hOut i _ v.prop

end OverfullWork.DirectedRobustExpansion
