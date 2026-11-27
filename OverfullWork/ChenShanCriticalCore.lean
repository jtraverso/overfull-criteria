module

public import OverfullWork.DeletedCopyKempeState
public import OverfullWork.CopyMultifanMaximal
public import OverfullWork.CanonicalColouringPullback
public import OverfullWork.MultigraphPartition
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph Finset ShannonColouring CopyMultifan
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem deleted_copy_coloring {M : MultiGraph V} {k : ℕ}
    (hcrit : M.IsCopyCritical k) (hk : 0 < k) (x v : V)
    (hpos : 0 < M.mult s(x,v)) :
    ∃ c : M.FreshCopies x v → Fin k,
      ProperOn (M.freshEnds x v) (univ.erase none) c := by
  obtain ⟨C⟩ := hcrit.deletion_colourable _ hpos
  obtain ⟨c,hc,_⟩ := C.exists_labelled_copy_colouring
  refine ⟨fun i => i.elim ⟨0,hk⟩ c,?_⟩
  intro i hi j hj hne hInc
  cases i with
  | none => exact ((mem_erase.mp hi).1 rfl).elim
  | some p =>
    cases j with
    | none => exact ((mem_erase.mp hj).1 rfl).elim
    | some q => exact hc p q (fun he => hne (congrArg some he)) hInc

omit [Fintype V] [DecidableEq V] in
private theorem endpoints_ne_of_positive {M : MultiGraph V} {x v : V}
    (h : 0 < M.mult s(x,v)) : x ≠ v := by
  rintro rfl
  rw [M.loopless _ (by simp)] at h
  omega

/-- Chen–Shan Lemma 3.5(1), counting the missing colors at both ends
of the removed copy. -/
theorem copyCritical_endpoint_degree_sum {M : MultiGraph V} {k : ℕ}
    (hcrit : M.IsCopyCritical k) (hDegree : ∀ w, M.degree w ≤ k)
    (x v : V) (hpos : 0 < M.mult s(x,v)) :
    k+2 ≤ M.degree x + M.degree v := by
  let ends := M.freshEnds x v
  let S : Finset (M.FreshCopies x v) := univ.erase none
  have hnone : (none : M.FreshCopies x v) ∉ S := by simp [S]
  have hx : Incident ends none x := Or.inl rfl
  have hv : Incident ends none v := Or.inr rfl
  have hdx : 0 < M.degree x := by
    rw [← M.freshEnds_degree x v hpos]
    exact card_pos.mpr ⟨none,mem_filter.mpr ⟨mem_univ _,hx⟩⟩
  obtain ⟨c,hc⟩ := deleted_copy_coloring hcrit (hdx.trans_le (hDegree x)) x v hpos
  have hc : ProperOn ends S c := hc
  have hdisj : Disjoint (univ.filter (Misses ends S c x)) (univ.filter (Misses ends S c v)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hb := hc.extend hnone (mem_filter.mp hi).2 (mem_filter.mp hj).2
    apply hcrit.not_fresh_colourable x v hpos
    exact ⟨_,fun e f hne hinc => hb e (by simp [S]) f (by simp [S]) hne hinc⟩
  have hcap : (univ.filter (Misses ends S c x)).card +
      (univ.filter (Misses ends S c v)).card ≤ k := by
    rw [← card_union_of_disjoint hdisj]
    exact (card_le_univ _).trans_eq (Fintype.card_fin k)
  have hlow (w : V) (hw : Incident ends none w) :
      k+1 ≤ (univ.filter (Misses ends S c w)).card + M.degree w := by
    have h₁ := card_misses_add ends S c w
    have h₂ := card_incident_lt ends hnone hw
    rw [M.freshEnds_degree x v hpos w] at h₂
    omega
  have h1 := hlow x hx
  have h2 := hlow v hv
  omega

set_option maxHeartbeats 1300000 in
/-- Chen–Shan Lemma 3.5(2). Among the missing colors at a low-degree
neighbor, one must appear on a copy to a second low-degree neighbor.
A two-leaf multifan then gives the required contradiction. -/
theorem copyCritical_no_low_degree_neighbour {M : MultiGraph V} {k s : ℕ}
    (hcrit : M.IsCopyCritical k) (hDegree : ∀ w, M.degree w ≤ k)
    (x : V) (X : Finset V) (_hX : x ∉ X) (hLow : ∀ v ∈ X, M.degree v ≤ s)
    (hTwo : 2*s ≤ k) (hBudget : ∀ v ∈ X, M.degreeInto Xᶜ x + M.mult s(x,v) ≤ k-s+1) :
    ∀ v ∈ X, M.mult s(x,v) = 0 := by
  intro v hv
  by_contra hZero
  have hpos : 0 < M.mult s(x,v) := by omega
  have hxv : x ≠ v := endpoints_ne_of_positive hpos
  let I := M.FreshCopies x v
  let E := M.freshEnds x v
  let S : Finset I := univ.erase none
  have hnone : (none : I) ∉ S := by simp [S]
  have hx : Incident E none x := Or.inl rfl
  have hincv : Incident E none v := Or.inr rfl
  have hDegEq (w : V) : degree E w = M.degree w := M.freshEnds_degree x v hpos w
  have hdx : 0 < M.degree x := by
    rw [← hDegEq]
    exact card_pos.mpr ⟨none,mem_filter.mpr ⟨mem_univ _,hx⟩⟩
  obtain ⟨c,hc⟩ := deleted_copy_coloring hcrit (hdx.trans_le (hDegree x)) x v hpos
  have hc : ProperOn E S c := hc
  have hNo : ¬ ∃ b : I → Fin k, ProperOn E (insert none S) b := by
    rintro ⟨b,hb⟩
    apply hcrit.not_fresh_colourable x v hpos
    exact ⟨_,fun e f hne hinc => hb e (by simp [S]) f (by simp [S]) hne hinc⟩
  have hRoot (b : I → Fin k) (_hb : ProperOn E S b) : ∃ a, Misses E S b x a := by
    have hh := card_misses_ge_of_incident (fun w => (hDegEq w).le.trans (hDegree w)) hnone b hx
    have hp : 0 < (univ.filter (Misses E S b x)).card := by omega
    obtain ⟨a,ha⟩ := card_pos.mp hp
    exact ⟨a,(mem_filter.mp ha).2⟩
  let A := univ.filter (Misses E S c v)
  have hA : k+1 ≤ A.card + s := by
    have h₁ := card_misses_add E S c v
    have h₂ := card_incident_lt E hnone hincv
    rw [hDegEq] at h₂
    have hd := hLow v hv
    change k ≤ A.card + _ at h₁
    omega
  let C := Xᶜ.biUnion (fun w => S.filter (fun e => Joins E e x w))
  let D := S.filter (fun e => Joins E e x v)
  have hCard (w : V) : (univ.filter (fun e => Joins E e x w)).card = M.mult s(x,w) := by
    have hEq : (univ.filter (fun e => Joins E e x w)) =
        (univ.filter (fun e : M.FreshCopies x v =>
          s((M.freshEnds x v e).1,(M.freshEnds x v e).2) = s(x,w))) := by
      ext e
      simp [Joins,E]
    rw [hEq]
    exact M.freshEnds_fibre x v hpos s(x,w)
  have hC : C.card ≤ M.degreeInto Xᶜ x := by
    apply card_biUnion_le.trans
    apply sum_le_sum
    intro w _
    exact (card_le_card (filter_subset_filter _ (subset_univ S))).trans (hCard w).le
  have hD : D.card+1 ≤ M.mult s(x,v) := by
    have hsub : insert none D ⊆ univ.filter (fun e => Joins E e x v) := by
      intro e he
      rcases mem_insert.mp he with rfl | he
      · exact mem_filter.mpr ⟨mem_univ _,rfl⟩
      · exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2⟩
    have hn : (none : I) ∉ D := fun h => hnone (mem_filter.mp h).1
    have h := card_le_card hsub
    rw [card_insert_of_notMem hn,hCard] at h
    exact h
  have hExists : ∃ e ∈ S, ∃ w ∈ X, w ≠ v ∧ Joins E e x w ∧ Misses E S c v (c e) := by
    by_contra! hn
    have hsub : A ⊆ (C ∪ D).image c := by
      intro a ha
      have hm := (mem_filter.mp ha).2
      have hxm : ¬ Misses E S c x a := fun h =>
        hNo ⟨_,hc.extend hnone h hm⟩
      unfold Misses at hxm
      push Not at hxm
      obtain ⟨e,he,hix,hce⟩ := hxm
      obtain ⟨w,hwj⟩ := exists_other hix
      refine mem_image.mpr ⟨e,?_,hce⟩
      by_cases hw : w ∈ X
      · have hEq : w = v := by
          by_contra hne
          exact hn e he w hw hne hwj (hce ▸ hm)
        exact mem_union_right _ (mem_filter.mpr ⟨he,hEq ▸ hwj⟩)
      · exact mem_union_left _ (mem_biUnion.mpr ⟨w,mem_compl.mpr hw,mem_filter.mpr ⟨he,hwj⟩⟩)
    have hcap := (card_le_card hsub).trans ((card_image_le).trans (card_union_le C D))
    have h := hBudget v hv
    omega
  obtain ⟨e,he,w,hw,hwv,hJoin,hMiss⟩ := hExists
  let y : ℕ → V := fun i => if i = 0 then v else w
  let g : ℕ → I := fun i => if i = 0 then none else e
  have hF : IsFan E S c x none 2 y g := by
    refine ⟨by decide,by simp [g],?_,?_,?_,?_⟩
    · intro i hi
      have hh : i = 0 ∨ i = 1 := by omega
      rcases hh with rfl | rfl
      · simp only [y,g,ite_true]
        rfl
      · simpa [y,g] using hJoin
    · intro i hi j hj heq
      have hh : i = 0 ∨ i = 1 := by omega
      have hh' : j = 0 ∨ j = 1 := by omega
      rcases hh with rfl | rfl <;> rcases hh' with rfl | rfl <;> simp_all [y]
    · intro i hi hi'
      have h : i = 1 := by omega
      simpa [g,h] using he
    · intro i hi hi'
      have h : i = 1 := by omega
      exact ⟨0,hi,by simpa [g,y,h] using hMiss⟩
  have hApart := (elementary (M.freshEnds_loopless x v hxv) hnone hNo hRoot 2 c hc hF).2.1
  let B := univ.filter (Misses E S c w)
  have hDisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact hApart 0 (by decide) 1 (by decide) (by decide) a
      (by simpa [y] using (mem_filter.mp ha).2) (by simpa [y] using (mem_filter.mp hb).2)
  have hB : k ≤ B.card+s := by
    have h₁ := card_misses_add E S c w
    have h₂ := card_incident_le E S w
    rw [hDegEq] at h₂
    have h₃ := hLow w hw
    change k ≤ B.card + _ at h₁
    omega
  have hAB : A.card+B.card ≤ k := by
    rw [← card_union_of_disjoint hDisj]
    exact (card_le_univ _).trans_eq (Fintype.card_fin k)
  omega


/-- The simple core edges restored to the exterior when moving Y out of
the core. This includes edges with both endpoints in Y. -/
def restoredCoreEdges (H : SimpleGraph V) (Y : Finset V) : SimpleGraph V where
  Adj x y := H.Adj x y ∧ (x ∈ Y ∨ y ∈ Y)
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => H.loopless.irrefl _ h.1⟩

private theorem degreeInto_le_degree (M : MultiGraph V) (S : Finset V) (v : V) :
    M.degreeInto S v ≤ M.degree v := by
  have h := M.degreeInto_add_compl S v
  omega

omit [Fintype V] [DecidableEq V] in
private theorem degreeInto_add (M N : MultiGraph V) (S : Finset V) (x : V) :
    (M.addCopies N).degreeInto S x = M.degreeInto S x + N.degreeInto S x := by
  simp only [MultiGraph.degreeInto,MultiGraph.addCopies,sum_add_distrib]

set_option maxHeartbeats 1400000 in
/-- Chen–Shan Lemma 3.7. Write the original regular multigraph as the
sum of the exterior M and the simple graph H on U. The exterior of
the trimmed core has a k-coloring and the stated retained degree bound. -/
theorem colourable_exterior_after_core_deletion
    (M : MultiGraph V) (H : SimpleGraph V) [DecidableRel H.Adj] (U Y : Finset V)
    (hY : Y ⊆ U) (hSupport : ∀ x y, H.Adj x y → x ∈ U ∧ y ∈ U) (k a : ℕ)
    (hRegular : ∀ v, (M.addCopies (MultiGraph.ofSimpleGraph H)).degree v = k)
    (hSmall : ∀ v ∈ U, M.degree v ≤ a) (hColour : Nonempty (M.EdgeColoring k))
    (hSlack : 3*(a+Y.card) < k) :
    let N := M.addCopies (MultiGraph.ofSimpleGraph (restoredCoreEdges H Y))
    Nonempty (N.EdgeColoring k) ∧ ∀ v ∈ U \ Y, N.degree v ≤ a+Y.card := by
  intro N
  let X := U \ Y
  let s := a+Y.card
  let Q := MultiGraph.ofSimpleGraph (restoredCoreEdges H Y)
  have hQ (v w : V) : Q.mult s(v,w) = if H.Adj v w ∧ (v ∈ Y ∨ w ∈ Y) then 1 else 0 := by
    simp only [Q,MultiGraph.ofSimpleGraph,mem_edgeSet,restoredCoreEdges]
  have hCap (v w : V) : Q.mult s(v,w) ≤ (MultiGraph.ofSimpleGraph H).mult s(v,w) := by
    rw [hQ]
    change _ ≤ if s(v,w) ∈ H.edgeSet then 1 else 0
    by_cases h : H.Adj v w
    · by_cases hY' : v ∈ Y ∨ w ∈ Y <;> simp [mem_edgeSet,h,hY']
    · simp [mem_edgeSet,h]
  have hDeg : ∀ v, N.degree v ≤ k := by
    intro v
    rw [← hRegular v]
    apply MultiGraph.degree_le_of_mult_le
    intro e
    induction e using Sym2.inductionOn with
    | hf x y =>
      exact Nat.add_le_add_left (hCap x y) _
  have hRow (v : V) (S : Finset V)
      (hBound : ∀ w ∈ S, H.Adj v w → (v ∈ Y ∨ w ∈ Y) → w ∈ Y) :
      Q.degreeInto S v ≤ Y.card := by
    unfold MultiGraph.degreeInto
    simp_rw [hQ]
    rw [← sum_filter,← card_eq_sum_ones]
    exact card_le_card (fun _ hw => hBound _ (mem_filter.mp hw).1
      (mem_filter.mp hw).2.1 (mem_filter.mp hw).2.2)
  have hRetained (v : V) (hv : v ∈ X) : N.degree v ≤ s := by
    have hvU := (mem_sdiff.mp hv).1
    have hvY := (mem_sdiff.mp hv).2
    have hq := hRow v univ (fun w _ _ hw => hw.resolve_left hvY)
    rw [MultiGraph.degreeInto, ← Q.degree_eq_sum_mult] at hq
    change (M.addCopies Q).degree v ≤ s
    rw [MultiGraph.degree_addCopies]
    exact Nat.add_le_add (hSmall v hvU) hq
  have hMoved (v : V) (hv : v ∈ Y) : N.degreeInto Xᶜ v ≤ s := by
    have hq := hRow v Xᶜ (fun w hw ha _ => by
      by_contra hwy
      exact (mem_compl.mp hw) (mem_sdiff.mpr ⟨(hSupport v w ha).2,hwy⟩))
    change (M.addCopies Q).degreeInto Xᶜ v ≤ s
    rw [degreeInto_add]
    exact Nat.add_le_add ((degreeInto_le_degree M _ v).trans (hSmall v (hY hv))) hq
  refine ⟨?_,hRetained⟩
  by_contra hNo
  obtain ⟨P,hPN,hcrit⟩ := N.exists_copy_critical k hNo
  have hPdeg (v : V) : P.degree v ≤ k := (N.degree_le_of_mult_le P hPN v).trans (hDeg v)
  have hPLow (v : V) (hv : v ∈ X) : P.degree v ≤ s :=
    (N.degree_le_of_mult_le P hPN v).trans (hRetained v hv)
  have hPOut (v : V) (hv : v ∈ Y) : P.degreeInto Xᶜ v ≤ s :=
    (sum_le_sum (fun w _ => hPN s(v,w))).trans (hMoved v hv)
  have hAcross (x : V) (hx : x ∈ Y) : ∀ v ∈ X, P.mult s(x,v) = 0 := by
    apply copyCritical_no_low_degree_neighbour hcrit hPdeg x X
      (fun hh => (mem_sdiff.mp hh).2 hx) hPLow (by dsimp [s] at *; omega)
    intro v hv
    have hm : P.mult s(x,v) ≤ P.degree v := by
      rw [P.degree_eq_sum_mult,Sym2.eq_swap]
      exact single_le_sum (f := fun y => P.mult s(v,y)) (fun _ _ => Nat.zero_le _) (mem_univ x)
    have h₁ := hPLow v hv
    have h₂ := hPOut x hx
    dsimp only [s] at *
    omega
  have hDeleted (x : V) (hx : x ∈ Y) : P.degree x ≤ s := by
    have hZero : P.degreeInto X x = 0 := sum_eq_zero (hAcross x hx)
    have hTotal := P.degreeInto_add_compl X x
    rw [hZero,zero_add] at hTotal
    exact hTotal ▸ hPOut x hx
  have hNoRestored (x y : V) (hx : x ∈ Y) (hyU : y ∈ U) : P.mult s(x,y) = 0 := by
    by_cases hy : y ∈ Y
    · by_contra hn
      have h := copyCritical_endpoint_degree_sum hcrit hPdeg x y (by omega : 0 < P.mult s(x,y))
      have hx' := hDeleted x hx
      have hy' := hDeleted y hy
      dsimp only [s] at *
      omega
    · exact hAcross x hx y (mem_sdiff.mpr ⟨hyU,hy⟩)
  have hPM : ∀ e, P.mult e ≤ M.mult e := by
    intro e
    induction e using Sym2.inductionOn with
    | hf x y =>
      by_cases h : H.Adj x y ∧ (x ∈ Y ∨ y ∈ Y)
      · obtain ⟨hxU,hyU⟩ := hSupport x y h.1
        rcases h.2 with hx | hy
        · rw [hNoRestored x y hx hyU]
          exact Nat.zero_le _
        · rw [Sym2.eq_swap,hNoRestored y x hy hxU]
          exact Nat.zero_le _
      · have hz : Q.mult s(x,y) = 0 := (hQ x y).trans (ite_eq_right h)
        have hh := hPN s(x,y)
        change P.mult s(x,y) ≤ M.mult s(x,y) + Q.mult s(x,y) at hh
        rwa [hz,add_zero] at hh
  obtain ⟨C⟩ := hColour
  exact hcrit.uncolourable (CanonicalColouringPullback.restrict_copies P M C hPM)

end OverfullWork.ChenShan
