module

public import OverfullWork.KuhnOsthusRoutedChords
public import OverfullWork.KuhnOsthusPathFactorCompletion
public import OverfullWork.KuhnOsthusPathPartitionSizes

@[expose] public section


/-! Insert the realized chords into the original path system and
construct the cyclic arc lists used in Proposition 7.3. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open DirectedDemandHall (Arc)
open scoped Classical
variable {V I : Type*} [Fintype V]

omit [Fintype V] in
/-- Pairwise disjoint ordered endpoints give a directed matching. -/
theorem path_system_of_separate_arcs {P : Type*} (f : P → V × V)
    (hne : ∀ p, (f p).1 ≠ (f p).2)
    (hSep : ∀ p q, p ≠ q → (f p).1 ≠ (f q).1 ∧ (f p).1 ≠ (f q).2 ∧
      (f p).2 ≠ (f q).1 ∧ (f p).2 ≠ (f q).2) :
    IsDirectedPathSystem (⟨fun x y => ∃ p, f p = (x,y)⟩ : Digraph V) := by
  let D : Digraph V := ⟨fun x y => ∃ p, f p = (x,y)⟩
  have hNoJoin {x y z : V} (hx : D.Adj x y) (hy : D.Adj y z) : False := by
    obtain ⟨p,hp⟩ := hx
    obtain ⟨q,hq⟩ := hy
    have he : (f p).2 = (f q).1 := (congrArg Prod.snd hp).trans (congrArg Prod.fst hq).symm
    by_cases h : p = q
    · subst q
      exact hne p he.symm
    · exact (hSep p q h).2.2.1 he
  have hPath {x y : V} (h : Relation.TransGen D.Adj x y) : D.Adj x y := by
    induction h with
    | single h => exact h
    | tail _ h ih => exact (hNoJoin ih h).elim
  refine ⟨?_,?_,?_⟩
  · intro x hx
    exact hNoJoin (hPath hx) (hPath hx)
  · intro x y z hy hz
    obtain ⟨p,hp⟩ := hy
    obtain ⟨q,hq⟩ := hz
    have he : (f p).1 = (f q).1 := (congrArg Prod.fst hp).trans (congrArg Prod.fst hq).symm
    have heq : p = q := by by_contra hn; exact (hSep p q hn).1 he
    subst q
    exact congrArg Prod.snd (hp.symm.trans hq)
  · intro x y z hy hz
    obtain ⟨p,hp⟩ := hy
    obtain ⟨q,hq⟩ := hz
    have he : (f p).2 = (f q).2 := (congrArg Prod.snd hp).trans (congrArg Prod.snd hq).symm
    have heq : p = q := by by_contra hn; exact (hSep p q hn).2.2.2 he
    subst q
    exact congrArg Prod.fst (hp.symm.trans hq)

omit [Fintype V] in
private theorem chord_cycle_step (cluster : V → I) (s : Equiv.Perm I)
    (x y : V) (l : List I) (hl : (cluster y :: l).getLast? = some (s (cluster x)))
    (f : Fin l.length → V × V)
    (hf : ∀ i : Fin l.length, cluster (f i).1 =
      s.symm ((cluster y :: l)[i.val]'(Nat.lt_succ_of_lt i.isLt)) ∧ cluster (f i).2 = l[i.val]) :
    ∀ i : Fin (l.length+1),
      cluster (Fin.cases (motive := fun _ => V × V) (x,y) f i).2 =
        s (cluster (Fin.cases (motive := fun _ => V × V) (x,y) f (finRotate _ i)).1) := by
  intro i
  let L := cluster y :: l
  have hFirst (i : Fin (l.length+1)) :
      s (cluster (Fin.cases (motive := fun _ => V × V) (x,y) f i).1) =
        if i.val = 0 then s (cluster x)
        else L[i.val-1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.cases_succ,Fin.val_succ,Nat.add_sub_cancel,Nat.add_one_ne_zero,if_false]
      rw [(hf j).1,s.apply_symm_apply]
  have hSecond (i : Fin (l.length+1)) : cluster (Fin.cases (motive := fun _ => V × V) (x,y) f i).2 = L[i.val] := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact (hf j).2
  have hLast : L[l.length]'(by simp [L]) = s (cluster x) := by
    change L.getLast? = some _ at hl
    rw [List.getLast?_eq_getElem?] at hl
    have he : L.length - 1 = l.length := by simp [L]
    rw [he,List.getElem?_eq_getElem (by simp [L])] at hl
    exact Option.some.inj hl
  rw [hFirst,hSecond]
  by_cases hi : i = Fin.last l.length
  · subst i
    rw [finRotate_last]
    simp only [Fin.val_zero,Fin.val_last]
    exact hLast
  · have hi' : (finRotate _ i).val = i.val + 1 := coe_finRotate_of_ne_last hi
    simp only [hi',Nat.add_one_ne_zero,if_false,Nat.add_sub_cancel]

/-- Add the chord arcs, keep the original paths, and obtain the balance
needed for the free matchings and the subsequent Hamilton merge. -/
theorem balanced_chord_extension_of_realized_routes (Q H : Digraph V)
    (cluster : V → I) (s : Equiv.Perm I) (hQ : IsDirectedPathSystem Q)
    (l : Arc Q → List I)
    (hEnd : ∀ j : Arc Q, (cluster j.val.2 :: l j).getLast? = some (s (cluster j.val.1)))
    (f : (Σ j, Fin (l j).length) → V × V)
    (hChord : ∀ p, cluster (f p).1 =
        s.symm ((cluster p.1.val.2 :: l p.1)[p.2.val]'(Nat.lt_succ_of_lt p.2.isLt)) ∧
      cluster (f p).2 = (l p.1)[p.2.val] ∧ H.Adj (f p).1 (f p).2 ∧ (f p).1 ≠ (f p).2)
    (hFresh : ∀ p, ¬ IncidentTo Q (f p).1 ∧ ¬ IncidentTo Q (f p).2)
    (hSep : ∀ p q, p ≠ q → (f p).1 ≠ (f q).1 ∧ (f p).1 ≠ (f q).2 ∧
      (f p).2 ≠ (f q).1 ∧ (f p).2 ≠ (f q).2)
    (hSize : ∀ i, (univ.filter (fun x => cluster x = i)).card =
      (univ.filter (fun x => cluster x = s i)).card) :
    ∃ D : Digraph V, Q ≤ D ∧ D ≤ Q ⊔ H ∧ IsDirectedPathSystem D ∧
      ∀ i, (freeOut D cluster i).card = (freeIn D cluster (s i)).card := by
  classical
  let C : Digraph V := ⟨fun x y => ∃ p, f p = (x,y)⟩
  let D := Q ⊔ C
  have hC : IsDirectedPathSystem C := path_system_of_separate_arcs f (fun p => (hChord p).2.2.2) hSep
  have hDis (v : V) (hv : IncidentTo Q v) (hc : IncidentTo C v) : False := by
    rcases hc with ⟨w,p,hp⟩ | ⟨w,p,hp⟩
    · exact (hFresh p).1 ((congrArg Prod.fst hp).symm ▸ hv)
    · exact (hFresh p).2 ((congrArg Prod.snd hp).symm ▸ hv)
  have hCH : C ≤ H := by
    rintro x y ⟨p,hp⟩
    have h := (hChord p).2.2.1
    rw [hp] at h
    exact h
  refine ⟨D,le_sup_left,sup_le_sup_left hCH _,hQ.sup_of_disjoint_vertices hC hDis,?_⟩
  let arc (p : Σ j, Fin ((l j).length+1)) : V × V :=
    Fin.cases p.1.val (fun k => f ⟨p.1,k⟩) p.2
  have hArcs (x y : V) : D.Adj x y ↔ ∃ p, (arc p).1 = x ∧ (arc p).2 = y := by
    constructor
    · intro he
      rcases (Digraph.sup_adj _ _ _ _).mp he with he | ⟨p,hp⟩
      · exact ⟨⟨⟨(x,y),he⟩,0⟩,rfl,rfl⟩
      · exact ⟨⟨p.1,p.2.succ⟩,congrArg Prod.fst hp,congrArg Prod.snd hp⟩
    · rintro ⟨⟨j,k⟩,hx,hy⟩
      revert hx hy
      refine Fin.cases ?_ (fun p => ?_) k
      · intro hx hy
        exact (Digraph.sup_adj _ _ _ _).mpr (Or.inl (hx ▸ hy ▸ j.prop))
      · intro hx hy
        exact (Digraph.sup_adj _ _ _ _).mpr (Or.inr ⟨⟨j,p⟩,Prod.ext hx hy⟩)
  have hInject (π : V × V → V) (hπ : π = Prod.fst ∨ π = Prod.snd) :
      Function.Injective (fun p => π (arc p)) := by
    have hOld (j : Arc Q) : IncidentTo Q (π j.val) := by
      rcases hπ with rfl | rfl
      · exact Or.inl ⟨_,j.prop⟩
      · exact Or.inr ⟨_,j.prop⟩
    have hNew (p : Σ j, Fin (l j).length) : ¬ IncidentTo Q (π (f p)) := by
      rcases hπ with rfl | rfl
      · exact (hFresh p).1
      · exact (hFresh p).2
    rintro ⟨j,k⟩ ⟨j',k'⟩
    refine Fin.cases ?_ (fun p => ?_) k <;> refine Fin.cases ?_ (fun q => ?_) k'
    · intro he
      have hj : j = j' := by
        apply Subtype.ext
        rcases hπ with rfl | rfl
        · have he' : j.val.1 = j'.val.1 := he
          exact Prod.ext he' (hQ.out_unique j.prop (he'.symm ▸ j'.prop))
        · have he' : j.val.2 = j'.val.2 := he
          exact Prod.ext (hQ.in_unique j.prop (he'.symm ▸ j'.prop)) he'
      subst j'
      rfl
    · intro he
      have he' : π j.val = π (f ⟨j',q⟩) := he
      exact (hNew _ (he' ▸ hOld j)).elim
    · intro he
      have he' : π (f ⟨j,p⟩) = π j'.val := he
      exact (hNew _ (he'.symm ▸ hOld j')).elim
    · intro he
      have he' : π (f ⟨j,p⟩) = π (f ⟨j',q⟩) := he
      have heq : (⟨j,p⟩ : Σ j, Fin (l j).length) = ⟨j',q⟩ := by
        by_contra hn
        rcases hπ with rfl | rfl
        · exact (hSep _ _ hn).1 he'
        · exact (hSep _ _ hn).2.2.2 he'
      exact congrArg (fun z : Σ j, Fin (l j).length => (⟨z.1,z.2.succ⟩ : Σ j, Fin ((l j).length+1))) heq
  exact locally_balanced_of_chord_lists (fun j => (l j).length) D cluster s
    (fun p => (arc p).1) (fun p => (arc p).2) hArcs
    (hInject _ (Or.inl rfl)) (hInject _ (Or.inr rfl))
    (fun j i => chord_cycle_step cluster s j.val.1 j.val.2 (l j) (hEnd j)
      (fun k => f ⟨j,k⟩) (fun k => ⟨(hChord ⟨j,k⟩).1,(hChord ⟨j,k⟩).2.1⟩) i) hSize

/-- The restricted physical chord pairs avoid the old path system.
Any further set reserved away from both systems remains free in both
directions after the chords have been added. -/
theorem exists_balanced_extension_for_routes [Fintype I] (R : Digraph I) (Q H : Digraph V)
    (cluster : V → I) (s : Equiv.Perm I) (hQ : IsDirectedPathSystem Q)
    (l : Arc Q → List I)
    (hR : ∀ i, ¬ R.Adj i i)
    (hRoute : ∀ j : Arc Q, DirectedListRoutes.Route (reindexSources R s.symm) (cluster j.val.2)
      (s (cluster j.val.1)) (l j))
    (A : I → Finset V) (m e : ℕ) (hm : 0 < m) (he : 50*e ≤ m)
    (hSize : ∀ i, 50*(A i).card = 24*m)
    (hClass : ∀ i x, x ∈ A i → cluster x = i)
    (hFresh : ∀ i x, x ∈ A i → ¬ IncidentTo Q x)
    (hRect : ∀ i j, R.Adj i j → ∀ S ⊆ A i, ∀ T ⊆ A j,
      e < S.card → e < T.card → 0 < incidences H S T)
    (hInt : ∀ i, 100*(∑ j, chordInteriorLoad s (l j) i) ≤ m)
    (hFrom : ∀ i, 10*(∑ j : Arc Q, if s.symm (cluster j.val.2) = i then (1:ℕ) else 0) ≤ m)
    (hTo : ∀ i, 10*(∑ j : Arc Q, if s (cluster j.val.1) = i then (1:ℕ) else 0) ≤ m)
    (hCluster : ∀ i, (univ.filter (fun x => cluster x = i)).card =
      (univ.filter (fun x => cluster x = s i)).card) :
    ∃ D : Digraph V, Q ≤ D ∧ D ≤ Q ⊔ H ∧ IsDirectedPathSystem D ∧
      (∀ i, (freeOut D cluster i).card = (freeIn D cluster (s i)).card) ∧
      ∀ x, ¬ IncidentTo Q x → x ∉ A (cluster x) →
        x ∈ freeOut D cluster (cluster x) ∧ x ∈ freeIn D cluster (cluster x) := by
  let H' : Digraph V := ⟨fun x y => H.Adj x y ∧ x ∈ A (cluster x) ∧ y ∈ A (cluster y)⟩
  obtain ⟨f,hf,hSep⟩ := exists_physical_chords_for_routes R H s cluster
    (fun j : Arc Q => cluster j.val.2) (fun j : Arc Q => s (cluster j.val.1)) l
    hR hRoute A m e hm he hSize hClass hRect hInt hFrom hTo
  have hF (p : Σ j : Arc Q, Fin (l j).length) :
      cluster (f p).1 =
        s.symm ((cluster p.1.val.2 :: l p.1)[p.2.val]'(Nat.lt_succ_of_lt p.2.isLt)) ∧
      cluster (f p).2 = (l p.1)[p.2.val] ∧ H'.Adj (f p).1 (f p).2 ∧ (f p).1 ≠ (f p).2 := by
    obtain ⟨ha,hb,hEdge,hne⟩ := hf p
    have ha' := hClass _ _ ha
    have hb' := hClass _ _ hb
    exact ⟨ha',hb',⟨hEdge,ha'.symm ▸ ha,hb'.symm ▸ hb⟩,hne⟩
  obtain ⟨D,hDQ,hDSub,hD,hBal⟩ := balanced_chord_extension_of_realized_routes Q H' cluster s hQ
    l (fun j => (hRoute j).2) f hF (fun p => ⟨hFresh _ _ (hf p).1,hFresh _ _ (hf p).2.1⟩)
    hSep hCluster
  have hLe : H' ≤ H := fun _ _ h => h.1
  refine ⟨D,hDQ,hDSub.trans (sup_le_sup_left hLe _),hD,hBal,?_⟩
  intro x hx hA
  refine ⟨mem_freeOut.mpr ⟨rfl,?_⟩,mem_freeIn.mpr ⟨rfl,?_⟩⟩
  · rintro ⟨y,hy⟩
    rcases (Digraph.sup_adj _ _ _ _).mp (hDSub hy) with h | h
    · exact hx (Or.inl ⟨y,h⟩)
    · exact hA h.2.1
  · rintro ⟨y,hy⟩
    rcases (Digraph.sup_adj _ _ _ _).mp (hDSub hy) with h | h
    · exact hx (Or.inr ⟨y,h⟩)
    · exact hA h.2.2

end OverfullWork.DirectedRobustExpansion
