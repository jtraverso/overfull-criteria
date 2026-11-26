module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V : Type*}

/-- Incoming and outgoing arcs have the same count at every vertex. -/
def ArcBalanced (E : Finset (V × V)) : Prop :=
  ∀ v, (E.filter (fun e => e.1 = v)).card = (E.filter (fun e => e.2 = v)).card

/-- The arc list of an injectively labeled cyclic order. -/
def cycleArcs (n : ℕ) (f : Fin (n+1) ↪ V) : Finset (V × V) :=
  (univ : Finset (Fin (n+1))).map ⟨fun i => (f i, f (finRotate (n+1) i)),
    fun _ _ h => f.injective (congrArg Prod.fst h)⟩

theorem cycleArcs_card (n : ℕ) (f : Fin (n+1) ↪ V) : (cycleArcs n f).card = n+1 := by
  simp [cycleArcs]

/-- Any nonempty balanced finite digraph contains a simple directed
cycle. Choose a shortest positive return in a successor sequence. -/
theorem exists_cycleArcs_subset [Fintype V] (E : Finset (V × V))
    (hBal : ArcBalanced E) (hE : E.Nonempty) :
    ∃ n : ℕ, ∃ f : Fin (n+1) ↪ V, cycleArcs n f ⊆ E := by
  classical
  have hNext (v : V) (hIn : (E.filter (fun e => e.2 = v)).Nonempty) :
      ∃ w : V, (v,w) ∈ E := by
    have h := card_pos.mpr hIn
    rw [← hBal v] at h
    obtain ⟨⟨u,w⟩,he⟩ := card_pos.mp h
    obtain ⟨he,hu⟩ := mem_filter.mp he
    change u = v at hu
    exact ⟨w,hu ▸ he⟩
  obtain ⟨⟨u,v⟩,huv⟩ := hE
  let T := {v : V // (E.filter (fun e => e.2 = v)).Nonempty}
  let start : T := ⟨v,⟨(u,v),mem_filter.mpr ⟨huv,rfl⟩⟩⟩
  let next (a : T) : T :=
    let w := (hNext a.val a.property).choose
    ⟨w,⟨(a.val,w),mem_filter.mpr ⟨(hNext a.val a.property).choose_spec,rfl⟩⟩⟩
  let seq (i : ℕ) : V := ((next^[i]) start).val
  have hStep (i : ℕ) : (seq i,seq (i+1)) ∈ E := by
    change (((next^[i]) start).val,((next^[i+1]) start).val) ∈ E
    rw [Function.iterate_succ_apply']
    exact (hNext _ ((next^[i]) start).property).choose_spec
  let P (d : ℕ) := 0 < d ∧ ∃ i, seq i = seq (i+d)
  have hP : ∃ d, P d := by
    let q (i : Fin (Fintype.card V+1)) := seq i.val
    have hq : ¬ Function.Injective q := by
      intro hin
      have h := Fintype.card_le_of_injective q hin
      rw [Fintype.card_fin] at h
      omega
    obtain ⟨i,j,he,hij⟩ := Function.not_injective_iff.mp hq
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    change seq i.val = seq j.val at he
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨j.val-i.val, Nat.sub_pos_of_lt h, i.val, by
        rwa [Nat.add_sub_of_le h.le]⟩
    · exact ⟨i.val-j.val, Nat.sub_pos_of_lt h, j.val, by
        rw [Nat.add_sub_of_le h.le]
        exact he.symm⟩
  let d := Nat.find hP
  have hd : 0 < d := (Nat.find_spec hP).1
  obtain ⟨i,hi⟩ := (Nat.find_spec hP).2
  let n := d-1
  have hn : n+1 = d := by omega
  let g (j : Fin (n+1)) := seq (i+j.val)
  have hInjective : Function.Injective g := by
    intro a b h
    apply Fin.ext
    by_contra hne
    change seq (i+a.val) = seq (i+b.val) at h
    have noShort (j k : ℕ) (hl : j < k) (hk : k < d) (he : seq (i+j) = seq (i+k)) : False := by
      have hlp : 0 < k-j := Nat.sub_pos_of_lt hl
      have hshort : k-j < d := by omega
      have hEq : i+j+(k-j) = i+k := by omega
      exact (Nat.find_min hP hshort) ⟨hlp,i+j,by rwa [hEq]⟩
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact noShort _ _ hl (by have := b.isLt; omega) h
    · exact noShort _ _ hl (by have := a.isLt; omega) h.symm
  let f : Fin (n+1) ↪ V := ⟨g,hInjective⟩
  refine ⟨n,f,?_⟩
  intro e he
  obtain ⟨j,_,rfl⟩ := mem_map.mp he
  change (seq (i+j.val),seq (i+(finRotate (n+1) j).val)) ∈ E
  by_cases hLast : j = Fin.last n
  · rw [hLast,finRotate_last]
    change (seq (i+n),seq (i+0)) ∈ E
    rw [Nat.add_zero,hi]
    have h := hStep (i+n)
    rwa [Nat.add_assoc,hn] at h
  · rw [coe_finRotate_of_ne_last hLast,← Nat.add_assoc]
    exact hStep (i+j.val)


theorem cycleArcs_balanced (n : ℕ) (f : Fin (n+1) ↪ V) : ArcBalanced (cycleArcs n f) := by
  classical
  intro v
  unfold cycleArcs
  rw [filter_map,filter_map,card_map,card_map]
  simp only [Function.comp_def]
  rw [card_filter,card_filter]
  exact (Equiv.sum_comp (finRotate (n+1)) (fun i => if f i = v then (1 : ℕ) else 0)).symm

theorem arcBalanced_sdiff {E C : Finset (V × V)} (hC : C ⊆ E)
    (hE : ArcBalanced E) (hCycle : ArcBalanced C) : ArcBalanced (E \ C) := by
  classical
  intro v
  have hf (p : V × V → Prop) [DecidablePred p] :
      (E \ C).filter p = E.filter p \ C.filter p := by
    ext e
    simp only [mem_filter, mem_sdiff]
    tauto
  rw [hf,hf,card_sdiff_of_subset (filter_subset_filter _ hC),
    card_sdiff_of_subset (filter_subset_filter _ hC),hE v,hCycle v]

/-- Edge-disjoint directed cycles partition a balanced finite arc set.
The cardinality identity keeps track of the total cycle lengths. -/
theorem exists_directed_cycle_decomposition [Fintype V] (E : Finset (V × V))
    (hBal : ArcBalanced E) :
    ∃ L : List (Finset (V × V)), L.Pairwise Disjoint ∧
      (∀ C ∈ L, ∃ n : ℕ, ∃ f : Fin (n+1) ↪ V, cycleArcs n f = C) ∧
      (∀ e, e ∈ E ↔ ∃ C ∈ L, e ∈ C) ∧ (L.map Finset.card).sum = E.card := by
  classical
  induction E using Finset.strongInductionOn with
  | _ E ih =>
    by_cases h : E.Nonempty
    · obtain ⟨n,f,hC⟩ := exists_cycleArcs_subset E hBal h
      let C := cycleArcs n f
      have hc : C.Nonempty := ⟨(f 0,f (finRotate (n+1) 0)),mem_map.mpr ⟨0,mem_univ _,rfl⟩⟩
      have hLt : E \ C ⊂ E := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,?_⟩
        obtain ⟨e,he⟩ := hc
        intro hEq
        exact (mem_sdiff.mp (hEq.symm ▸ hC he)).2 he
      obtain ⟨L,hPair,hL,hPart,hCount⟩ := ih (E \ C) hLt (arcBalanced_sdiff hC hBal (cycleArcs_balanced n f))
      refine ⟨C::L,List.pairwise_cons.mpr ⟨?_,hPair⟩,?_,?_,?_⟩
      · intro D hD
        apply Finset.disjoint_left.mpr
        intro e he hd
        exact (mem_sdiff.mp ((hPart e).mpr ⟨D,hD,hd⟩)).2 he
      · intro D hD
        rcases List.mem_cons.mp hD with rfl | hD
        · exact ⟨n,f,rfl⟩
        · exact hL D hD
      · intro e
        constructor
        · intro he
          by_cases heC : e ∈ C
          · exact ⟨C,List.mem_cons_self,heC⟩
          · obtain ⟨D,hD,hed⟩ := (hPart e).mp (mem_sdiff.mpr ⟨he,heC⟩)
            exact ⟨D,List.mem_cons_of_mem _ hD,hed⟩
        · rintro ⟨D,hD,hed⟩
          rcases List.mem_cons.mp hD with rfl | hD
          · exact hC hed
          · exact (mem_sdiff.mp ((hPart e).mpr ⟨D,hD,hed⟩)).1
      · simp only [List.map_cons,List.sum_cons,hCount]
        rw [Nat.add_comm]
        exact card_sdiff_add_card_eq_card hC
    · rw [not_nonempty_iff_eq_empty.mp h]
      exact ⟨[],by simp,by simp,by simp,by simp⟩

/-- Possible balanced remainders of F whose endpoints belong to U. -/
noncomputable def balancedRemainders (F : Finset (V × V)) (U : Finset V) :
    Finset (Finset (V × V)) :=
  (((U ×ˢ U) ∩ F).powerset).filter ArcBalanced

theorem mem_balancedRemainders {F L : Finset (V × V)} {U : Finset V} :
    L ∈ balancedRemainders F U ↔ L ⊆ F ∧ L ⊆ U ×ˢ U ∧ ArcBalanced L := by
  simp only [balancedRemainders,mem_filter,mem_powerset,subset_inter_iff]
  tauto

/-- The bounds on the number and size of the remainders in Lemma 4.6. -/
theorem balancedRemainders_bounds (F : Finset (V × V)) (U : Finset V)
    {h : ℕ} (hU : U.card ≤ h) :
    (balancedRemainders F U).card ≤ 2^(h*h) ∧
      ∀ L ∈ balancedRemainders F U, L.card ≤ h*h := by
  have hProd : (U ×ˢ U).card ≤ h*h := by
    rw [card_product]
    exact Nat.mul_le_mul hU hU
  constructor
  · unfold balancedRemainders
    calc
      _ ≤ ((U ×ˢ U) ∩ F).powerset.card := card_filter_le _ _
      _ = 2^((U ×ˢ U) ∩ F).card := card_powerset _
      _ ≤ 2^(h*h) := Nat.pow_le_pow_right (by decide)
        ((card_le_card inter_subset_left).trans hProd)
  · intro L hL
    exact (card_le_card (mem_balancedRemainders.mp hL).2.1).trans hProd

end OverfullWork.ChenShan
