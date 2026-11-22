module

public import OverfullWork.MergePathExpansion
public import OverfullWork.RankedDirectedPathCover
public import OverfullWork.PrefactorOpenOrbit

@[expose] public section


/-! Cut a directed 1-factor at a selected set of outgoing arcs.
Each orbit meeting the cut becomes a disjoint family of paths. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset Function DirectedAbsorbingLadder RankedDirectedPathCover
open scoped Classical
variable {V : Type*} [Fintype V]

def cutFactor (σ : Equiv.Perm V) (S : Set V) : Digraph V :=
  ⟨fun x y => x ∉ S ∧ σ x = y⟩

private theorem terminal_iff (R : V → V → Prop) (t : V) :
    t ∈ terminals R univ ↔ ∀ w, ¬ R t w := by simp [terminals]

theorem exists_cut_factor_paths (σ : Equiv.Perm V) (S : Finset V)
    (hHit : ∀ v, ∃ w ∈ S, σ.SameCycle v w) :
    ∃ P : S → PathRequest (cutFactor σ S), ∃ e : Equiv.Perm (↑S),
      (∀ i, (P i).target = i.val ∧ (P i).source = σ (e i).val) ∧
      (∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices) ∧
      (∀ v, ∃ i, v ∈ (P i).vertices) := by
  let D := cutFactor σ (S : Set V)
  let f : V → V := σ
  have hEx (v : V) : ∃ i : ℕ, f^[i] v ∈ S := by
    obtain ⟨w,hw,h⟩ := hHit v
    obtain ⟨i,_,he⟩ := h.exists_pow_eq'
    exact ⟨i,by simpa only [f,←Equiv.Perm.coe_pow,he] using hw⟩
  let dist (v : V) := Nat.find (hEx v)
  let bound := (univ : Finset V).sup dist
  have hB (v : V) : dist v ≤ bound := le_sup (mem_univ v)
  have hSucc {x y : V} (h : D.Adj x y) : dist x = dist y+1 := by
    obtain ⟨hx,he⟩ := h
    have hxy : f x = y := he
    have hFirst : f^[dist y] y ∈ S := Nat.find_spec (hEx y)
    have hUp : dist x ≤ dist y+1 := by
      apply Nat.find_min'
      rw [iterate_succ_apply,hxy]
      exact hFirst
    have hPos : 0 < dist x := by
      by_contra! hn
      have h0 : dist x = 0 := Nat.eq_zero_of_le_zero hn
      have hSpec : f^[dist x] x ∈ S := Nat.find_spec (hEx x)
      rw [h0,iterate_zero_apply] at hSpec
      exact hx hSpec
    have hDown : dist y ≤ dist x-1 := by
      apply Nat.find_min'
      have hh : f^[dist x] x ∈ S := Nat.find_spec (hEx x)
      have hEq : dist x = (dist x-1)+1 := by omega
      rw [hEq,iterate_succ_apply,hxy] at hh
      exact hh
    omega
  obtain ⟨C⟩ := exists_cover D.Adj (fun x => bound-dist x)
    (fun {x y} h => by have h' := hSucc h; have hx := hB x; omega)
    (fun h h' => σ.injective (h.2.trans h'.2.symm)) univ
  have hTerm (t : V) : t ∈ terminals D.Adj univ ↔ t ∈ S := by
    rw [terminal_iff]
    constructor
    · intro ht
      by_contra h
      exact ht (σ t) ⟨h,rfl⟩
    · exact fun h _ hw => hw.1 h
  have hPath (i : S) : ∃ P : PathRequest D, P.vertices = C.path i.val ∧ P.target = i.val := by
    have hi := (hTerm i.val).mpr i.prop
    have he := C.ends i.val hi
    have hs := C.simple i.val hi
    have hc := C.chain i.val hi
    cases hb : C.path i.val with
    | nil => simp [hb] at he
    | cons x L =>
      rw [hb] at he hs hc
      exact ⟨⟨x,i.val,L,⟨hc,he⟩,hs⟩,rfl,rfl⟩
  choose P hP hEnd using hPath
  have hDis (i j : S) (hne : i ≠ j) : List.Disjoint (P i).vertices (P j).vertices := by
    rw [hP,hP]
    exact C.disjoint _ ((hTerm _).mpr i.prop) _ ((hTerm _).mpr j.prop)
      (fun h => hne (Subtype.ext h))
  have hCover (v : V) : ∃ i : S, v ∈ (P i).vertices := by
    obtain ⟨t,ht,hm⟩ := C.covers v (mem_univ _)
    exact ⟨⟨t,(hTerm _).mp ht⟩,by rw [hP]; exact hm⟩
  have hPred (i : S) : σ.symm (P i).source ∈ S := by
    let x := (P i).source
    let y := σ.symm x
    by_contra hy
    have hArc : D.Adj y x := ⟨hy,σ.apply_symm_apply x⟩
    obtain ⟨t,ht,hinfix⟩ := C.arc_occurs (fun h h' => h.2.symm.trans h'.2)
      (mem_univ y) (mem_univ x) hArc
    have hx : x ∈ C.path i.val := hP i ▸ List.mem_cons_self ..
    obtain ⟨A,B,hAB⟩ := hinfix
    have hx' : x ∈ C.path t := by rw [←hAB]; simp
    have he : t = i.val := by
      by_contra h
      exact C.disjoint t ht i.val ((hTerm _).mpr i.prop) h hx' hx
    subst t
    have hEq : A ++ [y,x] ++ B = x :: (P i).tail := hAB.trans (hP i).symm
    have hTail : x ∈ (P i).tail := by
      cases A with
      | nil =>
        have hh := (List.cons.inj (by simpa using hEq : y :: x :: B = x :: (P i).tail)).2
        rw [←hh]
        simp
      | cons a A =>
        have hh := (List.cons.inj (by simpa using hEq :
          a :: ((A ++ [y,x]) ++ B) = x :: (P i).tail)).2
        rw [←hh]
        simp
    exact (List.nodup_cons.mp (P i).simple).1 hTail
  let g : S → S := fun i => ⟨σ.symm (P i).source,hPred i⟩
  have hg : Injective g := by
    intro i j h
    by_contra hij
    have he : (P i).source = (P j).source := σ.symm.injective (congrArg Subtype.val h)
    exact hDis i j hij (List.mem_cons_self ..) (he.symm ▸ List.mem_cons_self ..)
  let e := Equiv.ofBijective g ⟨hg,Finite.surjective_of_injective hg⟩
  exact ⟨P,e,fun i => ⟨hEnd i,(σ.apply_symm_apply _).symm⟩,hDis,hCover⟩

end OverfullWork.DirectedRobustExpansion
