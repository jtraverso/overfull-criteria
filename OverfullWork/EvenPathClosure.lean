module

public import OverfullWork.HeavyPairPathPacking
public import OverfullWork.TwoColourTrimming

@[expose] public section


/-! # Close an even spanning ordinary path with two new vertices

CMS Theorem 4.2, Case 1 closes a path u--v by a--u, v--b, b--a.
The colouring is constructed on the actual multigraph. Handshaking
forces the same missing colour at both path ends; no colouring of the
closed layer is assumed.
-/
namespace OverfullWork.EvenPathClosure
open SimpleGraph Finset HeavyPairBoundary
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

theorem full_two_colour_degree {M : MultiGraph V} (C : M.EdgeColoring 2)
    (w : V) (hd : M.degree w = 2) (i : Fin 2) : (C.colourGraph i).degree w = 1 := by
  have hs := C.sum_colour_degree w
  simp only [Fin.sum_univ_two, hd] at hs
  have h0 := C.colourGraph_degree_le_one 0 w
  have h1 := C.colourGraph_degree_le_one 1 w
  have hz : (C.colourGraph 0).degree w = 1 := by omega
  have ho : (C.colourGraph 1).degree w = 1 := by omega
  fin_cases i
  · exact hz
  · exact ho

theorem isolated_colour_degree {M : MultiGraph V} (C : M.EdgeColoring 2)
    (w : V) (hd : M.degree w = 0) (i : Fin 2) : (C.colourGraph i).degree w = 0 := by
  have hs := C.sum_colour_degree w
  simp only [Fin.sum_univ_two, hd] at hs
  have hz : (C.colourGraph 0).degree w = 0 := by omega
  have ho : (C.colourGraph 1).degree w = 0 := by omega
  fin_cases i
  · exact hz
  · exact ho

theorem same_missing_colour {M : MultiGraph V} (C : M.EdgeColoring 2)
    (a b : V) (hab : a ≠ b) (u v : outside a b) (huv : u ≠ v)
    (heven : Even (Fintype.card V))
    (hdegree : ∀ w, M.degree w = if w = a ∨ w = b then 0
      else if w = u.val ∨ w = v.val then 1 else 2)
    (i : Fin 2) (hu : (C.colourGraph i).degree u.val = 0) :
    (C.colourGraph i).degree v.val = 0 := by
  have hua := (mem_outside a b u.val).mp u.property
  have hva := (mem_outside a b v.val).mp v.property
  have huvval : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  have ha : (C.colourGraph i).degree a = 0 :=
    isolated_colour_degree C a (by simp [hdegree]) i
  have hb : (C.colourGraph i).degree b = 0 :=
    isolated_colour_degree C b (by simp [hdegree]) i
  by_contra hv
  have hset : C.missingSet univ i = {a,b,u.val} := by
    ext w
    simp only [MultiGraph.EdgeColoring.missingSet, mem_filter, mem_univ, true_and,
      mem_insert, mem_singleton]
    constructor
    · intro hw
      by_cases hwa : w = a
      · exact Or.inl hwa
      by_cases hwb : w = b
      · exact Or.inr (Or.inl hwb)
      by_cases hwu : w = u.val
      · exact Or.inr (Or.inr hwu)
      by_cases hwv : w = v.val
      · exact False.elim (hv (hwv ▸ hw))
      have hd : M.degree w = 2 := by simp [hdegree, hwa, hwb, hwu, hwv]
      have hf := full_two_colour_degree C w hd i
      omega
    · rintro (rfl | rfl | rfl)
      · exact ha
      · exact hb
      · exact hu
  have hm := C.missing_card_add_degree_sum univ i
  rw [hset, card_insert_of_notMem (by simp [hab, hua.1.symm]),
    card_pair hua.2.symm, card_univ, (C.colourGraph i).sum_degrees_eq_twice_edgeCount] at hm
  obtain ⟨k,hk⟩ := heven
  omega

def closure (M : MultiGraph V) (a b : V) (hab : a ≠ b) (u v : outside a b) : MultiGraph V :=
  ((M.addCopies (MultiGraph.unitEdge a u.val
      ((mem_outside a b u.val).mp u.property).1.symm)).addCopies
    (MultiGraph.unitEdge b v.val ((mem_outside a b v.val).mp v.property).2.symm)).addCopies
    (MultiGraph.unitEdge a b hab)

theorem closure_mult_ordinary (M : MultiGraph V) (a b : V) (hab : a ≠ b)
    (u v x y : outside a b) :
    (closure M a b hab u v).mult s(x.val,y.val) = M.mult s(x.val,y.val) := by
  have hx := (mem_outside a b x.val).mp x.property
  have hy := (mem_outside a b y.val).mp y.property
  simp [closure, MultiGraph.addCopies, MultiGraph.unitEdge, Sym2.eq_iff, hx, hy]

theorem closure_mult_left (M : MultiGraph V) (a b : V) (hab : a ≠ b)
    (u v w : outside a b) (hzero : M.degree a = 0) :
    (closure M a b hab u v).mult s(a,w.val) = if w = u then 1 else 0 := by
  have hu := (mem_outside a b u.val).mp u.property
  have hv := (mem_outside a b v.val).mp v.property
  have hw := (mem_outside a b w.val).mp w.property
  have hz : M.mult s(a,w.val) = 0 := by
    have hh := M.mult_pair_le_degree a w.val
    omega
  have heq : w.val = u.val ↔ w = u := Subtype.val_inj
  simp [closure, MultiGraph.addCopies, MultiGraph.unitEdge, Sym2.eq_iff,
    hab, hu.1.symm, hv.1.symm, hw.2, hz, heq]

theorem closure_mult_right (M : MultiGraph V) (a b : V) (hab : a ≠ b)
    (u v w : outside a b) (hzero : M.degree b = 0) :
    (closure M a b hab u v).mult s(b,w.val) = if w = v then 1 else 0 := by
  have hu := (mem_outside a b u.val).mp u.property
  have hv := (mem_outside a b v.val).mp v.property
  have hw := (mem_outside a b w.val).mp w.property
  have hz : M.mult s(b,w.val) = 0 := by
    have hh := M.mult_pair_le_degree b w.val
    omega
  have heq : w.val = v.val ↔ w = v := Subtype.val_inj
  simp [closure, MultiGraph.addCopies, MultiGraph.unitEdge, Sym2.eq_iff,
    hab.symm, hu.2.symm, hv.2.symm, hw.1, hz, heq]

theorem closure_mult_pair (M : MultiGraph V) (a b : V) (hab : a ≠ b)
    (u v : outside a b) (hzero : M.degree a = 0) :
    (closure M a b hab u v).mult s(a,b) = 1 := by
  have hu := (mem_outside a b u.val).mp u.property
  have hv := (mem_outside a b v.val).mp v.property
  have hz : M.mult s(a,b) = 0 := by
    have hh := M.mult_pair_le_degree a b
    omega
  simp [closure, MultiGraph.addCopies, MultiGraph.unitEdge, Sym2.eq_iff,
    hab, hu.1.symm, hu.2.symm, hv.1.symm, hz]

theorem closure_regular (M : MultiGraph V) (a b : V) (hab : a ≠ b)
    (u v : outside a b) (huv : u ≠ v)
    (hdegree : ∀ w, M.degree w = if w = a ∨ w = b then 0
      else if w = u.val ∨ w = v.val then 1 else 2) :
    (closure M a b hab u v).IsRegularOfDegree 2 := by
  have hua := (mem_outside a b u.val).mp u.property
  have hva := (mem_outside a b v.val).mp v.property
  have huvval : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  intro w
  simp only [closure, MultiGraph.degree_addCopies, MultiGraph.degree_unitEdge, hdegree]
  by_cases ha : w = a
  · subst w; simp [hab, hua.1.symm, hva.1.symm]
  by_cases hb : w = b
  · subst w; simp [hab.symm, hua.2.symm, hva.2.symm]
  by_cases hu : w = u.val
  · subst w; simp [hua.1, hua.2, huvval]
  by_cases hv : w = v.val
  · subst w; simp [hva.1, hva.2, huvval.symm]
  simp [ha, hb, hu, hv]

/-- Construct the two colours of the closed layer from the path colouring. -/
theorem closure_colourable {M : MultiGraph V} (C : M.EdgeColoring 2)
    (a b : V) (hab : a ≠ b) (u v : outside a b) (huv : u ≠ v)
    (heven : Even (Fintype.card V))
    (hdegree : ∀ w, M.degree w = if w = a ∨ w = b then 0
      else if w = u.val ∨ w = v.val then 1 else 2) :
    Nonempty ((closure M a b hab u v).EdgeColoring 2) := by
  have hua := (mem_outside a b u.val).mp u.property
  have hva := (mem_outside a b v.val).mp v.property
  have huvval : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  have huDeg : M.degree u.val = 1 := by simp [hdegree, hua.1, hua.2]
  have hmissing := C.missingPalette_card_add_degree u.val
  rw [huDeg] at hmissing
  obtain ⟨i,hi⟩ := card_pos.mp (show 0 < (C.missingPalette u.val).card by omega)
  have hmi : (C.colourGraph i).degree u.val = 0 := (mem_filter.mp hi).2
  have hmv := same_missing_colour C a b hab u v huv heven hdegree i hmi
  let U := MultiGraph.unitEdge a u.val hua.1.symm
  let W := MultiGraph.unitEdge b v.val hva.2.symm
  let T := MultiGraph.unitEdge a b hab
  refine ⟨{
    col := fun e j => C.col e j + (if j = i then U.mult e + W.mult e else T.mult e)
    sum_col := ?_
    proper := ?_
  }⟩
  · intro e
    rw [sum_add_distrib, C.sum_col]
    have hs : (∑ j : Fin 2, if j = i then U.mult e + W.mult e else T.mult e) =
        U.mult e + W.mult e + T.mult e := by
      fin_cases i <;> simp [Fin.sum_univ_two] <;> omega
    rw [hs]
    change M.mult e + (U.mult e + W.mult e + T.mult e) =
      M.mult e + U.mult e + W.mult e + T.mult e
    omega
  · intro w j
    by_cases hj : j = i
    · subst j
      simp only [ite_true, sum_add_distrib]
      change (C.colourGraph i).degree w + (U.degree w + W.degree w) ≤ 1
      have hp := C.colourGraph_degree_le_one i w
      have hca := isolated_colour_degree C a (by simp [hdegree]) i
      have hcb := isolated_colour_degree C b (by simp [hdegree]) i
      dsimp only [U,W]
      rw [MultiGraph.degree_unitEdge, MultiGraph.degree_unitEdge]
      by_cases ha : w = a
      · subst w; simp [hca, hab, hua.1.symm, hva.1.symm]
      by_cases hb : w = b
      · subst w; simp [hcb, hab.symm, hua.2.symm, hva.2.symm]
      by_cases hu : w = u.val
      · subst w; simp [hmi, hua.1, hua.2, huvval]
      by_cases hv : w = v.val
      · subst w; simp [hmv, hva.1, hva.2, huvval.symm]
      simpa [ha,hb,hu,hv] using hp
    · simp only [if_neg hj, sum_add_distrib]
      change (C.colourGraph j).degree w + T.degree w ≤ 1
      dsimp only [T]
      rw [MultiGraph.degree_unitEdge]
      by_cases hw : w = a ∨ w = b
      · rw [if_pos hw]
        rcases hw with hwa | hwb
        · rw [hwa, isolated_colour_degree C a (by simp [hdegree]) j]
        · rw [hwb, isolated_colour_degree C b (by simp [hdegree]) j]
      · rw [if_neg hw, add_zero]
        exact C.colourGraph_degree_le_one j w

end OverfullWork.EvenPathClosure
