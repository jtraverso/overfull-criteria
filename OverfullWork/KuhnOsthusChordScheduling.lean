module

public import OverfullWork.KuhnOsthusChordRoutes
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.List.Count

@[expose] public section


/-! Choose short routes successively with bounded interior congestion.
The cost counts the two cluster endpoints of an interior shifted
position separately, even when both contribute to the same cluster. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {I J W : Type*} [Fintype I] [Fintype J] [Inhabited W]

/-- If the total previous load can saturate at most `budget` clusters,
choose the next object avoiding all saturated clusters. -/
theorem exists_saturation_avoiding_selection
    (ok : J → W → Prop) (cost : W → I → ℕ)
    (cap mass increment budget : ℕ)
    (hBudget : Fintype.card J * mass < cap * (budget+1))
    (hMass : ∀ j w, ok j w → ∑ i, cost w i ≤ mass)
    (hInc : ∀ j w, ok j w → ∀ i, cost w i ≤ increment)
    (hPick : ∀ j (Z : Finset I), Z.card ≤ budget →
      ∃ w, ok j w ∧ ∀ i ∈ Z, cost w i = 0) :
    ∃ f : J → W, (∀ j, ok j (f j)) ∧
      ∀ i, (∑ j, cost (f j) i) ≤ cap + increment := by
  classical
  have hStep (P : Finset J) : ∃ f : J → W, (∀ j ∈ P, ok j (f j)) ∧
      ∀ i, (∑ j ∈ P, cost (f j) i) ≤ cap + increment := by
    induction P using Finset.induction_on with
    | empty => exact ⟨fun _ => default,by simp,by simp⟩
    | @insert j P hj ih =>
      obtain ⟨f,hf,hLoad⟩ := ih
      let u (i : I) := ∑ p ∈ P, cost (f p) i
      let Z := univ.filter (fun i => cap ≤ u i)
      have hSat : cap*Z.card ≤ ∑ i, u i := by
        calc
          cap*Z.card = ∑ _i ∈ Z, cap := by simp [mul_comm]
          _ ≤ ∑ i ∈ Z, u i := sum_le_sum (fun _ h => (mem_filter.mp h).2)
          _ ≤ ∑ i, u i := sum_le_sum_of_subset (subset_univ _)
      have hTotal : (∑ i, u i) ≤ Fintype.card J * mass := by
        dsimp only [u]
        rw [sum_comm]
        exact (sum_le_sum (fun p hp => hMass p (f p) (hf p hp))).trans
          (by simpa using Nat.mul_le_mul_right mass (card_le_univ P))
      have hZ : Z.card ≤ budget := by
        by_contra! h
        exact (not_lt_of_ge ((Nat.mul_le_mul_left cap (by omega : budget+1 ≤ Z.card)).trans
          (hSat.trans hTotal))) hBudget
      obtain ⟨w,hw,hAvoid⟩ := hPick j Z hZ
      let g := Function.update f j w
      have hSame (p : J) (hp : p ∈ P) : g p = f p := by
        have hne : p ≠ j := fun h => hj (h ▸ hp)
        exact Function.update_of_ne hne _ _
      refine ⟨g,?_,?_⟩
      · intro p hp
        rcases mem_insert.mp hp with rfl | hp
        · simpa only [g,Function.update_self] using hw
        · rw [hSame _ hp]
          exact hf _ hp
      · intro i
        rw [sum_insert hj]
        have he : (∑ p ∈ P, cost (g p) i) = u i :=
          sum_congr rfl (fun p hp => congrArg (fun w => cost w i) (hSame p hp))
        rw [he,show g j = w from Function.update_self _ _ _]
        by_cases hz : i ∈ Z
        · rw [hAvoid i hz,zero_add]
          exact hLoad i
        · have hSmall : ¬ cap ≤ u i := fun h => hz (mem_filter.mpr ⟨mem_univ _,h⟩)
          have hInc' := hInc j w hw i
          omega
  obtain ⟨f,hf,hLoad⟩ := hStep (univ : Finset J)
  exact ⟨f,fun j => hf j (mem_univ _),hLoad⟩

noncomputable def chordInteriorLoad (s : Equiv.Perm I) (l : List I) (i : I) : ℕ :=
  l.dropLast.count i + l.dropLast.count (s i)

private theorem sum_count_vertices (l : List I) : (∑ i, l.count i) = l.length := by
  classical
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons,List.length_cons,sum_add_distrib,ih]
    have h : (∑ i : I, if a == i then (1:ℕ) else 0) = 1 := by
      simp only [beq_iff_eq,sum_ite_eq,mem_univ,if_true]
    omega

/-- Choose one short chord route for each requested pair of clusters.
Only the global mass of the interiors is used to bound how many
clusters must be avoided at each step. -/
theorem exists_chord_routes_with_bounded_interior_load
    (R : Digraph I) (s : Equiv.Perm I) (a b : J → I)
    (r g t cap budget : ℕ) (hRobust : IsRobustAt R r t) (hg : 0 < g)
    (hAvoid : 2*budget+g ≤ r)
    (hOut : ∀ j, t+2*budget ≤ outDegree R (s.symm (a j)))
    (hIn : ∀ j, t ≤ inDegree R (b j))
    (hMass : Fintype.card J * (2*(Fintype.card I/g+3)) < cap*(budget+1)) :
    ∃ f : J → List I,
      (∀ j, DirectedListRoutes.Route (reindexSources R s.symm) (a j) (b j) (f j) ∧
        (a j :: f j).Nodup ∧ (f j).length ≤ Fintype.card I/g+3) ∧
      ∀ i, (∑ j, chordInteriorLoad s (f j) i) ≤ cap+2 := by
  classical
  let ok (j : J) (l : List I) :=
    DirectedListRoutes.Route (reindexSources R s.symm) (a j) (b j) l ∧
      (a j :: l).Nodup ∧ l.length ≤ Fintype.card I/g+3
  apply exists_saturation_avoiding_selection ok (chordInteriorLoad s) cap _ 2 budget hMass
  · intro j l hl
    simp only [chordInteriorLoad,sum_add_distrib]
    rw [Equiv.sum_comp s (fun i => l.dropLast.count i),sum_count_vertices,List.length_dropLast]
    have h := hl.2.2
    omega
  · intro j l hl i
    have hlN : l.dropLast.Nodup := hl.2.1.of_cons.sublist (List.dropLast_sublist _)
    exact Nat.add_le_add (List.nodup_iff_count_le_one.mp hlN i)
      (List.nodup_iff_count_le_one.mp hlN (s i))
  · intro j Z hZ
    obtain ⟨l,hRoute,hNodup,hLength,hFree⟩ := exists_short_chord_route R s Z r g t
      hRobust hg (by omega) (a j) (b j) ((by omega : t+2*Z.card ≤ t+2*budget).trans (hOut j))
      (hIn j)
    refine ⟨l,⟨hRoute,hNodup,hLength⟩,fun i hi => ?_⟩
    have h₁ : i ∉ l.dropLast := fun h => (hFree i h).1 hi
    have h₂ : s i ∉ l.dropLast := fun h => (hFree (s i) h).2 (by simpa using hi)
    simp [chordInteriorLoad,List.count_eq_zero_of_not_mem h₁,List.count_eq_zero_of_not_mem h₂]

/-- Source clusters of the actual chords. The tail gives their target
clusters in the same order. -/
def chordSources (s : Equiv.Perm I) (a : I) (l : List I) : List I :=
  ((a :: l).dropLast).map s.symm

/-- The actual incidence load is interior load plus at most one request
at each endpoint. A request with no chords pays neither endpoint. -/
theorem chord_endpoint_load_le (R : Digraph I) (s : Equiv.Perm I) (a b : I)
    (l : List I) (h : DirectedListRoutes.Route (reindexSources R s.symm) a b l) (i : I) :
    (chordSources s a l).count i + l.count i ≤ chordInteriorLoad s l i +
      (if s.symm a = i then 1 else 0) + (if b = i then 1 else 0) := by
  classical
  cases l with
  | nil => simp [chordSources,chordInteriorLoad]
  | cons v l =>
    have hb : (v :: l).getLast? = some b := by
      simpa only [List.getLast?_cons_cons] using h.2
    have hl : (v :: l).dropLast ++ [b] = v :: l :=
      List.dropLast_append_getLast? b (by simp [hb])
    have hm : (((v :: l).dropLast).map s.symm).count i = (v :: l).dropLast.count (s i) := by
      simpa only [Equiv.symm_apply_apply] using
        List.count_map_of_injective ((v :: l).dropLast) s.symm s.symm.injective (s i)
    have ht : (v :: l).count i = (v :: l).dropLast.count i + (if b = i then 1 else 0) := by
      conv_lhs => rw [←hl]
      simp only [List.count_append,List.count_cons,List.count_nil,zero_add,beq_iff_eq]
    have hs : (chordSources s a (v :: l)).count i =
        (v :: l).dropLast.count (s i) + (if s.symm a = i then 1 else 0) := by
      simp only [chordSources,List.dropLast_cons_cons,List.map_cons,List.count_cons,hm,beq_iff_eq]
    rw [hs,ht]
    unfold chordInteriorLoad
    omega

/-- Equation (8.2) in integer form, using bounds on the interior and
the two endpoint contributions separately. -/
theorem chord_endpoint_budget (R : Digraph I) (s : Equiv.Perm I)
    (a b : J → I) (l : J → List I) (m : ℕ)
    (hRoute : ∀ j, DirectedListRoutes.Route (reindexSources R s.symm) (a j) (b j) (l j))
    (hInt : ∀ i, 100*(∑ j, chordInteriorLoad s (l j) i) ≤ m)
    (hFrom : ∀ i, 10*(∑ j, if s.symm (a j) = i then (1:ℕ) else 0) ≤ m)
    (hTo : ∀ i, 10*(∑ j, if b j = i then (1:ℕ) else 0) ≤ m) :
    ∀ i, 100*(∑ j, ((chordSources s (a j) (l j)).count i + (l j).count i)) ≤ 21*m := by
  intro i
  have h := sum_le_sum (s := univ) (fun j _ => chord_endpoint_load_le R s (a j) (b j) (l j) (hRoute j) i)
  simp only [sum_add_distrib] at h ⊢
  have hl := hInt i
  have ha := hFrom i
  have hb := hTo i
  omega

end OverfullWork.DirectedRobustExpansion
