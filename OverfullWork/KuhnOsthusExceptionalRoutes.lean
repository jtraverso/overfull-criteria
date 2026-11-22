module

public import OverfullWork.KuhnOsthusChordScheduling
public import OverfullWork.OsthusStadenShadowExpansion
public import OverfullWork.DenseHall

@[expose] public section


/-! Reduced routes on the wrapped interval in Kühn–Osthus Lemma 7.5(ii).
The interval comprises complete winding rounds. Chord interiors avoid
its boundary in addition to the clusters saturated by previous routes. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- The induced reduced graph on whole winding rounds is a uniform
blow-up. Its degree and robust expansion come from the coarse graph. -/
theorem winding_interval_reduced_expansion {U I : Type*} [Fintype U]
    (R : Digraph U) (D : Digraph I) (base : I → U) (T : Finset I) (b : ℕ)
    (hb : 0 < b) (hFibres : ∀ u, (T.filter (fun i => base i = u)).card = b)
    (hAdj : ∀ x ∈ T, ∀ y ∈ T, D.Adj x y ↔ R.Adj (base x) (base y))
    (ν τ : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/4)
    (hOrder : 2 ≤ τ*(Fintype.card U:ℝ)) (hR : IsRealRobust R ν τ) :
    let H : Digraph T := ⟨fun x y => D.Adj x y⟩
    IsRealRobust H (ν^2/2) (2*τ) ∧
      ∀ x : T, inDegree H x = inDegree R (base x)*b ∧
        outDegree H x = outDegree R (base x)*b := by
  classical
  dsimp only
  let p (x : T) := base x
  have hFib (u : U) : fibreWeight p univ u = b := by
    unfold fibreWeight
    rw [DenseHall.subtype_filter_card T (fun i => base i = u)]
    exact hFibres u
  have hGraph : (⟨fun x y : T => D.Adj x y⟩ : Digraph T) = fibrePullback R p p := by
    ext x y
    exact hAdj x x.prop y y.prop
  rw [hGraph]
  exact ⟨fibrePullback_realRobust R p p b hFib hFib hb ν τ hν hντ hτ hOrder hR,
    fibrePullback_semidegrees R p p b hFib hFib⟩

/-- Route the endpoint requests inside the wrapped interval. The fixed
boundary set is forbidden even when its current load is zero. -/
theorem exists_exceptional_interval_chord_routes {I J : Type*} [Fintype I] [Fintype J]
    (R : Digraph I) (s : Equiv.Perm I) (a b : J → I) (boundary : Finset I)
    (r g t cap budget : ℕ) (hRobust : IsRobustAt R r t) (hg : 0 < g)
    (hAvoid : 2*(budget+boundary.card)+g ≤ r)
    (hOut : ∀ j, t+2*(budget+boundary.card) ≤ outDegree R (s.symm (a j)))
    (hIn : ∀ j, t ≤ inDegree R (b j))
    (hMass : Fintype.card J * (2*(Fintype.card I/g+3)) < cap*(budget+1)) :
    ∃ f : J → List I,
      (∀ j, DirectedListRoutes.Route (reindexSources R s.symm) (a j) (b j) (f j) ∧
        (a j :: f j).Nodup ∧ (f j).length ≤ Fintype.card I/g+3 ∧
        ∀ v ∈ (f j).dropLast, v ∉ boundary ∧ s.symm v ∉ boundary) ∧
      ∀ i, (∑ j, chordInteriorLoad s (f j) i) ≤ cap+2 := by
  classical
  let ok (j : J) (l : List I) :=
    DirectedListRoutes.Route (reindexSources R s.symm) (a j) (b j) l ∧
      (a j :: l).Nodup ∧ l.length ≤ Fintype.card I/g+3 ∧
      ∀ v ∈ l.dropLast, v ∉ boundary ∧ s.symm v ∉ boundary
  apply exists_saturation_avoiding_selection ok (chordInteriorLoad s) cap _ 2 budget hMass
  · intro j l hl
    have hcount : (∑ i : I,l.dropLast.count i) = l.dropLast.length := by
      simpa using Multiset.sum_count_eq_card
        (s := (univ : Finset I)) (m := (↑l.dropLast : Multiset I)) (fun i _ => mem_univ i)
    simp only [chordInteriorLoad,sum_add_distrib]
    rw [Equiv.sum_comp s (fun i => l.dropLast.count i),hcount,List.length_dropLast]
    have h := hl.2.2.1
    omega
  · intro j l hl i
    have hlN : l.dropLast.Nodup := hl.2.1.of_cons.sublist (List.dropLast_sublist _)
    exact Nat.add_le_add (List.nodup_iff_count_le_one.mp hlN i)
      (List.nodup_iff_count_le_one.mp hlN (s i))
  · intro j Z hZ
    let B := Z ∪ boundary
    have hB : B.card ≤ budget+boundary.card :=
      (card_union_le Z boundary).trans (Nat.add_le_add_right hZ _)
    obtain ⟨l,hRoute,hNodup,hLength,hFree⟩ := exists_short_chord_route R s B r g t
      hRobust hg (by omega) (a j) (b j)
      ((by omega : t+2*B.card ≤ t+2*(budget+boundary.card)).trans (hOut j)) (hIn j)
    refine ⟨l,⟨hRoute,hNodup,hLength,?_⟩,?_⟩
    · intro v hv
      exact ⟨fun h => (hFree v hv).1 (mem_union_right _ h),
        fun h => (hFree v hv).2 (mem_union_right _ h)⟩
    · intro i hi
      have hBi : i ∈ B := mem_union_left _ hi
      have h₁ : i ∉ l.dropLast := fun h => (hFree i h).1 hBi
      have h₂ : s i ∉ l.dropLast := fun h => (hFree (s i) h).2 (by simpa using hBi)
      simp [chordInteriorLoad,List.count_eq_zero_of_not_mem h₁,List.count_eq_zero_of_not_mem h₂]

/-- The two unshifted endpoint loads of the chord requests cost at
most twice the exceptional endpoint cap. -/
theorem exceptional_endpoint_chord_load {V I E : Type*} [Fintype E]
    (s : Equiv.Perm I) (cluster : V → I) (endpoint : Bool × E → V) (cap : ℕ)
    (hCap : ∀ i, ((univ : Finset (Bool × E)).filter (fun p => cluster (endpoint p) = i)).card ≤ cap) :
    ∀ i, (∑ z : E, if s.symm (cluster (endpoint (true,z))) = i then (1:ℕ) else 0) +
      (∑ z : E, if s (cluster (endpoint (false,z))) = i then (1:ℕ) else 0) ≤ 2*cap := by
  classical
  have hHalf (b : Bool) (p : Equiv.Perm I) (i : I) :
      (∑ z : E, if p (cluster (endpoint (b,z))) = i then (1:ℕ) else 0) ≤ cap := by
    rw [← card_filter]
    refine (card_le_card_of_injOn (fun z => (b,z)) ?_ ?_).trans (hCap (p.symm i))
    · intro z hz
      have h := (mem_filter.mp hz).2
      exact mem_filter.mpr ⟨mem_univ _,p.eq_symm_apply.mpr h⟩
    · intro z _ z' _ h
      exact congrArg Prod.snd h
  intro i
  have h₁ := hHalf true s.symm i
  have h₂ := hHalf false s i
  omega

/-- The fixed boundary receives no physical chord endpoints when both
endpoints of the request and all shifted interior positions avoid it. -/
theorem chord_has_no_boundary_incidence {I : Type*} [Fintype I]
    (R : Digraph I) (s : Equiv.Perm I) (a b : I) (l : List I)
    (B : Finset I) (h : DirectedListRoutes.Route (reindexSources R s.symm) a b l)
    (ha : s.symm a ∉ B) (hb : b ∉ B)
    (hInt : ∀ v ∈ l.dropLast, v ∉ B ∧ s.symm v ∉ B) :
    ∀ i ∈ B, (chordSources s a l).count i + l.count i = 0 := by
  classical
  intro i hi
  have h₁ : i ∉ l.dropLast := fun h => (hInt i h).1 hi
  have h₂ : s i ∉ l.dropLast := fun h => (hInt (s i) h).2 (by simpa using hi)
  have ho : s.symm a ≠ i := fun h => ha (h.symm ▸ hi)
  have he : b ≠ i := fun h => hb (h.symm ▸ hi)
  have hh := chord_endpoint_load_le R s a b l h i
  simpa [chordInteriorLoad,List.count_eq_zero_of_not_mem h₁,
    List.count_eq_zero_of_not_mem h₂,ho,he] using hh

end OverfullWork.DirectedRobustExpansion
