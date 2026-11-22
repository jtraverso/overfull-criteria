module

public import OverfullWork.DirectedRobustShortPaths
public import OverfullWork.MergeReserveReindex

@[expose] public section


/-! Kühn–Osthus Lemma 7.2. A chord sequence is a route in the digraph
obtained by shifting the source labels by one cyclic position. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedListRoutes
open scoped Classical
variable {I : Type*} [Fintype I]

theorem reindexSources_robust (R : Digraph I) (e : Equiv.Perm I) (r t : ℕ)
    (hR : IsRobustAt R r t) : IsRobustAt (reindexSources R e) r t := by
  intro S hlo hhi
  have hc : (S.image e).card = S.card := card_image_of_injective _ e.injective
  have hs : neighbourhood (reindexSources R e) r S = neighbourhood R r (S.image e) := by
    ext v
    have h := reindexSources_incidences R e S {v}
    simp only [incidences,sum_singleton] at h
    simp only [neighbourhood,mem_filter,mem_univ,true_and,h]
  rw [hs,←hc]
  exact hR _ (by rwa [hc]) (by rwa [hc])

/-- Interior shifted vertices and their predecessors both avoid the
forbidden set. The first tail vertex ends the first chord, and the last
tail vertex ends the last chord. The path may be empty. -/
theorem exists_short_chord_route (R : Digraph I) (s : Equiv.Perm I) (Z : Finset I)
    (r g t : ℕ) (hRobust : IsRobustAt R r t) (hg : 0 < g)
    (hBudget : 2*Z.card+g ≤ r) (a b : I)
    (ha : t+2*Z.card ≤ outDegree R (s.symm a)) (hb : t ≤ inDegree R b) :
    ∃ l, Route (reindexSources R s.symm) a b l ∧ (a :: l).Nodup ∧
      l.length ≤ Fintype.card I/g+3 ∧
      ∀ v ∈ l.dropLast, v ∉ Z ∧ s.symm v ∉ Z := by
  classical
  by_cases he : a = b
  · subst b
    exact ⟨[],nil_route _ _,by simp,by simp,by simp⟩
  let X := (Z ∪ Z.image s) \ {a,b}
  have hX : X.card ≤ 2*Z.card := by
    apply (card_le_card (sdiff_subset (s := Z ∪ Z.image s) (t := {a,b}))).trans
    exact (card_union_le _ _).trans (by rw [card_image_of_injective _ s.injective]; omega)
  have hx : a ∉ X := fun h => (mem_sdiff.mp h).2 (by simp)
  have hy : b ∉ X := fun h => (mem_sdiff.mp h).2 (by simp)
  obtain ⟨l,hl,hND,hLen,hAvoid⟩ :=
    DirectedRobustShortPaths.exists_short_path_avoiding (reindexSources R s.symm) X r g t
      (reindexSources_robust R s.symm r t hRobust) hg (by omega) a b hx hy
      (by rw [(reindexSources_semidegrees R s.symm a).2]; omega)
      (by rwa [(reindexSources_semidegrees R s.symm b).1])
  refine ⟨l,hl,hND,hLen,?_⟩
  have hlne : l ≠ [] := by
    intro h
    have hh := hl.2
    rw [h] at hh
    exact he (Option.some.inj hh)
  have hbLast : l.getLast? = some b := by
    cases l with
    | nil => exact (hlne rfl).elim
    | cons v vs => simpa only [List.getLast?_cons_cons] using hl.2
  have hSplit : l.dropLast ++ [b] = l :=
    List.dropLast_append_getLast? b (by simp [hbLast])
  intro v hv
  have hvl : v ∈ l := List.dropLast_subset _ hv
  have hvA : v ≠ a := fun h => (List.nodup_cons.mp hND).1 (h ▸ hvl)
  have hvB : v ≠ b := by
    intro h
    subst v
    have hN := (List.nodup_cons.mp hND).2
    rw [←hSplit,List.nodup_append] at hN
    exact hN.2.2 _ hv _ (by simp) rfl
  have hvX := hAvoid v (List.mem_cons_of_mem _ hvl)
  have hvU : v ∉ Z ∪ Z.image s := fun h =>
    hvX (mem_sdiff.mpr ⟨h,by simp [hvA,hvB]⟩)
  exact ⟨fun h => hvU (mem_union_left _ h),fun h =>
    hvU (mem_union_right _ (mem_image.mpr ⟨s.symm v,h,s.apply_symm_apply v⟩))⟩

/-- The integer version of the length bound (3/\nu), where
the robust radius is (r=\nu|I|) and the growth step is at least (r/2). -/
theorem chord_route_length_bound {n r g len : ℕ}
    (_hg : 0 < g) (hHalf : r ≤ 2*g) (hSmall : 3*r ≤ n) (hLen : len ≤ n/g+3) :
    r*len ≤ 3*n := by
  have hDiv := Nat.div_mul_le_self n g
  have h := Nat.mul_le_mul_left r hLen
  have h' := Nat.mul_le_mul_left (n/g) hHalf
  nlinarith only [h,h',hDiv,hSmall]

end OverfullWork.DirectedRobustExpansion
