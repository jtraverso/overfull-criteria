module

public import OverfullWork.KuhnOsthusMarkedTours

@[expose] public section


/-! Refine a marked return tour by inserting specified vertices along
its segments. The new segments partition the old forward traces. -/
namespace OverfullWork.DirectedRobustExpansion

open Function
open scoped Classical
variable {V I J : Type*}

theorem MarkedCycleSegments.trace_coordinates {σ : Equiv.Perm V} {mark : I ↪ V}
    {next : Equiv.Perm I} (H : MarkedCycleSegments σ mark next)
    {x y : I} {i j : ℕ} (hi : i < H.span x) (hj : j < H.span y)
    (h : (σ : V → V)^[i] (mark x) = (σ : V → V)^[j] (mark y)) : x = y ∧ i = j := by
  have hLe {a b : I} {u v : ℕ} (huv : u ≤ v) (hv : v < H.span b)
      (he : (σ : V → V)^[u] (mark a) = (σ : V → V)^[v] (mark b)) :
      a = b ∧ u = v := by
    have hv' : u+(v-u) = v := by omega
    rw [←hv',iterate_add_apply] at he
    have hf := (σ.injective.iterate u) he
    by_cases hab : u = v
    · subst v
      have hm : mark a = mark b := by simpa using hf
      exact ⟨mark.injective hm,rfl⟩
    · exact (H.interior b (v-u) (by omega) (by omega) a hf.symm).elim
  exact (le_total i j).elim (fun h' => hLe h' hj h) (fun h' =>
    let z := hLe h' hi h.symm
    ⟨z.1.symm,z.2.symm⟩)

/-- Reindex the marks without changing any of the physical traces. -/
def MarkedCycleSegments.reindex {σ : Equiv.Perm V} {mark : I ↪ V} {next : Equiv.Perm I}
    (H : MarkedCycleSegments σ mark next) (e : J ≃ I) (τ : Equiv.Perm J)
    (hComm : ∀ j, next (e j) = e (τ j)) :
    MarkedCycleSegments σ (e.toEmbedding.trans mark) τ where
  span j := H.span (e j)
  positive j := H.positive (e j)
  finish j := (H.finish (e j)).trans (congrArg mark (hComm j))
  interior a d hp hd b := H.interior (e a) d hp hd (e b)
  covers v := by
    obtain ⟨a,d,hd,he⟩ := H.covers v
    obtain ⟨j,rfl⟩ := e.surjective a
    exact ⟨j,d,hd,he⟩

/-- A subdivision of marked segments assigns a positive subinterval
to each new mark. The right end is either the next subinterval of
the old segment or the first position of the next old segment. -/
structure MarkedSegmentSubdivision {σ : Equiv.Perm V} {mark : I ↪ V} {next : Equiv.Perm I}
    (H : MarkedCycleSegments σ mark next) (τ : Equiv.Perm J) where
  base : J → I
  start : J → ℕ
  length : J → ℕ
  positive : ∀ j, 0 < length j
  within : ∀ j, start j + length j ≤ H.span (base j)
  next_slot : ∀ j,
    (base (τ j) = base j ∧ start (τ j) = start j + length j) ∨
      (base (τ j) = next (base j) ∧ start (τ j) = 0 ∧ start j + length j = H.span (base j))
  covers_slot : ∀ a i, i < H.span a →
    ∃! j, base j = a ∧ start j ≤ i ∧ i < start j + length j

/-- The actual new marks are the specified physical vertices of the
old traces. No vertex is repeated between two new marks. -/
def MarkedSegmentSubdivision.mark {σ : Equiv.Perm V} {old : I ↪ V} {next : Equiv.Perm I}
    {H : MarkedCycleSegments σ old next} {τ : Equiv.Perm J} (S : MarkedSegmentSubdivision H τ) :
    J ↪ V := by
  let f (j : J) := (σ : V → V)^[S.start j] (old (S.base j))
  have hSlot (j : J) : S.start j < S.start j + S.length j :=
    Nat.lt_add_of_pos_right (S.positive j)
  refine ⟨f,?_⟩
  intro x y he
  obtain ⟨hb,hi⟩ := H.trace_coordinates ((hSlot x).trans_le (S.within x))
    ((hSlot y).trans_le (S.within y)) he
  obtain ⟨j,_,hUnique⟩ := S.covers_slot (S.base x) (S.start x) ((hSlot x).trans_le (S.within x))
  have hx : x = j := hUnique x ⟨rfl,le_rfl,hSlot x⟩
  have hy : y = j := hUnique y ⟨hb.symm,hi.symm.le,by rw [hi]; exact hSlot y⟩
  exact hx.trans hy.symm

/-- Splitting at the indicated positions gives the refined
first-return permutation on all new marks. -/
def MarkedSegmentSubdivision.segments {σ : Equiv.Perm V} {old : I ↪ V} {next : Equiv.Perm I}
    {H : MarkedCycleSegments σ old next} {τ : Equiv.Perm J} (S : MarkedSegmentSubdivision H τ) :
    MarkedCycleSegments σ S.mark τ := by
  have hTrace (j : J) (d : ℕ) :
      (σ : V → V)^[d] (S.mark j) = (σ : V → V)^[S.start j+d] (old (S.base j)) := by
    change _^[d] (_^[S.start j] _) = (σ : V → V)^[S.start j+d] _
    rw [Nat.add_comm,iterate_add_apply]
  have hSlot (j : J) : S.start j < S.start j + S.length j :=
    Nat.lt_add_of_pos_right (S.positive j)
  refine ⟨S.length,S.positive,?_,?_,?_⟩
  · intro j
    rw [hTrace]
    change _ = (σ : V → V)^[S.start (τ j)] (old (S.base (τ j)))
    rcases S.next_slot j with ⟨hb,he⟩ | ⟨hb,he,hlen⟩
    · rw [hb,he]
    · rw [hb,he,hlen,iterate_zero_apply,H.finish]
  · intro x d hd hLen y he
    rw [hTrace] at he
    change _ = (σ : V → V)^[S.start y] (old (S.base y)) at he
    have hEnd : S.start x+d < S.start x+S.length x := Nat.add_lt_add_left hLen _
    obtain ⟨hb,hi⟩ := H.trace_coordinates (hEnd.trans_le (S.within x))
      ((hSlot y).trans_le (S.within y)) he
    obtain ⟨j,_,hUnique⟩ := S.covers_slot (S.base x) (S.start x+d) (hEnd.trans_le (S.within x))
    have hx : x = j := hUnique x ⟨rfl,by omega,hEnd⟩
    have hy : y = j := hUnique y ⟨hb.symm,hi.symm.le,by rw [hi]; exact hSlot y⟩
    have hz : x = y := hx.trans hy.symm
    have he' := congrArg S.start hz
    omega
  · intro v
    obtain ⟨a,i,hi,he⟩ := H.covers v
    obtain ⟨j,⟨hb,hl,hr⟩,_⟩ := S.covers_slot a i hi
    refine ⟨j,i-S.start j,by omega,?_⟩
    rw [hTrace,Nat.add_sub_of_le hl,hb,he]

end OverfullWork.DirectedRobustExpansion
