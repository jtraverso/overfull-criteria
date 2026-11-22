module

public import OverfullWork.SuccessorSwitchOrbits
public import OverfullWork.MergeReservePacking
public import OverfullWork.MergeConnectedCycles

@[expose] public section


/-! Proposition 10.1 and the exchanges used in Kühn–Osthus §10.4.
They change the owners of physical arcs and preserve the partition. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function DirectedPrefactor
open scoped Classical
variable {V : Type*} {t : ℕ}

/-- Perform the same successor exchange in each selected factor. -/
noncomputable def switchFactors (F : Fin t → Equiv.Perm V) (S : Finset (Fin t))
    (x y : V) (i : Fin t) : Equiv.Perm V :=
  if i ∈ S then switchSuccessors (F i) x y else F i

theorem switchFactors_protects (F : Fin t → Equiv.Perm V) (S : Finset (Fin t))
    {x y z : V} {i : Fin t} (h : i ∉ S ∨ z ≠ x ∧ z ≠ y) :
    switchFactors F S x y i z = F i z := by
  by_cases hi : i ∈ S
  · obtain ⟨hx,hy⟩ := h.resolve_left (fun hn => hn hi)
    simpa only [switchFactors,if_pos hi] using switchSuccessors_off (F i) hx hy
  · simp [switchFactors,hi]

/-- Reindexing the owners of the arcs leaving each vertex preserves
both the physical union and disjointness of the factors. -/
theorem matchingUnion_of_row_reindexing (F G : Fin t → Equiv.Perm V)
    (hRow : ∀ z, ∃ e : Equiv.Perm (Fin t), ∀ i, G i z = F (e i) z)
    (hDis : ∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) :
    matchingUnion G = matchingUnion F ∧ ∀ i j, i ≠ j → ∀ v, G i v ≠ G j v := by
  refine ⟨?_,?_⟩
  · ext z w
    obtain ⟨e,he⟩ := hRow z
    change (∃ i, G i z = w) ↔ ∃ i, F i z = w
    exact ⟨fun ⟨i,hi⟩ => ⟨e i,(he i).symm.trans hi⟩,fun ⟨i,hi⟩ =>
      ⟨e.symm i,by rw [he,e.apply_symm_apply,hi]⟩⟩
  · intro i j hij z
    obtain ⟨e,he⟩ := hRow z
    rw [he,he]
    exact hDis _ _ (e.injective.ne hij) z

/-- A permutation of the original owners at each of the two sources
certifies that the arc union and disjointness are preserved. -/
theorem switchFactors_conserves (F : Fin t → Equiv.Perm V) (S : Finset (Fin t))
    {x y : V} (p q : Equiv.Perm (Fin t))
    (hp : ∀ i, F (p i) x = if i ∈ S then F i y else F i x)
    (hq : ∀ i, F (q i) y = if i ∈ S then F i x else F i y)
    (hDis : ∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) :
    matchingUnion (switchFactors F S x y) = matchingUnion F ∧
      ∀ i j, i ≠ j → ∀ v, switchFactors F S x y i v ≠ switchFactors F S x y j v := by
  have hRow (z : V) : ∃ e : Equiv.Perm (Fin t),
      ∀ i, switchFactors F S x y i z = F (e i) z := by
    by_cases hx : z = x
    · subst z
      exact ⟨p,fun i => by by_cases hi : i ∈ S <;> simpa [switchFactors, hi] using (hp i).symm⟩
    by_cases hy : z = y
    · subst z
      exact ⟨q,fun i => by by_cases hi : i ∈ S <;> simpa [switchFactors, hi] using (hq i).symm⟩
    · exact ⟨1,fun i => switchFactors_protects F S (.inr ⟨hx,hy⟩)⟩
  exact matchingUnion_of_row_reindexing F _ hRow hDis

/-- The `C₄` exchange permutes the two owners at both switch sources. -/
theorem c4_exchange_conserves (F : Fin t → Equiv.Perm V) {i j : Fin t} {x y : V}
    (hx : F i x = F j y) (hy : F i y = F j x)
    (hDis : ∀ a b, a ≠ b → ∀ v, F a v ≠ F b v) :
    matchingUnion (switchFactors F {i,j} x y) = matchingUnion F ∧
      ∀ a b, a ≠ b → ∀ v, switchFactors F {i,j} x y a v ≠ switchFactors F {i,j} x y b v := by
  apply switchFactors_conserves F {i,j} (Equiv.swap i j) (Equiv.swap i j) _ _ hDis
  · intro a
    by_cases hi : a = i
    · subst a
      simpa using hy.symm
    by_cases hj : a = j
    · subst a
      simpa using hx
    · simp [Equiv.swap_apply_of_ne_of_ne hi hj,hi,hj]
  · intro a
    by_cases hi : a = i
    · subst a
      simpa using hx.symm
    by_cases hj : a = j
    · subst a
      simpa using hy
    · simp [Equiv.swap_apply_of_ne_of_ne hi hj,hi,hj]

/-- The `K₂,₃` exchange permutes the three owners in opposite cyclic
orders at the two sources, as in Figure 8. -/
theorem k23_exchange_conserves (F : Fin t → Equiv.Perm V) {i j k : Fin t} {x y : V}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : F i y = F j x) (hj : F j y = F k x) (hk : F k y = F i x)
    (hDis : ∀ a b, a ≠ b → ∀ v, F a v ≠ F b v) :
    matchingUnion (switchFactors F {i,j,k} x y) = matchingUnion F ∧
      ∀ a b, a ≠ b → ∀ v, switchFactors F {i,j,k} x y a v ≠ switchFactors F {i,j,k} x y b v := by
  let p := Equiv.swap i j * Equiv.swap j k
  let q := Equiv.swap j k * Equiv.swap i j
  apply switchFactors_conserves F {i,j,k} p q _ _ hDis
  · intro a
    by_cases ha : a = i
    · subst a
      simpa [p,Equiv.swap_apply_of_ne_of_ne hij hik] using hi.symm
    by_cases hb : a = j
    · subst a
      simpa [p,Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm] using hj.symm
    by_cases hc : a = k
    · subst a
      simpa [p] using hk.symm
    · simp [p,Equiv.swap_apply_of_ne_of_ne ha hb,Equiv.swap_apply_of_ne_of_ne hb hc,ha,hb,hc]
  · intro a
    by_cases ha : a = i
    · subst a
      simpa [q] using hk
    by_cases hb : a = j
    · subst a
      simpa [q,Equiv.swap_apply_of_ne_of_ne hij hik] using hi
    by_cases hc : a = k
    · subst a
      simpa [q,Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm] using hj
    · simp [q,Equiv.swap_apply_of_ne_of_ne ha hb,Equiv.swap_apply_of_ne_of_ne hb hc,ha,hb,hc]

variable [Fintype V]

/-- The cycle count of a factorization is the sum over its factors. -/
noncomputable def factorCycleTotal (F : Fin t → Equiv.Perm V) : ℕ :=
  ∑ i, (successorCyclePartition (F i)).card

private theorem switchFactors_total_balance (F : Fin t → Equiv.Perm V) (S : Finset (Fin t))
    (x y : V) :
    let G := switchFactors F S x y
    factorCycleTotal G + (∑ i ∈ S, (successorCyclePartition (F i)).card) =
      factorCycleTotal F + (∑ i ∈ S, (successorCyclePartition (G i)).card) := by
  intro G
  have hOutside : (∑ i ∈ univ \ S, (successorCyclePartition (G i)).card) =
      ∑ i ∈ univ \ S, (successorCyclePartition (F i)).card := by
    apply sum_congr rfl
    intro i hi
    simp [G,switchFactors,(mem_sdiff.mp hi).2]
  unfold factorCycleTotal
  rw [← sum_sdiff (subset_univ S) (f := fun i => (successorCyclePartition (G i)).card),
      ← sum_sdiff (subset_univ S) (f := fun i => (successorCyclePartition (F i)).card),
      hOutside]
  ac_rfl

/-- A C₄ exchange preserves the parity of the total cycle count. -/
theorem c4_exchange_cycle_parity (F : Fin t → Equiv.Perm V) {i j : Fin t} {x y : V}
    (hij : i ≠ j) (hxy : x ≠ y) :
    let G := switchFactors F {i,j} x y
    factorCycleTotal G % 2 = factorCycleTotal F % 2 := by
  intro G
  have hBalance := switchFactors_total_balance F {i,j} x y
  have hi : G i = switchSuccessors (F i) x y := by simp [G,switchFactors]
  have hj : G j = switchSuccessors (F j) x y := by simp [G,switchFactors]
  change factorCycleTotal G + _ = factorCycleTotal F +
    ∑ a ∈ ({i,j} : Finset (Fin t)), (successorCyclePartition (G a)).card at hBalance
  simp only [sum_insert (notMem_singleton.mpr hij), sum_singleton, hi, hj] at hBalance
  by_cases hI : (F i).SameCycle x y <;> by_cases hJ : (F j).SameCycle x y
  · have h1 := (switchSuccessors_split (F i) hxy hI).2
    have h2 := (switchSuccessors_split (F j) hxy hJ).2
    omega
  · have h1 := (switchSuccessors_split (F i) hxy hI).2
    have h2 := (switchSuccessors_merge (F j) x y hJ).2.2.2
    omega
  · have h1 := (switchSuccessors_merge (F i) x y hI).2.2.2
    have h2 := (switchSuccessors_split (F j) hxy hJ).2
    omega
  · have h1 := (switchSuccessors_merge (F i) x y hI).2.2.2
    have h2 := (switchSuccessors_merge (F j) x y hJ).2.2.2
    omega

/-- A triple merge removes three cycles and therefore changes the parity. -/
theorem k23_exchange_cycle_total (F : Fin t → Equiv.Perm V) {i j k : Fin t} {x y : V}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hI : ¬ (F i).SameCycle x y) (hJ : ¬ (F j).SameCycle x y)
    (hK : ¬ (F k).SameCycle x y) :
    factorCycleTotal (switchFactors F {i,j,k} x y) + 3 = factorCycleTotal F := by
  let G := switchFactors F {i,j,k} x y
  have hBalance := switchFactors_total_balance F {i,j,k} x y
  have hi : G i = switchSuccessors (F i) x y := by simp [G,switchFactors]
  have hj : G j = switchSuccessors (F j) x y := by simp [G,switchFactors]
  have hk : G k = switchSuccessors (F k) x y := by simp [G,switchFactors]
  change factorCycleTotal G + _ = factorCycleTotal F +
    ∑ a ∈ ({i,j,k} : Finset (Fin t)), (successorCyclePartition (G a)).card at hBalance
  have hNot : i ∉ ({j,k} : Finset (Fin t)) := by simp [hij,hik]
  simp only [sum_insert hNot, sum_insert (notMem_singleton.mpr hjk),
    sum_singleton, hi, hj, hk] at hBalance
  have h1 := (switchSuccessors_merge (F i) x y hI).2.2.2
  have h2 := (switchSuccessors_merge (F j) x y hJ).2.2.2
  have h3 := (switchSuccessors_merge (F k) x y hK).2.2.2
  change factorCycleTotal G + 3 = factorCycleTotal F
  omega

/-- The two marked vertices represent the two distinct cycles. -/
def MarkedBicycle (F : Equiv.Perm V) (x y : V) : Prop :=
  ¬ F.SameCycle x y ∧ ∀ v, F.SameCycle x v ∨ F.SameCycle y v

theorem switchSuccessors_hamilton_of_markedBicycle (F : Equiv.Perm V) {x y : V}
    (h : MarkedBicycle F x y) : HasSpanningCycle (fun v w => switchSuccessors F x y v = w) := by
  obtain ⟨hJoin,hOld,_,_⟩ := switchSuccessors_merge F x y h.1
  apply spanning_cycle_of_single_orbit _ x
  exact fun v => (h.2 v).elim (hOld x v) (fun hv => hJoin.trans (hOld y v hv))

/-- Cutting a Hamilton factor at alternating switch sources and
marks makes a bicycle with the marks in its two distinct cycles. -/
theorem switchSuccessors_markedBicycle_of_alternating (F : Equiv.Perm V) (x y : V)
    (l k r : ℕ) (hl : 0 < l) (hlk : l < k) (hkr : k < r)
    (hr : r < Function.minimalPeriod (F : V → V) x) (hy : (F : V → V)^[k] x = y)
    (hAll : ∀ z, F.SameCycle x z) :
    MarkedBicycle (switchSuccessors F x y) ((F : V → V)^[l] x) ((F : V → V)^[r] x) := by
  let G := switchSuccessors F x y
  let a := (F : V → V)^[l] x
  let b := (F : V → V)^[r] x
  have hApart : ¬ G.SameCycle a b :=
    switchSuccessors_separates_alternating F x y l k r hl hlk hkr hr hy
  have hxy : x ≠ y := by
    intro he
    have hAt : (F : V → V)^[k] x = (F : V → V)^[0] x := hy.trans he.symm
    have := Function.iterate_injOn_Iio_minimalPeriod
      (hkr.trans hr) (by omega : 0 < Function.minimalPeriod (F : V → V) x) hAt
    omega
  have hEnds := (switchSuccessors_split F hxy (hAll y)).1
  have hCover : ∀ z, G.SameCycle x z ∨ G.SameCycle y z := by
    have hEq := orbit_union_of_switchSuccessors G x y hEnds
    rw [show switchSuccessors G x y = F from switchSuccessors_twice F x y] at hEq
    intro z
    have hm := (orbit_mem_iff F x z).mpr (hAll z)
    rw [hEq,mem_union,orbit_mem_iff,orbit_mem_iff] at hm
    exact hm
  have hSeg := orbit_segment_of_switchSuccessors F x y k (by omega) (hkr.trans hr) hy
  have ha : G.SameCycle y a := by
    apply (orbit_mem_iff G y a).mp
    change a ∈ orbit (switchSuccessors F x y) y
    rw [hSeg]
    exact mem_image.mpr ⟨l-1,mem_range.mpr (by omega),by
      change (F : V → V)^[l-1+1] x = (F : V → V)^[l] x
      rw [show l-1+1=l by omega]⟩
  have hb : G.SameCycle x b :=
    (hCover b).resolve_right (fun h => hApart (ha.symm.trans h))
  exact ⟨hApart,fun z => (hCover z).elim (fun h => .inr (hb.symm.trans h))
    (fun h => .inl (ha.symm.trans h))⟩

/-- A two-factor exchange merges both marked bicycles while preserving
the physical arc partition. This is also the B₂B₃ repair in Lemma 10.4. -/
theorem c4_exchange_hamilton_of_markedBicycles (F : Fin t → Equiv.Perm V)
    {i j : Fin t} {x y : V} (hI : MarkedBicycle (F i) x y) (hJ : MarkedBicycle (F j) x y)
    (hx : F i x = F j y) (hy : F i y = F j x)
    (hDis : ∀ a b, a ≠ b → ∀ v, F a v ≠ F b v) :
    let G := switchFactors F {i,j} x y
    matchingUnion G = matchingUnion F ∧ (∀ a b, a ≠ b → ∀ v, G a v ≠ G b v) ∧
      HasSpanningCycle (fun v w => G i v = w) ∧ HasSpanningCycle (fun v w => G j v = w) := by
  intro G
  obtain ⟨hUnion,hDis'⟩ := c4_exchange_conserves F hx hy hDis
  exact ⟨hUnion,hDis',by simpa [G,switchFactors] using switchSuccessors_hamilton_of_markedBicycle (F i) hI,
    by simpa [G,switchFactors] using switchSuccessors_hamilton_of_markedBicycle (F j) hJ⟩

/-- In the second two-factor exchange of the two-bicycle case of
Lemma 10.4, the primary bicycle is repaired and the reserve Hamilton
cycle becomes a bicycle with the two triple-switch marks separated. -/
theorem c4_exchange_hamilton_and_markedBicycle (F : Fin t → Equiv.Perm V)
    {i j : Fin t} {x y : V} (hI : MarkedBicycle (F i) x y) (hJ : ∀ z, (F j).SameCycle x z)
    (l k r : ℕ) (hl : 0 < l) (hlk : l < k) (hkr : k < r)
    (hr : r < minimalPeriod (F j : V → V) x) (hAt : (F j : V → V)^[k] x = y)
    (hx : F i x = F j y) (hy : F i y = F j x)
    (hDis : ∀ a b, a ≠ b → ∀ v, F a v ≠ F b v) :
    let G := switchFactors F {i,j} x y
    matchingUnion G = matchingUnion F ∧ (∀ a b, a ≠ b → ∀ v, G a v ≠ G b v) ∧
      HasSpanningCycle (fun v w => G i v = w) ∧
      MarkedBicycle (G j) ((F j : V → V)^[l] x) ((F j : V → V)^[r] x) := by
  intro G
  obtain ⟨hUnion,hDis'⟩ := c4_exchange_conserves F hx hy hDis
  refine ⟨hUnion,hDis',?_,?_⟩
  · simpa [G,switchFactors] using switchSuccessors_hamilton_of_markedBicycle (F i) hI
  · simpa only [G,switchFactors,if_pos (mem_insert_of_mem (mem_singleton_self j))] using
      switchSuccessors_markedBicycle_of_alternating (F j) x y l k r hl hlk hkr hr hAt hJ

/-- Three triply switchable bicycles are replaced by three Hamilton
cycles on exactly the same arcs. The other factors are left unchanged. -/
theorem k23_exchange_hamilton_of_markedBicycles (F : Fin t → Equiv.Perm V)
    {i j k : Fin t} {x y : V} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hXi : MarkedBicycle (F i) x y) (hXj : MarkedBicycle (F j) x y) (hXk : MarkedBicycle (F k) x y)
    (hi : F i y = F j x) (hj : F j y = F k x) (hk : F k y = F i x)
    (hDis : ∀ a b, a ≠ b → ∀ v, F a v ≠ F b v) :
    let G := switchFactors F {i,j,k} x y
    matchingUnion G = matchingUnion F ∧ (∀ a b, a ≠ b → ∀ v, G a v ≠ G b v) ∧
      (∀ a ∈ ({i,j,k} : Finset (Fin t)), HasSpanningCycle (fun v w => G a v = w)) ∧
      ∀ a z, a ∉ ({i,j,k} : Finset (Fin t)) ∨ z ≠ x ∧ z ≠ y → G a z = F a z := by
  intro G
  obtain ⟨hUnion,hDis'⟩ := k23_exchange_conserves F hij hik hjk hi hj hk hDis
  refine ⟨hUnion,hDis',?_,fun a z h => switchFactors_protects F {i,j,k} h⟩
  intro a ha
  suffices h : MarkedBicycle (F a) x y by
    simpa only [G,switchFactors,if_pos ha] using switchSuccessors_hamilton_of_markedBicycle (F a) h
  simp only [mem_insert,mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · exact hXi
  · exact hXj
  · exact hXk

end OverfullWork.DirectedRobustExpansion
