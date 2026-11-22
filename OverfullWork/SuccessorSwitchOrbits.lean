module

public import OverfullWork.PrefactorOpenOrbit

@[expose] public section


/-! The orbits affected by exchanging two successors of a permutation. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function DirectedPrefactor
open scoped Classical
variable {E : Type*} [Fintype E]

omit [Fintype E] in
theorem successor_sameCycle_iterate (σ : Equiv.Perm E) (v : E) (k : ℕ) :
    σ.SameCycle v ((σ : E → E)^[k] v) := by
  rw [←Equiv.Perm.coe_pow,Equiv.Perm.sameCycle_pow_right]

theorem sameCycle_merge_of_left_swap (σ : Equiv.Perm E) (a b : E) (hApart : ¬ σ.SameCycle a b) :
    let ρ := Equiv.swap a b * σ
    ρ.SameCycle a b ∧ ∀ x y, σ.SameCycle x y → ρ.SameCycle x y := by
  intro ρ
  let k := minimalPeriod (σ : E → E) b
  have hk : 0 < k := minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts b)
  have hTrace (i : ℕ) (hi : i < k) : (ρ : E → E)^[i] b = (σ : E → E)^[i] b := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [iterate_succ_apply',ih (Nat.lt_of_succ_lt hi),iterate_succ_apply']
      have hb : σ ((σ : E → E)^[i] b) ≠ b := by
        intro h
        have hh : (σ : E → E)^[i+1] b = (σ : E → E)^[0] b := by
          rw [iterate_succ_apply',iterate_zero_apply,h]
        have := iterate_injOn_Iio_minimalPeriod hi hk hh
        omega
      have ha : σ ((σ : E → E)^[i] b) ≠ a := by
        intro h
        have hh := successor_sameCycle_iterate σ b (i+1)
        rw [iterate_succ_apply',h] at hh
        exact hApart hh.symm
      exact Equiv.swap_apply_of_ne_of_ne ha hb
  have hi : k-1+1 = k := by omega
  have hm : (ρ : E → E)^[k] b = a := by
    rw [←hi,iterate_succ_apply',hTrace (k-1) (by omega)]
    have hb : σ ((σ : E → E)^[k-1] b) = b := by
      rw [←iterate_succ_apply' (σ : E → E) (k-1) b,Nat.succ_eq_add_one,hi]
      exact isPeriodicPt_minimalPeriod (σ : E → E) b
    change Equiv.swap a b (σ ((σ : E → E)^[k-1] b)) = a
    rw [hb,Equiv.swap_apply_right]
  have hab : ρ.SameCycle a b := (hm ▸ successor_sameCycle_iterate ρ b k).symm
  have hNext (v : E) : ρ.SameCycle v (σ v) := by
    have hρ : ρ.SameCycle v (ρ v) := Equiv.Perm.sameCycle_apply_right.mpr <| Equiv.Perm.SameCycle.refl _ _
    by_cases ha : σ v = a
    · have hs : ρ v = b := by
        change Equiv.swap a b (σ v) = b
        rw [ha,Equiv.swap_apply_left]
      rw [ha]
      exact (hs ▸ hρ).trans hab.symm
    by_cases hb : σ v = b
    · have hs : ρ v = a := by
        change Equiv.swap a b (σ v) = a
        rw [hb,Equiv.swap_apply_right]
      rw [hb]
      exact (hs ▸ hρ).trans hab
    · have hh : ρ v = σ v := Equiv.swap_apply_of_ne_of_ne ha hb
      exact hh ▸ hρ
  refine ⟨hab,?_⟩
  intro x y h
  obtain ⟨n,_,hn⟩ := h.exists_pow_eq'
  rw [Equiv.Perm.coe_pow] at hn
  have hAll (m : ℕ) : ρ.SameCycle x ((σ : E → E)^[m] x) := by
    induction m with
    | zero => exact Equiv.Perm.SameCycle.refl _ _
    | succ m ih =>
      rw [iterate_succ_apply']
      exact ih.trans (hNext _)
  exact hn ▸ hAll n

/-- A cycle that avoids both switched vertices is preserved in its entirety. -/
theorem orbit_unchanged_of_left_swap (σ : Equiv.Perm E) (a b x : E)
    (ha : ¬ σ.SameCycle x a) (hb : ¬ σ.SameCycle x b) :
    orbit (Equiv.swap a b * σ) x = orbit σ x := by
  let ρ := Equiv.swap a b * σ
  have hTrace (i : ℕ) : (ρ : E → E)^[i] x = (σ : E → E)^[i] x := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [iterate_succ_apply', ih, iterate_succ_apply']
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h
        have hs := successor_sameCycle_iterate σ x (i+1)
        rw [iterate_succ_apply',h] at hs
        exact ha hs
      · intro h
        have hs := successor_sameCycle_iterate σ x (i+1)
        rw [iterate_succ_apply',h] at hs
        exact hb hs
  ext y
  rw [orbit_mem_iff, orbit_mem_iff]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h.exists_nat_pow_eq
    rw [Equiv.Perm.coe_pow, hTrace] at hi
    exact hi ▸ successor_sameCycle_iterate σ x i
  · intro h
    obtain ⟨i, hi⟩ := h.exists_nat_pow_eq
    rw [Equiv.Perm.coe_pow, ← hTrace] at hi
    exact hi ▸ successor_sameCycle_iterate ρ x i

private theorem orbit_eq_of_sameCycle (σ : Equiv.Perm E) {x y : E}
    (h : σ.SameCycle x y) : orbit σ x = orbit σ y := by
  ext z
  simp only [orbit_mem_iff]
  exact ⟨h.symm.trans, h.trans⟩

/-- The switched cycle through the two endpoints is exactly the union of
the two original cycles when their vertices were in distinct cycles. -/
theorem orbit_union_of_left_swap (σ : Equiv.Perm E) (a b : E)
    (hApart : ¬ σ.SameCycle a b) :
    orbit (Equiv.swap a b * σ) a = orbit σ a ∪ orbit σ b := by
  let ρ := Equiv.swap a b * σ
  obtain ⟨hJoin, hOld⟩ := sameCycle_merge_of_left_swap σ a b hApart
  ext x
  simp only [mem_union, orbit_mem_iff]
  refine ⟨fun h => ?_, fun h => h.elim (hOld a x) (fun hb => hJoin.trans (hOld b x hb))⟩
  by_contra! hx
  have he := orbit_unchanged_of_left_swap σ a b x
    (fun ha => hx.1 ha.symm) (fun hb => hx.2 hb.symm)
  have hmem : a ∈ orbit ρ x := (orbit_mem_iff _ _ _).mpr h.symm
  exact hx.1 ((orbit_mem_iff _ _ _).mp (he ▸ hmem)).symm

/-- Cutting the incoming arcs at the two endpoints closes the forward
segment from the first endpoint up to, but excluding, the second. -/
theorem orbit_prefix_of_left_swap (σ : Equiv.Perm E) (a b : E) (k : ℕ)
    (hkPos : 0 < k) (hkN : k < minimalPeriod (σ : E → E) a)
    (hEnd : (σ : E → E)^[k] a = b) :
    orbit (Equiv.swap a b * σ) a = (range k).image (fun i => (σ : E → E)^[i] a) := by
  let ρ := Equiv.swap a b * σ
  let n := minimalPeriod (σ : E → E) a
  change k < n at hkN
  have hTrace (i : ℕ) (hi : i < k) : (ρ : E → E)^[i] a = (σ : E → E)^[i] a := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [iterate_succ_apply', ih (by omega)]
      change Equiv.swap a b (σ ((σ : E → E)^[i] a)) = _
      rw [← iterate_succ_apply' (σ : E → E) i a, Equiv.swap_apply_of_ne_of_ne]
      · intro h
        have he : (σ : E → E)^[i+1] a = (σ : E → E)^[0] a := h
        have := iterate_injOn_Iio_minimalPeriod (by omega : i+1 < n) (by omega : 0 < n) he
        omega
      · intro h
        have := iterate_injOn_Iio_minimalPeriod (by omega : i+1 < n) hkN (h.trans hEnd.symm)
        omega
  have hPeriod : IsPeriodicPt (ρ : E → E) k a := by
    have he : k - 1 + 1 = k := by omega
    change (ρ : E → E)^[k] a = a
    rw [← he, iterate_succ_apply', hTrace (k - 1) (by omega)]
    change Equiv.swap a b (σ ((σ : E → E)^[k-1] a)) = a
    rw [← iterate_succ_apply' (σ : E → E) (k - 1) a, Nat.succ_eq_add_one,
      he, hEnd, Equiv.swap_apply_right]
  have hPeriodEq : minimalPeriod (ρ : E → E) a = k := by
    apply le_antisymm (hPeriod.minimalPeriod_le hkPos)
    by_contra! h
    have hPos : 0 < minimalPeriod (ρ : E → E) a :=
      minimalPeriod_pos_of_mem_periodicPts (ρ.injective.mem_periodicPts a)
    have he := isPeriodicPt_minimalPeriod (ρ : E → E) a
    change (ρ : E → E)^[minimalPeriod (ρ : E → E) a] a = a at he
    rw [hTrace _ h] at he
    have hzero : (σ : E → E)^[minimalPeriod (ρ : E → E) a] a = (σ : E → E)^[0] a := he
    have := iterate_injOn_Iio_minimalPeriod (h.trans hkN) (by omega : 0 < n) hzero
    omega
  rw [orbit_eq_forward_trace, hPeriodEq]
  exact image_congr (fun i hi => hTrace i (mem_range.mp hi))

/-- If two distinct vertices lie on one cycle, exchanging its incoming
arcs separates them into different cycles. -/
theorem not_sameCycle_of_left_swap (σ : Equiv.Perm E) {a b : E}
    (hne : a ≠ b) (hSame : σ.SameCycle a b) :
    ¬ (Equiv.swap a b * σ).SameCycle a b := by
  let ρ := Equiv.swap a b * σ
  let n := minimalPeriod (σ : E → E) a
  have hb : b ∈ orbit σ a := (orbit_mem_iff _ _ _).mpr hSame
  rw [orbit_eq_forward_trace] at hb
  obtain ⟨k, hk, hEnd⟩ := mem_image.mp hb
  have hkN : k < n := mem_range.mp hk
  have hkPos : 0 < k := by
    by_contra! h
    have he : k = 0 := by omega
    exact hne (by simpa [he] using hEnd)
  intro h
  have hm := (orbit_mem_iff _ _ _).mpr h
  rw [orbit_prefix_of_left_swap σ a b k hkPos hkN hEnd] at hm
  obtain ⟨i, hi, hAt⟩ := mem_image.mp hm
  have hiK : i < k := mem_range.mp hi
  have := iterate_injOn_Iio_minimalPeriod (hiK.trans hkN) hkN (hAt.trans hEnd.symm)
  omega

/-- The cycle partition includes the singleton cycles of fixed vertices. -/
noncomputable def successorCyclePartition (σ : Equiv.Perm E) : Finset (Finset E) :=
  univ.image (orbit σ)

theorem successorCyclePartition_of_left_swap (σ : Equiv.Perm E) (a b : E)
    (hApart : ¬ σ.SameCycle a b) :
    successorCyclePartition (Equiv.swap a b * σ) =
      insert (orbit σ a ∪ orbit σ b)
        ((successorCyclePartition σ).erase (orbit σ a) |>.erase (orbit σ b)) := by
  let ρ := Equiv.swap a b * σ
  obtain ⟨hJoin, hOld⟩ := sameCycle_merge_of_left_swap σ a b hApart
  have hUnion := orbit_union_of_left_swap σ a b hApart
  have hDist (x y : E) : σ.SameCycle x y ↔ orbit σ x = orbit σ y := by
    refine ⟨orbit_eq_of_sameCycle σ, fun h => ?_⟩
    have hm : y ∈ orbit σ y := (orbit_mem_iff _ _ _).mpr (Equiv.Perm.SameCycle.refl _ _)
    exact (orbit_mem_iff _ _ _).mp (h.symm ▸ hm)
  ext O
  simp only [successorCyclePartition, mem_image, mem_univ, true_and, mem_insert, mem_erase]
  constructor
  · rintro ⟨x,rfl⟩
    by_cases ha : σ.SameCycle x a
    · exact Or.inl ((orbit_eq_of_sameCycle ρ (hOld x a ha)).trans hUnion)
    by_cases hb : σ.SameCycle x b
    · exact Or.inl ((orbit_eq_of_sameCycle ρ ((hOld x b hb).trans hJoin.symm)).trans hUnion)
    · rw [orbit_unchanged_of_left_swap σ a b x ha hb]
      exact Or.inr ⟨fun he => hb (hDist x b |>.mpr he),
        fun he => ha (hDist x a |>.mpr he), ⟨x,rfl⟩⟩
  · rintro (rfl | ⟨hb, ha, x, rfl⟩)
    · exact ⟨a,hUnion⟩
    · exact ⟨x,orbit_unchanged_of_left_swap σ a b x
        (fun h => ha (hDist x a |>.mp h)) (fun h => hb (hDist x b |>.mp h))⟩

/-- Merging two cycles removes exactly one part of the cycle partition. -/
theorem successorCyclePartition_card_left_swap_merge (σ : Equiv.Perm E) (a b : E)
    (hApart : ¬ σ.SameCycle a b) :
    (successorCyclePartition (Equiv.swap a b * σ)).card + 1 =
      (successorCyclePartition σ).card := by
  have hMem (x : E) : orbit σ x ∈ successorCyclePartition σ :=
    mem_image.mpr ⟨x,mem_univ _,rfl⟩
  have hA : a ∈ orbit σ a := (orbit_mem_iff _ _ _).mpr (Equiv.Perm.SameCycle.refl _ _)
  have hDist : orbit σ b ≠ orbit σ a := by
    intro he
    exact hApart ((orbit_mem_iff _ _ _).mp (he.symm ▸ hA)).symm
  have hB := mem_erase.mpr ⟨hDist,hMem b⟩
  rw [successorCyclePartition_of_left_swap σ a b hApart]
  rw [card_insert_of_notMem, card_erase_of_mem hB, card_erase_of_mem (hMem a)]
  · have := card_pos.mpr ⟨_,hB⟩
    rw [card_erase_of_mem (hMem a)] at this
    omega
  · intro h
    obtain ⟨x, -, hx⟩ := mem_image.mp (mem_of_mem_erase (mem_of_mem_erase h))
    have ha : a ∈ orbit σ x := hx ▸ mem_union_left _ hA
    have he := orbit_eq_of_sameCycle σ ((orbit_mem_iff _ _ _).mp ha)
    exact (mem_erase.mp (mem_of_mem_erase h)).1 (hx.symm.trans he)

private theorem orbit_inv (σ : Equiv.Perm E) (a : E) : orbit σ⁻¹ a = orbit σ a := by
  ext z
  simp only [orbit_mem_iff, Equiv.Perm.sameCycle_inv]

private theorem cycle_partition_inv (σ : Equiv.Perm E) :
    successorCyclePartition σ⁻¹ = successorCyclePartition σ := by
  unfold successorCyclePartition
  congr 1
  funext x
  exact orbit_inv σ x

/-- Exchanging the successors of x and y. The two sources are the inputs
of the transposition, so every other outgoing arc is preserved. -/
noncomputable def switchSuccessors (σ : Equiv.Perm E) (x y : E) : Equiv.Perm E :=
  σ * Equiv.swap x y

omit [Fintype E] in
@[simp] theorem switchSuccessors_left (σ : Equiv.Perm E) (x y : E) :
    switchSuccessors σ x y x = σ y := by simp [switchSuccessors]

omit [Fintype E] in
@[simp] theorem switchSuccessors_right (σ : Equiv.Perm E) (x y : E) :
    switchSuccessors σ x y y = σ x := by simp [switchSuccessors]

omit [Fintype E] in
theorem switchSuccessors_off (σ : Equiv.Perm E) {x y z : E} (hx : z ≠ x) (hy : z ≠ y) :
    switchSuccessors σ x y z = σ z := by
  simp [switchSuccessors, Equiv.swap_apply_of_ne_of_ne hx hy]

omit [Fintype E] in
@[simp] theorem switchSuccessors_twice (σ : Equiv.Perm E) (x y : E) :
    switchSuccessors (switchSuccessors σ x y) x y = σ := by
  simp [switchSuccessors, mul_assoc]

theorem switchSuccessors_merge (σ : Equiv.Perm E) (x y : E) (hApart : ¬ σ.SameCycle x y) :
    (switchSuccessors σ x y).SameCycle x y ∧
      (∀ a b, σ.SameCycle a b → (switchSuccessors σ x y).SameCycle a b) ∧
      successorCyclePartition (switchSuccessors σ x y) =
        insert (orbit σ x ∪ orbit σ y)
          ((successorCyclePartition σ).erase (orbit σ x) |>.erase (orbit σ y)) ∧
      (successorCyclePartition (switchSuccessors σ x y)).card + 1 =
        (successorCyclePartition σ).card := by
  have hInv : (switchSuccessors σ x y)⁻¹ = Equiv.swap x y * σ⁻¹ := by simp [switchSuccessors]
  have ha : ¬ σ⁻¹.SameCycle x y := fun h => hApart h.of_inv
  obtain ⟨hJoin,hOld⟩ := sameCycle_merge_of_left_swap σ⁻¹ x y ha
  have hPart := successorCyclePartition_of_left_swap σ⁻¹ x y ha
  have hCard := successorCyclePartition_card_left_swap_merge σ⁻¹ x y ha
  rw [← hInv, cycle_partition_inv, cycle_partition_inv, orbit_inv, orbit_inv] at hPart
  rw [← hInv, cycle_partition_inv, cycle_partition_inv] at hCard
  rw [← hInv] at hJoin hOld
  exact ⟨hJoin.of_inv, fun a b h => (hOld a b h.inv).of_inv, hPart, hCard⟩

theorem orbit_union_of_switchSuccessors (σ : Equiv.Perm E) (x y : E)
    (hApart : ¬ σ.SameCycle x y) :
    orbit (switchSuccessors σ x y) x = orbit σ x ∪ orbit σ y := by
  have hInv : (switchSuccessors σ x y)⁻¹ = Equiv.swap x y * σ⁻¹ := by simp [switchSuccessors]
  have h := orbit_union_of_left_swap σ⁻¹ x y (fun ha => hApart ha.of_inv)
  simpa only [← hInv, orbit_inv] using h

theorem switchSuccessors_split (σ : Equiv.Perm E) {x y : E} (hne : x ≠ y)
    (hSame : σ.SameCycle x y) :
    ¬ (switchSuccessors σ x y).SameCycle x y ∧
      (successorCyclePartition (switchSuccessors σ x y)).card =
        (successorCyclePartition σ).card + 1 := by
  have hInv : (switchSuccessors σ x y)⁻¹ = Equiv.swap x y * σ⁻¹ := by simp [switchSuccessors]
  have hApart := not_sameCycle_of_left_swap σ⁻¹ hne hSame.inv
  rw [← hInv, Equiv.Perm.sameCycle_inv] at hApart
  refine ⟨hApart, ?_⟩
  have h := (switchSuccessors_merge (switchSuccessors σ x y) x y hApart).2.2.2
  simpa only [switchSuccessors_twice] using h.symm

/-- In a split at the outgoing arcs of x and y, the new cycle
through y is the forward interval from the old successor of x to y. -/
theorem orbit_segment_of_switchSuccessors (σ : Equiv.Perm E) (x y : E) (k : ℕ)
    (hk : 0 < k) (hkN : k < minimalPeriod (σ : E → E) x)
    (hEnd : (σ : E → E)^[k] x = y) :
    orbit (switchSuccessors σ x y) y =
      (range k).image (fun i => (σ : E → E)^[i+1] x) := by
  let ρ := switchSuccessors σ x y
  have hY : ρ.SameCycle y (σ x) := by
    rw [← switchSuccessors_right σ x y]
    exact (Equiv.Perm.SameCycle.refl ρ y).apply_right
  have hTrans : ρ = Equiv.swap (σ x) (σ y) * σ :=
    Equiv.mul_swap_eq_swap_mul σ x y
  have hPeriod := minimalPeriod_apply (σ.injective.mem_periodicPts x)
  have hIter (i : ℕ) : (σ : E → E)^[i+1] x = (σ : E → E)^[i] (σ x) := by
    rw [iterate_add_apply, iterate_one]
  have hEnd' : (σ : E → E)^[k] (σ x) = σ y := by
    rw [← hIter, iterate_succ_apply', hEnd]
  change orbit ρ y = _
  rw [orbit_eq_of_sameCycle ρ hY, hTrans,
    orbit_prefix_of_left_swap σ (σ x) (σ y) k hk (hPeriod.symm ▸ hkN) hEnd']
  exact image_congr (fun i _ => (hIter i).symm)

/-- Figure 6 and the second split of Lemma 10.4. If the two
marks alternate with the two switch sources, the marks are separated. -/
theorem switchSuccessors_separates_alternating (σ : Equiv.Perm E) (x y : E)
    (l k r : ℕ) (hl : 0 < l) (hlk : l < k) (hkr : k < r)
    (hr : r < minimalPeriod (σ : E → E) x) (hy : (σ : E → E)^[k] x = y) :
    ¬ (switchSuccessors σ x y).SameCycle ((σ : E → E)^[l] x) ((σ : E → E)^[r] x) := by
  let ρ := switchSuccessors σ x y
  have hSeg := orbit_segment_of_switchSuccessors σ x y k (by omega) (hkr.trans hr) hy
  have hL : (σ : E → E)^[l] x ∈ orbit ρ y := by
    change _ ∈ orbit (switchSuccessors σ x y) y
    rw [hSeg]
    exact mem_image.mpr ⟨l-1, mem_range.mpr (by omega), by rw [show l-1+1=l by omega]⟩
  intro h
  have hR : (σ : E → E)^[r] x ∈ orbit ρ y := (orbit_mem_iff _ _ _).mpr
    (((orbit_mem_iff _ _ _).mp hL).trans h)
  change _ ∈ orbit (switchSuccessors σ x y) y at hR
  rw [hSeg] at hR
  obtain ⟨i,hi,hAt⟩ := mem_image.mp hR
  have hiK : i < k := mem_range.mp hi
  have := iterate_injOn_Iio_minimalPeriod (by omega : i+1 < minimalPeriod (σ : E → E) x) hr hAt
  omega

end OverfullWork.DirectedRobustExpansion
