module

public import OverfullWork.ChenShanAugmentationIteration
public import OverfullWork.ChenShanCanonicalSpecialIntervals
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {I K X Y V : Type*}

/-- Extend local Hall demands by zero on all other cluster pairs. -/
noncomputable def embeddedAugmentationMatrix [Fintype X] [Fintype Y]
    (L : X ↪ I) (R : Y ↪ K) (H : X → Y → ℕ) (i : I) (j : K) : ℕ :=
  ∑ x, ∑ y, if L x = i ∧ R y = j then H x y else 0

private theorem embeddedAugmentationMatrix_positive [Fintype X] [Fintype Y]
    (L : X ↪ I) (R : Y ↪ K) (H : X → Y → ℕ) (i : I) (j : K)
    (h : 0 < embeddedAugmentationMatrix L R H i j) :
    ∃ x y, L x = i ∧ R y = j ∧ 0 < H x y := by
  by_contra hn
  have hZero : embeddedAugmentationMatrix L R H i j = 0 := by
    apply sum_eq_zero
    intro x _
    apply sum_eq_zero
    intro y _
    by_cases hEq : L x = i ∧ R y = j
    · have hz : H x y = 0 := by
        by_contra hne
        exact hn ⟨x,y,hEq.1,hEq.2,Nat.pos_of_ne_zero hne⟩
      simp [hEq,hz]
    · simp [hEq]
  omega

private theorem embeddedAugmentationMatrix_rows [Fintype X] [Fintype Y] [Fintype K]
    (L : X ↪ I) (R : Y ↪ K) (H : X → Y → ℕ) (i : I) :
    (∑ j, embeddedAugmentationMatrix L R H i j) = ∑ x, if L x = i then ∑ y, H x y else 0 := by
  unfold embeddedAugmentationMatrix
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  by_cases h : L x = i
  · simp [h, eq_comm]
  · simp [h]

private theorem embeddedAugmentationMatrix_cols [Fintype X] [Fintype Y] [Fintype I]
    (L : X ↪ I) (R : Y ↪ K) (H : X → Y → ℕ) (j : K) :
    (∑ i, embeddedAugmentationMatrix L R H i j) = ∑ y, if R y = j then ∑ x, H x y else 0 := by
  unfold embeddedAugmentationMatrix
  rw [sum_comm]
  simp_rw [sum_comm (s := (univ : Finset I))]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  by_cases h : R y = j
  · simp [h, eq_comm]
  · simp [h]

private theorem embeddedAugmentation_load [Fintype X] (E : X ↪ I) (row : X → ℕ) (i : I) :
    (∑ x, if E x = i then row x else 0) =
      if p : i ∈ Set.range E then row (Classical.choose p) else 0 := by
  by_cases hi : i ∈ Set.range E
  · rw [dite_eq_left hi, sum_eq_single (Classical.choose hi)]
    · simp [Classical.choose_spec hi]
    · intro x _ hx
      have hn : E x ≠ i := fun he => hx (E.injective (he.trans (Classical.choose_spec hi).symm))
      simp [hn]
    · simp
  · rw [dite_eq_right hi]
    exact sum_eq_zero (fun x _ => ite_eq_right fun he => hi ⟨x,he⟩)

private theorem phase_load_bound {B C Q : Type*} [Fintype B] {s : ℕ}
    (e : B → Fin 2 → Q → C)
      (he : ∀ u, Function.Injective (fun p : B × Q => e p.1 u p.2))
      (load : B × (Fin s × Fin 2) → ℕ) (i : C) (b : ℕ) (hLoad : ∀ j, load j ≤ b)
      (hPos : ∀ j, 0 < load j → ∃ x, e j.1 j.2.2 x = i) :
      (∑ j, load j) ≤ 4*s*b := by
  classical
  apply augmentation_matrix_budget_of_rounds (fun j => j.2.1) load b hLoad
  intro r
  let T := (univ : Finset (B × (Fin s × Fin 2))).filter (fun j => j.2.1 = r ∧ 0 < load j)
  have hn : Set.InjOn (fun j : B × (Fin s × Fin 2) => j.2.2) (T : Set _) := by
    intro j hj k hk hEq
    have hj' := (mem_filter.mp hj).2
    have hk' := (mem_filter.mp hk).2
    obtain ⟨x, hx⟩ := hPos j hj'.2
    obtain ⟨y, hy⟩ := hPos k hk'.2
    change j.2.2 = k.2.2 at hEq
    rw [← hEq] at hy
    have hPair : (j.1,x) = (k.1,y) := he j.2.2 (hx.trans hy.symm)
    exact Prod.ext (congrArg (fun a : B × Q => a.1) hPair) (Prod.ext (hj'.1.trans hk'.1.symm) hEq)
  have hTwo : T.card ≤ 2 := by
    rw [← card_image_of_injOn hn]
    simpa using card_le_univ (T.image fun j => j.2.2)
  exact hTwo.trans (by decide)

/-- Realize the Hall assignments of all intervals and rounds in one
physical reserve. For each of the two augmentations in a round,
distinct blocks use disjoint indexed clusters on each side. The
block embeddings can change between the first and second cycles. -/
theorem exists_global_augmentation_of_interval_matrices
    [Fintype I] [Fintype K] [Fintype X] [Fintype Y] [Fintype V] [DecidableEq V] [Nonempty V]
    {B : Type*} [Fintype B] {s : ℕ}
    (adj : V → V → Prop) [DecidableRel adj]
    (L : I → Finset V) (R : K → Finset V)
    (eL : B → Fin 2 → X ↪ I) (eR : B → Fin 2 → Y ↪ K)
    (H : B × (Fin s × Fin 2) → X → Y → ℕ)
    (blocked : B × (Fin s × Fin 2) → Finset V) (b forbidden cap : ℕ)
    (hCap : 0 < cap) (hBudget : 4*s*b ≤ forbidden*cap)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hCross : ∀ i j, Disjoint (L i) (R j))
    (hPhaseL : ∀ u, Function.Injective (fun p : B × X => eL p.1 u p.2))
    (hPhaseR : ∀ u, Function.Injective (fun p : B × Y => eR p.1 u p.2))
    (hRows : ∀ j x, (L (eL j.1 j.2.2 x) ∩ blocked j).card + ∑ y, H j x y = b)
    (hCols : ∀ j y, (R (eR j.1 j.2.2 y) ∩ blocked j).card + ∑ x, H j x y = b)
    (hBlockedL : ∀ j i, (L i ∩ blocked j).card ≤ b)
    (hRoomL : ∀ i, b + forbidden ≤ (L i).card)
    (hRoomR : ∀ j x y, 0 < H j x y →
      ∀ u ∈ L (eL j.1 j.2.2 x), u ∉ blocked j →
      b + forbidden + cap ≤ ((R (eR j.1 j.2.2 y)).filter (adj u)).card) :
    let M j := embeddedAugmentationMatrix (eL j.1 j.2.2) (eR j.1 j.2.2) (H j)
    let requests j := @Finset.filter (ScheduledAugmentationRequest M) (fun e => e.1 = j)
      (Classical.decPred _) univ
    ∃ f g : ScheduledAugmentationRequest M → V,
      (∀ e, f e ∈ L e.2.1 ∧ g e ∈ R e.2.2.1 ∧
        f e ∉ blocked e.1 ∧ g e ∉ blocked e.1 ∧ adj (f e) (g e)) ∧
      Function.Injective (fun e => s(f e,g e)) ∧
      (∀ v, augmentationLoad univ f g v ≤ cap) ∧
      (∀ j x, (L (eL j.1 j.2.2 x) ∩ (blocked j ∪ (requests j).image f)).card = b) ∧
      (∀ j y, (R (eR j.1 j.2.2 y) ∩ (blocked j ∪ (requests j).image g)).card = b) := by
  classical
  intro M requests
  let row j i := ∑ k, M j i k
  let col j k := ∑ i, M j i k
  have hRow j i : row j i = if p : i ∈ Set.range (eL j.1 j.2.2) then
      ∑ y, H j (Classical.choose p) y else 0 := by
    change (∑ k, M j i k) = _
    exact (embeddedAugmentationMatrix_rows _ _ _ _).trans (embeddedAugmentation_load _ _ _)
  have hCol j k : col j k = if p : k ∈ Set.range (eR j.1 j.2.2) then
      ∑ x, H j x (Classical.choose p) else 0 := by
    change (∑ i, M j i k) = _
    exact (embeddedAugmentationMatrix_cols _ _ _ _).trans (embeddedAugmentation_load _ _ _)
  have hRowOn j x : row j (eL j.1 j.2.2 x) = ∑ y, H j x y := by
    rw [hRow, dite_eq_left (Set.mem_range_self x)]
    have hEq : Classical.choose (Set.mem_range_self (f := eL j.1 j.2.2) x) = x :=
      (eL j.1 j.2.2).injective (Classical.choose_spec (Set.mem_range_self x))
    rw [hEq]
  have hColOn j y : col j (eR j.1 j.2.2 y) = ∑ x, H j x y := by
    rw [hCol, dite_eq_left (Set.mem_range_self y)]
    have hEq : Classical.choose (Set.mem_range_self (f := eR j.1 j.2.2) y) = y :=
      (eR j.1 j.2.2).injective (Classical.choose_spec (Set.mem_range_self y))
    rw [hEq]
  have hRowLe j i : (L i ∩ blocked j).card + row j i ≤ b := by
    by_cases p : i ∈ Set.range (eL j.1 j.2.2)
    · obtain ⟨x, rfl⟩ := p
      rw [hRowOn]
      exact (hRows j x).le
    · rw [hRow, dite_eq_right p, add_zero]
      exact hBlockedL j i
  have hColLe j k : col j k ≤ b := by
    by_cases p : k ∈ Set.range (eR j.1 j.2.2)
    · obtain ⟨y, rfl⟩ := p
      rw [hColOn]
      exact (Nat.le_add_left _ _).trans_eq (hCols j y)
    · simp [hCol, p]
  have hTotalL (i : I) : (∑ j, row j i) ≤ 4*s*b := by
    apply phase_load_bound (fun p u (x : X) => eL p u x) hPhaseL _ i b
      (fun j => (Nat.le_add_left _ _).trans (hRowLe j i))
    intro j hj
    by_contra hn
    have hn' : i ∉ Set.range (eL j.1 j.2.2) := hn
    rw [hRow, dite_eq_right hn'] at hj
    omega
  have hTotalR (k : K) : (∑ j, col j k) ≤ 4*s*b := by
    apply phase_load_bound (fun p u (y : Y) => eR p u y) hPhaseR _ k b (fun j => hColLe j k)
    intro j hj
    by_contra hn
    have hn' : k ∉ Set.range (eR j.1 j.2.2) := hn
    rw [hCol, dite_eq_right hn'] at hj
    omega
  obtain ⟨f,g,hEdge,_,hUnique,hCapLoad,hCountL,hCountR⟩ :=
    exists_scheduled_augmentation_of_matrices adj L R M blocked cap (4*s*b) forbidden
      hCap hBudget hL hR hCross hTotalL hTotalR
      (fun j i => (Nat.add_le_add_right (hRowLe j i) _).trans (hRoomL i))
      (fun j i k hPos u hu hFree => by
        obtain ⟨x,y,hx,hy,hPositive⟩ := embeddedAugmentationMatrix_positive _ _ _ _ _ hPos
        subst i
        subst k
        change (R _ ∩ blocked j).card + col j _ + forbidden + cap ≤ _
        rw [hColOn, hCols]
        exact hRoomR j x y hPositive u hu hFree)
  refine ⟨f,g,hEdge,hUnique,hCapLoad,?_,?_⟩
  · intro j x
    exact (hCountL j _).trans (by
      change (L _ ∩ blocked j).card + row j _ = b
      rw [hRowOn]
      exact hRows j x)
  · intro j y
    exact (hCountR j _).trans (by
      change (R _ ∩ blocked j).card + col j _ = b
      rw [hColOn]
      exact hCols j y)

/-- Half-index of the left subcluster in an augmentation cycle.
The second cycle uses the successor of the first cycle's left
subcluster, including the wrap between intervals. -/
def canonicalAugmentationLeft {h f ℓ : ℕ}
    (b : Fin h × Fin f) (u : Fin 2) : Fin ℓ ↪ Fin h × Fin (f*ℓ) where
  toFun x := (b.1, if u = 0 then finProdFinEquiv (b.2,x) else
    finRotate (f*ℓ) (finProdFinEquiv (b.2,x)))
  inj' := by
    intro x y he
    have hh := congrArg Prod.snd he
    by_cases hu : u = 0
    · simp only [hu, ite_true] at hh
      exact congrArg Prod.snd (finProdFinEquiv.injective hh)
    · simp only [ite_eq_right hu] at hh
      exact congrArg Prod.snd (finProdFinEquiv.injective ((finRotate _).injective hh))

/-- The right subclusters have the same half-indices in both cycles. -/
def canonicalAugmentationRight {h f ℓ : ℕ}
    (b : Fin h × Fin f) : Fin ℓ ↪ Fin h × Fin (f*ℓ) :=
  canonicalAugmentationLeft b 0

theorem canonicalAugmentationLeft_injective {h f ℓ : ℕ} (u : Fin 2) :
    Function.Injective (fun p : (Fin h × Fin f) × Fin ℓ =>
      canonicalAugmentationLeft p.1 u p.2) := by
  intro p q he
  have hFirst : p.1.1 = q.1.1 := congrArg (fun x : Fin h × Fin (f*ℓ) => x.1) he
  have hSecond := congrArg Prod.snd he
  change (if u = 0 then finProdFinEquiv (p.1.2,p.2) else
      finRotate (f*ℓ) (finProdFinEquiv (p.1.2,p.2))) =
    (if u = 0 then finProdFinEquiv (q.1.2,q.2) else
      finRotate (f*ℓ) (finProdFinEquiv (q.1.2,q.2))) at hSecond
  have hPair : (p.1.2,p.2) = (q.1.2,q.2) := by
    apply finProdFinEquiv.injective
    by_cases hu : u = 0
    · simpa [hu] using hSecond
    · apply (finRotate (f*ℓ)).injective
      simpa [hu] using hSecond
  exact Prod.ext (Prod.ext hFirst (congrArg (fun a : Fin f × Fin ℓ => a.1) hPair))
    (congrArg (fun a : Fin f × Fin ℓ => a.2) hPair)

/-- For each augmentation cycle the local positions enumerate the
global half-indices, including the shared boundaries. -/
theorem canonicalAugmentationLeft_bijective {h f ℓ : ℕ} (u : Fin 2) :
    Function.Bijective (fun p : (Fin h × Fin f) × Fin ℓ =>
      canonicalAugmentationLeft p.1 u p.2) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨canonicalAugmentationLeft_injective u, by simp [mul_assoc]⟩

/-- Expand a half-index into the even or odd position on the full
cluster cycle. -/
def canonicalAugmentationPosition {f ℓ : ℕ} (u : Fin 2) (x : Fin (f*ℓ)) : Fin (f*(2*ℓ)) :=
  ⟨2*x.val+u.val, by
    have hmul : f*(2*ℓ) = 2*(f*ℓ) := by ring
    rw [hmul]
    have := u.isLt
    have := x.isLt
    omega⟩

theorem canonicalAugmentationLeft_position {h f ℓ : ℕ} (hf : 0 < f) (hℓ : 0 < ℓ)
    (b : Fin h × Fin f) (u : Fin 2) (x : Fin ℓ) :
    canonicalAugmentationPosition 0 (canonicalAugmentationLeft b u x).2 =
      canonicalSpecialPosition hf (by omega : 0 < 2*ℓ) b.2 (2*x.val+if u=0 then 0 else 2) := by
  have hLift (i : ℕ) :
      canonicalAugmentationPosition 0 (canonicalSpecialPosition hf hℓ b.2 i) =
        canonicalSpecialPosition hf (by omega : 0 < 2*ℓ) b.2 (2*i) := by
    apply Fin.ext
    change 2*((b.2.val*ℓ+i)%(f*ℓ))+0 = (b.2.val*(2*ℓ)+2*i)%(f*(2*ℓ))
    rw [show b.2.val*(2*ℓ)+2*i = 2*(b.2.val*ℓ+i) by ring,
      show f*(2*ℓ) = 2*(f*ℓ) by ring, Nat.mul_mod_mul_left, add_zero]
  by_cases hu : u=0
  · simpa [canonicalAugmentationLeft, hu, canonicalSpecialPosition_of_lt hf hℓ] using hLift x.val
  · have hh := hLift (x.val+1)
    rw [canonicalSpecialPosition_succ, canonicalSpecialPosition_of_lt] at hh
    simpa [canonicalAugmentationLeft, hu, Nat.mul_succ] using hh

theorem canonicalAugmentationRight_position {h f ℓ : ℕ} (hf : 0 < f) (hℓ : 0 < ℓ)
    (b : Fin h × Fin f) (x : Fin ℓ) :
    canonicalAugmentationPosition 1 (canonicalAugmentationRight b x).2 =
      canonicalSpecialPosition hf (by omega : 0 < 2*ℓ) b.2 (2*x.val+1) := by
  change canonicalAugmentationPosition 1 (finProdFinEquiv (b.2,x)) = _
  have hSource : canonicalSpecialPosition hf (by omega : 0 < 2*ℓ) b.2 (2*x.val) =
      canonicalAugmentationPosition 0 (finProdFinEquiv (b.2,x)) := by
    simpa [canonicalAugmentationLeft] using (canonicalAugmentationLeft_position hf hℓ b 0 x).symm
  rw [canonicalSpecialPosition_succ, hSource]
  apply Fin.ext
  rw [finRotate_apply, Fin.val_add_one_of_lt']
  · rfl
  · have hmul : f*(2*ℓ) = 2*(f*ℓ) := by ring
    change 2*(finProdFinEquiv (b.2,x)).val + 0 + 1 < f*(2*ℓ)
    rw [hmul]
    have := (finProdFinEquiv (b.2,x)).isLt
    omega

/-- Identify the local cycle clusters with their physical global
indices. Within each augmentation, a boundary cluster belongs to
the unique interval that uses it on that cycle. -/
theorem canonicalAugmentation_clusters {h f ℓ : ℕ} (hf : 0 < f) (hℓ : 0 < ℓ)
    (C : Fin h × Fin (f*(2*ℓ)) → Finset V)
    (hDisj : Pairwise (fun i j => Disjoint (C i) (C j))) :
    let A := canonicalSpecialCluster hf (by omega : 0 < 2*ℓ) C
    let L (i : Fin h × Fin (f*ℓ)) := C (i.1, canonicalAugmentationPosition 0 i.2)
    let R (i : Fin h × Fin (f*ℓ)) := C (i.1, canonicalAugmentationPosition 1 i.2)
    (Pairwise fun i j => Disjoint (L i) (L j)) ∧
    (Pairwise fun i j => Disjoint (R i) (R j)) ∧
    (∀ i j, Disjoint (L i) (R j)) ∧
    (∀ b u x, L (canonicalAugmentationLeft b u x) = A b (2*x.val+if u=0 then 0 else 2)) ∧
    (∀ b x, R (canonicalAugmentationRight b x) = A b (2*x.val+1)) := by
  intro A L R
  have hInj (u : Fin 2) :
      Function.Injective (fun i : Fin h × Fin (f*ℓ) => (i.1, canonicalAugmentationPosition u i.2)) := by
    intro i j he
    have h₁ := congrArg (fun a : Fin h × Fin (f*(2*ℓ)) => a.1) he
    have h₂ := congrArg (fun a : Fin h × Fin (f*(2*ℓ)) => a.2.val) he
    change 2*i.2.val+u.val = 2*j.2.val+u.val at h₂
    exact Prod.ext h₁ (Fin.ext (by omega))
  refine ⟨fun _ _ hn => hDisj (fun he => hn (hInj 0 he)),
    fun _ _ hn => hDisj (fun he => hn (hInj 1 he)), ?_, ?_, ?_⟩
  · intro i j
    apply hDisj
    intro he
    have h₂ := congrArg (fun a : Fin h × Fin (f*(2*ℓ)) => a.2.val) he
    change 2*i.2.val+0 = 2*j.2.val+1 at h₂
    omega
  · intro b u x
    change C (b.1, canonicalAugmentationPosition 0 (canonicalAugmentationLeft b u x).2) =
      C (b.1, canonicalSpecialPosition hf (by omega) b.2 (2*x.val+if u=0 then 0 else 2))
    rw [canonicalAugmentationLeft_position hf hℓ]
  · intro b x
    change C (b.1, canonicalAugmentationPosition 1 (canonicalAugmentationRight b x).2) =
      C (b.1, canonicalSpecialPosition hf (by omega) b.2 (2*x.val+1))
    rw [canonicalAugmentationRight_position hf hℓ]

/-- Realize all local cycle assignments on the canonical subclusters.
The occupied sets for the special paths are the augmented endpoints
intersected with their corresponding subclusters. -/
theorem exists_canonical_augmentation_of_interval_matrices
    [Fintype V] [DecidableEq V] [Nonempty V] {h f ℓ s : ℕ}
    (hf : 0 < f) (hℓ : 0 < ℓ)
    (C : Fin h × Fin (f*(2*ℓ)) → Finset V)
    (adj : V → V → Prop) [DecidableRel adj]
    (H : (Fin h × Fin f) × (Fin s × Fin 2) → Fin ℓ → Fin ℓ → ℕ)
    (blocked : (Fin h × Fin f) × (Fin s × Fin 2) → Finset V)
    (b forbidden cap : ℕ)
    (hCap : 0 < cap) (hBudget : 4*s*b ≤ forbidden*cap)
    (hDisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hBlocked : ∀ j, (blocked j).card ≤ b)
    (hRoomL : ∀ i, b + forbidden ≤ (C i).card) :
    let A := canonicalSpecialCluster hf (by omega : 0 < 2*ℓ) C
    let left (j : (Fin h × Fin f) × (Fin s × Fin 2)) (x : Fin ℓ) :=
      A j.1 (2*x.val + if j.2.2 = 0 then 0 else 2)
    let right (j : (Fin h × Fin f) × (Fin s × Fin 2)) (y : Fin ℓ) := A j.1 (2*y.val+1)
    (∀ j x, (left j x ∩ blocked j).card + ∑ y, H j x y = b) →
    (∀ j y, (right j y ∩ blocked j).card + ∑ x, H j x y = b) →
    (∀ j x y, 0 < H j x y → ∀ v ∈ left j x, v ∉ blocked j →
      b + forbidden + cap ≤ ((right j y).filter (adj v)).card) →
    let M j := embeddedAugmentationMatrix (canonicalAugmentationLeft j.1 j.2.2)
      (canonicalAugmentationRight j.1) (H j)
    let requests j := @Finset.filter (ScheduledAugmentationRequest M) (fun e => e.1 = j)
      (Classical.decPred _) univ
    ∃ gL gR : ScheduledAugmentationRequest M → V,
      (∀ e, adj (gL e) (gR e) ∧ gL e ∉ blocked e.1 ∧ gR e ∉ blocked e.1) ∧
      Function.Injective (fun e => s(gL e,gR e)) ∧
      (∀ v, augmentationLoad univ gL gR v ≤ cap) ∧
      (∀ j x, (left j x ∩ (blocked j ∪ (requests j).image gL)).card = b) ∧
      (∀ j y, (right j y ∩ (blocked j ∪ (requests j).image gR)).card = b) := by
  intro A left right hRows hCols hRoomR M requests
  let L (i : Fin h × Fin (f*ℓ)) := C (i.1, canonicalAugmentationPosition 0 i.2)
  let R (i : Fin h × Fin (f*ℓ)) := C (i.1, canonicalAugmentationPosition 1 i.2)
  obtain ⟨hL,hR,hCross,hLeft,hRight⟩ := canonicalAugmentation_clusters hf hℓ C hDisj
  have hLeft' (j : (Fin h × Fin f) × (Fin s × Fin 2)) (x : Fin ℓ) :
      L (canonicalAugmentationLeft j.1 j.2.2 x) = left j x := hLeft j.1 j.2.2 x
  have hRight' (j : (Fin h × Fin f) × (Fin s × Fin 2)) (y : Fin ℓ) :
      R (canonicalAugmentationRight j.1 y) = right j y := hRight j.1 y
  obtain ⟨gL,gR,hEdge,hUnique,hLoad,hCountL,hCountR⟩ :=
    exists_global_augmentation_of_interval_matrices adj L R canonicalAugmentationLeft
      (fun c _ => canonicalAugmentationRight c) H blocked b forbidden cap hCap hBudget hL hR hCross
      canonicalAugmentationLeft_injective (fun _ => canonicalAugmentationLeft_injective 0)
      (fun j x => by rw [hLeft' j x]; exact hRows j x)
      (fun j y => by rw [hRight' j y]; exact hCols j y)
      (fun j _ => (card_le_card inter_subset_right).trans (hBlocked j))
      (fun i => hRoomL _)
      (fun j x y hPos v hv hFree => by
        rw [hRight' j y]
        exact hRoomR j x y hPos v (by rwa [hLeft' j x] at hv) hFree)
  refine ⟨gL,gR,fun e => ⟨(hEdge e).2.2.2.2,(hEdge e).2.2.1,(hEdge e).2.2.2.1⟩,
    hUnique,hLoad,?_,?_⟩
  · intro j x
    have h := hCountL j x
    rw [hLeft' j x] at h
    exact h
  · intro j y
    have h := hCountR j y
    rw [hRight' j y] at h
    exact h

/-- Convert the occupied sets after the two augmentations into
the sets U and W on each successive pair of the special path
system. They have size b even at the shared boundaries. -/
theorem canonical_augmented_occupied_sets [DecidableEq V] {B J : Type*} {ℓ : ℕ}
    (A : B → ℕ → Finset V) (left right : B → J → Fin 2 → Finset V) (b : ℕ)
    (hL : ∀ c j (u : Fin 2) (x : Fin ℓ),
      (A c (2*x.val+if u=0 then 0 else 2) ∩ left c j u).card = b)
    (hR : ∀ c j u (x : Fin ℓ), (A c (2*x.val+1) ∩ right c j u).card = b) :
    let U (c : B) (j : J) (i : ℕ) :=
      A c i ∩ (if i % 2 = 0 then left c j 0 else right c j 1)
    let W (c : B) (j : J) (i : ℕ) :=
      A c (i+1) ∩ (if i % 2 = 0 then right c j 0 else left c j 1)
    (∀ c j i, U c j i ⊆ A c i) ∧ (∀ c j i, W c j i ⊆ A c (i+1)) ∧
    ∀ c j i, i < 2*ℓ → (U c j i).card = b ∧ (W c j i).card = b := by
  intro U W
  refine ⟨fun _ _ _ => inter_subset_left, fun _ _ _ => inter_subset_left, ?_⟩
  intro c j i hi
  let x : Fin ℓ := ⟨i/2, by omega⟩
  by_cases he : i % 2 = 0
  · have hEq : 2*x.val = i := by dsimp [x]; omega
    refine ⟨?_, ?_⟩
    · simpa [U, he, hEq] using hL c j 0 x
    · simpa [W, he, hEq] using hR c j 0 x
  · have hEq : 2*x.val+1 = i := by dsimp [x]; omega
    have hNext : 2*x.val+2 = i+1 := by omega
    refine ⟨?_, ?_⟩
    · simpa [U, he, hEq] using hR c j 1 x
    · simpa [W, he, hNext] using hL c j 1 x

end OverfullWork.ChenShan
