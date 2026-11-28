module

public import OverfullWork.ChenShanClusterCycleDemands
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V : Type*}

/-- The total incidence load pays for every vertex that has reached
the augmentation cap. -/
theorem augmentation_saturated_card_mul_le
    (S : Finset V) (load : V → ℕ) (cap : ℕ) :
    (S.filter (fun v => cap ≤ load v)).card*cap ≤ ∑ v ∈ S, load v := by
  let T := S.filter (fun v => cap ≤ load v)
  calc
    _ = ∑ _v ∈ T, cap := by simp [T]
    _ ≤ ∑ v ∈ T, load v := sum_le_sum fun _ hv => (mem_filter.mp hv).2
    _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)

/-- Convert a cluster's total load budget into a bound on the number
of saturated vertices. In §5.1.5 the total budget is 4*s*b. -/
theorem augmentation_saturated_card_le
    (S : Finset V) (load : V → ℕ) (cap budget forbidden : ℕ)
    (hCap : 0 < cap) (hLoad : (∑ v ∈ S, load v) ≤ budget)
    (hBudget : budget ≤ forbidden*cap) :
    (S.filter (fun v => cap ≤ load v)).card ≤ forbidden :=
  Nat.le_of_mul_le_mul_right
    ((augmentation_saturated_card_mul_le S load cap).trans (hLoad.trans hBudget)) hCap

private theorem occupied_or_saturated_card_le [Fintype V] [DecidableEq V]
    (S occupied : Finset V) (load : V → ℕ) (cap : ℕ) :
    (S ∩ (occupied ∪ univ.filter (fun v => cap ≤ load v))).card ≤
      (S ∩ occupied).card + (S.filter (fun v => cap ≤ load v)).card := by
  rw [inter_union_distrib_left]
  have hEq : S ∩ univ.filter (fun v => cap ≤ load v) = S.filter (fun v => cap ≤ load v) := by
    ext v
    simp
  rw [hEq]
  exact card_union_le _ _

/-- The greedy choice in §5.1.5 with both exclusions explicit.
The chosen endpoints are free and below the incidence cap, and the
edge is new. The old-edge relation may include both orientations
of each previously selected undirected edge. -/
theorem exists_augmentation_edge_below_cap [Fintype V] [DecidableEq V]
    (adj old : V → V → Prop) [DecidableRel adj] [DecidableRel old]
    (L R occupied : Finset V) (load : V → ℕ)
    (cap budgetL budgetR forbiddenL forbiddenR : ℕ)
    (hCap : 0 < cap)
    (hLoadL : (∑ v ∈ L, load v) ≤ budgetL) (hLoadR : (∑ v ∈ R, load v) ≤ budgetR)
    (hBudgetL : budgetL ≤ forbiddenL*cap) (hBudgetR : budgetR ≤ forbiddenR*cap)
    (hRoomL : (L ∩ occupied).card + forbiddenL < L.card)
    (hRoomR : ∀ u ∈ L, u ∉ occupied → load u < cap →
      (R ∩ occupied).card + forbiddenR + cap ≤ (R.filter (adj u)).card)
    (hOld : ∀ u ∈ L, (R.filter (old u)).card ≤ load u) :
    ∃ u ∈ L, ∃ v ∈ R, u ∉ occupied ∧ v ∉ occupied ∧
      load u < cap ∧ load v < cap ∧ adj u v ∧ ¬ old u v := by
  classical
  let used := occupied ∪ univ.filter (fun v => cap ≤ load v)
  let remaining : V → V → Prop := fun u v => adj u v ∧ ¬ old u v
  have hFree (u : V) (hu : u ∉ used) : u ∉ occupied ∧ load u < cap := by
    simpa [used, not_or, not_le] using hu
  have hLeft : (L ∩ used).card < L.card :=
    (occupied_or_saturated_card_le L occupied load cap).trans_lt
      ((Nat.add_le_add_left (augmentation_saturated_card_le L load cap budgetL forbiddenL
        hCap hLoadL hBudgetL) _).trans_lt hRoomL)
  have hRight : ∀ u ∈ L, u ∉ used → (R ∩ used).card < (R.filter (remaining u)).card := by
    intro u hu huFree
    have hBlocked := (occupied_or_saturated_card_le R occupied load cap).trans
      (Nat.add_le_add_left (augmentation_saturated_card_le R load cap budgetR forbiddenR
        hCap hLoadR hBudgetR) _)
    have hSub : R.filter (adj u) ⊆ R.filter (remaining u) ∪ R.filter (old u) := by
      intro v hv
      obtain ⟨hvR, hvAdj⟩ := mem_filter.mp hv
      by_cases hvOld : old u v
      · exact mem_union_right _ (mem_filter.mpr ⟨hvR, hvOld⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨hvR, hvAdj, hvOld⟩)
    have hLoss := ((card_le_card hSub).trans (card_union_le _ _)).trans
      (Nat.add_le_add_left (hOld u hu) _)
    have hRoom := hRoomR u hu (hFree u huFree).1 (hFree u huFree).2
    have hBelow := (hFree u huFree).2
    change (R ∩ used).card ≤ _ at hBlocked
    omega
  obtain ⟨u, hu, v, hv, huFree, hvFree, h⟩ :=
    exists_cluster_augmentation_edge remaining L R used hLeft hRight
  exact ⟨u, hu, v, hv, (hFree u huFree).1, (hFree v hvFree).1,
    (hFree u huFree).2, (hFree v hvFree).2, h.1, h.2⟩

/-- Sum the augmentation incidences over at most four uses of the
cluster per round. Empty sets can fill unused positions. -/
theorem augmentation_cluster_total_load_le
    (S : Finset V) (s b : ℕ) (endpoints : Fin s → Fin 4 → Finset V)
    (hEndpoints : ∀ i j, (S ∩ endpoints i j).card ≤ b) :
    (∑ v ∈ S, ∑ i, ∑ j, if v ∈ endpoints i j then 1 else 0) ≤ 4*s*b := by
  rw [sum_comm (s := S)]
  simp_rw [sum_comm (s := S)]
  calc
    _ = ∑ i, ∑ j, (S ∩ endpoints i j).card := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      congr 1
    _ ≤ ∑ _i : Fin s, ∑ _j : Fin 4, b := sum_le_sum fun i _ => sum_le_sum fun j _ => hEndpoints i j
    _ = _ := by simp [mul_comm, mul_left_comm]

/-- The bound used in the paper for the vertices whose incidence
load has reached the threshold d₀²*n/100. -/
theorem augmentation_saturated_card_paper_bound
    (S : Finset V) (load : V → ℕ) (s b n : ℕ) (d₀ : ℝ)
    (hd : 0 < d₀) (hn : 0 < n) (hLoad : (∑ v ∈ S, load v) ≤ 4*s*b) :
    ((S.filter (fun v => d₀^2*n/100 ≤ (load v:ℝ))).card:ℝ) ≤
      400*(s:ℝ)*b/(d₀^2*n) := by
  let threshold : ℝ := d₀^2*n/100
  let T := S.filter (fun v => threshold ≤ (load v:ℝ))
  have hSum : (T.card:ℝ)*threshold ≤ 4*(s:ℝ)*b := by
    calc
      _ = ∑ _v ∈ T, threshold := by simp [nsmul_eq_mul]
      _ ≤ ∑ v ∈ T, (load v:ℝ) := sum_le_sum fun _ hv => (mem_filter.mp hv).2
      _ ≤ ∑ v ∈ S, (load v:ℝ) := sum_le_sum_of_subset_of_nonneg
        (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ _ := by exact_mod_cast hLoad
  change (T.card:ℝ) ≤ _
  apply (le_div_iff₀ (show 0 < d₀^2*(n:ℝ) by positivity)).mpr
  dsimp [threshold] at hSum
  linarith only [hSum]

/-- Choose the integer target used in (5.12) from explicit margins.
The quadratic margin pays for at most d₀*n/100 saturated vertices
when combined with the paper's incidence bound. -/
theorem exists_augmentation_target_of_scaled_margins (ℓ s n : ℕ) (z d₀ : ℝ)
    (hz : 0 ≤ z)
    (hLocal : (ℓ:ℝ)*z+2 ≤ d₀*n/100)
    (hGlobal : (s:ℝ)*((ℓ:ℝ)*z+2) ≤ d₀^3*(n:ℝ)^2/40000) :
    ∃ b : ℕ, (ℓ:ℝ)*z+1 ≤ b ∧ (b:ℝ) < d₀*n/100 ∧
      (s:ℝ)*(b:ℝ) ≤ d₀^3*(n:ℝ)^2/40000 := by
  let target : ℝ := (ℓ:ℝ)*z
  let b := ⌈target⌉₊ + 1
  have hLow := Nat.le_ceil target
  have hHigh := Nat.ceil_lt_add_one (show 0 ≤ target by positivity)
  have hbLow : target+1 ≤ (b:ℝ) := by
    dsimp [b]
    push_cast
    linarith only [hLow]
  have hbHigh : (b:ℝ) < target+2 := by
    dsimp [b]
    push_cast
    linarith only [hHigh]
  exact ⟨b, hbLow, hbHigh.trans_le hLocal,
    (mul_le_mul_of_nonneg_left hbHigh.le (Nat.cast_nonneg s)).trans hGlobal⟩

end OverfullWork.ChenShan
