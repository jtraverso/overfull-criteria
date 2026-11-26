module

public import OverfullWork.ChenShanNestedDegreeControl
public import OverfullWork.ChenShanRepairTripartite
import OverfullWork.DenseHall

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]

private theorem card_out_arcs_eq_neighbors {V : Type*} [Fintype V]
    (G : Finset (V × V)) (v : V) :
    ((G.filter fun e => e.1 = v).card) = (arcOutNeighbors G v).card := by
  let f : V ↪ V × V := ⟨fun w => (v,w),fun _ _ h => congrArg Prod.snd h⟩
  have hEq : G.filter (fun e => e.1 = v) = (arcOutNeighbors G v).map f := by
    ext e
    rcases e with ⟨a,b⟩
    simp only [mem_filter,mem_map,mem_arcOutNeighbors]
    constructor
    · rintro ⟨he,rfl⟩
      exact ⟨b,he,rfl⟩
    · rintro ⟨w,hw,he⟩
      change (v,w) = (a,b) at he
      cases he
      exact ⟨hw,rfl⟩
  rw [hEq,card_map]

private theorem card_in_arcs_eq_neighbors {V : Type*} [Fintype V]
    (G : Finset (V × V)) (v : V) :
    ((G.filter fun e => e.2 = v).card) = (arcInNeighbors G v).card := by
  let f : V ↪ V × V := ⟨fun w => (w,v),fun _ _ h => congrArg Prod.fst h⟩
  have hEq : G.filter (fun e => e.2 = v) = (arcInNeighbors G v).map f := by
    ext e
    rcases e with ⟨a,b⟩
    simp only [mem_filter,mem_map,mem_arcInNeighbors]
    constructor
    · rintro ⟨he,rfl⟩
      exact ⟨a,he,rfl⟩
    · rintro ⟨w,hw,he⟩
      change (w,v) = (a,b) at he
      cases he
      exact ⟨hw,rfl⟩
  rw [hEq,card_map]

theorem arcDivergence_eq_neighbor_counts {V : Type*} [Fintype V]
    (G : Finset (V × V)) (v : V) :
    arcDivergence G v = ((arcOutNeighbors G v).card : ℤ) - (arcInNeighbors G v).card := by
  unfold arcDivergence
  rw [card_out_arcs_eq_neighbors,card_in_arcs_eq_neighbors]

private theorem abs_gap_of_sampled_degrees {x y p q d t : ℝ}
    (hx : |x-p*d| ≤ t) (hy : |y-q*d| ≤ t)
    (hpq : |p*d-q*d| ≤ 1/2) : |x-y| ≤ 2*t+1/2 := by
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  have hpq' := abs_le.mp hpq
  exact abs_le.mpr ⟨by linarith only [hx'.1,hy'.2,hpq'.1],
    by linarith only [hx'.2,hy'.1,hpq'.2]⟩

private theorem color_rounding_degree_gap {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (s : ℕ) {d : ℝ} (hd : 0 ≤ d) (hd₁ : d ≤ k) :
    |((nestedColorSize ((k:ℝ)/m) s : ℝ)/k)*d-((s:ℝ)/m)*d| ≤ 1/2 := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hRound := nestedColorSize_error ((k:ℝ)/m) (by positivity) s
  have hEq : ((nestedColorSize ((k:ℝ)/m) s : ℝ)/k)*d-((s:ℝ)/m)*d =
      d/((k:ℝ)) * ((nestedColorSize ((k:ℝ)/m) s : ℝ) - ((k:ℝ)/m)*s) := by
    field_simp [hmR.ne',hkR.ne']
  rw [hEq,abs_mul,abs_of_nonneg (div_nonneg hd hkR.le)]
  have hOne : d/(k:ℝ) ≤ 1 := (div_le_iff₀ hkR).mpr (by simpa only [one_mul] using hd₁)
  exact (mul_le_mul hOne hRound (abs_nonneg _) (by norm_num)).trans_eq (by ring)

private theorem prefix_induced_degree_error {U V : Type*} [Fintype U] [Fintype V]
    (E : U → V → Prop) (X : Finset U) (Y : Finset V)
    (v : X) (t : ℝ) (h : sampledDegreeError E v Y ≤ t) :
    |((univ.filter (fun w : Y => E v w)).card : ℝ) -
      ((Y.card : ℝ)/Fintype.card V)*(univ.filter (E v)).card| ≤ t := by
  rw [DenseHall.subtype_filter_card Y (E v)]
  unfold sampledDegreeError at h
  have hEq : (univ.filter (E v)) ∩ Y = Y.filter (E v) := by
    ext w
    simp only [mem_inter,mem_filter,mem_univ,true_and,and_comm]
  simpa only [hEq] using h

/-- Equation (4.21). The two errors at a vertex add, and the rounded
color proportion costs at most one half of one neighbor. -/
theorem nested_prefix_imbalance {ρ : ℝ} {m k l : ℕ}
    (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop)
    (S : NestedTripartitePrefixes A B W ρ m k l) (ξ : ℝ)
    (hm : 0 < m) (hk : 0 < k)
    (hA : Fintype.card A = m) (hB : Fintype.card B = m) (hW : Fintype.card W = k)
    (hBal : TripartiteLocallyBalanced E L R)
    (hSample : TripartitePrefixDegreeControl E L R S ξ) (i : ℕ) (hi : i ≤ l)
    (v : ↥(S.left i) ⊕ ↥(S.right i) ⊕ ↥(S.colors i)) :
    |(arcDivergence
      (tripartiteArcs (fun a b => E a.1 b.1) (fun a w => L a.1 w.1) (fun b w => R b.1 w.1)) v : ℝ)|
      ≤ 2*ξ*nestedCoreSize ρ m i + 1/2 := by
  let s := nestedCoreSize ρ m i
  rw [arcDivergence_eq_neighbor_counts,Int.cast_sub,Int.cast_natCast,Int.cast_natCast,
    card_tripartite_outNeighbors,card_tripartite_inNeighbors]
  rcases v with a | (b | w)
  · have hAB := prefix_induced_degree_error E (S.left i) (S.right i) a _ (by
      simpa only [Nat.add_zero] using hSample.leftRight i hi 0 (by decide) (by simpa using hi) a a.2)
    have hAW := prefix_induced_degree_error L (S.left i) (S.colors i) a _ (by
      simpa only [Nat.add_zero] using hSample.leftColors i hi 0 (by decide) (by simpa using hi) a a.2)
    have hDeg : (univ.filter (E a)).card = (univ.filter (L a)).card := by
      simpa only [Fintype.card_subtype] using hBal.1 a
    rw [S.rightSize i hi,hB,hDeg] at hAB
    rw [S.colorsSize i hi,hW] at hAW
    have hh := color_rounding_degree_gap hm hk s
      (Nat.cast_nonneg (α := ℝ) ((univ.filter (L a)).card))
      (by exact_mod_cast (card_le_univ (univ.filter (L a))).trans_eq hW)
    rw [abs_sub_comm] at hh
    simpa only [mul_assoc] using abs_gap_of_sampled_degrees hAB hAW hh
  · have hBA := prefix_induced_degree_error (fun b a => E a b) (S.right i) (S.left i) b _ (by
      simpa only [Nat.add_zero] using hSample.rightLeft i hi 0 (by decide) (by simpa using hi) b b.2)
    have hBW := prefix_induced_degree_error R (S.right i) (S.colors i) b _ (by
      simpa only [Nat.add_zero] using hSample.rightColors i hi 0 (by decide) (by simpa using hi) b b.2)
    have hDeg : (univ.filter (fun a => E a b)).card = (univ.filter (R b)).card := by
      simpa only [Fintype.card_subtype] using hBal.2.1 b
    rw [S.leftSize i hi,hA,hDeg] at hBA
    rw [S.colorsSize i hi,hW] at hBW
    have hh := color_rounding_degree_gap hm hk s
      (Nat.cast_nonneg (α := ℝ) ((univ.filter (R b)).card))
      (by exact_mod_cast (card_le_univ (univ.filter (R b))).trans_eq hW)
    simpa only [mul_assoc] using abs_gap_of_sampled_degrees hBW hBA hh
  · have hWA := prefix_induced_degree_error (fun w a => L a w) (S.colors i) (S.left i) w _ (by
      simpa only [Nat.add_zero] using hSample.colorsLeft i hi 0 (by decide) (by simpa using hi) w w.2)
    have hWB := prefix_induced_degree_error (fun w b => R b w) (S.colors i) (S.right i) w _ (by
      simpa only [Nat.add_zero] using hSample.colorsRight i hi 0 (by decide) (by simpa using hi) w w.2)
    have hDeg : (univ.filter (fun a => L a w)).card = (univ.filter (fun b => R b w)).card := by
      simpa only [Fintype.card_subtype] using hBal.2.2 w
    rw [S.leftSize i hi,hA,hDeg] at hWA
    rw [S.rightSize i hi,hB] at hWB
    simpa only [mul_assoc] using abs_gap_of_sampled_degrees hWA hWB (by simp)

end OverfullWork.ChenShan
