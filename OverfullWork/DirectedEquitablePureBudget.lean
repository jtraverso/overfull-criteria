module

public import OverfullWork.DirectedEquitableRegularity
public import OverfullWork.DirectedPurePairGraph
public import OverfullWork.DirectedDegreeTrimming
public import OverfullWork.PurePairPreservation

@[expose] public section


/-! Bound the actual arc loss when forming the pure graph from an
equitable directed partition, before trimming the degrees. -/
namespace OverfullWork.DirectedPairEnergy

open Finset Finpartition DirectedRobustExpansion DirectedClusterQuotient DirectedRegularPairs
open scoped Classical

set_option maxHeartbeats 1700000 in
/-- Count the remaining deleted arcs after taking a bounded-degree
subgraph out of the low-density pairs. Pair regularity is measured
in the original graph and the low-pair cost is supplied separately. -/
theorem equitable_pure_deletion_bound_of_low_pairs {V : Type*} [Fintype V]
    (G D : Digraph V) (P : Finpartition (univ : Finset V)) (m : ℕ) (ε ζ d loss : ℝ)
    (hDG : D ≤ G) (hV : 0 < Fintype.card V) (hLoss : 0 ≤ loss)
    (hSize : ∀ U ∈ P.parts, U.card ≤ m)
    (hRest : (∑ U ∈ P.parts, if U.card = m then (0:ℝ) else (U.card:ℝ)) ≤ ζ*(Fintype.card V:ℝ))
    (hIrregular : irregularMass G P ε ≤ ε) :
    let I := P.parts.filter (fun U => U.card = m)
    ∀ f : V → Option I, (∀ i : I, cluster f i = i.val) →
    let H := restrictPairs G f (regularReduced G f ε d)
    (∀ i j : I, i ≠ j → IsUniform G ε (cluster f i) (cluster f j) →
      density G (cluster f i) (cluster f j) < d →
      (incidences D (cluster f i) (cluster f j):ℝ) ≤ loss*mass (cluster f i) (cluster f j)) →
    (DirectedDegreeTrimming.total (D \ H):ℝ) ≤
      (2*ζ+ε+loss)*(Fintype.card V:ℝ)^2+(m:ℝ)*(Fintype.card V:ℝ) := by
  intro I f hLabels H hLow
  let n : ℝ := Fintype.card V
  let short (U : Finset V) : ℝ := if U.card = m then 0 else U.card
  let diag (U W : Finset V) : ℝ := if U = W then mass U W else 0
  let irr (U W : Finset V) : ℝ := if IsUniform G ε U W then 0 else mass U W
  have hn : 0 < n := by dsimp only [n]; exact_mod_cast hV
  have hCard : (∑ U ∈ P.parts,(U.card:ℝ)) = n := by
    dsimp only [n]
    exact_mod_cast P.sum_card_parts
  have hRect (U W : Finset V) (hU : U ∈ P.parts) (hW : W ∈ P.parts) :
      (incidences (D \ H) U W:ℝ) ≤ short U*(W.card:ℝ)+(U.card:ℝ)*short W+
        diag U W+irr U W+loss*mass U W := by
    have hMass : 0 ≤ mass U W := by dsimp only [mass]; positivity
    have hAll : (incidences (D \ H) U W:ℝ) ≤ mass U W := by
      unfold mass
      exact_mod_cast DirectedArcSelection.incidences_le (D \ H) U W
    have hShort (T : Finset V) : 0 ≤ short T := by dsimp only [short]; split_ifs <;> positivity
    have hS₁ := mul_nonneg (hShort U) (Nat.cast_nonneg (α := ℝ) W.card)
    have hS₂ := mul_nonneg (Nat.cast_nonneg (α := ℝ) U.card) (hShort W)
    have hD : 0 ≤ diag U W := by dsimp only [diag]; split_ifs <;> positivity
    have hI : 0 ≤ irr U W := by dsimp only [irr]; split_ifs <;> positivity
    have hDens := mul_nonneg hLoss hMass
    by_cases hUm : U.card = m
    · by_cases hWm : W.card = m
      · by_cases hUW : U = W
        · simp only [diag,if_pos hUW]
          linarith only [hAll,hS₁,hS₂,hI,hDens]
        · by_cases hRegular : IsUniform G ε U W
          · by_cases hDensity : d ≤ density G U W
            · let i : I := ⟨U,mem_filter.mpr ⟨hU,hUm⟩⟩
              let j : I := ⟨W,mem_filter.mpr ⟨hW,hWm⟩⟩
              have hi : cluster f i = U := hLabels i
              have hj : cluster f j = W := hLabels j
              have hPair : (regularReduced G f ε d).Adj i j :=
                ⟨fun h => hUW (congrArg Subtype.val h),
                  by rwa [hi,hj],by rwa [hi,hj]⟩
              have hEmpty : incidences (D \ H) U W = 0 := by
                unfold incidences
                apply sum_eq_zero
                intro y hy
                unfold inNeighbours
                apply card_eq_zero.mpr
                apply eq_empty_iff_forall_notMem.mpr
                intro x hx
                have h : x ∈ U ∧ (D \ H).Adj x y := by simpa only [mem_filter] using hx
                exact h.2.2 ⟨hDG h.2.1,i,j,(mem_cluster f i x).mp (hi.symm ▸ h.1),
                  (mem_cluster f j y).mp (hj.symm ▸ hy),hPair⟩
              rw [hEmpty,Nat.cast_zero]
              linarith only [hS₁,hS₂,hD,hI,hDens]
            · let i : I := ⟨U,mem_filter.mpr ⟨hU,hUm⟩⟩
              let j : I := ⟨W,mem_filter.mpr ⟨hW,hWm⟩⟩
              have hi : cluster f i = U := hLabels i
              have hj : cluster f j = W := hLabels j
              have hCap := hLow i j (fun h => hUW (congrArg Subtype.val h))
              rw [hi,hj] at hCap
              have hSub : incidences (D \ H) U W ≤ incidences D U W := by
                unfold incidences
                apply sum_le_sum
                intro y _
                unfold inNeighbours
                apply card_le_card
                intro x hx
                have h : x ∈ U ∧ (D \ H).Adj x y := by simpa only [mem_filter] using hx
                simp only [mem_filter]
                exact ⟨h.1,h.2.1⟩
              have hSub' : (incidences (D \ H) U W:ℝ) ≤ (incidences D U W:ℝ) := by exact_mod_cast hSub
              linarith only [hSub',hCap hRegular (lt_of_not_ge hDensity),hS₁,hS₂,hD,hI]
          · simp only [irr,if_neg hRegular]
            linarith only [hAll,hS₁,hS₂,hD,hDens]
      · simp only [short,if_pos hUm,if_neg hWm,zero_mul]
        linarith only [hAll,hD,hI,hDens,show mass U W = (U.card:ℝ)*(W.card:ℝ) from rfl]
    · have hS : short U*(W.card:ℝ) = mass U W := by simp [short,hUm,mass]
      rw [hS]
      linarith only [hAll,hS₂,hD,hI,hDens]
  have hSum := sum_le_sum (s := P.parts) (fun U hU => sum_le_sum (s := P.parts) (fun W hW => hRect U W hU hW))
  have hTotal : (DirectedDegreeTrimming.total (D \ H):ℝ) =
      ∑ U ∈ P.parts,∑ W ∈ P.parts,(incidences (D \ H) U W:ℝ) := by
    have h := incidences_rect_partition (D \ H) P P
    exact_mod_cast (show _ = _ from h.symm)
  have hA : (∑ U ∈ P.parts,∑ W ∈ P.parts,short U*(W.card:ℝ)) = (∑ U ∈ P.parts,short U)*n := by
    simp_rw [←mul_sum,hCard]
    rw [←sum_mul]
  have hB : (∑ U ∈ P.parts,∑ W ∈ P.parts,(U.card:ℝ)*short W) = n*(∑ W ∈ P.parts,short W) := by
    rw [sum_comm]
    simp_rw [←sum_mul,hCard]
    rw [←mul_sum]
  have hDiag : (∑ U ∈ P.parts,∑ W ∈ P.parts,diag U W) ≤ (m:ℝ)*n := by
    rw [mul_comm,←hCard,sum_mul]
    apply sum_le_sum
    intro U hU
    have he : (∑ W ∈ P.parts,diag U W) = mass U U := by
      simp [diag,hU]
    rw [he,mass]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hSize U hU) (Nat.cast_nonneg _)
  have hIr : (∑ U ∈ P.parts,∑ W ∈ P.parts,irr U W) ≤ ε*n^2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos hn)).mp hIrregular
    change (∑ U : P.parts,∑ W : P.parts,irr U.val W.val) ≤ ε*n^2 at h
    rw [Finset.sum_coe_sort P.parts (fun U => ∑ W : P.parts,irr U W.val)] at h
    have hEq (U : Finset V) : (∑ W : P.parts,irr U W.val) = ∑ W ∈ P.parts,irr U W := Finset.sum_coe_sort _ _
    change (∑ U ∈ P.parts,∑ W : P.parts,irr U W.val) ≤ ε*n^2 at h
    simpa only [hEq] using h
  have hDensitySum : (∑ U ∈ P.parts,∑ W ∈ P.parts,loss*mass U W) = loss*n^2 := by
    simp_rw [←mul_sum]
    rw [partition_mass_sum]
  simp_rw [sum_add_distrib] at hSum
  rw [←hTotal,hA,hB,hDensitySum] at hSum
  have hShort := mul_le_mul_of_nonneg_right (show (∑ U ∈ P.parts,short U) ≤ ζ*n from hRest) hn.le
  change _ ≤ (2*ζ+ε+loss)*n^2+(m:ℝ)*n
  linarith only [hSum,hShort,hDiag,hIr]

/-- The arcs discarded from a regular partition are paid for by
short cells, diagonal pairs, irregular pairs, and low-density pairs.
The bound is on arcs in the original digraph. -/
theorem equitable_pure_deletion_bound {V : Type*} [Fintype V]
    (G : Digraph V) (P : Finpartition (univ : Finset V)) (m : ℕ) (ε ζ d : ℝ)
    (hV : 0 < Fintype.card V) (hd : 0 ≤ d)
    (hSize : ∀ U ∈ P.parts, U.card ≤ m)
    (hRest : (∑ U ∈ P.parts, if U.card = m then (0:ℝ) else (U.card:ℝ)) ≤ ζ*(Fintype.card V:ℝ))
    (hIrregular : irregularMass G P ε ≤ ε) :
    let I := P.parts.filter (fun U => U.card = m)
    ∀ f : V → Option I, (∀ i : I, cluster f i = i.val) →
    let H := restrictPairs G f (regularReduced G f ε d)
    (DirectedDegreeTrimming.total (G \ H):ℝ) ≤
      (2*ζ+ε+d)*(Fintype.card V:ℝ)^2+(m:ℝ)*(Fintype.card V:ℝ) := by
  intro I f hLabels H
  apply equitable_pure_deletion_bound_of_low_pairs G G P m ε ζ d d le_rfl hV hd hSize hRest hIrregular f hLabels
  intro i j _ _ hLow
  rw [←density_mass G (cluster f i) (cluster f j),mul_comm d]
  exact mul_le_mul_of_nonneg_left hLow.le (by unfold mass; positivity)

end OverfullWork.DirectedPairEnergy
