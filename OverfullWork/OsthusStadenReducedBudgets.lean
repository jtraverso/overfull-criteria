module

public import OverfullWork.OsthusStadenQuotientCopies

@[expose] public section


/-! Transfer weighted degree bounds to the rounded multidigraph.
Each floor pays at most one copy per reduced neighbour. -/
namespace OverfullWork.DirectedRegularPairs

open Finset DirectedRobustExpansion
open scoped Classical
variable {I : Type*} [Fintype I]

noncomputable def supportedDensity (R : Digraph I) (d : I → I → ℝ) (u v : I) : ℝ :=
  if R.Adj u v then d u v else 0

theorem reducedMultiplicity_rounding (R : Digraph I) (d : I → I → ℝ) (β : ℝ)
    (hβ : 0 < β) (hNonneg : ∀ u v, R.Adj u v → 0 ≤ d u v) (u v : I) :
    supportedDensity R d u v-β ≤ β*(reducedMultiplicity R d β u v:ℝ) ∧
      β*(reducedMultiplicity R d β u v:ℝ) ≤ supportedDensity R d u v := by
  by_cases h : R.Adj u v
  · simp only [supportedDensity,reducedMultiplicity,if_pos h]
    have hi := Nat.lt_floor_add_one (d u v/β)
    have hlo := mul_lt_mul_of_pos_right hi hβ
    have hhi := mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg (hNonneg u v h) hβ.le)) hβ.le
    rw [div_mul_cancel₀ _ hβ.ne'] at hlo hhi
    constructor <;> linarith only [hlo,hhi]
  · simp [supportedDensity,reducedMultiplicity,h,hβ.le]

/-- Lower and upper reduced degree bounds, paying the floor loss in (6)
on each side separately. The similarly rounded dense support can be
obtained by using its own support digraph as the argument. -/
theorem reduced_semidegrees_of_density_budget (R : Digraph I) (d : I → I → ℝ)
    (β lower upper : ℝ) (hβ : 0 < β) (hNonneg : ∀ u v, R.Adj u v → 0 ≤ d u v)
    (hRow : ∀ u, lower ≤ (∑ v,supportedDensity R d u v) ∧ (∑ v,supportedDensity R d u v) ≤ upper)
    (hCol : ∀ v, lower ≤ (∑ u,supportedDensity R d u v) ∧ (∑ u,supportedDensity R d u v) ≤ upper) :
    let M := reducedMultiplicity R d β
    (∀ u, lower-β*(Fintype.card I:ℝ) ≤ β*(↑(∑ v,M u v):ℝ) ∧ β*(↑(∑ v,M u v):ℝ) ≤ upper) ∧
    ∀ v, lower-β*(Fintype.card I:ℝ) ≤ β*(↑(∑ u,M u v):ℝ) ∧ β*(↑(∑ u,M u v):ℝ) ≤ upper := by
  have hSum (d' : I → ℝ) (m : I → ℕ)
      (h₁ : ∀ i, d' i-β ≤ β*(m i:ℝ)) (h₂ : ∀ i, β*(m i:ℝ) ≤ d' i)
      (h₃ : lower ≤ ∑ i,d' i) (h₄ : (∑ i,d' i) ≤ upper) :
      lower-β*(Fintype.card I:ℝ) ≤ β*(↑(∑ i,m i):ℝ) ∧ β*(↑(∑ i,m i):ℝ) ≤ upper := by
    have hl := sum_le_sum (s := (univ : Finset I)) (fun i _ => h₁ i)
    have hu := sum_le_sum (s := (univ : Finset I)) (fun i _ => h₂ i)
    simp only [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,←mul_sum,←Nat.cast_sum] at hl hu
    exact ⟨by linarith only [hl,h₃],hu.trans h₄⟩
  exact ⟨fun u => hSum _ _ (fun v => (reducedMultiplicity_rounding R d β hβ hNonneg u v).1)
      (fun v => (reducedMultiplicity_rounding R d β hβ hNonneg u v).2) (hRow u).1 (hRow u).2,
    fun v => hSum _ _ (fun u => (reducedMultiplicity_rounding R d β hβ hNonneg u v).1)
      (fun u => (reducedMultiplicity_rounding R d β hβ hNonneg u v).2) (hCol v).1 (hCol v).2⟩

/-- Restricting the support produces a parallel submatrix, with every
retained edge still backed by the requested number of copies. -/
theorem reduced_dense_submatrix (R S : Digraph I) (d : I → I → ℝ) (β : ℝ) (q : ℕ)
    (hβ : 0 < β) (hS : S ≤ R)
    (hDense : ∀ i j, S.Adj i j → (q:ℝ)*β ≤ d i j) :
    (∀ i j, reducedMultiplicity S d β i j ≤ reducedMultiplicity R d β i j) ∧
    ∀ i j, S.Adj i j → q ≤ reducedMultiplicity S d β i j := by
  constructor
  · intro i j
    by_cases h : S.Adj i j
    · simp [reducedMultiplicity,h,hS h]
    · simp [reducedMultiplicity,h]
  · intro i j h
    simp only [reducedMultiplicity,if_pos h]
    exact (Nat.le_floor_iff (div_nonneg ((mul_nonneg (Nat.cast_nonneg q) hβ.le).trans (hDense i j h)) hβ.le)).mpr
      ((le_div_iff₀ hβ).mpr (hDense i j h))

/-- Equation (6) uses densities of the actual quotient pairs. Their
weighted degree sums count precisely the arcs to the nonexceptional
vertices, with the two equal cell sizes as denominator. -/
theorem quotient_density_sums {V : Type*} [Fintype V] (D : Digraph V)
    (f : V → Option I) (m : ℕ) (hSize : ∀ i, (DirectedClusterQuotient.cluster f i).card = m)
    (u : I) :
    (∑ v, density D (DirectedClusterQuotient.cluster f u) (DirectedClusterQuotient.cluster f v)) =
      (incidences D (DirectedClusterQuotient.cluster f u) (DirectedClusterQuotient.lift f univ):ℝ) /
        ((m:ℝ)*(m:ℝ)) ∧
    (∑ v, density D (DirectedClusterQuotient.cluster f v) (DirectedClusterQuotient.cluster f u)) =
      (incidences D (DirectedClusterQuotient.lift f univ) (DirectedClusterQuotient.cluster f u):ℝ) /
        ((m:ℝ)*(m:ℝ)) := by
  open DirectedClusterQuotient in
  have hDis : (↑(univ : Finset I) : Set I).PairwiseDisjoint (cluster f) :=
    fun _ _ _ _ h => clusters_disjoint f h
  open DirectedClusterQuotient in
  have hRow : incidences D (cluster f u) (lift f univ) =
      ∑ v,incidences D (cluster f u) (cluster f v) := by
    unfold incidences lift
    rw [sum_biUnion hDis]
  open DirectedClusterQuotient in
  have hCol : incidences D (lift f univ) (cluster f u) =
      ∑ v,incidences D (cluster f v) (cluster f u) := by
    unfold incidences inNeighbours lift
    simp only [filter_biUnion]
    have he (x : V) :
        ((univ : Finset I).biUnion (fun v => (cluster f v).filter (fun y => D.Adj y x))).card =
          ∑ v,((cluster f v).filter (fun y => D.Adj y x)).card :=
      card_biUnion (fun i hi j hj hn => (hDis hi hj hn).mono (filter_subset _ _) (filter_subset _ _))
    simp_rw [he]
    rw [sum_comm]
  constructor
  · simp only [density,hSize,hRow,Nat.cast_sum,div_eq_mul_inv,←sum_mul]
  · simp only [density,hSize,hCol,Nat.cast_sum,div_eq_mul_inv,←sum_mul]

/-- Start from arc counts in the actual pure graph and obtain the
rounded semidegree inequalities used to prepare the reduced factors. -/
theorem reduced_semidegrees_from_cluster_arc_counts {V : Type*} [Fintype V]
    (D : Digraph V) (f : V → Option I) (m : ℕ) (β lo hi : ℝ)
    (hβ : 0 < β) (hm : 0 < m)
    (hSize : ∀ i, (DirectedClusterQuotient.cluster f i).card = m)
    (hRow : ∀ i, lo*((m:ℝ)*(m:ℝ)) ≤
        (incidences D (DirectedClusterQuotient.cluster f i) (DirectedClusterQuotient.lift f univ):ℝ) ∧
      (incidences D (DirectedClusterQuotient.cluster f i) (DirectedClusterQuotient.lift f univ):ℝ) ≤ hi*((m:ℝ)*(m:ℝ)))
    (hCol : ∀ i, lo*((m:ℝ)*(m:ℝ)) ≤
        (incidences D (DirectedClusterQuotient.lift f univ) (DirectedClusterQuotient.cluster f i):ℝ) ∧
      (incidences D (DirectedClusterQuotient.lift f univ) (DirectedClusterQuotient.cluster f i):ℝ) ≤ hi*((m:ℝ)*(m:ℝ))) :
    let M := reducedMultiplicity (DirectedClusterQuotient.quotient D f)
      (fun i j => density D (DirectedClusterQuotient.cluster f i) (DirectedClusterQuotient.cluster f j)) β
    (∀ i, lo-β*(Fintype.card I:ℝ) ≤ β*(↑(∑ j,M i j):ℝ) ∧ β*(↑(∑ j,M i j):ℝ) ≤ hi) ∧
    ∀ i, lo-β*(Fintype.card I:ℝ) ≤ β*(↑(∑ j,M j i):ℝ) ∧ β*(↑(∑ j,M j i):ℝ) ≤ hi := by
  open DirectedClusterQuotient in
  let d (i j : I) := density D (cluster f i) (cluster f j)
  let R := DirectedClusterQuotient.quotient D f
  have hEq (i j : I) : supportedDensity R d i j = d i j := by
    by_cases hij : R.Adj i j
    · exact if_pos hij
    · rw [supportedDensity,if_neg hij]
      have he : (incidences D (DirectedClusterQuotient.cluster f i) (DirectedClusterQuotient.cluster f j):ℝ) = 0 := by
        rw [incidences_eq_sum]
        refine sum_eq_zero (fun v hv => sum_eq_zero (fun u hu => ?_))
        have hn : ¬ D.Adj u v := fun h => hij ⟨u,v,
          (DirectedClusterQuotient.mem_cluster f i u).mp hu,
          (DirectedClusterQuotient.mem_cluster f j v).mp hv,h⟩
        exact if_neg hn
      simp only [d,density,he,zero_div]
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hDen := mul_pos hmR hmR
  apply reduced_semidegrees_of_density_budget R d β lo hi hβ
  · intro i j _
    dsimp [d,density]
    positivity
  · intro i
    simp only [hEq,d,(quotient_density_sums D f m hSize i).1]
    exact ⟨(le_div_iff₀ hDen).mpr (hRow i).1,(div_le_iff₀ hDen).mpr (hRow i).2⟩
  · intro i
    simp only [hEq,d,(quotient_density_sums D f m hSize i).2]
    exact ⟨(le_div_iff₀ hDen).mpr (hCol i).1,(div_le_iff₀ hDen).mpr (hCol i).2⟩

end OverfullWork.DirectedRegularPairs
