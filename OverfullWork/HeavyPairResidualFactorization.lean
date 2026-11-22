module

public import OverfullWork.HeavyPairPeeling
public import OverfullWork.LinearFactorization
public import OverfullWork.GeometricCap
public import OverfullWork.CanonicalImageDegreeRange

@[expose] public section


/-! # Factorize the actual peeled ordinary component using the linear engine

The multiplicity and excess hypotheses are derived from the actual
off-centre addition. The only extra requirements are the displayed
linear order reserve and density for the residual regular degree.
-/
namespace OverfullWork.HeavyPairPeeling
open SimpleGraph Finset HeavyPairBoundary Gate8J2I
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 8000000

theorem internal_mono (A : MultiGraph V) {S T : Finset V} (hST : S ⊆ T) :
    A.twiceInternal S ≤ A.twiceInternal T := by
  apply (sum_le_sum (fun v _ => sum_le_sum_of_subset_of_nonneg hST
    (fun _ _ _ => Nat.zero_le _))).trans
  exact sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => Nat.zero_le _)

theorem ordinary_parallel_budget (D A : MultiGraph V) (d q B : ℕ) (a b : V)
    (c : Certificate (D.addCopies A) d q a b) (hStar : D.IsStarAt a)
    (hBudget : A.twiceInternal (univ.erase a) ≤ B) (x : outside a b) :
    (ordinary c.residual a b).parallelExcess x ≤ B := by
  have hxa := ((mem_outside a b x.val).mp x.property).1
  have hpoint : ∀ y : outside a b,
      (ordinary c.residual a b).mult s(x,y) - 1 ≤ A.mult s(x.val,y.val) := by
    intro y
    have hya := ((mem_outside a b y.val).mp y.property).1
    have hs := hStar x.val y.val hxa hya
    change D.mult s(x.val,y.val) + A.mult s(x.val,y.val) - c.cover.mult s(x.val,y.val) - 1 ≤ _
    omega
  have hsum := sum_le_sum (s := univ) (fun y _ => hpoint y)
  have hsub : outside a b ⊆ univ.erase a := by
    intro w hw
    exact mem_erase.mpr ⟨((mem_outside a b w).mp hw).1, mem_univ _⟩
  have hrow : (∑ y : outside a b, A.mult s(x.val,y.val)) ≤
      A.degreeInto (univ.erase a) x.val := by
    rw [sum_coe_sort (outside a b) (fun y : V => A.mult s(x.val,y))]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  exact hsum.trans (hrow.trans
    (CompletionOffCentreBudget.outside_row_le A B a x.val hxa hBudget))

theorem ordinary_total_degree_bound (D A : MultiGraph V) (d q B : ℕ) (a b : V)
    (c : Certificate (D.addCopies A) d q a b) (hStar : D.IsStarAt a)
    (hBudget : A.twiceInternal (univ.erase a) ≤ B) :
    (∑ x, (ordinary c.residual a b).degree x) ≤
      (outside a b).card * ((outside a b).card-1) + B := by
  have hsub : outside a b ⊆ univ.erase a := by
    intro w hw
    exact mem_erase.mpr ⟨((mem_outside a b w).mp hw).1, mem_univ _⟩
  have hA := (internal_mono A hsub).trans hBudget
  have hD := CanonicalImageDegreeRange.internal_bound_away_from_star D a hStar
    (outside a b) (by simp)
  have hpoint : (∑ x, (ordinary c.residual a b).degree x) ≤
      D.twiceInternal (outside a b) + A.twiceInternal (outside a b) := by
    simp_rw [MultiGraph.degree_eq_sum_mult, ordinary_mult]
    have hs : (∑ x : outside a b, ∑ y : outside a b, c.residual.mult s(x.val,y.val)) =
        ∑ x ∈ outside a b, ∑ y ∈ outside a b, c.residual.mult s(x,y) := by
      calc
        _ = ∑ x : outside a b, ∑ y ∈ outside a b, c.residual.mult s(x.val,y) := by
          apply sum_congr rfl
          intro x _
          exact sum_coe_sort (outside a b) (fun y : V => c.residual.mult s(x.val,y))
        _ = _ := sum_coe_sort (outside a b)
          (fun x : V => ∑ y ∈ outside a b, c.residual.mult s(x,y))
    rw [hs]
    rw [MultiGraph.twiceInternal, MultiGraph.twiceInternal, ← sum_add_distrib]
    apply sum_le_sum
    intro x hx
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro y hy
    exact Nat.sub_le _ _
  omega

/-- Factorization is an output, with all excess/multiplicity conditions
of the existing engine discharged for this actual residual. -/
theorem ordinary_factorization (D A : MultiGraph V) (d q B C m : ℕ) (a b : V)
    (c : Certificate (D.addCopies A) d q a b) (hab : a ≠ b) (hStar : D.IsStarAt a)
    (hBudget : A.twiceInternal (univ.erase a) ≤ B)
    (hC : 4000 ≤ C) (hsize : linearHalfBound C (B+1) ≤ m)
    (hcard : Fintype.card ↥(outside a b) = 2*m)
    (hdense : (C+64)*m ≤ C*(d-2*q)) :
    ∃ F : (ordinary c.residual a b).EdgeColoring (d-2*q), F.IsFactorization := by
  let R := ordinary c.residual a b
  have hreg : R.IsRegularOfDegree (d-2*q) := c.ordinary_regular hab
  have hbudget : ∀ x, R.parallelExcess x ≤ B :=
    ordinary_parallel_budget D A d q B a b c hStar hBudget
  have hmu : ∀ t, R.mult t ≤ B+1 := by
    intro t
    induction t using Sym2.inductionOn with
    | hf x y =>
      have hx := hbudget x
      have hs := single_le_sum (f := fun w => R.mult s(x,w)-1)
        (fun _ _ => Nat.zero_le _) (mem_univ y)
      change (∑ w, (R.mult s(x,w)-1)) ≤ B at hx
      omega
  have hmass := ordinary_total_degree_bound D A d q B a b c hStar hBudget
  have hN : (outside a b).card = 2*m := by
    exact (Fintype.card_coe _).symm.trans hcard
  have hsmall : B+1 ≤ m := by
    have hpow : 1 ≤ C^6 := Nat.one_le_pow _ C (by omega)
    have hcoef : 1 ≤ (10:ℕ)^24*C^6 := by nlinarith only [hpow]
    have hs := Nat.mul_le_mul_right (B+1) hcoef
    change (10:ℕ)^24*C^6*(B+1) ≤ m at hsize
    omega
  have hpos : 0 < m := by omega
  have htotal : (∑ x, R.degree x) = (2*m)*(d-2*q) := by
    calc
      _ = ∑ _x : outside a b, (d-2*q) := sum_congr rfl (fun x _ => hreg x)
      _ = _ := by simp [hN]
  change (∑ x, R.degree x) ≤ (outside a b).card * ((outside a b).card-1) + B at hmass
  rw [htotal,hN] at hmass
  have hUpper : d-2*q ≤ 2*m := by
    have hsub : 2*m-1+1 = 2*m := by omega
    nlinarith only [hmass,hsmall,hpos,hsub]
  have : Nontrivial ↥(outside a b) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x,y,hxy⟩ := exists_pair_ne ↥(outside a b)
  obtain ⟨h,hcapLo,hcap,_,_,_,_,_⟩ := Gate8J2C.exists_geometric_cap B
  exact linear_centre_factorization R x y hxy C (B+1) h B m (d-2*q)
    hC (by omega) hcapLo hcap (by omega) hsize hcard hreg
    (fun t => (hmu t).trans hcapLo) (fun x _ => hbudget x) (Or.inr (hbudget x))
    hUpper hdense

end OverfullWork.HeavyPairPeeling
