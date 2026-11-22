module

public import OverfullWork.BernoulliExponentialBudget
public import OverfullWork.KuhnOsthusCodegreeCount

@[expose] public section


/-! A single arc sample tracks all degree and cut statistics with
fraction p and both codegree statistics with fraction p squared. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Real BernoulliPairBlocks DirectedArcSelection
open scoped Classical
universe u
variable {V : Type u} [Fintype V]
set_option maxHeartbeats 2400000

private theorem pairCentered_eq_codegree (D : Digraph V) (p : ℝ)
    (y z : V) (s : V × V → Bool) :
    pairCentered p (fun x => if D.Adj x y ∧ D.Adj x z then 1 else 0) y z s =
      (commonInNeighbours (selected D s) y z:ℝ)-p^2*(commonInNeighbours D y z:ℝ) := by
  simp only [pairCentered,commonInNeighbours,card_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero,mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro x _
  by_cases hy : D.Adj x y <;> by_cases hz : D.Adj x z <;> cases hsY : s (x,y) <;>
    cases hsZ : s (x,z) <;> simp [selected,hy,hz,hsY,hsZ]

private theorem weighted_codegree_exp (D : Digraph V) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (y z : V) (t : ℝ) :
    (∑ s : V × V → Bool, assignmentMass p s *
      exp (t*(if y = z then 0 else (commonInNeighbours (selected D s) y z:ℝ) -
        p^2*(commonInNeighbours D y z:ℝ)))) ≤ exp (t^2*(Fintype.card V:ℝ)/2) := by
  classical
  by_cases hyz : y = z
  · subst z
    simp only [ite_true,mul_zero,exp_zero,mul_one]
    have hOne : (∑ x : V × V → Bool, assignmentMass p x) = 1 := by
      convert (assignmentMass_sum (E := V × V) p) using 1 <;>
        congr 1 <;> ext x <;> simp only [mem_univ]
    rw [hOne]
    exact one_le_exp (by positivity)
  let a : V → ℝ := fun x => if D.Adj x y ∧ D.Adj x z then 1 else 0
  have hv : (∑ i,a i^2) ≤ (Fintype.card V:ℝ) := by
    have h := sum_le_sum (s := (univ : Finset V)) (fun i _ => show a i^2 ≤ (1:ℝ) by
      dsimp [a]
      split <;> norm_num)
    simpa using h
  have hBound := weighted_pair_exp p hp hp1 a hyz t
  simp only [if_neg hyz]
  simp_rw [←pairCentered_eq_codegree]
  exact hBound.trans (exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hv (sq_nonneg t)]))

private theorem weighted_out_codegree_exp (D : Digraph V) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (y z : V) (t : ℝ) :
    (∑ s : V × V → Bool, assignmentMass p s *
      exp (t*(if y = z then 0 else (commonInNeighbours (reverseArcs (selected D s)) y z:ℝ) -
        p^2*(commonInNeighbours (reverseArcs D) y z:ℝ)))) ≤ exp (t^2*(Fintype.card V:ℝ)/2) := by
  let e := Equiv.prodComm V V
  let f : (V × V → Bool) ≃ (V × V → Bool) := Equiv.arrowCongr e (Equiv.refl _)
  have heq : (∑ s : V × V → Bool, assignmentMass p s *
      exp (t*(if y = z then 0 else (commonInNeighbours (reverseArcs (selected D s)) y z:ℝ) -
        p^2*(commonInNeighbours (reverseArcs D) y z:ℝ)))) =
      ∑ s : V × V → Bool, assignmentMass p s *
        exp (t*(if y = z then 0 else (commonInNeighbours (selected (reverseArcs D) s) y z:ℝ) -
          p^2*(commonInNeighbours (reverseArcs D) y z:ℝ))) := by
    apply Fintype.sum_equiv f
    intro s
    have hm : assignmentMass p (f s) = assignmentMass p s := by
      exact e.symm.prod_comp (fun i => coordinateMass p (s i))
    have hs : selected (reverseArcs D) (f s) = reverseArcs (selected D s) := by
      ext x w
      rfl
    rw [hm,hs]
  rw [heq]
  exact weighted_codegree_exp (reverseArcs D) p hp hp1 y z t

private theorem eventual_style_sampling_budget (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      4*(51*(n:ℝ)+n^2)*exp (-(η^2*(n:ℝ))/8) +
        2*(4:ℝ)^n*exp (-(η^2*(n:ℝ)^2)/8) < 1 := by
  obtain ⟨N₀,hN⟩ := eventual_degree_codegree_cut_budget (η/2) (by positivity)
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt (51/(3*η^2/32))
  refine ⟨max N₀ N₁,?_⟩
  intro n hn
  have hnR : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hn₁ := hN₁.trans_le (show (N₁:ℝ) ≤ n by exact_mod_cast (le_max_right _ _).trans hn)
  have hn₂ := (div_lt_iff₀ (show 0 < 3*η^2/32 by positivity)).mp hn₁
  have hExp : (51:ℝ) ≤ exp (3*(η^2*(n:ℝ))/32) := by
    linarith only [hn₂,Real.add_one_le_exp (3*(η^2*(n:ℝ))/32)]
  have he : exp (3*(η^2*(n:ℝ))/32)*exp (-(η^2*(n:ℝ))/8) =
      exp (-((η/2)^2*(n:ℝ))/8) := by rw [←exp_add]; congr 1; ring
  have hSmall : 4*(51*(n:ℝ)+n^2)*exp (-(η^2*(n:ℝ))/8) ≤
      4*((n:ℝ)+n^2)*exp (-((η/2)^2*(n:ℝ))/8) := by
    calc
      _ ≤ 4*((n:ℝ)+n^2)*51*exp (-(η^2*(n:ℝ))/8) := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        nlinarith only [sq_nonneg (n:ℝ)]
      _ ≤ 4*((n:ℝ)+n^2)*exp (3*(η^2*(n:ℝ))/32)*exp (-(η^2*(n:ℝ))/8) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hExp (by positivity)) (exp_pos _).le
      _ = _ := by rw [mul_assoc,he]
  have hCut : exp (-(η^2*(n:ℝ)^2)/8) ≤ exp (-((η/2)^2*(n:ℝ)^2)/8) := by
    apply exp_le_exp.mpr
    nlinarith only [mul_nonneg (sq_nonneg η) (sq_nonneg (n:ℝ))]
  exact (add_le_add hSmall (mul_le_mul_of_nonneg_left hCut (by positivity))).trans_lt
    (hN n ((le_max_left _ _).trans hn))

/-- One arc sample controls the usual rectangles and codegrees and
also tracks every vertex degree into any of the prescribed style cells.
The additional whole-cluster row is represented by `none`. -/
theorem exists_arc_sample_tracking_codegrees_and_styles (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] (D : Digraph W) (p : ℝ)
      (A B : Option (Fin 50) → Finset W),
      0 ≤ p → p ≤ 1 → N ≤ Fintype.card W →
      ∃ H : Digraph W, H ≤ D ∧
        (∀ x i, |(inNeighbours H (A i) x:ℝ)-p*(inNeighbours D (A i) x:ℝ)| <
          η*(Fintype.card W:ℝ)) ∧
        (∀ x i, |(outTo H (B i) x:ℝ)-p*(outTo D (B i) x:ℝ)| <
          η*(Fintype.card W:ℝ)) ∧
        (∀ X Y : Finset W, |(incidences H X Y:ℝ)-p*(incidences D X Y:ℝ)| <
          η*(Fintype.card W:ℝ)^2) ∧
        (∀ x y, x ≠ y → |(commonInNeighbours H x y:ℝ) -
          p^2*(commonInNeighbours D x y:ℝ)| < η*(Fintype.card W:ℝ)) ∧
        (∀ x y, x ≠ y → |(commonInNeighbours (reverseArcs H) x y:ℝ) -
          p^2*(commonInNeighbours (reverseArcs D) x y:ℝ)| < η*(Fintype.card W:ℝ)) := by
  classical
  obtain ⟨N,hN⟩ := eventual_style_sampling_budget η hη
  refine ⟨N,?_⟩
  intro W _ D p A B hp hp1 hn
  let : DecidableEq (W × W) := Classical.decEq _
  let n : ℝ := Fintype.card W
  let Small := (W × Bool × Option (Fin 50)) ⊕ (Bool × (W × W))
  let Large := Finset W × Finset W
  let Rows := Small ⊕ Large
  let row (v : W × Bool × Option (Fin 50)) :=
    if v.2.1 then weight D {v.1} (B v.2.2) else weight D (A v.2.2) {v.1}
  let codeg (r : Bool × (W × W)) (s : W × W → Bool) :=
    let A := if r.1 then reverseArcs D else D
    let B := if r.1 then reverseArcs (selected D s) else selected D s
    if r.2.1 = r.2.2 then 0 else (commonInNeighbours B r.2.1 r.2.2:ℝ) -
      p^2*(commonInNeighbours A r.2.1 r.2.2:ℝ)
  let score : Rows → (W × W → Bool) → ℝ := Sum.elim
    (Sum.elim (fun v => BiasedDegreeCutSelection.value p (row v)) codeg)
    (fun ST => BiasedDegreeCutSelection.value p (weight D ST.1 ST.2))
  let var : Rows → ℝ := Sum.elim (fun _ => n) (fun _ => 2*n^2)
  let b : Rows → ℝ := Sum.elim (fun _ => η*n) (fun _ => η*n^2)
  have hMoment (r : Rows) (t : ℝ) :
      (∑ s,assignmentMass p s*exp (t*score r s)) ≤ exp (t^2*var r/2) := by
    rcases r with (v | ⟨a,y,z⟩) | ⟨S,T⟩
    · have hv : (∑ e, row v e^2) ≤ n := by
        rcases v with ⟨v,a,j⟩
        cases a
        · simp only [row,Bool.false_eq_true,if_false,sum_squared_weight]
          have hv : incidences D (A j) {v} ≤ Fintype.card W :=
            (incidences_le D (A j) {v}).trans
              (by simpa only [card_singleton,mul_one] using card_le_univ (A j))
          change (incidences D (A j) {v}:ℝ) ≤ (Fintype.card W:ℝ)
          exact_mod_cast hv
        · simp only [row,if_true,sum_squared_weight]
          have hv : incidences D {v} (B j) ≤ Fintype.card W :=
            (incidences_le D {v} (B j)).trans
              (by simpa only [card_singleton,one_mul] using card_le_univ (B j))
          change (incidences D {v} (B j):ℝ) ≤ (Fintype.card W:ℝ)
          exact_mod_cast hv
      apply (weighted_linear_exp p hp hp1 (row v) t).trans
      apply exp_le_exp.mpr
      change t^2*(∑ e, row v e^2)/2 ≤ t^2*n/2
      linarith only [mul_le_mul_of_nonneg_left hv (sq_nonneg t)]
    · cases a
      · have h := weighted_codegree_exp D p hp hp1 y z t
        convert h using 1 <;> congr 1 <;> ext x <;> simp only [mem_univ]
      · have h := weighted_out_codegree_exp D p hp hp1 y z t
        convert h using 1 <;> congr 1 <;> ext x <;> simp only [mem_univ]
    · apply (weighted_linear_exp p hp hp1 (weight D S T) t).trans
      apply exp_le_exp.mpr
      change t^2*(∑ e, weight D S T e^2)/2 ≤ t^2*(2*n^2)/2
      linarith only [mul_le_mul_of_nonneg_left (cut_variance_bound D S T) (sq_nonneg t)]
  have hBudget : (∑ r : Rows, 2*exp ((η/4)^2*var r/2-(η/4)*b r)) < 1 := by
    rw [Fintype.sum_sum_type]
    have hSmall (r : Small) : 2*exp ((η/4)^2*var (.inl r)/2-(η/4)*b (.inl r)) ≤
        2*exp (-(η^2*n)/8) := by
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
      change (η/4)^2*n/2-(η/4)*(η*n) ≤ _
      have he : (0:ℝ) ≤ η^2*n := by positivity
      nlinarith only [he]
    have hLarge (r : Large) : 2*exp ((η/4)^2*var (.inr r)/2-(η/4)*b (.inr r)) ≤
        2*exp (-(η^2*n^2)/8) := by
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
      change (η/4)^2*(2*n^2)/2-(η/4)*(η*n^2) ≤ _
      have he : (0:ℝ) ≤ η^2*n^2 := by positivity
      nlinarith only [he]
    have hSm := sum_le_sum (s := univ) (fun r _ => hSmall r)
    have hLg := sum_le_sum (s := univ) (fun r _ => hLarge r)
    have hCutCard : Fintype.card Large = 4^Fintype.card W := by
      simp only [Large,Fintype.card_prod,Fintype.card_finset]
      rw [←mul_pow]
      norm_num
    have hSmCard : (Fintype.card Small:ℝ) = 2*(51*n+n^2) := by
      simp only [Small,n,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,
        Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat]
      ring
    simp only [sum_const,card_univ,nsmul_eq_mul,hSmCard] at hSm
    simp only [sum_const,card_univ,nsmul_eq_mul,hCutCard,Nat.cast_pow,Nat.cast_ofNat] at hLg
    have hFinal := hN (Fintype.card W) hn
    change 4*(51*n+n^2)*exp (-(η^2*n)/8)+2*(4:ℝ)^Fintype.card W*exp (-(η^2*n^2)/8) < 1 at hFinal
    linarith only [hSm,hLg,hFinal]
  obtain ⟨s,hs⟩ := exists_sample_of_moment_budget p hp hp1 score var (fun _ => η/4) b
    (fun _ => by positivity) hMoment hBudget
  refine ⟨selected D s,selected_le D s,?_,?_,?_,?_,?_⟩
  · intro x j
    have h := hs (.inl (.inl (x,false,j)))
    change |BiasedDegreeCutSelection.value p (weight D (A j) {x}) s| < η*n at h
    simpa only [biased_cut_identity,incidences,sum_singleton] using h
  · intro x j
    have h := hs (.inl (.inl (x,true,j)))
    change |BiasedDegreeCutSelection.value p (weight D {x} (B j)) s| < η*n at h
    simpa only [biased_cut_identity,incidences_eq_sum_outTo,sum_singleton] using h
  · intro X Y
    have h := hs (.inr (X,Y))
    change |BiasedDegreeCutSelection.value p (weight D X Y) s| < _ at h
    rwa [biased_cut_identity] at h
  · intro x y hxy
    simpa [score,codeg,b,n,hxy] using hs (.inl (.inr (false,x,y)))
  · intro x y hxy
    simpa [score,codeg,b,n,hxy] using hs (.inl (.inr (true,x,y)))

/-- The common sample has absolute error at most ηn in each semidegree
and codegree and at most ηn² in every ordered rectangle. -/
theorem exists_arc_sample_tracking_codegrees (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] (D : Digraph W) (p : ℝ),
      0 ≤ p → p ≤ 1 → N ≤ Fintype.card W →
      ∃ H : Digraph W, H ≤ D ∧
        (∀ x, |(inDegree H x:ℝ)-p*(inDegree D x:ℝ)| < η*(Fintype.card W:ℝ)) ∧
        (∀ x, |(outDegree H x:ℝ)-p*(outDegree D x:ℝ)| < η*(Fintype.card W:ℝ)) ∧
        (∀ X Y : Finset W, |(incidences H X Y:ℝ)-p*(incidences D X Y:ℝ)| <
          η*(Fintype.card W:ℝ)^2) ∧
        (∀ x y, x ≠ y → |(commonInNeighbours H x y:ℝ) -
          p^2*(commonInNeighbours D x y:ℝ)| < η*(Fintype.card W:ℝ)) ∧
        (∀ x y, x ≠ y → |(commonInNeighbours (reverseArcs H) x y:ℝ) -
          p^2*(commonInNeighbours (reverseArcs D) x y:ℝ)| < η*(Fintype.card W:ℝ)) := by
  obtain ⟨N,hN⟩ := exists_arc_sample_tracking_codegrees_and_styles.{u} η hη
  refine ⟨N,?_⟩
  intro W _ D p hp hp1 hn
  obtain ⟨H,hSub,hIn,hOut,hRect,hCI,hCO⟩ := hN D p (fun _ => univ) (fun _ => univ) hp hp1 hn
  exact ⟨H,hSub,fun x => hIn x none,fun x => hOut x none,hRect,hCI,hCO⟩

end OverfullWork.DirectedRobustExpansion
