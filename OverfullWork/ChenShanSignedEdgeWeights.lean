module

public import OverfullWork.ChenShanSignedCutBudgets
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical BigOperators

universe uA uB

variable {A : Type uA} {B : Type uB} [Fintype A] [Fintype B]

private theorem sum_replace_one {I : Type*} [Fintype I] (f g : I → ℝ) (i : I)
    (h : ∀ j, j ≠ i → g j = f j) :
    (∑ j, g j) = (∑ j, f j) + (g i - f i) := by
  have hErase : ∑ j ∈ (univ.erase i), g j = ∑ j ∈ (univ.erase i), f j :=
    sum_congr rfl (fun j hj => h j (ne_of_mem_erase hj))
  have h₁ := sum_erase_add (univ : Finset I) g (mem_univ i)
  have h₂ := sum_erase_add (univ : Finset I) f (mem_univ i)
  linarith

private theorem sum_insert_indicator {I : Type*} [Fintype I] (S : Finset I) (f : I → ℝ) :
    (∑ i ∈ S, f i) = ∑ i, if i ∈ S then f i else 0 := by
  have h : univ.filter (fun i => i ∈ S) = S := by ext; simp
  rw [← sum_filter, h]

/-- Net outflow from the cut is the sum of the signed weights with
positive sign from the left shore and negative sign from the right. -/
private theorem bipartite_net_outflow (z : A → B → ℝ) (S : Finset A) (T : Finset B) :
    (∑ a ∈ S, ∑ b, z a b) - (∑ b ∈ T, ∑ a, z a b) =
      ∑ a, ∑ b, ((if a ∈ S then z a b else 0) - (if b ∈ T then z a b else 0)) := by
  have hL : (∑ a ∈ S, ∑ b, z a b) = ∑ a, ∑ b, if a ∈ S then z a b else 0 := by
    rw [sum_insert_indicator]
    apply sum_congr rfl
    intro a _
    by_cases h : a ∈ S <;> simp [h]
  have hR : (∑ b ∈ T, ∑ a, z a b) = ∑ a, ∑ b, if b ∈ T then z a b else 0 := by
    rw [sum_insert_indicator, sum_comm (s := (univ : Finset A))]
    apply sum_congr rfl
    intro b _
    by_cases h : b ∈ T <;> simp [h]
  rw [hL,hR,← sum_sub_distrib]
  exact sum_congr rfl (fun _ _ => (sum_sub_distrib _ _).symm)

/-- A symmetric-capacity bipartite demand problem is feasible under
the cut inequalities. At a least-squares minimizer, every edge
out of the vertices of positive residual demand is saturated. -/
theorem exists_signed_bipartite_weights_of_cut_capacity
    (E : A → B → Prop) (r : A → ℝ) (s : B → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hBalance : (∑ a, r a) = ∑ b, s b)
    (hCut : ∀ S : Finset A, ∀ T : Finset B,
      (∑ a ∈ S, r a) - (∑ b ∈ T, s b) ≤ c * (bipartiteCutEdges E S T).card) :
    ∃ z : A → B → ℝ,
      (∀ a, (∑ b, z a b) = r a) ∧ (∀ b, (∑ a, z a b) = s b) ∧
      (∀ a b, |z a b| ≤ c) ∧ (∀ a b, ¬ E a b → z a b = 0) := by
  let cap (a : A) (b : B) := if E a b then c else 0
  let Box : Set (A → B → ℝ) := {z | ∀ a b, z a b ∈ Set.Icc (-cap a b) (cap a b)}
  let eA (z : A → B → ℝ) (a : A) := r a - ∑ b, z a b
  let eB (z : A → B → ℝ) (b : B) := (∑ a, z a b) - s b
  let cost (z : A → B → ℝ) := (∑ a, (eA z a)^2) + (∑ b, (eB z b)^2)
  have hCap (a : A) (b : B) : 0 ≤ cap a b := by
    by_cases h : E a b <;> simp [cap,h,hc]
  have hCompact : IsCompact Box :=
    isCompact_pi_infinite (fun a : A => isCompact_pi_infinite (fun b : B =>
      isCompact_Icc (a := -cap a b) (b := cap a b)))
  have hBox : Box.Nonempty := ⟨fun _ _ => 0,fun a b => ⟨neg_nonpos.mpr (hCap a b),hCap a b⟩⟩
  have hEval (a : A) (b : B) : Continuous (fun z : A → B → ℝ => z a b) :=
    (continuous_apply b).comp (continuous_apply a)
  have hEA (a : A) : Continuous (fun z => eA z a) :=
    continuous_const.sub (continuous_finsetSum _ (fun b _ => hEval a b))
  have hEB (b : B) : Continuous (fun z => eB z b) :=
    (continuous_finsetSum _ (fun a _ => hEval a b)).sub continuous_const
  have hCost : Continuous cost :=
    (continuous_finsetSum _ (fun a _ => (hEA a).pow 2)).add
      (continuous_finsetSum _ (fun b _ => (hEB b).pow 2))
  obtain ⟨z,hz,hMin⟩ := hCompact.exists_isMinOn hBox hCost.continuousOn
  have hZero (a : A) (b : B) (h : ¬ E a b) : z a b = 0 := by
    have hBounds := hz a b
    simp only [cap,h,ite_false,neg_zero,Set.mem_Icc] at hBounds
    exact le_antisymm hBounds.2 hBounds.1
  have perturb (a : A) (b : B) (δ : ℝ)
      (hδ : -cap a b ≤ z a b + δ ∧ z a b + δ ≤ cap a b) :
      0 ≤ 2*δ*(δ-(eA z a-eB z b)) := by
    let z' (x : A) (y : B) := z x y + if x = a ∧ y = b then δ else 0
    have hz' : z' ∈ Box := by
      intro x y
      by_cases h : x = a ∧ y = b
      · obtain ⟨rfl,rfl⟩ := h
        simpa [z',Set.mem_Icc] using hδ
      · simpa [z',h] using hz x y
    have hRow (x : A) : eA z' x = eA z x - (if x = a then δ else 0) := by
      have hSum : (∑ y, z' x y) = (∑ y, z x y) + (if x = a then δ else 0) := by
        simp only [z',sum_add_distrib]
        congr 1
        by_cases hx : x = a <;> simp [hx]
      simp only [eA,hSum]
      ring
    have hCol (y : B) : eB z' y = eB z y + (if y = b then δ else 0) := by
      have hSum : (∑ x, z' x y) = (∑ x, z x y) + (if y = b then δ else 0) := by
        simp only [z',sum_add_distrib]
        congr 1
        by_cases hy : y = b <;> simp [hy]
      simp only [eB,hSum]
      ring
    have h₁ := sum_replace_one (fun x => (eA z x)^2) (fun x => (eA z' x)^2) a
      (fun x hx => by simp [hRow,hx])
    have h₂ := sum_replace_one (fun y => (eB z y)^2) (fun y => (eB z' y)^2) b
      (fun y hy => by simp [hCol,hy])
    have hDiff : cost z' = cost z + 2*δ*(δ-(eA z a-eB z b)) := by
      dsimp only [cost]
      rw [h₁,h₂,hRow a,hCol b]
      simp only [ite_true]
      ring
    have h := hMin hz'
    change cost z ≤ cost z' at h
    linarith
  have hPos (a : A) (b : B) (h : eB z b < eA z a) : z a b = cap a b := by
    refine le_antisymm (hz a b).2 (le_of_not_gt ?_)
    intro hRoom
    let δ := min (cap a b - z a b) ((eA z a-eB z b)/2)
    have hp : 0 < δ := lt_min (by linarith) (by linarith)
    have hd₁ : δ ≤ cap a b - z a b := min_le_left _ _
    have hd₂ : δ ≤ (eA z a-eB z b)/2 := min_le_right _ _
    have hlo := (hz a b).1
    have h := perturb a b δ ⟨by linarith,by linarith⟩
    have hn : δ-(eA z a-eB z b) < 0 := by linarith
    exact (not_lt_of_ge h) (mul_neg_of_pos_of_neg (by positivity) hn)
  have hNeg (a : A) (b : B) (h : eA z a < eB z b) : z a b = -cap a b := by
    refine le_antisymm (le_of_not_gt ?_) (hz a b).1
    intro hRoom
    let δ := min (z a b + cap a b) ((eB z b-eA z a)/2)
    have hp : 0 < δ := lt_min (by linarith) (by linarith)
    have hd₁ : δ ≤ z a b + cap a b := min_le_left _ _
    have hd₂ : δ ≤ (eB z b-eA z a)/2 := min_le_right _ _
    have hhi := (hz a b).2
    have h := perturb a b (-δ) ⟨by linarith,by linarith⟩
    have hn : -δ-(eA z a-eB z b) > 0 := by linarith
    exact (not_lt_of_ge h) (mul_neg_of_neg_of_pos (by linarith) hn)
  let S := univ.filter (fun a => 0 < eA z a)
  let T := univ.filter (fun b => 0 < eB z b)
  have hS (a : A) : a ∈ S ↔ 0 < eA z a := by simp [S]
  have hT (b : B) : b ∈ T ↔ 0 < eB z b := by simp [T]
  have hNet : (∑ a ∈ S, ∑ b, z a b) - (∑ b ∈ T, ∑ a, z a b) =
      c * (bipartiteCutEdges E S T).card := by
    rw [bipartite_net_outflow]
    have hCard : c * ((bipartiteCutEdges E S T).card : ℝ) = ∑ _ ∈ bipartiteCutEdges E S T, c := by
      rw [sum_const,nsmul_eq_mul,mul_comm]
    rw [hCard]
    simp only [bipartiteCutEdges,sum_filter,Fintype.sum_prod_type]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ T <;> by_cases hE : E a b
    all_goals try simp [ha,hb,hE,hZero a b]
    · have hlt : eB z b < eA z a :=
        (le_of_not_gt (fun h => hb ((hT b).mpr h))).trans_lt ((hS a).mp ha)
      simp [hPos a b hlt,cap,hE]
    · have hlt : eA z a < eB z b :=
        (le_of_not_gt (fun h => ha ((hS a).mpr h))).trans_lt ((hT b).mp hb)
      simp [hNeg a b hlt,cap,hE]
  have hResidual : (∑ a ∈ S, eA z a) + (∑ b ∈ T, eB z b) ≤ 0 := by
    simp only [eA,eB,sum_sub_distrib]
    linarith [hCut S T]
  have hSA : 0 ≤ ∑ a ∈ S, eA z a := sum_nonneg (fun a ha => ((hS a).mp ha).le)
  have hTB : 0 ≤ ∑ b ∈ T, eB z b := sum_nonneg (fun b hb => ((hT b).mp hb).le)
  have hNA (a : A) : eA z a ≤ 0 := by
    by_contra! h
    have hle := single_le_sum (s := S) (f := eA z) (fun x hx => ((hS x).mp hx).le) ((hS a).mpr h)
    linarith
  have hNB (b : B) : eB z b ≤ 0 := by
    by_contra! h
    have hle := single_le_sum (s := T) (f := eB z) (fun x hx => ((hT x).mp hx).le) ((hT b).mpr h)
    linarith
  have hBal : (∑ a, eA z a) + (∑ b, eB z b) = 0 := by
    simp only [eA,eB,sum_sub_distrib]
    rw [hBalance,sum_comm (s := (univ : Finset B)) (t := (univ : Finset A))]
    ring
  have hNonposA : (∑ a, eA z a) ≤ 0 := sum_nonpos (fun a _ => hNA a)
  have hNonposB : (∑ b, eB z b) ≤ 0 := sum_nonpos (fun b _ => hNB b)
  have hA0 : ∀ a, eA z a = 0 :=
    fun a => (sum_eq_zero_iff_of_nonpos (fun a _ => hNA a)).mp (by linarith) a (mem_univ a)
  have hB0 : ∀ b, eB z b = 0 :=
    fun b => (sum_eq_zero_iff_of_nonpos (fun b _ => hNB b)).mp (by linarith) b (mem_univ b)
  refine ⟨z,fun a => ?_,fun b => ?_,fun a b => ?_,hZero⟩
  · have h := hA0 a
    exact (sub_eq_zero.mp h).symm
  · exact sub_eq_zero.mp (hB0 b)
  · have hcap : cap a b ≤ c := by by_cases h : E a b <;> simp [cap,h,hc]
    exact (abs_le.mpr (hz a b)).trans hcap

/-- Chen–Shan, Lemma 4.7. Signed edge weights with the prescribed row
and column sums admit the uniform bound d/gap. Nonedges have weight zero. -/
theorem exists_bounded_signed_edge_weights
    (E : A → B → Prop) (r : A → ℝ) (s : B → ℝ) (n : ℕ) (gap d : ℝ)
    (hGap : 0 < gap) (hd : 0 ≤ d) (hSizeA : Fintype.card A = n) (hSizeB : Fintype.card B = n)
    (hA : ∀ a, (n : ℝ)/2+gap ≤ ((univ.filter (E a)).card : ℝ))
    (hB : ∀ b, (n : ℝ)/2+gap ≤ ((univ.filter (fun a => E a b)).card : ℝ))
    (hBalance : (∑ a, r a) = ∑ b, s b)
    (hr : ∀ a, |r a| ≤ d) (hs : ∀ b, |s b| ≤ d) :
    ∃ z : A → B → ℝ,
      (∀ a, (∑ b, z a b) = r a) ∧ (∀ b, (∑ a, z a b) = s b) ∧
      (∀ a b, |z a b| ≤ d/gap) ∧ (∀ a b, ¬ E a b → z a b = 0) := by
  refine exists_signed_bipartite_weights_of_cut_capacity E r s (d/gap)
    (div_nonneg hd hGap.le) hBalance (fun S T => ?_)
  exact (le_abs_self _).trans
    (bipartite_demands_cut_capacity E r s n gap d hGap hd hSizeA hSizeB hA hB hBalance hr hs S T)

end OverfullWork.ChenShan
