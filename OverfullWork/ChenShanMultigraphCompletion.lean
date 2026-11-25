module

public import OverfullWork.ChenShanAuxiliaryOrder
public import OverfullWork.MultigraphCuts
public import OverfullWork.OddCutDeficit
public import OverfullWork.ChenShanAuxiliaryCompletion

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph Finset KLOS PrunedCore RobustExpansion

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (M : MultiGraph V) (f : V → Finset W) (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The original multiplicities are retained and each new edge is simple. -/
def completionMultiplicity : V ⊕ W → V ⊕ W → ℕ
  | .inl v, .inl u => M.mult s(v, u)
  | .inl v, .inr w | .inr w, .inl v => if w ∈ f v then 1 else 0
  | .inr w, .inr z => if H.Adj w z then 1 else 0

omit [Fintype V] [Fintype W] [DecidableEq V] in
theorem completionMultiplicity_symm (x y : V ⊕ W) :
    completionMultiplicity M f H x y = completionMultiplicity M f H y x := by
  cases x with
  | inl v =>
      cases y with
      | inl u => exact congrArg M.mult (Sym2.eq_swap)
      | inr w => rfl
  | inr w =>
      cases y with
      | inl v => rfl
      | inr z => simp [completionMultiplicity, H.adj_comm]

/-- The union of the original multigraph with the bipartite attachment
and the simple auxiliary graph. -/
def auxiliaryCompletion : MultiGraph (V ⊕ W) where
  mult := Sym2.lift ⟨completionMultiplicity M f H, completionMultiplicity_symm M f H⟩
  loopless := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      obtain rfl := Sym2.mk_isDiag_iff.mp he
      change completionMultiplicity M f H u u = 0
      cases u with
      | inl v => exact M.loopless _ (Sym2.mk_isDiag_iff.mpr rfl)
      | inr w => simp [completionMultiplicity]

omit [Fintype V] [Fintype W] [DecidableEq V] in
@[simp] theorem auxiliaryCompletion_mult (x y : V ⊕ W) :
    (auxiliaryCompletion M f H).mult s(x, y) = completionMultiplicity M f H x y := rfl

theorem auxiliaryCompletion_degree_left (v : V) :
    (auxiliaryCompletion M f H).degree (.inl v) = M.degree v + (f v).card := by
  rw [MultiGraph.degree_eq_sum_mult, Fintype.sum_sum_type, MultiGraph.degree_eq_sum_mult]
  simp only [auxiliaryCompletion_mult, completionMultiplicity]
  have hSum : (∑ w : W, if w ∈ f v then (1 : ℕ) else 0) = (f v).card := by
    rw [sum_boole]
    simp
  rw [hSum]

open scoped Classical in
theorem auxiliaryCompletion_degree_right (w : W) :
    (auxiliaryCompletion M f H).degree (.inr w) =
      (auxiliaryCrossGraph f).degree (.inr w) + H.degree w := by
  rw [MultiGraph.degree_eq_sum_mult, Fintype.sum_sum_type, auxiliaryCrossGraph_degree_right,
    ← card_neighborFinset_eq_degree]
  simp only [auxiliaryCompletion_mult, completionMultiplicity]
  have hSum : (∑ z : W, if H.Adj w z then (1 : ℕ) else 0) = (H.neighborFinset w).card := by
    rw [sum_boole]
    apply congrArg Finset.card
    ext z
    simp
  rw [hSum, sum_boole]
  apply congrArg (fun a : ℕ => a + (H.neighborFinset w).card)
  apply congrArg Finset.card
  ext v
  simp

open scoped Classical in
theorem auxiliaryCompletion_regular (k : ℕ)
    (hDegree : ∀ v, M.degree v ≤ k)
    (hRows : ∀ v, (f v).card = k - M.degree v)
    (hAux : ∀ w, (auxiliaryCrossGraph f).degree (.inr w) + H.degree w = k) :
    (auxiliaryCompletion M f H).IsRegularOfDegree k := by
  intro x
  cases x with
  | inl v =>
      rw [auxiliaryCompletion_degree_left, hRows]
      exact (Nat.add_comm _ _).trans (Nat.sub_add_cancel (hDegree v))
  | inr w => exact (auxiliaryCompletion_degree_right M f H w).trans (hAux w)


omit [Fintype V] [Fintype W] in
private theorem sum_disjoint_shores (S : Finset V) (T : Finset W) (g : V ⊕ W → ℕ) :
    (∑ x ∈ S.disjSum T, g x) = (∑ v ∈ S, g (.inl v)) + ∑ w ∈ T, g (.inr w) := by
  have hDis : Disjoint (S.map Function.Embedding.inl : Finset (V ⊕ W))
      (T.map Function.Embedding.inr) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨v, _, rfl⟩ := mem_map.mp hx
    obtain ⟨w, _, h⟩ := mem_map.mp hy
    cases h
  have hUnion : S.disjSum T = S.map Function.Embedding.inl ∪ T.map Function.Embedding.inr := by
    ext (v | w) <;> simp [mem_map]
  rw [hUnion, sum_union hDis, sum_map, sum_map]
  rfl

private theorem completion_compl_shores (S : Finset V) (T : Finset W) :
    (S.disjSum T)ᶜ = Sᶜ.disjSum Tᶜ := by
  ext (v | w) <;> simp

theorem auxiliaryCompletion_cut_ge (S : Finset V) (T : Finset W) :
    OddCutDeficit.cutEdges H T ≤ (auxiliaryCompletion M f H).cutSize (S.disjSum T) := by
  rw [OddCutDeficit.cutEdges_eq_multigraph]
  simp only [MultiGraph.cutSize, completion_compl_shores, sum_disjoint_shores,
    auxiliaryCompletion_mult, completionMultiplicity, MultiGraph.ofSimpleGraph, mem_edgeSet]
  have hSum : (∑ x ∈ T, ∑ y ∈ Tᶜ, if H.Adj x y then (1 : ℕ) else 0) ≤
      ∑ x ∈ T, ((∑ y ∈ Sᶜ, if x ∈ f y then (1 : ℕ) else 0) +
        (∑ y ∈ Tᶜ, if H.Adj x y then 1 else 0)) :=
    sum_le_sum fun _ _ => Nat.le_add_left _ _
  omega

omit [Fintype V] [Fintype W] in
theorem auxiliaryCompletion_twiceInternal (S : Finset V) (T : Finset W) :
    (auxiliaryCompletion M f H).twiceInternal (S.disjSum T) =
      M.twiceInternal S + 2 * (∑ v ∈ S, ∑ w ∈ T, if w ∈ f v then (1 : ℕ) else 0) +
        (MultiGraph.ofSimpleGraph H).twiceInternal T := by
  simp only [MultiGraph.twiceInternal, sum_disjoint_shores, auxiliaryCompletion_mult,
    completionMultiplicity, MultiGraph.ofSimpleGraph, mem_edgeSet]
  rw [sum_add_distrib, sum_add_distrib]
  have hCross :
      (∑ v ∈ S, ∑ w ∈ T, if w ∈ f v then (1 : ℕ) else 0) =
        (∑ w ∈ T, ∑ v ∈ S, if w ∈ f v then (1 : ℕ) else 0) := sum_comm
  rw [← hCross]
  omega


omit [Fintype W] in
/-- The one-new-vertex case, measured in the doubled internal edge
count so that parallel edges of the original graph are included. -/
theorem auxiliaryCompletion_singleton_bound (k : ℕ) (S : Finset V) (w : W)
    (hDegree : ∀ v, M.degree v ≤ k) (hEven : Even S.card)
    (hRows : ∀ v, (f v).card = k - M.degree v)
    (hOne : ∀ z, ((univ : Finset V).filter (fun v => k - M.degree v = 1 ∧ z ∈ f v)).card ≤ 1) :
    (auxiliaryCompletion M f H).twiceInternal (S.disjSum {w}) ≤ k * S.card := by
  let d (v : V) := k - M.degree v
  let T := S.filter (fun v => w ∈ f v)
  have hPos (v : V) (hv : v ∈ T) : 0 < d v := by
    change 0 < k - M.degree v
    rw [← hRows v]
    exact card_pos.mpr ⟨w, (mem_filter.mp hv).2⟩
  have hRare : (T.filter fun v => d v = 1).card ≤ 1 := by
    apply (card_le_card (t := univ.filter (fun v => d v = 1 ∧ w ∈ f v)) ?_).trans (hOne w)
    intro v hv
    obtain ⟨ha, hb⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨mem_univ _, hb, (mem_filter.mp ha).2⟩
  have hCosts : 2 * T.card ≤ ∑ v ∈ T, (d v + if d v = 1 then 1 else 0) := by
    calc
      _ = ∑ _ ∈ T, (2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum fun v hv => by
        have h := hPos v hv
        split <;> omega
  rw [sum_add_distrib, sum_boole] at hCosts
  simp only [Nat.cast_id] at hCosts
  have hBudget : (∑ v ∈ T, d v) ≤ ∑ v ∈ S, d v :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have hSum : (∑ v ∈ S, M.degree v) + (∑ v ∈ S, d v) = k * S.card := by
    rw [← sum_add_distrib]
    simp only [d, show ∀ v, M.degree v + (k - M.degree v) = k from
      fun v => (Nat.add_comm _ _).trans (Nat.sub_add_cancel (hDegree v))]
    simp [Nat.mul_comm]
  have hWithin := M.twiceInternal_le_degree_sum S
  have hDouble := M.twiceInternal_eq S
  obtain ⟨j, hj⟩ := hEven
  have hEvenBudget : k * S.card = 2 * (k * j) := by rw [hj]; ring
  rw [auxiliaryCompletion_twiceInternal M f H]
  have hCross : (∑ v ∈ S, ∑ z ∈ ({w} : Finset W), if z ∈ f v then (1 : ℕ) else 0) =
      T.card := by
    simp only [sum_singleton]
    rw [sum_boole]
    rfl
  have hNoLoop : (MultiGraph.ofSimpleGraph H).twiceInternal ({w} : Finset W) = 0 := by
    simp [MultiGraph.twiceInternal, MultiGraph.ofSimpleGraph, mem_edgeSet]
  rw [hCross, hNoLoop, add_zero]
  omega

/-- The odd-cut argument in Lemma 3.24, given the large-cut bound
on the auxiliary graph when both shores have at least two vertices. -/
theorem auxiliaryCompletion_noOddOverfull (k : ℕ)
    (hDegree : ∀ v, M.degree v ≤ k) (hNo : M.NoOddOverfull k)
    (hRows : ∀ v, (f v).card = k - M.degree v)
    (hOne : ∀ z, ((univ : Finset V).filter (fun v => k - M.degree v = 1 ∧ z ∈ f v)).card ≤ 1)
    (hEven : Even (Fintype.card (V ⊕ W))) (hReg : (auxiliaryCompletion M f H).IsRegularOfDegree k)
    (hCut : ∀ T : Finset W, 2 ≤ T.card → 2 * T.card ≤ Fintype.card W → k < OddCutDeficit.cutEdges H T) :
    ¬ (auxiliaryCompletion M f H).HasOverfullSubset k := by
  let P := auxiliaryCompletion M f H
  have hSmall (S : Finset V) (T : Finset W) (hOdd : Odd (S.disjSum T).card) (hT : T.card ≤ 1) :
      k ≤ P.cutSize (S.disjSum T) := by
    apply Nat.le_of_not_gt
    intro hBad
    have hin := (P.odd_overfull_iff_small_cut hReg _ hOdd).mpr hBad
    rw [card_disjSum] at hin hOdd
    by_cases h0 : T.card = 0
    · have he := card_eq_zero.mp h0
      have ho : Odd S.card := by simpa only [h0, add_zero] using hOdd
      have hb := hNo S ho
      change k * (S.card + T.card - 1) < (auxiliaryCompletion M f H).twiceInternal (S.disjSum T) at hin
      rw [auxiliaryCompletion_twiceInternal, he] at hin
      exact (not_lt_of_ge hb) (by simpa [MultiGraph.twiceInternal] using hin)
    · have h1 : T.card = 1 := by omega
      obtain ⟨w, rfl⟩ := card_eq_one.mp h1
      have hEvenS : Even S.card := by
        rw [Nat.odd_iff, h1] at hOdd
        exact ⟨S.card / 2, by omega⟩
      have hb := auxiliaryCompletion_singleton_bound M f H k S w hDegree hEvenS hRows hOne
      rw [h1, Nat.add_sub_cancel] at hin
      exact (not_lt_of_ge hb) hin
  apply (P.noOverfull_iff_odd_cut_bound hReg).mpr
  intro Q hOdd
  let S := Q.toLeft
  let T := Q.toRight
  have hQ : S.disjSum T = Q := toLeft_disjSum_toRight
  by_cases ht : T.card ≤ 1
  · rw [← hQ] at hOdd ⊢
    exact hSmall S T hOdd ht
  by_cases htc : Tᶜ.card ≤ 1
  · have ho := MultiGraph.odd_card_compl hEven hOdd
    rw [← hQ, completion_compl_shores] at ho
    have hh := hSmall Sᶜ Tᶜ ho htc
    rwa [← completion_compl_shores, hQ, MultiGraph.cutSize_compl] at hh
  by_cases hHalf : 2 * T.card ≤ Fintype.card W
  · rw [← hQ]
    exact (hCut T (by omega) hHalf).le.trans (auxiliaryCompletion_cut_ge M f H S T)
  · have hHalfC : 2 * Tᶜ.card ≤ Fintype.card W := by
      have hCard := card_compl T
      have hLe : T.card ≤ Fintype.card W := card_le_univ _
      omega
    have hh := (hCut Tᶜ (by omega) hHalfC).le.trans (auxiliaryCompletion_cut_ge M f H Sᶜ Tᶜ)
    change k ≤ P.cutSize (Sᶜ.disjSum Tᶜ) at hh
    rwa [← completion_compl_shores, hQ, MultiGraph.cutSize_compl] at hh


open scoped Classical in
/-- Chen–Shan, Lemma 3.24. A multigraph with small total deficit and no
overfull subset embeds as the original side of an even regular multigraph
with a simple robust auxiliary side. -/
theorem exists_regular_auxiliary_completion
    (α τ : ℝ) (hα : 0 < α) (hαOne : α < 1) (hτ : 0 < τ) (hRange : τ < α / 24) :
    ∃ ν ε : ℝ, 0 < ν ∧ 0 < ε ∧ ∃ N : ℕ,
      ∀ {U : Type*} [Fintype U] [DecidableEq U] (L : MultiGraph U) (k : ℕ),
      let n := Fintype.card U
      N ≤ n → α * (n : ℝ) ≤ (k : ℝ) → k ≤ 2 * n →
      (∀ u, L.degree u ≤ k) → ¬ L.HasOverfullSubset k →
      let s := ∑ u, (k - L.degree u)
      (s : ℝ) ≤ ε * (n : ℝ) ^ 2 →
      let m := auxiliaryOrder n k
      let b := ⌈(s : ℝ) / (m : ℝ)⌉₊
      ∃ P : MultiGraph (U ⊕ Fin m), ∃ G : SimpleGraph (Fin m), ∃ _ : DecidableRel G.Adj,
        P.IsRegularOfDegree k ∧ Even (Fintype.card (U ⊕ Fin m)) ∧
        (∀ u v : U, P.mult s(.inl u, .inl v) = L.mult s(u, v)) ∧
        (∀ u : U, ∀ w : Fin m, P.mult s(.inl u, .inr w) ≤ 1) ∧
        (∀ w z : Fin m, P.mult s(.inr w, .inr z) = if G.Adj w z then 1 else 0) ∧
        ¬ P.HasOverfullSubset k ∧ (∀ w, k - b ≤ G.degree w) ∧ ExpandsInside G ν τ univ := by
  obtain ⟨ν, hν, N, hN⟩ := exists_robust_auxiliary_attachment α τ hα hτ
  let R := max (max N ⌈16 / α⌉₊) (max 2 (⌈2 / ν^2⌉₊ + 1))
  refine ⟨ν, α / 16, hν, by positivity, R, ?_⟩
  intro U _ _ L k n hn hkLo hkHi hDegree hNo s hs m b
  let d (u : U) := k - L.degree u
  have hSumD : (∑ u, L.degree u) + s = n * k := by
    change (∑ u, L.degree u) + (∑ u, d u) = n * k
    rw [← sum_add_distrib]
    simp only [d, show ∀ u, L.degree u + (k - L.degree u) = k from
      fun u => (Nat.add_comm _ _).trans (Nat.sub_add_cancel (hDegree u))]
    simp [n]
  have hParity : s % 2 = (n * k) % 2 := by
    have hEven := L.sum_degrees_eq_twice_edgeCount
    omega
  have hLeft : max N ⌈16 / α⌉₊ ≤ n := (le_max_left _ _).trans hn
  have hRight : max 2 (⌈2 / ν^2⌉₊ + 1) ≤ n := (le_max_right _ _).trans hn
  have hNn : N ≤ n := (le_max_left _ _).trans hLeft
  obtain ⟨f, G, hG, hRows, hOne, hAux, hMin, hExpand⟩ :=
    hN k d hNn hkLo hkHi (fun _ => Nat.sub_le _ _) hs hParity
  let P := auxiliaryCompletion L f G
  have hReg : P.IsRegularOfDegree k := auxiliaryCompletion_regular L f G k hDegree hRows hAux
  obtain ⟨hmn, _, hmParity, _, _⟩ := auxiliaryOrder_spec n k
  change n ≤ m at hmn
  change m % 2 = n % 2 at hmParity
  have hEven : Even (Fintype.card (U ⊕ Fin m)) := by
    rw [Fintype.card_sum, Fintype.card_fin]
    change Even (n + m)
    exact ⟨(n + m) / 2, by omega⟩
  have hnTwo : 2 ≤ n := (le_max_left _ _).trans hRight
  have hnLarge : 16 ≤ α * (n : ℝ) := by
    have hCeil : ⌈16 / α⌉₊ ≤ n := (le_max_right _ _).trans hLeft
    have h := (div_le_iff₀ hα).mp ((Nat.le_ceil (16 / α)).trans
      (show (↑⌈16 / α⌉₊ : ℝ) ≤ (n : ℝ) by exact_mod_cast hCeil))
    simpa only [mul_comm] using h
  obtain ⟨hmThree, _, hbK, _⟩ :=
    auxiliaryOrder_deficit_budget n k s α hα hnTwo hnLarge hkLo hkHi hs
  have hB : b ≤ k := by
    have h : (b : ℝ) ≤ (k : ℝ) := by
      have hk : 0 ≤ (k : ℝ) := by positivity
      linarith only [hbK, hk]
    exact_mod_cast h
  have hk : 0 < k := by
    by_contra! h
    have hz : k = 0 := by omega
    simp only [hz, Nat.cast_zero] at hkLo
    linarith only [hkLo, hnLarge]
  have hτhalf : τ ≤ 1 / 2 := by linarith only [hRange, hαOne]
  have hNonempty : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have hMinR : 7 * (k : ℝ) / 8 ≤ (G.minDegree : ℝ) := by
    have h := G.le_minDegree_of_forall_le_degree (k - b) hMin
    have hh : ((k - b : ℕ) : ℝ) ≤ (G.minDegree : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub hB] at hh
    linarith only [hbK, hh]
  have hScale : τ * (m : ℝ) ≤ (k : ℝ) / 8 := by
    have hSize : (m : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast hmThree
    have h1 := mul_le_mul_of_nonneg_left hSize hτ.le
    have h2 := mul_le_mul_of_nonneg_right hRange.le (Nat.cast_nonneg n)
    nlinarith only [h1, h2, hkLo]
  have hOrder : (k : ℝ) < (ν * (m : ℝ)) ^ 2 := by
    have hCeil : ⌈2 / ν^2⌉₊ + 1 ≤ n := (le_max_right _ _).trans hRight
    have hCeilR : (↑⌈2 / ν^2⌉₊ : ℝ) < (n : ℝ) := by
      exact_mod_cast (show ⌈2 / ν^2⌉₊ < n by omega)
    have hTime : 2 / ν^2 < (n : ℝ) := (Nat.le_ceil _).trans_lt hCeilR
    have hCoeff := (div_lt_iff₀ (sq_pos_of_pos hν)).mp hTime
    have hnPos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmn
    have hh := mul_lt_mul_of_pos_right hCoeff hnPos
    have hSq : (ν * (n : ℝ)) ^ 2 ≤ (ν * (m : ℝ)) ^ 2 := by
      gcongr
    have hK : (k : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hkHi
    nlinarith only [hh, hK, hSq]
  have hOld := (L.noOverfull_iff_odd_bounds k hDegree).mp hNo
  have hOdd : ¬ P.HasOverfullSubset k := auxiliaryCompletion_noOddOverfull L f G k
    hDegree hOld hRows hOne hEven hReg (fun T hTwo hHalf =>
      auxiliary_core_cut_large G k hk hν hτhalf hMinR
        (by simpa only [Fintype.card_fin] using hScale)
        (by simpa only [Fintype.card_fin] using hOrder) hExpand T hTwo hHalf)
  refine ⟨P, G, hG, hReg, hEven, fun _ _ => rfl, ?_, fun _ _ => ?_, hOdd, hMin, hExpand⟩
  · intro v w
    change (if w ∈ f v then 1 else 0) ≤ 1
    split <;> omega
  · rfl


/-- With degree strictly below the original order, the least auxiliary
order is the original order itself. -/
theorem auxiliaryOrder_eq_order {n k : ℕ} (h : k < n) : auxiliaryOrder n k = n := by
  unfold auxiliaryOrder
  rw [max_eq_left (by omega)]
  simp

open scoped Classical in
/-- The simple-graph case of Lemma 3.24, in the form used in the proofs
of Theorems 2.1 and 2.2. -/
theorem exists_simple_auxiliary_completion
    (α τ : ℝ) (hα : 0 < α) (hαOne : α < 1) (hτ : 0 < τ) (hRange : τ < α / 24) :
    ∃ ν ε : ℝ, 0 < ν ∧ 0 < ε ∧ ∃ N : ℕ,
      ∀ {U : Type*} [Fintype U] [DecidableEq U] (L : SimpleGraph U) [DecidableRel L.Adj] (k : ℕ),
      let n := Fintype.card U
      N ≤ n → α * (n : ℝ) ≤ (k : ℝ) → k < n →
      (∀ u, L.degree u ≤ k) → ¬ (MultiGraph.ofSimpleGraph L).HasOverfullSubset k →
      let s := ∑ u, (k - L.degree u)
      (s : ℝ) ≤ ε * (n : ℝ) ^ 2 →
      let b := ⌈(s : ℝ) / (n : ℝ)⌉₊
      ∃ R : SimpleGraph (U ⊕ Fin n), ∃ G : SimpleGraph (Fin n), ∃ _ : DecidableRel G.Adj,
        (∀ x, R.degree x = k) ∧
        (∀ u v : U, R.Adj (.inl u) (.inl v) ↔ L.Adj u v) ∧
        (∀ w z : Fin n, R.Adj (.inr w) (.inr z) ↔ G.Adj w z) ∧
        ¬ (MultiGraph.ofSimpleGraph R).HasOverfullSubset k ∧
        (∀ w, k - b ≤ G.degree w) ∧ ExpandsInside G ν τ univ := by
  obtain ⟨ν, ε, hν, hε, N, hN⟩ := exists_regular_auxiliary_completion α τ hα hαOne hτ hRange
  refine ⟨ν, ε, hν, hε, N, ?_⟩
  intro U _ _ L _ k n hn hkLo hkLt hDegree hNo s hs b
  have hInput := hN (MultiGraph.ofSimpleGraph L) k hn hkLo (by omega)
    (fun u => by rw [MultiGraph.degree_ofSimpleGraph]; exact hDegree u) hNo
    (by simpa only [MultiGraph.degree_ofSimpleGraph] using hs)
  dsimp only at hInput
  simp only [MultiGraph.degree_ofSimpleGraph] at hInput
  have he : auxiliaryOrder (Fintype.card U) k = Fintype.card U := auxiliaryOrder_eq_order hkLt
  rw [he] at hInput
  obtain ⟨P, G, hG, hReg, _, hLeft, hCross, hRight, hP, hMin, hExp⟩ := hInput
  have hMult (e : Sym2 (U ⊕ Fin n)) : P.mult e ≤ 1 := by
    induction e using Sym2.inductionOn with
    | hf x y =>
      cases x with
      | inl u =>
        cases y with
        | inl v =>
          rw [hLeft]
          change (if s(u, v) ∈ L.edgeSet then 1 else 0) ≤ 1
          split <;> omega
        | inr w => exact hCross u w
      | inr w =>
        cases y with
        | inl v => rw [Sym2.eq_swap]; exact hCross v w
        | inr z => rw [hRight]; split <;> omega
  let R := P.supportGraph
  have hR : MultiGraph.ofSimpleGraph R = P := MultiGraph.of_supportGraph P hMult
  refine ⟨R, G, hG, ?_, ?_, ?_, hR.symm ▸ hP, hMin, hExp⟩
  · intro x
    rw [← MultiGraph.degree_ofSimpleGraph, hR]
    exact hReg x
  · intro u v
    change 0 < P.mult s(.inl u, .inl v) ↔ L.Adj u v
    rw [hLeft]
    change (0 < if s(u, v) ∈ L.edgeSet then 1 else 0) ↔ L.Adj u v
    simp only [mem_edgeSet]
    by_cases ha : L.Adj u v
    · rw [ite_eq_left ha]
      exact iff_of_true (by decide) ha
    · rw [ite_eq_right ha]
      exact iff_of_false (by decide) ha
  · intro w z
    change 0 < P.mult s(.inr w, .inr z) ↔ G.Adj w z
    rw [hRight]
    by_cases ha : G.Adj w z
    · rw [ite_eq_left ha]
      exact iff_of_true (by decide) ha
    · rw [ite_eq_right ha]
      exact iff_of_false (by decide) ha

end OverfullWork.ChenShan
