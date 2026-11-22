module

public import OverfullWork.CMSRegularizationDeficitProfiles
public import OverfullWork.CanonicalNoOverfullCompletion

@[expose] public section


/-! The common completion argument and the dense simple-second branch
of CMS Claim 4.3. -/
namespace OverfullWork.CanonicalRegularization

open Finset SimpleGraph PrunedCore RobustExpansion OrderedCanonicalTransport
open scoped Classical

theorem integer_robust_of_real {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν τ : ℝ) (hν : 0 ≤ ν)
    (hRob : IsRealRobust G ν τ) :
    IsRobustAt G ⌈ν*(Fintype.card V:ℝ)⌉₊ ⌈τ*(Fintype.card V:ℝ)⌉₊ := by
  intro S hlo hhi
  have hLo : τ*(Fintype.card V:ℝ) ≤ (S.card:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hlo)
  have hHi : (S.card:ℝ) ≤ (1-τ)*(Fintype.card V:ℝ) := by
    have hh : (S.card:ℝ)+(⌈τ*(Fintype.card V:ℝ)⌉₊:ℝ) ≤ (Fintype.card V:ℝ) := by exact_mod_cast hhi
    nlinarith only [hh,Nat.le_ceil (τ*(Fintype.card V:ℝ))]
  have hGrow := hRob S hLo hHi
  have hEq : realNeighbourhood G ν S = neighbourhood G ⌈ν*(Fintype.card V:ℝ)⌉₊ S := by
    ext v
    simp only [realNeighbourhood,neighbourhood,mem_filter,mem_univ,true_and,Nat.ceil_le]
  rw [hEq] at hGrow
  have hCeil := Nat.ceil_le.mpr hGrow
  rw [add_comm,Nat.ceil_add_natCast (mul_nonneg hν (Nat.cast_nonneg _))] at hCeil
  simpa only [Nat.add_comm] using hCeil

private theorem real_robust_mono_support {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hLe : G ≤ H) (ν τ : ℝ) (hRob : IsRealRobust G ν τ) : IsRealRobust H ν τ := by
  intro S hlo hhi
  have hSub : realNeighbourhood G ν S ⊆ realNeighbourhood H ν S := by
    intro v hv
    have hh : neighboursIn G S v ≤ neighboursIn H S v := by
      rw [neighboursIn_eq_filter_card,neighboursIn_eq_filter_card]
      exact card_le_card (fun w hw => mem_filter.mpr ⟨(mem_filter.mp hw).1,hLe (mem_filter.mp hw).2⟩)
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2.trans (by exact_mod_cast hh)⟩
  exact (hRob S hlo hhi).trans (by exact_mod_cast card_le_card hSub)

set_option maxHeartbeats 2600000 in
theorem cms_regularization_of_local_profiles (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 ≤ η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {m : ℕ} (D : MultiGraph (Fin (m+1) × Bool)) (d : ℕ),
          let W := Fin (m+1) × Bool
          let a : W := (0,false)
          let b : W := (0,true)
          let n := Fintype.card W
          N ≤ n → d < n → α*(n:ℝ) ≤ (d:ℝ) →
          (∀ v, D.degree v ≤ d) → ¬D.HasOverfullSubset d →
          (∀ i : Fin (m+1), D.degree (i,false) ≤ D.degree (i,true)) →
          (∀ i j : Fin (m+1), i.val < j.val → D.degree (i,true) ≤ D.degree (j,false)) →
          (∀ v, v ≠ a → v ≠ b → (D.mult s(a,v):ℝ) ≤ 2*η^2*(n:ℝ)) →
          (∀ v, v ≠ a → v ≠ b →
            let k := (pairedIndex (m+1) v).val
            (((k-1:ℕ):ℝ)/(k:ℝ))*(d:ℝ)-6*η*(n:ℝ) ≤ D.supportGraph.degree v) →
          (∀ C : Completion D d,
            let M := (D.addCopies C.L).addCopies C.N
            ((d:ℝ)-(M.mult s(a,b):ℝ)-13*η*(n:ℝ) ≤ M.supportGraph.degree b) ∧
            (∀ v, v ≠ a → v ≠ b →
              (d:ℝ)-(M.mult s(a,v):ℝ)-6*η*(n:ℝ) ≤ M.supportGraph.degree v) ∧
            ∀ v, v ≠ a → v ≠ b → d ≤ M.cutSize {a,b,v}) →
          IsRealRobust D.supportGraph ν τ →
          ∃ C : Completion D d, Nonempty (((D.addCopies C.L).addCopies C.N).EdgeColoring d) := by
  obtain ⟨τ,hτ,hτCap,hPaper⟩ := cms_theorem_4_2_for_canonical_completion α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨η₀,hη₀,hUse⟩ := hPaper ν hν hντ
  let ηMax := min η₀ (α/192)
  refine ⟨ηMax,by dsimp only [ηMax]; positivity,?_⟩
  intro η hη hηMax
  have hηCap : η ≤ α/192 := hηMax.trans (min_le_right _ _)
  obtain ⟨N₀,hN₀⟩ := hUse η hη (hηMax.trans (min_le_left _ _))
  obtain ⟨N₁,hN₁⟩ := exists_nat_ge (max (1/ν^2) (64/α))
  refine ⟨max N₀ N₁,?_⟩
  intro m D d W a b n hN hDens hRel hD hNo hPair hOrder hBase hRankBase hLocal hRob
  obtain ⟨C⟩ := CanonicalNoOverfullCompletion.exists_completion_of_no_overfull D d hD hPair hOrder hNo
  let M := (D.addCopies C.L).addCopies C.N
  have hSub (e : Sym2 W) : D.mult e ≤ M.mult e := by
    change D.mult e ≤ D.mult e+C.L.mult e+C.N.mult e
    omega
  have hOrderAB : a ≠ b := by intro h; have hh := congrArg Prod.snd h; cases hh
  have hTwo : n = 2*(m+1) := by simp [n,W,Nat.mul_comm]
  let r := ⌈ν*(n:ℝ)⌉₊
  let t := ⌈τ*(n:ℝ)⌉₊
  have hLargeN : (N₁:ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hN
  have hLarge := hN₁.trans hLargeN
  have hRate : d ≤ r*r := by
    have hh := (div_le_iff₀ (show 0 < ν^2 by positivity)).mp ((le_max_left _ _).trans hLarge)
    have hr := Nat.le_ceil (ν*(n:ℝ))
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hProduct := mul_le_mul_of_nonneg_right hh hn
    have hSq := mul_le_mul hr hr (by positivity : 0 ≤ ν*(n:ℝ)) (Nat.cast_nonneg (α := ℝ) r)
    have hDensR : (d:ℝ) ≤ n := by exact_mod_cast hDens.le
    apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    nlinarith only [hDensR,hProduct,hSq]
  let rank : W → ℕ := fun x => (pairedIndex (m+1) x).val
  have hRankInj : Function.Injective rank := fun _ _ h => (pairedIndex (m+1)).injective (Fin.ext h)
  have hRank (x : W) (hxa : x ≠ a) (hxb : x ≠ b) : 2 ≤ rank x := by
    obtain ⟨i,j⟩ := x
    have hi : i ≠ 0 := by
      intro h
      subst i
      cases j
      · exact hxa rfl
      · exact hxb rfl
    have hiPos : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
    cases j <;> simp only [rank,pairedIndex_false_val,pairedIndex_true_val] <;> omega
  have hMargin : 2*(t:ℝ)+2*(6*η*(n:ℝ)) ≤ (d:ℝ)/6 := by
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hCut := Nat.ceil_lt_add_one (show 0 ≤ τ*(n:ℝ) by positivity)
    have hT := mul_le_mul_of_nonneg_right hτCap hn
    have hE := mul_le_mul_of_nonneg_right hηCap hn
    have hGrow := (div_le_iff₀ hα).mp ((le_max_right _ _).trans hLarge)
    change (t:ℝ) < τ*(n:ℝ)+1 at hCut
    nlinarith only [hCut,hT,hE,hGrow,hRel]
  have hOrdPair := support_pair_of_ranked_bounds D d t (6*η*(n:ℝ)) a b rank
    hRankInj hRank hRankBase hMargin
  obtain ⟨hB,hOrdM,hAllCuts⟩ := hLocal C
  have hRobI : IsRobustAt D.supportGraph r t := integer_robust_of_real D.supportGraph ν τ hν.le hRob
  have hNoM : ¬M.HasOverfullSubset d :=
    (no_overfull_iff_two_anchor_triples D M d (m+1) r t a b hOrderAB hTwo C.regular hSub hRobI hRate
      hOrdPair).mpr hAllCuts
  have hOrdBase (x : W) (hxa : x ≠ a) : D.degree b ≤ D.degree x := by
    apply ordered_rank_mono_of_pairs hPair hOrder
    by_cases hxb : x = b
    · rw [hxb]
    · change (pairedIndex (m+1) b).val ≤ rank x
      have hb : (pairedIndex (m+1) b).val = 1 := by simp [b,pairedIndex_true_val]
      rw [hb]
      exact (by decide : 1 ≤ 2) |>.trans (hRank x hxa hxb)
  have hRobM := real_robust_mono_support D.supportGraph M.supportGraph C.support_le ν τ hRob
  have hPaint := hN₀ C rank ((le_max_left _ _).trans hN) hDens hRel hRobM
    hOrdBase hBase hRank (fun x hxa hxb => (hRankBase x hxa hxb).trans
      (by exact_mod_cast C.support_degree_mono x)) hB hOrdM
  exact ⟨C,hPaint.mpr hNoM⟩

theorem cms_regularization_dense_simple_second (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ τ →
      ∃ ηMax : ℝ, 0 < ηMax ∧ ∀ η : ℝ, 0 ≤ η → η ≤ ηMax → ∃ N : ℕ,
        ∀ {m : ℕ} (D : MultiGraph (Fin (m+1) × Bool)) (d : ℕ),
          let W := Fin (m+1) × Bool
          let a : W := (0,false)
          let b : W := (0,true)
          let n := Fintype.card W
          N ≤ n → d < n → α*(n:ℝ) ≤ (d:ℝ) →
          (∀ v, D.degree v ≤ d) → ¬D.HasOverfullSubset d →
          (∀ i : Fin (m+1), D.degree (i,false) ≤ D.degree (i,true)) →
          (∀ i j : Fin (m+1), i.val < j.val → D.degree (i,true) ≤ D.degree (j,false)) →
          (∀ v, D.mult s(b,v) ≤ 1) →
          (∀ v, v ≠ a → v ≠ b → (D.mult s(a,v):ℝ) ≤ 2*η^2*(n:ℝ)) →
          (∀ v, v ≠ a → v ≠ b → (d:ℝ)-6*η*(n:ℝ) ≤ (D.supportGraph.degree v:ℝ)) →
          (((D.supportGraph.neighborFinset a).erase b).card ≤ 1 →
            (∃ w : W, w ≠ a ∧ w ≠ b ∧ D.degree w < d ∧
              ∀ v, v ∉ ({a,b,w}:Finset W) → D.degree v = d) ∨
            ∀ v, v ≠ a → v ≠ b → d ≤ D.cutSize {a,b,v}) →
          IsRealRobust D.supportGraph ν τ →
          ∃ C : Completion D d, Nonempty (((D.addCopies C.L).addCopies C.N).EdgeColoring d) := by
  obtain ⟨τ,hτ,hGeneral⟩ := cms_regularization_of_local_profiles α hα hα₁
  refine ⟨τ,hτ,?_⟩
  intro ν hν hντ
  obtain ⟨ηMax,hηMax,hUse⟩ := hGeneral ν hν hντ
  refine ⟨ηMax,hηMax,?_⟩
  intro η hη hηCap
  obtain ⟨N,hN⟩ := hUse η hη hηCap
  refine ⟨N,?_⟩
  intro m D d W a b n hSize hd hRel hD hNo hPair hOrder hSimple hBase hOrd hLocal hRob
  apply hN D d hSize hd hRel hD hNo hPair hOrder hBase _ _ hRob
  · intro x hxa hxb k
    have hRatio : (((k-1:ℕ):ℝ)/(k:ℝ)) ≤ 1 := by
      by_cases hp : k = 0
      · simp [hp]
      · apply (div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero hp) : (0:ℝ) < k)).mpr
        exact_mod_cast Nat.sub_le k 1
    have hh := mul_le_mul_of_nonneg_right hRatio (Nat.cast_nonneg (α := ℝ) d)
    linarith only [hh,hOrd x hxa hxb]
  · intro C M
    have hB0 : D.degree b ≤ D.supportGraph.degree b := by
      rw [←MultiGraph.degree_ofSimpleGraph,MultiGraph.degree_eq_sum_mult,MultiGraph.degree_eq_sum_mult]
      apply sum_le_sum
      intro x _
      by_cases hx : 0 < D.mult s(b,x)
      · have hAdj : D.supportGraph.Adj b x := hx
        change D.mult s(b,x) ≤ if s(b,x) ∈ D.supportGraph.edgeSet then 1 else 0
        rw [if_pos (D.supportGraph.mem_edgeSet.mpr hAdj)]
        exact hSimple x
      · omega
    have hB := C.second_anchor_profile_of_dense_base (6*η*(n:ℝ)) 0 (by positivity) hOrd
      (by simpa only [add_zero] using (show (D.degree b:ℝ) ≤ (D.supportGraph.degree b:ℝ) by exact_mod_cast hB0))
    refine ⟨?_,?_,C.simple_second_triples_safe hD hNo (hPair 0) hSimple hLocal⟩
    · linarith only [hB,mul_nonneg hη (Nat.cast_nonneg (α := ℝ) n)]
    · intro x hxa hxb
      have hh := (hOrd x hxa hxb).trans (show (D.supportGraph.degree x:ℝ) ≤ M.supportGraph.degree x by
        exact_mod_cast C.support_degree_mono x)
      linarith only [hh,Nat.cast_nonneg (α := ℝ) (M.mult s(a,x))]

end OverfullWork.CanonicalRegularization
