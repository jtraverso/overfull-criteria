module

public import OverfullWork.DirectedPrefactorReachability

@[expose] public section


/-! A normalized form of Lo–Patel Lemma 5.2 with explicit,
conservative constants and at most ceil(12/nu)+1 extensions. -/
namespace OverfullWork.DirectedPrefactor
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] {D : Digraph V} {x : V}
set_option maxHeartbeats 18000000

theorem real_most_termini_reachable (B : Prefactor D x → Finset V) (F₀ : Prefactor D x)
    (ν τ ξ : ℝ) (hν : 0 < ν) (hν₁ : ν ≤ 1) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (hSmall : ξ ≤ ν^2/8) (hOrder : 128 ≤ ν^3*(Fintype.card V:ℝ))
    (hB : ∀ F,((B F).card:ℝ) ≤ ξ*(Fintype.card V:ℝ))
    (hRobust : IsRealRobust D ν τ)
    (hOut : (τ+ξ)*(Fintype.card V:ℝ)+2 ≤ (outDegree D (terminus F₀):ℝ)) :
    (Fintype.card V:ℝ)-τ*(Fintype.card V:ℝ) ≤
      ((reachableTermini B F₀ (⌈12/ν⌉₊+1)).card:ℝ) := by
  let n := Fintype.card V
  let r := ⌈ν*(n:ℝ)⌉₊
  let t := ⌈τ*(n:ℝ)⌉₊
  let b := ⌊ξ*(n:ℝ)⌋₊
  let K := ⌈12/ν⌉₊
  let j := r/2
  let g := r/4
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hνSq : ν^2 ≤ 1 := by nlinarith only [hν,hν₁,mul_nonneg hν.le (sub_nonneg.mpr hν₁)]
  have hνn : 128 ≤ ν*(n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hνSq hν.le) hn
    change 128 ≤ ν^3*(n:ℝ) at hOrder
    nlinarith only [hh,hOrder]
  have hr : ν*(n:ℝ) ≤ (r:ℝ) := Nat.le_ceil _
  have hr8 : 8 ≤ r := by exact_mod_cast (show (8:ℝ) ≤ r by linarith)
  have hBr : (b:ℝ) ≤ ξ*(n:ℝ) := Nat.floor_le (by positivity)
  have hTr : (t:ℝ) ≤ τ*(n:ℝ)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hKr : (K:ℝ) < 12/ν+1 := Nat.ceil_lt_add_one (by positivity)
  have hKlo : 12/ν ≤ (K:ℝ) := Nat.le_ceil _
  have hKup : (K:ℝ) ≤ ν^2*(n:ℝ)/8 := by
    have hh := (lt_div_iff₀ hν).mp (show (K:ℝ) < (12+ν)/ν by
        rw [add_div,div_self hν.ne']; exact hKr)
    apply (mul_le_mul_iff_right₀ hν).mp
    nlinarith only [hh,hOrder,hν₁]
  have hBsum : (b:ℝ)+(K:ℝ) ≤ ν^2*(n:ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right hSmall hn
    linarith only [hh,hBr,hKup]
  have hj : (r:ℝ)/2 ≤ (j:ℝ)+1 := by
    have hh : r ≤ (j+1)*2 := by dsimp [j]; omega
    exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by exact_mod_cast hh)
  have hBudget : n*(b+K) < (j+1)*r := by
    have h1 : (n:ℝ)*((b:ℝ)+K) ≤ (n:ℝ)*(ν^2*(n:ℝ)/4) := mul_le_mul_of_nonneg_left hBsum hn
    have h2 := mul_le_mul_of_nonneg_right hj (Nat.cast_nonneg r : (0:ℝ)≤r)
    have h3 := pow_le_pow_left₀ (mul_nonneg hν.le hn) hr 2
    have h4 : (0:ℝ) < (r:ℝ)^2 := by positivity
    exact_mod_cast (show (n:ℝ)*((b:ℝ)+K) < ((j:ℝ)+1)*r by nlinarith only [h1,h2,h3,h4])
  have hg : (r:ℝ)/8 ≤ (g:ℝ) := by
    have hh : r≤g*8 := by dsimp [g]; omega
    exact (div_le_iff₀ (by norm_num : (0:ℝ)<8)).mpr (by exact_mod_cast hh)
  have hSteps : n<t+K*g := by
    have hh := mul_le_mul hKlo hg (by positivity : (0:ℝ)≤(r:ℝ)/8)
      (Nat.cast_nonneg K)
    exact_mod_cast (show (n:ℝ) < (t:ℝ)+(K:ℝ)*g by
      have hNpos : (0:ℝ)<n := pos_of_mul_pos_right (by linarith only [hνn] : 0 < ν*(n:ℝ)) hν.le
      have hScale := mul_le_mul_of_nonneg_left hr (show (0:ℝ) ≤ (12/ν)/8 by positivity)
      have hEq : (12/ν)/8*(ν*(n:ℝ))=3*(n:ℝ)/2 := by field_simp; ring
      rw [hEq] at hScale
      have ht : (0:ℝ) ≤ t := Nat.cast_nonneg _
      nlinarith only [hh,hScale,hNpos,ht])
  have hf : ∀ F,(B F).card ≤ b := fun F => Nat.le_floor (hB F)
  have hout : t+b+1 ≤ outDegree D (terminus F₀) := by
    exact_mod_cast (show (t:ℝ)+(b:ℝ)+1 ≤ (outDegree D (terminus F₀):ℝ) by
      change (τ+ξ)*(n:ℝ)+2 ≤ _ at hOut
      nlinarith only [hOut,hBr,hTr])
  have hFinal := most_termini_reachable B F₀ r t b j g K hf
    (integer_of_real D ν τ hν.le hRobust) hout hBudget
    (by dsimp [g,j]; omega) hSteps
  let S := reachableTermini B F₀ (K+1)
  have hCard : S.card ≤ n := card_le_univ _
  have hMiss : n-S.card < t := by
    change n < S.card+t at hFinal
    omega
  have hReal := Nat.lt_ceil.mp hMiss
  rw [Nat.cast_sub hCard] at hReal
  change (n:ℝ)-τ*(n:ℝ) ≤ (S.card:ℝ)
  linarith only [hReal]

/-- Close a reachable prefactor at an incoming neighbour outside a
prescribed set, as needed to close the enlarged path in Theorem 5.3. -/
theorem exists_reachable_closed_factor (B : Prefactor D x → Finset V)
    (F₀ : Prefactor D x) (k : ℕ) (a : ℝ) (Z : Finset V)
    (hReach : (Fintype.card V:ℝ)-a ≤ ((reachableTermini B F₀ k).card:ℝ))
    (hIn : a+(Z.card:ℝ) < (inDegree D x:ℝ)) :
    ∃ F, Reach B F₀ k F ∧ terminus F ∉ Z ∧ ∀ v,D.Adj v (F.successor v) := by
  let S := reachableTermini B F₀ k
  let I : Finset V := univ.filter fun v => D.Adj v x
  have hI : a+(Z.card:ℝ) < (I.card:ℝ) := hIn
  have hDiff : (I.card:ℝ) ≤ ((I\Z).card:ℝ)+(Z.card:ℝ) := by
    exact_mod_cast card_le_card_sdiff_add_card (s:=I) (t:=Z)
  have hSum : Fintype.card V < S.card+(I\Z).card := by
    exact_mod_cast (show (Fintype.card V:ℝ) < (S.card:ℝ)+((I\Z).card:ℝ) by
      change (Fintype.card V:ℝ)-a ≤ (S.card:ℝ) at hReach
      linarith only [hReach,hI,hDiff])
  have hCount := card_union_add_card_inter S (I\Z)
  have hBound := card_le_univ (S∪(I\Z))
  obtain ⟨y,hy⟩ := card_pos.mp (show 0 < (S∩(I\Z)).card by omega)
  obtain ⟨hyS,hyI⟩ := mem_inter.mp hy
  obtain ⟨hyArc,hyAvoid⟩ := mem_sdiff.mp hyI
  obtain ⟨F,hF,hEnd⟩ := mem_reachableTermini.mp hyS
  have hAdj : D.Adj y x := (mem_filter.mp hyArc).2
  refine ⟨F,hF,by simpa only [hEnd] using hyAvoid,close_factor F ?_⟩
  rw [hEnd]
  exact hAdj

end OverfullWork.DirectedPrefactor
