module

public import OverfullWork.KuhnOsthusExtenderRoutePreparation
public import OverfullWork.RealDirectedRobustExpansion

@[expose] public section


/-! Round the routing and saturation parameters used in Lemma 8.3. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- The order of the ordinary host is determined by the 50 equal
style cells in each cluster. -/
theorem ordinary_order_of_cluster_styles {V I : Type*} [Fintype V] [Fintype I]
    (cluster : V → I) (label : V → Fin 50) (u : ℕ)
    (hCell : ∀ i j, (univ.filter (fun x => cluster x = i ∧ label x = j)).card = u) :
    Fintype.card V = Fintype.card I*(50*u) := by
  let X (i : I) := univ.filter (fun x => cluster x = i)
  have hSize (i : I) : (X i).card = 50*u := by
    simpa only [X,mem_univ,and_true,card_univ,Fintype.card_fin] using
      card_cluster_styles cluster label u hCell i univ
  have hUnion : (univ : Finset I).biUnion X = univ := by
    ext x
    simp only [X,mem_biUnion,mem_univ,true_and,mem_filter,iff_true]
    exact ⟨cluster x,rfl⟩
  have hDis : (↑(univ : Finset I) : Set I).PairwiseDisjoint X := by
    intro i _ j _ hne
    exact disjoint_left.mpr (fun x hx hy => hne (((mem_filter.mp hx).2).symm.trans (mem_filter.mp hy).2))
  calc
    Fintype.card V = ((univ : Finset I).biUnion X).card := by rw [hUnion,card_univ]
    _ = Fintype.card I*(50*u) := by
      rw [card_biUnion hDis]
      simp only [hSize,sum_const,card_univ,Nat.nsmul_eq_mul]

/-- The original scale `s ≥ 10^7/ν²` is sufficient for the integer
chord scheduler. A cluster of size `50*u` uses the saturation
threshold `u/2-2`, leaving room for the endpoint correction. -/
theorem preprocessing_routing_parameters {I : Type*} [Fintype I]
    (R : Digraph I) (ν τ : ℝ) (hν : 0 < ν) (hν₁ : ν ≤ 1/3) (hντ : ν ≤ τ)
    (u n s : ℕ) (hu : 40 ≤ u) (hOrder : n ≤ 2*Fintype.card I*(50*u))
    (hLarge : 3 ≤ τ*(Fintype.card I:ℝ)) (hSlots : (10^7:ℝ) ≤ (s:ℝ)*ν^2)
    (hRob : IsRealRobust R ν τ)
    (hIn : ∀ i, 2*τ*(Fintype.card I:ℝ) ≤ (inDegree R i:ℝ))
    (hOut : ∀ i, 2*τ*(Fintype.card I:ℝ) ≤ (outDegree R i:ℝ)) :
    ∃ radius growth cutoff cap budget : ℕ,
      IsRobustAt R radius cutoff ∧ 0 < growth ∧ 2*budget+growth ≤ radius ∧
      (∀ i, cutoff+2*budget ≤ outDegree R i) ∧ (∀ i, cutoff ≤ inDegree R i) ∧
      ⌊1230*(n:ℝ)/(s:ℝ)⌋₊*(2*(Fintype.card I/growth+3)) < cap*(budget+1) ∧
      100*(cap+2) ≤ 50*u := by
  let q := Fintype.card I
  let r := ⌈ν*(q:ℝ)⌉₊
  let t := ⌈τ*(q:ℝ)⌉₊
  let b := r/4
  let g := r-2*b
  let cap := u/2-2
  have hq : 0 < q := by
    by_contra! h
    have he : q = 0 := Nat.eq_zero_of_le_zero h
    change 3 ≤ τ*(q:ℝ) at hLarge
    norm_num [he] at hLarge
  have hνq : 0 < ν*(q:ℝ) := mul_pos hν (by exact_mod_cast hq)
  have hr₀ : ν*(q:ℝ) ≤ (r:ℝ) := Nat.le_ceil _
  have hr₁ : (r:ℝ) ≤ ν*(q:ℝ)+1 := (Nat.ceil_lt_add_one hνq.le).le
  have ht₁ : (t:ℝ) ≤ τ*(q:ℝ)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hr : 0 < r := by exact_mod_cast hνq.trans_le hr₀
  have hg : 0 < g := by dsimp only [g,b]; omega
  have hg₂ : r ≤ 2*g := by dsimp only [g,b]; omega
  have hAvoid : 2*b+g ≤ r := by dsimp only [g,b]; omega
  have hFloor : (r:ℝ) ≤ 4*(b+1) := by exact_mod_cast (show r ≤ 4*(b+1) by dsimp only [b]; omega)
  have hSpend : (4:ℝ)*b ≤ r := by exact_mod_cast (show 4*b ≤ r by dsimp only [b]; omega)
  have hDegree : (t:ℝ)+2*(b:ℝ) ≤ 2*τ*(q:ℝ) := by
    have hντq := mul_le_mul_of_nonneg_right hντ (Nat.cast_nonneg q)
    linarith only [hLarge,hSpend,hr₁,ht₁,hντq]
  have hRatio : ((q/g:ℕ):ℝ) ≤ 2/ν := by
    have hGrow : ν*(q:ℝ) ≤ 2*(g:ℝ) := hr₀.trans (by exact_mod_cast hg₂)
    have hDiv : ((q/g:ℕ):ℝ)*(g:ℝ) ≤ q := by exact_mod_cast Nat.div_mul_le_self q g
    have hMul := mul_le_mul_of_nonneg_left hGrow (Nat.cast_nonneg (q/g))
    have hCancel := mul_le_mul_of_nonneg_left hDiv (by norm_num : (0:ℝ) ≤ 2)
    apply (le_div_iff₀ hν).mpr
    apply (mul_le_mul_iff_of_pos_right (by exact_mod_cast hq : (0:ℝ) < q)).mp
    nlinarith only [hMul,hCancel]
  have hRoute : ((q/g+3:ℕ):ℝ) ≤ 3/ν := by
    push_cast
    have hThird : (3:ℝ) ≤ 1/ν := (le_div_iff₀ hν).mpr (by linarith)
    have hSum : (2:ℝ)/ν+1/ν = 3/ν := by rw [←add_div]; norm_num
    linarith only [hRatio,hThird,hSum]
  have hCap : 50*u ≤ 120*cap := by dsimp only [cap]; omega
  have hCapUpper : 100*(cap+2) ≤ 50*u := by dsimp only [cap]; omega
  have hArc : (⌊1230*(n:ℝ)/(s:ℝ)⌋₊:ℝ) ≤ 1230*(n:ℝ)/(s:ℝ) := Nat.floor_le (by positivity)
  have hMass := extender_chord_schedule_mass _ n q (50*u) s g cap b ν hν hq (by omega)
    hOrder hSlots hArc hRoute hCap (by linarith only [hr₀,hFloor])
  refine ⟨r,g,t,cap,b,integer_of_real R ν τ hν.le hRob,hg,hAvoid,?_,?_,hMass,hCapUpper⟩
  · intro i
    exact_mod_cast hDegree.trans (hOut i)
  · intro i
    have ht : (t:ℝ) ≤ 2*τ*(q:ℝ) := (le_add_of_nonneg_right (by positivity)).trans hDegree
    exact_mod_cast ht.trans (hIn i)

end OverfullWork.DirectedRobustExpansion
