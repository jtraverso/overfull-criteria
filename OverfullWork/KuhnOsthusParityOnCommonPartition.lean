module

public import OverfullWork.KuhnOsthusParityFromWoundPack
public import OverfullWork.KuhnOsthusWindingOrdinaryCoordinates

@[expose] public section


/-! Fix the tolerances for Lemma 10.5 before constructing the common
partition and the ordinary reserves. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 1800000 in
/-- Use the third packing on the original trimmed clusters.
The upper bound on the number of clusters makes the size threshold
uniform. The rates pay for the deletion of the two physical reserves,
the original parity factors, and the bounded losses within each round. -/
theorem exists_kuhn_osthus_parity_on_common_partition (d : ℝ) (hd : 0 < d) (hd₁ : d ≤ 1) :
    ∃ d₁Max ξMax : ℝ, 0 < d₁Max ∧ 0 < ξMax ∧
    ∀ J : ℕ, ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {n j base s loss : ℕ}
      (G C : Digraph V) (Z : Finset V) (X : Fin n → Finset V)
      (hi : n = 7*j) (hj : 0 < j) (ξ σ d₁ : ℝ),
      let Y (i : Fin (7*j)) := X (finCongr hi.symm i)
      let r₁ := ⌊d₁*(base:ℝ)⌋₊
      210 ≤ n → n ≤ J → 14 ∣ n →
      N ≤ base → (∃ m, base = 2*m) →
      0 ≤ d₁ → d₁ ≤ d₁Max → 0 ≤ ξ → ξ ≤ ξMax →
      loss ≤ 4*r₁ → s ≤ 3*r₁ → C ≤ G →
      (∀ v ∉ Z, inDegree C v ≤ loss ∧ outDegree C v ≤ loss) →
      (∀ i, (X i).card = base) → (∀ i i', i ≠ i' → Disjoint (X i) (X i')) →
      (∀ i, Disjoint (X i) Z) → (∀ v ∉ Z, ∃ i, v ∈ X i) →
      (∀ i, IsLowerSuperregularPair G ξ d (X i) (X (finRotate n i))) →
      ∀ E : WoundFactorPacking (G \ C) Z Y hj 1 base s σ,
        ∃ (c : ↥Zᶜ → Fin n) (P : Fin s → Digraph (↥Zᶜ ⊕ ↥Z))
          (L : Fin s → Fin 7 → Digraph (↥Zᶜ ⊕ ↥Z)) (T : Digraph ↥Zᶜ),
          let A (i : Fin n) := (univ : Finset ↥Zᶜ).filter (fun x => c x = i)
          let e := (exceptionalCoordinates Z).toEmbedding
          let F := pullDirectedPair e e (⨆ i, ⨆ j, (E.factors i j).digraph)
          let PC := liftDirectedPair e e (⨆ i, P i)
          (∀ i v, c v = i ↔ v.val ∈ X i) ∧
          PC ≤ G \ C ∧ (⨆ i, ⨆ j, (E.factors i j).digraph) ≤ PC ∧
          (∀ x, let D := if x ∈ Z then 7*s else 6*s; inDegree PC x = D ∧ outDegree PC x = D) ∧
          (∀ i, P i ≤ pullDirectedPair e e (G \ C) ∧ AbsorbsWindingFactor A (P i) (L i)) ∧
          Pairwise (fun i j => Disjoint (P i) (P j)) ∧
          (⨆ i, P i) = liftOrdinaryCycleArcs (↥Z) T ⊔ F ∧
          liftOrdinaryCycleArcs (↥Z) T ≤ pullDirectedPair e e (G \ C) \ F ∧
          (∀ x, inDegree T x = 5*s ∧ outDegree T x = 5*s) ∧
          ∀ v, let D := match v with | .inl _ => 6*s | .inr _ => 7*s
            inDegree (⨆ i, P i) v = D ∧ outDegree (⨆ i, P i) v = D := by
  obtain ⟨θ,hθ,hGap,hRoute⟩ := exists_parity_routing_tolerance d hd
  let a := θ/8192
  have ha : 0 < a := by dsimp only [a]; positivity
  have hθEq : θ = 8192*a := by dsimp only [a]; ring
  have hCoeff : ∀ (x : ℝ), 0 < x → x ≤ 4096 → 0 < x*a ∧ x*a ≤ 1 ∧ 2*(x*a) < d ∧ x*a ≤ θ := by
    intro x hx hX
    have h := mul_le_mul_of_nonneg_right hX ha.le
    exact ⟨mul_pos hx ha,by linarith only [h,hθEq,hGap,hd₁,ha],by linarith only [h,hθEq,hGap,ha],
      by linarith only [h,hθEq,ha]⟩
  obtain ⟨hAfter,hAfter₁,_,_⟩ := hCoeff 4 (by norm_num) (by norm_num)
  obtain ⟨hBase,hBase₁,_,_⟩ := hCoeff 16 (by norm_num) (by norm_num)
  obtain ⟨hε₀,hε₀₁,_,_⟩ := hCoeff 64 (by norm_num) (by norm_num)
  obtain ⟨hε,hε₁,hGap₁,hBound₁⟩ := hCoeff 256 (by norm_num) (by norm_num)
  obtain ⟨hε',hε'₁,hGap₂,hBound₂⟩ := hCoeff 1024 (by norm_num) (by norm_num)
  obtain ⟨hδ,hδ₁,hGap₃,hBound₃⟩ := hCoeff 4096 (by norm_num) (by norm_num)
  let ready (q : ℕ) (hq : 15 ≤ q) :=
    kuhn_osthus_parity_reserve_from_wound_pack.{u} q hq (64*a) (256*a) (1024*a) θ
      (256*a) (1024*a) (4096*a) d a
      hε₀ hε₀₁ hε hε₁ hε' hε'₁ ha.le
      (by linarith only [ha]) (by linarith only [ha]) (by linarith only [hθEq,ha]) hGap hGap₂ hd₁
      hε hε' hδ hε₁ hε'₁ hδ₁ hGap₁ hGap₂ hGap₃
      (by linarith only [ha]) (by linarith only [ha]) (by linarith only [ha]) hRoute
      (fun ξ hξ => by
        simp only [mem_insert,mem_singleton] at hξ
        rcases hξ with rfl | rfl | rfl | rfl | rfl
        exacts [hBound₁,hBound₂,hBound₁,hBound₂,hBound₃])
  refine ⟨a*a/4,a,by positivity,ha,?_⟩
  intro J
  let cutoff (q : ℕ) : ℕ := if h : 15 ≤ q then (ready q h).choose else 0
  let bound := (range (J+1)).sup cutoff
  let N := max 1 (max bound ⌈3/(a*a)⌉₊)
  refine ⟨N,?_⟩
  intro V _ n j base s loss G C Z X hi hj ξ σ d₁ Y r₁ hn hnJ hDiv hN hEven hd₁Pos hd₁Cap hξ hξCap
    hLoss hS hC hDegree hXSize hDis hOrdinary hCover hCycle E
  obtain ⟨q,rfl⟩ := hDiv
  have hq : 15 ≤ q := by omega
  have hjQ : j = 2*q := by omega
  subst j
  obtain ⟨m,rfl⟩ := hEven
  have hm : 0 < m := by
    have := (le_max_left 1 _).trans hN
    omega
  have hQ : q ≤ J := by omega
  have hReady : (ready q hq).choose ≤ 2*m := by
    have hCut : cutoff q ≤ bound := Finset.le_sup (f := cutoff) (mem_range.mpr (by omega : q < J+1))
    have hCut' : (ready q hq).choose ≤ bound := by simpa only [cutoff,dif_pos hq] using hCut
    exact hCut'.trans ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hM' : 3/(a*a) ≤ ((2*m:ℕ):ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈3/(a*a)⌉₊ ≤ 2*m from (le_max_right _ _).trans ((le_max_right _ _).trans hN)))
  have hPay : 3 ≤ a*a*((2*m:ℕ):ℝ) := by
    simpa only [mul_comm (a*a)] using (div_le_iff₀ (mul_pos ha ha)).mp hM'
  have hUnit (x : ℝ) (hx : 1 ≤ x) : 3 ≤ a*(((2*m:ℕ):ℝ)*(x*a)) := by
    have h := mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ a*a*((2*m:ℕ):ℝ))
    linarith only [h,hPay]
  have hR₁ : (r₁:ℝ) ≤ d₁*((2*m:ℕ):ℝ) := Nat.floor_le (by positivity)
  have hSmallR : (4:ℝ)*(r₁:ℝ) ≤ a*a*((2*m:ℕ):ℝ) := by
    have h := mul_le_mul_of_nonneg_right hd₁Cap (Nat.cast_nonneg (2*m))
    linarith only [h,hR₁]
  have hLossR : (loss:ℝ) ≤ 4*(r₁:ℝ) := by exact_mod_cast hLoss
  have hSR : (s:ℝ) ≤ 3*(r₁:ℝ) := by exact_mod_cast hS
  have h6 : ((s*6:ℕ):ℝ) ≤ a*(((2*m:ℕ):ℝ)*(64*a)) := by
    calc
      ((s*6:ℕ):ℝ) ≤ 18*(r₁:ℝ) := by push_cast; linarith only [hSR]
      _ ≤ 64*(a*a*((2*m:ℕ):ℝ)) := by
        linarith only [hSmallR,(show 0 ≤ a*a*((2*m:ℕ):ℝ) by positivity)]
      _ = _ := by ring
  obtain ⟨c,hCoord,hMap,hSize,hPair⟩ :=
    exists_kuhn_osthus_winding_ordinary_coordinates G Z X hOrdinary hDis hCover
  let A (i : Fin (14*q)) := (univ : Finset ↥Zᶜ).filter (fun v => c v = i)
  have hSize' (i : Fin (14*q)) : (A i).card = 2*m := by
    convert (hSize i).trans (hXSize i) using 1
    apply congrArg card
    ext x
    simp only [A,mem_filter]
  have hPairs (i : Fin (14*q)) :
      IsLowerSuperregularPair (induced G Zᶜ) ξ d (A i) (A (finRotate (14*q) i)) := by
    convert hPair i _ ξ d (hCycle i) using 1 <;> ext x <;> simp only [A,mem_filter]
  have hMap' (i : Fin (7*(2*q))) : Y i = (A (finCongr (by omega) i)).map (Function.Embedding.subtype _) := by
    convert (hMap (finCongr hi.symm i)).symm using 1
    congr 1
    ext x
    simp only [A,mem_filter]
  obtain ⟨P,L,T,hPC,hKeep,hReg,hAbs,hApart,hEq,hT,hTDeg,hPDeg⟩ :=
    (ready q hq).choose_spec G C Z c Y loss ξ (4*a) (16*a) σ hC hm hReady hDegree
      hAfter hAfter₁ hBase hBase₁ (by linarith only [hξCap,ha]) (by linarith only [ha]) (by linarith only [ha])
      (by linarith only [hLossR,hSmallR,mul_nonneg (mul_nonneg ha.le ha.le) (Nat.cast_nonneg (2*m))])
      (by linarith only [hSR,hSmallR,mul_nonneg (mul_nonneg ha.le ha.le) (Nat.cast_nonneg (2*m))])
      h6 ((by norm_num : (1:ℝ) ≤ 3).trans (hUnit 256 (by norm_num))) (hUnit 1024 (by norm_num))
      (hUnit 256 (by norm_num)) ((by norm_num : (1:ℝ) ≤ 3).trans (hUnit 1024 (by norm_num)))
      ((by norm_num : (1:ℝ) ≤ 3).trans (hUnit 4096 (by norm_num)))
      hMap' hSize' hPairs E
  exact ⟨c,P,L,T,hCoord,hPC,hKeep,hReg,hAbs,hApart,hEq,hT,hTDeg,hPDeg⟩

end OverfullWork.DirectedRobustExpansion
