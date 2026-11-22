module

public import OverfullWork.KuhnOsthusExtenderCoordinates
public import OverfullWork.KuhnOsthusFinalAssembly
public import OverfullWork.KuhnOsthusPreprocessingRouteBudgets

@[expose] public section


/-! Apply Corollary 8.5 to the same two reserves selected in
Lemma 8.6, with the integer chord budgets chosen from the reduced graph. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset InducedDigraphSampling
open scoped Classical
universe u

set_option maxHeartbeats 650000 in
/-- Fixed preprocessing reserves work for every regular leftover in
the physical complement. Only the expansion and semidegree bounds of
the reduced graph are needed to choose the routes and their capacity. -/
theorem kuhn_osthus_corollary_8_5_of_sampled_reserves
    (d d₀ ε ζ' ν τ γ : ℝ) (q : ℕ) (hq : 0 < q)
    (hd : 0 < d) (hd₀ : 0 < d₀) (hε : 0 < ε) (hεSmall : ε ≤ 1/100)
    (hζ' : 0 < ζ') (hν : 0 < ν) (hτ : 2*ν ≤ τ)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hGamma : γ ≤ ζ'*d₀)
    (hScale : 160*(5*ε) ≤ (ζ'*(d/4))^2) (hDiscard : 8*ν ≤ τ*(ζ'*d₀)^2)
    (hνDensity : ν < (1-5*ε)*d₀*(5*ε)) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {Z : Finset V} {label : V → Fin 50} {r l t : ℕ}
      (G P B E : Digraph V) (F : Fin r → OriginalExceptionalFactor label Z l)
      (R : Digraph (Fin q)) (H S : Digraph ↥Zᶜ) (cluster : ↥Zᶜ → Fin q)
      (m : ℕ) (b νR τR : ℝ),
      let s := 50*l+1
      let n := Fintype.card V
      N ≤ m → (∀ v, ¬ G.Adj v v) →
      (∀ v, let a := if v ∈ Z then r*s else r*s+t
        inDegree P v+r = a ∧ outDegree P v+r = a) →
      E ≤ P → induced E Zᶜ = H ⊔ S →
      (∀ i, (F i).digraph ≤ P ∧ Disjoint (F i).digraph E) →
      Pairwise (fun i j => Disjoint (F i).digraph (F j).digraph) →
      ExtenderPairBounds R H S cluster (fun x => label x.val) m d₀ (d₀/(q:ℕ)) ε b ((d₀/(d/2))^2*(50*m)) →
      s ≤ n → 2*(Z.card:ℝ) ≤ (n:ℝ)/s →
      (10^7:ℝ) ≤ (s:ℝ)*νR^2 → 0 < νR → νR ≤ 1/3 → νR ≤ τR → 3 ≤ τR*(q:ℝ) →
      (∀ i, ¬ R.Adj i i) → IsRealRobust R νR τR →
      (∀ i, 2*τR*(q:ℝ) ≤ (inDegree R i:ℝ)) → (∀ i, 2*τR*(q:ℝ) ≤ (outDegree R i:ℝ)) →
      16 ≤ (ζ'*d₀)^2*(21*m) →
      ((r*s:ℕ):ℝ) ≤ ε*(d₀/(q:ℕ))*((2*ε)*(50*m)) →
      ζ'*d₀*(50*m)+((r*s:ℕ):ℝ) ≤ 21*b →
      ∀ D : Digraph V, D ≤ G \ (P ⊔ B) →
        (∀ v, inDegree D v = r ∧ outDegree D v = r) →
        (∀ x y, x ∈ Z → y ∈ Z → ¬ D.Adj x y) →
        ∃ (a : ℕ) (C : Fin a → Equiv.Perm V), matchingUnion C ≤ P ⊔ D ∧
          (∀ i, HasSpanningCycle (fun x y => C i x = y)) ∧
          (∀ i j, i ≠ j → ∀ v, C i v ≠ C j v) ∧
          let L := (P ⊔ D) \ matchingUnion C
          (∀ x y, L.Adj x y → x ∉ Z ∧ y ∉ Z) ∧
          ∀ v : ↥Zᶜ, inDegree (induced L Zᶜ) v = t ∧ outDegree (induced L Zᶜ) v = t := by
  have hε₁ : 5*ε < 1 := by linarith only [hεSmall]
  obtain ⟨N,hN⟩ := exists_bounded_path_extension_of_sampled_pairs.{u}
    d d₀ ε ζ' ν τ γ q hq hd hd₀ hε hε₁ hζ' hν hτ hτγ hγ hGamma hScale hDiscard hνDensity
  refine ⟨max N 40,?_⟩
  intro V _ Z label r l t G P B E F R H S cluster m b νR τR s n hM hNoLoop hRegP hEP hE hF hDisF
    hPairs hSize hZ hSlots hνR hνR₁ hνRτ hLarge hLoopR hRobR hIn hOut hDiagonal hPay hStyles
  have hm : 40 ≤ m := (le_max_right _ _).trans hM
  have hCard : Zᶜ.card = q*(50*m) := by
    simpa only [Fintype.card_coe,Fintype.card_fin] using
      (ordinary_order_of_cluster_styles cluster (fun v => label v.val) m (fun i j => by
        convert (hPairs.cells i j) using 1
        congr 1
        exact filter_congr_decidable _ _ _))
  have hHalf : 2*Z.card ≤ n := by
    have hs : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast (show 1 ≤ s by dsimp only [s]; omega)
    have hh := hZ.trans (div_le_self (Nat.cast_nonneg n) hs)
    exact_mod_cast hh
  have hOrder : n ≤ 2*q*(50*m) := by
    have hsum : Zᶜ.card+Z.card = n := card_compl_add_card Z
    calc
      n ≤ 2*(q*(50*m)) := by omega
      _ = 2*q*(50*m) := by rw [mul_assoc]
  have hSlotsNat : 10^7 ≤ s := by
    have hSq : νR^2 ≤ 1 := by nlinarith only [hνR₁,mul_nonneg hνR.le (show 0 ≤ 1-νR by linarith)]
    exact_mod_cast hSlots.trans (mul_le_of_le_one_right (Nat.cast_nonneg s) hSq)
  have hL : 2452 ≤ (50*l)/1226 := by dsimp only [s] at hSlotsNat; omega
  have hRoute := preprocessing_routing_parameters R νR τR hνR hνR₁ hνRτ m n s hm
    (by simpa only [Fintype.card_fin] using hOrder) (by simpa only [Fintype.card_fin] using hLarge) hSlots
    hRobR (fun i => by simpa only [Fintype.card_fin] using hIn i)
    (fun i => by simpa only [Fintype.card_fin] using hOut i)
  obtain ⟨radius,growth,cutoff,cap,budget,hRob,hGrowth,hAvoid,hDegreeOut,hDegreeIn,hMass,hCap⟩ := hRoute
  let e := ⌊(2*ε)*(50*m)⌋₊
  have hCut : (2*ε)*(50*m) ≤ (e:ℝ)+1 := (Nat.lt_floor_add_one _).le
  have he : e ≤ m := by
    have he₀ : (e:ℝ) ≤ (2*ε)*(50*m) := Nat.floor_le (by positivity)
    have hεm := mul_le_mul_of_nonneg_right hεSmall (Nat.cast_nonneg m)
    exact_mod_cast (show (e:ℝ) ≤ m by linarith only [he₀,hεm])
  have hExtend := hN R H S cluster (fun v => label v.val) m e (r*s) radius growth cutoff cap budget
    ⌊1230*(n:ℝ)/(s:ℝ)⌋₊ b ((le_max_left _ _).trans hM) (by omega) hPairs hLoopR
    (by simpa only [Fintype.card_fin] using hRob) hGrowth hAvoid hDegreeOut hDegreeIn
    (by simpa only [Fintype.card_fin] using hMass) hCap he hCut hDiagonal hPay hStyles
  rw [←hE] at hExtend
  exact kuhn_osthus_process_leftover_from_residual_extender G P B E F hNoLoop hRegP
    (fun i => (hF i).1) hEP (fun i => (hF i).2) (fun _ _ hij => hDisF hij) hL hSize
    (by simpa only [n,s,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hZ)
    (by simpa only [n,s,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hExtend)

end OverfullWork.DirectedRobustExpansion
