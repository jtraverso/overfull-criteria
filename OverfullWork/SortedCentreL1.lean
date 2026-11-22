module

public import OverfullWork.SortedCentrePairing

@[expose] public section


/-! # Telescoping L1 control for an exceptional weighted row

Unlike a second-moment bound, this controls every signing of the pairing.
One prescribed pair is removed before sorting and reinserted afterwards.
-/
namespace OverfullWork.SortedCentreL1
open Finset SortedCentrePairing
open scoped Classical
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_sorted_pairing_l1 {m : ℕ} (hcard : Fintype.card V=2*m)
    (w : V → ℝ) (S : ℝ) (hS : 0≤S) (hw : ∀ v,0≤w v ∧ w v≤S) :
    ∃ e : (Fin m×Bool) ≃ V,
      (∑ i : Fin m,|w (e (i,true))-w (e (i,false))|)≤S := by
  classical
  by_cases hm : m=0
  · subst m
    let e : (Fin 0×Bool) ≃ V:=Fintype.equivOfCardEq (by simp [hcard])
    exact ⟨e,by simpa using hS⟩
  have hn : 0<2*m:=by omega
  let e₀ : Fin (2*m) ≃ V:=(Fintype.equivFinOfCardEq hcard).symm
  let f₀ : Fin (2*m) → ℝ:=fun i => w (e₀ i)
  let q : Fin (2*m) ≃ V:=(Tuple.sort f₀).trans e₀
  have hq : Monotone (fun i => w (q i)) := by
    intro i j hij
    have hh : f₀ (Tuple.sort f₀ i)≤f₀ (Tuple.sort f₀ j):=Tuple.monotone_sort f₀ hij
    exact hh
  let f : ℕ → ℝ:=fun k => w (q (clampIndex hn k))
  have hf : Monotone f:=hq.comp (clampIndex_monotone hn)
  let e : (Fin m×Bool) ≃ V:=(adjacentPairEquiv m).trans q
  refine ⟨e,?_⟩
  calc
    _ = ∑ i : Fin m,|f (2*i.val+1)-f (2*i.val)| := by
      apply sum_congr rfl
      intro i _
      have htrue : clampIndex hn (2*i.val+1)=adjacentPairEquiv m (i,true) := by
        apply Fin.ext
        rw [clampIndex_val_of_lt hn (show 2*i.val+1<2*m by omega),adjacentPairEquiv_true_val]
      have hfalse : clampIndex hn (2*i.val)=adjacentPairEquiv m (i,false) := by
        apply Fin.ext
        rw [clampIndex_val_of_lt hn (show 2*i.val<2*m by omega),adjacentPairEquiv_false_val]
      change |w (q (adjacentPairEquiv m (i,true)))-w (q (adjacentPairEquiv m (i,false)))|=
        |w (q (clampIndex hn (2*i.val+1)))-w (q (clampIndex hn (2*i.val)))|
      rw [htrue,hfalse]
    _ = ∑ i : Fin m,(f (2*i.val+1)-f (2*i.val)) := by
      apply sum_congr rfl
      intro i _
      exact abs_of_nonneg (sub_nonneg.mpr (hf (by omega)))
    _ = ∑ i∈range m,(f (2*i+1)-f (2*i)) :=
      Fin.sum_univ_eq_sum_range (fun i => f (2*i+1)-f (2*i)) m
    _ ≤ f (2*m)-f 0:=sum_alternating_gaps_le f hf m
    _ ≤ S:=by
      have hhi:=(hw (q (clampIndex hn (2*m)))).2
      have hlo:=(hw (q (clampIndex hn 0))).1
      change f (2*m)≤S at hhi
      change 0≤f 0 at hlo
      linarith

theorem exists_sorted_pairing_prescribed_succ_l1 {m : ℕ}
    (hcard : Fintype.card V=2*(m+1)) (x y : V) (hxy : x≠y)
    (w : V → ℝ) (S : ℝ) (hw : ∀ v,0≤w v ∧ w v≤S) :
    ∃ e : (Fin (m+1)×Bool) ≃ V,
      e (0,true)=x ∧ e (0,false)=y ∧
      (∑ i : Fin (m+1),|w (e (i,true))-w (e (i,false))|)≤2*S := by
  let p:=SimpleGraph.MultiGraph.pairEmbedding x y hxy
  obtain ⟨e₀,he₀⟩:=PairedPartition.exists_pairing_extending hcard
    (by omega : 1≤m+1) p
  have hpx : p (0,true)=x := by
    change (if (true : Bool) then x else y)=x
    simp only [ite_true]
  have hpy : p (0,false)=y := by
    change (if (false : Bool) then x else y)=y
    simp only [Bool.false_eq_true,if_false]
  have h₀x : e₀ (0,true)=x := by
    have hh:=he₀ (0 : Fin 1) true
    change e₀ (0,true)=p (0,true) at hh
    exact hh.trans hpx
  have h₀y : e₀ (0,false)=y := by
    have hh:=he₀ (0 : Fin 1) false
    change e₀ (0,false)=p (0,false) at hh
    exact hh.trans hpy
  have hS : 0≤S:=(hw x).1.trans (hw x).2
  let wt : (Fin m×Bool) → ℝ:=fun z => w (e₀ (z.1.succ,z.2))
  obtain ⟨σ,hσ⟩:=exists_sorted_pairing_l1
    (by simp [Nat.mul_comm] : Fintype.card (Fin m×Bool)=2*m) wt S hS (fun z => hw _)
  let π : (Fin (m+1)×Bool) ≃ (Fin (m+1)×Bool):=
    ((peelPair m).trans (Equiv.sumCongr (Equiv.refl Bool) σ)).trans (peelPair m).symm
  let e : (Fin (m+1)×Bool) ≃ V:=π.trans e₀
  have hhead : ∀ b,e (0,b)=e₀ (0,b):=fun b => rfl
  refine ⟨e,(hhead true).trans h₀x,(hhead false).trans h₀y,?_⟩
  have hheadE : |w (e (0,true))-w (e (0,false))|≤S := by
    rw [hhead,hhead,h₀x,h₀y]
    have hx:=hw x
    have hy:=hw y
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have htailE : (∑ i : Fin m,|w (e (i.succ,true))-w (e (i.succ,false))|)≤S:=hσ
  rw [Fin.sum_univ_succ]
  linarith only [hheadE,htailE]

theorem exists_sorted_pairing_prescribed_l1 {m : ℕ} (hm : 1≤m)
    (hcard : Fintype.card V=2*m) (x y : V) (hxy : x≠y)
    (w : V → ℝ) (S : ℝ) (hw : ∀ v,0≤w v ∧ w v≤S) :
    ∃ e : (Fin m×Bool) ≃ V,
      e (⟨0,by omega⟩,true)=x ∧ e (⟨0,by omega⟩,false)=y ∧
      (∑ i : Fin m,|w (e (i,true))-w (e (i,false))|)≤2*S := by
  cases m with
  | zero => omega
  | succ m => exact exists_sorted_pairing_prescribed_succ_l1 hcard x y hxy w S hw

/-- An L1 pairing budget controls every signing, without a random moment. -/
theorem signedSum_abs_le_of_pair_l1 {m : ℕ} (e : (Fin m×Bool) ≃ V)
    (w : V → ℝ) (B : ℝ)
    (hL1 : (∑ i : Fin m,|w (e (i,true))-w (e (i,false))|)≤B)
    (s : Fin m → Bool) :
    |SigningMoments.signedSum (fun i => w (e (i,true))-w (e (i,false))) s|≤B := by
  unfold SigningMoments.signedSum
  calc
    _ ≤ ∑ i : Fin m,|if s i then w (e (i,true))-w (e (i,false)) else -(w (e (i,true))-w (e (i,false)))| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin m,|w (e (i,true))-w (e (i,false))| := by
      apply sum_congr rfl
      intro i _
      split_ifs <;> simp only [abs_neg]
    _ ≤ B:=hL1

end OverfullWork.SortedCentreL1
