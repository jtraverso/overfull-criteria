module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public import OverfullWork.GlobalParallelVariance
public import OverfullWork.MultigraphPartition
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section


/-! # Adaptive pairing for one bounded exceptional row

Sorting the exceptional row and pairing consecutive values gives a
squared-difference sum bounded by the squared range. A prescribed pair
can be separated out first, at the cost of a factor two.
-/
namespace OverfullWork.SortedCentrePairing
open Finset
open scoped Classical
set_option maxHeartbeats 4000000

/-- Alternating gaps of an increasing chain telescope below its range. -/
theorem sum_alternating_gaps_le (f : ℕ → ℝ) (hf : Monotone f) (m : ℕ) :
    (∑ i∈range m,(f (2*i+1)-f (2*i)))≤f (2*m)-f 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hh:=hf (show 2*m+1≤2*(m+1) by omega)
    linarith

/-- The sum of squares of the disjoint gaps is at most the squared range. -/
theorem sum_alternating_gap_squares_le (f : ℕ → ℝ) (hf : Monotone f) (m : ℕ)
    (S : ℝ) (hbound : ∀ i,0≤f i ∧ f i≤S) :
    (∑ i∈range m,(f (2*i+1)-f (2*i))^2)≤S^2 := by
  have hnonneg : ∀ i∈range m,0≤f (2*i+1)-f (2*i) := by
    intro i _
    exact sub_nonneg.mpr (hf (by omega))
  have hs : (∑ i∈range m,(f (2*i+1)-f (2*i)))≤S := by
    have hh:=sum_alternating_gaps_le f hf m
    have hhi:=(hbound (2*m)).2
    have hlo:=(hbound 0).1
    linarith
  exact (sum_sq_le_sq_sum_of_nonneg hnonneg).trans
    (pow_le_pow_left₀ (sum_nonneg hnonneg) hs 2)

/-- Indexing adjacent pairs by even and odd positions. -/
def adjacentPairEquiv (m : ℕ) : (Fin m×Bool) ≃ Fin (2*m) :=
  ((Equiv.prodCongr (Equiv.refl (Fin m)) finTwoEquiv.symm).trans finProdFinEquiv).trans
    (finCongr (by omega : m*2=2*m))

theorem adjacentPairEquiv_false_val (m : ℕ) (i : Fin m) :
    (adjacentPairEquiv m (i,false)).val=2*i.val := by
  change (finTwoEquiv.symm false).val+2*i.val=2*i.val
  simp [finTwoEquiv]

theorem adjacentPairEquiv_true_val (m : ℕ) (i : Fin m) :
    (adjacentPairEquiv m (i,true)).val=2*i.val+1 := by
  change (finTwoEquiv.symm true).val+2*i.val=2*i.val+1
  simp [finTwoEquiv]
  omega

def clampIndex {n : ℕ} (hn : 0<n) (k : ℕ) : Fin n :=
  ⟨min k (n-1),by omega⟩

theorem clampIndex_monotone {n : ℕ} (hn : 0<n) : Monotone (clampIndex hn) := by
  intro i j hij
  change min i (n-1)≤min j (n-1)
  exact min_le_min_right _ hij

theorem clampIndex_val_of_lt {n k : ℕ} (hn : 0<n) (hk : k<n) :
    (clampIndex hn k).val=k := by
  change min k (n-1)=k
  exact min_eq_left (by omega)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No prescribed pair: a pairing is constructed by sorting the row.
The weights may have ties and may vanish. -/
theorem exists_sorted_pairing {m : ℕ} (hcard : Fintype.card V=2*m)
    (w : V → ℝ) (S : ℝ) (hw : ∀ v,0≤w v ∧ w v≤S) :
    ∃ e : (Fin m×Bool) ≃ V,
      (∑ i : Fin m,(w (e (i,true))-w (e (i,false)))^2)≤S^2 := by
  classical
  by_cases hm : m=0
  · subst m
    let e : (Fin 0×Bool) ≃ V:=Fintype.equivOfCardEq (by simp [hcard])
    exact ⟨e,by simpa using sq_nonneg S⟩
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
  have hbound : ∀ i,0≤f i ∧ f i≤S:=fun i => hw _
  let e : (Fin m×Bool) ≃ V:=(adjacentPairEquiv m).trans q
  refine ⟨e,?_⟩
  calc
    _ = ∑ i : Fin m,(f (2*i.val+1)-f (2*i.val))^2 := by
      apply sum_congr rfl
      intro i _
      have htrue : clampIndex hn (2*i.val+1)=adjacentPairEquiv m (i,true) := by
        apply Fin.ext
        rw [clampIndex_val_of_lt hn (show 2*i.val+1<2*m by omega),adjacentPairEquiv_true_val]
      have hfalse : clampIndex hn (2*i.val)=adjacentPairEquiv m (i,false) := by
        apply Fin.ext
        rw [clampIndex_val_of_lt hn (show 2*i.val<2*m by omega),adjacentPairEquiv_false_val]
      change (w (q (adjacentPairEquiv m (i,true)))-w (q (adjacentPairEquiv m (i,false))))^2=
        (w (q (clampIndex hn (2*i.val+1)))-w (q (clampIndex hn (2*i.val))))^2
      rw [htrue,hfalse]
    _ = ∑ i∈range m,(f (2*i+1)-f (2*i))^2 :=
      Fin.sum_univ_eq_sum_range (fun i => (f (2*i+1)-f (2*i))^2) m
    _ ≤ S^2:=sum_alternating_gap_squares_le f hf m S hbound

/-- Separate the first pair from its tail, fixing the Boolean orientation. -/
def peelPair (m : ℕ) : (Fin (m+1)×Bool) ≃ Bool ⊕ (Fin m×Bool) where
  toFun z:=Fin.cases (Sum.inl z.2) (fun i => Sum.inr (i,z.2)) z.1
  invFun:=Sum.elim (fun b => (0,b)) (fun z => (z.1.succ,z.2))
  left_inv:=by
    rintro ⟨i,b⟩
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv:=by
    intro z
    cases z <;> rfl

/-- Prescribing the first pair costs at most one additional squared range:
remove that pair, sort and pair the remaining vertices, then reinsert it. -/
theorem exists_sorted_pairing_prescribed_succ {m : ℕ}
    (hcard : Fintype.card V=2*(m+1)) (x y : V) (hxy : x≠y)
    (w : V → ℝ) (S : ℝ) (hw : ∀ v,0≤w v ∧ w v≤S) :
    ∃ e : (Fin (m+1)×Bool) ≃ V,
      e (0,true)=x ∧ e (0,false)=y ∧
      (∑ i : Fin (m+1),(w (e (i,true))-w (e (i,false)))^2)≤2*S^2 := by
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
  let wt : (Fin m×Bool) → ℝ:=fun z => w (e₀ (z.1.succ,z.2))
  obtain ⟨σ,hσ⟩:=exists_sorted_pairing
    (by simp [Nat.mul_comm] : Fintype.card (Fin m×Bool)=2*m) wt S (fun z => hw _)
  let π : (Fin (m+1)×Bool) ≃ (Fin (m+1)×Bool):=
    ((peelPair m).trans (Equiv.sumCongr (Equiv.refl Bool) σ)).trans (peelPair m).symm
  let e : (Fin (m+1)×Bool) ≃ V:=π.trans e₀
  have hhead : ∀ b,e (0,b)=e₀ (0,b):=fun b => rfl
  have htail : ∀ (i : Fin m) b,e (i.succ,b)=e₀ ((σ (i,b)).1.succ,(σ (i,b)).2):=fun i b => rfl
  refine ⟨e,(hhead true).trans h₀x,(hhead false).trans h₀y,?_⟩
  have hheadE : (w (e (0,true))-w (e (0,false)))^2≤S^2 := by
    rw [hhead,hhead,h₀x,h₀y]
    have hx:=hw x
    have hy:=hw y
    have hp:=mul_nonneg (show 0≤S-(w x-w y) by linarith)
      (show 0≤S+(w x-w y) by linarith)
    nlinarith only [hp]
  have htailE : (∑ i : Fin m,(w (e (i.succ,true))-w (e (i.succ,false)))^2)≤S^2 := by
    exact hσ
  rw [Fin.sum_univ_succ]
  nlinarith only [hheadE,htailE]

/-- Arbitrary positive half-order version, with the prescribed vertices
in a named pair and every ordinary row still free to use a universal bound. -/
theorem exists_sorted_pairing_prescribed {m : ℕ} (hm : 1≤m)
    (hcard : Fintype.card V=2*m) (x y : V) (hxy : x≠y)
    (w : V → ℝ) (S : ℝ) (hw : ∀ v,0≤w v ∧ w v≤S) :
    ∃ e : (Fin m×Bool) ≃ V,
      e (⟨0,by omega⟩,true)=x ∧ e (⟨0,by omega⟩,false)=y ∧
      (∑ i : Fin m,(w (e (i,true))-w (e (i,false)))^2)≤2*S^2 := by
  cases m with
  | zero => omega
  | succ m => exact exists_sorted_pairing_prescribed_succ hcard x y hxy w S hw

end OverfullWork.SortedCentrePairing
