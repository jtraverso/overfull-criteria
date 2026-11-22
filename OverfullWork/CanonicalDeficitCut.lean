module

public import OverfullWork.CanonicalBipartiteRealization

@[expose] public section


/-! # The actual even cut in an ordered deficiency sequence

Select the last prefixMass of the odd entries whose sum is at most half
the total deficiency. Admissibility forces the prefixMass to contain at
least the first pair. The next odd entry straddles the remaining budget.
-/
namespace OverfullWork.CanonicalDeficitCut
open Finset
open scoped Classical
set_option maxHeartbeats 5000000

noncomputable def prefixMass {n : ℕ} (a : Fin n→ℕ) (k : ℕ) : ℕ:=
  ∑i : Fin n,if i.val<k then a i else 0

noncomputable def entry {n : ℕ} (a : Fin n→ℕ) (k : ℕ) : ℕ:=
  ∑i : Fin n,if i.val=k then a i else 0

theorem entry_eq {n : ℕ} (a : Fin n→ℕ) (i : Fin n) : entry a i.val=a i := by
  unfold entry
  rw [sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg (fun he=>hji (Fin.ext he))]
  · simp

theorem entry_eq_zero {n : ℕ} (a : Fin n→ℕ) (k : ℕ) (hk : n≤k) : entry a k=0 := by
  unfold entry
  apply sum_eq_zero
  intro i _
  exact if_neg (by omega)

theorem prefix_succ {n : ℕ} (a : Fin n→ℕ) (k : ℕ) :
    prefixMass a (k+1)=prefixMass a k+entry a k := by
  unfold prefixMass entry
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  split_ifs <;> omega

theorem prefix_full {n : ℕ} (a : Fin n→ℕ) : prefixMass a n=∑i,a i := by
  unfold prefixMass
  apply sum_congr rfl
  intro i _
  exact if_pos i.isLt

theorem prefix_one {n : ℕ} (a : Fin (n+1)→ℕ) : prefixMass a 1=a 0 := by
  have hh:=prefix_succ a 0
  have hz : prefixMass a 0=0 := by simp [prefixMass]
  have he : entry a 0=a 0:=entry_eq a 0
  simpa only [hz,zero_add,he] using hh

/-- The cut is constructed by finite maximization. Its hypotheses are
just pairwise order, admissibility at the first vertex and the even sum. -/
theorem exists_cut {n : ℕ} (a b : Fin (n+1)→ℕ) (T : ℕ)
    (hpair : ∀i,b i≤a i) (hfirst : a 0≤T)
    (htotal : (∑i : Fin (n+1),(a i+b i))=2*T) :
    ∃k : ℕ,1≤k ∧ k≤n+1 ∧ prefixMass a k≤T ∧ T≤prefixMass a k+entry a k := by
  have hsum : T≤∑i,a i := by
    have hh:=sum_le_sum (s:=univ) (fun i _=>hpair i)
    rw [sum_add_distrib] at htotal
    omega
  let k:=Nat.findGreatest (fun k=>prefixMass a k≤T) (n+1)
  have hk : k≤n+1:=Nat.findGreatest_le _
  have hpre : prefixMass a k≤T := Nat.findGreatest_spec (P:=fun k=>prefixMass a k≤T) (show 1≤n+1 by omega)
    (by rw [prefix_one];exact hfirst)
  have hkpos : 1≤k := Nat.le_findGreatest (P:=fun k=>prefixMass a k≤T) (show 1≤n+1 by omega)
    (by rw [prefix_one];exact hfirst)
  refine ⟨k,hkpos,hk,hpre,?_⟩
  by_cases hkn : k=n+1
  · rw [hkn,entry_eq_zero a _ (by omega),add_zero,prefix_full]
    exact hsum
  · have hlt : k<n+1 := by omega
    have hh:¬prefixMass a (k+1)≤T:=Nat.findGreatest_is_greatest (P:=fun k=>prefixMass a k≤T) (by omega : k<k+1) (by omega)
    rw [prefix_succ] at hh
    omega

end OverfullWork.CanonicalDeficitCut
