module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section


/-! The directed 1-factor decomposition of Osthus–Staden, Proposition 4.3.
A multiplicity matrix distinguishes the two directions at each pair. -/
namespace OverfullWork.DirectedMultigraphFactors
open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

private theorem exists_factor (M : V → V → ℕ) (d : ℕ) (hd : 0 < d)
    (hOut : ∀ v, ∑ w,M v w = d) (hIn : ∀ w, ∑ v,M v w = d) :
    ∃ σ : Equiv.Perm V, ∀ v, 0 < M v (σ v) := by
  let N := fun v => univ.filter (fun w => 0 < M v w)
  have hHall (S : Finset V) : S.card ≤ (S.biUnion N).card := by
    let T := S.biUnion N
    have hZero (v w : V) (hv : v ∈ S) (hw : w ∉ T) : M v w = 0 := by
      by_contra h
      exact hw (mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨mem_univ _,Nat.pos_of_ne_zero h⟩⟩)
    have hRows (v : V) (hv : v ∈ S) : ∑ w ∈ T,M v w = d := by
      rw [← hOut v]
      apply sum_subset (subset_univ T)
      exact fun w _ hw => hZero v w hv hw
    apply Nat.le_of_mul_le_mul_right _ hd
    calc
      S.card*d = ∑ v ∈ S,∑ w ∈ T,M v w := by simp [sum_congr rfl hRows]
      _ = ∑ w ∈ T,∑ v ∈ S,M v w := sum_comm
      _ ≤ ∑ w ∈ T,∑ v,M v w := sum_le_sum fun _ _ => sum_le_sum_of_subset (subset_univ S)
      _ = T.card*d := by simp [hIn]
  obtain ⟨f,hf,hAdj⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hHall
  exact ⟨Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩,
    fun v => (mem_filter.mp (hAdj v)).2⟩

/-- Every ordered pair appears exactly as often as its arc multiplicity. -/
theorem exists_factorization (M : V → V → ℕ) (d : ℕ)
    (hOut : ∀ v, ∑ w,M v w = d) (hIn : ∀ w, ∑ v,M v w = d) :
    ∃ F : Fin d → Equiv.Perm V, ∀ v w,
      ((univ : Finset (Fin d)).filter (fun i => F i v = w)).card = M v w := by
  induction d generalizing M with
  | zero =>
    refine ⟨Fin.elim0,?_⟩
    intro v w
    have h := single_le_sum (s := (univ : Finset V)) (f := M v)
      (fun _ _ => Nat.zero_le _) (mem_univ w)
    simp only [hOut v] at h
    simp [Nat.eq_zero_of_le_zero h]
  | succ d ih =>
    obtain ⟨σ,hσ⟩ := exists_factor M (d+1) (Nat.succ_pos _) hOut hIn
    let R := fun v w => M v w - if σ v = w then 1 else 0
    have hPay (v w : V) : R v w + (if σ v = w then 1 else 0) = M v w := by
      dsimp only [R]
      split_ifs with he
      · rw [←he]
        exact Nat.sub_add_cancel (hσ v)
      · simp
    have ho (v : V) : ∑ w,R v w = d := by
      have h := sum_congr (s₁ := (univ : Finset V)) rfl (fun w _ => hPay v w)
      rw [sum_add_distrib,hOut v] at h
      have hc : (∑ w : V, if σ v = w then (1:ℕ) else 0) = 1 := by
        simp [eq_comm (a := σ v)]
      omega
    have hi (w : V) : ∑ v,R v w = d := by
      have h := sum_congr (s₁ := (univ : Finset V)) rfl (fun v _ => hPay v w)
      rw [sum_add_distrib,hIn w] at h
      have hc : (∑ v : V, if σ v = w then (1:ℕ) else 0) = 1 := by
        simp [← σ.eq_symm_apply]
      omega
    obtain ⟨F,hF⟩ := ih R ho hi
    refine ⟨Fin.cases σ F,?_⟩
    intro v w
    rw [card_filter,Fin.sum_univ_succ]
    simp only [Fin.cases_zero,Fin.cases_succ]
    calc
      _ = (if σ v = w then 1 else 0) + ((univ : Finset (Fin d)).filter (fun i => F i v = w)).card := by
        congr 1
        rw [card_filter]
        apply sum_congr rfl
        intro i _
        by_cases h : F i v = w <;> simp [h]
      _ = M v w := by rw [hF,add_comm,hPay]

end OverfullWork.DirectedMultigraphFactors
