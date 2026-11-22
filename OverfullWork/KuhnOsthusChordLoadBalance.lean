module

public import OverfullWork.PrefactorOpenOrbit

@[expose] public section


/-! The global load calculation in Claim 2 of Kühn–Osthus Lemma 9.5.
The cyclic intervals are counted with multiplicity. Their load
difference telescopes to the difference of the endpoint counts. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function DirectedPrefactor
open scoped Classical
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] in
theorem forward_load_telescope (s : Equiv.Perm I) (a x : I) (n : ℕ) :
    (∑ i ∈ range n, if (s : I → I)^[i] a = s x then (1:ℕ) else 0) +
        (if (s : I → I)^[n] a = s x then 1 else 0) =
      (∑ i ∈ range n, if (s : I → I)^[i] a = x then (1:ℕ) else 0) +
        (if a = s x then 1 else 0) := by
  induction n with
  | zero => by_cases h : a = s x <;> simp [h]
  | succ n ih =>
    rw [sum_range_succ,sum_range_succ,iterate_succ_apply']
    simp only [s.injective.eq_iff]
    omega

/-- Every request uses each elementary block at most once. When the
initial and terminal requests have the same distribution, each
elementary block has the same total load. -/
theorem exists_balanced_forward_chord_loads (s : Equiv.Perm I) (x₀ : I) (a b : J → I)
    (hCycle : ∀ x, s.SameCycle x₀ x)
    (hBalance : ∀ x,
      (∑ j, if a j = x then (1:ℕ) else 0) = ∑ j, if b j = x then (1:ℕ) else 0) :
    ∃ len : J → ℕ,
      let load (j : J) (x : I) := ∑ i ∈ range (len j), if (s : I → I)^[i] (a j) = x then (1:ℕ) else 0
      (∀ j, len j < minimalPeriod (s : I → I) (a j) ∧ (s : I → I)^[len j] (a j) = b j) ∧
      (∀ j x, load j x ≤ 1) ∧
      ∃ k ≤ Fintype.card J, ∀ x, ∑ j, load j x = k := by
  have hReach (j : J) : ∃ n < minimalPeriod (s : I → I) (a j), (s : I → I)^[n] (a j) = b j := by
    have h := (orbit_mem_iff s (a j) (b j)).mpr ((hCycle (a j)).symm.trans (hCycle (b j)))
    rw [orbit_eq_forward_trace] at h
    obtain ⟨i,hi,he⟩ := mem_image.mp h
    exact ⟨i,mem_range.mp hi,he⟩
  choose len hLen hEnd using hReach
  let load (j : J) (x : I) := ∑ i ∈ range (len j), if (s : I → I)^[i] (a j) = x then (1:ℕ) else 0
  have hSmall (j : J) (x : I) : load j x ≤ 1 := by
    dsimp only [load]
    rw [←card_filter]
    apply card_le_one.mpr
    intro i hi p hp
    apply iterate_injOn_Iio_minimalPeriod
      ((mem_range.mp (mem_filter.mp hi).1).trans (hLen j))
      ((mem_range.mp (mem_filter.mp hp).1).trans (hLen j))
    exact ((mem_filter.mp hi).2).trans ((mem_filter.mp hp).2).symm
  let total (x : I) := ∑ j, load j x
  have hStep (x : I) : total (s x) = total x := by
    have hh := sum_congr (s₁ := (univ : Finset J)) rfl (fun j _ =>
      forward_load_telescope s (a j) x (len j))
    simp only [hEnd,sum_add_distrib] at hh
    have h := hBalance (s x)
    change total (s x) + (∑ j, if b j = s x then 1 else 0) =
      total x + (∑ j, if a j = s x then 1 else 0) at hh
    omega
  have hIter (n : ℕ) : total ((s : I → I)^[n] x₀) = total x₀ := by
    induction n with
    | zero => rfl
    | succ n ih => rw [iterate_succ_apply',hStep,ih]
  refine ⟨len,fun j => ⟨hLen j,hEnd j⟩,hSmall,total x₀,?_,?_⟩
  · simpa [total] using
      sum_le_sum (s := (univ : Finset J)) (fun j _ => hSmall j x₀)
  · intro x
    obtain ⟨n,_,hn⟩ := (hCycle x).exists_pow_eq'
    rw [Equiv.Perm.coe_pow] at hn
    exact hn ▸ hIter n

omit [Fintype I] in
/-- For a 1-factor the shifted reversed requests of Claim 2 do
have balanced endpoint counts, even if there are loops after
contracting the clusters. -/
theorem balanced_requests_of_factor {V : Type*} [Fintype V]
    (cluster : V → I) (s : Equiv.Perm I) (F : Equiv.Perm V)
    (hSize : ∀ x, (univ.filter (fun v => cluster v = x)).card =
      (univ.filter (fun v => cluster v = s x)).card) :
    ∀ x, (∑ v, if cluster (F v) = x then (1:ℕ) else 0) =
      ∑ v, if s (cluster v) = x then (1:ℕ) else 0 := by
  intro x
  rw [Equiv.sum_comp F (fun v => if cluster v = x then (1:ℕ) else 0)]
  simp only [←s.eq_symm_apply,←card_filter]
  have h := hSize (s.symm x)
  rw [s.apply_symm_apply] at h
  exact h.symm

private theorem exists_load_allocation (q cap total : ℕ) (h : total ≤ q*cap) :
    ∃ f : Fin q → ℕ, (∀ i, f i ≤ cap) ∧ (∑ i, f i) = total := by
  induction q generalizing total with
  | zero =>
    have he : total = 0 := by simpa using h
    exact ⟨Fin.elim0,fun i => i.elim0,by simp [he]⟩
  | succ q ih =>
    let a := min cap total
    have ha : a ≤ cap := min_le_left _ _
    have ht : a ≤ total := min_le_right _ _
    have hb : total-a ≤ q*cap := by
      rw [Nat.succ_mul] at h
      dsimp only [a]
      omega
    obtain ⟨f,hf,hSum⟩ := ih (total-a) hb
    refine ⟨Fin.cases a f,?_,?_⟩
    · intro i
      exact Fin.cases (motive := fun i => Fin.cases a f i ≤ cap) ha hf i
    · rw [Fin.sum_univ_succ,Fin.cases_zero]
      simpa only [Fin.cases_succ,hSum] using Nat.add_sub_of_le ht

/-- The padding step of Claim 4. A whole copy of the universal walk
adds the same amount to every labeled edge in a batch. -/
theorem exists_balanced_chord_padding {A : Type*} (q s total : ℕ)
    (load : Fin q → A → ℕ) (hSize : ∀ i a, load i a ≤ s)
    (hTotal : ∀ a, (∑ i, load i a) = total) (hCap : total ≤ q*s) :
    ∃ pad : Fin q → ℕ,
      (∀ i, 11*s ≤ pad i ∧ pad i ≤ 12*s) ∧
      (∀ i a, 11*s ≤ load i a+pad i ∧ load i a+pad i ≤ 13*s) ∧
      ∀ a, (∑ i, (load i a+pad i)) = 12*s*q := by
  obtain ⟨f,hf,hSum⟩ := exists_load_allocation q s (q*s-total) (Nat.sub_le _ _)
  let pad (i : Fin q) := 11*s+f i
  refine ⟨pad,fun i => ⟨by dsimp [pad]; omega,by have := hf i; dsimp [pad]; omega⟩,
    fun i a => ⟨by dsimp [pad]; omega,by have := hf i; have := hSize i a; dsimp [pad]; omega⟩,?_⟩
  intro a
  simp only [sum_add_distrib,hTotal,pad,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,hSum]
  have he : total+(q*s-total) = q*s := Nat.add_sub_of_le hCap
  nlinarith only [he]

/-- The per-pair edge count need only lie between the adjacent
integer scales. The spare twelve slots per batch account for
rounding the lower scale down. -/
theorem exists_rounded_chord_padding {A : Type*} (q s total target : ℕ)
    (load : Fin q → A → ℕ) (hs : 24 ≤ s) (hSize : ∀ i a, load i a ≤ s/2)
    (hTotal : ∀ a, (∑ i, load i a) = total) (hCap : total ≤ q*(s/2))
    (hLo : q*(12*s) ≤ target) (hHi : target ≤ q*(12*(s+1))) :
    ∃ pad : Fin q → ℕ,
      (∀ i a, 11*s ≤ load i a+pad i ∧ load i a+pad i ≤ 13*s) ∧
      ∀ a, (∑ i, (load i a+pad i)) = target := by
  let lo := q*(11*s)
  let high := q*(12*(s+1))
  let d := target-total-lo
  have hTotalLe : total ≤ q*s :=
    hCap.trans (Nat.mul_le_mul_left _ (Nat.div_le_self _ _))
  have hT : lo+total ≤ target := by
    change q*(11*s)+total ≤ target
    rw [show 12*s = 11*s+s by omega,Nat.mul_add] at hLo
    exact (Nat.add_le_add_left hTotalLe _).trans hLo
  have hd : d ≤ q*(s+12) := by
    have hHigh : high = lo+q*(s+12) := by
      dsimp [high,lo]
      rw [←Nat.mul_add]
      congr 1
      omega
    change target ≤ high at hHi
    change target-total-lo ≤ q*(s+12)
    omega
  obtain ⟨f,hf,hSum⟩ := exists_load_allocation q (s+12) d hd
  let pad (i : Fin q) := 11*s+f i
  refine ⟨pad,?_ ,?_⟩
  · intro i a
    have h := hf i
    have h' := hSize i a
    dsimp [pad]
    omega
  · intro a
    simp only [sum_add_distrib,hTotal,pad,sum_const,card_univ,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_id,hSum]
    change total+(lo+d) = target
    dsimp only [d]
    omega

end OverfullWork.DirectedRobustExpansion
