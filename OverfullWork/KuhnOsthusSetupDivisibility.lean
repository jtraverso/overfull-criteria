module

public import OverfullWork.KuhnOsthusDivisibleClusters
public import Mathlib.Algebra.GCDMonoid.Finset

@[expose] public section


/-! The integer divisibilities used by the common setup of
Kühn–Osthus Lemmas 8.6, 9.5, 9.7 and 11.2. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- A fixed modulus for the initial cluster count suffices after
refinement. The factor of ten permits the batches in Lemma 9.5.
Divisibility by `q` makes the exceptional factor count integral. -/
theorem exists_kuhn_osthus_cluster_count_modulus (f g q s : ℕ)
    (hf : 0 < f) (hg : 2 ≤ g) (hq : 0 < q) (hs : 1 < s) :
    ∃ b : ℕ, 0 < b ∧ ∀ (k₀ ℓ : ℕ), b ∣ k₀ →
      let k := ℓ*k₀
      14 ∣ k ∧ f ∣ k ∧ g ∣ k ∧ (s-1) ∣ 50*k ∧
      (∃ t : ℕ, f*k = q*t) ∧
      (∃ p d : ℕ, f*k = p*10 ∧ f*k = d*3*g.choose 2) := by
  let divisors : Finset ℕ := {14,f,g,3*g.choose 2,10,q,s-1}
  let b := divisors.lcm id
  have hChoose : 0 < g.choose 2 := Nat.choose_pos hg
  have hPos : 0 < b := by
    apply Nat.pos_of_ne_zero
    exact Finset.lcm_ne_zero_iff.mpr (by
      intro a ha
      simp only [divisors,mem_insert,mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hf.ne',hq.ne'] <;> omega)
  refine ⟨b,hPos,?_⟩
  intro k₀ ℓ hb k
  have hAll (a : ℕ) (ha : a ∈ divisors) : a ∣ k :=
    (Finset.dvd_lcm (f := id) ha).trans (hb.trans (dvd_mul_left _ _))
  have h14 := hAll 14 (by simp [divisors])
  have hF := hAll f (by simp [divisors])
  have hG := hAll g (by simp [divisors])
  have hS := (hAll (s-1) (by simp [divisors])).trans (dvd_mul_left k 50)
  obtain ⟨t,ht⟩ := (hAll q (by simp [divisors])).trans (dvd_mul_left k f)
  obtain ⟨p,hp⟩ := (hAll 10 (by simp [divisors])).trans (dvd_mul_left k f)
  obtain ⟨d,hd⟩ := (hAll (3*g.choose 2) (by simp [divisors])).trans (dvd_mul_left k f)
  exact ⟨h14,hF,hG,hS,⟨t,ht⟩,p,d,hp.trans (Nat.mul_comm _ _),hd.trans (by ring)⟩

/-- The cluster-size modulus from the proof gives simultaneously
the fifty styles, the four walk quarters in each subcluster, and
the styles of the chord exceptional factors. -/
theorem kuhn_osthus_cluster_size_divisibilities (f q ℓ m : ℕ)
    (hq : 0 < q) (hFQ : f ∣ q) (hℓ : 0 < ℓ)
    (hm : 200*ℓ*(q/f) ∣ m) :
    0 < 200*ℓ*(q/f) ∧ 50 ∣ m ∧ (4*ℓ) ∣ m ∧
      ∃ z : ℕ, m = (q/f)*z ∧ f*m = q*z := by
  have hQ := Nat.div_mul_cancel hFQ
  have hqf : 0 < q/f := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h,zero_mul] at hQ
    omega
  have hM : 200*ℓ*(q/f) = 50*(4*ℓ)*(q/f) := by ring
  have h50 : 50 ∣ 200*ℓ*(q/f) := by rw [hM, Nat.mul_assoc]; exact dvd_mul_right _ _
  have h4 : 4*ℓ ∣ 200*ℓ*(q/f) := by
    rw [hM]
    exact (dvd_mul_left (4*ℓ) 50).trans (dvd_mul_right _ _)
  obtain ⟨z,hz⟩ := (dvd_mul_left (q/f) (200*ℓ)).trans hm
  refine ⟨by positivity,h50.trans hm,h4.trans hm,z,hz,?_⟩
  calc
    f*m = ((q/f)*f)*z := by rw [hz]; ring
    _ = q*z := by rw [hQ]

end OverfullWork.DirectedRobustExpansion
