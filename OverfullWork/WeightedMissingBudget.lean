module

public import OverfullWork.FirstPhaseSeed

@[expose] public section


/-! # Weighted missing incidences and the initial centre budget -/
namespace SimpleGraph.MultiGraph.EdgeColoring
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {M : MultiGraph V} {k : ℕ}

def missingWeight (C : M.EdgeColoring k) (S : Finset V) (w : V → ℕ) (i : Fin k) : ℕ :=
  ∑ v∈C.missingSet S i,w v

def coveredWeight (C : M.EdgeColoring k) (S : Finset V) (w : V → ℕ) (i : Fin k) : ℕ :=
  ∑ v∈S,w v*(C.colourGraph i).degree v

theorem missingWeight_add_coveredWeight (C : M.EdgeColoring k) (S : Finset V)
    (w : V → ℕ) (i : Fin k) :
    C.missingWeight S w i+C.coveredWeight S w i=∑ v∈S,w v := by
  simp only [missingWeight,missingSet,sum_filter,coveredWeight,←sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  have hd:=C.colourGraph_degree_le_one i v
  by_cases hz : (C.colourGraph i).degree v=0
  · simp only [hz,ite_true,Nat.mul_zero,Nat.add_zero]
  · have he : (C.colourGraph i).degree v=1:=by omega
    simp only [he,show ¬(1:ℕ)=0 by omega,ite_false,Nat.mul_one,Nat.zero_add]

theorem sum_missingWeight (C : M.EdgeColoring k) (S : Finset V) (w : V → ℕ) :
    (∑ i,C.missingWeight S w i)=∑ v∈S,w v*(C.missingPalette v).card := by
  simp only [missingWeight,missingSet,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v hv
  simp only [missingPalette,card_eq_sum_ones,sum_filter,mul_sum,mul_ite,Nat.mul_one,Nat.mul_zero]

theorem sum_missingWeight_le (C : M.EdgeColoring k) (S : Finset V) (w : V → ℕ)
    (t D : ℕ) (hv : ∀ v∈S,(C.missingPalette v).card≤t) (hw : (∑ v∈S,w v)≤D) :
    (∑ i,C.missingWeight S w i)≤t*D := by
  rw [C.sum_missingWeight]
  calc
    _ ≤ ∑ v∈S,w v*t:=sum_le_sum (fun v hv' => Nat.mul_le_mul_left (w v) (hv v hv'))
    _ = (∑ v∈S,w v)*t:=by rw [sum_mul]
    _ ≤ D*t:=Nat.mul_le_mul_right t hw
    _ = _:=by ring

theorem missingWeight_balance_of_coveredWeight (C : M.EdgeColoring k) (S : Finset V)
    (w : V → ℕ) (L : ℕ)
    (hload : ∀ i j,C.coveredWeight S w i≤C.coveredWeight S w j+L) :
    ∀ i j,C.missingWeight S w i≤C.missingWeight S w j+L := by
  intro i j
  have hi:=C.missingWeight_add_coveredWeight S w i
  have hj:=C.missingWeight_add_coveredWeight S w j
  have hh:=hload j i
  omega

/-- A vertex defect bound t becomes a weighted missing bound 4t+L,
provided the palette has size at least one quarter of the weight budget. -/
theorem missingWeight_le_of_balanced_load (C : M.EdgeColoring k) (S : Finset V)
    (w : V → ℕ) (t D L : ℕ) (hk : 0<k) (hD : D≤4*k)
    (hv : ∀ v∈S,(C.missingPalette v).card≤t) (hw : (∑ v∈S,w v)≤D)
    (hload : ∀ i j,C.coveredWeight S w i≤C.coveredWeight S w j+L) :
    ∀ i,C.missingWeight S w i≤4*t+L := by
  have hbal:=C.missingWeight_balance_of_coveredWeight S w L hload
  have htotal:=C.sum_missingWeight_le S w t D hv hw
  intro i
  have hs:=sum_le_sum (s:=univ) (fun j _ => hbal i j)
  have hs' : k*C.missingWeight S w i≤(∑ j,C.missingWeight S w j)+k*L := by
    simpa only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] using hs
  have hDt:=Nat.mul_le_mul_left t hD
  have hh : k*C.missingWeight S w i≤k*(4*t+L):=by nlinarith only [hs',htotal,hDt]
  exact Nat.le_of_mul_le_mul_left hh hk

end SimpleGraph.MultiGraph.EdgeColoring
